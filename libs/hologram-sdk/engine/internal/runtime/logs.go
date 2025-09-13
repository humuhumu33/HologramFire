package runtime

import (
	"bufio"
	"bytes"
	"io"
	"sync"
	"time"

	"github.com/sirupsen/logrus"
)

// LogEntry represents a single log entry
type LogEntry struct {
	Timestamp time.Time
	Stream    string // "stdout" or "stderr"
	Data      []byte
}

// LogBuffer represents a ring buffer for container logs
type LogBuffer struct {
	mu       sync.RWMutex
	entries  []LogEntry
	capacity int
	head     int
	tail     int
	size     int
}

// NewLogBuffer creates a new log buffer with the specified capacity
func NewLogBuffer(capacity int) *LogBuffer {
	return &LogBuffer{
		entries:  make([]LogEntry, capacity),
		capacity: capacity,
	}
}

// Add adds a new log entry to the buffer
func (lb *LogBuffer) Add(entry LogEntry) {
	lb.mu.Lock()
	defer lb.mu.Unlock()

	lb.entries[lb.tail] = entry
	lb.tail = (lb.tail + 1) % lb.capacity

	if lb.size < lb.capacity {
		lb.size++
	} else {
		lb.head = (lb.head + 1) % lb.capacity
	}
}

// GetEntries returns log entries, optionally filtered and limited
func (lb *LogBuffer) GetEntries(since time.Time, tail int, stdout, stderr bool) []LogEntry {
	lb.mu.RLock()
	defer lb.mu.RUnlock()

	var result []LogEntry
	count := 0

	// Start from the appropriate position
	start := lb.head
	if tail > 0 && tail < lb.size {
		start = (lb.tail - tail + lb.capacity) % lb.capacity
	}

	// Collect entries
	for i := 0; i < lb.size; i++ {
		idx := (start + i) % lb.capacity
		entry := lb.entries[idx]

		// Filter by timestamp
		if !since.IsZero() && entry.Timestamp.Before(since) {
			continue
		}

		// Filter by stream
		if !stdout && entry.Stream == "stdout" {
			continue
		}
		if !stderr && entry.Stream == "stderr" {
			continue
		}

		result = append(result, entry)
		count++

		// Limit by tail if specified
		if tail > 0 && count >= tail {
			break
		}
	}

	return result
}

// LogManager manages logs for containers
type LogManager struct {
	logger *logrus.Logger
	mu     sync.RWMutex
	bufs   map[string]*LogBuffer
	subs   map[string][]chan LogEntry
}

// NewLogManager creates a new log manager
func NewLogManager(logger *logrus.Logger) *LogManager {
	return &LogManager{
		logger: logger,
		bufs:   make(map[string]*LogBuffer),
		subs:   make(map[string][]chan LogEntry),
	}
}

// CreateBuffer creates a log buffer for a container
func (lm *LogManager) CreateBuffer(containerID string, capacity int) {
	lm.mu.Lock()
	defer lm.mu.Unlock()

	lm.bufs[containerID] = NewLogBuffer(capacity)
	lm.subs[containerID] = make([]chan LogEntry, 0)
}

// AddLog adds a log entry for a container
func (lm *LogManager) AddLog(containerID string, stream string, data []byte) {
	lm.mu.RLock()
	buf, exists := lm.bufs[containerID]
	subs, subExists := lm.subs[containerID]
	lm.mu.RUnlock()

	if !exists {
		return
	}

	entry := LogEntry{
		Timestamp: time.Now(),
		Stream:    stream,
		Data:      make([]byte, len(data)),
	}
	copy(entry.Data, data)

	// Add to buffer
	buf.Add(entry)

	// Notify subscribers
	if subExists {
		for _, sub := range subs {
			select {
			case sub <- entry:
			default:
				// Non-blocking send, drop if channel is full
			}
		}
	}
}

// GetLogs returns logs for a container
func (lm *LogManager) GetLogs(containerID string, since time.Time, tail int, stdout, stderr bool) []LogEntry {
	lm.mu.RLock()
	buf, exists := lm.bufs[containerID]
	lm.mu.RUnlock()

	if !exists {
		return nil
	}

	return buf.GetEntries(since, tail, stdout, stderr)
}

// StreamLogs creates a channel for streaming logs
func (lm *LogManager) StreamLogs(containerID string) <-chan LogEntry {
	lm.mu.Lock()
	defer lm.mu.Unlock()

	ch := make(chan LogEntry, 100) // Buffered channel

	if subs, exists := lm.subs[containerID]; exists {
		lm.subs[containerID] = append(subs, ch)
	} else {
		lm.subs[containerID] = []chan LogEntry{ch}
	}

	return ch
}

// StopStreaming stops streaming logs for a container
func (lm *LogManager) StopStreaming(containerID string, ch <-chan LogEntry) {
	lm.mu.Lock()
	defer lm.mu.Unlock()

	if subs, exists := lm.subs[containerID]; exists {
		for i, sub := range subs {
			if sub == ch {
				// Remove the channel
				lm.subs[containerID] = append(subs[:i], subs[i+1:]...)
				close(sub)
				break
			}
		}
	}
}

// RemoveContainer removes all logs and subscriptions for a container
func (lm *LogManager) RemoveContainer(containerID string) {
	lm.mu.Lock()
	defer lm.mu.Unlock()

	// Close all subscriptions
	if subs, exists := lm.subs[containerID]; exists {
		for _, sub := range subs {
			close(sub)
		}
		delete(lm.subs, containerID)
	}

	// Remove buffer
	delete(lm.bufs, containerID)
}

// LogWriter is a writer that captures output and sends it to the log manager
type LogWriter struct {
	containerID string
	stream      string
	logManager  *LogManager
}

// NewLogWriter creates a new log writer
func NewLogWriter(containerID, stream string, logManager *LogManager) *LogWriter {
	return &LogWriter{
		containerID: containerID,
		stream:      stream,
		logManager:  logManager,
	}
}

// Write implements io.Writer
func (lw *LogWriter) Write(p []byte) (n int, err error) {
	lw.logManager.AddLog(lw.containerID, lw.stream, p)
	return len(p), nil
}

// StreamMux multiplexes stdout and stderr from a process
type StreamMux struct {
	containerID string
	logManager  *LogManager
	stdout      *LogWriter
	stderr      *LogWriter
}

// NewStreamMux creates a new stream multiplexer
func NewStreamMux(containerID string, logManager *LogManager) *StreamMux {
	return &StreamMux{
		containerID: containerID,
		logManager:  logManager,
		stdout:      NewLogWriter(containerID, "stdout", logManager),
		stderr:      NewLogWriter(containerID, "stderr", logManager),
	}
}

// GetStdout returns the stdout writer
func (sm *StreamMux) GetStdout() io.Writer {
	return sm.stdout
}

// GetStderr returns the stderr writer
func (sm *StreamMux) GetStderr() io.Writer {
	return sm.stderr
}

// CaptureProcessOutput captures output from a process and sends it to logs
func (sm *StreamMux) CaptureProcessOutput(reader io.Reader, stream string) {
	scanner := bufio.NewScanner(reader)
	for scanner.Scan() {
		line := scanner.Bytes()
		sm.logManager.AddLog(sm.containerID, stream, append(line, '\n'))
	}
}

// FormatLogEntry formats a log entry for output
func FormatLogEntry(entry LogEntry, timestamps bool) []byte {
	var buf bytes.Buffer

	if timestamps {
		buf.WriteString(entry.Timestamp.Format(time.RFC3339Nano))
		buf.WriteString(" ")
	}

	// Add stream prefix for stderr
	if entry.Stream == "stderr" {
		buf.WriteString("stderr ")
	}

	buf.Write(entry.Data)
	return buf.Bytes()
}
