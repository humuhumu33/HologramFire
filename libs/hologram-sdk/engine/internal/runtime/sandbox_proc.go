package runtime

import (
	"context"
	"fmt"
	"os"
	"os/exec"
	"sync"
	"time"

	"github.com/sirupsen/logrus"
)

// ProcessRunner represents a sandbox process runner
type ProcessRunner struct {
	logger *logrus.Logger
	mu     sync.RWMutex
	procs  map[string]*Process
}

// Process represents a running process
type Process struct {
	ID       string
	Cmd      *exec.Cmd
	Context  context.Context
	Cancel   context.CancelFunc
	Started  time.Time
	Finished time.Time
	ExitCode int
	Running  bool
	mu       sync.RWMutex
}

// NewProcessRunner creates a new process runner
func NewProcessRunner(logger *logrus.Logger) *ProcessRunner {
	return &ProcessRunner{
		logger: logger,
		procs:  make(map[string]*Process),
	}
}

// StartProcess starts a new process with the given command
func (pr *ProcessRunner) StartProcess(id, image string, cmd []string, env []string) (*Process, error) {
	pr.mu.Lock()
	defer pr.mu.Unlock()

	// For MVP, we'll use a simple shell command execution
	// In a real implementation, this would involve container runtime integration
	var execCmd []string

	if len(cmd) == 0 {
		// Default command for hello-world style containers
		execCmd = []string{"sh", "-c", "echo 'Hello from Hologram!' && sleep 1"}
	} else {
		// Use the provided command
		execCmd = append([]string{"sh", "-c"}, fmt.Sprintf("%s", cmd[0]))
		if len(cmd) > 1 {
			// Join multiple command arguments
			for i := 1; i < len(cmd); i++ {
				execCmd[len(execCmd)-1] += " " + cmd[i]
			}
		}
	}

	ctx, cancel := context.WithCancel(context.Background())
	process := &Process{
		ID:      id,
		Context: ctx,
		Cancel:  cancel,
		Started: time.Now(),
		Running: true,
	}

	// Create the command
	process.Cmd = exec.CommandContext(ctx, execCmd[0], execCmd[1:]...)

	// Set environment variables
	if len(env) > 0 {
		process.Cmd.Env = append(os.Environ(), env...)
	}

	// Start the process
	if err := process.Cmd.Start(); err != nil {
		cancel()
		return nil, fmt.Errorf("failed to start process: %w", err)
	}

	// Store the process
	pr.procs[id] = process

	// Monitor the process in a goroutine
	go pr.monitorProcess(process)

	pr.logger.WithFields(logrus.Fields{
		"container_id": id,
		"image":        image,
		"cmd":          execCmd,
		"pid":          process.Cmd.Process.Pid,
	}).Info("Started container process")

	return process, nil
}

// StopProcess stops a running process
func (pr *ProcessRunner) StopProcess(id string, timeout time.Duration) error {
	pr.mu.Lock()
	process, exists := pr.procs[id]
	pr.mu.Unlock()

	if !exists {
		return fmt.Errorf("process %s not found", id)
	}

	process.mu.Lock()
	defer process.mu.Unlock()

	if !process.Running {
		return nil // Already stopped
	}

	// Cancel the context to signal the process to stop
	process.Cancel()

	// Wait for the process to finish with timeout
	done := make(chan error, 1)
	go func() {
		done <- process.Cmd.Wait()
	}()

	select {
	case err := <-done:
		process.Running = false
		process.Finished = time.Now()
		if err != nil {
			if exitError, ok := err.(*exec.ExitError); ok {
				process.ExitCode = exitError.ExitCode()
			} else {
				process.ExitCode = 1
			}
		} else {
			process.ExitCode = 0
		}
		return err
	case <-time.After(timeout):
		// Force kill the process
		if process.Cmd.Process != nil {
			process.Cmd.Process.Kill()
		}
		process.Running = false
		process.Finished = time.Now()
		process.ExitCode = 137 // SIGKILL
		return fmt.Errorf("process %s did not stop within timeout", id)
	}
}

// GetProcess returns a process by ID
func (pr *ProcessRunner) GetProcess(id string) (*Process, bool) {
	pr.mu.RLock()
	defer pr.mu.RUnlock()

	process, exists := pr.procs[id]
	return process, exists
}

// RemoveProcess removes a process from tracking
func (pr *ProcessRunner) RemoveProcess(id string) {
	pr.mu.Lock()
	defer pr.mu.Unlock()

	if process, exists := pr.procs[id]; exists {
		process.Cancel()
		delete(pr.procs, id)
	}
}

// monitorProcess monitors a process and updates its state when it finishes
func (pr *ProcessRunner) monitorProcess(process *Process) {
	err := process.Cmd.Wait()

	process.mu.Lock()
	process.Running = false
	process.Finished = time.Now()
	if err != nil {
		if exitError, ok := err.(*exec.ExitError); ok {
			process.ExitCode = exitError.ExitCode()
		} else {
			process.ExitCode = 1
		}
	} else {
		process.ExitCode = 0
	}
	process.mu.Unlock()

	pr.logger.WithFields(logrus.Fields{
		"container_id": process.ID,
		"exit_code":    process.ExitCode,
		"duration":     process.Finished.Sub(process.Started),
	}).Info("Container process finished")
}

// GetPID returns the process PID
func (p *Process) GetPID() int {
	p.mu.RLock()
	defer p.mu.RUnlock()

	if p.Cmd != nil && p.Cmd.Process != nil {
		return p.Cmd.Process.Pid
	}
	return 0
}

// IsRunning returns whether the process is running
func (p *Process) IsRunning() bool {
	p.mu.RLock()
	defer p.mu.RUnlock()
	return p.Running
}

// GetExitCode returns the process exit code
func (p *Process) GetExitCode() int {
	p.mu.RLock()
	defer p.mu.RUnlock()
	return p.ExitCode
}
