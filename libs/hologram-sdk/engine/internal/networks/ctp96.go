package networks

import (
	"fmt"
	"sync"
	"time"

	"github.com/sirupsen/logrus"
)

// CTP96Manager manages CTP-96 transport connections
type CTP96Manager struct {
	logger        *logrus.Logger
	mu            sync.RWMutex
	sessions      map[string]*CTP96Session
	nextSessionID int
}

// CTP96Session represents a CTP-96 transport session
type CTP96Session struct {
	SessionID   string
	NetworkID   string
	ContainerID string
	CreatedAt   time.Time
	Status      string
	Config      map[string]string
	XHologram   map[string]any
}

// NewCTP96Manager creates a new CTP-96 manager
func NewCTP96Manager(logger *logrus.Logger) *CTP96Manager {
	return &CTP96Manager{
		logger:   logger,
		sessions: make(map[string]*CTP96Session),
	}
}

// CreateSession creates a new CTP-96 session
func (cm *CTP96Manager) CreateSession(networkID, containerID string, config map[string]string) (*CTP96Session, error) {
	cm.mu.Lock()
	defer cm.mu.Unlock()

	cm.nextSessionID++
	sessionID := fmt.Sprintf("ctp96_session_%d", cm.nextSessionID)

	// Check if session already exists for this container
	for _, session := range cm.sessions {
		if session.ContainerID == containerID && session.NetworkID == networkID {
			return nil, fmt.Errorf("CTP-96 session already exists for container %s on network %s", containerID, networkID)
		}
	}

	session := &CTP96Session{
		SessionID:   sessionID,
		NetworkID:   networkID,
		ContainerID: containerID,
		CreatedAt:   time.Now(),
		Status:      "active",
		Config:      make(map[string]string),
		XHologram:   make(map[string]any),
	}

	// Copy configuration
	if config != nil {
		for k, v := range config {
			session.Config[k] = v
		}
	}

	// Add Hologram-specific data
	session.XHologram["protocol"] = "ctp96"
	session.XHologram["version"] = "1.0"
	session.XHologram["encryption"] = "enabled"
	session.XHologram["quantum_resistant"] = true

	cm.sessions[sessionID] = session

	cm.logger.WithFields(logrus.Fields{
		"session_id":   sessionID,
		"network_id":   networkID,
		"container_id": containerID,
		"status":       session.Status,
	}).Info("CTP-96 session created")

	return session, nil
}

// GetSession retrieves a CTP-96 session by ID
func (cm *CTP96Manager) GetSession(sessionID string) (*CTP96Session, bool) {
	cm.mu.RLock()
	defer cm.mu.RUnlock()

	session, exists := cm.sessions[sessionID]
	return session, exists
}

// GetSessionByContainer retrieves a CTP-96 session by container ID
func (cm *CTP96Manager) GetSessionByContainer(containerID, networkID string) (*CTP96Session, bool) {
	cm.mu.RLock()
	defer cm.mu.RUnlock()

	for _, session := range cm.sessions {
		if session.ContainerID == containerID && session.NetworkID == networkID {
			return session, true
		}
	}

	return nil, false
}

// RemoveSession removes a CTP-96 session
func (cm *CTP96Manager) RemoveSession(sessionID string) error {
	cm.mu.Lock()
	defer cm.mu.Unlock()

	session, exists := cm.sessions[sessionID]
	if !exists {
		return fmt.Errorf("CTP-96 session %s not found", sessionID)
	}

	delete(cm.sessions, sessionID)

	cm.logger.WithFields(logrus.Fields{
		"session_id":   sessionID,
		"network_id":   session.NetworkID,
		"container_id": session.ContainerID,
	}).Info("CTP-96 session removed")

	return nil
}

// UpdateSessionStatus updates the status of a CTP-96 session
func (cm *CTP96Manager) UpdateSessionStatus(sessionID, status string) error {
	cm.mu.Lock()
	defer cm.mu.Unlock()

	session, exists := cm.sessions[sessionID]
	if !exists {
		return fmt.Errorf("CTP-96 session %s not found", sessionID)
	}

	oldStatus := session.Status
	session.Status = status

	cm.logger.WithFields(logrus.Fields{
		"session_id": sessionID,
		"old_status": oldStatus,
		"new_status": status,
	}).Info("CTP-96 session status updated")

	return nil
}

// ListSessions returns all CTP-96 sessions
func (cm *CTP96Manager) ListSessions() []*CTP96Session {
	cm.mu.RLock()
	defer cm.mu.RUnlock()

	sessions := make([]*CTP96Session, 0, len(cm.sessions))
	for _, session := range cm.sessions {
		sessions = append(sessions, session)
	}
	return sessions
}

// GetSessionsByNetwork returns all CTP-96 sessions for a network
func (cm *CTP96Manager) GetSessionsByNetwork(networkID string) []*CTP96Session {
	cm.mu.RLock()
	defer cm.mu.RUnlock()

	var sessions []*CTP96Session
	for _, session := range cm.sessions {
		if session.NetworkID == networkID {
			sessions = append(sessions, session)
		}
	}
	return sessions
}

// AddHologramData adds Hologram-specific data to a session
func (cm *CTP96Manager) AddHologramData(sessionID string, data map[string]any) error {
	cm.mu.Lock()
	defer cm.mu.Unlock()

	session, exists := cm.sessions[sessionID]
	if !exists {
		return fmt.Errorf("CTP-96 session %s not found", sessionID)
	}

	if session.XHologram == nil {
		session.XHologram = make(map[string]any)
	}

	for k, v := range data {
		session.XHologram[k] = v
	}

	return nil
}

// IsCTP96Enabled checks if CTP-96 is enabled via environment variable
func IsCTP96Enabled() bool {
	// This would check the HOLOGRAM_NET environment variable
	// For now, return false as default
	return false
}

// GetCTP96SessionID generates a CTP-96 session ID for verbose mode
func GetCTP96SessionID(containerID, networkID string) string {
	// Generate a deterministic session ID
	return fmt.Sprintf("ctp96_%s_%s", networkID[:8], containerID[:8])
}
