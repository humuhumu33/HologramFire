package runtime

import (
	"sync"
	"time"
)

// ContainerState represents the state of a container
type ContainerState struct {
	ID              string
	Name            string
	Image           string
	Created         string // RFC3339
	StartedAt       string
	FinishedAt      string
	Running         bool
	OOMKilled       bool
	ExitCode        int
	Pid             int
	HostConfig      map[string]any // store docker-shaped fields
	Config          map[string]any // docker-shaped container config
	NetworkSettings map[string]any
	XHologram       map[string]any // internal; attach via guards when verbose
}

// Store manages container state
type Store struct {
	mu  sync.RWMutex
	ctr map[string]*ContainerState
}

// NewStore creates a new container state store
func NewStore() *Store {
	return &Store{
		ctr: make(map[string]*ContainerState),
	}
}

// Put stores a container state
func (s *Store) Put(c *ContainerState) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.ctr[c.ID] = c
}

// Get retrieves a container state by ID
func (s *Store) Get(id string) (*ContainerState, bool) {
	s.mu.RLock()
	defer s.mu.RUnlock()
	c, ok := s.ctr[id]
	return c, ok
}

// Del removes a container state by ID
func (s *Store) Del(id string) {
	s.mu.Lock()
	defer s.mu.Unlock()
	delete(s.ctr, id)
}

// List returns all container states
func (s *Store) List() []*ContainerState {
	s.mu.RLock()
	defer s.mu.RUnlock()

	containers := make([]*ContainerState, 0, len(s.ctr))
	for _, c := range s.ctr {
		containers = append(containers, c)
	}
	return containers
}

// UpdateState updates container state fields
func (s *Store) UpdateState(id string, updates map[string]any) bool {
	s.mu.Lock()
	defer s.mu.Unlock()

	c, ok := s.ctr[id]
	if !ok {
		return false
	}

	// Update fields based on the updates map
	if running, ok := updates["Running"].(bool); ok {
		c.Running = running
		if running {
			c.StartedAt = time.Now().Format(time.RFC3339Nano)
		} else {
			c.FinishedAt = time.Now().Format(time.RFC3339Nano)
		}
	}

	if exitCode, ok := updates["ExitCode"].(int); ok {
		c.ExitCode = exitCode
	}

	if pid, ok := updates["Pid"].(int); ok {
		c.Pid = pid
	}

	if oomKilled, ok := updates["OOMKilled"].(bool); ok {
		c.OOMKilled = oomKilled
	}

	return true
}
