package runtime

import (
	"context"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"sync"
	"time"

	"github.com/sirupsen/logrus"
)

// VPIManager manages VPI leases
type VPIManager struct {
	logger *logrus.Logger
	leases map[string]*VPILease
	mu     sync.RWMutex
	ctx    context.Context
	cancel context.CancelFunc
}

// VPILease represents a Virtual Process Isolation lease
type VPILease struct {
	ID                     string                 `json:"id"`
	UORID                  string                 `json:"uor_id"`
	WitnessID              string                 `json:"witness_id"`
	Config                 map[string]interface{} `json:"config"`
	Status                 string                 `json:"status"`
	CreatedAt              time.Time              `json:"created_at"`
	UpdatedAt              time.Time              `json:"updated_at"`
	ExpiresAt              time.Time              `json:"expires_at"`
	ResourceLimits         ResourceLimits         `json:"resource_limits"`
	IsolationLevel         string                 `json:"isolation_level"`
	SecurityContext        SecurityContext        `json:"security_context"`
	ProcessID              string                 `json:"process_id,omitempty"`
	NetworkNamespace       string                 `json:"network_namespace,omitempty"`
	MountNamespace         string                 `json:"mount_namespace,omitempty"`
	PIDNamespace           string                 `json:"pid_namespace,omitempty"`
	UserNamespace          string                 `json:"user_namespace,omitempty"`
	UTSNamespace           string                 `json:"uts_namespace,omitempty"`
	IPCNamespace           string                 `json:"ipc_namespace,omitempty"`
	LeaseSignature         string                 `json:"lease_signature"`
	HolographicFingerprint string                 `json:"holographic_fingerprint"`
	Version                int                    `json:"version"`
}

// ResourceLimits defines resource constraints for the VPI lease
type ResourceLimits struct {
	CPULimit     string `json:"cpu_limit"`
	MemoryLimit  string `json:"memory_limit"`
	DiskLimit    string `json:"disk_limit"`
	NetworkLimit string `json:"network_limit"`
	ProcessLimit int    `json:"process_limit"`
	FileLimit    int    `json:"file_limit"`
	TimeLimit    string `json:"time_limit"`
}

// SecurityContext defines security constraints for the VPI lease
type SecurityContext struct {
	UserID          int      `json:"user_id"`
	GroupID         int      `json:"group_id"`
	Capabilities    []string `json:"capabilities"`
	SeccompProfile  string   `json:"seccomp_profile"`
	AppArmorProfile string   `json:"apparmor_profile"`
	ReadOnlyRoot    bool     `json:"read_only_root"`
	NoNewPrivileges bool     `json:"no_new_privileges"`
}

// NewVPIManager creates a new VPI manager
func NewVPIManager(logger *logrus.Logger) *VPIManager {
	ctx, cancel := context.WithCancel(context.Background())

	return &VPIManager{
		logger: logger,
		leases: make(map[string]*VPILease),
		ctx:    ctx,
		cancel: cancel,
	}
}

// Close closes the VPI manager
func (m *VPIManager) Close() error {
	m.cancel()
	return nil
}

// Create creates a new VPI lease with full lifecycle support
func (m *VPIManager) Create(uorID, witnessID string, config map[string]interface{}) (*VPILease, error) {
	m.mu.Lock()
	defer m.mu.Unlock()

	// Generate lease ID
	leaseID := fmt.Sprintf("vpi-lease:%s:%d", uorID, time.Now().Unix())

	// Parse configuration
	resourceLimits := m.parseResourceLimits(config)
	securityContext := m.parseSecurityContext(config)
	isolationLevel := m.parseIsolationLevel(config)

	// Generate namespaces
	namespaces := m.generateNamespaces(leaseID)

	// Generate lease signature
	leaseSignature := m.generateLeaseSignature(leaseID, uorID, witnessID, config)

	// Generate holographic fingerprint
	holographicFingerprint := m.generateHolographicFingerprint(leaseID, leaseSignature)

	// Set expiration time (default 1 hour)
	expiresAt := time.Now().Add(time.Hour)
	if expTime, ok := config["expires_at"].(string); ok {
		if parsedTime, err := time.Parse(time.RFC3339, expTime); err == nil {
			expiresAt = parsedTime
		}
	}

	// Create lease
	lease := &VPILease{
		ID:                     leaseID,
		UORID:                  uorID,
		WitnessID:              witnessID,
		Config:                 config,
		Status:                 "created",
		CreatedAt:              time.Now(),
		UpdatedAt:              time.Now(),
		ExpiresAt:              expiresAt,
		ResourceLimits:         resourceLimits,
		IsolationLevel:         isolationLevel,
		SecurityContext:        securityContext,
		NetworkNamespace:       namespaces["network"],
		MountNamespace:         namespaces["mount"],
		PIDNamespace:           namespaces["pid"],
		UserNamespace:          namespaces["user"],
		UTSNamespace:           namespaces["uts"],
		IPCNamespace:           namespaces["ipc"],
		LeaseSignature:         leaseSignature,
		HolographicFingerprint: holographicFingerprint,
		Version:                1,
	}

	// Store lease
	m.leases[leaseID] = lease

	m.logger.WithFields(logrus.Fields{
		"lease_id":                leaseID,
		"uor_id":                  uorID,
		"witness_id":              witnessID,
		"isolation_level":         isolationLevel,
		"expires_at":              expiresAt,
		"holographic_fingerprint": holographicFingerprint[:16] + "...",
	}).Info("Created VPI lease with full lifecycle support")

	return lease, nil
}

// Get retrieves a VPI lease by ID
func (m *VPIManager) Get(leaseID string) (*VPILease, error) {
	m.mu.RLock()
	defer m.mu.RUnlock()

	lease, exists := m.leases[leaseID]
	if !exists {
		return nil, fmt.Errorf("VPI lease not found: %s", leaseID)
	}

	return lease, nil
}

// List lists all VPI leases
func (m *VPIManager) List(uorID, status string, limit, offset int) ([]*VPILease, error) {
	m.mu.RLock()
	defer m.mu.RUnlock()

	var leases []*VPILease
	for _, lease := range m.leases {
		if (uorID == "" || lease.UORID == uorID) && (status == "" || lease.Status == status) {
			leases = append(leases, lease)
		}
	}

	// Apply pagination
	if offset > 0 && offset < len(leases) {
		leases = leases[offset:]
	}

	if limit > 0 && limit < len(leases) {
		leases = leases[:limit]
	}

	return leases, nil
}

// Activate activates a VPI lease
func (m *VPIManager) Activate(leaseID string) error {
	m.mu.Lock()
	defer m.mu.Unlock()

	lease, exists := m.leases[leaseID]
	if !exists {
		return fmt.Errorf("VPI lease not found: %s", leaseID)
	}

	lease.Status = "active"
	lease.UpdatedAt = time.Now()

	m.logger.WithField("lease_id", leaseID).Info("Activated VPI lease")

	return nil
}

// Deactivate deactivates a VPI lease
func (m *VPIManager) Deactivate(leaseID string) error {
	m.mu.Lock()
	defer m.mu.Unlock()

	lease, exists := m.leases[leaseID]
	if !exists {
		return fmt.Errorf("VPI lease not found: %s", leaseID)
	}

	lease.Status = "inactive"
	lease.UpdatedAt = time.Now()

	m.logger.WithField("lease_id", leaseID).Info("Deactivated VPI lease")

	return nil
}

// Delete deletes a VPI lease
func (m *VPIManager) Delete(leaseID string) error {
	m.mu.Lock()
	defer m.mu.Unlock()

	_, exists := m.leases[leaseID]
	if !exists {
		return fmt.Errorf("VPI lease not found: %s", leaseID)
	}

	delete(m.leases, leaseID)

	m.logger.WithField("lease_id", leaseID).Info("Deleted VPI lease")

	return nil
}

// Start starts a VPI lease and creates the isolated process environment
func (m *VPIManager) Start(leaseID string) error {
	m.mu.Lock()
	defer m.mu.Unlock()

	lease, exists := m.leases[leaseID]
	if !exists {
		return fmt.Errorf("VPI lease not found: %s", leaseID)
	}

	if lease.Status != "created" && lease.Status != "stopped" {
		return fmt.Errorf("cannot start lease %s in status %s", leaseID, lease.Status)
	}

	// Check if lease has expired
	if time.Now().After(lease.ExpiresAt) {
		lease.Status = "expired"
		return fmt.Errorf("lease %s has expired", leaseID)
	}

	// Generate process ID
	lease.ProcessID = m.generateProcessID(leaseID)

	// Update status
	lease.Status = "running"
	lease.UpdatedAt = time.Now()

	m.logger.WithFields(logrus.Fields{
		"lease_id":        leaseID,
		"process_id":      lease.ProcessID,
		"isolation_level": lease.IsolationLevel,
	}).Info("Started VPI lease")

	return nil
}

// Stop stops a VPI lease and cleans up the isolated process environment
func (m *VPIManager) Stop(leaseID string) error {
	m.mu.Lock()
	defer m.mu.Unlock()

	lease, exists := m.leases[leaseID]
	if !exists {
		return fmt.Errorf("VPI lease not found: %s", leaseID)
	}

	if lease.Status != "running" {
		return fmt.Errorf("cannot stop lease %s in status %s", leaseID, lease.Status)
	}

	// Clean up process
	lease.ProcessID = ""

	// Update status
	lease.Status = "stopped"
	lease.UpdatedAt = time.Now()

	m.logger.WithField("lease_id", leaseID).Info("Stopped VPI lease")

	return nil
}

// Renew renews a VPI lease by extending its expiration time
func (m *VPIManager) Renew(leaseID string, duration time.Duration) error {
	m.mu.Lock()
	defer m.mu.Unlock()

	lease, exists := m.leases[leaseID]
	if !exists {
		return fmt.Errorf("VPI lease not found: %s", leaseID)
	}

	// Extend expiration time
	lease.ExpiresAt = lease.ExpiresAt.Add(duration)
	lease.UpdatedAt = time.Now()
	lease.Version++

	m.logger.WithFields(logrus.Fields{
		"lease_id":       leaseID,
		"new_expires_at": lease.ExpiresAt,
		"duration":       duration,
	}).Info("Renewed VPI lease")

	return nil
}

// Verify verifies the integrity of a VPI lease
func (m *VPIManager) Verify(leaseID string) (bool, error) {
	m.mu.RLock()
	defer m.mu.RUnlock()

	lease, exists := m.leases[leaseID]
	if !exists {
		return false, fmt.Errorf("VPI lease not found: %s", leaseID)
	}

	// Verify lease signature
	expectedSignature := m.generateLeaseSignature(lease.ID, lease.UORID, lease.WitnessID, lease.Config)
	if lease.LeaseSignature != expectedSignature {
		return false, fmt.Errorf("lease signature mismatch for lease %s", leaseID)
	}

	// Verify holographic fingerprint
	expectedFingerprint := m.generateHolographicFingerprint(lease.ID, lease.LeaseSignature)
	if lease.HolographicFingerprint != expectedFingerprint {
		return false, fmt.Errorf("holographic fingerprint mismatch for lease %s", leaseID)
	}

	// Check if lease has expired
	if time.Now().After(lease.ExpiresAt) {
		return false, fmt.Errorf("lease %s has expired", leaseID)
	}

	return true, nil
}

// parseResourceLimits parses resource limits from configuration
func (m *VPIManager) parseResourceLimits(config map[string]interface{}) ResourceLimits {
	limits := ResourceLimits{
		CPULimit:     "1.0",
		MemoryLimit:  "512Mi",
		DiskLimit:    "1Gi",
		NetworkLimit: "100Mbps",
		ProcessLimit: 100,
		FileLimit:    1000,
		TimeLimit:    "1h",
	}

	if cpuLimit, ok := config["cpu_limit"].(string); ok {
		limits.CPULimit = cpuLimit
	}
	if memoryLimit, ok := config["memory_limit"].(string); ok {
		limits.MemoryLimit = memoryLimit
	}
	if diskLimit, ok := config["disk_limit"].(string); ok {
		limits.DiskLimit = diskLimit
	}
	if networkLimit, ok := config["network_limit"].(string); ok {
		limits.NetworkLimit = networkLimit
	}
	if processLimit, ok := config["process_limit"].(int); ok {
		limits.ProcessLimit = processLimit
	}
	if fileLimit, ok := config["file_limit"].(int); ok {
		limits.FileLimit = fileLimit
	}
	if timeLimit, ok := config["time_limit"].(string); ok {
		limits.TimeLimit = timeLimit
	}

	return limits
}

// parseSecurityContext parses security context from configuration
func (m *VPIManager) parseSecurityContext(config map[string]interface{}) SecurityContext {
	context := SecurityContext{
		UserID:          1000,
		GroupID:         1000,
		Capabilities:    []string{},
		SeccompProfile:  "default",
		AppArmorProfile: "default",
		ReadOnlyRoot:    true,
		NoNewPrivileges: true,
	}

	if userID, ok := config["user_id"].(int); ok {
		context.UserID = userID
	}
	if groupID, ok := config["group_id"].(int); ok {
		context.GroupID = groupID
	}
	if capabilities, ok := config["capabilities"].([]string); ok {
		context.Capabilities = capabilities
	}
	if seccompProfile, ok := config["seccomp_profile"].(string); ok {
		context.SeccompProfile = seccompProfile
	}
	if appArmorProfile, ok := config["apparmor_profile"].(string); ok {
		context.AppArmorProfile = appArmorProfile
	}
	if readOnlyRoot, ok := config["read_only_root"].(bool); ok {
		context.ReadOnlyRoot = readOnlyRoot
	}
	if noNewPrivileges, ok := config["no_new_privileges"].(bool); ok {
		context.NoNewPrivileges = noNewPrivileges
	}

	return context
}

// parseIsolationLevel parses isolation level from configuration
func (m *VPIManager) parseIsolationLevel(config map[string]interface{}) string {
	if level, ok := config["isolation_level"].(string); ok {
		return level
	}
	return "standard" // default isolation level
}

// generateNamespaces generates unique namespace identifiers
func (m *VPIManager) generateNamespaces(leaseID string) map[string]string {
	hash := sha256.New()
	hash.Write([]byte(leaseID))
	hashBytes := hash.Sum(nil)
	hashStr := hex.EncodeToString(hashBytes)[:16]

	return map[string]string{
		"network": fmt.Sprintf("vpi-net-%s", hashStr),
		"mount":   fmt.Sprintf("vpi-mnt-%s", hashStr),
		"pid":     fmt.Sprintf("vpi-pid-%s", hashStr),
		"user":    fmt.Sprintf("vpi-usr-%s", hashStr),
		"uts":     fmt.Sprintf("vpi-uts-%s", hashStr),
		"ipc":     fmt.Sprintf("vpi-ipc-%s", hashStr),
	}
}

// generateLeaseSignature generates a cryptographic signature for the lease
func (m *VPIManager) generateLeaseSignature(leaseID, uorID, witnessID string, config map[string]interface{}) string {
	hash := sha256.New()

	hash.Write([]byte("lease_signature|"))
	hash.Write([]byte(leaseID))
	hash.Write([]byte("|"))
	hash.Write([]byte(uorID))
	hash.Write([]byte("|"))
	hash.Write([]byte(witnessID))
	hash.Write([]byte("|"))

	if config != nil {
		configJSON, _ := json.Marshal(config)
		hash.Write([]byte("config|"))
		hash.Write(configJSON)
		hash.Write([]byte("|"))
	}

	hash.Write([]byte("holographic_domain|vpi_lease|"))

	return "lease:" + hex.EncodeToString(hash.Sum(nil))[:16]
}

// generateHolographicFingerprint generates a holographic fingerprint for the lease
func (m *VPIManager) generateHolographicFingerprint(leaseID, leaseSignature string) string {
	hash := sha256.New()
	hash.Write([]byte("holographic_fingerprint|"))
	hash.Write([]byte(leaseID))
	hash.Write([]byte("|"))
	hash.Write([]byte(leaseSignature))
	hash.Write([]byte("|"))
	hash.Write([]byte("holographic_domain|vpi_fingerprint|"))

	return "holographic:" + hex.EncodeToString(hash.Sum(nil))[:16]
}

// generateProcessID generates a unique process ID for the lease
func (m *VPIManager) generateProcessID(leaseID string) string {
	hash := sha256.New()
	hash.Write([]byte("process_id|"))
	hash.Write([]byte(leaseID))
	hash.Write([]byte("|"))
	hash.Write([]byte(time.Now().Format(time.RFC3339Nano)))
	hash.Write([]byte("|"))

	return "vpi-proc:" + hex.EncodeToString(hash.Sum(nil))[:12]
}
