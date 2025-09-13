package modes

import (
	"context"
	"fmt"
	"os"
	"strconv"
	"strings"

	"github.com/containerd/containerd/log"
	ocispec "github.com/opencontainers/image-spec/specs-go/v1"
)

// Modes manages hologram operation modes
type Modes struct {
	enforce bool
	verbose bool
	net     string
}

// NewModes creates a new modes instance from environment variables
func NewModes() *Modes {
	return &Modes{
		enforce: getBoolEnv("HOLOGRAM_ENFORCE", false),
		verbose: getBoolEnv("HOLOGRAM_VERBOSE", false),
		net:     getStringEnv("HOLOGRAM_NET", "ctp96"),
	}
}

// IsEnforce returns true if enforce mode is enabled
func (m *Modes) IsEnforce() bool {
	return m.enforce
}

// IsVerbose returns true if verbose mode is enabled
func (m *Modes) IsVerbose() bool {
	return m.verbose
}

// GetNetwork returns the network mode
func (m *Modes) GetNetwork() string {
	return m.net
}

// AddHologramAnnotations adds hologram-specific annotations to a descriptor
func (m *Modes) AddHologramAnnotations(ctx context.Context, desc *ocispec.Descriptor, uorID string, witnessOK bool, leaseID string, ctp96Session string) {
	if !m.verbose {
		return
	}

	if desc.Annotations == nil {
		desc.Annotations = make(map[string]string)
	}

	// Add hologram metadata
	desc.Annotations["hologram.uor_id"] = uorID
	desc.Annotations["hologram.witness_ok"] = strconv.FormatBool(witnessOK)
	desc.Annotations["hologram.lease_id"] = leaseID
	desc.Annotations["hologram.ctp96_session"] = ctp96Session
	desc.Annotations["hologram.enforce_mode"] = strconv.FormatBool(m.enforce)
	desc.Annotations["hologram.verbose_mode"] = strconv.FormatBool(m.verbose)
	desc.Annotations["hologram.network"] = m.net

	log.G(ctx).WithFields(map[string]interface{}{
		"uor_id":        uorID,
		"witness_ok":    witnessOK,
		"lease_id":      leaseID,
		"ctp96_session": ctp96Session,
		"enforce":       m.enforce,
		"verbose":       m.verbose,
		"net":           m.net,
	}).Debug("Added hologram annotations")
}

// ValidateEnforceMode validates operations in enforce mode
func (m *Modes) ValidateEnforceMode(ctx context.Context, operation string, uorID string, witnessOK bool) error {
	if !m.enforce {
		return nil
	}

	if !witnessOK {
		log.G(ctx).WithFields(map[string]interface{}{
			"operation": operation,
			"uor_id":    uorID,
			"enforce":   true,
		}).Error("Operation blocked in enforce mode: witness verification failed")
		return fmt.Errorf("operation blocked in enforce mode: witness verification failed for UOR-ID %s", uorID)
	}

	log.G(ctx).WithFields(map[string]interface{}{
		"operation": operation,
		"uor_id":    uorID,
		"enforce":   true,
	}).Debug("Operation allowed in enforce mode: witness verification passed")

	return nil
}

// LogVerbose logs verbose information if verbose mode is enabled
func (m *Modes) LogVerbose(ctx context.Context, level string, message string, fields map[string]interface{}) {
	if !m.verbose {
		return
	}

	// Add mode information to fields
	if fields == nil {
		fields = make(map[string]interface{})
	}
	fields["hologram_mode"] = "verbose"
	fields["hologram_enforce"] = m.enforce
	fields["hologram_net"] = m.net

	switch strings.ToLower(level) {
	case "debug":
		log.G(ctx).WithFields(fields).Debug(message)
	case "info":
		log.G(ctx).WithFields(fields).Info(message)
	case "warn":
		log.G(ctx).WithFields(fields).Warn(message)
	case "error":
		log.G(ctx).WithFields(fields).Error(message)
	default:
		log.G(ctx).WithFields(fields).Info(message)
	}
}

// GetModeInfo returns information about current modes
func (m *Modes) GetModeInfo() map[string]interface{} {
	return map[string]interface{}{
		"enforce": m.enforce,
		"verbose": m.verbose,
		"net":     m.net,
	}
}

// getBoolEnv gets a boolean environment variable
func getBoolEnv(key string, defaultValue bool) bool {
	if value := os.Getenv(key); value != "" {
		if parsed, err := strconv.ParseBool(value); err == nil {
			return parsed
		}
	}
	return defaultValue
}

// getStringEnv gets a string environment variable
func getStringEnv(key, defaultValue string) string {
	if value := os.Getenv(key); value != "" {
		return value
	}
	return defaultValue
}
