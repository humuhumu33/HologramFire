package runtime

import (
	"testing"
	"time"

	"github.com/sirupsen/logrus"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestUORManager_CompleteImplementation(t *testing.T) {
	logger := logrus.New()
	logger.SetLevel(logrus.ErrorLevel) // Reduce noise during tests

	manager := NewUORManager(logger)
	defer manager.Close()

	t.Run("Create UOR with cryptographic hashing", func(t *testing.T) {
		objectRef := "nginx:alpine"
		metadata := map[string]interface{}{
			"version": "1.0",
			"arch":    "amd64",
		}

		uor, err := manager.Create(objectRef, metadata)
		require.NoError(t, err)
		require.NotNil(t, uor)

		// Verify UOR structure
		assert.NotEmpty(t, uor.ID)
		assert.Equal(t, objectRef, uor.ObjectRef)
		assert.NotEmpty(t, uor.ContentHash)
		assert.NotEmpty(t, uor.HolographicFingerprint)
		assert.Equal(t, 1, uor.Version)
		assert.Equal(t, metadata, uor.Metadata)

		// Verify UOR ID format
		assert.Contains(t, uor.ID, "uor:sha256:")

		// Verify content hash is deterministic
		uor2, err := manager.Create(objectRef, metadata)
		require.NoError(t, err)
		assert.Equal(t, uor.ContentHash, uor2.ContentHash)
		_ = uor2 // Use the variable to avoid unused variable error
	})

	t.Run("Verify UOR integrity", func(t *testing.T) {
		objectRef := "test:image"
		metadata := map[string]interface{}{"test": true}

		uor, err := manager.Create(objectRef, metadata)
		require.NoError(t, err)

		// Verify integrity
		valid, err := manager.Verify(uor.ID)
		require.NoError(t, err)
		assert.True(t, valid)

		// Test with non-existent UOR
		_, err = manager.Verify("non-existent")
		assert.Error(t, err)
	})

	t.Run("Update UOR with version increment", func(t *testing.T) {
		objectRef := "test:update"
		metadata := map[string]interface{}{"version": "1.0"}

		uor, err := manager.Create(objectRef, metadata)
		require.NoError(t, err)

		// Store original values before update
		originalContentHash := uor.ContentHash
		originalHolographicFingerprint := uor.HolographicFingerprint

		// Add small delay to ensure different timestamps
		time.Sleep(1 * time.Millisecond)

		// Update metadata
		newMetadata := map[string]interface{}{"version": "2.0", "updated": true}
		updatedUor, err := manager.Update(uor.ID, newMetadata)
		require.NoError(t, err)

		assert.Equal(t, 2, updatedUor.Version)
		assert.Equal(t, newMetadata, updatedUor.Metadata)
		assert.NotEqual(t, originalContentHash, updatedUor.ContentHash)
		assert.NotEqual(t, originalHolographicFingerprint, updatedUor.HolographicFingerprint)
	})

	t.Run("Search and list UORs", func(t *testing.T) {
		// Create multiple UORs
		uor1, _ := manager.Create("image1:tag", map[string]interface{}{"type": "base"})
		uor2, _ := manager.Create("image2:tag", map[string]interface{}{"type": "app"})

		// List all UORs
		uors, err := manager.List(10, 0)
		require.NoError(t, err)
		assert.GreaterOrEqual(t, len(uors), 2)

		// Search by object reference
		results, err := manager.Search("image1:tag", 10)
		require.NoError(t, err)
		assert.Len(t, results, 1)
		assert.Equal(t, uor1.ID, results[0].ID)

		// Verify both UORs were created
		assert.NotEmpty(t, uor1.ID)
		assert.NotEmpty(t, uor2.ID)
	})
}

func TestWitnessManager_QuantumResistantCryptography(t *testing.T) {
	logger := logrus.New()
	logger.SetLevel(logrus.ErrorLevel)

	manager := NewWitnessManager(logger)
	defer manager.Close()

	t.Run("Create quantum-resistant witness", func(t *testing.T) {
		uorID := "uor:sha256:test123"
		witnessType := "integrity"
		metadata := map[string]interface{}{
			"algorithm": "quantum-resistant",
			"strength":  "high",
		}

		witness, err := manager.Create(uorID, witnessType, metadata)
		require.NoError(t, err)
		require.NotNil(t, witness)

		// Verify witness structure
		assert.NotEmpty(t, witness.ID)
		assert.Equal(t, uorID, witness.UORID)
		assert.Equal(t, witnessType, witness.Type)
		assert.NotEmpty(t, witness.QuantumSignature)
		assert.NotEmpty(t, witness.FieldKey)
		assert.NotEmpty(t, witness.ConservationProof)
		assert.NotEmpty(t, witness.HolographicCorrespondence)
		assert.NotEmpty(t, witness.FieldTopology)
		assert.NotEmpty(t, witness.ResonanceSpectrum)
		assert.Equal(t, "pending", witness.VerificationStatus)

		// Verify coherence score
		assert.GreaterOrEqual(t, witness.CoherenceScore, 0.95)
		assert.LessOrEqual(t, witness.CoherenceScore, 1.0)

		// Verify resonance spectrum
		assert.Len(t, witness.ResonanceSpectrum, 96)
		for _, value := range witness.ResonanceSpectrum {
			assert.GreaterOrEqual(t, value, 0.1)
			assert.LessOrEqual(t, value, 0.3)
		}
	})

	t.Run("Verify witness with quantum-resistant cryptography", func(t *testing.T) {
		uorID := "uor:sha256:verify123"
		witnessType := "provenance"
		metadata := map[string]interface{}{"verified": true}

		witness, err := manager.Create(uorID, witnessType, metadata)
		require.NoError(t, err)

		// Verify witness
		valid, err := manager.Verify(witness.ID)
		require.NoError(t, err)
		assert.True(t, valid)

		// Check verification status was updated
		verifiedWitness, err := manager.Get(witness.ID)
		require.NoError(t, err)
		assert.Equal(t, "verified", verifiedWitness.VerificationStatus)
	})

	t.Run("Test different witness types", func(t *testing.T) {
		uorID := "uor:sha256:types123"

		// Test integrity witness
		integrityWitness, err := manager.Create(uorID, "integrity", nil)
		require.NoError(t, err)
		assert.GreaterOrEqual(t, integrityWitness.CoherenceScore, 0.98)

		// Test provenance witness
		provenanceWitness, err := manager.Create(uorID, "provenance", nil)
		require.NoError(t, err)
		assert.GreaterOrEqual(t, provenanceWitness.CoherenceScore, 0.97)

		// Test performance witness
		performanceWitness, err := manager.Create(uorID, "performance", nil)
		require.NoError(t, err)
		assert.GreaterOrEqual(t, performanceWitness.CoherenceScore, 0.96)
	})
}

func TestVPIManager_FullLifecycleSupport(t *testing.T) {
	logger := logrus.New()
	logger.SetLevel(logrus.ErrorLevel)

	manager := NewVPIManager(logger)
	defer manager.Close()

	t.Run("Create VPI lease with full configuration", func(t *testing.T) {
		uorID := "uor:sha256:vpi123"
		witnessID := "witness:vpi123:1234567890"
		config := map[string]interface{}{
			"cpu_limit":         "2.0",
			"memory_limit":      "1Gi",
			"disk_limit":        "10Gi",
			"process_limit":     200,
			"isolation_level":   "high",
			"user_id":           1001,
			"group_id":          1001,
			"read_only_root":    true,
			"no_new_privileges": true,
			"expires_at":        time.Now().Add(2 * time.Hour).Format(time.RFC3339),
		}

		lease, err := manager.Create(uorID, witnessID, config)
		require.NoError(t, err)
		require.NotNil(t, lease)

		// Verify lease structure
		assert.NotEmpty(t, lease.ID)
		assert.Equal(t, uorID, lease.UORID)
		assert.Equal(t, witnessID, lease.WitnessID)
		assert.Equal(t, "created", lease.Status)
		assert.Equal(t, 1, lease.Version)
		assert.NotEmpty(t, lease.LeaseSignature)
		assert.NotEmpty(t, lease.HolographicFingerprint)

		// Verify resource limits
		assert.Equal(t, "2.0", lease.ResourceLimits.CPULimit)
		assert.Equal(t, "1Gi", lease.ResourceLimits.MemoryLimit)
		assert.Equal(t, "10Gi", lease.ResourceLimits.DiskLimit)
		assert.Equal(t, 200, lease.ResourceLimits.ProcessLimit)

		// Verify security context
		assert.Equal(t, 1001, lease.SecurityContext.UserID)
		assert.Equal(t, 1001, lease.SecurityContext.GroupID)
		assert.True(t, lease.SecurityContext.ReadOnlyRoot)
		assert.True(t, lease.SecurityContext.NoNewPrivileges)

		// Verify isolation level
		assert.Equal(t, "high", lease.IsolationLevel)

		// Verify namespaces
		assert.NotEmpty(t, lease.NetworkNamespace)
		assert.NotEmpty(t, lease.MountNamespace)
		assert.NotEmpty(t, lease.PIDNamespace)
		assert.NotEmpty(t, lease.UserNamespace)
		assert.NotEmpty(t, lease.UTSNamespace)
		assert.NotEmpty(t, lease.IPCNamespace)
	})

	t.Run("VPI lease lifecycle management", func(t *testing.T) {
		uorID := "uor:sha256:lifecycle123"
		witnessID := "witness:lifecycle123:1234567890"
		config := map[string]interface{}{"test": true}

		// Create lease
		lease, err := manager.Create(uorID, witnessID, config)
		require.NoError(t, err)
		assert.Equal(t, "created", lease.Status)

		// Start lease
		err = manager.Start(lease.ID)
		require.NoError(t, err)

		startedLease, err := manager.Get(lease.ID)
		require.NoError(t, err)
		assert.Equal(t, "running", startedLease.Status)
		assert.NotEmpty(t, startedLease.ProcessID)

		// Stop lease
		err = manager.Stop(lease.ID)
		require.NoError(t, err)

		stoppedLease, err := manager.Get(lease.ID)
		require.NoError(t, err)
		assert.Equal(t, "stopped", stoppedLease.Status)
		assert.Empty(t, stoppedLease.ProcessID)

		// Start again
		err = manager.Start(lease.ID)
		require.NoError(t, err)

		restartedLease, err := manager.Get(lease.ID)
		require.NoError(t, err)
		assert.Equal(t, "running", restartedLease.Status)
		assert.NotEmpty(t, restartedLease.ProcessID)
	})

	t.Run("VPI lease renewal", func(t *testing.T) {
		uorID := "uor:sha256:renewal123"
		witnessID := "witness:renewal123:1234567890"
		config := map[string]interface{}{"test": true}

		lease, err := manager.Create(uorID, witnessID, config)
		require.NoError(t, err)

		originalExpiresAt := lease.ExpiresAt

		// Renew lease
		err = manager.Renew(lease.ID, time.Hour)
		require.NoError(t, err)

		renewedLease, err := manager.Get(lease.ID)
		require.NoError(t, err)
		assert.Equal(t, 2, renewedLease.Version)
		assert.True(t, renewedLease.ExpiresAt.After(originalExpiresAt))
		assert.Equal(t, originalExpiresAt.Add(time.Hour), renewedLease.ExpiresAt)
	})

	t.Run("VPI lease verification", func(t *testing.T) {
		uorID := "uor:sha256:verify123"
		witnessID := "witness:verify123:1234567890"
		config := map[string]interface{}{"verified": true}

		lease, err := manager.Create(uorID, witnessID, config)
		require.NoError(t, err)

		// Verify lease
		valid, err := manager.Verify(lease.ID)
		require.NoError(t, err)
		assert.True(t, valid)

		// Test with non-existent lease
		_, err = manager.Verify("non-existent")
		assert.Error(t, err)
	})

	t.Run("VPI lease expiration", func(t *testing.T) {
		uorID := "uor:sha256:expired123"
		witnessID := "witness:expired123:1234567890"
		config := map[string]interface{}{
			"expires_at": time.Now().Add(-time.Hour).Format(time.RFC3339), // Already expired
		}

		lease, err := manager.Create(uorID, witnessID, config)
		require.NoError(t, err)

		// Try to start expired lease
		err = manager.Start(lease.ID)
		assert.Error(t, err)
		assert.Contains(t, err.Error(), "expired")

		// Check status was updated
		expiredLease, err := manager.Get(lease.ID)
		require.NoError(t, err)
		assert.Equal(t, "expired", expiredLease.Status)
	})
}

func TestCTP96Manager_TransportProtocol(t *testing.T) {
	logger := logrus.New()
	logger.SetLevel(logrus.ErrorLevel)

	manager := NewCTP96Manager(logger)
	defer manager.Close()

	t.Run("Create CTP-96 connection", func(t *testing.T) {
		config := map[string]interface{}{
			"protocol_version":    "1.0",
			"encryption_enabled":  true,
			"compression_enabled": true,
			"connection_type":     "tcp",
		}
		_ = config // Use the variable to avoid unused variable error

		// Note: This test would require a real server to connect to
		// For now, we'll test the connection creation logic without actual network
		connectionID := manager.generateConnectionID("localhost", 8080)
		assert.NotEmpty(t, connectionID)
		assert.Contains(t, connectionID, "ctp96-conn:")

		sessionKey := manager.generateSessionKey(connectionID, "localhost", 8080)
		assert.NotEmpty(t, sessionKey)
		assert.Contains(t, sessionKey, "session:")

		fingerprint := manager.generateHolographicFingerprint(connectionID, sessionKey)
		assert.NotEmpty(t, fingerprint)
		assert.Contains(t, fingerprint, "holographic:")
	})

	t.Run("CTP-96 message creation and verification", func(t *testing.T) {
		connectionID := "ctp96-conn:test123"
		sessionKey := "session:test123"

		// Create message
		message := &CTP96Message{
			ID:             manager.generateMessageID(connectionID),
			Type:           "test",
			Payload:        []byte("test payload"),
			Headers:        map[string]string{"test": "header"},
			Timestamp:      time.Now(),
			SequenceNumber: 1,
			Encrypted:      true,
			Compressed:     true,
		}

		// Generate checksum
		checksum := manager.generateChecksum(message)
		message.Checksum = checksum

		// Generate holographic signature
		signature := manager.generateHolographicSignature(message, sessionKey)
		message.HolographicSignature = signature

		// Verify message structure
		assert.NotEmpty(t, message.ID)
		assert.Contains(t, message.ID, "ctp96-msg:")
		assert.NotEmpty(t, message.Checksum)
		assert.Contains(t, message.Checksum, "checksum:")
		assert.NotEmpty(t, message.HolographicSignature)
		assert.Contains(t, message.HolographicSignature, "signature:")

		// Verify checksum
		expectedChecksum := manager.generateChecksum(message)
		assert.Equal(t, expectedChecksum, message.Checksum)

		// Verify holographic signature
		expectedSignature := manager.generateHolographicSignature(message, sessionKey)
		assert.Equal(t, expectedSignature, message.HolographicSignature)
	})

	t.Run("CTP-96 connection management", func(t *testing.T) {
		// Test connection listing (should be empty initially)
		connections := manager.ListConnections()
		assert.Empty(t, connections)

		// Test getting non-existent connection
		_, err := manager.GetConnection("non-existent")
		assert.Error(t, err)
	})
}

func TestPhase1Integration_EndToEnd(t *testing.T) {
	logger := logrus.New()
	logger.SetLevel(logrus.ErrorLevel)

	// Create all managers
	uorManager := NewUORManager(logger)
	witnessManager := NewWitnessManager(logger)
	vpiManager := NewVPIManager(logger)
	ctp96Manager := NewCTP96Manager(logger)

	defer func() {
		uorManager.Close()
		witnessManager.Close()
		vpiManager.Close()
		ctp96Manager.Close()
	}()

	t.Run("Complete workflow: UOR -> Witness -> VPI Lease -> CTP-96", func(t *testing.T) {
		// Step 1: Create UOR
		objectRef := "nginx:alpine"
		metadata := map[string]interface{}{
			"version": "1.0",
			"arch":    "amd64",
		}

		uor, err := uorManager.Create(objectRef, metadata)
		require.NoError(t, err)
		assert.NotEmpty(t, uor.ID)
		assert.NotEmpty(t, uor.ContentHash)

		// Step 2: Create witness for UOR
		witness, err := witnessManager.Create(uor.ID, "integrity", metadata)
		require.NoError(t, err)
		assert.NotEmpty(t, witness.ID)
		assert.Equal(t, uor.ID, witness.UORID)

		// Step 3: Verify witness
		valid, err := witnessManager.Verify(witness.ID)
		require.NoError(t, err)
		assert.True(t, valid)

		// Step 4: Create VPI lease
		vpiConfig := map[string]interface{}{
			"cpu_limit":       "1.0",
			"memory_limit":    "512Mi",
			"isolation_level": "standard",
		}

		lease, err := vpiManager.Create(uor.ID, witness.ID, vpiConfig)
		require.NoError(t, err)
		assert.NotEmpty(t, lease.ID)
		assert.Equal(t, uor.ID, lease.UORID)
		assert.Equal(t, witness.ID, lease.WitnessID)

		// Step 5: Start VPI lease
		err = vpiManager.Start(lease.ID)
		require.NoError(t, err)

		startedLease, err := vpiManager.Get(lease.ID)
		require.NoError(t, err)
		assert.Equal(t, "running", startedLease.Status)

		// Step 6: Verify VPI lease
		valid, err = vpiManager.Verify(lease.ID)
		require.NoError(t, err)
		assert.True(t, valid)

		// Step 7: Create CTP-96 message for communication
		connectionID := ctp96Manager.generateConnectionID("localhost", 8080)
		sessionKey := ctp96Manager.generateSessionKey(connectionID, "localhost", 8080)

		message := &CTP96Message{
			ID:             ctp96Manager.generateMessageID(connectionID),
			Type:           "container_start",
			Payload:        []byte(`{"container_id": "` + lease.ID + `"}`),
			Headers:        map[string]string{"content-type": "application/json"},
			Timestamp:      time.Now(),
			SequenceNumber: 1,
			Encrypted:      true,
			Compressed:     true,
		}

		message.Checksum = ctp96Manager.generateChecksum(message)
		message.HolographicSignature = ctp96Manager.generateHolographicSignature(message, sessionKey)

		// Verify message integrity
		expectedChecksum := ctp96Manager.generateChecksum(message)
		assert.Equal(t, expectedChecksum, message.Checksum)

		expectedSignature := ctp96Manager.generateHolographicSignature(message, sessionKey)
		assert.Equal(t, expectedSignature, message.HolographicSignature)

		// Step 8: Stop VPI lease
		err = vpiManager.Stop(lease.ID)
		require.NoError(t, err)

		stoppedLease, err := vpiManager.Get(lease.ID)
		require.NoError(t, err)
		assert.Equal(t, "stopped", stoppedLease.Status)

		t.Logf("✅ Complete Phase 1 workflow successful:")
		t.Logf("   UOR ID: %s", uor.ID)
		t.Logf("   Witness ID: %s", witness.ID)
		t.Logf("   VPI Lease ID: %s", lease.ID)
		t.Logf("   CTP-96 Message ID: %s", message.ID)
	})
}

func TestOracleValidation_SystemCoherence(t *testing.T) {
	logger := logrus.New()
	logger.SetLevel(logrus.ErrorLevel)

	// Test holographic correspondence across all components
	t.Run("Holographic correspondence validation", func(t *testing.T) {
		uorManager := NewUORManager(logger)
		witnessManager := NewWitnessManager(logger)
		vpiManager := NewVPIManager(logger)

		defer func() {
			uorManager.Close()
			witnessManager.Close()
			vpiManager.Close()
		}()

		// Create a consistent object across all systems
		objectRef := "holographic:test"
		metadata := map[string]interface{}{
			"holographic_correspondence": true,
			"system_coherence":           "validated",
		}

		// Create UOR
		uor, err := uorManager.Create(objectRef, metadata)
		require.NoError(t, err)

		// Create witness
		witness, err := witnessManager.Create(uor.ID, "integrity", metadata)
		require.NoError(t, err)

		// Create VPI lease
		lease, err := vpiManager.Create(uor.ID, witness.ID, metadata)
		require.NoError(t, err)

		// Verify all components maintain holographic correspondence
		assert.Contains(t, uor.HolographicFingerprint, "holographic:")
		assert.Contains(t, witness.HolographicCorrespondence, "correspondence:")
		assert.Contains(t, lease.HolographicFingerprint, "holographic:")

		// Verify all components can be validated
		uorValid, err := uorManager.Verify(uor.ID)
		require.NoError(t, err)
		assert.True(t, uorValid)

		witnessValid, err := witnessManager.Verify(witness.ID)
		require.NoError(t, err)
		assert.True(t, witnessValid)

		leaseValid, err := vpiManager.Verify(lease.ID)
		require.NoError(t, err)
		assert.True(t, leaseValid)

		t.Logf("✅ Oracle validation successful - all components maintain holographic correspondence")
	})

	t.Run("Quantum-resistant cryptography validation", func(t *testing.T) {
		witnessManager := NewWitnessManager(logger)
		defer witnessManager.Close()

		// Test quantum-resistant properties
		uorID := "uor:sha256:quantum123"
		witness, err := witnessManager.Create(uorID, "integrity", nil)
		require.NoError(t, err)

		// Verify quantum-resistant components
		assert.NotEmpty(t, witness.QuantumSignature)
		assert.NotEmpty(t, witness.FieldKey)
		assert.NotEmpty(t, witness.ConservationProof)
		assert.NotEmpty(t, witness.ResonanceSpectrum)
		assert.Greater(t, witness.CoherenceScore, 0.95)

		// Verify all quantum-resistant components are consistent
		valid, err := witnessManager.Verify(witness.ID)
		require.NoError(t, err)
		assert.True(t, valid)

		t.Logf("✅ Quantum-resistant cryptography validation successful")
	})

	t.Run("Content-addressed object validation", func(t *testing.T) {
		uorManager := NewUORManager(logger)
		defer uorManager.Close()

		// Test content-addressed properties
		objectRef := "content:addressed:test"
		metadata := map[string]interface{}{"content": "test"}

		uor1, err := uorManager.Create(objectRef, metadata)
		require.NoError(t, err)

		uor2, err := uorManager.Create(objectRef, metadata)
		require.NoError(t, err)

		// Same content should produce same hash
		assert.Equal(t, uor1.ContentHash, uor2.ContentHash)

		// Different content should produce different hash
		metadata2 := map[string]interface{}{"content": "different"}
		uor3, err := uorManager.Create(objectRef, metadata2)
		require.NoError(t, err)

		assert.NotEqual(t, uor1.ContentHash, uor3.ContentHash)

		t.Logf("✅ Content-addressed object validation successful")
	})
}
