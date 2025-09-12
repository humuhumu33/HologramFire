package telemetry

import (
	"context"
	"sync"
	"time"

	"github.com/containerd/containerd/log"
	"github.com/prometheus/client_golang/prometheus"
	"github.com/prometheus/client_golang/prometheus/promauto"
)

var (
	// Global telemetry instance
	globalTelemetry *Telemetry
	initOnce        sync.Once
)

// Telemetry tracks metrics for the hologram snapshotter
type Telemetry struct {
	// Prometheus metrics
	snapshotterOps     *prometheus.CounterVec
	snapshotterLatency *prometheus.HistogramVec
	fuseOps            *prometheus.CounterVec
	fuseLatency        *prometheus.HistogramVec
	resolverOps        *prometheus.CounterVec
	resolverLatency    *prometheus.HistogramVec
	witnessOps         *prometheus.CounterVec
	witnessLatency     *prometheus.HistogramVec
	ctp96Ops           *prometheus.CounterVec
	ctp96Latency       *prometheus.HistogramVec
	contentOps         *prometheus.CounterVec
	contentLatency     *prometheus.HistogramVec
	energyHints        *prometheus.GaugeVec
	leaseDuration      *prometheus.HistogramVec

	// Internal counters
	mu sync.RWMutex
}

// Init initializes the global telemetry instance
func Init() {
	initOnce.Do(func() {
		globalTelemetry = NewTelemetry()
	})
}

// NewTelemetry creates a new telemetry instance
func NewTelemetry() *Telemetry {
	return &Telemetry{
		snapshotterOps: promauto.NewCounterVec(
			prometheus.CounterOpts{
				Name: "hologram_snapshotter_operations_total",
				Help: "Total number of snapshotter operations",
			},
			[]string{"operation", "status"},
		),
		snapshotterLatency: promauto.NewHistogramVec(
			prometheus.HistogramOpts{
				Name:    "hologram_snapshotter_operation_duration_seconds",
				Help:    "Duration of snapshotter operations",
				Buckets: prometheus.DefBuckets,
			},
			[]string{"operation"},
		),
		fuseOps: promauto.NewCounterVec(
			prometheus.CounterOpts{
				Name: "hologram_fuse_operations_total",
				Help: "Total number of FUSE operations",
			},
			[]string{"operation", "status"},
		),
		fuseLatency: promauto.NewHistogramVec(
			prometheus.HistogramOpts{
				Name:    "hologram_fuse_operation_duration_seconds",
				Help:    "Duration of FUSE operations",
				Buckets: prometheus.DefBuckets,
			},
			[]string{"operation"},
		),
		resolverOps: promauto.NewCounterVec(
			prometheus.CounterOpts{
				Name: "hologram_resolver_operations_total",
				Help: "Total number of resolver operations",
			},
			[]string{"operation", "status"},
		),
		resolverLatency: promauto.NewHistogramVec(
			prometheus.HistogramOpts{
				Name:    "hologram_resolver_operation_duration_seconds",
				Help:    "Duration of resolver operations",
				Buckets: prometheus.DefBuckets,
			},
			[]string{"operation"},
		),
		witnessOps: promauto.NewCounterVec(
			prometheus.CounterOpts{
				Name: "hologram_witness_operations_total",
				Help: "Total number of witness operations",
			},
			[]string{"operation", "status"},
		),
		witnessLatency: promauto.NewHistogramVec(
			prometheus.HistogramOpts{
				Name:    "hologram_witness_operation_duration_seconds",
				Help:    "Duration of witness operations",
				Buckets: prometheus.DefBuckets,
			},
			[]string{"operation"},
		),
		ctp96Ops: promauto.NewCounterVec(
			prometheus.CounterOpts{
				Name: "hologram_ctp96_operations_total",
				Help: "Total number of CTP-96 operations",
			},
			[]string{"operation", "status"},
		),
		ctp96Latency: promauto.NewHistogramVec(
			prometheus.HistogramOpts{
				Name:    "hologram_ctp96_operation_duration_seconds",
				Help:    "Duration of CTP-96 operations",
				Buckets: prometheus.DefBuckets,
			},
			[]string{"operation"},
		),
		contentOps: promauto.NewCounterVec(
			prometheus.CounterOpts{
				Name: "hologram_content_operations_total",
				Help: "Total number of content operations",
			},
			[]string{"operation", "status"},
		),
		contentLatency: promauto.NewHistogramVec(
			prometheus.HistogramOpts{
				Name:    "hologram_content_operation_duration_seconds",
				Help:    "Duration of content operations",
				Buckets: prometheus.DefBuckets,
			},
			[]string{"operation"},
		),
		energyHints: promauto.NewGaugeVec(
			prometheus.GaugeOpts{
				Name: "hologram_energy_hints",
				Help: "Energy hints from CTP-96 sessions",
			},
			[]string{"hint_type", "uor_id"},
		),
		leaseDuration: promauto.NewHistogramVec(
			prometheus.HistogramOpts{
				Name:    "hologram_lease_duration_seconds",
				Help:    "Duration of CTP-96 leases",
				Buckets: prometheus.DefBuckets,
			},
			[]string{"uor_id"},
		),
	}
}

// GetGlobal returns the global telemetry instance
func GetGlobal() *Telemetry {
	return globalTelemetry
}

// RecordSnapshotterOperation records a snapshotter operation
func (t *Telemetry) RecordSnapshotterOperation(ctx context.Context, operation string, status string, duration time.Duration) {
	t.snapshotterOps.WithLabelValues(operation, status).Inc()
	t.snapshotterLatency.WithLabelValues(operation).Observe(duration.Seconds())

	log.G(ctx).WithFields(map[string]interface{}{
		"operation": operation,
		"status":    status,
		"duration":  duration,
	}).Debug("Snapshotter operation recorded")
}

// RecordFUSEOperation records a FUSE operation
func (t *Telemetry) RecordFUSEOperation(ctx context.Context, operation string, status string, duration time.Duration) {
	t.fuseOps.WithLabelValues(operation, status).Inc()
	t.fuseLatency.WithLabelValues(operation).Observe(duration.Seconds())

	log.G(ctx).WithFields(map[string]interface{}{
		"operation": operation,
		"status":    status,
		"duration":  duration,
	}).Debug("FUSE operation recorded")
}

// RecordResolverOperation records a resolver operation
func (t *Telemetry) RecordResolverOperation(ctx context.Context, operation string, status string, duration time.Duration) {
	t.resolverOps.WithLabelValues(operation, status).Inc()
	t.resolverLatency.WithLabelValues(operation).Observe(duration.Seconds())

	log.G(ctx).WithFields(map[string]interface{}{
		"operation": operation,
		"status":    status,
		"duration":  duration,
	}).Debug("Resolver operation recorded")
}

// RecordWitnessOperation records a witness operation
func (t *Telemetry) RecordWitnessOperation(ctx context.Context, operation string, status string, duration time.Duration) {
	t.witnessOps.WithLabelValues(operation, status).Inc()
	t.witnessLatency.WithLabelValues(operation).Observe(duration.Seconds())

	log.G(ctx).WithFields(map[string]interface{}{
		"operation": operation,
		"status":    status,
		"duration":  duration,
	}).Debug("Witness operation recorded")
}

// RecordCTP96Operation records a CTP-96 operation
func (t *Telemetry) RecordCTP96Operation(ctx context.Context, operation string, status string, duration time.Duration) {
	t.ctp96Ops.WithLabelValues(operation, status).Inc()
	t.ctp96Latency.WithLabelValues(operation).Observe(duration.Seconds())

	log.G(ctx).WithFields(map[string]interface{}{
		"operation": operation,
		"status":    status,
		"duration":  duration,
	}).Debug("CTP-96 operation recorded")
}

// RecordContentOperation records a content operation
func (t *Telemetry) RecordContentOperation(ctx context.Context, operation string, status string, duration time.Duration) {
	t.contentOps.WithLabelValues(operation, status).Inc()
	t.contentLatency.WithLabelValues(operation).Observe(duration.Seconds())

	log.G(ctx).WithFields(map[string]interface{}{
		"operation": operation,
		"status":    status,
		"duration":  duration,
	}).Debug("Content operation recorded")
}

// RecordEnergyHint records an energy hint
func (t *Telemetry) RecordEnergyHint(ctx context.Context, hintType, uorID string, value float64) {
	t.energyHints.WithLabelValues(hintType, uorID).Set(value)

	log.G(ctx).WithFields(map[string]interface{}{
		"hint_type": hintType,
		"uor_id":    uorID,
		"value":     value,
	}).Debug("Energy hint recorded")
}

// RecordLeaseDuration records lease duration
func (t *Telemetry) RecordLeaseDuration(ctx context.Context, uorID string, duration time.Duration) {
	t.leaseDuration.WithLabelValues(uorID).Observe(duration.Seconds())

	log.G(ctx).WithFields(map[string]interface{}{
		"uor_id":   uorID,
		"duration": duration,
	}).Debug("Lease duration recorded")
}

// GetMetrics returns current metrics as a map
func (t *Telemetry) GetMetrics() map[string]interface{} {
	t.mu.RLock()
	defer t.mu.RUnlock()

	// This would typically collect metrics from Prometheus collectors
	// For now, return a basic structure
	return map[string]interface{}{
		"snapshotter_ops": "collected from Prometheus",
		"fuse_ops":        "collected from Prometheus",
		"resolver_ops":    "collected from Prometheus",
		"witness_ops":     "collected from Prometheus",
		"ctp96_ops":       "collected from Prometheus",
		"content_ops":     "collected from Prometheus",
		"energy_hints":    "collected from Prometheus",
		"lease_duration":  "collected from Prometheus",
	}
}
