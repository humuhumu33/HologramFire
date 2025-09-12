# Example 4: Energy-Aware Runtime

**Advanced insights - VPI leases + energy/compute tracking**

This example demonstrates Hologram's advanced runtime features including VPI (Virtual Process Isolation) leases and energy/compute tracking. This is where users see the full power of the Hologram ecosystem.

## Prerequisites

1. Complete Examples 1, 2, and 3
2. Understand VPI leases and energy tracking concepts

## Running the Example

```bash
# Enable verbose mode to see all Hologram fields
export HOLOGRAM_VERBOSE=1

# Run a container and see VPI lease information
docker run -d --name web -p 8080:80 nginx:alpine

# Check container stats (standard Docker)
docker stats --no-stream

# Inspect container to see XHologram fields
docker inspect web | jq '.[0].XHologram'

# Check energy and compute insights
docker inspect web | jq '.[0].XHologram.lease_id'
docker inspect web | jq '.[0].XHologram.budget_delta'
```

## What You'll See

With `HOLOGRAM_VERBOSE=1`, container inspection shows:

```json
{
  "XHologram": {
    "lease_id": "vpi:lease:abc123def456",
    "budget_delta": "2.3J",
    "r96_checksum": "r96:sha256:...",
    "ctp96_session": "ctp96:session:xyz789",
    "energy_profile": {
      "baseline": "1.2J",
      "current": "3.5J",
      "efficiency": "0.85"
    },
    "compute_insights": {
      "cpu_cycles": 1234567,
      "memory_pages": 1024,
      "network_packets": 42
    }
  }
}
```

## Key Features Demonstrated

### VPI Leases
- **Virtual Process Isolation**: Each container gets a VPI lease
- **Resource allocation**: Precise control over compute resources
- **Lease management**: Track and manage container lifecycles

### Energy Tracking
- **Real-time monitoring**: Track energy consumption per container
- **Efficiency metrics**: Compare baseline vs. actual usage
- **Budget management**: Set and enforce energy budgets

### Compute Insights
- **Detailed metrics**: CPU cycles, memory pages, network packets
- **Performance analysis**: Understand resource utilization
- **Optimization opportunities**: Identify efficiency improvements

## The Full Power Moment

This is where users see that Hologram isn't just Docker with provenance - it's a **complete container runtime** with:

- **Cryptographic provenance** (UOR-IDs + witnesses)
- **Fail-closed security** (enforce mode)
- **Energy-aware execution** (VPI leases + tracking)
- **Advanced compute insights** (detailed metrics)

## Use Cases

- **Edge computing**: Optimize for energy efficiency
- **Cloud cost optimization**: Track and minimize resource usage
- **Performance tuning**: Detailed insights for optimization
- **Compliance**: Energy and resource usage reporting
- **Research**: Advanced container behavior analysis

## Production Benefits

- **Cost optimization**: Reduce energy and compute costs
- **Performance tuning**: Data-driven optimization decisions
- **Compliance**: Meet energy efficiency requirements
- **Monitoring**: Advanced observability beyond standard Docker
