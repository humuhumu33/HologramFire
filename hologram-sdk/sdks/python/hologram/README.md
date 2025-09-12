# hologram

Native Hologram SDK with UOR-IDs, witnesses, VPI leases, and CTP-96.

## Installation

```bash
pip install hologram
```

## Usage

This package provides first-class support for Hologram concepts:

```python
import hologram

# Create a Hologram client
client = hologram.Client()

# Create a UOR-ID
uor_id = client.uor.create("nginx:latest")

# Create a witness
witness = client.witness.create(uor_id)

# Create a VPI lease
lease = client.vpi.create_lease(uor_id, witness)

# Create a container with Hologram features
container = client.containers.create(
    uor_id=uor_id,
    witness=witness,
    vpi_lease=lease
)

# Start container with CTP-96 transport
container.start(transport="ctp96")
```

## Core Concepts

### UOR-IDs (Universal Object References)

UOR-IDs provide a universal way to reference objects across the Hologram ecosystem:

```python
# Create a UOR-ID
uor_id = client.uor.create("nginx:latest")

# Resolve a UOR-ID
image = client.uor.resolve(uor_id)

# List UOR-IDs
uor_ids = client.uor.list()
```

### Witnesses

Witnesses provide cryptographic verification of object integrity:

```python
# Create a witness
witness = client.witness.create(uor_id)

# Verify a witness
is_valid = client.witness.verify(witness, uor_id)

# List witnesses
witnesses = client.witness.list()
```

### VPI Leases

VPI (Virtual Process Isolation) leases provide secure process isolation:

```python
# Create a VPI lease
lease = client.vpi.create_lease(uor_id, witness)

# Activate a VPI lease
client.vpi.activate(lease)

# Deactivate a VPI lease
client.vpi.deactivate(lease)
```

### CTP-96 Transport

CTP-96 provides efficient transport for Hologram objects:

```python
# Create a CTP-96 connection
connection = client.ctp96.connect("remote-host")

# Send data via CTP-96
client.ctp96.send(connection, data)

# Receive data via CTP-96
data = client.ctp96.receive(connection)
```

## 12,288 Space

The 12,288 space provides a high-dimensional coordinate system for object placement:

```python
# Create a coordinate in 12,288 space
coord = client.space.create_coordinate(dimensions=12288)

# Place an object in 12,288 space
client.space.place(uor_id, coord)

# Query objects in 12,288 space
objects = client.space.query(coord, radius=100)
```

## Advanced Features

### Meta-Awareness

Enable meta-awareness for self-monitoring and optimization:

```python
# Enable meta-awareness
client.meta.enable()

# Get meta-awareness data
data = client.meta.get_data()

# Configure meta-awareness
client.meta.configure({
    "monitoring": True,
    "optimization": True,
    "self_healing": True
})
```

### Oracle Integration

Integrate with Hologram oracles for enhanced functionality:

```python
# Connect to an oracle
oracle = client.oracle.connect("oracle-host")

# Query oracle
result = oracle.query("SELECT * FROM objects WHERE type='container'")

# Subscribe to oracle events
oracle.subscribe("object_created", callback)
```

## Configuration

Configure the Hologram client:

```python
import hologram

client = hologram.Client(
    base_url="http://localhost:2375",
    hologram_features={
        "uor_id": True,
        "witness": True,
        "vpi_lease": True,
        "ctp96": True,
        "space_12288": True,
        "meta_awareness": True,
        "oracle": True
    }
)
```

## Environment Variables

- `HOLOGRAM_BASE_URL`: Hologram daemon URL (default: http://localhost:2375)
- `HOLOGRAM_UOR_ID`: Enable UOR-ID support (default: true)
- `HOLOGRAM_WITNESS`: Enable witness verification (default: true)
- `HOLOGRAM_VPI_LEASE`: Enable VPI lease management (default: true)
- `HOLOGRAM_CTP96`: Enable CTP-96 transport (default: true)
- `HOLOGRAM_SPACE_12288`: Enable 12,288 space (default: true)
- `HOLOGRAM_META_AWARENESS`: Enable meta-awareness (default: false)
- `HOLOGRAM_ORACLE`: Enable oracle integration (default: false)
