# Hologram SDK Quickstart

Get started with the Hologram SDK in minutes.

## Installation

### Python (Compat)
```bash
pip install hologram-docker
```

### Python (Native)
```bash
pip install hologram
```

### Go (Compat)
```bash
go get github.com/hologram/sdks/go/compat
```

### Go (Native)
```bash
go get github.com/hologram/sdks/go/sdk
```

### Node.js (Compat)
```bash
npm install hologramode
```

### Node.js (Native)
```bash
npm install @hologram/sdk
```

## Quick Examples

### Python Compat (Drop-in Docker replacement)

```python
import hologram_docker as docker

# All existing Docker code works unchanged
client = docker.from_env()
container = client.containers.run('nginx', detach=True)
print(container.logs())
```

### Python Native (First-class Hologram features)

```python
import hologram

# Create a Hologram client
client = hologram.Client()

# Create a UOR-ID
uor_id = client.uor.create("nginx:latest")

# Create a witness
witness = client.witness.create(uor_id)

# Create a container with Hologram features
container = client.containers.create(
    uor_id=uor_id,
    witness=witness
)
```

### Go Native

```go
package main

import (
    "fmt"
    "log"
    
    "github.com/hologram/sdks/go/sdk"
)

func main() {
    // Create a Hologram client
    client, err := sdk.NewClient()
    if err != nil {
        log.Fatal(err)
    }
    
    // Create a UOR-ID
    uorID, err := client.UOR.Create("nginx:latest", nil)
    if err != nil {
        log.Fatal(err)
    }
    
    // Create a witness
    witness, err := client.Witness.Create(uorID, "integrity", nil)
    if err != nil {
        log.Fatal(err)
    }
    
    fmt.Printf("Created UOR: %s\n", uorID)
    fmt.Printf("Created witness: %s\n", witness)
}
```

### Node.js Native

```javascript
const hologram = require('@hologram/sdk');

// Create a Hologram client
const client = new hologram.Client();

// Create a UOR-ID
const uorId = await client.uor.create('nginx:latest');

// Create a witness
const witness = await client.witness.create(uorId);

// Create a container with Hologram features
const container = await client.containers.create({
    uorId: uorId,
    witness: witness
});
```

## Running the Hologram Daemon

```bash
# Start hologramd
hologramd --hologram-enabled --hologram-uor-id --hologram-witness

# Or with environment variables
export HOLOGRAM_ENABLED=true
export HOLOGRAM_UOR_ID=true
export HOLOGRAM_WITNESS=true
hologramd
```

## Next Steps

- [Deep Dive Guide](../deep-dive/README.md) - Learn about advanced features
- [API Reference](../api/README.md) - Complete API documentation
- [Examples](../../examples/README.md) - More code examples
- [Contributing](../../CONTRIBUTING.md) - How to contribute
