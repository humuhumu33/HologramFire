package main

import (
	"fmt"
	"os"
)

// printInstallerOutput prints the Cursor-style installer messages
func printInstallerOutput() {
	fmt.Println("✅ Bound to `/var/run/hologramd.sock` (compat mode: behaves like Docker).")
	fmt.Println("✨ Try `docker buildx build --driver=hologram -t app:holo .` to unlock provenance (UOR-ID + witness).")
	fmt.Println("🔒 Set `HOLOGRAM_ENFORCE=1` to enforce witness at runtime (fail-closed).")
	fmt.Println("🔎 Set `HOLOGRAM_VERBOSE=1` to show `XHologram` details in inspect/events.")
	fmt.Println("")
	fmt.Println("🚀 Welcome to Hologram SDK - Docker with cryptographic superpowers!")
}

// printStartupMessage prints the startup message with current configuration
func printStartupMessage(config Config) {
	fmt.Println("🎯 Hologram SDK Starting...")
	fmt.Println("==========================")
	
	// Show current mode
	if config.Server.Host == "unix" {
		fmt.Printf("📡 Listening on: %s\n", config.Server.Socket)
	} else {
		fmt.Printf("📡 Listening on: %s:%d\n", config.Server.Host, config.Server.Port)
	}
	
	// Show compatibility mode
	fmt.Println("🔧 Compatibility mode: ON (behaves like Docker)")
	
	// Show Hologram features status
	if config.Hologram.Enabled {
		fmt.Println("✨ Hologram features: ENABLED")
		if config.Hologram.UORID {
			fmt.Println("   - UOR-ID support: ON")
		}
		if config.Hologram.Witness {
			fmt.Println("   - Witness verification: ON")
		}
		if config.Hologram.VPILease {
			fmt.Println("   - VPI lease management: ON")
		}
		if config.Hologram.CTP96 {
			fmt.Println("   - CTP-96 transport: ON")
		}
	} else {
		fmt.Println("🔧 Hologram features: DISABLED (pure Docker compatibility)")
	}
	
	// Show environment variables
	fmt.Println("")
	fmt.Println("💡 Quick start:")
	fmt.Println("   export DOCKER_HOST=unix:///var/run/hologramd.sock")
	fmt.Println("   docker version")
	fmt.Println("")
	fmt.Println("💡 Unlock Hologram features:")
	fmt.Println("   export HOLOGRAM_VERBOSE=1  # Show XHologram fields")
	fmt.Println("   export HOLOGRAM_ENFORCE=1  # Enable fail-closed security")
	fmt.Println("")
	fmt.Println("🎉 Ready to use! Run 'docker version' to test.")
}

// printShutdownMessage prints the shutdown message
func printShutdownMessage() {
	fmt.Println("")
	fmt.Println("👋 Hologram SDK shutting down...")
	fmt.Println("   Thanks for using Hologram SDK!")
	fmt.Println("   🚀 Docker with cryptographic superpowers")
}

// checkAndPrintInstallerOutput checks if this is the first run and prints installer output
func checkAndPrintInstallerOutput() {
	// Check if this is the first run by looking for a marker file
	markerFile := "/var/run/hologramd.installed"
	if _, err := os.Stat(markerFile); os.IsNotExist(err) {
		// First run - print installer output
		printInstallerOutput()
		
		// Create marker file to indicate installation
		if file, err := os.Create(markerFile); err == nil {
			file.Close()
		}
	}
}
