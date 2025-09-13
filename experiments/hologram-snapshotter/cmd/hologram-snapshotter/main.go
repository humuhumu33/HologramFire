package main

import (
	"context"
	"fmt"
	"os"
	"os/signal"
	"syscall"

	"github.com/containerd/containerd"
	"github.com/containerd/containerd/defaults"
	"github.com/containerd/containerd/namespaces"
	"github.com/containerd/containerd/snapshots"
	"github.com/containerd/log"
	"github.com/sirupsen/logrus"
	"github.com/urfave/cli/v2"

	"github.com/hologram/hologram-snapshotter/pkg/snapshotter"
	"github.com/hologram/hologram-snapshotter/pkg/telemetry"
)

func main() {
	app := &cli.App{
		Name:  "hologram-snapshotter",
		Usage: "Hologram snapshotter with FUSE backend for containerd",
		Flags: []cli.Flag{
			&cli.StringFlag{
				Name:  "root",
				Usage: "Root directory for snapshotter state",
				Value: defaults.DefaultStateDir,
			},
			&cli.StringFlag{
				Name:  "address",
				Usage: "Address for containerd GRPC server",
				Value: defaults.DefaultAddress,
			},
			&cli.StringFlag{
				Name:  "namespace",
				Usage: "Namespace for containerd operations",
				Value: namespaces.Default,
			},
			&cli.BoolFlag{
				Name:  "verbose",
				Usage: "Enable verbose logging",
				Value: false,
			},
			&cli.BoolFlag{
				Name:  "enforce",
				Usage: "Enable enforce mode (fail closed on invalid witness)",
				Value: false,
			},
		},
		Action: run,
	}

	if err := app.Run(os.Args); err != nil {
		log.L.Fatal(err)
	}
}

func run(c *cli.Context) error {
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	// Setup logging
	if c.Bool("verbose") {
		log.L.Logger.SetLevel(logrus.DebugLevel)
	}

	// Setup telemetry
	telemetry.Init()

	// Create containerd client
	client, err := containerd.New(c.String("address"))
	if err != nil {
		return fmt.Errorf("failed to create containerd client: %w", err)
	}
	defer client.Close()

	// Create snapshotter
	snapshotterConfig := &snapshotter.Config{
		Root:    c.String("root"),
		Enforce: c.Bool("enforce"),
		Verbose: c.Bool("verbose"),
		Client:  client,
	}

	snapshotterInstance, err := snapshotter.NewSnapshotter(snapshotterConfig)
	if err != nil {
		return fmt.Errorf("failed to create snapshotter: %w", err)
	}

	// Register snapshotter with containerd
	if err := snapshots.Register("hologram", snapshotterInstance); err != nil {
		return fmt.Errorf("failed to register snapshotter: %w", err)
	}

	log.L.Info("Hologram snapshotter registered successfully")

	// Wait for shutdown signal
	sigChan := make(chan os.Signal, 1)
	signal.Notify(sigChan, syscall.SIGINT, syscall.SIGTERM)

	<-sigChan
	log.L.Info("Shutting down hologram snapshotter...")

	return nil
}
