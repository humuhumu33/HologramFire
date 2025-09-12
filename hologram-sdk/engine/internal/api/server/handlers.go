package server

import (
	"github.com/hologram/engine/internal/runtime"
	"github.com/sirupsen/logrus"
)

// handlers contains all the HTTP handlers for the API server
type handlers struct {
	logger  *logrus.Logger
	runtime *runtime.Runtime
}

// NewHandlers creates a new handlers instance
func NewHandlers(logger *logrus.Logger, rt *runtime.Runtime) *handlers {
	return &handlers{
		logger:  logger,
		runtime: rt,
	}
}
