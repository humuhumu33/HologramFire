package api

import (
	"encoding/json"
	"net/http"
)

// DockerError represents a Docker-compatible error response
type DockerError struct {
	Message string `json:"message"`
	Code    int    `json:"code,omitempty"`
}

// HologramError represents a Hologram-specific error with additional context
type HologramError struct {
	DockerError
	XHologram struct {
		Reason    string `json:"reason,omitempty"`
		UORID     string `json:"uor_id,omitempty"`
		Witness   string `json:"witness,omitempty"`
		VPILease  string `json:"vpi_lease,omitempty"`
		CTP96     string `json:"ctp96,omitempty"`
		Space12288 string `json:"space_12288,omitempty"`
		MetaAware string `json:"meta_aware,omitempty"`
		Oracle    string `json:"oracle,omitempty"`
	} `json:"XHologram,omitempty"`
}

// WriteDockerError writes a Docker-compatible error response
func WriteDockerError(w http.ResponseWriter, statusCode int, message string) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(statusCode)
	
	error := DockerError{
		Message: message,
	}
	
	json.NewEncoder(w).Encode(error)
}

// WriteHologramError writes a Hologram error response with additional context
func WriteHologramError(w http.ResponseWriter, statusCode int, message string, verbose bool, hologramContext map[string]string) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(statusCode)
	
	error := HologramError{
		DockerError: DockerError{
			Message: message,
		},
	}
	
	// Add Hologram context only in verbose mode
	if verbose {
		if reason, ok := hologramContext["reason"]; ok {
			error.XHologram.Reason = reason
		}
		if uorID, ok := hologramContext["uor_id"]; ok {
			error.XHologram.UORID = uorID
		}
		if witness, ok := hologramContext["witness"]; ok {
			error.XHologram.Witness = witness
		}
		if vpiLease, ok := hologramContext["vpi_lease"]; ok {
			error.XHologram.VPILease = vpiLease
		}
		if ctp96, ok := hologramContext["ctp96"]; ok {
			error.XHologram.CTP96 = ctp96
		}
		if space12288, ok := hologramContext["space_12288"]; ok {
			error.XHologram.Space12288 = space12288
		}
		if metaAware, ok := hologramContext["meta_aware"]; ok {
			error.XHologram.MetaAware = metaAware
		}
		if oracle, ok := hologramContext["oracle"]; ok {
			error.XHologram.Oracle = oracle
		}
	}
	
	json.NewEncoder(w).Encode(error)
}

// Common Docker error responses
var (
	ErrImageNotFound = DockerError{
		Message: "No such image: %s",
		Code:    404,
	}
	
	ErrContainerNotFound = DockerError{
		Message: "No such container: %s",
		Code:    404,
	}
	
	ErrInvalidParameter = DockerError{
		Message: "Invalid parameter: %s",
		Code:    400,
	}
	
	ErrServerError = DockerError{
		Message: "Server error: %s",
		Code:    500,
	}
	
	ErrNotImplemented = DockerError{
		Message: "Not implemented: %s",
		Code:    501,
	}
)
