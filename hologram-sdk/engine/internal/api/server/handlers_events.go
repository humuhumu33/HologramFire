package server

import (
	"encoding/json"
	"net/http"
	"strings"

	"github.com/hologram/engine/internal/events"
	"github.com/sirupsen/logrus"
)

// EventsHandler handles GET /events
func (h *handlers) EventsHandler(w http.ResponseWriter, r *http.Request) {
	h.logger.WithField("path", r.URL.Path).Info("Events request")

	// Parse query parameters
	filter := events.Filter{}

	if eventType := r.URL.Query().Get("type"); eventType != "" {
		filter.Type = eventType
	}

	if action := r.URL.Query().Get("action"); action != "" {
		filter.Action = action
	}

	if id := r.URL.Query().Get("id"); id != "" {
		filter.ID = id
	}

	// Parse labels filter
	if labels := r.URL.Query().Get("labels"); labels != "" {
		filter.Labels = make(map[string]string)
		// Parse labels in format "key1=value1,key2=value2"
		for _, label := range strings.Split(labels, ",") {
			if parts := strings.SplitN(label, "=", 2); len(parts) == 2 {
				filter.Labels[parts[0]] = parts[1]
			}
		}
	}

	// Check if verbose mode is enabled
	verbose := getVerboseFromRequest(r)

	// Create event subscription
	eventBus := h.runtime.GetEventBus()
	subscriber := eventBus.Subscribe(r.Context(), filter, verbose)
	defer eventBus.Unsubscribe(subscriber)

	// Set response headers for streaming
	w.Header().Set("Content-Type", "application/json")
	w.Header().Set("Transfer-Encoding", "chunked")

	// Get flusher for streaming
	flusher, ok := w.(http.Flusher)
	if !ok {
		h.logger.Error("ResponseWriter does not support flushing")
		http.Error(w, "Streaming not supported", http.StatusInternalServerError)
		return
	}

	// Stream events
	h.logger.WithFields(logrus.Fields{
		"filter":  filter,
		"verbose": verbose,
	}).Info("Starting event stream")

	for {
		select {
		case event := <-subscriber.Channel:
			// Marshal event to JSON
			data, err := json.Marshal(event)
			if err != nil {
				h.logger.WithError(err).Error("Failed to marshal event")
				continue
			}

			// Write event data
			w.Write(data)
			w.Write([]byte("\n"))
			flusher.Flush()

		case <-r.Context().Done():
			h.logger.Info("Event stream ended")
			return
		}
	}
}
