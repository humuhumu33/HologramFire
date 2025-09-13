package events

import (
	"context"
	"encoding/json"
	"fmt"
	"sync"

	"github.com/sirupsen/logrus"
)

// Filter represents event filtering criteria
type Filter struct {
	Type   string            `json:"type,omitempty"`
	Action string            `json:"action,omitempty"`
	ID     string            `json:"id,omitempty"`
	Labels map[string]string `json:"labels,omitempty"`
}

// Subscriber represents an event subscriber
type Subscriber struct {
	ID      string
	Filter  Filter
	Channel chan *Message
	Context context.Context
	Cancel  context.CancelFunc
	Verbose bool
}

// Bus represents the event bus
type Bus struct {
	logger      *logrus.Logger
	mu          sync.RWMutex
	subscribers map[string]*Subscriber
	nextID      int
}

// NewBus creates a new event bus
func NewBus(logger *logrus.Logger) *Bus {
	return &Bus{
		logger:      logger,
		subscribers: make(map[string]*Subscriber),
	}
}

// Subscribe creates a new event subscription
func (b *Bus) Subscribe(ctx context.Context, filter Filter, verbose bool) *Subscriber {
	b.mu.Lock()
	defer b.mu.Unlock()

	b.nextID++
	subID := fmt.Sprintf("sub_%d", b.nextID)

	subCtx, cancel := context.WithCancel(ctx)
	subscriber := &Subscriber{
		ID:      subID,
		Filter:  filter,
		Channel: make(chan *Message, 100), // Buffered channel
		Context: subCtx,
		Cancel:  cancel,
		Verbose: verbose,
	}

	b.subscribers[subID] = subscriber

	b.logger.WithFields(logrus.Fields{
		"subscriber_id": subID,
		"filter":        filter,
		"verbose":       verbose,
	}).Debug("Event subscriber created")

	return subscriber
}

// Unsubscribe removes a subscriber
func (b *Bus) Unsubscribe(subscriber *Subscriber) {
	b.mu.Lock()
	defer b.mu.Unlock()

	if sub, exists := b.subscribers[subscriber.ID]; exists {
		sub.Cancel()
		close(sub.Channel)
		delete(b.subscribers, subscriber.ID)

		b.logger.WithField("subscriber_id", subscriber.ID).Debug("Event subscriber removed")
	}
}

// Publish publishes an event to all matching subscribers
func (b *Bus) Publish(event *Message) {
	b.mu.RLock()
	subscribers := make([]*Subscriber, 0, len(b.subscribers))
	for _, sub := range b.subscribers {
		subscribers = append(subscribers, sub)
	}
	b.mu.RUnlock()

	// Send to all matching subscribers
	for _, sub := range subscribers {
		if b.matchesFilter(event, sub.Filter) {
			// Create a copy of the event for this subscriber
			eventCopy := b.createEventCopy(event, sub.Verbose)

			select {
			case sub.Channel <- eventCopy:
			case <-sub.Context.Done():
				// Subscriber context cancelled, remove it
				b.Unsubscribe(sub)
			default:
				// Channel is full, drop the event
				b.logger.WithFields(logrus.Fields{
					"subscriber_id": sub.ID,
					"event_type":    event.Type,
					"event_action":  event.Action,
				}).Warn("Dropped event due to full channel")
			}
		}
	}
}

// matchesFilter checks if an event matches the given filter
func (b *Bus) matchesFilter(event *Message, filter Filter) bool {
	// Check type filter
	if filter.Type != "" && event.Type != filter.Type {
		return false
	}

	// Check action filter
	if filter.Action != "" && event.Action != filter.Action {
		return false
	}

	// Check ID filter
	if filter.ID != "" && event.Actor.ID != filter.ID {
		return false
	}

	// Check label filters
	if len(filter.Labels) > 0 {
		for key, value := range filter.Labels {
			if event.Actor.Attributes[key] != value {
				return false
			}
		}
	}

	return true
}

// createEventCopy creates a copy of the event, optionally filtering Hologram attributes
func (b *Bus) createEventCopy(event *Message, verbose bool) *Message {
	copy := &Message{
		Type:   event.Type,
		Action: event.Action,
		Actor: struct {
			ID         string            `json:"ID"`
			Attributes map[string]string `json:"Attributes"`
		}{
			ID:         event.Actor.ID,
			Attributes: make(map[string]string),
		},
		Time:     event.Time,
		TimeNano: event.TimeNano,
	}

	// Copy attributes, filtering Hologram attributes based on verbose mode
	for key, value := range event.Actor.Attributes {
		if !verbose && len(key) > 10 && key[:10] == "XHologram." {
			// Skip Hologram attributes in non-verbose mode
			continue
		}
		copy.Actor.Attributes[key] = value
	}

	return copy
}

// GetSubscriberCount returns the number of active subscribers
func (b *Bus) GetSubscriberCount() int {
	b.mu.RLock()
	defer b.mu.RUnlock()
	return len(b.subscribers)
}

// Cleanup removes all subscribers
func (b *Bus) Cleanup() {
	b.mu.Lock()
	defer b.mu.Unlock()

	for _, sub := range b.subscribers {
		sub.Cancel()
		close(sub.Channel)
	}
	b.subscribers = make(map[string]*Subscriber)
}

// PublishContainerEvent publishes a container-related event
func (b *Bus) PublishContainerEvent(action EventAction, containerID, image string, attributes map[string]string, verbose bool) {
	event := NewMessage(EventTypeContainer, action, containerID, attributes)

	// Add standard container attributes
	event.AddAttribute("image", image)
	event.AddAttribute("name", "/"+containerID[:12]) // Short container name

	// Add Hologram attributes if verbose
	if verbose {
		event.AddHologramAttribute("lease_id", fmt.Sprintf("lease_%s", containerID))
		event.AddHologramAttribute("witness_ok", "true")
		event.AddHologramAttribute("uor_id", fmt.Sprintf("uor:%s", containerID))
	}

	b.Publish(event)
}

// PublishImageEvent publishes an image-related event
func (b *Bus) PublishImageEvent(action EventAction, imageID, tag string, attributes map[string]string, verbose bool) {
	event := NewMessage(EventTypeImage, action, imageID, attributes)

	// Add standard image attributes
	event.AddAttribute("name", tag)

	// Add Hologram attributes if verbose
	if verbose {
		event.AddHologramAttribute("uor_id", fmt.Sprintf("uor:%s", imageID))
		event.AddHologramAttribute("witness_ok", "true")
	}

	b.Publish(event)
}

// PublishVolumeEvent publishes a volume-related event
func (b *Bus) PublishVolumeEvent(action EventAction, volumeName string, attributes map[string]string, verbose bool) {
	event := NewMessage(EventTypeVolume, action, volumeName, attributes)

	// Add standard volume attributes
	event.AddAttribute("name", volumeName)

	// Add Hologram attributes if verbose
	if verbose {
		event.AddHologramAttribute("driver", "hologram")
	}

	b.Publish(event)
}

// PublishNetworkEvent publishes a network-related event
func (b *Bus) PublishNetworkEvent(action EventAction, networkID, networkName string, attributes map[string]string, verbose bool) {
	event := NewMessage(EventTypeNetwork, action, networkID, attributes)

	// Add standard network attributes
	event.AddAttribute("name", networkName)
	event.AddAttribute("type", "bridge")

	// Add Hologram attributes if verbose
	if verbose {
		event.AddHologramAttribute("driver", "hologram")
		if networkName == "ctp96" {
			event.AddHologramAttribute("ctp96_session", fmt.Sprintf("session_%s", networkID))
		}
	}

	b.Publish(event)
}

// StreamEvents streams events to a subscriber until the context is cancelled
func (b *Bus) StreamEvents(subscriber *Subscriber, w chan []byte) {
	defer close(w)

	for {
		select {
		case event := <-subscriber.Channel:
			// Marshal event to JSON
			data, err := json.Marshal(event)
			if err != nil {
				b.logger.WithError(err).Error("Failed to marshal event")
				continue
			}

			// Send to output channel
			select {
			case w <- data:
			case <-subscriber.Context.Done():
				return
			}

		case <-subscriber.Context.Done():
			return
		}
	}
}
