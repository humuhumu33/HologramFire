package events

import "time"

// Message represents a Docker-compatible event message
type Message struct {
	Type   string `json:"Type"`   // "container" | "image" | "volume" | "network"
	Action string `json:"Action"` // "create","start","stop","destroy","pull","push"
	Actor  struct {
		ID         string            `json:"ID"`
		Attributes map[string]string `json:"Attributes"`
	} `json:"Actor"`
	Time     int64 `json:"time"`
	TimeNano int64 `json:"timeNano"`
}

// EventType represents the type of event
type EventType string

const (
	EventTypeContainer EventType = "container"
	EventTypeImage     EventType = "image"
	EventTypeVolume    EventType = "volume"
	EventTypeNetwork   EventType = "network"
)

// EventAction represents the action that occurred
type EventAction string

const (
	// Container actions
	ActionCreate     EventAction = "create"
	ActionStart      EventAction = "start"
	ActionStop       EventAction = "stop"
	ActionKill       EventAction = "kill"
	ActionDie        EventAction = "die"
	ActionDestroy    EventAction = "destroy"
	ActionRestart    EventAction = "restart"
	ActionPause      EventAction = "pause"
	ActionUnpause    EventAction = "unpause"
	ActionRename     EventAction = "rename"
	ActionUpdate     EventAction = "update"
	ActionExecCreate EventAction = "exec_create"
	ActionExecStart  EventAction = "exec_start"
	ActionExecDie    EventAction = "exec_die"

	// Image actions
	ActionPull   EventAction = "pull"
	ActionPush   EventAction = "push"
	ActionTag    EventAction = "tag"
	ActionUntag  EventAction = "untag"
	ActionDelete EventAction = "delete"
	ActionImport EventAction = "import"
	ActionLoad   EventAction = "load"
	ActionSave   EventAction = "save"

	// Volume actions
	ActionMount   EventAction = "mount"
	ActionUnmount EventAction = "unmount"

	// Network actions
	ActionConnect    EventAction = "connect"
	ActionDisconnect EventAction = "disconnect"
)

// NewMessage creates a new event message
func NewMessage(eventType EventType, action EventAction, id string, attributes map[string]string) *Message {
	now := time.Now()
	return &Message{
		Type:   string(eventType),
		Action: string(action),
		Actor: struct {
			ID         string            `json:"ID"`
			Attributes map[string]string `json:"Attributes"`
		}{
			ID:         id,
			Attributes: attributes,
		},
		Time:     now.Unix(),
		TimeNano: now.UnixNano(),
	}
}

// AddAttribute adds an attribute to the event message
func (m *Message) AddAttribute(key, value string) {
	if m.Actor.Attributes == nil {
		m.Actor.Attributes = make(map[string]string)
	}
	m.Actor.Attributes[key] = value
}

// AddHologramAttribute adds a Hologram-specific attribute (only in verbose mode)
func (m *Message) AddHologramAttribute(key, value string) {
	// Prefix with XHologram to namespace Hologram-specific attributes
	m.AddAttribute("XHologram."+key, value)
}
