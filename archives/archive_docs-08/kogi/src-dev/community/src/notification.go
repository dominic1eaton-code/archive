/**
 * @license
 * @brief
 * @copyright Copyright (c) 2024 Project X Contributors
 */
package notification

import (
	"projectx/user"
	"time"
)

// Notification represents a notification sent to a user.
type Notification struct {
	Recipient *user.User
	Message   string
	Timestamp time.Time
	Read      bool
}

// NewNotification creates a new Notification instance.
func NewNotification(recipient *user.User, message string) *Notification {
	return &Notification{
		Recipient: recipient,
		Message:   message,
		Timestamp: time.Now(),
		Read:      false,
	}
}

// MarkAsRead marks the notification as read.
func (n *Notification) MarkAsRead() {
	n.Read = true
}

// IsRead checks if the notification has been read.
func (n *Notification) IsRead() bool {
	return n.Read
}

// GetRecipient returns the recipient of the notification.
func (n *Notification) GetRecipient() *user.User {
	return n.Recipient
}

// GetMessage returns the message of the notification.
func (n *Notification) GetMessage() string {
	return n.Message
}

// GetTimestamp returns the timestamp of the notification.
func (n *Notification) GetTimestamp() time.Time {
	return n.Timestamp
}

// SetMessage updates the message of the notification.
func (n *Notification) SetMessage(newMessage string) {
	n.Message = newMessage
}

// SetTimestamp updates the timestamp of the notification.
func (n *Notification) SetTimestamp(newTimestamp time.Time) {
	n.Timestamp = newTimestamp
}

func (a *Activity) Mute(u *user.User) *Activity {
	return NewActivity(u, a.Post, "muted")
}

func (a *Activity) Unmute(u *user.User) *Activity {
	return NewActivity(u, a.Post, "unmuted")
}
