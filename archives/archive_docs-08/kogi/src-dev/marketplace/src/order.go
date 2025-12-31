package order

import (
	"errors"
	"fmt"
	"time"
)

// Basic domain types and errors
type ID string
type Status string

const (
	StatusPending   Status = "pending"
	StatusPaid      Status = "paid"
	StatusShipped   Status = "shipped"
	StatusCompleted Status = "completed"
	StatusCancelled Status = "cancelled"
	StatusRefunded  Status = "refunded"
)

var (
	ErrNotFound      = errors.New("order: not found")
	ErrEmptyOrder    = errors.New("order: order must contain at least one item")
	ErrInvalidItem   = errors.New("order: invalid item")
	ErrInvalidStatus = errors.New("order: invalid status transition")
)

// allowedTransitions maps current status -> allowed next statuses.
var allowedTransitions = map[Status]map[Status]bool{
	StatusPending: {
		StatusPaid:      true,
		StatusCancelled: true,
	},
	StatusPaid: {
		StatusShipped:   true,
		StatusRefunded:  true,
		StatusCancelled: true,
	},
	StatusShipped: {
		StatusCompleted: true,
		StatusRefunded:  true,
	},
	// completed/cancelled/refunded should be terminal (no transitions)
	StatusCompleted: {},
	StatusCancelled: {},
	StatusRefunded:  {},
}

// Item represents a purchasable unit in an order.
// UnitPrice is represented in the smallest currency unit (e.g., cents).
type Item struct {
	ID        string
	Name      string
	UnitPrice int64 // cents
	Quantity  int
}

// Validate checks the item fields for correctness.
func (it Item) Validate() error {
	if it.ID == "" {
		return fmt.Errorf("%w: id is required", ErrInvalidItem)
	}
	if it.Name == "" {
		return fmt.Errorf("%w: name is required", ErrInvalidItem)
	}
	if it.UnitPrice < 0 {
		return fmt.Errorf("%w: unit price must be >= 0", ErrInvalidItem)
	}
	if it.Quantity <= 0 {
		return fmt.Errorf("%w: quantity must be > 0", ErrInvalidItem)
	}
	return nil
}

// Order is the aggregate root for an order in the marketplace.
type Order struct {
	ID        ID
	Items     []Item
	Status    Status
	Currency  string // ISO 4217 code like "USD"
	CreatedAt time.Time
	UpdatedAt time.Time
	// you can add fields like CustomerID, ShippingAddress, Metadata, etc.
}

// New creates a new order and validates input.
func New(id ID, currency string, items []Item) (*Order, error) {
	if len(items) == 0 {
		return nil, ErrEmptyOrder
	}
	for i := range items {
		if err := items[i].Validate(); err != nil {
			return nil, err
		}
	}
	now := time.Now().UTC()
	return &Order{
		ID:        id,
		Items:     copyItems(items),
		Status:    StatusPending,
		Currency:  currency,
		CreatedAt: now,
		UpdatedAt: now,
	}, nil
}

// TotalCents returns total order amount in smallest currency unit (e.g., cents).
func (o *Order) TotalCents() int64 {
	var total int64
	for _, it := range o.Items {
		total += it.UnitPrice * int64(it.Quantity)
	}
	return total
}

// AddItem appends an item to the order (validates item).
func (o *Order) AddItem(it Item) error {
	if err := it.Validate(); err != nil {
		return err
	}
	o.Items = append(o.Items, it)
	o.touch()
	return nil
}

// RemoveItem removes the first item matching id. Returns true if removed.
func (o *Order) RemoveItem(id string) bool {
	for i := range o.Items {
		if o.Items[i].ID == id {
			o.Items = append(o.Items[:i], o.Items[i+1:]...)
			o.touch()
			return true
		}
	}
	return false
}

// UpdateStatus attempts to change order status following allowed transitions.
func (o *Order) UpdateStatus(next Status) error {
	if o.Status == next {
		return nil
	}
	allowed, ok := allowedTransitions[o.Status]
	if !ok {
		return ErrInvalidStatus
	}
	if !allowed[next] {
		return fmt.Errorf("%w: %s -> %s", ErrInvalidStatus, o.Status, next)
	}
	o.Status = next
	o.touch()
	return nil
}

// touch updates the UpdatedAt timestamp.
func (o *Order) touch() {
	o.UpdatedAt = time.Now().UTC()
}

// copyItems returns a shallow copy of items slice.
func copyItems(src []Item) []Item {
	dst := make([]Item, len(src))
	copy(dst, src)
	return dst
}

// Repository defines persistence operations for orders.
type Repository interface {
	Save(o *Order) error
	GetByID(id ID) (*Order, error)
	Delete(id ID) error
}