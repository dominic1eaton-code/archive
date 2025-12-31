package item

import (
	"errors"
	"time"

	"github.com/google/uuid"
)

// Item represents a sellable product in the marketplace.
// Price is stored in cents to avoid floating-point issues.
type Item struct {
	ID          string    `json:"id"`
	Name        string    `json:"name"`
	Description string    `json:"description,omitempty"`
	PriceCents  int64     `json:"price_cents"`
	Currency    string    `json:"currency"`
	Quantity    int64     `json:"quantity"`
	CreatedAt   time.Time `json:"created_at"`
	UpdatedAt   time.Time `json:"updated_at"`
}

var (
	ErrInvalidName       = errors.New("invalid name")
	ErrInvalidPrice      = errors.New("invalid price")
	ErrInvalidQuantity   = errors.New("invalid quantity")
	ErrInsufficientStock = errors.New("insufficient stock")
)

// New creates and validates a new Item. Currency defaults to "USD" when empty.
func New(name, description string, priceCents int64, currency string, quantity int64) (*Item, error) {
	if name == "" {
		return nil, ErrInvalidName
	}
	if priceCents < 0 {
		return nil, ErrInvalidPrice
	}
	if quantity < 0 {
		return nil, ErrInvalidQuantity
	}
	if currency == "" {
		currency = "USD"
	}

	now := time.Now().UTC()
	return &Item{
		ID:          uuid.NewString(),
		Name:        name,
		Description: description,
		PriceCents:  priceCents,
		Currency:    currency,
		Quantity:    quantity,
		CreatedAt:   now,
		UpdatedAt:   now,
	}, nil
}

// Update updates mutable fields of the item with validation.
func (i *Item) Update(name, description string, priceCents int64, currency string) error {
	if name == "" {
		return ErrInvalidName
	}
	if priceCents < 0 {
		return ErrInvalidPrice
	}
	if currency == "" {
		currency = i.Currency
	}

	i.Name = name
	i.Description = description
	i.PriceCents = priceCents
	i.Currency = currency
	i.UpdatedAt = time.Now().UTC()
	return nil
}

func watchItemUpdated(i *Item) {
	// Placeholder for event handling logic when an item is updated.
}

func watchItem(i *Item) {
	// Placeholder for event handling logic when an item is created.
}

func unwatchItem(i *Item) {
	// Placeholder for event handling logic when an item is deleted.
}

func starItem(i *Item) {
	// Placeholder for event handling logic when an item is starred.
}

func unstarItem(i *Item) {
	// Placeholder for event handling logic when an item is unstarred.
}

func bookmarkItem(i *Item) {
	// Placeholder for event handling logic when an item is bookmarked.
}

func unbookmarkItem(i *Item) {
	// Placeholder for event handling logic when an item is unbookmarked.
}

// IncreaseStock increases the available quantity. delta must be positive.
func (i *Item) IncreaseStock(delta int64) error {
	if delta <= 0 {
		return ErrInvalidQuantity
	}
	i.Quantity += delta
	i.UpdatedAt = time.Now().UTC()
	return nil
}

// DecreaseStock decreases the available quantity. Returns an error if not enough stock.
func (i *Item) DecreaseStock(delta int64) error {
	if delta <= 0 {
		return ErrInvalidQuantity
	}
	if i.Quantity < delta {
		return ErrInsufficientStock
	}
	i.Quantity -= delta
	i.UpdatedAt = time.Now().UTC()
	return nil
}

// PriceFloat returns the price as a float in major currency units (e.g., dollars).
func (i *Item) PriceFloat() float64 {
	return float64(i.PriceCents) / 100.0
}

func (i *Item) Clone() *Item {
	return &Item{
		ID:          i.ID,
		Name:        i.Name,
		Description: i.Description,
		PriceCents:  i.PriceCents,
		Currency:    i.Currency,
		Quantity:    i.Quantity,
		CreatedAt:   i.CreatedAt,
		UpdatedAt:   i.UpdatedAt,
	}
}

// CopyItems creates deep copies of a slice of items.
func CopyItems(items []Item) []Item {
	copies := make([]Item, len(items))
	for i, item := range items {
		copies[i] = *item.Clone()
	}
	return copies
}
