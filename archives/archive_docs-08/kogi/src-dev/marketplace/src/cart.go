package cart

import (
	"errors"
	"sync"
)

// Item represents a product in the cart.
// Price is stored in smallest currency unit (e.g., cents).
type Item struct {
	ID       string `json:"id"`
	Name     string `json:"name"`
	Price    int64  `json:"price"`
	Quantity int    `json:"quantity"`
}

// Cart holds items and provides concurrency-safe operations.
type Cart struct {
	mu    sync.RWMutex
	items map[string]*Item
}

// New creates and returns an empty cart.
func New() *Cart {
	return &Cart{
		items: make(map[string]*Item),
	}
}

var (
	// ErrInvalidQuantity is returned when quantity is non-positive on add/update.
	ErrInvalidQuantity = errors.New("quantity must be > 0")
	// ErrInvalidPrice is returned when price is negative.
	ErrInvalidPrice = errors.New("price must be >= 0")
)

// Add adds an item to the cart. If the item already exists it increases its quantity.
// Returns an error for invalid price or quantity.
func (c *Cart) Add(it Item) error {
	if it.Quantity <= 0 {
		return ErrInvalidQuantity
	}
	if it.Price < 0 {
		return ErrInvalidPrice
	}
	if it.ID == "" {
		return errors.New("item id required")
	}

	c.mu.Lock()
	defer c.mu.Unlock()

	if exist, ok := c.items[it.ID]; ok {
		exist.Quantity += it.Quantity
		// keep existing name/price if they differ; update if caller provided values
		if it.Name != "" {
			exist.Name = it.Name
		}
		if it.Price != 0 {
			exist.Price = it.Price
		}
	} else {
		// store a copy
		cp := it
		c.items[it.ID] = &cp
	}
	return nil
}

// Remove deletes an item by id. Returns true if the item was present.
func (c *Cart) Remove(id string) bool {
	c.mu.Lock()
	defer c.mu.Unlock()
	if _, ok := c.items[id]; ok {
		delete(c.items, id)
		return true
	}
	return false
}

// UpdateQuantity sets the quantity for an item. If quantity <= 0 the item is removed.
// Returns true if item existed (and was updated/removed).
func (c *Cart) UpdateQuantity(id string, qty int) (updated bool, err error) {
	if qty < 0 {
		return false, ErrInvalidQuantity
	}

	c.mu.Lock()
	defer c.mu.Unlock()

	it, ok := c.items[id]
	if !ok {
		return false, nil
	}
	if qty == 0 {
		delete(c.items, id)
		return true, nil
	}
	it.Quantity = qty
	return true, nil
}

// Items returns a snapshot slice of the items in the cart.
func (c *Cart) Items() []Item {
	c.mu.RLock()
	defer c.mu.RUnlock()

	out := make([]Item, 0, len(c.items))
	for _, it := range c.items {
		out = append(out, *it)
	}
	return out
}

// Total returns the total price (sum of price * quantity) in smallest currency unit.
func (c *Cart) Total() int64 {
	c.mu.RLock()
	defer c.mu.RUnlock()

	var total int64
	for _, it := range c.items {
		total += it.Price * int64(it.Quantity)
	}
	return total
}

// Count returns total quantity of all items.
func (c *Cart) Count() int {
	c.mu.RLock()
	defer c.mu.RUnlock()

	var cnt int
	for _, it := range c.items {
		cnt += it.Quantity
	}
	return cnt
}

// Size returns the number of distinct items in the cart.
func (c *Cart) Size() int {
	c.mu.RLock()
	defer c.mu.RUnlock()
	return len(c.items)
}

// Clear empties the cart.
func (c *Cart) Clear() {
	c.mu.Lock()
	defer c.mu.Unlock()
	c.items = make(map[string]*Item)
}