package com.portal;

import java.time.Instant;
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.atomic.AtomicLong;
import java.util.stream.Collectors;

/**
 * MarketplacePortal — a compact, in-memory marketplace implementation intended for examples,
 * demos and lightweight local use. It models sellers, products, listings, orders and reviews
 * using thread-friendly containers and simple ID generators.
 */
public class MarketplacePortal {

	private final AtomicLong sellerIdSeq = new AtomicLong(1);
	private final AtomicLong buyerIdSeq = new AtomicLong(1);
	private final AtomicLong productIdSeq = new AtomicLong(1);
	private final AtomicLong listingIdSeq = new AtomicLong(1);
	private final AtomicLong orderIdSeq = new AtomicLong(1);
	private final AtomicLong reviewIdSeq = new AtomicLong(1);

	private final Map<Long, Seller> sellers = new ConcurrentHashMap<>();
	private final Map<Long, Buyer> buyers = new ConcurrentHashMap<>();
	private final Map<Long, Product> products = new ConcurrentHashMap<>();
	private final Map<Long, Listing> listings = new ConcurrentHashMap<>();
	private final Map<Long, Order> orders = new ConcurrentHashMap<>();

	// ---------------------- Public API ----------------------

	public Seller registerSeller(String name, String contact) {
		Objects.requireNonNull(name, "name");
		long id = sellerIdSeq.getAndIncrement();
		Seller s = new Seller(id, name, contact, Instant.now());
		sellers.put(id, s);
		return s;
	}

	public Buyer registerBuyer(String name, String contact) {
		Objects.requireNonNull(name, "name");
		long id = buyerIdSeq.getAndIncrement();
		Buyer b = new Buyer(id, name, contact, Instant.now());
		buyers.put(id, b);
		return b;
	}

	public Product createProduct(long sellerId, String title, String description) {
		Seller s = getSellerOrThrow(sellerId);
		Objects.requireNonNull(title, "title");
		long id = productIdSeq.getAndIncrement();
		Product p = new Product(id, sellerId, title, description, Instant.now());
		products.put(id, p);
		s.productIds.add(id);
		return p;
	}

	public Listing createListing(long productId, double price, int quantity) {
		Product p = getProductOrThrow(productId);
		if (price < 0 || quantity < 0) throw new IllegalArgumentException("invalid price or quantity");
		long id = listingIdSeq.getAndIncrement();
		Listing l = new Listing(id, productId, p.sellerId, price, quantity, Instant.now());
		listings.put(id, l);
		p.listingIds.add(id);
		return l;
	}

	public List<Listing> searchListings(String query, Double minPrice, Double maxPrice, int limit) {
		String q = query == null ? "" : query.trim().toLowerCase();
		return listings.values().stream()
				.filter(l -> l.quantity > 0)
				.filter(l -> (minPrice == null || l.price >= minPrice) && (maxPrice == null || l.price <= maxPrice))
				.filter(l -> q.isEmpty() || productMatches(l.productId, q))
				.sorted(Comparator.comparing(Listing::getCreatedAt).reversed())
				.limit(Math.max(0, limit))
				.collect(Collectors.toList());
	}

	public Order placeOrder(long buyerId, Map<Long, Integer> listingQuantities) {
		Buyer buyer = getBuyerOrThrow(buyerId);
		Objects.requireNonNull(listingQuantities, "listingQuantities");
		if (listingQuantities.isEmpty()) throw new IllegalArgumentException("empty order");

		// Reserve inventory by decrementing listing quantities atomically
		List<OrderItem> items = new ArrayList<>();
		for (Map.Entry<Long, Integer> e : listingQuantities.entrySet()) {
			long listingId = e.getKey();
			int qty = e.getValue();
			if (qty <= 0) throw new IllegalArgumentException("quantity must be > 0");

			Listing l = listings.get(listingId);
			if (l == null) throw new NoSuchElementException("Listing not found: " + listingId);

			synchronized (l) {
				if (l.quantity < qty) throw new IllegalStateException("Not enough quantity for listing: " + listingId);
				l.quantity -= qty;
			}

			double subtotal = qty * l.price;
			items.add(new OrderItem(listingId, l.productId, l.sellerId, qty, l.price, subtotal));
		}

		long orderId = orderIdSeq.getAndIncrement();
		Order order = new Order(orderId, buyerId, items, Instant.now());
		orders.put(orderId, order);
		buyer.orderIds.add(orderId);
		return order;
	}

	public Review addReview(long buyerId, long orderId, int rating, String message) {
		getBuyerOrThrow(buyerId);
		Order order = getOrderOrThrow(orderId);
		if (!order.buyerIdEquals(buyerId)) throw new IllegalStateException("buyer does not own order");
		if (rating < 1 || rating > 5) throw new IllegalArgumentException("rating must be 1-5");

		long id = reviewIdSeq.getAndIncrement();
		Review r = new Review(id, buyerId, orderId, rating, message, Instant.now());
		// attach review to each seller in the order
		order.items.stream()
				.map(item -> item.sellerId)
				.distinct()
				.forEach(sellerId -> {
					Seller s = sellers.get(sellerId);
					if (s != null) s.reviews.add(r);
				});

		return r;
	}

	// Convenience lookups
	public Product getProduct(long id) { return products.get(id); }
	public Listing getListing(long id) { return listings.get(id); }
	public Order getOrder(long id) { return orders.get(id); }
	public Seller getSeller(long id) { return sellers.get(id); }
	public Buyer getBuyer(long id) { return buyers.get(id); }

	// ---------------------- Helpers ----------------------

	private boolean productMatches(long productId, String q) {
		Product p = products.get(productId);
		if (p == null) return false;
		return p.title.toLowerCase().contains(q) || (p.description != null && p.description.toLowerCase().contains(q));
	}

	private Seller getSellerOrThrow(long id) { Seller s = sellers.get(id); if (s == null) throw new NoSuchElementException("seller not found: " + id); return s; }
	private Buyer getBuyerOrThrow(long id) { Buyer b = buyers.get(id); if (b == null) throw new NoSuchElementException("buyer not found: " + id); return b; }
	private Product getProductOrThrow(long id) { Product p = products.get(id); if (p == null) throw new NoSuchElementException("product not found: " + id); return p; }
	private Order getOrderOrThrow(long id) { Order o = orders.get(id); if (o == null) throw new NoSuchElementException("order not found: " + id); return o; }

	// ---------------------- Domain types ----------------------

	public static class Seller {
		public final long id;
		public String name;
		public String contact;
		public final Instant registeredAt;
		public final List<Long> productIds = new CopyOnWriteArrayList<>();
		public final List<Review> reviews = new CopyOnWriteArrayList<>();

		public Seller(long id, String name, String contact, Instant registeredAt) {
			this.id = id;
			this.name = name;
			this.contact = contact;
			this.registeredAt = registeredAt;
		}

		public double getAverageRating() {
			return reviews.stream().mapToInt(r -> r.rating).average().orElse(0.0);
		}
	}

	public static class Buyer {
		public final long id;
		public String name;
		public String contact;
		public final Instant registeredAt;
		public final List<Long> orderIds = new CopyOnWriteArrayList<>();

		public Buyer(long id, String name, String contact, Instant registeredAt) {
			this.id = id;
			this.name = name;
			this.contact = contact;
			this.registeredAt = registeredAt;
		}
	}

	public static class Product {
		public final long id;
		public final long sellerId;
		public String title;
		public String description;
		public final Instant createdAt;
		public final List<Long> listingIds = new CopyOnWriteArrayList<>();

		public Product(long id, long sellerId, String title, String description, Instant createdAt) {
			this.id = id;
			this.sellerId = sellerId;
			this.title = title;
			this.description = description;
			this.createdAt = createdAt;
		}
	}

	public static class Listing {
		public final long id;
		public final long productId;
		public final long sellerId;
		public double price;
		public int quantity;
		private final Instant createdAt;

		public Listing(long id, long productId, long sellerId, double price, int quantity, Instant createdAt) {
			this.id = id;
			this.productId = productId;
			this.sellerId = sellerId;
			this.price = price;
			this.quantity = quantity;
			this.createdAt = createdAt;
		}

		public Instant getCreatedAt() { return createdAt; }
	}

	public static class Order {
		public final long id;
		public final long buyerId;
		public final List<OrderItem> items;
		public final Instant createdAt;

		public Order(long id, long buyerId, List<OrderItem> items, Instant createdAt) {
			this.id = id;
			this.buyerId = buyerId;
			this.items = Collections.unmodifiableList(new ArrayList<>(items));
			this.createdAt = createdAt;
		}

		public double total() { return items.stream().mapToDouble(i -> i.subtotal).sum(); }

		public boolean buyerIdEquals(long id) { return this.buyerId == id; }
	}

	public static class OrderItem {
		public final long listingId;
		public final long productId;
		public final long sellerId;
		public final int quantity;
		public final double price;
		public final double subtotal;

		public OrderItem(long listingId, long productId, long sellerId, int quantity, double price, double subtotal) {
			this.listingId = listingId;
			this.productId = productId;
			this.sellerId = sellerId;
			this.quantity = quantity;
			this.price = price;
			this.subtotal = subtotal;
		}
	}

	public static class Review {
		public final long id;
		public final long buyerId;
		public final long orderId;
		public final int rating; // 1..5
		public final String message;
		public final Instant createdAt;

		public Review(long id, long buyerId, long orderId, int rating, String message, Instant createdAt) {
			this.id = id;
			this.buyerId = buyerId;
			this.orderId = orderId;
			this.rating = rating;
			this.message = message;
			this.createdAt = createdAt;
		}
	}

	// ---------------------- Demo entrypoint ----------------------

	public static void main(String[] args) {
		MarketplacePortal portal = new MarketplacePortal();
		Seller s = portal.registerSeller("Acme Inc.", "acme@example.com");
		Buyer b = portal.registerBuyer("Jane Doe", "jane@example.com");

		Product p = portal.createProduct(s.id, "Widget", "A useful widget");
		Listing l = portal.createListing(p.id, 9.99, 10);

		Map<Long, Integer> orderReq = new HashMap<>();
		orderReq.put(l.id, 2);
		Order ord = portal.placeOrder(b.id, orderReq);

		portal.addReview(b.id, ord.id, 5, "Great item and fast shipping");

		System.out.println("Demo complete — order total=" + ord.total());
	}

}

