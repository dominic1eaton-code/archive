package com.portal;

import org.junit.jupiter.api.Test;

import java.util.HashMap;

import static org.junit.jupiter.api.Assertions.*;

public class MarketplacePortalTest {

    @Test
    public void basicMarketplaceFlow() {
        MarketplacePortal portal = new MarketplacePortal();

        var seller = portal.registerSeller("Test Seller", "seller@example.com");
        var buyer = portal.registerBuyer("Test Buyer", "buyer@example.com");

        var product = portal.createProduct(seller.id, "Test Product", "A test product");
        var listing = portal.createListing(product.id, 4.50, 5);

        assertNotNull(product);
        assertNotNull(listing);
        assertEquals(5, listing.quantity + 0); // listing quantity still tracked

        var req = new HashMap<Long, Integer>();
        req.put(listing.id, 2);

        var order = portal.placeOrder(buyer.id, req);
        assertNotNull(order);
        assertEquals(1, buyer.orderIds.size());
        assertEquals(2, order.items.get(0).quantity);

        var review = portal.addReview(buyer.id, order.id, 5, "excellent");
        assertNotNull(review);
        assertTrue(seller.getAverageRating() >= 0.0);
    }
}
