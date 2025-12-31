# Portal Module

This module contains lightweight example portal implementations used for learning and small demos.

- CommunityPortal — social/community features
- GigPortal — simple gig-worker/job system
- KogiPortal — tiny app bootstrap
- MarketplacePortal — in-memory marketplace (products, listings, orders, reviews)

MarketplacePortal is a single-file, self-contained class (in `src/main/java/com/portal/MarketplacePortal.java`) that provides thread-friendly, in-memory objects suitable for local testing and exploration. It is not intended for production use — to make it production-ready you would add persistence, validation, authentication, and API layers.

Example (quick):

```java
MarketplacePortal portal = new MarketplacePortal();
Seller s = portal.registerSeller("Acme", "acme@example.com");
Buyer b = portal.registerBuyer("Jane", "jane@example.com");
Product p = portal.createProduct(s.id, "Widget", "... ");
Listing l = portal.createListing(p.id, 9.99, 10);
Map<Long,Integer> orderReq = Map.of(l.id, 2);
Order o = portal.placeOrder(b.id, orderReq);
portal.addReview(b.id, o.id, 5, "Awesome");
```
