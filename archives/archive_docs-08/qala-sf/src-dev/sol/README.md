# software solution factory management system

File persistence: Products are saved to products.json and loaded on startup.

Interactive console menu: Users can create, build, test, release, and list products.

Pipeline enforcement: Products can only advance in order (Created → Built → Tested → Released).

Fully extendable for more stages or attributes.



✅ New Features:

Automatic version incrementing:

Minor version increases on each build (e.g., 0.11 → 0.12).

Build history tracking:

Stores timestamps and versions for each build.

Listed when showing product details.

Still compatible with pipeline logic: only builds → tests → releases.