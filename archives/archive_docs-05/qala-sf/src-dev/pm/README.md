# Design Overview

A general-purpose artifact repository needs to handle:

Storage & Retrieval

Store binary artifacts (files, packages, libraries).

Retrieve artifacts by name, version, or hash.

Metadata Management

Keep track of artifact metadata: name, version, checksum, creation date, dependencies.

APIs

HTTP API to upload/download artifacts.

Optional REST endpoints for querying metadata.

Security & Integrity

Verify checksums.

Optional authentication.

File Storage


We can add REST API endpoints:

Endpoint	Method	Description
/upload	POST	Upload artifact (auth required)
/download?name=x&version=y	GET	Download artifact by version
/latest?name=x	GET	Get latest version metadata
/search?q=term	GET	Search artifacts by name


✅ Summary of Enhancements

Metadata storage: SQLite or JSON with easy swap interface.

Versioning: Semantic version comparison & multiple versions supported.

Authentication: Token-based access control.

Search & query: REST endpoints for search, latest, download.

HTTP parsing: Use Zig HTTP framework for robustness.

# How to run

Fetch and include zig-sqlite (e.g. via zig fetch …) so that @import("sqlite") works. 
GitHub
+1

zig build (or zig build run) — this builds the server.

Start server. It will listen on port 8080.

Use HTTP requests:

Upload (POST to /upload) — JSON body with name, version, data (base64) + header Authorization: Bearer secret-token-123.

Download (GET /download?name=foo&version=1.0.0) — returns raw file data.

Search (GET /search?q=foo) — returns JSON list of metadata for all versions of artifact foo.

Metadata persists in artifacts.db. Files stored under storage/.

⚠️ Caveats & What You Should Expand

This example only supports in‑memory base64 upload; for real binaries bigger than memory, you’d want streaming upload and file writing.

Authentication is trivial — just a token. For real use: hashed passwords, user database, sessions, ACLs.

Concurrency and request isolation: this code is single‑threaded; you'd likely want to spawn a new task or thread per request and ensure sqlite.Db is safe to share or use a connection pool.

No cleanup, no version deletion, no access controls (other than simple token).

Error handling is minimal.

No MIME‑type detection or other metadata (e.g. content‑type, size).

The “latest version” logic in download is incomplete — you’d need to implement picking the highest semantic version using version.zig.