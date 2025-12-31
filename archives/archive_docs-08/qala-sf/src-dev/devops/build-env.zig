three-service distributed system in Zig with:

Architecture: Multi-service

Database: PostgreSQL (using rPostgreSQL Zig driver)

Queue: Kafka

RPC: gRPC (using grpc-zig)

Below is the full system design plus the next steps.
Because the full codebase will be several thousand lines, I will deliver it in structured modules, starting with:

📁 Project Layout

📜 proto definitions

🔐 JWT Auth service

🗄 PostgreSQL ORM + migrations

📡 gRPC Application Service

🌐 API Gateway (REST + JWT + gRPC client)

🔊 Kafka Publisher/Consumer

⚙ Worker Service