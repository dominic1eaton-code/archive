

📁 Project Layout

📜 proto definitions

🔐 JWT Auth service

🗄 PostgreSQL ORM + migrations

📡 gRPC Application Service

🌐 API Gateway (REST + JWT + gRPC client)

🔊 Kafka Publisher/Consumer

⚙ Worker Service




grpc-zig --out app-service/src/gen/ --proto proto/app.proto
grpc-zig --out api-gateway/src/gen/ --proto proto/app.proto


##
JWT access + refresh tokens
✅ Users table (login / register)
✅ Rate limiting middleware
✅ Logging middleware
✅ REST → gRPC forwarding
✅ Configurable auth rules
✅ Production-grade structure

##
worker-service

Kafka consumer + background processing:

Will include:

✔ Kafka consumer (librdkafka)
✔ Background job processor
✔ PostgreSQL updates
✔ Config loader
✔ Async workers
✔ main.zig