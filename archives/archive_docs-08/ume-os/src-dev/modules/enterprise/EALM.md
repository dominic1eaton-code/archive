Skip to content
You said:
create an enterprise architecture lifecycle management system in rust
ChatGPT said:
Got it! Let’s break this down carefully. You want an Enterprise Architecture Lifecycle Management (EALM) system implemented in Rust. I’ll guide you through a solid architecture and a starting implementation strategy. We’ll make it modular, maintainable, and realistic for a production-grade system.

1. Define the System
An EALM system typically involves:

Architecture Artifacts

Business, Data, Application, Technology layers (e.g., TOGAF ADM)

Relationships between artifacts

Lifecycle Management

Create, Update, Retire, Version artifacts

Track dependencies

Governance & Compliance

Rules for approving changes

Reporting

Visualization & Reporting

Export architecture diagrams

Dashboards for lifecycle status

2. High-Level Rust Architecture
Rust is great for backend systems. For an EALM system, we could structure it as:

src/
├─ main.rs             # Entry point
├─ api/
│  ├─ mod.rs           # API module
│  └─ routes.rs        # REST API routes
├─ models/
│  ├─ mod.rs           # Models for artifacts, versions, etc.
│  └─ artifact.rs
├─ storage/
│  ├─ mod.rs           # Storage interface
│  └─ db.rs            # DB implementation (Postgres/SQLite)
├─ services/
│  ├─ mod.rs           # Business logic
│  └─ artifact_service.rs
├─ utils/
│  └─ mod.rs
Dependencies (Cargo.toml)
[package]
name = "ealm_system"
version = "0.1.0"
edition = "2021"

[dependencies]
actix-web = "4.3"        # Web framework
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
sqlx = { version = "0.7", features = ["postgres", "runtime-tokio-native-tls", "macros"] }
uuid = { version = "1.3", features = ["v4"] }
chrono = "0.4"
dotenvy = "0.15"
3. Define Models
For example, an Artifact model:

use serde::{Serialize, Deserialize};
use uuid::Uuid;
use chrono::{DateTime, Utc};

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct Artifact {
    pub id: Uuid,
    pub name: String,
    pub description: Option<String>,
    pub artifact_type: ArtifactType,
    pub version: i32,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
    pub status: LifecycleStatus,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub enum ArtifactType {
    Business,
    Data,
    Application,
    Technology,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub enum LifecycleStatus {
    Draft,
    Approved,
    Retired,
}
4. Storage Layer (SQLX + PostgreSQL)
use sqlx::postgres::PgPoolOptions;
use sqlx::PgPool;

pub async fn get_db_pool() -> PgPool {
    let database_url = std::env::var("DATABASE_URL").expect("DATABASE_URL must be set");
    PgPoolOptions::new()
        .max_connections(5)
        .connect(&database_url)
        .await
        .expect("Failed to connect to database")
}
5. Service Layer (Business Logic)
use crate::models::artifact::{Artifact, LifecycleStatus};
use uuid::Uuid;
use chrono::Utc;

pub fn create_artifact(name: &str, artifact_type: &str) -> Artifact {
    Artifact {
        id: Uuid::new_v4(),
        name: name.to_string(),
        description: None,
        artifact_type: match artifact_type {
            "Business" => crate::models::artifact::ArtifactType::Business,
            "Data" => crate::models::artifact::ArtifactType::Data,
            "Application" => crate::models::artifact::ArtifactType::Application,
            "Technology" => crate::models::artifact::ArtifactType::Technology,
            _ => crate::models::artifact::ArtifactType::Business,
        },
        version: 1,
        created_at: Utc::now(),
        updated_at: Utc::now(),
        status: LifecycleStatus::Draft,
    }
}
6. API Layer (Actix-Web)
use actix_web::{get, post, web, App, HttpServer, Responder};
use crate::services::artifact_service;
use serde_json::json;

#[post("/artifact")]
async fn create_artifact_api(info: web::Json<CreateArtifactRequest>) -> impl Responder {
    let artifact = artifact_service::create_artifact(&info.name, &info.artifact_type);
    web::Json(json!(artifact))
}

#[derive(serde::Deserialize)]
struct CreateArtifactRequest {
    name: String,
    artifact_type: String,
}

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    HttpServer::new(|| App::new().service(create_artifact_api))
        .bind(("127.0.0.1", 8080))?
        .run()
        .await
}
7. Next Steps / Enhancements
Versioning: Track artifact changes over time.

Relationships: Connect artifacts across layers (dependencies).

Workflow / Approval: Implement lifecycle transitions.

Persistence: Full SQL CRUD using SQLx.

UI: Optional frontend with Actix or serve a web app via API.

If you want, I can create a fully functional Rust prototype of this system with CRUD operations, lifecycle management, and versioning ready to run. This would be a minimal, working EALM system.

Do you want me to do that next?

You said:
create a fully functional Rust prototype of this system with CRUD operations, lifecycle management, and versioning
ChatGPT said:
Perfect! Let’s build a fully functional Rust prototype of an Enterprise Architecture Lifecycle Management (EALM) system with:

CRUD operations for artifacts

Lifecycle management (Draft → Approved → Retired)

Versioning

We'll use Actix-Web, SQLx with PostgreSQL, and Serde for JSON serialization. I’ll provide a ready-to-run minimal prototype.

1. Project Setup
cargo new ealm_system --bin
cd ealm_system
cargo add actix-web sqlx tokio serde serde_json uuid chrono dotenvy
Add Cargo.toml dependencies:

[package]
name = "ealm_system"
version = "0.1.0"
edition = "2021"

[dependencies]
actix-web = "4.3"
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
sqlx = { version = "0.7", features = ["postgres", "runtime-tokio-native-tls", "macros"] }
uuid = { version = "1.3", features = ["v4"] }
chrono = "0.4"
dotenvy = "0.15"
tokio = { version = "1", features = ["macros", "rt-multi-thread"] }
Create a .env file:

DATABASE_URL=postgres://username:password@localhost/ealm_db
2. Models
src/models/artifact.rs:

use serde::{Serialize, Deserialize};
use uuid::Uuid;
use chrono::{DateTime, Utc};

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct Artifact {
    pub id: Uuid,
    pub name: String,
    pub description: Option<String>,
    pub artifact_type: ArtifactType,
    pub version: i32,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
    pub status: LifecycleStatus,
}

#[derive(Debug, Serialize, Deserialize, Clone, sqlx::Type)]
#[sqlx(type_name = "artifact_type")]
pub enum ArtifactType {
    Business,
    Data,
    Application,
    Technology,
}

#[derive(Debug, Serialize, Deserialize, Clone, sqlx::Type)]
#[sqlx(type_name = "lifecycle_status")]
pub enum LifecycleStatus {
    Draft,
    Approved,
    Retired,
}
src/models/mod.rs:

pub mod artifact;
3. Database Layer
src/storage/db.rs:

use sqlx::postgres::PgPoolOptions;
use sqlx::PgPool;
use dotenvy::dotenv;
use std::env;

pub async fn get_db_pool() -> PgPool {
    dotenv().ok();
    let database_url = env::var("DATABASE_URL").expect("DATABASE_URL must be set");
    PgPoolOptions::new()
        .max_connections(5)
        .connect(&database_url)
        .await
        .expect("Failed to connect to database")
}
4. Artifact Service (CRUD + Lifecycle)
src/services/artifact_service.rs:

use crate::models::artifact::{Artifact, ArtifactType, LifecycleStatus};
use sqlx::PgPool;
use uuid::Uuid;
use chrono::Utc;

pub async fn create_artifact(pool: &PgPool, name: &str, artifact_type: ArtifactType) -> Artifact {
    let id = Uuid::new_v4();
    let version = 1;
    let created_at = Utc::now();
    let updated_at = Utc::now();
    let status = LifecycleStatus::Draft;

    sqlx::query!(
        r#"
        INSERT INTO artifacts (id, name, artifact_type, version, created_at, updated_at, status)
        VALUES ($1, $2, $3, $4, $5, $6, $7)
        "#,
        id,
        name,
        format!("{:?}", artifact_type),
        version,
        created_at,
        updated_at,
        format!("{:?}", status)
    )
    .execute(pool)
    .await
    .unwrap();

    Artifact { id, name: name.to_string(), description: None, artifact_type, version, created_at, updated_at, status }
}

pub async fn get_artifact(pool: &PgPool, id: Uuid) -> Option<Artifact> {
    let row = sqlx::query!(
        r#"
        SELECT id, name, artifact_type, version, created_at, updated_at, status
        FROM artifacts WHERE id = $1
        "#,
        id
    )
    .fetch_one(pool)
    .await
    .ok()?;

    Some(Artifact {
        id: row.id,
        name: row.name,
        description: None,
        artifact_type: match row.artifact_type.as_str() {
            "Business" => ArtifactType::Business,
            "Data" => ArtifactType::Data,
            "Application" => ArtifactType::Application,
            "Technology" => ArtifactType::Technology,
            _ => ArtifactType::Business,
        },
        version: row.version,
        created_at: row.created_at,
        updated_at: row.updated_at,
        status: match row.status.as_str() {
            "Draft" => LifecycleStatus::Draft,
            "Approved" => LifecycleStatus::Approved,
            "Retired" => LifecycleStatus::Retired,
            _ => LifecycleStatus::Draft,
        },
    })
}

pub async fn update_artifact_status(pool: &PgPool, id: Uuid, status: LifecycleStatus) -> Option<Artifact> {
    let updated_at = Utc::now();

    sqlx::query!(
        r#"
        UPDATE artifacts SET status = $1, updated_at = $2
        WHERE id = $3
        "#,
        format!("{:?}", status),
        updated_at,
        id
    )
    .execute(pool)
    .await
    .ok()?;

    get_artifact(pool, id).await
}
src/services/mod.rs:

pub mod artifact_service;
5. API Layer
src/api/routes.rs:

use actix_web::{get, post, web, Responder};
use serde::Deserialize;
use uuid::Uuid;
use crate::services::artifact_service;
use crate::storage::db::get_db_pool;
use crate::models::artifact::ArtifactType;
use serde_json::json;

#[derive(Deserialize)]
pub struct CreateArtifactRequest {
    name: String,
    artifact_type: String,
}

#[post("/artifact")]
pub async fn create_artifact(info: web::Json<CreateArtifactRequest>) -> impl Responder {
    let pool = get_db_pool().await;
    let artifact_type = match info.artifact_type.as_str() {
        "Business" => ArtifactType::Business,
        "Data" => ArtifactType::Data,
        "Application" => ArtifactType::Application,
        "Technology" => ArtifactType::Technology,
        _ => ArtifactType::Business,
    };
    let artifact = artifact_service::create_artifact(&pool, &info.name, artifact_type).await;
    web::Json(json!(artifact))
}

#[get("/artifact/{id}")]
pub async fn get_artifact(web::Path(id): web::Path<Uuid>) -> impl Responder {
    let pool = get_db_pool().await;
    if let Some(artifact) = artifact_service::get_artifact(&pool, id).await {
        web::Json(json!(artifact))
    } else {
        web::HttpResponse::NotFound().finish()
    }
}
src/api/mod.rs:

pub mod routes;
6. Main File
src/main.rs:

use actix_web::{App, HttpServer};
use ealm_system::api::routes::{create_artifact, get_artifact};

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    HttpServer::new(|| {
        App::new()
            .service(create_artifact)
            .service(get_artifact)
    })
    .bind(("127.0.0.1", 8080))?
    .run()
    .await
}
7. Database Schema
CREATE TYPE artifact_type AS ENUM ('Business', 'Data', 'Application', 'Technology');
CREATE TYPE lifecycle_status AS ENUM ('Draft', 'Approved', 'Retired');

CREATE TABLE artifacts (
    id UUID PRIMARY KEY,
    name TEXT NOT NULL,
    artifact_type artifact_type NOT NULL,
    version INT NOT NULL,
    created_at TIMESTAMP WITH TIME ZONE NOT NULL,
    updated_at TIMESTAMP WITH TIME ZONE NOT NULL,
    status lifecycle_status NOT NULL
);
✅ This prototype supports:

Creating artifacts (POST /artifact)

Fetching artifacts (GET /artifact/{id})

Lifecycle management via update_artifact_status function

Versioning initialized at 1 (can be incremented on updates)

If you want, I can expand this to include:

Full CRUD (Update/Delete)

Automatic version increment on updates

Listing all artifacts with filters by status/type

This would make it a fully functional EALM system in Rust.

Do you want me to do that next?

You said:
n expand this to include:

Full CRUD (Update/Delete)

Automatic version increment on updates

Listing all artifacts with filters by status/type
ChatGPT said:
Perfect! Let’s expand the Rust EALM prototype to include:

Full CRUD: Create, Read, Update, Delete

Automatic version increment on updates

Listing artifacts with filters (by status and artifact_type)

We’ll modify the service and API layers accordingly.

1. Service Layer: Full CRUD + Versioning
Update src/services/artifact_service.rs:

use crate::models::artifact::{Artifact, ArtifactType, LifecycleStatus};
use sqlx::PgPool;
use uuid::Uuid;
use chrono::Utc;

// Create artifact
pub async fn create_artifact(pool: &PgPool, name: &str, artifact_type: ArtifactType) -> Artifact {
    let id = Uuid::new_v4();
    let version = 1;
    let created_at = Utc::now();
    let updated_at = Utc::now();
    let status = LifecycleStatus::Draft;

    sqlx::query!(
        r#"
        INSERT INTO artifacts (id, name, artifact_type, version, created_at, updated_at, status)
        VALUES ($1, $2, $3, $4, $5, $6, $7)
        "#,
        id,
        name,
        format!("{:?}", artifact_type),
        version,
        created_at,
        updated_at,
        format!("{:?}", status)
    )
    .execute(pool)
    .await
    .unwrap();

    Artifact { id, name: name.to_string(), description: None, artifact_type, version, created_at, updated_at, status }
}

// Get single artifact
pub async fn get_artifact(pool: &PgPool, id: Uuid) -> Option<Artifact> {
    let row = sqlx::query!(
        r#"
        SELECT id, name, artifact_type, version, created_at, updated_at, status
        FROM artifacts WHERE id = $1
        "#,
        id
    )
    .fetch_one(pool)
    .await
    .ok()?;

    Some(Artifact {
        id: row.id,
        name: row.name,
        description: None,
        artifact_type: match row.artifact_type.as_str() {
            "Business" => ArtifactType::Business,
            "Data" => ArtifactType::Data,
            "Application" => ArtifactType::Application,
            "Technology" => ArtifactType::Technology,
            _ => ArtifactType::Business,
        },
        version: row.version,
        created_at: row.created_at,
        updated_at: row.updated_at,
        status: match row.status.as_str() {
            "Draft" => LifecycleStatus::Draft,
            "Approved" => LifecycleStatus::Approved,
            "Retired" => LifecycleStatus::Retired,
            _ => LifecycleStatus::Draft,
        },
    })
}

// Update artifact with automatic version increment
pub async fn update_artifact(pool: &PgPool, id: Uuid, new_name: Option<&str>, new_status: Option<LifecycleStatus>) -> Option<Artifact> {
    let mut artifact = get_artifact(pool, id).await?;

    if let Some(name) = new_name {
        artifact.name = name.to_string();
    }
    if let Some(status) = new_status {
        artifact.status = status;
    }

    artifact.version += 1;
    artifact.updated_at = Utc::now();

    sqlx::query!(
        r#"
        UPDATE artifacts
        SET name = $1, version = $2, updated_at = $3, status = $4
        WHERE id = $5
        "#,
        artifact.name,
        artifact.version,
        artifact.updated_at,
        format!("{:?}", artifact.status),
        id
    )
    .execute(pool)
    .await
    .ok()?;

    Some(artifact)
}

// Delete artifact
pub async fn delete_artifact(pool: &PgPool, id: Uuid) -> bool {
    sqlx::query!("DELETE FROM artifacts WHERE id = $1", id)
        .execute(pool)
        .await
        .ok()
        .map_or(false, |res| res.rows_affected() > 0)
}

// List artifacts with optional filters
pub async fn list_artifacts(pool: &PgPool, status: Option<LifecycleStatus>, artifact_type: Option<ArtifactType>) -> Vec<Artifact> {
    let mut query = "SELECT id, name, artifact_type, version, created_at, updated_at, status FROM artifacts".to_string();
    let mut conditions = vec![];
    let mut args: Vec<String> = vec![];

    if let Some(s) = &status {
        conditions.push(format!("status = ${}", args.len() + 1));
        args.push(format!("{:?}", s));
    }
    if let Some(a_type) = &artifact_type {
        conditions.push(format!("artifact_type = ${}", args.len() + 1));
        args.push(format!("{:?}", a_type));
    }

    if !conditions.is_empty() {
        query.push_str(" WHERE ");
        query.push_str(&conditions.join(" AND "));
    }

    let rows = sqlx::query(&query).bind_all(args).fetch_all(pool).await.unwrap();

    rows.into_iter().map(|row| Artifact {
        id: row.get("id"),
        name: row.get("name"),
        description: None,
        artifact_type: match row.get::<String, _>("artifact_type").as_str() {
            "Business" => ArtifactType::Business,
            "Data" => ArtifactType::Data,
            "Application" => ArtifactType::Application,
            "Technology" => ArtifactType::Technology,
            _ => ArtifactType::Business,
        },
        version: row.get("version"),
        created_at: row.get("created_at"),
        updated_at: row.get("updated_at"),
        status: match row.get::<String, _>("status").as_str() {
            "Draft" => LifecycleStatus::Draft,
            "Approved" => LifecycleStatus::Approved,
            "Retired" => LifecycleStatus::Retired,
            _ => LifecycleStatus::Draft,
        },
    }).collect()
}
2. API Layer: Routes for CRUD + List
Update src/api/routes.rs:

use actix_web::{get, post, put, delete, web, Responder};
use serde::Deserialize;
use uuid::Uuid;
use crate::services::artifact_service;
use crate::storage::db::get_db_pool;
use crate::models::artifact::{ArtifactType, LifecycleStatus};
use serde_json::json;

#[derive(Deserialize)]
pub struct CreateArtifactRequest {
    name: String,
    artifact_type: String,
}

#[derive(Deserialize)]
pub struct UpdateArtifactRequest {
    name: Option<String>,
    status: Option<String>,
}

#[derive(Deserialize)]
pub struct ListArtifactsQuery {
    status: Option<String>,
    artifact_type: Option<String>,
}

#[post("/artifact")]
pub async fn create_artifact(info: web::Json<CreateArtifactRequest>) -> impl Responder {
    let pool = get_db_pool().await;
    let artifact_type = match info.artifact_type.as_str() {
        "Business" => ArtifactType::Business,
        "Data" => ArtifactType::Data,
        "Application" => ArtifactType::Application,
        "Technology" => ArtifactType::Technology,
        _ => ArtifactType::Business,
    };
    let artifact = artifact_service::create_artifact(&pool, &info.name, artifact_type).await;
    web::Json(json!(artifact))
}

#[get("/artifact/{id}")]
pub async fn get_artifact(web::Path(id): web::Path<Uuid>) -> impl Responder {
    let pool = get_db_pool().await;
    if let Some(artifact) = artifact_service::get_artifact(&pool, id).await {
        web::Json(json!(artifact))
    } else {
        web::HttpResponse::NotFound().finish()
    }
}

#[put("/artifact/{id}")]
pub async fn update_artifact(web::Path(id): web::Path<Uuid>, info: web::Json<UpdateArtifactRequest>) -> impl Responder {
    let pool = get_db_pool().await;
    let status = info.status.as_ref().map(|s| match s.as_str() {
        "Draft" => LifecycleStatus::Draft,
        "Approved" => LifecycleStatus::Approved,
        "Retired" => LifecycleStatus::Retired,
        _ => LifecycleStatus::Draft,
    });
    if let Some(artifact) = artifact_service::update_artifact(&pool, id, info.name.as_deref(), status).await {
        web::Json(json!(artifact))
    } else {
        web::HttpResponse::NotFound().finish()
    }
}

#[delete("/artifact/{id}")]
pub async fn delete_artifact(web::Path(id): web::Path<Uuid>) -> impl Responder {
    let pool = get_db_pool().await;
    if artifact_service::delete_artifact(&pool, id).await {
        web::HttpResponse::Ok().finish()
    } else {
        web::HttpResponse::NotFound().finish()
    }
}

#[get("/artifacts")]
pub async fn list_artifacts(web::Query(query): web::Query<ListArtifactsQuery>) -> impl Responder {
    let pool = get_db_pool().await;
    let status = query.status.as_ref().map(|s| match s.as_str() {
        "Draft" => LifecycleStatus::Draft,
        "Approved" => LifecycleStatus::Approved,
        "Retired" => LifecycleStatus::Retired,
        _ => LifecycleStatus::Draft,
    });
    let artifact_type = query.artifact_type.as_ref().map(|s| match s.as_str() {
        "Business" => ArtifactType::Business,
        "Data" => ArtifactType::Data,
        "Application" => ArtifactType::Application,
        "Technology" => ArtifactType::Technology,
        _ => ArtifactType::Business,
    });

    let artifacts = artifact_service::list_artifacts(&pool, status, artifact_type).await;
    web::Json(json!(artifacts))
}
3. Main File
src/main.rs:

use actix_web::{App, HttpServer};
use ealm_system::api::routes::{create_artifact, get_artifact, update_artifact, delete_artifact, list_artifacts};

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    HttpServer::new(|| {
        App::new()
            .service(create_artifact)
            .service(get_artifact)
            .service(update_artifact)
            .service(delete_artifact)
            .service(list_artifacts)
    })
    .bind(("127.0.0.1", 8080))?
    .run()
    .await
}
✅ Features Now Supported
Create artifact (POST /artifact)

Read artifact (GET /artifact/{id})

Update artifact with version increment (PUT /artifact/{id})

Delete artifact (DELETE /artifact/{id})

List artifacts with optional filters (GET /artifacts?status=Draft&artifact_type=Business)

Lifecycle management (Draft, Approved, Retired)

Automatic versioning on updates

If you want, I can also add relationships between artifacts across layers (Business → Data → Application → Technology), which is a key part of Enterprise Architecture modeling. This would make the prototype even closer to a real EALM system.

Do you want me to add artifact relationships next?

You said:
add relationships between artifacts across layers
ChatGPT said:
Perfect! Let’s extend your Rust EALM system to include relationships between artifacts across layers, which is a core part of Enterprise Architecture modeling (Business → Data → Application → Technology).

We’ll implement:

Relationship model

CRUD operations for relationships

Linking artifacts across layers

Listing relationships for a given artifact

1. Database Schema for Relationships
Add a new table for artifact relationships:

CREATE TABLE artifact_relationships (
    id UUID PRIMARY KEY,
    source_artifact UUID NOT NULL REFERENCES artifacts(id) ON DELETE CASCADE,
    target_artifact UUID NOT NULL REFERENCES artifacts(id) ON DELETE CASCADE,
    relationship_type TEXT NOT NULL,
    created_at TIMESTAMP WITH TIME ZONE NOT NULL
);
source_artifact: The artifact initiating the relationship

target_artifact: The artifact it connects to

relationship_type: E.g., depends_on, realizes, uses

2. Relationship Model
src/models/relationship.rs:

use serde::{Serialize, Deserialize};
use uuid::Uuid;
use chrono::{DateTime, Utc};

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct ArtifactRelationship {
    pub id: Uuid,
    pub source_artifact: Uuid,
    pub target_artifact: Uuid,
    pub relationship_type: String,
    pub created_at: DateTime<Utc>,
}
src/models/mod.rs:

pub mod artifact;
pub mod relationship;
3. Service Layer for Relationships
src/services/relationship_service.rs:

use crate::models::relationship::ArtifactRelationship;
use sqlx::PgPool;
use uuid::Uuid;
use chrono::Utc;

// Create relationship
pub async fn create_relationship(pool: &PgPool, source: Uuid, target: Uuid, relationship_type: &str) -> ArtifactRelationship {
    let id = Uuid::new_v4();
    let created_at = Utc::now();

    sqlx::query!(
        r#"
        INSERT INTO artifact_relationships (id, source_artifact, target_artifact, relationship_type, created_at)
        VALUES ($1, $2, $3, $4, $5)
        "#,
        id, source, target, relationship_type, created_at
    )
    .execute(pool)
    .await
    .unwrap();

    ArtifactRelationship { id, source_artifact: source, target_artifact: target, relationship_type: relationship_type.to_string(), created_at }
}

// List relationships for an artifact
pub async fn list_relationships(pool: &PgPool, artifact_id: Uuid) -> Vec<ArtifactRelationship> {
    let rows = sqlx::query!(
        r#"
        SELECT id, source_artifact, target_artifact, relationship_type, created_at
        FROM artifact_relationships
        WHERE source_artifact = $1 OR target_artifact = $1
        "#,
        artifact_id
    )
    .fetch_all(pool)
    .await
    .unwrap();

    rows.into_iter()
        .map(|row| ArtifactRelationship {
            id: row.id,
            source_artifact: row.source_artifact,
            target_artifact: row.target_artifact,
            relationship_type: row.relationship_type,
            created_at: row.created_at,
        })
        .collect()
}

// Delete relationship
pub async fn delete_relationship(pool: &PgPool, id: Uuid) -> bool {
    sqlx::query!("DELETE FROM artifact_relationships WHERE id = $1", id)
        .execute(pool)
        .await
        .ok()
        .map_or(false, |res| res.rows_affected() > 0)
}
src/services/mod.rs:

pub mod artifact_service;
pub mod relationship_service;
4. API Layer for Relationships
src/api/routes.rs (add these routes):

use actix_web::{post, get, delete, web, Responder};
use serde::Deserialize;
use uuid::Uuid;
use crate::services::relationship_service;
use crate::storage::db::get_db_pool;
use serde_json::json;

#[derive(Deserialize)]
pub struct CreateRelationshipRequest {
    source_artifact: Uuid,
    target_artifact: Uuid,
    relationship_type: String,
}

#[post("/relationship")]
pub async fn create_relationship(info: web::Json<CreateRelationshipRequest>) -> impl Responder {
    let pool = get_db_pool().await;
    let relationship = relationship_service::create_relationship(
        &pool,
        info.source_artifact,
        info.target_artifact,
        &info.relationship_type
    ).await;
    web::Json(json!(relationship))
}

#[get("/relationships/{artifact_id}")]
pub async fn list_relationships(web::Path(artifact_id): web::Path<Uuid>) -> impl Responder {
    let pool = get_db_pool().await;
    let relationships = relationship_service::list_relationships(&pool, artifact_id).await;
    web::Json(json!(relationships))
}

#[delete("/relationship/{id}")]
pub async fn delete_relationship(web::Path(id): web::Path<Uuid>) -> impl Responder {
    let pool = get_db_pool().await;
    if relationship_service::delete_relationship(&pool, id).await {
        web::HttpResponse::Ok().finish()
    } else {
        web::HttpResponse::NotFound().finish()
    }
}
5. Main File
Update src/main.rs:

use actix_web::{App, HttpServer};
use ealm_system::api::routes::{
    create_artifact, get_artifact, update_artifact, delete_artifact, list_artifacts,
    create_relationship, list_relationships, delete_relationship
};

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    HttpServer::new(|| {
        App::new()
            .service(create_artifact)
            .service(get_artifact)
            .service(update_artifact)
            .service(delete_artifact)
            .service(list_artifacts)
            .service(create_relationship)
            .service(list_relationships)
            .service(delete_relationship)
    })
    .bind(("127.0.0.1", 8080))?
    .run()
    .await
}
6. Features Now Supported
Artifacts CRUD with lifecycle and versioning

Relationships between artifacts across layers

Listing relationships for any artifact

Delete relationships

This allows modeling, for example:

A Business Process artifact depends_on a Data Entity artifact

An Application Component realizes a Business Process

A Technology Component supports an Application Component

I can also create a visualization API that outputs the full architecture as a graph (nodes + edges) showing all artifacts and relationships, which is super useful for enterprise architecture dashboards.

Do you want me to add that visualization API next?

You said:
reate a visualization API that outputs the full architecture as a graph (nodes + edges) showing all artifacts and relationships
ChatGPT said:
Perfect! Let’s add a Visualization API that outputs the full enterprise architecture as a graph—nodes (artifacts) and edges (relationships)—which can later be rendered in a frontend or graph visualization tool like D3.js or Graphviz.

1. API Output Structure
We'll define the JSON response as:

{
  "nodes": [
    { "id": "artifact-uuid", "name": "Artifact Name", "type": "Business", "status": "Draft" }
  ],
  "edges": [
    { "source": "source-uuid", "target": "target-uuid", "relationship_type": "depends_on" }
  ]
}
2. Visualization API Endpoint
src/api/routes.rs (add at the bottom):

use actix_web::get;
use serde::Serialize;
use crate::services::{artifact_service, relationship_service};
use crate::storage::db::get_db_pool;

#[derive(Serialize)]
struct Node {
    id: String,
    name: String,
    artifact_type: String,
    status: String,
}

#[derive(Serialize)]
struct Edge {
    source: String,
    target: String,
    relationship_type: String,
}

#[derive(Serialize)]
struct Graph {
    nodes: Vec<Node>,
    edges: Vec<Edge>,
}

#[get("/visualization")]
pub async fn get_visualization() -> impl actix_web::Responder {
    let pool = get_db_pool().await;

    // Fetch all artifacts
    let artifacts = artifact_service::list_artifacts(&pool, None, None).await;

    // Fetch all relationships
    let mut edges = vec![];
    for artifact in &artifacts {
        let relationships = relationship_service::list_relationships(&pool, artifact.id).await;
        for r in relationships {
            edges.push(Edge {
                source: r.source_artifact.to_string(),
                target: r.target_artifact.to_string(),
                relationship_type: r.relationship_type.clone(),
            });
        }
    }

    // Convert artifacts to nodes
    let nodes: Vec<Node> = artifacts
        .into_iter()
        .map(|a| Node {
            id: a.id.to_string(),
            name: a.name,
            artifact_type: format!("{:?}", a.artifact_type),
            status: format!("{:?}", a.status),
        })
        .collect();

    let graph = Graph { nodes, edges };

    actix_web::web::Json(graph)
}
3. Update Main File
Add the new service:

use ealm_system::api::routes::get_visualization;

App::new()
    .service(create_artifact)
    .service(get_artifact)
    .service(update_artifact)
    .service(delete_artifact)
    .service(list_artifacts)
    .service(create_relationship)
    .service(list_relationships)
    .service(delete_relationship)
    .service(get_visualization) // Add this
4. Features of the Visualization API
Nodes: All artifacts with their id, name, type, and status

Edges: All relationships with source, target, and relationship_type

Filter-ready: Frontend can filter by type/status easily

Graph-ready JSON: Can be used directly with D3.js, Cytoscape.js, or any graph rendering library

Example JSON Output:

{
  "nodes": [
    { "id": "1a2b3c", "name": "Order Process", "artifact_type": "Business", "status": "Draft" },
    { "id": "4d5e6f", "name": "Order DB", "artifact_type": "Data", "status": "Approved" }
  ],
  "edges": [
    { "source": "1a2b3c", "target": "4d5e6f", "relationship_type": "depends_on" }
  ]
}
This gives you a full architecture graph, showing all artifacts and their relationships—perfect for visualization dashboards or further analysis.

I can take it one step further and generate a DOT/Graphviz representation from this API, which allows you to render a diagram directly from Rust.

Do you want me to do that next?

You said:
generate a DOT/Graphviz representation f
ChatGPT said:
Absolutely! Let's extend the visualization API to generate a DOT/Graphviz representation of your enterprise architecture graph. This will allow you to render diagrams directly from Rust or export to Graphviz tools.

1. DOT/Graphviz Generation Function
We’ll add a function that converts artifacts and relationships into DOT format.

src/services/visualization_service.rs:

use crate::services::{artifact_service, relationship_service};
use crate::storage::db::get_db_pool;
use uuid::Uuid;

pub async fn generate_dot() -> String {
    let pool = get_db_pool().await;

    // Fetch all artifacts
    let artifacts = artifact_service::list_artifacts(&pool, None, None).await;

    // Start DOT graph
    let mut dot = String::from("digraph EA {\n    rankdir=LR;\n    node [shape=box, style=filled, color=lightblue];\n");

    // Add nodes
    for a in &artifacts {
        let label = format!("{}\\nType: {:?}\\nStatus: {:?}", a.name, a.artifact_type, a.status);
        dot.push_str(&format!("    \"{}\" [label=\"{}\"];\n", a.id, label));
    }

    // Add edges
    for a in &artifacts {
        let relationships = relationship_service::list_relationships(&pool, a.id).await;
        for r in relationships {
            dot.push_str(&format!(
                "    \"{}\" -> \"{}\" [label=\"{}\"];\n",
                r.source_artifact, r.target_artifact, r.relationship_type
            ));
        }
    }

    dot.push_str("}\n");
    dot
}
2. API Endpoint for DOT Output
src/api/routes.rs (add at the bottom):

use actix_web::get;
use actix_web::HttpResponse;
use crate::services::visualization_service::generate_dot;

#[get("/visualization/dot")]
pub async fn get_dot_visualization() -> impl actix_web::Responder {
    let dot_string = generate_dot().await;
    HttpResponse::Ok()
        .content_type("text/plain")
        .body(dot_string)
}
3. Update Main File
Add the new route:

use ealm_system::api::routes::get_dot_visualization;

App::new()
    .service(create_artifact)
    .service(get_artifact)
    .service(update_artifact)
    .service(delete_artifact)
    .service(list_artifacts)
    .service(create_relationship)
    .service(list_relationships)
    .service(delete_relationship)
    .service(get_visualization)
    .service(get_dot_visualization) // <-- DOT endpoint
4. Example DOT Output
If you have a Business Process Order Process depending on a Data artifact Order DB:

digraph EA {
    rankdir=LR;
    node [shape=box, style=filled, color=lightblue];
    "1a2b3c" [label="Order Process\nType: Business\nStatus: Draft"];
    "4d5e6f" [label="Order DB\nType: Data\nStatus: Approved"];
    "1a2b3c" -> "4d5e6f" [label="depends_on"];
}
You can save this to a .dot file and render:

dot -Tpng architecture.dot -o architecture.png
✅ Features of the DOT Visualization API:

Exports the full enterprise architecture as DOT

Includes artifact labels with name, type, status

Includes relationships as labeled edges

Ready to generate diagrams in Graphviz or integrate into CI/CD dashboards

If you want, I can also color-code the nodes by artifact layer (Business/Data/Application/Technology) and statuses (Draft/Approved/Retired) in the DOT graph for even clearer visualization.

Do you want me to do that next?

You said:
also color-code the nodes by artifact layer (Business/Data/Application/Technology) and statuses (Draft/Approved/Retired) in the DOT graph for even clearer visualization.
ChatGPT said:
Perfect! Let’s enhance the DOT/Graphviz visualization so that nodes are color-coded based on:

Artifact layer (Business/Data/Application/Technology)

Lifecycle status (Draft/Approved/Retired)

This will make the graph much easier to read.

1. DOT Generation with Color-Coding
Update src/services/visualization_service.rs:

use crate::services::{artifact_service, relationship_service};
use crate::storage::db::get_db_pool;

pub async fn generate_dot_colored() -> String {
    let pool = get_db_pool().await;

    // Fetch all artifacts
    let artifacts = artifact_service::list_artifacts(&pool, None, None).await;

    // Define colors by artifact type
    let type_colors = |artifact_type: &str| match artifact_type {
        "Business" => "lightblue",
        "Data" => "lightgreen",
        "Application" => "orange",
        "Technology" => "pink",
        _ => "gray",
    };

    // Define border styles by status
    let status_styles = |status: &str| match status {
        "Draft" => "dashed",
        "Approved" => "solid",
        "Retired" => "dotted",
        _ => "solid",
    };

    // Start DOT graph
    let mut dot = String::from("digraph EA {\n    rankdir=LR;\n");

    // Add nodes with colors and styles
    for a in &artifacts {
        let color = type_colors(&format!("{:?}", a.artifact_type));
        let style = status_styles(&format!("{:?}", a.status));
        let label = format!("{}\\nType: {:?}\\nStatus: {:?}", a.name, a.artifact_type, a.status);

        dot.push_str(&format!(
            "    \"{}\" [label=\"{}\", style=filled, fillcolor={}, color=black, penwidth=2, shape=box, fontsize=10, fontname=\"Arial\", style=\"{}\"];\n",
            a.id, label, color, style
        ));
    }

    // Add edges
    for a in &artifacts {
        let relationships = relationship_service::list_relationships(&pool, a.id).await;
        for r in relationships {
            dot.push_str(&format!(
                "    \"{}\" -> \"{}\" [label=\"{}\", fontsize=10, fontname=\"Arial\"];\n",
                r.source_artifact, r.target_artifact, r.relationship_type
            ));
        }
    }

    dot.push_str("}\n");
    dot
}
2. API Endpoint for Colored DOT Graph
src/api/routes.rs (add endpoint):

use actix_web::get;
use actix_web::HttpResponse;
use crate::services::visualization_service::generate_dot_colored;

#[get("/visualization/dot/colored")]
pub async fn get_dot_colored() -> impl actix_web::Responder {
    let dot_string = generate_dot_colored().await;
    HttpResponse::Ok()
        .content_type("text/plain")
        .body(dot_string)
}
3. Update Main File
Add the new route:

use ealm_system::api::routes::get_dot_colored;

App::new()
    .service(create_artifact)
    .service(get_artifact)
    .service(update_artifact)
    .service(delete_artifact)
    .service(list_artifacts)
    .service(create_relationship)
    .service(list_relationships)
    .service(delete_relationship)
    .service(get_visualization)
    .service(get_dot_visualization)
    .service(get_dot_colored) // <-- colored DOT endpoint
4. Example DOT Output (Colored)
digraph EA {
    rankdir=LR;
    "1a2b3c" [label="Order Process\nType: Business\nStatus: Draft", style=filled, fillcolor=lightblue, color=black, penwidth=2, shape=box, fontsize=10, fontname="Arial", style="dashed"];
    "4d5e6f" [label="Order DB\nType: Data\nStatus: Approved", style=filled, fillcolor=lightgreen, color=black, penwidth=2, shape=box, fontsize=10, fontname="Arial", style="solid"];
    "1a2b3c" -> "4d5e6f" [label="depends_on", fontsize=10, fontname="Arial"];
}
Business artifacts → light blue

Data artifacts → light green

Application artifacts → orange

Technology artifacts → pink

Status determines border style:

Draft → dashed

Approved → solid

Retired → dotted

✅ Features of this enhancement:

Full architecture graph in DOT format

Color-coded by artifact layer

Styled by lifecycle status

Ready for visualization in Graphviz (dot -Tpng colored_graph.dot -o graph.png)

If you want, I can also enhance edges with colors based on relationship types (e.g., depends_on = red, realizes = green, uses = blue) so the diagram is fully color-coded for both nodes and edges.

Do you want me to do that next?




Attach

Search

Study

Voice
No file chosenNo file chosen
ChatGPT can make mistakes. Check important info.
