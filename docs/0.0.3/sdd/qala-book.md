# The Book of Qala
## Comprehensive Design Specification Document
### Qala Software Factory Operating System Platform

---

## Document Control
- **Version**: 1.0.0
- **Date**: January 2026
- **Status**: Final Design Specification
- **Classification**: Implementation-Ready Blueprint

---

# Table of Contents

1. [Executive Summary](#1-executive-summary)
2. [Vision & Mission](#2-vision--mission)
3. [System Architecture](#3-system-architecture)
4. [Core Platform Modules](#4-core-platform-modules)
5. [Technical Specifications](#5-technical-specifications)
6. [Data Architecture](#6-data-architecture)
7. [Security & Privacy](#7-security--privacy)
8. [AI & Analytics Framework](#8-ai--analytics-framework)
9. [Implementation Roadmap](#9-implementation-roadmap)
10. [Deployment & Operations](#10-deployment--operations)

---

# 1. Executive Summary

## 1.1 Platform Overview

**Qala** is a next-generation, fully microservices-based Software Factory Operating System designed to revolutionize enterprise software development lifecycle management. It provides an integrated platform for managing personal and remote Software Development Environments (SDEs), CI/CD pipelines, AI-driven analytics, security, and collaboration across global teams.

### Core Capabilities
- Personal & Remote Software Development Environments (SDEs)
- Digital Workspaces & Content Management System
- Hermetic CI/CD Pipelines with Rollback
- AI Agents for Predictive Recommendations
- Data Platform with Analytics & Master Data Management
- Security Event Management (SEM) with Threat Containment
- Workflow Orchestration & Automation
- Multi-Channel Notifications & Collaboration

## 1.2 Value Proposition

### For Developers
- Rapid SDE provisioning (< 2 hours)
- Snapshot/rollback capabilities for safe experimentation
- AI-assisted coding and workflow optimization
- Seamless local/remote development transitions
- IDE integration (VSCode, PyCharm, Eclipse, Emacs, custom)

### For Organizations
- 95%+ CI/CD build success rate
- Reduced time-to-deployment
- Enterprise-grade security and compliance
- Multi-cloud deployment flexibility
- Comprehensive audit trails and governance

### For Executives
- Measurable productivity gains
- Reduced operational risk
- Predictive analytics for resource planning
- Scalable architecture supporting 10,000+ concurrent SDEs
- Clear ROI through automation and efficiency

## 1.3 Target Market

### Primary Markets
- Enterprise Software Development Organizations (500+ developers)
- DevOps Platform Providers
- Cloud-Native Development Teams
- Regulated Industries (Finance, Healthcare, Government)

### Market Opportunity
- $50B+ Global DevOps & Software Productivity Market
- 60% YoY growth in AI-assisted workflow demand
- Increasing remote/hybrid development team adoption
- Growing need for secure, compliant software delivery

---

# 2. Vision & Mission

## 2.1 Vision Statement

*"To create the world's most comprehensive, intelligent, and secure software development factory platform that empowers teams to build, deploy, and manage software with unprecedented efficiency and reliability."*

## 2.2 Mission Statement

*"Qala unifies development environments, CI/CD pipelines, security, data analytics, and AI-driven insights into a cohesive platform that accelerates software delivery while maintaining enterprise-grade governance and compliance."*

## 2.3 Guiding Principles

1. **Developer First**: Every feature designed with developer experience as priority
2. **Security by Design**: Security integrated at every layer, not bolted on
3. **AI-Augmented**: Intelligent assistance embedded throughout workflows
4. **Cloud Native**: Built for multi-cloud, scalable, resilient operations
5. **Open Integration**: Standards-based APIs and extensible architecture
6. **Governance Enabled**: Compliance and audit capabilities from day one
7. **Performance Obsessed**: Sub-second response times for critical operations

---

# 3. System Architecture

## 3.1 Architectural Overview

Qala employs a fully microservices-based, event-driven architecture with the following key characteristics:

### Architecture Principles
- **Microservices**: Independently deployable, scalable services
- **Event-Driven**: Asynchronous communication via Kafka
- **API-First**: RESTful and gRPC interfaces for all services
- **Database-Per-Service**: Isolated data stores for each microservice
- **Containerized**: Docker containers orchestrated by Kubernetes
- **Multi-Cloud**: Platform-agnostic deployment capabilities

## 3.2 High-Level Architecture Diagram

```
                         ┌─────────────────────────────┐
                         │      API Gateway /          │
                         │  Unified Access Portal      │
                         └───────────┬─────────────────┘
                                     │ REST / gRPC / WebSocket
      ┌──────────────────────────────┼──────────────────────────────┐
      │                              │                              │
┌─────▼──────┐              ┌────────▼────────┐           ┌────────▼────────┐
│   User     │              │      SDE        │           │   Workspace/    │
│ Identity   │              │  Management     │           │      CMS        │
│  Service   │              │    Service      │           │    Service      │
└─────┬──────┘              └────────┬────────┘           └────────┬────────┘
      │                              │                              │
      └──────────────────────────────┼──────────────────────────────┘
                                     │
                         ┌───────────▼────────────┐
                         │   Kafka Event Bus      │
                         │  (Event Streaming)     │
                         └───────────┬────────────┘
                                     │
      ┌──────────────────────────────┼──────────────────────────────┐
      │                              │                              │
┌─────▼──────┐              ┌────────▼────────┐           ┌────────▼────────┐
│ Workflow/  │              │   Artifact/     │           │     Data        │
│   CI/CD    │              │    Package      │           │   Platform      │
│  Service   │              │    Service      │           │    Service      │
└─────┬──────┘              └────────┬────────┘           └────────┬────────┘
      │                              │                              │
      └──────────────────────────────┼──────────────────────────────┘
                                     │
      ┌──────────────────────────────┼──────────────────────────────┐
      │                              │                              │
┌─────▼──────┐              ┌────────▼────────┐           ┌────────▼────────┐
│ AI Agents  │              │  Security/SEM   │           │ Notifications   │
│  Service   │              │    Service      │           │    Service      │
└────────────┘              └─────────────────┘           └─────────────────┘
```

## 3.3 Core Service Catalog

### Service Layer 1: Gateway & Identity
1. **API Gateway**: Request routing, authentication, rate limiting
2. **User Identity Service**: User/role management, RBAC, audit logging

### Service Layer 2: Development Environment
3. **SDE Management Service**: Personal/remote SDE lifecycle, templates, snapshots
4. **Workspace/CMS Service**: Personal/shared workspaces, content versioning
5. **IDE Integration Service**: VSCode, PyCharm, Eclipse, custom editor support

### Service Layer 3: Build & Release
6. **Workflow/CI-CD Service**: Pipeline orchestration, hermetic builds
7. **Artifact/Package Service**: Binary storage, dependency management
8. **Release Management Service**: Version control, deployment orchestration

### Service Layer 4: Intelligence & Security
9. **AI Agents Service**: Predictive recommendations, optimization
10. **Security/SEM Service**: Threat detection, secrets management, quarantine
11. **Data Platform Service**: Pipelines, warehouse, analytics, MDM

### Service Layer 5: Collaboration & Administration
12. **Notifications Service**: Multi-channel alerts (portal, email, chat)
13. **Platform Admin Service**: Configuration, policies, monitoring
14. **Collaboration Service**: Chat integration, team coordination

## 3.4 Technology Stack

### Programming Languages
- **Primary**: Zig (microservices core)
- **Scripting**: Python (AI/ML, data processing)
- **Frontend**: TypeScript/React

### Databases
- **Relational**: PostgreSQL (primary datastore)
- **Document**: MongoDB (unstructured data, logs)
- **Cache**: Redis (session management, caching)
- **Time-Series**: InfluxDB (metrics, telemetry)

### Messaging & Streaming
- **Event Bus**: Apache Kafka
- **Message Queue**: RabbitMQ (task queues)

### Container & Orchestration
- **Containerization**: Docker
- **Orchestration**: Kubernetes
- **Service Mesh**: Istio (optional)

### Storage
- **Object Storage**: S3-compatible (artifacts, backups)
- **Block Storage**: Persistent volumes (databases)

### Monitoring & Observability
- **Metrics**: Prometheus
- **Visualization**: Grafana
- **Logging**: ELK Stack (Elasticsearch, Logstash, Kibana)
- **Tracing**: Jaeger

---

# 4. Core Platform Modules

## 4.1 User Identity & Access Management

### Purpose
Centralized authentication, authorization, and user lifecycle management.

### Key Features
- Multi-factor authentication (MFA)
- Role-based access control (RBAC)
- SSO integration (OAuth2, SAML)
- User provisioning and de-provisioning
- Audit logging of all user actions

### Database Schema
```sql
CREATE TABLE users (
    id UUID PRIMARY KEY,
    name VARCHAR(255) NOT NULL,
    email VARCHAR(255) UNIQUE NOT NULL,
    created_at TIMESTAMP DEFAULT NOW(),
    updated_at TIMESTAMP DEFAULT NOW()
);

CREATE TABLE roles (
    id UUID PRIMARY KEY,
    name VARCHAR(100) UNIQUE NOT NULL,
    description TEXT
);

CREATE TABLE user_roles (
    user_id UUID REFERENCES users(id),
    role_id UUID REFERENCES roles(id),
    assigned_at TIMESTAMP DEFAULT NOW(),
    PRIMARY KEY (user_id, role_id)
);

CREATE TABLE audit_logs (
    id UUID PRIMARY KEY,
    user_id UUID REFERENCES users(id),
    action VARCHAR(100) NOT NULL,
    resource_type VARCHAR(100),
    resource_id VARCHAR(255),
    details JSONB,
    timestamp TIMESTAMP DEFAULT NOW()
);
```

### API Endpoints
```
POST   /api/v1/users              - Create user
GET    /api/v1/users              - List users
GET    /api/v1/users/{id}         - Get user details
PUT    /api/v1/users/{id}         - Update user
DELETE /api/v1/users/{id}         - Delete user
POST   /api/v1/auth/login         - Authenticate user
POST   /api/v1/auth/logout        - Logout user
GET    /api/v1/auth/verify        - Verify token
```

### Kafka Events
- `USER_CREATED`
- `USER_UPDATED`
- `USER_DELETED`
- `USER_LOGIN`
- `USER_LOGOUT`
- `ROLE_ASSIGNED`
- `ROLE_REVOKED`

### AI Hooks
- `ai_detect_role_conflicts()` - Identify permission conflicts
- `ai_recommend_roles()` - Suggest appropriate roles based on user activity

### SEM Hooks
- `sem_audit_user_action()` - Log security-relevant actions
- `sem_detect_anomalous_login()` - Identify suspicious login patterns

---

## 4.2 SDE Management Service

### Purpose
Manage the complete lifecycle of personal and remote Software Development Environments.

### Key Features
- Templated SDE provisioning
- Local and remote SDE support
- Snapshot and rollback capabilities
- Disk-persistent configurations
- Multi-cloud deployment
- IDE integration

### Database Schema
```sql
CREATE TABLE sdes (
    id UUID PRIMARY KEY,
    owner_id UUID REFERENCES users(id),
    template_id UUID,
    name VARCHAR(255) NOT NULL,
    type VARCHAR(50) NOT NULL, -- 'local', 'remote', 'cloud'
    status VARCHAR(50) NOT NULL, -- 'provisioning', 'active', 'suspended', 'terminated'
    snapshot_version INT DEFAULT 0,
    config JSONB,
    created_at TIMESTAMP DEFAULT NOW(),
    updated_at TIMESTAMP DEFAULT NOW()
);

CREATE TABLE sde_templates (
    id UUID PRIMARY KEY,
    name VARCHAR(255) NOT NULL,
    description TEXT,
    base_image VARCHAR(255),
    config JSONB,
    version VARCHAR(50),
    created_at TIMESTAMP DEFAULT NOW()
);

CREATE TABLE sde_snapshots (
    id UUID PRIMARY KEY,
    sde_id UUID REFERENCES sdes(id),
    version INT NOT NULL,
    snapshot_path VARCHAR(500),
    description TEXT,
    created_at TIMESTAMP DEFAULT NOW(),
    UNIQUE (sde_id, version)
);

CREATE TABLE sde_activity (
    id UUID PRIMARY KEY,
    sde_id UUID REFERENCES sdes(id),
    activity_type VARCHAR(100),
    details JSONB,
    timestamp TIMESTAMP DEFAULT NOW()
);
```

### API Endpoints
```
POST   /api/v1/sdes                    - Create SDE
GET    /api/v1/sdes                    - List SDEs
GET    /api/v1/sdes/{id}               - Get SDE details
PUT    /api/v1/sdes/{id}               - Update SDE
DELETE /api/v1/sdes/{id}               - Delete SDE
POST   /api/v1/sdes/{id}/snapshot      - Create snapshot
POST   /api/v1/sdes/{id}/rollback      - Rollback to snapshot
GET    /api/v1/sdes/{id}/snapshots     - List snapshots
POST   /api/v1/sdes/{id}/start         - Start SDE
POST   /api/v1/sdes/{id}/stop          - Stop SDE
GET    /api/v1/sde-templates           - List templates
POST   /api/v1/sde-templates           - Create template
```

### Kafka Events
- `SDE_CREATED`
- `SDE_PROVISIONED`
- `SDE_STARTED`
- `SDE_STOPPED`
- `SDE_SNAPSHOT_CREATED`
- `SDE_ROLLBACK_COMPLETED`
- `SDE_DELETED`

### AI Hooks
- `ai_optimize_sde_config()` - Recommend optimal SDE configuration
- `ai_predict_resource_usage()` - Forecast resource requirements
- `ai_suggest_template()` - Recommend appropriate template for project

### SEM Hooks
- `sem_validate_sde_config()` - Check for security misconfigurations
- `sem_quarantine_sde()` - Isolate compromised SDE
- `sem_scan_snapshot()` - Security scan of snapshot contents

---

## 4.3 Workspace & CMS Service

### Purpose
Manage personal and shared digital workspaces with content versioning and collaboration.

### Key Features
- Personal workspaces per developer
- Shared team workspaces
- File versioning and diff tracking
- Content search and indexing
- Access control per workspace
- Integration with SDE and CI/CD

### Database Schema
```sql
CREATE TABLE workspaces (
    id UUID PRIMARY KEY,
    owner_id UUID REFERENCES users(id),
    name VARCHAR(255) NOT NULL,
    type VARCHAR(50) NOT NULL, -- 'personal', 'shared'
    description TEXT,
    created_at TIMESTAMP DEFAULT NOW(),
    updated_at TIMESTAMP DEFAULT NOW()
);

CREATE TABLE workspace_members (
    workspace_id UUID REFERENCES workspaces(id),
    user_id UUID REFERENCES users(id),
    role VARCHAR(50) NOT NULL, -- 'owner', 'editor', 'viewer'
    added_at TIMESTAMP DEFAULT NOW(),
    PRIMARY KEY (workspace_id, user_id)
);

CREATE TABLE workspace_content (
    id UUID PRIMARY KEY,
    workspace_id UUID REFERENCES workspaces(id),
    parent_id UUID REFERENCES workspace_content(id),
    name VARCHAR(255) NOT NULL,
    type VARCHAR(50) NOT NULL, -- 'file', 'folder'
    content TEXT,
    version INT DEFAULT 1,
    created_by UUID REFERENCES users(id),
    created_at TIMESTAMP DEFAULT NOW(),
    updated_at TIMESTAMP DEFAULT NOW()
);

CREATE TABLE content_versions (
    id UUID PRIMARY KEY,
    content_id UUID REFERENCES workspace_content(id),
    version INT NOT NULL,
    content TEXT,
    changed_by UUID REFERENCES users(id),
    change_description TEXT,
    created_at TIMESTAMP DEFAULT NOW(),
    UNIQUE (content_id, version)
);
```

### API Endpoints
```
POST   /api/v1/workspaces                     - Create workspace
GET    /api/v1/workspaces                     - List workspaces
GET    /api/v1/workspaces/{id}                - Get workspace details
PUT    /api/v1/workspaces/{id}                - Update workspace
DELETE /api/v1/workspaces/{id}                - Delete workspace
POST   /api/v1/workspaces/{id}/members        - Add member
DELETE /api/v1/workspaces/{id}/members/{uid}  - Remove member
POST   /api/v1/workspaces/{id}/content        - Create content
GET    /api/v1/workspaces/{id}/content        - List content
GET    /api/v1/workspaces/{id}/content/{cid}  - Get content
PUT    /api/v1/workspaces/{id}/content/{cid}  - Update content
DELETE /api/v1/workspaces/{id}/content/{cid}  - Delete content
GET    /api/v1/content/{id}/versions          - List versions
GET    /api/v1/content/{id}/versions/{ver}    - Get specific version
```

### Kafka Events
- `WORKSPACE_CREATED`
- `WORKSPACE_UPDATED`
- `WORKSPACE_DELETED`
- `WORKSPACE_MEMBER_ADDED`
- `WORKSPACE_MEMBER_REMOVED`
- `CONTENT_CREATED`
- `CONTENT_UPDATED`
- `CONTENT_DELETED`

### AI Hooks
- `ai_suggest_folder_structure()` - Recommend optimal organization
- `ai_detect_duplicate_content()` - Identify redundant files
- `ai_recommend_collaboration()` - Suggest team members to add

---

## 4.4 Workflow & CI/CD Service

### Purpose
Orchestrate build, test, and deployment pipelines with hermetic environments.

### Key Features
- Hermetic build environments
- Multi-stage pipelines
- Automated testing integration
- Deployment orchestration
- Rollback capabilities
- Performance metrics collection

### Database Schema
```sql
CREATE TABLE pipelines (
    id UUID PRIMARY KEY,
    name VARCHAR(255) NOT NULL,
    sde_id UUID REFERENCES sdes(id),
    config JSONB NOT NULL,
    status VARCHAR(50), -- 'active', 'paused', 'archived'
    created_by UUID REFERENCES users(id),
    created_at TIMESTAMP DEFAULT NOW(),
    updated_at TIMESTAMP DEFAULT NOW()
);

CREATE TABLE pipeline_executions (
    id UUID PRIMARY KEY,
    pipeline_id UUID REFERENCES pipelines(id),
    trigger_type VARCHAR(50), -- 'manual', 'commit', 'schedule', 'webhook'
    triggered_by UUID REFERENCES users(id),
    status VARCHAR(50), -- 'pending', 'running', 'success', 'failed', 'cancelled'
    started_at TIMESTAMP,
    completed_at TIMESTAMP,
    duration_seconds INT,
    logs TEXT
);

CREATE TABLE pipeline_stages (
    id UUID PRIMARY KEY,
    execution_id UUID REFERENCES pipeline_executions(id),
    stage_name VARCHAR(255) NOT NULL,
    stage_order INT NOT NULL,
    status VARCHAR(50),
    started_at TIMESTAMP,
    completed_at TIMESTAMP,
    logs TEXT
);

CREATE TABLE build_artifacts (
    id UUID PRIMARY KEY,
    execution_id UUID REFERENCES pipeline_executions(id),
    artifact_name VARCHAR(255) NOT NULL,
    artifact_path VARCHAR(500),
    artifact_size BIGINT,
    checksum VARCHAR(128),
    created_at TIMESTAMP DEFAULT NOW()
);
```

### API Endpoints
```
POST   /api/v1/pipelines                  - Create pipeline
GET    /api/v1/pipelines                  - List pipelines
GET    /api/v1/pipelines/{id}             - Get pipeline details
PUT    /api/v1/pipelines/{id}             - Update pipeline
DELETE /api/v1/pipelines/{id}             - Delete pipeline
POST   /api/v1/pipelines/{id}/run         - Trigger pipeline execution
GET    /api/v1/pipelines/{id}/executions  - List executions
GET    /api/v1/executions/{id}            - Get execution details
POST   /api/v1/executions/{id}/cancel     - Cancel execution
GET    /api/v1/executions/{id}/logs       - Get execution logs
GET    /api/v1/executions/{id}/artifacts  - List artifacts
```

### Kafka Events
- `PIPELINE_CREATED`
- `PIPELINE_UPDATED`
- `PIPELINE_TRIGGERED`
- `BUILD_STARTED`
- `BUILD_COMPLETED`
- `BUILD_FAILED`
- `TEST_STARTED`
- `TEST_COMPLETED`
- `DEPLOYMENT_STARTED`
- `DEPLOYMENT_COMPLETED`

### AI Hooks
- `ai_predict_build_time()` - Estimate pipeline duration
- `ai_detect_bottleneck()` - Identify performance issues
- `ai_optimize_pipeline()` - Suggest pipeline improvements
- `ai_predict_failure()` - Forecast potential build failures

---

## 4.5 Artifact & Package Management Service

### Purpose
Store, version, and manage build artifacts, binaries, and software packages.

### Key Features
- Binary artifact storage
- Version management
- Dependency tracking
- Third-party integration (Artifactory, Nexus)
- Checksum verification
- Artifact promotion workflows

### Database Schema
```sql
CREATE TABLE artifacts (
    id UUID PRIMARY KEY,
    name VARCHAR(255) NOT NULL,
    version VARCHAR(100) NOT NULL,
    type VARCHAR(50), -- 'binary', 'library', 'container', 'package'
    storage_path VARCHAR(500) NOT NULL,
    size_bytes BIGINT,
    checksum VARCHAR(128),
    metadata JSONB,
    created_by UUID REFERENCES users(id),
    created_at TIMESTAMP DEFAULT NOW(),
    UNIQUE (name, version)
);

CREATE TABLE artifact_dependencies (
    artifact_id UUID REFERENCES artifacts(id),
    depends_on_id UUID REFERENCES artifacts(id),
    dependency_type VARCHAR(50), -- 'build', 'runtime'
    version_constraint VARCHAR(100),
    PRIMARY KEY (artifact_id, depends_on_id)
);

CREATE TABLE artifact_downloads (
    id UUID PRIMARY KEY,
    artifact_id UUID REFERENCES artifacts(id),
    downloaded_by UUID REFERENCES users(id),
    download_timestamp TIMESTAMP DEFAULT NOW()
);
```

### API Endpoints
```
POST   /api/v1/artifacts              - Upload artifact
GET    /api/v1/artifacts              - List artifacts
GET    /api/v1/artifacts/{id}         - Get artifact metadata
GET    /api/v1/artifacts/{id}/download - Download artifact
DELETE /api/v1/artifacts/{id}         - Delete artifact
GET    /api/v1/artifacts/{id}/dependencies - Get dependencies
POST   /api/v1/artifacts/{id}/dependencies - Add dependency
```

### Kafka Events
- `ARTIFACT_UPLOADED`
- `ARTIFACT_DOWNLOADED`
- `ARTIFACT_DELETED`
- `ARTIFACT_PROMOTED`

### AI Hooks
- `ai_detect_dependency_conflicts()` - Identify version conflicts
- `ai_suggest_version_upgrade()` - Recommend updates
- `ai_predict_artifact_usage()` - Forecast storage needs

---

## 4.6 Data Platform Service

### Purpose
Centralized data management with pipelines, warehouse, analytics, and master data.

### Key Features
- ETL/ELT pipeline orchestration
- Data warehouse and lake storage
- Master data management (MDM)
- Real-time analytics
- Data quality monitoring
- Cross-project lineage tracking

### Database Schema
```sql
CREATE TABLE data_pipelines (
    id UUID PRIMARY KEY,
    name VARCHAR(255) NOT NULL,
    description TEXT,
    schedule VARCHAR(100), -- cron expression
    config JSONB,
    status VARCHAR(50),
    created_at TIMESTAMP DEFAULT NOW(),
    updated_at TIMESTAMP DEFAULT NOW()
);

CREATE TABLE pipeline_runs (
    id UUID PRIMARY KEY,
    pipeline_id UUID REFERENCES data_pipelines(id),
    status VARCHAR(50), -- 'running', 'success', 'failed'
    started_at TIMESTAMP,
    completed_at TIMESTAMP,
    records_processed BIGINT,
    errors_count INT,
    logs TEXT
);

CREATE TABLE metrics_store (
    id UUID PRIMARY KEY,
    metric_name VARCHAR(255) NOT NULL,
    metric_value NUMERIC,
    dimensions JSONB,
    timestamp TIMESTAMP NOT NULL,
    source VARCHAR(100)
);

CREATE INDEX idx_metrics_name_time ON metrics_store(metric_name, timestamp DESC);

CREATE TABLE master_data (
    id UUID PRIMARY KEY,
    entity_type VARCHAR(100) NOT NULL,
    entity_id VARCHAR(255) NOT NULL,
    data JSONB NOT NULL,
    version INT DEFAULT 1,
    created_at TIMESTAMP DEFAULT NOW(),
    updated_at TIMESTAMP DEFAULT NOW(),
    UNIQUE (entity_type, entity_id)
);
```

### API Endpoints
```
POST   /api/v1/data/pipelines           - Create pipeline
GET    /api/v1/data/pipelines           - List pipelines
GET    /api/v1/data/pipelines/{id}      - Get pipeline details
POST   /api/v1/data/pipelines/{id}/run  - Trigger pipeline run
GET    /api/v1/data/pipelines/{id}/runs - List runs
GET    /api/v1/data/metrics             - Query metrics
POST   /api/v1/data/metrics             - Store metrics
GET    /api/v1/data/master/{type}/{id}  - Get master data
PUT    /api/v1/data/master/{type}/{id}  - Update master data
```

### Kafka Events
- `PIPELINE_STARTED`
- `PIPELINE_COMPLETED`
- `PIPELINE_FAILED`
- `DATA_QUALITY_ALERT`
- `MASTER_DATA_UPDATED`

### AI Hooks
- `ai_detect_data_anomaly()` - Identify unusual patterns
- `ai_predict_pipeline_duration()` - Estimate run time
- `ai_optimize_query()` - Improve query performance
- `ai_recommend_partitioning()` - Suggest data organization

---

## 4.7 AI Agents Service

### Purpose
Provide intelligent recommendations, predictions, and optimizations across all platform services.

### Key Features
- Predictive analytics
- Workflow optimization
- Resource forecasting
- Code quality analysis
- Performance recommendations
- Anomaly detection

### API Endpoints
```
POST   /api/v1/ai/recommend              - Get recommendations
POST   /api/v1/ai/predict                - Get predictions
POST   /api/v1/ai/analyze/sde            - Analyze SDE configuration
POST   /api/v1/ai/analyze/pipeline       - Analyze pipeline performance
POST   /api/v1/ai/analyze/code           - Analyze code quality
GET    /api/v1/ai/insights               - Get platform insights
```

### AI Models & Capabilities

#### 1. SDE Optimization Model
- **Input**: SDE configuration, usage patterns, resource metrics
- **Output**: Optimized configuration recommendations
- **Algorithms**: Regression analysis, clustering

#### 2. Pipeline Performance Model
- **Input**: Historical pipeline data, code changes, test results
- **Output**: Build time predictions, bottleneck identification
- **Algorithms**: Time series forecasting, anomaly detection

#### 3. Resource Prediction Model
- **Input**: Platform usage trends, scheduled activities
- **Output**: Resource requirement forecasts
- **Algorithms**: Prophet, ARIMA, neural networks

#### 4. Code Quality Model
- **Input**: Code repository, test coverage, complexity metrics
- **Output**: Quality scores, improvement suggestions
- **Algorithms**: Static analysis, pattern matching, ML classification

### Kafka Events
- `AI_RECOMMENDATION_GENERATED`
- `AI_PREDICTION_MADE`
- `AI_ANOMALY_DETECTED`

---

## 4.8 Security & SEM Service

### Purpose
Comprehensive security management with threat detection, secrets management, and compliance.

### Key Features
- Real-time threat detection
- Security event management (SEM)
- Secrets vault and rotation
- Cross-SDE threat containment
- Vulnerability scanning
- Compliance reporting

### Database Schema
```sql
CREATE TABLE security_events (
    id UUID PRIMARY KEY,
    event_type VARCHAR(100) NOT NULL,
    severity VARCHAR(20) NOT NULL, -- 'critical', 'high', 'medium', 'low'
    source_service VARCHAR(100),
    source_id VARCHAR(255),
    details JSONB,
    detected_at TIMESTAMP DEFAULT NOW(),
    resolved_at TIMESTAMP,
    status VARCHAR(50) -- 'open', 'investigating', 'resolved', 'false_positive'
);

CREATE TABLE threats (
    id UUID PRIMARY KEY,
    threat_type VARCHAR(100) NOT NULL,
    sde_id UUID REFERENCES sdes(id),
    severity VARCHAR(20),
    description TEXT,
    mitigation_steps TEXT,
    detected_at TIMESTAMP DEFAULT NOW(),
    mitigated_at TIMESTAMP
);

CREATE TABLE secrets (
    id UUID PRIMARY KEY,
    key_name VARCHAR(255) NOT NULL UNIQUE,
    encrypted_value TEXT NOT NULL,
    rotation_policy VARCHAR(50),
    last_rotated TIMESTAMP,
    created_by UUID REFERENCES users(id),
    created_at TIMESTAMP DEFAULT NOW(),
    expires_at TIMESTAMP
);

CREATE TABLE compliance_reports (
    id UUID PRIMARY KEY,
    report_type VARCHAR(100) NOT NULL,
    compliance_framework VARCHAR(100), -- 'GDPR', 'SOC2', 'ISO27001'
    status VARCHAR(50),
    findings JSONB,
    generated_at TIMESTAMP DEFAULT NOW()
);
```

### API Endpoints
```
GET    /api/v1/security/events          - List security events
GET    /api/v1/security/events/{id}     - Get event details
PUT    /api/v1/security/events/{id}     - Update event status
GET    /api/v1/security/threats         - List active threats
POST   /api/v1/security/scan/{sde_id}   - Scan SDE for threats
POST   /api/v1/security/quarantine      - Quarantine resource
POST   /api/v1/security/secrets         - Create secret
GET    /api/v1/security/secrets/{key}   - Get secret (authorized)
PUT    /api/v1/security/secrets/{key}   - Rotate secret
DELETE /api/v1/security/secrets/{key}   - Delete secret
GET    /api/v1/security/compliance      - Get compliance status
POST   /api/v1/security/compliance/scan - Run compliance scan
```

### Kafka Events
- `SECURITY_EVENT_DETECTED`
- `THREAT_IDENTIFIED`
- `THREAT_MITIGATED`
- `SECRET_CREATED`
- `SECRET_ROTATED`
- `COMPLIANCE_VIOLATION`
- `SDE_QUARANTINED`

### Security Workflows

#### Threat Detection Flow
```
1. Monitor → 2. Detect Anomaly → 3. Analyze Threat → 4. Generate Alert
   ↓                                                          ↓
5. Auto-Containment (if critical) ← 6. Investigation ← 7. Notification
```

#### Secret Rotation Flow
```
1. Policy Check → 2. Generate New Secret → 3. Update Systems
                                               ↓
4. Verify Access → 5. Revoke Old Secret → 6. Audit Log
```

### AI Hooks
- `ai_predict_threat()` - Predictive threat analytics
- `ai_detect_anomaly()` - Behavioral anomaly detection
- `ai_recommend_mitigation()` - Suggest security measures

---

## 4.9 Notifications Service
### Purpose
Multi-channel notification delivery with intelligent routing and prioritization.

### Key Features
- Multi-channel support (portal, email, Slack, Teams, SMS)
- Priority-based routing
- Notification templates
- User preferences management
- Delivery tracking and analytics

### Database Schema
```sql
CREATE TABLE notification_channels (
    id UUID PRIMARY KEY,
    user_id UUID REFERENCES users(id),
    channel_type VARCHAR(50) NOT NULL, -- 'email', 'slack', 'teams', 'sms', 'portal'
    channel_config JSONB,
    enabled BOOLEAN DEFAULT TRUE,
    created_at TIMESTAMP DEFAULT NOW()
);

CREATE TABLE notifications (
    id UUID PRIMARY KEY,
    user_id UUID REFERENCES users(id),
    title VARCHAR(255) NOT NULL,
    message TEXT NOT NULL,
    priority VARCHAR(20), -- 'critical', 'high', 'normal', 'low'
    category VARCHAR(100),
    source_service VARCHAR(100),
    source_id VARCHAR(255),
    created_at TIMESTAMP DEFAULT NOW(),
    read_at TIMESTAMP
);

CREATE TABLE notification_deliveries (
    id UUID PRIMARY KEY,
    notification_id UUID REFERENCES notifications(id),
    channel_type VARCHAR(50),
    status VARCHAR(50), -- 'pending', 'sent', 'failed'
    sent_at TIMESTAMP,
    error_message TEXT
);
```

### API Endpoints
```
POST   /api/v1/notifications            - Create notification
GET    /api/v1/notifications            - List notifications (for user)
GET    /api/v1/notifications/{id}       - Get notification details
PUT    /api/v1/notifications/{id}/read  - Mark as read
POST   /api/v1/notify                   - Send notification (system)
GET    /api/v1/notification-channels    - List user channels
POST   /api/v1/notification-channels    - Add channel
PUT    /api/v1/notification-channels/{id} - Update channel
DELETE /api/v1/notification-channels/{id} - Remove channel
```

### Kafka Events
- `NOTIFICATION_CREATED`
- `NOTIFICATION_SENT`
- `NOTIFICATION_FAILED`
- `NOTIFICATION_READ`

### AI Hooks
- `ai_prioritize_notification()` - Intelligent priority assignment
- `ai_choose_channel()` - Optimal channel selection
- `ai_aggregate_notifications()` - Combine related notifications

---

# 5. Technical Specifications

## 5.1 Performance Requirements

### Response Time Targets
- **API Gateway**: < 50ms (95th percentile)
- **Database Queries**: < 100ms (simple), < 500ms (complex)
- **SDE Provisioning**: < 2 hours (initial), < 15 minutes (from template)
- **Pipeline Execution**: Variable (workload-dependent)
- **Notification Delivery**: < 5 seconds (critical), < 30 seconds (normal)

### Throughput Requirements
- **API Requests**: 10,000 requests/second (sustained)
- **Kafka Messages**: 100,000 messages/second
- **Concurrent SDEs**: 10,000+ active environments
- **Concurrent Users**: 50,000+ simultaneous users

### Scalability Targets
- **Horizontal Scaling**: All services must support horizontal scaling
- **Auto-Scaling**: Dynamic scaling based on load (CPU, memory, queue depth)
- **Multi-Region**: Support for deployment across multiple regions
- **Data Replication**: Cross-region replication with < 1 second lag

## 5.2 Reliability & Availability

### Availability Targets
- **Platform SLA**: 99.9% uptime (< 8.76 hours downtime/year)
- **Critical Services**: 99.95% uptime
- **Scheduled Maintenance**: < 4 hours/month
- **Zero-Downtime Deployments**: Required for all services

### Fault Tolerance
- **Service Redundancy**: Minimum 3 instances per critical service
- **Database Replication**: Multi-node clusters with automatic failover
- **Message Queue**: Persistent queues with replication
- **Circuit Breakers**: Automatic fallback for failing services

### Disaster Recovery
- **RPO (Recovery Point Objective)**: < 1 hour data loss
- **RTO (Recovery Time Objective)**: < 4 hours recovery time
- **Backup Frequency**: Continuous (incremental), daily (full)
- **Backup Retention**: 30 days online, 1 year archival

## 5.3 Security Requirements

### Authentication & Authorization
- **Authentication**: Multi-factor authentication (MFA) required for admins
- **Authorization**: Role-based access control (RBAC) for all resources
- **Session Management**: Token-based with expiration and refresh
- **API Security**: OAuth 2.0, JWT tokens, API key management

### Data Protection
- **Encryption at Rest**: AES-256 for all stored data
- **Encryption in Transit**: TLS 1.3 for all network communication
- **Key Management**: Hardware security module (HSM) or cloud KMS
- **Data Masking**: PII and sensitive data masked in logs and non-production

### Compliance
- **GDPR**: Data privacy, right to erasure, consent management
- **SOC 2**: Security, availability, processing integrity
- **ISO 27001**: Information security management
- **HIPAA**: Healthcare data protection (if applicable)

### Vulnerability Management
- **Scanning Frequency**: Daily automated scans
- **Patch Management**: Critical patches within 24 hours
- **Penetration Testing**: Quarterly external assessments
- **Security Audits**: Annual third-party audits

## 5.4 Observability Requirements

### Logging
- **Log Levels**: DEBUG, INFO, WARN, ERROR, FATAL
- **Structured Logging**: JSON format with correlation IDs
- **Log Retention**: 30 days hot, 1 year cold storage
- **Centralized Logging**: ELK stack or equivalent

### Metrics
- **Collection Frequency**: 10-second intervals
- **Metric Types**: Counters, gauges, histograms, summaries
- **Retention**: 24 hours (10s resolution), 30 days (1m resolution), 1 year (1h resolution)
- **Dashboards**: Real-time Grafana dashboards for all services

### Tracing
- **Distributed Tracing**: OpenTelemetry/Jaeger for request flows
- **Sampling Rate**: 100% for errors, 1% for successful requests (configurable)
- **Trace Retention**: 7 days

### Alerting
- **Alert Channels**: PagerDuty, Slack, email
- **Alert Severity**: Critical (immediate), Warning (15 min), Info (1 hour)
- **On-Call Rotation**: 24/7 support for critical alerts
- **Runbooks**: Automated remediation steps for common issues

---

# 6. Data Architecture

## 6.1 Data Flow Architecture

```
┌─────────────┐
│   Sources   │ (SDEs, Pipelines, Users, Events)
└──────┬──────┘
       │
       ▼
┌─────────────────────────────┐
│   Ingestion Layer           │
│  - Kafka Producers          │
│  - API Endpoints            │
│  - File Uploads             │
└──────────┬──────────────────┘
           │
           ▼
┌─────────────────────────────┐
│   Processing Layer          │
│  - Stream Processing        │
│  - Batch Processing         │
│  - Data Validation          │
└──────────┬──────────────────┘
           │
           ▼
┌─────────────────────────────┐
│   Storage Layer             │
│  - Operational DBs          │
│  - Data Warehouse           │
│  - Data Lake                │
│  - Object Storage           │
└──────────┬──────────────────┘
           │
           ▼
┌─────────────────────────────┐
│   Consumption Layer         │
│  - Analytics APIs           │
│  - Dashboards               │
│  - ML Models                │
│  - Reports                  │
└─────────────────────────────┘
```

## 6.2 Data Governance

### Data Classification
- **Public**: Marketing content, public documentation
- **Internal**: General business data, non-sensitive information
- **Confidential**: Source code, customer data, business secrets
- **Restricted**: PII, financial data, security credentials

### Data Quality Framework
- **Completeness**: Required fields populated
- **Accuracy**: Data matches source of truth
- **Consistency**: Same data across systems
- **Timeliness**: Data available when needed
- **Validity**: Data conforms to defined formats

### Master Data Management
- **Entities**: Users, Projects, SDEs, Artifacts, Organizations
- **Golden Records**: Single source of truth per entity
- **Data Stewardship**: Defined ownership and accountability
- **Data Lineage**: Track data from source to consumption

## 6.3 Data Retention Policy

| Data Type | Hot Storage | Warm Storage | Cold Storage | Deletion |
|-----------|-------------|--------------|--------------|----------|
| Transaction Logs | 7 days | 30 days | 1 year | After 1 year |
| Metrics | 24 hours | 30 days | 1 year | After 1 year |
| Audit Logs | 30 days | 90 days | 7 years | After 7 years |
| Build Artifacts | 90 days | 1 year | 3 years | After 3 years |
| User Data | Active | N/A | N/A | On account deletion + 30 days |
| SDE Snapshots | 30 days | 90 days | 1 year | After 1 year or on request |

---

# 7. Security & Privacy

## 7.1 Security Architecture

### Defense in Depth Layers

```
┌─────────────────────────────────────────────────────┐
│ Layer 7: Physical Security                          │
│  - Data center access controls                      │
│  - Environmental monitoring                         │
└─────────────────────────────────────────────────────┘
┌─────────────────────────────────────────────────────┐
│ Layer 6: Perimeter Security                         │
│  - DDoS protection, WAF, Rate limiting              │
└─────────────────────────────────────────────────────┘
┌─────────────────────────────────────────────────────┐
│ Layer 5: Network Security                           │
│  - VPC isolation, Security groups, NACLs            │
└─────────────────────────────────────────────────────┘
┌─────────────────────────────────────────────────────┐
│ Layer 4: Host Security                              │
│  - OS hardening, Patch management, EDR              │
└─────────────────────────────────────────────────────┘
┌─────────────────────────────────────────────────────┐
│ Layer 3: Application Security                       │
│  - Input validation, OWASP Top 10 mitigation        │
└─────────────────────────────────────────────────────┘
┌─────────────────────────────────────────────────────┐
│ Layer 2: Data Security                              │
│  - Encryption, Tokenization, Access control         │
└─────────────────────────────────────────────────────┘
┌─────────────────────────────────────────────────────┐
│ Layer 1: Identity & Access                          │
│  - MFA, RBAC, IAM, Privileged access management     │
└─────────────────────────────────────────────────────┘
```

## 7.2 Threat Model

### Identified Threats

#### 1. External Threats
- **DDoS Attacks**: Overwhelming platform with traffic
- **SQL Injection**: Database manipulation via input
- **Cross-Site Scripting (XSS)**: Client-side code injection
- **API Abuse**: Unauthorized or excessive API usage
- **Credential Stuffing**: Automated login attempts with stolen credentials

#### 2. Internal Threats
- **Privilege Escalation**: Unauthorized access to higher privileges
- **Data Exfiltration**: Unauthorized data downloads
- **Insider Threats**: Malicious or negligent employees
- **Misconfiguration**: Security gaps due to errors

#### 3. Supply Chain Threats
- **Dependency Vulnerabilities**: Compromised third-party libraries
- **Container Vulnerabilities**: Malicious or vulnerable base images
- **Integration Risks**: Compromised external services

### Mitigation Strategies

| Threat | Mitigation |
|--------|------------|
| DDoS | CloudFlare/AWS Shield, Rate limiting, Auto-scaling |
| SQL Injection | Parameterized queries, ORM usage, Input validation |
| XSS | Output encoding, CSP headers, Input sanitization |
| API Abuse | Rate limiting, API keys, OAuth tokens with expiration |
| Credential Stuffing | MFA, Account lockout, CAPTCHA, Password policies |
| Privilege Escalation | Least privilege, Regular access reviews, Audit logging |
| Data Exfiltration | DLP tools, Network monitoring, Access controls |
| Dependency Vulnerabilities | SCA scanning, Dependency pinning, Regular updates |

## 7.3 Privacy Framework

### Privacy by Design Principles
1. **Proactive not Reactive**: Prevent privacy issues before they occur
2. **Privacy as Default**: Strongest privacy settings by default
3. **Privacy Embedded**: Built into design, not added later
4. **Full Functionality**: Positive-sum, not zero-sum approach
5. **End-to-End Security**: Lifecycle protection
6. **Visibility and Transparency**: Open and honest practices
7. **User-Centric**: Respect for user privacy

### Personal Data Handling

#### Data Minimization
- Collect only necessary data
- Anonymize where possible
- Pseudonymize identifiable data
- Regular data purges

#### User Rights (GDPR Compliance)
- **Right to Access**: Export personal data
- **Right to Rectification**: Correct inaccurate data
- **Right to Erasure**: Delete account and data
- **Right to Portability**: Download data in portable format
- **Right to Object**: Opt-out of processing
- **Right to Restrict**: Limit processing activities

#### Consent Management
- Explicit consent for data collection
- Granular consent options
- Easy consent withdrawal
- Consent audit trail

---

# 8. AI & Analytics Framework

## 8.1 AI/ML Architecture

```
┌─────────────────────────────────────────────────────┐
│               Feature Engineering                    │
│  - Data extraction from services                     │
│  - Feature transformation and normalization          │
│  - Feature store for reusability                     │
└─────────────────┬───────────────────────────────────┘
                  │
                  ▼
┌─────────────────────────────────────────────────────┐
│               Model Training                         │
│  - Experiment tracking (MLflow)                      │
│  - Hyperparameter tuning                             │
│  - Cross-validation and evaluation                   │
└─────────────────┬───────────────────────────────────┘
                  │
                  ▼
┌─────────────────────────────────────────────────────┐
│               Model Registry                         │
│  - Version control for models                        │
│  - Model metadata and lineage                        │
│  - A/B testing capabilities                          │
└─────────────────┬───────────────────────────────────┘
                  │
                  ▼
┌─────────────────────────────────────────────────────┐
│               Model Serving                          │
│  - Real-time inference API                           │
│  - Batch prediction jobs                             │
│  - Edge deployment (for SDEs)                        │
└─────────────────┬───────────────────────────────────┘
                  │
                  ▼
┌─────────────────────────────────────────────────────┐
│               Monitoring & Retraining                │
│  - Model performance tracking                        │
│  - Drift detection                                   │
│  - Automated retraining pipelines                    │
└─────────────────────────────────────────────────────┘
```

## 8.2 Analytics Capabilities

### Real-Time Analytics
- **Stream Processing**: Kafka Streams, Flink for real-time aggregations
- **Use Cases**: Live dashboards, instant alerts, fraud detection
- **Latency**: < 1 second from event to insight

### Batch Analytics
- **Processing**: Apache Spark for large-scale data processing
- **Use Cases**: Historical trend analysis, reporting, ML training
- **Schedule**: Daily, weekly, monthly jobs

### Interactive Analytics
- **Query Engine**: Presto or ClickHouse for ad-hoc queries
- **Use Cases**: Business intelligence, data exploration
- **Performance**: Sub-second query response for most queries

## 8.3 Key Metrics & KPIs

### Development Metrics
- **Developer Productivity**: Commits per day, PR merge time
- **Code Quality**: Test coverage, code complexity, bug density
- **SDE Utilization**: Active time, resource usage, snapshot frequency

### Operations Metrics
- **Build Performance**: Success rate, duration, queue time
- **Deployment Frequency**: Deployments per day/week
- **Mean Time to Recovery (MTTR)**: Incident resolution time
- **Change Failure Rate**: % of deployments causing issues

### Business Metrics
- **Platform Adoption**: Active users, workspace growth
- **Cost Efficiency**: Cost per developer, resource optimization
- **User Satisfaction**: NPS score, support ticket volume
- **Revenue**: MRR, ARR, customer lifetime value

---

# 9. Implementation Roadmap

## 9.1 Phase 1: Foundation (Months 1-3)

### Objectives
- Establish core infrastructure
- Deploy foundational services
- Validate architecture with pilot

### Deliverables
1. **Infrastructure Setup**
   - Kubernetes cluster deployment
   - PostgreSQL, MongoDB, Redis setup
   - Kafka cluster installation
   - Monitoring stack (Prometheus, Grafana, ELK)

2. **Core Services**
   - API Gateway
   - User Identity Service
   - Basic SDE Management (local only)
   - Notification Service (portal only)

3. **Developer Experience**
   - Developer onboarding documentation
   - CLI tools for SDE management
   - Basic web portal UI

### Success Criteria
- 10 developers using platform
- 50+ SDEs created
- API gateway handling 1,000+ requests/day
- < 30 minute SDE provisioning time

## 9.2 Phase 2: Expansion (Months 4-6)

### Objectives
- Add critical workflow capabilities
- Expand SDE management features
- Implement collaboration tools

### Deliverables
1. **Workflow & CI/CD**
   - Pipeline creation and execution
   - Hermetic build environments
   - Basic artifact management
   - Test integration

2. **Enhanced SDE Management**
   - SDE templates
   - Snapshot and rollback
   - Remote SDE support (Phase 1)
   - IDE integration (VSCode)

3. **Collaboration**
   - Workspace/CMS service
   - Shared workspaces
   - Basic version control

### Success Criteria
- 50 developers onboarded
- 100+ pipelines created
- 500+ successful builds
- 95%+ build success rate

## 9.3 Phase 3: Intelligence (Months 7-9)

### Objectives
- Deploy AI and analytics capabilities
- Enhance security posture
- Implement data platform

### Deliverables
1. **AI & Analytics**
   - AI Agents service deployment
   - SDE optimization recommendations
   - Pipeline performance predictions
   - Anomaly detection

2. **Security & SEM**
   - Security event management
   - Threat detection (basic)
   - Secrets vault
   - Compliance scanning

3. **Data Platform**
   - Data pipelines
   - Metrics warehouse
   - Basic analytics dashboards
   - Master data management

### Success Criteria
- AI recommendations adopted by 50%+ developers
- 90% threat detection accuracy
- < 5 minute security incident response
- Data warehouse processing 1M+ events/day

## 9.4 Phase 4: Scale & Polish (Months 10-12)

### Objectives
- Optimize for scale
- Multi-cloud deployment
- Enterprise-grade features

### Deliverables
1. **Scalability**
   - Auto-scaling policies
   - Multi-region deployment
   - Performance optimization
   - Load testing validation

2. **Advanced Features**
   - Advanced AI (Phase 2 & 3)
   - Multi-cloud SDE provisioning
   - Advanced IDE integrations
   - Enhanced collaboration tools

3. **Enterprise Readiness**
   - SOC 2 compliance
   - Advanced security features
   - SLA monitoring
   - Customer success tools

### Success Criteria
- 500+ active developers
- 10,000+ concurrent SDEs supported
- 99.9% platform uptime
- SOC 2 Type I certification

## 9.5 Multi-Year Vision (Years 2-3)

### Year 2 Focus
- Global expansion and localization
- Marketplace for templates and plugins
- Advanced analytics and business intelligence
- Industry-specific solutions

### Year 3 Focus
- AI-driven autonomous operations
- Predictive infrastructure management
- Industry leadership and ecosystem building
- IPO readiness

---

# 10. Deployment & Operations

## 10.1 Deployment Architecture

### Production Environment

```
┌─────────────────────────────────────────────────────┐
│                   Load Balancer                      │
│         (CloudFlare / AWS ALB / Azure FD)            │
└────────────────┬────────────────────────────────────┘
                 │
    ┌────────────┴────────────┐
    │                         │
┌───▼───────────┐    ┌────────▼──────────┐
│  Region US    │    │   Region EU       │
│               │    │                   │
│ ┌───────────┐ │    │ ┌───────────┐    │
│ │ K8s Cluster│ │    │ │ K8s Cluster│   │
│ │ - API GW  │ │    │ │ - API GW  │    │
│ │ - Services│ │    │ │ - Services│    │
│ └───────────┘ │    │ └───────────┘    │
│               │    │                   │
│ ┌───────────┐ │    │ ┌───────────┐    │
│ │ PostgreSQL│ │    │ │ PostgreSQL│    │
│ │ (Primary) │ │    │ │ (Replica) │    │
│ └───────────┘ │    │ └───────────┘    │
│               │    │                   │
│ ┌───────────┐ │    │ ┌───────────┐    │
│ │  Kafka    │ │    │ │  Kafka    │    │
│ │ (Primary) │ │    │ │ (Replica) │    │
│ └───────────┘ │    │ └───────────┘    │
└───────────────┘    └───────────────────┘
```

### Deployment Strategy

#### Blue-Green Deployment
1. Deploy new version to "green" environment
2. Run smoke tests and validation
3. Switch traffic to green
4. Monitor for issues
5. Keep blue as rollback option

#### Canary Deployment
1. Deploy to 1% of traffic
2. Monitor metrics for 30 minutes
3. Gradually increase to 10%, 25%, 50%, 100%
4. Rollback if error rate increases

#### Rolling Updates
1. Update pods one availability zone at a time
2. Wait for health checks before proceeding
3. Maintain minimum availability during rollout

## 10.2 Infrastructure as Code

### Terraform Modules
```
infrastructure/
├── modules/
│   ├── networking/
│   ├── kubernetes/
│   ├── databases/
│   ├── monitoring/
│   └── security/
├── environments/
│   ├── dev/
│   ├── staging/
│   └── production/
└── main.tf
```

### Key Resources
- **VPC**: Isolated network per environment
- **EKS/AKS/GKE**: Managed Kubernetes clusters
- **RDS/CloudSQL**: Managed database instances
- **MSK/EventHub**: Managed Kafka clusters
- **S3/Blob**: Object storage for artifacts
- **CloudWatch/Stackdriver**: Monitoring and alerting

## 10.3 Operational Procedures

### Standard Operating Procedures

#### 1. Service Deployment
```bash
# 1. Update version in deployment manifest
# 2. Apply Kubernetes manifest
kubectl apply -f k8s/deployments/user-service.yaml

# 3. Monitor rollout
kubectl rollout status deployment/user-service

# 4. Verify health
kubectl get pods -l app=user-service
```

#### 2. Database Migration
```bash
# 1. Backup database
pg_dump -h <host> -U <user> <db> > backup.sql

# 2. Test migration on staging
flyway migrate -url=jdbc:postgresql://staging/db

# 3. Apply to production during maintenance window
flyway migrate -url=jdbc:postgresql://prod/db

# 4. Verify migration
flyway info -url=jdbc:postgresql://prod/db
```

#### 3. Incident Response
```
1. Alert received → PagerDuty notification
2. On-call engineer acknowledges (< 5 min)
3. Assess severity and impact
4. Follow runbook for known issues
5. Escalate if needed
6. Mitigate issue
7. Post-mortem within 24 hours
```

### Runbooks

#### High CPU Usage
```
Symptoms: CPU utilization > 80% for 5+ minutes
Diagnosis:
  1. Check pod resource requests/limits
  2. Review recent deployments
  3. Analyze application logs for errors
  4. Check for traffic spikes
Remediation:
  1. Scale up replicas: kubectl scale deployment/<name> --replicas=<new count>
  2. If persistent, increase resource limits
  3. Investigate code-level issues
```

#### Database Connection Exhaustion
```
Symptoms: Connection pool errors in logs
Diagnosis:
  1. Check active connections: SELECT count(*) FROM pg_stat_activity;
  2. Identify long-running queries
  3. Check for connection leaks in application
Remediation:
  1. Kill idle connections
  2. Increase max_connections (temporary)
  3. Fix connection leaks in code
  4. Implement connection pooling (PgBouncer)
```

## 10.4 Disaster Recovery Plan

### Recovery Procedures

#### Database Failure
```
RTO: 1 hour
RPO: 15 minutes

1. Detect failure via health checks
2. Promote read replica to primary
3. Update DNS/service endpoints
4. Verify application connectivity
5. Restore from backup if replica unavailable
6. Post-recovery validation
```

#### Complete Region Failure
```
RTO: 4 hours
RPO: 1 hour

1. Activate DR region
2. Promote replicated databases
3. Update global load balancer
4. Verify services in DR region
5. Restore from backups if needed
6. Monitor for data consistency issues
```

### Backup Strategy

| Component | Frequency | Retention | Method |
|-----------|-----------|-----------|--------|
| Databases | Continuous + Daily full | 30 days | WAL archiving + pg_dump |
| Kafka Topics | Real-time replication | 7 days | MirrorMaker |
| Object Storage | Versioning enabled | 90 days | S3 versioning |
| Kubernetes State | Daily | 30 days | Velero |
| Configuration | On change | Forever (Git) | GitOps |

---

# Conclusion

The Book of Qala represents a comprehensive blueprint for a next-generation software factory platform. This document serves as the foundational design specification for implementation, encompassing:

- **Complete Architecture**: Microservices-based, event-driven, cloud-native design
- **Detailed Specifications**: API contracts, database schemas, event definitions
- **Security Framework**: Defense-in-depth security and privacy by design
- **AI Integration**: Intelligent recommendations and predictive analytics
- **Operational Excellence**: Comprehensive deployment and operations procedures
- **Strategic Roadmap**: Phased implementation plan with clear milestones

## Next Steps

1. **Stakeholder Review**: Present to executive team and key stakeholders
2. **Technical Validation**: Architecture review with senior engineers
3. **Resource Planning**: Allocate team members to Phase 1 deliverables
4. **Infrastructure Setup**: Begin provisioning cloud resources
5. **Sprint Planning**: Define detailed sprint plans for first quarter

## Document Evolution

This document is a living specification that will evolve as the platform matures. All changes must be:
- Reviewed by architecture team
- Approved by technical leadership  
- Version controlled in Git
- Communicated to all stakeholders

---

**Document Status**: ✅ Ready for Implementation

**Approval Required From**:
- [ ] Chief Technology Officer
- [ ] VP of Engineering
- [ ] Chief Information Security Officer
- [ ] VP of Product
- [ ] Chief Architect

**Version History**:
- v1.0.0 (January 2026) - Initial comprehensive specification

---

*"Qala: Unifying Development. Accelerating Innovation."*

# Qala Software Design Document
## Software Factory Operating System Platform

---

## Document Information
- **Document Type**: Software Design Document (SDD)
- **Version**: 1.0.0
- **Date**: January 12, 2026
- **Status**: Final - Ready for Implementation
- **Project**: Qala Software Factory Platform
- **Classification**: Internal Technical Reference

---

# Table of Contents

1. [Introduction](#1-introduction)
2. [System Overview](#2-system-overview)
3. [Architecture Design](#3-architecture-design)
4. [Component Design](#4-component-design)
5. [Data Design](#5-data-design)
6. [Interface Design](#6-interface-design)
7. [Security Design](#7-security-design)
8. [Deployment Design](#8-deployment-design)
9. [Quality Attributes](#9-quality-attributes)
10. [Design Decisions](#10-design-decisions)

---

# 1. Introduction

## 1.1 Purpose

This Software Design Document (SDD) describes the architecture and detailed design of the Qala Software Factory Operating System Platform. It serves as the primary technical reference for developers, architects, and technical stakeholders during implementation and maintenance.

## 1.2 Scope

Qala is a comprehensive, microservices-based platform that provides:
- Personal and remote Software Development Environments (SDEs)
- CI/CD pipeline orchestration with hermetic builds
- Workspace and content management
- AI-driven recommendations and analytics
- Security event management and threat containment
- Data platform with pipelines and warehousing
- Multi-channel notifications and collaboration

## 1.3 Intended Audience

- **Software Architects**: System design and technical decisions
- **Backend Engineers**: Microservice implementation
- **Frontend Engineers**: UI/UX implementation
- **DevOps Engineers**: Infrastructure and deployment
- **QA Engineers**: Testing strategy and automation
- **Security Engineers**: Security implementation and auditing
- **Product Managers**: Feature understanding and planning

## 1.4 Design Goals

1. **Scalability**: Support 10,000+ concurrent SDEs and 50,000+ users
2. **Reliability**: 99.9% uptime with automated failover
3. **Performance**: Sub-second API response times, < 2 hour SDE provisioning
4. **Security**: Defense-in-depth with zero-trust architecture
5. **Maintainability**: Modular design with clear service boundaries
6. **Extensibility**: Plugin architecture for custom integrations
7. **Observability**: Comprehensive logging, metrics, and tracing

## 1.5 Document Conventions

- **Diagrams**: ASCII art for text compatibility
- **Code Samples**: Zig, SQL, YAML as appropriate
- **Terminology**: Consistent with platform glossary
- **References**: [Section.Subsection] format

---

# 2. System Overview

## 2.1 System Context

```
                    ┌─────────────────────┐
                    │   External Users    │
                    │  (Developers, Admins)│
                    └──────────┬──────────┘
                               │
                               ▼
              ┌────────────────────────────────┐
              │         Qala Platform          │
              │  (Software Factory OS)         │
              │                                │
              │  ┌──────────────────────────┐ │
              │  │   Microservices Layer    │ │
              │  └──────────────────────────┘ │
              │  ┌──────────────────────────┐ │
              │  │     Data Layer           │ │
              │  └──────────────────────────┘ │
              │  ┌──────────────────────────┐ │
              │  │   Integration Layer      │ │
              │  └──────────────────────────┘ │
              └────────┬───────────────┬───────┘
                       │               │
         ┌─────────────┴──┐       ┌───┴─────────────┐
         │  External      │       │  External       │
         │  Services      │       │  Infrastructure │
         │  (GitHub, etc) │       │  (AWS, K8s)     │
         └────────────────┘       └─────────────────┘
```

## 2.2 Key Stakeholders

| Stakeholder | Interest | Concerns |
|-------------|----------|----------|
| Developers | Productive development environment | Performance, reliability, ease of use |
| DevOps | Operational excellence | Automation, observability, scalability |
| Security Team | Platform security | Compliance, threat detection, data protection |
| Product Team | Feature delivery | Time to market, user satisfaction |
| Executive Team | Business value | ROI, competitive advantage, risk management |

## 2.3 Design Constraints

### Technical Constraints
- Must support multi-cloud deployment (AWS, Azure, GCP)
- Must integrate with existing enterprise systems (LDAP, SSO)
- Must support air-gapped deployment for regulated industries
- Must handle legacy codebases and build systems

### Business Constraints
- 12-month timeline for v1.0 release
- Team size: 15-20 engineers
- Budget: Cloud infrastructure and tooling licenses
- Must achieve SOC 2 compliance by month 9

### Regulatory Constraints
- GDPR compliance for EU users
- SOC 2 Type II certification required
- HIPAA compliance for healthcare customers (optional)
- ISO 27001 alignment

---

# 3. Architecture Design

## 3.1 Architectural Style

Qala employs a **microservices architecture** with the following characteristics:

### Core Principles
1. **Service Independence**: Each service is independently deployable
2. **Database per Service**: No shared databases between services
3. **Event-Driven Communication**: Asynchronous via Kafka
4. **API Gateway Pattern**: Single entry point for clients
5. **Service Discovery**: Dynamic service registration and lookup
6. **Circuit Breaker Pattern**: Fault tolerance and resilience

### Architecture Patterns

```
┌─────────────────────────────────────────────────────┐
│              Architectural Patterns                  │
├─────────────────────────────────────────────────────┤
│                                                      │
│  ┌────────────┐  ┌────────────┐  ┌────────────┐   │
│  │  API       │  │ Service    │  │  Event     │   │
│  │  Gateway   │  │ Mesh       │  │  Sourcing  │   │
│  └────────────┘  └────────────┘  └────────────┘   │
│                                                      │
│  ┌────────────┐  ┌────────────┐  ┌────────────┐   │
│  │  CQRS      │  │ Saga       │  │  Circuit   │   │
│  │  Pattern   │  │ Pattern    │  │  Breaker   │   │
│  └────────────┘  └────────────┘  └────────────┘   │
│                                                      │
│  ┌────────────┐  ┌────────────┐  ┌────────────┐   │
│  │  Database  │  │ Strangler  │  │  BFF       │   │
│  │  per Service│  │ Fig        │  │  Pattern   │   │
│  └────────────┘  └────────────┘  └────────────┘   │
└─────────────────────────────────────────────────────┘
```

## 3.2 Logical Architecture

### Layer Architecture

```
┌───────────────────────────────────────────────────────────┐
│                    Presentation Layer                      │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐       │
│  │  Web Portal │  │  CLI Tools  │  │  IDE Plugins│       │
│  └─────────────┘  └─────────────┘  └─────────────┘       │
└────────────────────────┬──────────────────────────────────┘
                         │
┌────────────────────────▼──────────────────────────────────┐
│                    API Gateway Layer                       │
│  ┌──────────────────────────────────────────────────┐     │
│  │  Authentication │ Routing │ Rate Limiting │ Cache │    │
│  └──────────────────────────────────────────────────┘     │
└────────────────────────┬──────────────────────────────────┘
                         │
┌────────────────────────▼──────────────────────────────────┐
│                   Business Logic Layer                     │
│  ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────┐        │
│  │ User    │ │ SDE     │ │Workspace│ │Workflow │        │
│  │ Service │ │ Service │ │ Service │ │ Service │        │
│  └─────────┘ └─────────┘ └─────────┘ └─────────┘        │
│  ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────┐        │
│  │Artifact │ │  Data   │ │   AI    │ │Security │        │
│  │ Service │ │ Service │ │ Service │ │ Service │        │
│  └─────────┘ └─────────┘ └─────────┘ └─────────┘        │
└────────────────────────┬──────────────────────────────────┘
                         │
┌────────────────────────▼──────────────────────────────────┐
│                    Event/Message Layer                     │
│  ┌──────────────────────────────────────────────────┐     │
│  │              Apache Kafka Event Bus               │     │
│  └──────────────────────────────────────────────────┘     │
└────────────────────────┬──────────────────────────────────┘
                         │
┌────────────────────────▼──────────────────────────────────┐
│                      Data Layer                            │
│  ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐    │
│  │PostgreSQL│ │ MongoDB  │ │  Redis   │ │InfluxDB  │    │
│  └──────────┘ └──────────┘ └──────────┘ └──────────┘    │
└───────────────────────────────────────────────────────────┘
```

## 3.3 Physical Architecture

### Deployment View

```
┌─────────────────────────────────────────────────────────────┐
│                      CDN / Edge Layer                        │
│                    (CloudFlare / AWS)                        │
└────────────────────────┬────────────────────────────────────┘
                         │
┌────────────────────────▼────────────────────────────────────┐
│                   Load Balancer Layer                        │
│              (ALB / NLB / Azure Front Door)                  │
└────────────────────────┬────────────────────────────────────┘
                         │
         ┌───────────────┴───────────────┐
         │                               │
┌────────▼────────────┐      ┌───────────▼────────────┐
│   Region: US-East   │      │   Region: EU-West      │
│                     │      │                        │
│ ┌─────────────────┐ │      │ ┌─────────────────┐   │
│ │ Kubernetes      │ │      │ │ Kubernetes      │   │
│ │ Cluster (AZ1)   │ │      │ │ Cluster (AZ1)   │   │
│ └─────────────────┘ │      │ └─────────────────┘   │
│ ┌─────────────────┐ │      │ ┌─────────────────┐   │
│ │ Kubernetes      │ │      │ │ Kubernetes      │   │
│ │ Cluster (AZ2)   │ │      │ │ Cluster (AZ2)   │   │
│ └─────────────────┘ │      │ └─────────────────┘   │
│ ┌─────────────────┐ │      │ ┌─────────────────┐   │
│ │ Kubernetes      │ │      │ │ Kubernetes      │   │
│ │ Cluster (AZ3)   │ │      │ │ Cluster (AZ3)   │   │
│ └─────────────────┘ │      │ └─────────────────┘   │
│                     │      │                        │
│ ┌─────────────────┐ │      │ ┌─────────────────┐   │
│ │ RDS Primary     │ │      │ │ RDS Replica     │   │
│ └─────────────────┘ │      │ └─────────────────┘   │
│                     │      │                        │
│ ┌─────────────────┐ │      │ ┌─────────────────┐   │
│ │ Kafka Cluster   │ │      │ │ Kafka Mirror    │   │
│ └─────────────────┘ │      │ └─────────────────┘   │
└─────────────────────┘      └────────────────────────┘
```

## 3.4 Service Decomposition

### Microservices Catalog

| Service | Responsibility | Technology Stack | Data Store |
|---------|---------------|------------------|------------|
| API Gateway | Request routing, auth, rate limiting | Kong/Nginx | Redis (cache) |
| User Identity | User/role management, authentication | Zig + PostgreSQL | PostgreSQL |
| SDE Management | SDE lifecycle, templates, snapshots | Zig + PostgreSQL | PostgreSQL + S3 |
| Workspace/CMS | Digital workspaces, content versioning | Zig + PostgreSQL | PostgreSQL + S3 |
| Workflow/CI-CD | Pipeline orchestration, builds | Zig + PostgreSQL | PostgreSQL |
| Artifact Management | Binary storage, versioning | Zig + S3 | PostgreSQL + S3 |
| Data Platform | ETL pipelines, analytics, MDM | Python + Spark | PostgreSQL + S3 |
| AI Agents | Recommendations, predictions | Python + TensorFlow | MongoDB + Redis |
| Security/SEM | Threat detection, secrets vault | Zig + PostgreSQL | PostgreSQL |
| Notifications | Multi-channel alerts | Zig + PostgreSQL | PostgreSQL + Redis |
| Platform Admin | Configuration, monitoring | Zig + PostgreSQL | PostgreSQL |

### Service Communication Matrix

```
┌──────────┬─────┬─────┬────┬────┬────┬────┬────┬────┬────┐
│          │User │ SDE │ WS │WF  │Art │Data│ AI │Sec │Not │
├──────────┼─────┼─────┼────┼────┼────┼────┼────┼────┼────┤
│User      │  -  │ API │API │API │API │API │API │Evt │API │
│SDE       │ Evt │  -  │Evt │API │Evt │Evt │Evt │Evt │Evt │
│Workspace │ Evt │ API │ -  │API │Evt │Evt │Evt │Evt │Evt │
│Workflow  │ Evt │ API │API │ -  │API │Evt │Evt │Evt │Evt │
│Artifact  │ Evt │ Evt │Evt │Evt │ -  │Evt │Evt │Evt │Evt │
│Data      │ Evt │ Evt │Evt │Evt │Evt │ -  │API │Evt │Evt │
│AI        │ Evt │ API │API │API │API │API │ -  │API │API │
│Security  │ API │ API │API │API │API │API │Evt │ -  │API │
│Notify    │ API │ Evt │Evt │Evt │Evt │Evt │Evt │Evt │ -  │
└──────────┴─────┴─────┴────┴────┴────┴────┴────┴────┴────┘

Legend: API = Synchronous REST/gRPC, Evt = Async via Kafka
```

---

# 4. Component Design

## 4.1 User Identity Service

### Component Overview

The User Identity Service manages authentication, authorization, and user lifecycle operations.

### Component Diagram

```
┌─────────────────────────────────────────────────────┐
│          User Identity Service                       │
├─────────────────────────────────────────────────────┤
│                                                      │
│  ┌──────────────────────────────────────────────┐  │
│  │         API Controller Layer                 │  │
│  │  ┌──────┐ ┌──────┐ ┌──────┐ ┌──────┐       │  │
│  │  │Users │ │Roles │ │Auth  │ │Audit │       │  │
│  │  └──┬───┘ └──┬───┘ └──┬───┘ └──┬───┘       │  │
│  └─────┼────────┼────────┼────────┼────────────┘  │
│        │        │        │        │                │
│  ┌─────▼────────▼────────▼────────▼────────────┐  │
│  │         Business Logic Layer                │  │
│  │  ┌─────────────┐  ┌─────────────┐          │  │
│  │  │User Manager │  │Auth Manager │          │  │
│  │  └──────┬──────┘  └──────┬──────┘          │  │
│  │  ┌──────▼──────┐  ┌──────▼──────┐          │  │
│  │  │Role Manager │  │Audit Logger │          │  │
│  │  └─────────────┘  └─────────────┘          │  │
│  └─────────────────┬──────────────────────────┘  │
│                    │                              │
│  ┌─────────────────▼──────────────────────────┐  │
│  │         Data Access Layer                  │  │
│  │  ┌────────┐ ┌────────┐ ┌────────┐         │  │
│  │  │User DAO│ │Role DAO│ │Audit DAO│        │  │
│  │  └───┬────┘ └───┬────┘ └───┬────┘         │  │
│  └──────┼──────────┼──────────┼──────────────┘  │
│         │          │          │                  │
│  ┌──────▼──────────▼──────────▼──────────────┐  │
│  │         PostgreSQL Database              │  │
│  │   ┌───────┐ ┌───────┐ ┌───────────┐     │  │
│  │   │users  │ │roles  │ │audit_logs │     │  │
│  │   └───────┘ └───────┘ └───────────┘     │  │
│  └─────────────────────────────────────────┘  │
│                                                  │
│  ┌──────────────────────────────────────────┐  │
│  │         Event Publisher                   │  │
│  │         (Kafka Producer)                  │  │
│  └──────────────────────────────────────────┘  │
└─────────────────────────────────────────────────┘
```

### Class Design

```zig
// User Model
pub const User = struct {
    id: []const u8,
    name: []const u8,
    email: []const u8,
    password_hash: []const u8,
    created_at: i64,
    updated_at: i64,
    
    pub fn validate(self: *const User) !void {
        if (self.name.len == 0) return error.InvalidName;
        if (!isValidEmail(self.email)) return error.InvalidEmail;
    }
    
    pub fn hashPassword(password: []const u8) ![]const u8 {
        // bcrypt hashing implementation
    }
};

// User Repository Interface
pub const UserRepository = struct {
    pub fn create(user: *User) ![]const u8 {
        // Database insertion logic
    }
    
    pub fn findById(id: []const u8) !?User {
        // Database query logic
    }
    
    pub fn findByEmail(email: []const u8) !?User {
        // Database query logic
    }
    
    pub fn update(user: *User) !void {
        // Database update logic
    }
    
    pub fn delete(id: []const u8) !void {
        // Database deletion logic
    }
};

// User Service
pub const UserService = struct {
    repository: *UserRepository,
    event_publisher: *EventPublisher,
    
    pub fn createUser(self: *UserService, name: []const u8, email: []const u8, password: []const u8) ![]const u8 {
        var user = User{
            .id = generateUUID(),
            .name = name,
            .email = email,
            .password_hash = try User.hashPassword(password),
            .created_at = timestamp(),
            .updated_at = timestamp(),
        };
        
        try user.validate();
        const user_id = try self.repository.create(&user);
        
        // Publish event
        try self.event_publisher.publish("USER_CREATED", user);
        
        return user_id;
    }
    
    pub fn authenticate(self: *UserService, email: []const u8, password: []const u8) !AuthToken {
        const user = try self.repository.findByEmail(email) orelse return error.UserNotFound;
        
        if (!verifyPassword(password, user.password_hash)) {
            return error.InvalidCredentials;
        }
        
        return generateToken(user);
    }
};
```

### API Specification

```yaml
openapi: 3.0.0
info:
  title: User Identity Service API
  version: 1.0.0

paths:
  /api/v1/users:
    post:
      summary: Create a new user
      requestBody:
        required: true
        content:
          application/json:
            schema:
              type: object
              required: [name, email, password]
              properties:
                name:
                  type: string
                  minLength: 1
                  maxLength: 255
                email:
                  type: string
                  format: email
                password:
                  type: string
                  minLength: 8
      responses:
        '201':
          description: User created successfully
          content:
            application/json:
              schema:
                type: object
                properties:
                  id:
                    type: string
                    format: uuid
                  name:
                    type: string
                  email:
                    type: string
        '400':
          description: Invalid input
        '409':
          description: User already exists

    get:
      summary: List users
      parameters:
        - name: page
          in: query
          schema:
            type: integer
            default: 1
        - name: limit
          in: query
          schema:
            type: integer
            default: 20
      responses:
        '200':
          description: List of users
          content:
            application/json:
              schema:
                type: object
                properties:
                  users:
                    type: array
                    items:
                      $ref: '#/components/schemas/User'
                  total:
                    type: integer
                  page:
                    type: integer

  /api/v1/users/{id}:
    get:
      summary: Get user by ID
      parameters:
        - name: id
          in: path
          required: true
          schema:
            type: string
            format: uuid
      responses:
        '200':
          description: User details
          content:
            application/json:
              schema:
                $ref: '#/components/schemas/User'
        '404':
          description: User not found

  /api/v1/auth/login:
    post:
      summary: Authenticate user
      requestBody:
        required: true
        content:
          application/json:
            schema:
              type: object
              required: [email, password]
              properties:
                email:
                  type: string
                  format: email
                password:
                  type: string
      responses:
        '200':
          description: Authentication successful
          content:
            application/json:
              schema:
                type: object
                properties:
                  token:
                    type: string
                  expires_at:
                    type: string
                    format: date-time
        '401':
          description: Invalid credentials

components:
  schemas:
    User:
      type: object
      properties:
        id:
          type: string
          format: uuid
        name:
          type: string
        email:
          type: string
          format: email
        created_at:
          type: string
          format: date-time
        updated_at:
          type: string
          format: date-time
```

### State Diagram

```
User Lifecycle States:

     ┌──────────┐
     │ Created  │
     └────┬─────┘
          │ activate()
          ▼
     ┌──────────┐     suspend()      ┌───────────┐
     │  Active  │─────────────────────▶│ Suspended │
     └────┬─────┘                      └─────┬─────┘
          │                                  │
          │ deactivate()          reactivate()│
          │                                  │
          ▼                                  │
     ┌──────────┐◀─────────────────────────┘
     │ Inactive │
     └────┬─────┘
          │ delete()
          ▼
     ┌──────────┐
     │ Deleted  │
     └──────────┘
```

## 4.2 SDE Management Service

### Component Overview

Manages the complete lifecycle of Software Development Environments including provisioning, configuration, snapshots, and rollbacks.

### Component Architecture

```
┌──────────────────────────────────────────────────────────┐
│            SDE Management Service                         │
├──────────────────────────────────────────────────────────┤
│                                                           │
│  ┌────────────────────────────────────────────────────┐ │
│  │              API Layer                             │ │
│  │  ┌──────┐ ┌──────┐ ┌──────┐ ┌──────┐ ┌──────┐   │ │
│  │  │SDEs  │ │Templ.│ │Snap. │ │Start │ │Stop  │   │ │
│  │  └──┬───┘ └──┬───┘ └──┬───┘ └──┬───┘ └──┬───┘   │ │
│  └─────┼────────┼────────┼────────┼────────┼────────┘ │
│        │        │        │        │        │            │
│  ┌─────▼────────▼────────▼────────▼────────▼─────────┐ │
│  │           Core Business Logic                     │ │
│  │                                                    │ │
│  │  ┌─────────────────┐  ┌─────────────────┐       │ │
│  │  │ Provisioning    │  │ Template        │       │ │
│  │  │ Manager         │  │ Manager         │       │ │
│  │  └────────┬────────┘  └────────┬────────┘       │ │
│  │           │                    │                 │ │
│  │  ┌────────▼────────┐  ┌────────▼────────┐       │ │
│  │  │ Snapshot        │  │ Lifecycle       │       │ │
│  │  │ Manager         │  │ Manager         │       │ │
│  │  └────────┬────────┘  └────────┬────────┘       │ │
│  │           │                    │                 │ │
│  │  ┌────────▼────────┐  ┌────────▼────────┐       │ │
│  │  │ Configuration   │  │ Resource        │       │ │
│  │  │ Manager         │  │ Monitor         │       │ │
│  │  └─────────────────┘  └─────────────────┘       │ │
│  └───────────────────────┬──────────────────────────┘ │
│                          │                              │
│  ┌───────────────────────▼──────────────────────────┐  │
│  │           Infrastructure Layer                   │  │
│  │  ┌──────────┐  ┌──────────┐  ┌──────────┐      │  │
│  │  │Container │  │ VM       │  │ Cloud    │      │  │
│  │  │ Adapter  │  │ Adapter  │  │ Adapter  │      │  │
│  │  └──────────┘  └──────────┘  └──────────┘      │  │
│  └──────────────────────────────────────────────────┘  │
│                                                          │
│  ┌──────────────────────────────────────────────────┐  │
│  │           Data Access Layer                      │  │
│  │  ┌──────────┐  ┌──────────┐  ┌──────────┐      │  │
│  │  │SDE DAO   │  │Tmpl DAO  │  │Snap DAO  │      │  │
│  │  └────┬─────┘  └────┬─────┘  └────┬─────┘      │  │
│  └───────┼─────────────┼─────────────┼─────────────┘  │
│          │             │             │                 │
│  ┌───────▼─────────────▼─────────────▼─────────────┐  │
│  │         PostgreSQL + Object Storage             │  │
│  └─────────────────────────────────────────────────┘  │
└──────────────────────────────────────────────────────────┘
```

### Sequence Diagram: SDE Provisioning

```
Actor: Developer
Service: API Gateway
Service: SDE Management
Service: AI Agents
Service: Infrastructure
Database: PostgreSQL

Developer -> API Gateway: POST /api/v1/sdes {template_id, config}
API Gateway -> SDE Management: Forward request
SDE Management -> PostgreSQL: Check template exists
PostgreSQL --> SDE Management: Template details
SDE Management -> AI Agents: Request config optimization
AI Agents --> SDE Management: Optimized config
SDE Management -> PostgreSQL: Create SDE record (status: provisioning)
PostgreSQL --> SDE Management: SDE ID
SDE Management -> Infrastructure: Provision container/VM
Infrastructure --> SDE Management: Provisioning initiated
SDE Management --> API Gateway: 202 Accepted {sde