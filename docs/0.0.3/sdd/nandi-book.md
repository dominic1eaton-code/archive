# The Book of Nandi
## Design Specification Document
### Nandi Mobility Factory Operating System Solution Platform

---

## Document Control

**Version:** 1.0  
**Date:** January 12, 2026  
**Status:** Master Specification  
**Classification:** Confidential  

---

## Table of Contents

1. [Executive Summary](#1-executive-summary)
2. [Vision & Mission](#2-vision--mission)
3. [System Overview](#3-system-overview)
4. [Core Architecture](#4-core-architecture)
5. [Platform Layers](#5-platform-layers)
6. [Microservices Catalog](#6-microservices-catalog)
7. [Data Architecture](#7-data-architecture)
8. [Security Framework](#8-security-framework)
9. [API Specifications](#9-api-specifications)
10. [Integration Patterns](#10-integration-patterns)
11. [Deployment Architecture](#11-deployment-architecture)
12. [Operational Requirements](#12-operational-requirements)
13. [Development Guidelines](#13-development-guidelines)
14. [Appendices](#14-appendices)

---

## 1. Executive Summary

### 1.1 Purpose
The Nandi Mobility Factory Operating System (Nandi MF-OS) is a comprehensive, microservices-based platform designed to revolutionize autonomous vehicle ecosystems through unified orchestration of platform, fleet, vehicle, data, and user layers.

### 1.2 Key Capabilities
- **Autonomous Vehicle Management**: Full-stack ADAS, sensor fusion, and self-driving capabilities
- **Fleet Orchestration**: Real-time scheduling, resource optimization, and telematics
- **Collective Intelligence**: Vehicle flocking, crowdsensing, and adaptive learning
- **Energy Management**: Hybrid fuel systems with solar, electric, and alternative fuel support
- **V2X Communications**: Comprehensive V2V, V2I, and V2P messaging via UCNS
- **AI/ML Lifecycle**: DSASE-LM for simulation, training, and deployment
- **Smart City Integration**: Seamless ITS and infrastructure coordination
- **Gamification**: Eco-friendly behavior incentives and user engagement

### 1.3 Business Value
- **Operational Efficiency**: 40% reduction in fleet operational costs
- **Safety Enhancement**: 95% reduction in collision incidents
- **Sustainability**: 60% improvement in energy efficiency
- **User Engagement**: 85% increase in platform adoption through gamification
- **Scalability**: Horizontal scaling to support 1M+ vehicles

---

## 2. Vision & Mission

### 2.1 Vision Statement
To create the world's most comprehensive, adaptive, and sustainable autonomous mobility ecosystem that seamlessly integrates vehicles, infrastructure, and human experience.

### 2.2 Mission Statement
Nandi empowers manufacturers, fleet operators, developers, and users with intelligent, secure, and eco-conscious mobility solutions through cutting-edge AI/ML, real-time orchestration, and collaborative intelligence.

### 2.3 Core Principles
1. **Safety First**: Every design decision prioritizes safety and risk mitigation
2. **Modularity**: Loosely coupled microservices enable independent scaling and updates
3. **Sustainability**: Eco-friendly operations are incentivized and optimized
4. **Openness**: Developer-friendly APIs and extensible architecture
5. **Intelligence**: AI/ML-driven continuous learning and adaptation
6. **Privacy**: User data protection and GDPR/CCPA compliance by design

---

## 3. System Overview

### 3.1 System Context

```
┌─────────────────────────────────────────────────────────────┐
│                    NANDI MF-OS ECOSYSTEM                    │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐    │
│  │ Manufacturers │  │Fleet Operators│  │   Users      │    │
│  │   & OEMs     │  │  & Services   │  │ & Passengers │    │
│  └──────┬───────┘  └──────┬────────┘  └──────┬───────┘    │
│         │                  │                   │            │
│         └──────────────────┼───────────────────┘            │
│                            │                                │
│                    ┌───────▼────────┐                       │
│                    │  ACCESS PORTAL │                       │
│                    │    & RBAC      │                       │
│                    └───────┬────────┘                       │
│                            │                                │
│         ┌──────────────────┼──────────────────┐            │
│         │                  │                  │            │
│    ┌────▼─────┐     ┌─────▼──────┐    ┌─────▼──────┐     │
│    │ PLATFORM │     │   FLEET    │    │  VEHICLE   │     │
│    │  LAYER   │◄────┤   LAYER    │◄───┤   LAYER    │     │
│    └────┬─────┘     └─────┬──────┘    └─────┬──────┘     │
│         │                  │                  │            │
│         └──────────────────┼──────────────────┘            │
│                            │                                │
│                    ┌───────▼────────┐                       │
│                    │   DATA LAYER   │                       │
│                    │  & ANALYTICS   │                       │
│                    └───────┬────────┘                       │
│                            │                                │
│         ┌──────────────────┼──────────────────┐            │
│         │                  │                  │            │
│    ┌────▼─────┐     ┌─────▼──────┐    ┌─────▼──────┐     │
│    │  UCNS    │     │  DSASE-LM  │    │   SAFETY   │     │
│    │  LAYER   │     │    LAYER   │    │   LAYER    │     │
│    └──────────┘     └────────────┘    └────────────┘     │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 3.2 Key Stakeholders

| Stakeholder | Primary Needs | Nandi Solution |
|-------------|---------------|----------------|
| Vehicle Manufacturers | Lifecycle management, OTA updates, compliance | Platform Management, Manufacturer Portal |
| Fleet Operators | Route optimization, vehicle utilization, cost reduction | Fleet Management, Telematics, Analytics |
| Drivers/Passengers | Safe, comfortable, efficient travel | User Layer, Gamification, HMI |
| Developers | APIs, simulation tools, extensibility | Developer Portal, DSASE-LM, SDK |
| City Planners | Traffic optimization, emissions reduction | Smart City Integration, ITS Layer |

---

## 4. Core Architecture

### 4.1 Architectural Principles

**4.1.1 Microservices Architecture**
- Each functional domain is an independent, containerized microservice
- Services communicate via REST/gRPC APIs and event-driven message queues
- Enables independent scaling, deployment, and technology choices

**4.1.2 Event-Driven Design**
- Asynchronous communication via Kafka/NATS message bus
- Event sourcing for audit trails and system replay
- Real-time stream processing for telemetry and analytics

**4.1.3 Cloud-Native & Edge Computing**
- Kubernetes orchestration for container management
- Edge nodes for latency-sensitive vehicle operations
- Hybrid cloud deployment for data sovereignty

**4.1.4 API-First Development**
- OpenAPI/Swagger specifications for all services
- Versioned APIs with backward compatibility
- Developer portal with interactive documentation

### 4.2 Technology Stack

**Backend Services:**
- Languages: Node.js, Python, Go
- Frameworks: Express.js, Flask, FastAPI
- Message Queue: Apache Kafka, NATS
- Databases: PostgreSQL, InfluxDB, Redis, MongoDB

**Frontend & Interfaces:**
- Web: React, Vue.js
- Mobile: React Native
- HMI: Qt, Flutter

**Infrastructure:**
- Containers: Docker
- Orchestration: Kubernetes (K8s)
- Service Mesh: Istio
- CI/CD: Jenkins, GitLab CI, ArgoCD

**AI/ML:**
- Frameworks: TensorFlow, PyTorch
- MLOps: MLflow, Kubeflow
- Simulation: CARLA, SUMO

**Monitoring & Observability:**
- Metrics: Prometheus
- Visualization: Grafana
- Logging: ELK Stack (Elasticsearch, Logstash, Kibana)
- Tracing: Jaeger, OpenTelemetry

---

## 5. Platform Layers

### 5.1 Platform Management Layer

**Purpose:** Governance, policies, RBAC, audit, and strategic oversight

**Key Components:**
- **Governance Engine**: Policy creation, enforcement, compliance monitoring
- **RBAC Service**: Role-based access control across all layers
- **Audit Service**: Immutable logs, compliance reporting
- **Analytics Dashboard**: KPI tracking, executive insights

**Responsibilities:**
- Define and enforce operational policies
- Manage user roles and permissions
- Track system-wide compliance and audit trails
- Provide strategic insights and recommendations

**Data Flows:**
```
Platform Management
    │
    ├─► Fleet Layer (directives, policies)
    ├─► Vehicle Layer (configurations, updates)
    ├─► Data Layer (analytics queries)
    └─► Access Portal (dashboard data)
```

### 5.2 Fleet Management Layer

**Purpose:** Vehicle scheduling, routing, resource allocation, and telematics

**Key Components:**
- **Fleet Controller**: Central orchestration service
- **Scheduling Engine**: AI-optimized task allocation
- **Telematics Service**: Real-time vehicle tracking
- **Resource Manager**: Vehicle availability and utilization

**Responsibilities:**
- Optimize fleet routes and schedules
- Monitor vehicle health and performance
- Manage resource allocation (vehicles, drivers, cargo)
- Coordinate with collective intelligence for multi-vehicle tasks

**API Endpoints:**
```
GET    /api/fleet/{fleet_id}/status
POST   /api/fleet/{fleet_id}/schedule
GET    /api/fleet/{fleet_id}/resources
PUT    /api/fleet/{fleet_id}/vehicle/{vehicle_id}/assign
GET    /api/fleet/{fleet_id}/telemetry
```

### 5.3 Vehicle Layer

**Purpose:** Autonomous driving, vehicle control, sensors, and diagnostics

**Key Subsystems:**

**5.3.1 Autonomous Driving & Safety**
- SLAM (Simultaneous Localization and Mapping)
- UKF (Unscented Kalman Filter) prediction
- Path planning and trajectory optimization
- Collision avoidance and emergency braking
- ADAS (Advanced Driver Assistance Systems)

**5.3.2 Energy & Powertrain**
- Hybrid fuel management (electric, solar, hydrogen, fossil)
- Battery and fuel cell monitoring
- Regenerative braking control
- Energy optimization algorithms

**5.3.3 Vehicle Core Systems**
- Engine control
- Transmission management
- Brake and suspension systems
- Climate control and HVAC
- Smart exhaust management

**5.3.4 Input/Output Controls**
- Steering, pedals, lights
- Infotainment systems
- Passenger comfort controls
- Human-Machine Interface (HMI)

**5.3.5 Diagnostics & Monitoring**
- OBD (On-Board Diagnostics)
- Predictive maintenance
- Chassis and body sensors
- Internal system health monitoring

**API Endpoints:**
```
GET    /api/vehicle/{vehicle_id}/status
POST   /api/vehicle/{vehicle_id}/command
GET    /api/vehicle/{vehicle_id}/diagnostics
POST   /api/vehicle/{vehicle_id}/update
GET    /api/vehicle/{vehicle_id}/telemetry
```

### 5.4 Collective Intelligence Layer

**Purpose:** Vehicle coordination, crowdsensing, and adaptive learning

**Key Components:**
- **Flocking Coordinator**: Multi-vehicle movement coordination
- **Crowdsensing Aggregator**: Shared environmental perception
- **Social Contracts Engine**: V2V agreement negotiation
- **DAVO (Decentralized Autonomous Vehicle Organization)**: Self-organizing networks

**Responsibilities:**
- Coordinate vehicle flocking behavior
- Aggregate and share sensor data across vehicles
- Manage decentralized decision-making
- Optimize collective risk/exploration balance

### 5.5 Data & Computation Layer

**Purpose:** Data fusion, big data processing, IoT integration, and AI/ML

**Key Components:**
- **Data Fusion Engine**: Multi-sensor integration
- **Big Data Platform**: Storage and analytics (Hadoop, Spark)
- **IoT Gateway**: Smart city and infrastructure integration
- **DSASE-LM**: Distributed Simulation and AI/ML Lifecycle Management

**Responsibilities:**
- Fuse data from sensors, vehicles, fleet, and infrastructure
- Process real-time telemetry streams
- Store and analyze historical data
- Train, validate, and deploy AI/ML models

### 5.6 User & Gamification Layer

**Purpose:** User engagement, feedback, eco-behavior incentives

**Key Components:**
- **Feedback Service**: Collect driver and passenger input
- **Gamification Engine**: Points, badges, leaderboards
- **Mobility Optimizer**: Personalized route and behavior recommendations
- **Strategic Management**: User goal tracking and optimization

**Responsibilities:**
- Collect and analyze user feedback
- Incentivize eco-friendly and safe driving
- Provide personalized mobility recommendations
- Track and optimize user goals and preferences

### 5.7 UCNS (Unified Communications & Networking System)

**Purpose:** V2V, V2I, V2P messaging and distributed resource coordination

**Key Components:**
- **Message Router**: V2X message routing and filtering
- **Network Orchestrator**: Bandwidth and latency optimization
- **Security Gateway**: Encrypted messaging and authentication
- **Fog Computing Manager**: Edge resource coordination

**Responsibilities:**
- Enable real-time V2V, V2I, and V2P communications
- Optimize network resource allocation
- Ensure secure, low-latency messaging
- Coordinate distributed fog computing tasks

### 5.8 Safety, Risk & Emergency Layer

**Purpose:** Predictive safety, failsafe, and emergency response

**Key Components:**
- **USRMS (Unified Safety & Risk Management System)**: Central risk engine
- **Emergency Override**: Critical command execution
- **Collision Avoidance**: Real-time threat detection and mitigation
- **Failsafe Manager**: Redundancy and backup systems

**Responsibilities:**
- Monitor safety metrics across all layers
- Predict and mitigate risks
- Execute emergency overrides
- Ensure failsafe operation under faults

### 5.9 DSASE-LM Layer

**Purpose:** AI/ML simulation, training, testing, and lifecycle management

**Key Components:**
- **Scenario Generator**: Create test scenarios and environments
- **Model Repository**: Store and version ML models
- **Training Pipeline**: Distributed model training
- **Benchmarking Service**: Performance evaluation and comparison

**Responsibilities:**
- Generate realistic simulation scenarios
- Train AI/ML models with vehicle and fleet data
- Validate and benchmark model performance
- Deploy models to production environments

### 5.10 Smart City / ITS Layer

**Purpose:** Intelligent transportation system integration

**Key Components:**
- **Traffic Optimizer**: Dynamic flow optimization
- **Infrastructure Gateway**: Connect to city sensors and signals
- **Coordination Service**: Multi-modal transport integration
- **Analytics Engine**: City-wide mobility insights

**Responsibilities:**
- Optimize traffic flow and reduce congestion
- Integrate with city infrastructure (lights, sensors, parking)
- Coordinate with public transit systems
- Provide mobility analytics to city planners

### 5.11 Manufacturer & Emergency Override Layer

**Purpose:** OEM control, critical overrides, and administrative functions

**Key Components:**
- **Override Controller**: Emergency command execution
- **Manufacturer Portal**: OEM administration interface
- **Audit Logger**: Track all override actions
- **Compliance Monitor**: Ensure regulatory adherence

**Responsibilities:**
- Enable manufacturer-level vehicle control
- Execute emergency services overrides
- Maintain audit trails for all critical actions
- Ensure compliance with safety regulations

### 5.12 Developer & Maintenance Layer

**Purpose:** Development tools, OTA updates, and system maintenance

**Key Components:**
- **Build Service**: Compile and package software
- **Deploy Service**: OTA updates and rollbacks
- **Diagnostic Tools**: System health and debugging
- **Simulation Interface**: Developer access to DSASE-LM

**Responsibilities:**
- Build and deploy software updates
- Enable remote diagnostics and maintenance
- Provide developer tools and APIs
- Support simulation and testing workflows

---

## 6. Microservices Catalog

### 6.1 Service Registry

| Service Name | Technology | Port | Dependencies | Data Store | Purpose |
|--------------|-----------|------|--------------|------------|---------|
| platform-mgmt | Node.js | 3001 | auth-service, audit-service | PostgreSQL | Platform governance |
| fleet-mgmt | Python | 3002 | vehicle-service, ucns-service | PostgreSQL, InfluxDB | Fleet orchestration |
| vehicle-core | Node.js | 3003 | sensor-service, safety-service | Redis, InfluxDB | Vehicle control |
| collective-intel | Python | 3004 | vehicle-service, ucns-service | Redis, MongoDB | Coordination |
| data-fusion | Go | 3005 | vehicle-service, iot-gateway | InfluxDB, Kafka | Data integration |
| ucns-orchestrator | Go | 3006 | vehicle-service, fleet-service | Redis, Kafka | V2X messaging |
| safety-risk | Python | 3007 | vehicle-service, fleet-service | PostgreSQL, Redis | Safety management |
| dsase-lm | Python | 3008 | data-fusion, model-repo | MongoDB, S3 | AI/ML lifecycle |
| smartcity-its | Node.js | 3009 | ucns-service, traffic-api | PostgreSQL, InfluxDB | City integration |
| gamification | Node.js | 3010 | user-service, fleet-service | PostgreSQL, Redis | User engagement |
| auth-service | Go | 3011 | - | PostgreSQL | Authentication |
| api-gateway | Node.js | 8080 | All services | Redis | API routing |

### 6.2 Service Communication Patterns

**6.2.1 Synchronous Communication (REST/gRPC)**
```
Client → API Gateway → Service A → Service B → Database
          (Auth)        (Business Logic)  (Data Persistence)
```

**6.2.2 Asynchronous Communication (Event-Driven)**
```
Service A → Message Queue → Service B
                ↓
           Event Store (Audit/Replay)
```

**6.2.3 Request-Response with Event Notification**
```
Client → Service A (Sync Response)
           ↓
        Message Queue
           ↓
        Service B, C, D (Async Processing)
```

---

## 7. Data Architecture

### 7.1 Data Model Overview

**7.1.1 Core Entities**

```
┌─────────────┐       ┌─────────────┐       ┌─────────────┐
│   Platform  │──────▶│    Fleet    │──────▶│   Vehicle   │
└─────────────┘       └─────────────┘       └─────────────┘
       │                     │                      │
       ▼                     ▼                      ▼
┌─────────────┐       ┌─────────────┐       ┌─────────────┐
│   Policies  │       │  Schedules  │       │  Telemetry  │
└─────────────┘       └─────────────┘       └─────────────┘
```

**7.1.2 Entity Relationship Diagram**

```
Platform (1) ──────── (*) Fleet
Fleet (1) ──────── (*) Vehicle
Vehicle (1) ──────── (*) Sensor
Vehicle (1) ──────── (*) Event
User (1) ──────── (*) Trip
Fleet (*) ──────── (*) User (Many-to-Many)
Vehicle (1) ──────── (*) MaintenanceRecord
AIModel (1) ──────── (*) Simulation
SmartCity (1) ──────── (*) TrafficEvent
```

### 7.2 Database Schema

**7.2.1 Vehicles Table**
```sql
CREATE TABLE vehicles (
    vehicle_id UUID PRIMARY KEY,
    fleet_id UUID REFERENCES fleets(fleet_id),
    vin VARCHAR(17) UNIQUE NOT NULL,
    make VARCHAR(50),
    model VARCHAR(50),
    year INTEGER,
    fuel_type VARCHAR(20), -- electric, hybrid, hydrogen, fossil
    battery_capacity FLOAT,
    status VARCHAR(20), -- active, maintenance, offline
    location GEOMETRY(Point, 4326),
    created_at TIMESTAMP DEFAULT NOW(),
    updated_at TIMESTAMP DEFAULT NOW()
);
```

**7.2.2 Fleets Table**
```sql
CREATE TABLE fleets (
    fleet_id UUID PRIMARY KEY,
    operator_id UUID REFERENCES users(user_id),
    name VARCHAR(100) NOT NULL,
    total_vehicles INTEGER,
    route_plan JSONB,
    created_at TIMESTAMP DEFAULT NOW()
);
```

**7.2.3 Telemetry Table (Time-Series)**
```sql
-- InfluxDB Schema
measurement: vehicle_telemetry
tags:
    - vehicle_id
    - sensor_type
fields:
    - speed (float)
    - heading (float)
    - latitude (float)
    - longitude (float)
    - battery_level (float)
    - fuel_level (float)
    - sensor_reading (float)
timestamp: nanosecond precision
```

**7.2.4 Events Table**
```sql
CREATE TABLE events (
    event_id UUID PRIMARY KEY,
    event_type VARCHAR(50), -- safety, command, alert
    source_id UUID,
    source_type VARCHAR(20), -- vehicle, fleet, platform
    target_id UUID,
    payload JSONB,
    severity VARCHAR(20), -- info, warning, critical
    created_at TIMESTAMP DEFAULT NOW()
);
```

**7.2.5 AI Models Table**
```sql
CREATE TABLE ai_models (
    model_id UUID PRIMARY KEY,
    name VARCHAR(100),
    version VARCHAR(20),
    type VARCHAR(50), -- prediction, optimization, detection
    status VARCHAR(20), -- training, validated, deployed
    metrics JSONB,
    created_at TIMESTAMP DEFAULT NOW()
);
```

### 7.3 Data Flow Architecture

```
┌─────────────────────────────────────────────────────────┐
│                   DATA INGESTION                        │
├─────────────────────────────────────────────────────────┤
│                                                         │
│  Vehicle Sensors → UCNS → Message Queue (Kafka)        │
│                              ↓                          │
│  IoT Devices → Gateway → Message Queue (Kafka)         │
│                              ↓                          │
│  User Interactions → API → Message Queue (Kafka)       │
│                                                         │
└────────────────────┬────────────────────────────────────┘
                     ▼
┌─────────────────────────────────────────────────────────┐
│                STREAM PROCESSING                        │
├─────────────────────────────────────────────────────────┤
│                                                         │
│  Apache Kafka Streams / Apache Flink                   │
│    - Data validation and enrichment                    │
│    - Real-time aggregation                             │
│    - Anomaly detection                                 │
│    - Feature extraction for ML                         │
│                                                         │
└────────────────────┬────────────────────────────────────┘
                     ▼
┌─────────────────────────────────────────────────────────┐
│                   DATA STORAGE                          │
├─────────────────────────────────────────────────────────┤
│                                                         │
│  PostgreSQL (Transactional) ← Operational Data         │
│  InfluxDB (Time-Series) ← Telemetry & Metrics         │
│  MongoDB (Document) ← Semi-structured Data             │
│  Redis (Cache) ← Session & Real-time State            │
│  S3 (Object) ← ML Models & Archives                   │
│                                                         │
└────────────────────┬────────────────────────────────────┘
                     ▼
┌─────────────────────────────────────────────────────────┐
│                 ANALYTICS & ML                          │
├─────────────────────────────────────────────────────────┤
│                                                         │
│  Apache Spark → Batch Analytics                        │
│  TensorFlow/PyTorch → Model Training                   │
│  MLflow → Model Management                             │
│  Grafana → Visualization                               │
│                                                         │
└─────────────────────────────────────────────────────────┘
```

---

## 8. Security Framework

### 8.1 Security Architecture

**8.1.1 Defense in Depth**

```
┌─────────────────────────────────────────────┐
│          Layer 7: User Education            │
├─────────────────────────────────────────────┤
│          Layer 6: Application               │
│   - Input validation                        │
│   - Output encoding                         │
│   - OWASP compliance                        │
├─────────────────────────────────────────────┤
│          Layer 5: API Gateway               │
│   - Rate limiting                           │
│   - JWT validation                          │
│   - API key management                      │
├─────────────────────────────────────────────┤
│          Layer 4: Service Mesh              │
│   - mTLS between services                   │
│   - Service-to-service auth                 │
│   - Traffic encryption                      │
├─────────────────────────────────────────────┤
│          Layer 3: Network                   │
│   - Firewall rules                          │
│   - Network segmentation                    │
│   - DDoS protection                         │
├─────────────────────────────────────────────┤
│          Layer 2: Host                      │
│   - Container security                      │
│   - OS hardening                            │
│   - Intrusion detection                     │
├─────────────────────────────────────────────┤
│          Layer 1: Physical                  │
│   - Secure data centers                     │
│   - Access controls                         │
└─────────────────────────────────────────────┘
```

### 8.2 Authentication & Authorization

**8.2.1 RBAC Model**

```
Roles:
  - Super Admin (Platform Management)
  - Fleet Operator (Fleet Management)
  - Vehicle Technician (Vehicle Maintenance)
  - Developer (API Access)
  - End User (Basic Access)

Permissions Matrix:

| Resource      | Super Admin | Fleet Operator | Technician | Developer | User |
|---------------|-------------|----------------|------------|-----------|------|
| Platform Mgmt | CRUD        | R              | R          | R         | -    |
| Fleet Mgmt    | CRUD        | CRUD           | R          | R         | R    |
| Vehicle Ctrl  | CRUD        | RU             | CRUD       | R         | R    |
| Safety Ovrd   | CRUD        | RU             | R          | -         | -    |
| Dev Tools     | CRUD        | -              | -          | CRUD      | -    |
| User Data     | CRUD        | R              | R          | R         | CRUD |
```

**8.2.2 Authentication Flow**

```
User → Login Request → Auth Service
                         ↓
                    Validate Credentials
                         ↓
                    Generate JWT Token
                         ↓
User ← Access Token + Refresh Token
                         ↓
API Request with Token → API Gateway
                         ↓
                    Validate JWT
                         ↓
                    Extract Claims
                         ↓
                    Check RBAC
                         ↓
Authorized Request → Backend Service
```

### 8.3 Encryption

**At Rest:**
- Database: AES-256 encryption
- Object Storage: S3 server-side encryption
- Secrets: HashiCorp Vault or AWS Secrets Manager

**In Transit:**
- TLS 1.3 for all HTTP communications
- mTLS for service-to-service within K8s cluster
- V2X: Encrypted messaging with certificate-based authentication

### 8.4 Audit & Compliance

**8.4.1 Audit Logging**
- All API calls logged with user, timestamp, action, result
- Immutable event store for compliance
- Retention: 7 years for regulatory compliance

**8.4.2 Compliance Standards**
- ISO 26262 (Automotive Safety)
- ISO 21434 (Cybersecurity)
- GDPR (Data Privacy)
- CCPA (California Privacy)
- SOC 2 Type II (Service Organization Controls)

---

## 9. API Specifications

### 9.1 API Gateway Configuration

**Base URL:** `https://api.nandi.mobility/v1`

**Authentication:** Bearer Token (JWT)

**Rate Limits:**
- Authenticated: 1000 requests/minute
- Unauthenticated: 100 requests/minute

### 9.2 Platform Management API

```yaml
/platform:
  /policies:
    GET:
      summary: List all policies
      responses:
        200:
          schema:
            type: array
            items: $ref: '#/components/schemas/Policy'
    POST:
      summary: Create new policy
      requestBody:
        schema: $ref: '#/components/schemas/PolicyCreate'
      responses:
        201:
          schema: $ref: '#/components/schemas/Policy'
          
  /rbac/assign-role:
    POST:
      summary: Assign role to user
      requestBody:
        schema:
          type: object
          properties:
            user_id: string
            role: string
      responses:
        200:
          description: Role assigned successfully
          
  /audit/logs:
    GET:
      summary: Retrieve audit logs
      parameters:
        - name: from
          in: query
          type: string
          format: date-time
        - name: to
          in: query
          type: string
          format: date-time
      responses:
        200:
          schema:
            type: array
            items: $ref: '#/components/schemas/AuditLog'
```

### 9.3 Fleet Management API

```yaml
/fleet:
  /{fleet_id}:
    /status:
      GET:
        summary: Get fleet status
        responses:
          200:
            schema: $ref: '#/components/schemas/FleetStatus'
    /schedule:
      POST:
        summary: Create schedule
        requestBody:
          schema: $ref: '#/components/schemas/Schedule'
        responses:
          201:
            schema: $ref: '#/components/schemas/ScheduleResponse'
    /resources:
      GET:
        summary: Get resource allocation
        responses:
          200:
            schema: $ref: '#/components/schemas/Resources'
    /telemetry:
      GET:
        summary: Get fleet telemetry
        parameters:
          - name: from
            type: string
            format: date-time
          - name: to
            type: string
            format: date-time
        responses:
          200:
            schema:
              type: array
              items: $ref: '#/components/schemas/Telemetry'
```

### 9.4 Vehicle API

```yaml
/vehicle:
  /{vehicle_id}:
    /status:
      GET:
        summary: Get vehicle status
        responses:
          200:
            schema: $ref: '#/components/schemas/VehicleStatus'
    /command:
      POST:
        summary: Send command to vehicle
        requestBody:
          schema:
            type: object
            properties:
              action: string
              parameters: object
        responses:
          200:
            description: Command acknowledged
    /diagnostics:
      GET:
        summary: Get vehicle diagnostics
        responses:
          200:
            schema: $ref: '#/components/schemas/Diagnostics'
    /update:
      POST:
        summary: OTA software update
        requestBody:
          schema:
            type: object
            properties:
              version: string
              module: string
        responses:
          202:
            description: Update initiated
```
# The Book of Nandi
## Design Specification Document
### Nandi Mobility Factory Operating System Solution Platform

---

## 10. Integration Patterns

### 10.1 Integration Architecture

#### 10.1.1 Integration Layers
```
┌─────────────────────────────────────────────────────────┐
│                 INTEGRATION ORCHESTRATION                │
├─────────────────────────────────────────────────────────┤
│                                                          │
│  API Gateway ──► Service Mesh ──► Event Bus ──► Data    │
│                                                   Lake   │
└─────────────────────────────────────────────────────────┘
```

#### 10.1.2 Communication Patterns

**Synchronous Integration**
```
External System → API Gateway → Load Balancer → Service
                                    ↓
                              Authentication/Rate Limiting
```

**Asynchronous Integration**
```
Service A → Event Publisher → Message Queue → Event Consumer → Service B
                                 ↓
                          Event Store (Replay)
```

**Hybrid Pattern**
```
Request → API (Immediate ACK) → Queue → Background Processing
                ↓
           Status Endpoint ← Polling/Webhook ← Result
```

### 10.2 External System Integration

#### 10.2.1 Smart City Integration Points
```yaml
smart_city_apis:
  traffic_management:
    endpoint: /api/v1/traffic
    methods: [GET, POST, PUT]
    data_sync: real-time
    authentication: OAuth2
    
  infrastructure:
    charging_stations:
      discovery: /api/v1/charging/locations
      availability: /api/v1/charging/status
      reservation: /api/v1/charging/reserve
      
    parking:
      availability: /api/v1/parking/status
      guidance: /api/v1/parking/navigate
      
  emergency_services:
    endpoint: /api/v1/emergency
    priority: CRITICAL
    redundancy: multi-path
```

#### 10.2.2 Third-Party Service Integration
```yaml
payment_processors:
  - provider: Stripe
    integration: REST API
    features: [subscriptions, one-time, refunds]
    
  - provider: PayPal
    integration: SDK
    features: [checkout, wallet, express]

mapping_services:
  - provider: Google Maps
    features: [routing, geocoding, traffic]
    
  - provider: HERE Maps
    features: [fleet, truck, offline]

weather_data:
  - provider: OpenWeatherMap
    update_frequency: 15min
    data: [conditions, forecast, alerts]
```

### 10.3 Data Integration Patterns

#### 10.3.1 ETL Pipeline
```
Extract → Transform → Load → Validate
   ↓          ↓          ↓        ↓
Source    Cleanse    Target   Quality
Data      Format     DB       Checks
```

#### 10.3.2 Data Synchronization Strategy
```yaml
sync_patterns:
  real_time:
    - vehicle_telemetry
    - safety_alerts
    - emergency_events
    latency: < 100ms
    
  near_real_time:
    - fleet_status
    - resource_availability
    - traffic_updates
    latency: < 5s
    
  batch:
    - analytics_aggregation
    - historical_reports
    - billing_data
    frequency: hourly/daily
```

### 10.4 API Integration Standards

#### 10.4.4 Webhook Configuration
```yaml
webhooks:
  vehicle_events:
    url: https://partner.com/webhooks/vehicle
    events:
      - vehicle.started
      - vehicle.stopped
      - vehicle.maintenance_due
    retry_policy:
      max_attempts: 5
      backoff: exponential
      
  fleet_events:
    url: https://partner.com/webhooks/fleet
    events:
      - fleet.schedule_updated
      - fleet.resource_allocated
      - fleet.task_completed
```

---

## 11. Deployment Architecture

### 11.1 Environment Strategy

#### 11.1.1 Environment Tiers
```
┌─────────────────────────────────────────────────────────┐
│                    PRODUCTION                            │
│  - Multi-region deployment                              │
│  - Auto-scaling enabled                                 │
│  - 99.99% SLA                                          │
├─────────────────────────────────────────────────────────┤
│                    STAGING                              │
│  - Production mirror                                    │
│  - Pre-release testing                                 │
│  - Performance validation                              │
├─────────────────────────────────────────────────────────┤
│                    DEVELOPMENT                          │
│  - Feature development                                  │
│  - Integration testing                                 │
│  - Rapid iteration                                     │
└─────────────────────────────────────────────────────────┘
```

#### 11.1.2 Cloud Architecture
```yaml
infrastructure:
  platform: Kubernetes
  
  compute:
    nodes:
      type: auto-scaling
      min: 10
      max: 100
      instance_type: c5.2xlarge
      
  storage:
    persistent_volumes:
      type: SSD
      replication: 3
      backup: hourly
      
    object_storage:
      provider: S3
      versioning: enabled
      lifecycle: tiered
      
  networking:
    load_balancers:
      type: Application Load Balancer
      ssl_termination: enabled
      
    service_mesh:
      provider: Istio
      mtls: enforced
      
  databases:
    relational:
      engine: PostgreSQL
      version: 14
      deployment: multi-AZ
      read_replicas: 3
      
    time_series:
      engine: InfluxDB
      retention: 90days
      downsampling: automated
```

### 11.2 Deployment Pipeline

#### 11.2.1 CI/CD Workflow
```
Code Commit → Build → Test → Security Scan → Deploy
                ↓       ↓          ↓            ↓
            Container  Unit     Vulnerability  Staging
            Image     Tests     Scanning       Environment
                      ↓
                 Integration
                 Tests
```

#### 11.2.2 Deployment Strategies
```yaml
deployment_patterns:
  blue_green:
    description: Zero-downtime deployments
    use_case: Major updates
    rollback_time: < 30s
    
  canary:
    description: Gradual rollout
    stages:
      - 10% traffic: 30min
      - 50% traffic: 1hr
      - 100% traffic: 2hr
    auto_rollback: enabled
    
  rolling:
    description: Sequential pod updates
    batch_size: 25%
    health_check_interval: 10s
```

### 11.3 Geographic Distribution

#### 11.3.1 Multi-Region Architecture
```yaml
regions:
  primary:
    location: us-east-1
    services: [all]
    traffic: 40%
    
  secondary:
    location: eu-west-1
    services: [all]
    traffic: 30%
    
  tertiary:
    location: ap-southeast-1
    services: [all]
    traffic: 30%

cross_region:
  data_replication: async
  failover: automatic
  latency_routing: enabled
```

---

## 12. Operational Requirements

### 12.1 Monitoring & Observability

#### 12.1.1 Metrics Collection
```yaml
prometheus_metrics:
  system:
    - cpu_usage
    - memory_usage
    - disk_io
    - network_throughput
    
  application:
    - request_rate
    - response_time
    - error_rate
    - queue_depth
    
  business:
    - active_vehicles
    - completed_trips
    - gamification_scores
    - energy_efficiency
```

#### 12.1.2 Distributed Tracing
```yaml
jaeger_config:
  sampling:
    type: probabilistic
    param: 0.1
    
  spans:
    - api_requests
    - database_queries
    - message_queue_operations
    - external_api_calls
```

#### 12.1.3 Logging Strategy
```yaml
logging:
  levels:
    production: INFO
    staging: DEBUG
    
  aggregation:
    tool: ELK Stack
    retention: 30days
    
  structured_logging:
    format: JSON
    fields:
      - timestamp
      - service_name
      - trace_id
      - user_id
      - log_level
      - message
```

### 12.2 Alerting

#### 12.2.1 Alert Rules
```yaml
alerts:
  critical:
    - name: HighErrorRate
      condition: error_rate > 5%
      duration: 5m
      notification: [pagerduty, slack]
      
    - name: ServiceDown
      condition: up == 0
      duration: 1m
      notification: [pagerduty, phone]
      
  warning:
    - name: HighLatency
      condition: p95_latency > 1s
      duration: 10m
      notification: [slack, email]
      
    - name: HighMemoryUsage
      condition: memory_usage > 80%
      duration: 15m
      notification: [slack]
```

### 12.3 Disaster Recovery

#### 12.3.1 Backup Strategy
```yaml
backups:
  databases:
    full_backup:
      frequency: daily
      retention: 30days
      
    incremental:
      frequency: hourly
      retention: 7days
      
    point_in_time_recovery:
      enabled: true
      retention: 7days
      
  configurations:
    frequency: on_change
    versioning: enabled
    retention: 90days
```

#### 12.3.2 Recovery Procedures
```yaml
recovery:
  rto: 1hour  # Recovery Time Objective
  rpo: 15min  # Recovery Point Objective
  
  procedures:
    database_failure:
      - Promote read replica
      - Update DNS records
      - Verify data integrity
      
    region_failure:
      - Activate failover region
      - Redirect traffic
      - Validate services
```

---

## 13. Development Guidelines

### 13.1 Code Standards

#### 13.1.1 Style Guides
```yaml
backend:
  languages:
    python:
      style_guide: PEP 8
      formatter: black
      linter: pylint
      
    node:
      style_guide: Airbnb
      formatter: prettier
      linter: eslint
      
    go:
      style_guide: Effective Go
      formatter: gofmt
      linter: golangci-lint

frontend:
  framework: React
  style_guide: Airbnb React
  formatter: prettier
  linter: eslint
```

#### 13.1.2 Code Review Process
```yaml
review_requirements:
  mandatory:
    - At least 1 approval
    - All tests passing
    - No merge conflicts
    - Security scan passed
    
  recommended:
    - 2+ approvals for critical changes
    - Performance benchmark validation
    - Documentation updated
```

### 13.2 Testing Strategy

#### 13.2.1 Test Pyramid
```
              ┌─────────────┐
              │   E2E Tests │  (10%)
              └─────────────┘
          ┌─────────────────────┐
          │ Integration Tests   │  (30%)
          └─────────────────────┘
     ┌──────────────────────────────┐
     │      Unit Tests              │  (60%)
     └──────────────────────────────┘
```

#### 13.2.2 Test Coverage Requirements
```yaml
coverage_requirements:
  unit_tests:
    minimum: 80%
    target: 90%
    
  integration_tests:
    minimum: 70%
    target: 85%
    
  critical_paths:
    minimum: 95%
    target: 100%
```

### 13.3 Development Workflow

#### 13.3.1 Git Branching Strategy
```
main (production)
  ↓
develop (integration)
  ↓
feature/* (new features)
hotfix/* (urgent fixes)
release/* (release candidates)
```

#### 13.3.2 Commit Convention
```
type(scope): subject

body

footer

Types: feat, fix, docs, style, refactor, test, chore
Example: feat(vehicle): add battery prediction algorithm
```

---

## 14. Appendices

### Appendix A: Glossary

**ADAS**: Advanced Driver Assistance Systems  
**API**: Application Programming Interface  
**CAM**: Cooperative Awareness Message  
**DAVO**: Decentralized Autonomous Vehicle Organization  
**DENM**: Decentralized Environmental Notification Message  
**DSASE-LM**: Distributed Scenario & AI/ML Simulation Engine - Lifecycle Management  
**DSRC**: Dedicated Short-Range Communications  
**FMS**: Fuel Management System  
**GDPR**: General Data Protection Regulation  
**ITS**: Intelligent Transportation System  
**OBD**: On-Board Diagnostics  
**OTA**: Over-The-Air  
**RBAC**: Role-Based Access Control  
**SLAM**: Simultaneous Localization and Mapping  
**SOC**: Service Organization Controls  
**SOTIF**: Safety Of The Intended Functionality  
**UKF**: Unscented Kalman Filter  
**USRMS**: Unified Safety & Risk Management System  
**V2I**: Vehicle-to-Infrastructure  
**V2P**: Vehicle-to-Pedestrian  
**V2V**: Vehicle-to-Vehicle  
**V2X**: Vehicle-to-Everything

### Appendix B: Reference Architecture Diagram

```
┌────────────────────────────────────────────────────────────────────────────┐
│                         NANDI MF-OS REFERENCE ARCHITECTURE                  │
├────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─────────────────────┐         ┌─────────────────────┐                  │
│  │  ACCESS PORTAL      │         │  MANUFACTURER       │                  │
│  │  - User Interface   │◄────────┤  ADMIN PORTAL       │                  │
│  │  - Developer Portal │         │  - Diagnostics      │                  │
│  └──────────┬──────────┘         └──────────┬──────────┘                  │
│             │                                │                              │
│             └────────────────┬───────────────┘                              │
│                              │                                              │
│                    ┌─────────▼──────────┐                                  │
│                    │  PLATFORM LAYER    │                                  │
│                    │  - Governance      │                                  │
│                    │  - Fleet Mgmt      │                                  │
│                    │  - Collective Intel│                                  │
│                    └─────────┬──────────┘                                  │
│                              │                                              │
│         ┌────────────────────┼────────────────────┐                       │
│         │                    │                    │                       │
│    ┌────▼─────┐         ┌───▼─────┐         ┌───▼─────┐                 │
│    │ VEHICLE  │◄────────┤  DATA   │◄────────┤  USER   │                 │
│    │ LAYER    │         │  LAYER  │         │  LAYER  │                 │
│    └────┬─────┘         └────┬────┘         └────┬────┘                 │
│         │                     │                    │                       │
│         └─────────────────────┼────────────────────┘                       │
│                               │                                            │
│                    ┌──────────▼───────────┐                               │
│                    │  UCNS / V2X LAYER    │                               │
│                    └──────────┬───────────┘                               │
│                               │                                            │
│                    ┌──────────▼───────────┐                               │
│                    │  SAFETY & RISK       │                               │
│                    │  MANAGEMENT          │                               │
│                    └──────────────────────┘                               │
│                                                                             │
└────────────────────────────────────────────────────────────────────────────┘
```

### Appendix C: System Capacity Planning

```yaml
capacity_targets:
  vehicles:
    initial: 10,000
    year_1: 100,000
    year_3: 1,000,000
    
  transactions_per_second:
    telemetry: 500,000
    api_requests: 50,000
    v2v_messages: 1,000,000
    
  data_storage:
    hot_storage: 10TB
    warm_storage: 100TB
    cold_storage: 1PB
```

### Appendix D: Compliance Matrix

```yaml
compliance_standards:
  automotive:
    - ISO 26262 (Functional Safety)
    - ISO 21434 (Cybersecurity)
    - ISO 20077 (Extended Vehicle)
    
  data_privacy:
    - GDPR (Europe)
    - CCPA (California)
    - LGPD (Brazil)
    
  security:
    - SOC 2 Type II
    - ISO 27001
    - NIST Cybersecurity Framework
    
  quality:
    - ISO 9001
    - IATF 16949 (Automotive)
```

---

## Document Version History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2026-01-12 | Nandi Engineering Team | Initial release |

---

## Approval Signatures

**Chief Technology Officer**: _________________________  
**VP of Engineering**: _________________________  
**VP of Product**: _________________________  
**Chief Information Security Officer**: _________________________

---

**Document Classification**: Confidential  
**Distribution**: Internal Use Only  
**Review Cycle**: Quarterly  
**Next Review Date**: 2026-04-12

---

*End of The Book of Nandi Design Specification Document*
