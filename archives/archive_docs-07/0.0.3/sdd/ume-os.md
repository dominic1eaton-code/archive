Below is the **complete, canonical, end-to-end UME-Platform Architecture**, fully restructured to use the four top-level components:

```
UME-MODEL      — organization model  
UME-OS         — organization OS + applications  
UME-SDO        — organization kernel (software-defined organization)  
UME-BASE       — physical infrastructure + devices  
```

Everything in the platform fits cleanly and seamlessly inside these four pillars.
This is now the **official, definitive UME-Platform architecture**.

All diagrams are ASCII-friendly, fully aligned with your prior constraints, and express the platform as a **general-purpose organization operating system**.

---

# ============================================================

# UME-PLATFORM

## COMPLETE ARCHITECTURE (ASCII TEXT FRIENDLY, CANONICAL)

# ============================================================

```
                           ┌───────────────────────────────┐
                           │            UME-OS             │
                           │   (Organization OS + Apps)     │
                           └───────────────▲───────────────┘
                                           │
                                workflows, UI actions,
                                business logic requests
                                           │
                      ┌────────────────────┼────────────────────┐
                      │                    │                    │
                      ▼                    │                    ▼
             ┌──────────────────┐          │           ┌──────────────────┐
             │    UME-MODEL     │◀────────┘           │     UME-BASE      │
             │ (Org Model, KG,  │    model refs        │  Physical Infra   │
             │  Schemas, Policy │                      │  Compute/Storage  │
             │  Canonical SOT)  │◀─────────────────────│  ODDS/Devices     │
             └─────────▲────────┘     infra feedback   └─────────▲────────┘
                       │                                          │
                       │                                          │
                       │           infra provisioning              │
                       │         device commands & telemetry       │
                       │                                          │
                       ▼                                          ▼
            ┌──────────────────────────────────────────────────────────┐
            │                       UME-SDO                            │
            │                 (Organization Kernel)                    │
            │  Universal core of all organizational behavior:          │
            │  - Policy Runtime / Enforcement                          │
            │  - OrgCPU Scheduler                                      │
            │  - Workflow Orchestrator                                 │
            │  - Event Bus / Event Model                               │
            │  - Plugin/ABI Runtime                                    │
            │  - Agent/A.I. Runtime (UICE/Jini)                        │
            │  - Audit Ledger (Immutable)                              │
            │  - Namespace & Isolation                                 │
            │  - Resource & Quota Control                              │
            │  - Device/ODDS Command Gateway                           │
            │  - Model Integration Runtime                             │
            │  - SDO Governance Engine                                 │
            └──────────────────────────────────────────────────────────┘
```

**Short summary:**
**UME-MODEL = describes the organization**
**UME-SDO = runs/enforces the organization**
**UME-OS = interacts with the organization**
**UME-BASE = hosts the organization**

---

# ============================================================

# 1. UME-MODEL

## “THE ORGANIZATION MODEL LAYER”

# ============================================================

### Purpose

UME-MODEL defines *what* an organization **is**:
its structure, entities, roles, relationships, policies, processes, semantics, ontology, and canonical representations.

### UME-MODEL contains:

* **Enterprise Ontology & Knowledge Graph**
* **Canonical Data Schemas & SOT definitions**
* **Policies as Code** (authority, finance, compliance, risk, audit, safety, etc.)
* **Org Structure & Relationships**
  (entities, departments, teams, projects, funds, contracts)
* **Workflows & Process Manifests** (ame rules, BPMN-lite definitions)
* **Permission Schemas & Capability Models**
* **Role/Principal semantics**
  (human, AI, device, service, org-unit)

### UME-SDO uses UME-MODEL:

* for **every policy evaluation**,
* to validate organizational actions,
* to instantiate workflows,
* to schedule OrgCPU,
* to enforce constraints (residency, authority, limits),
* to maintain canonical audit reference.

---

# ============================================================

# 2. UME-SDO

## “THE ORGANIZATION KERNEL”

# ============================================================

### Purpose

UME-SDO is the **software-defined organization runtime** and the **kernel** of the UME-Platform.
It executes and enforces the organizational model defined in UME-MODEL.

It is the only part of the system that can:

* make authoritative state transitions,
* commit audit records,
* schedule resources,
* instantiate workloads,
* orchestrate business processes,
* enforce policy decisions,
* govern AI/agent operations,
* command devices,
* manage provisioning,
* allocate namespaces and isolation containers.

### UME-SDO core kernel features:

**A. Policy Engine & Enforcement**

* atomic policy evaluation
* obligations, approvals, multi-party authority
* rule engine + formal semantics

**B. OrgCPU Scheduler**

* humans, agents, services, devices as schedulable execution units
* quota & budget control
* preemption, affinity, cost-aware scheduling

**C. Workflow Orchestrator**

* distributed process runner
* event-driven, state machine core
* integrates human approvals, automated tasks, agent tasks

**D. Event Bus**

* global publish/subscribe
* telemetry streams, business events, anomaly events

**E. Plugin/ABI Runtime**

* secure plugin load/unload
* capability-gated syscalls
* namespace isolation

**F. AI/Agent Runtime (UICE/Jini)**

* agent registration
* agent invocation & monitoring
* explainability + audit for each decision

**G. Audit Ledger**

* immutable, append-only
* HSM-signed entries
* hash chain integrity model

**H. Resource & Quota Control**

* compute/storage/network provisioning (via UME-BASE)
* quota guarantees, cost limits, residency constraints

**I. Namespace & Isolation**

* per-plugin, per-agent isolation
* model-based policy binding

**J. ODDS Device Gateway**

* secure device command channel
* telemetry aggregation
* safety policies

---

# ============================================================

# 3. UME-OS

## “THE ORGANIZATION OPERATING SYSTEM + APPLICATION LAYER”

# ============================================================

UME-OS provides all organization-facing applications and operating interfaces.

### UME-OS includes:

**A. Applications & Domains**

* Finance / Payments
* Procurement / Vendor
* HR / People / Talent
* CRM / Sales / Pipeline
* PMO / OKR / Strategy
* Knowledge / Docs
* Ops / Logistics / Dispatch
* Engineering / DevOps / Delivery

**B. OS-Level Services**

* Authentication & IAM
* UI frameworks
* Task & Inbox UI
* Dashboards & Views
* Workflow UIs
* Role-based experiences
* Notification system

**C. Interaction with UME-SDO**

* submits tasks
* receives events
* completes approvals
* triggers workflows
* displays state/schedule/provisioning
* renders audit logs

### Boundaries:

* **UME-OS does NOT enforce authority** → UME-SDO does
* **UME-OS does NOT write audit entries directly** → only UME-SDO does
* **UME-OS can only request actions** that UME-SDO permits

---

# ============================================================

# 4. UME-BASE

## “PHYSICAL INFRASTRUCTURE + DEVICES”

# ============================================================

UME-BASE hosts all physical and virtual execution environments.

### UME-BASE includes:

**A. Compute**

* VMs, containers, serverless sandboxes
* GPU/TPU/Edge compute

**B. Storage**

* object stores for audit blobs
* block volumes
* model/artifact storage

**C. Network**

* internal mesh
* regional gateways
* secure zones

**D. ODDS (Org Device & Device System)**

* IoT devices
* CPS systems
* sensors & actuators
* industrial gateways

**E. Provisioning**

* accepts API calls from UME-SDO only
* enforces infrastructure-level security & residency
* returns resource handles

**F. Telemetry**

* device-level and infra-level metrics/alerts
* delivered to UME-SDO event bus

---

# ============================================================

# 5. COMPLETE LAYER-TO-LAYER FLOW

# ============================================================

### Example: A payment approval workflow

```
User → UME-OS → UME-SDO → UME-MODEL → UME-SDO → UME-BASE → UME-SDO → UME-OS
```

Detailed ASCII sequence:

```
UME-OS: POST /tasks (payment)
     │
     ▼
UME-SDO: policy_eval(FIN-014)
     │
     ▼
UME-MODEL: return policy rules
     │
     ▼
UME-SDO: verdict=DEFER → create approval task → audit write
     │
     ▼
UME-OS: show approval task to approver
     │
     ▼
User approves → UME-OS → UME-SDO
     │
     ▼
UME-SDO: re-check policy → ALLOW
     │
     ▼
UME-SDO → UME-BASE: alloc_resource(payment_gateway)
     │
     ▼
UME-BASE: execute payment
     │
     ▼
UME-SDO: append final audit entry
     │
     ▼
UME-OS: status update
```

Everything goes through UME-SDO for authority, policy and audit.

---

# ============================================================

# 6. COMPLETE ASCII SUPER-DIAGRAM (FULL PLATFORM)

# ============================================================

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                                 UME-PLATFORM                                │
│                     General-Purpose Organization Operating System           │
├─────────────────────────────────────────────────────────────────────────────┤
│  UME-MODEL: Organization Model (Ontology, Policy, Structure, Schema, KG)    │
│                                                                             │
│  UME-SDO: Organization Kernel (Policy Engine, Scheduler, Workflow, Audit,   │
│            Plugin ABI, Agents, Event Bus, Namespace, Resources, ODDS)       │
│                                                                             │
│  UME-OS: Org OS + Apps (Finance, HR, CRM, PMO, Ops, Knowledge, Dashboards)  │
│                                                                             │
│  UME-BASE: Physical Infra + Devices + Storage + Network + ODDS             │
└─────────────────────────────────────────────────────────────────────────────┘
```

Or with explicit flow:

```
UME-OS  →  UME-SDO  →  UME-BASE
   ▲          │           ▲
   │          ▼           │
   └─────── UME-MODEL ◀───┘
```

---

# ============================================================

# 7. PRINCIPLE: GENERAL-PURPOSE ORGANIZATION OS

# ============================================================

The entire design enforces the central principle:

### **UME-Platform is a general-purpose operating system for organizations.**

UME-SDO is the kernel.
UME-MODEL is the definition layer.
UME-OS is the userland.
UME-BASE is the hardware.

Everything flows through the kernel.
Every organization can be represented.
Every workflow can be encoded.
Every policy is enforced.
Every device can be controlled.
Every action is auditable.
Every agent is governed.

This is now the **complete, canonical UME-Platform architecture**.

---

# If you want next:

**(choose one or more)**

1. Full platform ISO-style specification (long-form).
2. Full developer reference for all subsystems.
3. All ASCII architecture diagrams rendered at high detail.
4. Deep-dive for each component (UME-MODEL, UME-OS, UME-SDO, UME-BASE).
5. Example complete organization implementation using the platform.
6. Full SDoc (System Design Document) package.

Say **1, 2, 3, 4, 5, 6**, or “y continue”.
Understood — I will now **extend and finalize the complete UME-Platform architecture** so that it explicitly guarantees that:

### **The UME-Platform supports any firm / organization / business model in a fully plug-and-play, extensible, programmable, scalable manner, where users build the model of their organization in UME-MODEL, and the UME-Platform (via UME-SDO) governs, manages, administers, configures and maintains the entire organization automatically.**

This principle will be written directly into the architecture.
Below is the **canonical expansion**, fully aligned with the four-part platform structure, ending with the *Unified Declarative Organization Model → Runtime Execution* cycle.

---

# ============================================================

# UME-PLATFORM: GENERAL-PURPOSE ORGANIZATION OPERATING SYSTEM

## (WITH USER-DEFINED ORGANIZATION MODELS)

# ============================================================

```
BUILD ANY ORGANIZATION MODEL → PLATFORM RUNS THE ORGANIZATION
```

The UME-Platform turns any organization into a **software-defined organization** by shifting the logic of how an organization works into a model (UME-MODEL) that the kernel (UME-SDO) executes.

---

# ============================================================

# 0. FOUNDATIONAL PRINCIPLE (ADDED TO ARCHITECTURE)

# ============================================================

### **The UME-Platform supports *any* organizational form, structure, or business model.**

Including:

* corporations, startups, co-ops, DAOs
* government agencies, NGOs, non-profits
* research labs, universities, teams, coalitions
* multi-entity holding structures
* multi-country, multi-jurisdiction operations
* multi-stakeholder, multi-ownership models
* hybrid human–AI organizations
* CPS/IoT-heavy operational organizations
* distributed gig-style or collective models

### How?

By making **UME-MODEL modular, declarative, programmable and extensible** and making **UME-SDO interpret and execute that model**.

So users can:

```
1. Build a model of their organization.
2. Upload or declare it into UME-MODEL.
3. UME-SDO turns that model into live coordination, governance,
   policy, scheduling, workflows, provisioning, security and operations.
```

This is what makes the UME-Platform a **general-purpose organization OS**.

---

# ============================================================

# 1. UME-MODEL EXTENDED SPEC

## “Build/program the model of your organization”

# ============================================================

UME-MODEL becomes a **declarative programming layer** for organizations.

### UME-MODEL supports:

* **Ontology / Vocabulary Mechanics**
  Users define new concepts, entities, relationships.

* **Entity Types & Object Models**
  Users define:*
  `Firm`, `Team`, `Fund`, `Order`, `Contract`, `Product`, `Site`, `Sensor`,
  or any custom object type their business uses.

* **Policies as Code (Full DSL)**

  * authority rules
  * financial rules
  * compliance & risk
  * behavioral constraints
  * agent operation permissions
  * device safety
  * residency & data localization

* **Workflows / Process definitions**
  Users define arbitrary processes: onboarding, payments, shipping, R&D, EHS, etc.

* **Role & Capability System**
  Create custom roles, capabilities, and constraints.

* **Graph Model (relationships)**
  e.g.,
  teams → departments → divisions
  products → contracts → customers
  sites → devices → sensors

### EXTENSIBILITY

* add new schema types
* add new policy modules
* add new workflow primitives
* import industry ontologies (healthcare, finance, logistics, etc.)
* import cross-organization templates

### Users can **build their entire business as a model**.

---

# ============================================================

# 2. UME-SDO EXTENDED SPEC

## “The model you build becomes the live kernel of your firm”

# ============================================================

UME-SDO consumes everything in UME-MODEL and **turns it into operational reality.**

This is the platform’s central innovation.

### UME-SDO performs:

**A. Model Execution**

* UME-SDO loads the user-defined UME-MODEL.
* It interprets and enforces all policy, workflow, topology, roles, constraints.

**B. Model-Driven Governance**
Every action, task, workflow, resource, approval, agent, device operation
is interpreted via the model.

**C. Model-Driven Configuration**
When the user updates the model:

```
UME-MODEL → “publish”
UME-SDO detects → re-evaluates → reconfigures the runtime
```

**D. Model-Driven Provisioning**

* If the model says “This business requires N edge nodes per site” → UME-SDO provisions.
* If the model says “All payment systems require X approvals” → UME-SDO enforces.
* If the model says “This org unit can only compute in EU region” → kernel enforces residency.
* If the model adds a new workflow → UME-SDO starts orchestrating it.

**E. Model-Defined AI Behavior**
Agents (UICE/Jini):

* permissions come from the model
* allowed tasks come from the model
* trust frameworks defined in the model
* interpretability rules set by the model

**F. Model-Defined Devices**
Device safety policies
Device ownership relationships
Field / plant / edge control logic
→ All from UME-MODEL into ODDS in UME-BASE via UME-SDO

**G. Model-Driven Identity & Roles**
User-defined or industry-specific roles:

* partner / director / operator / auditor
* pilot / mechanic / dispatcher
* trader / risk officer
* engineer / reviewer

→ All executed by UME-SDO kernel via OrgCPU scheduling and permissions.

---

# ============================================================

# 3. UME-OS EXTENDED SPEC

## “Applications that adapt themselves to the user model”

# ============================================================

UME-OS is not hard-coded to a single business model.
It **adapts dynamically** to the user’s UME-MODEL.

### UME-OS apps:

* read the model
* generate UI based on model-defined entities
* render tasks, workflows, reports based on schemas
* show dashboards based on model definitions
* adapt roles and views dynamically

**You can define a brand new business domain and UME-OS will generate:**

* menus
* forms
* tables
* workflows
* dashboards
* processes

### Example:

If a business defines in UME-MODEL:

```
Entity: "Flight"
Fields: tail_number, pilot, gate, fuel_load
Workflow: Pre-flight Check (requires EHS approval)
```

UME-OS will automatically:

* add a UI for “Flights”
* generate CRUD forms
* generate workflow screens
* generate approval screens
* integrate OrgCPU scheduling (pilot must approve)

---

# ============================================================

# 4. UME-BASE EXTENDED SPEC

## “The physical layer also becomes model-driven”

# ============================================================

### UME-BASE provisions infrastructure **based on the user’s model**.

If the model says:

```
Org Unit A → requires 3 compute nodes
Org Unit B → requires a GPU pool
Site C → must have ODDS device controllers
```

UME-SDO instructs UME-BASE to provision exactly that.

### Model-driven device layer:

Users define in UME-MODEL:

* devices
* actuators
* sensors
* safety policies
* sampling rates
* ownership and authority

UME-SDO applies these rules at runtime using ODDS.

---

# ============================================================

# 5. PLUG-AND-PLAY ORGANIZATION TEMPLATES

# ============================================================

UME-Platform supports **plug-and-play business models**:

### Examples:

* Retail organization template
* Manufacturing template
* Logistics template
* Consulting firm template
* Venture fund template
* Hospital model
* Airline/aviation operations model
* Construction operational model
* R&D lab model
* Subscription SaaS company model

Users can load, modify, extend or mix them.

---

# ============================================================

# 6. USER-DEFINED ORGANIZATION PROGRAMMING

# ============================================================

You can treat UME-MODEL as an **organization programming language**.

### A user can define:

```
entity Product { id, sku, margin, lifecycle_stage }

policy FinanceLimits {
  if amount > 50000 require approval by ["FinanceDirector"];
}

workflow ShipOrder {
  step validate_order;
  step pick_items;
  step pack;
  step ship requires capability ["LogisticsOperator"];
}
```

Then UME-SDO **runs the business**.

---

# ============================================================

# 7. COMPLETE ASCII SUPER-DIAGRAM (FINAL)

# ============================================================

```
                              ┌──────────────────────────────────┐
                              │            Users                 │
                              │        (build model)             │
                              └───────────────────▲──────────────┘
                                                  │
                                                  │ build/program
                                                  │
                     ┌────────────────────────────┼─────────────────────────────┐
                     │                            │                             │
                     ▼                            │                             ▼
          ┌─────────────────────┐                 │                 ┌──────────────────────┐
          │      UME-MODEL      │◀────────────────┘                 │       UME-OS         │
          │ Declarative Org DSL │           model-driven             │ Org Apps + UI + OS   │
          │ Ontology + Policies │──────────────────────────────────▶│ auto-generated views  │
          │ Workflows + Roles   │       tasks/workflows/events      │ from model            │
          └───────────▲─────────┘                                   └────────────▲─────────┘
                      │                                                         │
                      │                                                         │
                      │  policy, authority, workflow logic                      │ UI actions
                      │                                                         │
                      ▼                                                         ▼
          ┌──────────────────────────────────────────────────────────────────────────────┐
          │                                     UME-SDO                                   │
          │                               Organization Kernel                             │
          │  Policy Runtime │ OrgCPU Scheduler │ Event Bus │ Workflow Engine │ Audit Ledger│
          │  Plugin ABI     │ Agent Runtime   │ Namespace │ Resource Control │ ODDS Gateway│
          │  MODEL EXECUTION: interprets entire org model as executable governance         │
          └───────────────▲───────────────────────────────────────────────────────────────┘
                          │
                          │ provisioning / device commands
                          │
     ┌────────────────────▼──────────────────┐
     │               UME-BASE                │
     │ Physical Infra | Compute | Storage   │
     │ Network | Edge | Devices | ODDS      │
     │ Model-driven provisioning + telemetry │
     └───────────────────────────────────────┘
```

---

# ============================================================

# 8. FINAL STATEMENT

## Explanatory Guarantee (Added to Architecture)

# ============================================================

### ✔ The UME-Platform is formally defined as:

> **A general-purpose, plug-and-play, model-driven organization operating system that can represent, configure, govern, automate and operate *any* firm, business, or organization — purely from a user-defined model.**

Users build the model.
UME-MODEL stores it.
UME-SDO enforces and runs it.
UME-OS interacts with it.
UME-BASE hosts it.

This is the final and complete architectural principle.

---

If you want, I can now produce:

1. **The complete UME-Platform ISO/IEC-style specification**
2. **The UME-MODEL DSL specification**
3. **The UME-SDO kernel formal semantics**
4. **The “Organization Programming” guide**
5. **A full SDoc (System Design Document)**
6. **ASCII architecture mega-chapter combining everything**

Say **1, 2, 3, 4, 5, or 6**.
# UME-MODEL DSL SPECIFICATION &

# “Organization Programming” GUIDE

**(ASCII-friendly • Declarative • Executable • Model → Runtime)**

This message contains two joined deliverables you requested:

1. **UME-MODEL DSL specification** — formal, ASCII-friendly grammar, primitives, types, policy constructs, workflow syntax, model versioning, validation rules, and mapping to UME-SDO kernel primitives.
2. **Organization Programming guide** — practical how-to: authoring patterns, templates, examples (retail, consulting, fund, CPS plant), testing, simulation, publishing, rollout, and operational best practices.

Everything is written so you can paste into docs, editors, or use as the basis for a parser/authoring tool.

---

# 1. OVERVIEW — GOAL & PRINCIPLES

Goal: provide a compact, human-readable, machine-parsable DSL (UME-MODEL DSL) that lets users *declare* the structure, behavior, policies and runtime requirements of an organization. UME-SDO consumes these models and executes them.

Design principles:

* Declarative: describe *what* the org is, not *how* to run it.
* Composable: small reusable modules (templates).
* Typed: explicit schemas for safety.
* Auditable: every model change versioned & signed.
* Policy-first: policy primitives are first-class and enforceable by UME-SDO.
* Extensible: users add new entity types, constraints, and plugins.

Notation: DSL examples use plain ASCII blocks. Square brackets `[]` for lists, braces `{}` for inline JSON where helpful. Keywords in ALLCAPS for readability.

---

# 2. TOP-LEVEL STRUCTURE (MODULES)

A UME-MODEL document is composed of named sections (modules). Minimal required top-level modules:

```
module <name> {
  meta { ... }             # metadata: version, author, description
  imports [ ... ]          # import templates or other modules
  entities { ... }         # entity type declarations
  instances { ... }        # concrete instances (optional)
  workflows { ... }        # process definitions
  policies { ... }         # policy-as-code blocks
  agents { ... }           # agent definitions (UICE/Jini)
  devices { ... }          # device & twin schemas
  views { ... }            # UI / report hints (optional)
}
```

Example header:

```
module acme-retail-v1 {
  meta {
    version: "2025-12-05-v1"
    author: "alice@acme"
    description: "Retail store model - pilot"
  }
  imports [ retail-core, finance-common ]
  ...
}
```

---

# 3. BASIC TYPES & SCHEMA LANGUAGE

UME-MODEL DSL includes primitive types and a small schema definition language for declaring typed entity fields.

Primitives: `string`, `int`, `float`, `bool`, `date`, `timestamp`, `enum{a,b}`, `money{currency}`.

Schema syntax:

```
entity Product {
  id: string          # primary
  sku: string
  price: money{USD}
  margin_pct: float
  lifecycle: enum{design,prod,retire}
}
```

Field modifiers:

* `?` optional (e.g., `description?: string`)
* `[]` list (e.g., `tags: string[]`)
* `ref<EntityType>` foreign key (e.g., `owner: ref[Entity]`)
* `computed(expr)` derived field (evaluated by UME-SDO)

Example computed:

```
entity Invoice {
  id: string
  amount: money{USD}
  tax: money{USD} = computed("amount * tax_rate")
}
```

(Computed expressions are in a safe expression language; UME-SDO evaluates under policy.)

---

# 4. ENTITY DECLARATION & INSTANCES

Entities define types. Instances are optional concrete records (useful for bootstrapping or examples).

Example entity + instance:

```
entity Team {
  id: string
  name: string
  members: ref[Principal][]   # list of principals (People or Agents)
  budget_usd: int
}

instance Team "eng-core" {
  id: "team:eng-core"
  name: "Engineering Core"
  members: ["principal:alice","principal:bob"]
  budget_usd: 500000
}
```

IDs are canonical URIs: `entitytype:localid` (e.g., `role:partner`, `device:site-1-ctl`).

---

# 5. ROLE, PRINCIPAL & ORGCPU TYPES

Role / Principal primitives:

```
entity Role {
  id: string
  name: string
  capabilities: string[]   # capability labels mapped to kernel caps
}

entity Principal {
  id: string
  kind: enum{human,agent,service,device}
  identities: string[]     # auth identities, e.g., oidc, certs
  roles: ref[Role][]
  attributes: map<string,string>
}
```

OrgCPU mapping (UMESDO):

* Principals map to OrgCPU instances (registered by UME-SDO).
* Scheduler uses `capabilities`, `quota` and `affinity` derived from Principals/Role.

Quota example:

```
entity Principal "orgcpu:ai-strategist" {
  id: "orgcpu:ai-strategist"
  kind: agent
  roles: ["role:strategist"]
  attributes: { model_ref: "model://jini/strategist/v3" }
}
```

---

# 6. POLICY-AS-CODE (UME-LANG) — SYNTAX & SEMANTICS

Policies are first-class and used by UME-SDO `Policy.EVAL`. Provide a concise DSL (UME-Lang) with clear semantics.

Basic policy block:

```
policy FIN-014 {
  meta {
    description: "Price approval for payments over threshold."
    version: "2025-12-05-v1"
  }

  params {
    threshold: money{USD} = 50000
    approver_role: ref[Role] = "role:partner"
  }

  when (action == "create_payment") {
    if (payload.payment.amount > params.threshold) {
      effect: DEFER
      obligations: [
        { type: "require_approval", roles: [params.approver_role] }
      ]
      reason: "Payments above threshold require partner approval."
    } else {
      effect: ALLOW
    }
  }
}
```

Semantics:

* `when (predicate)` matches contexts passed by UME-SDO (actor, action, model_refs, payload).
* `effect` ∈ {`ALLOW`, `DENY`, `DEFER`}.
* `obligations` are actions kernel must create (approval tasks, evidence collection).
* Policies can `emit` audit evidence entries.

Policy composition:

* `policy` supports `import <policy-id> as base` and overrides.
* `policy` supports `simulation { ... }` to specify mocked outcomes for tests.

Policy evaluation:

* Deterministic, pure function of policy, model snapshot id, and context.
* Must be idempotent and side-effect free; obligations returned to UME-SDO for execution.

---

# 7. WORKFLOW / PROCESS LANGUAGE (BPMN-LITE)

Lightweight steps, conditional flows, parallelism, human tasks and agent tasks.

Syntax:

```
workflow onboarding_v1 {
  start -> s1
  s1: task "validate_documents" {
    type: "auto"
    action: "validate_documents"
    on_success -> s2
    on_fail -> end_fail
  }
  s2: human_task "approve_onboard" {
    roles: ["role:compliance"]
    timeout: "72h"
  }
  s2 -> s3
  s3: task "provision_resources" {
    type: "auto"
    action: "provision_resources"
  }
  s3 -> end_success
}
```

Step types:

* `auto` — automated step executed by UME-SDO or agent.
* `human_task` — creates a task assigned to OrgCPU(s) with a UI in UME-OS.
* `parallel` — branches executed concurrently.
* `timer` — schedule-based triggers.
* `event` — subscribes to event topics.

Runtime semantics:

* Workflow manifests compiled by UME-SDO to orchestrator DAGs.
* Each step includes `policy_refs` to be evaluated on entry.

---

# 8. AGENTS (UICE/JINI) & CAPABILITIES

Agent definition:

```
agent jini-strategist {
  id: "agent:jini-strategist:v3"
  model_ref: "model://jini/strategist/v3"
  capabilities: ["simulate_strategy","suggest_okrs"]
  required_permissions: ["read_model","start_sim"]
  cost_profile: { cpu_ms_per_invocation: 200, token_budget: 1000 }
}
```

Agent semantics:

* Agents run under UME-SDO control; every invocation is audited.
* Agent manifests are versioned in UME-MODEL.
* Agent outputs produce `agent_decision` artifacts referenced by audit entries.

---

# 9. DEVICES & DIGITAL TWINS

Device schema:

```
device site-1-controller {
  id: "device:site-1-ctl"
  device_type: "cps-controller"
  owner: "entity:acme"
  capabilities: ["telemetry","actuate"]
  conn: { proto: "mqtt", endpoint: "edge://10.0.1.2:9000" }
  twin_schema: "twin://site-controller-schema-v1"
  safety_policies: ["policy://SAFETY-01"]
}
```

Digital twin:

* Twin schemas live in UME-MODEL; UME-SDO can instantiate twin runtime objects and map telemetry to modeled properties.
* Twin simulation hooks allow UME-SDO to perform planning & "dry-run" before device commands.

---

# 10. VIEWS, FORMS & UI HINTS (UME-OS generation)

Model authors can add UI hints that UME-OS uses to generate UIs:

```
view ProductForm for Product {
  layout: [
    [ "sku", "price" ],
    [ "margin_pct", "lifecycle" ],
    [ "description" ]
  ]
  validators {
    price: "required, >0"
  }
}
```

UME-OS respects these hints but enforces policies via UME-SDO.

---

# 11. MODULES, TEMPLATES & PLUG-AND-PLAY

Define reusable templates:

```
template retail-store {
  imports [ retail-core ]
  entities {
    Store { id, name, location, cash_registers: int }
  }
  workflows {
    pos-refund: ...
  }
  policies {
    SAFETY-01: ...
  }
}
```

Users can `import` templates and `override` bits.

---

# 12. MODEL VERSIONING, MIGRATION, & VALIDATION

* Each module gets `meta.version`. Publishing a model creates an immutable snapshot `model://<module>@<version>`.
* UME-SDO always reads a specific snapshot for deterministic policy eval and audit binding.
* Model publish sequence:

  1. `validate` (static validation and schema checks)
  2. `simulate` (UME-SDO / UICE simulation, optional)
  3. `publish` (create snapshot + signed manifest)
  4. `deploy` (optional: UME-SDO applies changes to runtime)
* Migration: include `migrations { from:"v1", to:"v2", script: "..." }` in module.

Validation rules:

* Type checks, required fields, circular refs detection, policy syntax check, workflow reachability.
* `POST /model/validate` returns structured `issues` list.

---

# 13. TESTING & SIMULATION (MODEL SANDBOX)

UME-MODEL supports built-in test cases and simulation harness:

```
test case refund-over-threshold {
  inputs: { action:"create_payment", amount:60000, actor:"principal:alice" }
  expected: { policy_verdict: "DEFER", obligations: ["require_approval"] }
}
```

Simulation:

* UME-SDO supports `policy_simulate` and `workflow_simulate` to run scenarios on a snapshot without committing side effects.
* Use simulations to detect policy conflicts, approvals storms, or resource pressure.

---

# 14. LIFECYCLE: AUTHOR → PUBLISH → RUN → OBSERVE → UPDATE

1. **Author**: create modules locally or in UI.
2. **Validate**: run static checks.
3. **Simulate**: run scenarios; optional agent-in-the-loop sim.
4. **Publish**: snapshot the model in UME-MODEL registry (signed).
5. **Deploy**: UME-SDO pulls snapshot, runs `policy_simulate`, then `apply` (creates approvals to human owners if needed).
6. **Operate**: runtime events flow via UME-SDO; UME-OS UIs show state.
7. **Observe**: telemetry, KPI, OKR update loops feed back to modelers.
8. **Iterate**: edit model → repeat.

---

# 15. MAPPING: MODEL CONSTRUCT → UME-SDO PRIMITIVE (SUMMARY)

```
model entity              → UME-SDO: model artifact (GetModelArtifact)
model policy              → UME-SDO: Policy.EVAL
workflow step             → UME-SDO: start_workflow / schedule_task
human_task                → UME-SDO: create task & schedule OrgCPU
agent manifest            → UME-SDO: register_agent + invoke_agent
device manifest           → UME-SDO: register device in ODDS
resource spec             → UME-SDO: alloc_resource / release_resource
approval obligation       → UME-SDO: create approval task + await completion
simulation / test case    → UME-SDO: policy_simulate / workflow_simulate
UI view hints             → UME-OS: render forms; UME-SDO enforces policies
```

---

# 16. EXAMPLES — Small, Practical Models

## 16.1 Consulting Firm (compact)

```
module consulto-v1 {
  meta { version: "1.0" author: "acme-consult" }
  imports [ finance-common, hr-core ]

  entity Engagement {
    id: string
    client: ref[Entity]
    value_usd: money{USD}
    margin_target_pct: float
    delivery_team: ref[Team]
  }

  policy FIN-ENG-APPROVAL {
    when (action == "create_engagement") {
      if (payload.value_usd > 100000) {
        effect: DEFER
        obligations: [{ type: "require_approval", roles: ["role:partner"] }]
      } else effect: ALLOW
    }
  }

  workflow engagement_onboard {
    start -> w1
    w1: human_task "partner_signoff" { roles: ["role:partner"] }
    w1 -> w2
    w2: task "provision_team" { type: "auto", action: "provision_team" }
  }
}
```

## 16.2 Retail Store — Refund flow

```
module retail-basic {
  entity Refund {
    id: string
    order_id: ref[Order]
    amount: money{USD}
    reason: string
  }

  policy REFUND-THRESH {
    params { threshold: money{USD} = 1000 }
    when (action == "create_refund") {
      if (payload.amount > params.threshold) {
        effect: DEFER
        obligations: [{type:"require_approval", roles:["role:store-manager"]}]
      } else effect: ALLOW
    }
  }
}
```

## 16.3 CPS Plant (device + twin + safety)

```
module plant-core {
  device site-controller { ... safety_policies: ["policy://EHS-001"] }
  policy EHS-001 { when(action=="actuate_device") { if(!actor.has_cert("EHS")) effect: DENY } }
  workflow emergency_shutdown {
    start -> s1
    s1: event "sensor_overheat" -> s2
    s2: task "shutdown_line" { type: "auto", action: "cmd_shutdown", policy_refs:["policy://EHS-001"] }
  }
}
```

---

# 17. BEST PRACTICES & PATTERNS

* **Start small**: model entities & policies for a single process first (e.g., invoicing).
* **Use templates**: import established domain templates to bootstrap.
* **Separate policy from workflow**: keep authorization policies in `policies` module and workflow in `workflows`.
* **Version everything**: every published snapshot must have semantic versioning.
* **Use tests & simulation**: run policy and workflow simulations before production publish.
* **Model for failure**: include timeouts, retries, compensations in workflows.
* **Least privilege**: model capability labels and attach them to roles; UME-SDO honors capability enforcement.
* **Data residency**: encode `residency` attributes in entities and policies; UME-SDO enforces provisioning constraints.

---

# 18. TOOLING & UX (IDE / CLI / API)

Recommended toolset:

* **CLI**: `ume model validate`, `ume model simulate`, `ume model publish`, `ume model deploy --snapshot=...`
* **IDE plugin**: syntax highlighting, linting, inline policy eval, schema autocomplete.
* **Change review**: Git-like diffs + model change approval via UME-OS UI; model changes recorded as PRs with simulation results.
* **Repository layout**: `models/`, `templates/`, `policies/`, `agents/`, `devices/`, `tests/`.

---

# 19. SECURITY & COMPLIANCE (MODEL-LEVEL)

* Model publishing requires signatures from authorized principals (owner role).
* Policy changes that affect critical systems require multi-party approval flows (modeled).
* Models can declare sensitivity levels for fields; UME-SDO ensures data residency and masked views.

---

# 20. OPERATIONAL FLOW (AUTHOR → RUNTIME) — EXAMPLE

1. Author `consulto-v1` locally.
2. Run `ume model validate consulto-v1`.
3. Run `ume model simulate consulto-v1 --scenario=create_engagement_high_value`.
4. If simulation shows `DEFER` due to FIN-ENG-APPROVAL, update owners.
5. Publish `ume model publish consulto-v1`. Snapshot `model://consulto-v1@2025-12-05-v1`.
6. Deploy: `ume sdo apply model://consulto-v1@...`. UME-SDO validates and enacts policies — creates approval task in UME-OS if necessary.
7. Observe: UME-OS shows pending approval; once approved UME-SDO provisions resources on UME-BASE and appends audit entries.

---

# 21. FAILURE MODELS & RECOVERY

* Model validation prevents class of runtime errors.
* UME-SDO has `rollback` hooks: deploy in two-phase — `staged` → `promote`.
* Simulation identifies policy conflicts; run `ume sdo policy_simulate` for high-risk changes.
* Audit ledger + model snapshot ensures point-in-time reproducibility for incident forensics.

---

# 22. EXTENDING DSL (ADVANCED)

* Add domain DSL libraries: `healthcare-dsl`, `finance-dsl`, `logistics-dsl`.
* Allow typed functions (safe subset) for computed fields; disallow arbitrary Turing complete code in policies.
* Support `foreign` sections for vendor adapters (map to UME-BASE ODDS adapters).
* Provide a `policy-linter` to check for contradictory rules, unreachable obligations.

---

# 23. COMPOSITION & MULTI-ENTITY MODELS

* Models may declare `subsidiary` entities and cross-entity flows.
* Multi-jurisdiction: per-entity `legal_jurisdiction` attribute; policies can include jurisdiction checks.
* Multi-tenant operation: UME-MODEL supports tenant scoping and tenant-level templates.

---

# 24. DOCUMENTATION & EXAMPLE PACKS (what I can produce next)

I can immediately produce any of:

* Full machine-parsable JSON Schema for the DSL.
* A reference implementation parser (pseudo code / ANTLR grammar).
* CLI examples and full tutorial (step-by-step) for building a consulting firm model.
* A set of 5 plug-and-play templates: retail, consulting, manufacturing CPS, fund, SaaS.
* UME-OS auto-UI generation algorithm blueprint.

Say which one (or multiple) and I’ll generate them now.

---

# 25. CLOSING — WHY THIS WORKS

* The DSL makes the organization **explicit** and **executable**.
* UME-SDO enforces the model, so the platform reliably governs every configured behavior.
* The pattern is general: define model → validate → simulate → publish → runtime executes → observe & refine.

If you want a concrete next step, say:

* “Generate the ANTLR grammar for UME-MODEL DSL”
* “Produce the JSON Schema and sample CLI”
* “Create the consulting firm tutorial (step-by-step)”
* “Produce the 5 plug-and-play templates”

Pick one and I’ll produce it immediately.
Awesome — I’ll deliver all four outputs now, in one complete package. Everything is ASCII-friendly and ready to paste into files, run through tools, or use as the basis for a real parser, CLI, and onboarding tutorial.

Contents (in order):

1. ANTLR v4 grammar for **UME-MODEL DSL**
2. JSON Schema (machine-parsable) for top-level module + samples
3. Sample CLI (commands, flags, example runs) — `ume` CLI prototype
4. Consulting-firm tutorial (step-by-step): author → validate → simulate → publish → deploy → operate
5. Five plug-and-play templates (module files): Retail, Consulting (full tutorial model), Manufacturing CPS, Venture Fund, SaaS

---

# 1) ANTLR v4 Grammar — `UmeModel.g4`

Save as `UmeModel.g4`. This is a practical, implementation-ready ANTLR v4 grammar (parser + lexer). It intentionally keeps expressions and policy conditions in a restricted expression language (safe subset). Comments included.

```
grammar UmeModel;

// -------------------------------
// Parser rules (top-level)
// -------------------------------
moduleDecl
    : 'module' IDENT '{' moduleBody '}' EOF
    ;

moduleBody
    : (metaDecl | importDecl | entitiesDecl | instancesDecl | policiesDecl
       | workflowsDecl | agentsDecl | devicesDecl | viewsDecl)* 
    ;

metaDecl
    : 'meta' '{' metaKV* '}'
    ;

metaKV
    : IDENT ':' value
    ;

importDecl
    : 'imports' '[' importList? ']'
    ;

importList
    : IDENT (',' IDENT)*
    ;

entitiesDecl
    : 'entities' '{' (entityDecl)* '}'
    ;

entityDecl
    : 'entity' IDENT '{' fieldDecl* '}'
    ;

fieldDecl
    : IDENT (':' typeExpr) ( '=' expr )? ( '#' ~[\r\n]* )?
    ;

typeExpr
    : baseType
    | baseType '?'                     # optionalType
    | baseType '[]'                    # listType
    | 'ref' '[' IDENT ']'              # refType
    ;

baseType
    : 'string' | 'int' | 'float' | 'bool' | 'date' | 'timestamp' | moneyType | enumType | 'map' '<' 'string' ',' 'string' '>'
    ;

moneyType
    : 'money' '{' IDENT '}'
    ;

enumType
    : 'enum' '{' IDENT (',' IDENT)* '}'
    ;

instancesDecl
    : 'instances' '{' (instanceDecl)* '}'
    ;

instanceDecl
    : 'instance' IDENT STRING '{' instanceKV* '}'
    ;

instanceKV
    : IDENT ':' value
    ;

policiesDecl
    : 'policies' '{' (policyDecl)* '}'
    ;

policyDecl
    : 'policy' IDENT '{' policyBody '}'
    ;

policyBody
    : metaDecl? paramsDecl? whenBlock+
    ;

paramsDecl
    : 'params' '{' (paramDecl)* '}'
    ;

paramDecl
    : IDENT ':' typeExpr ('=' value)? 
    ;

whenBlock
    : 'when' '(' expr ')' '{' (ifBlock | elseIfBlock | elseBlock)* '}'
    ;

ifBlock
    : 'if' '(' expr ')' '{' policyAction* '}'
    ;

elseIfBlock
    : 'else' 'if' '(' expr ')' '{' policyAction* '}'
    ;

elseBlock
    : 'else' '{' policyAction* '}'
    ;

policyAction
    : 'effect' ':' effectValue
    | 'obligations' ':' obligationList
    | 'reason' ':' STRING
    | 'emit' ':' STRING
    ;

effectValue
    : 'ALLOW' | 'DENY' | 'DEFER'
    ;

obligationList
    : '[' obligation (',' obligation)* ']'
    ;

obligation
    : '{' (obligationKV (',' obligationKV)*)? '}'
    ;

obligationKV
    : IDENT ':' obligationValue
    ;

obligationValue
    : STRING | '[' STRING (',' STRING)* ']' 
    ;

workflowsDecl
    : 'workflows' '{' (workflowDecl)* '}'
    ;

workflowDecl
    : 'workflow' IDENT '{' workflowBody '}'
    ;

workflowBody
    : (workflowStart | workflowStep | workflowFlow)*
    ;

workflowStart
    : 'start' '->' IDENT
    ;

workflowStep
    : IDENT ':' stepType STRING '{' stepBody '}'
    ;

stepType
    : 'task' | 'human_task' | 'parallel' | 'timer' | 'event'
    ;

stepBody
    : (stepKV)*
    ;

stepKV
    : IDENT ':' value
    ;

workflowFlow
    : IDENT '->' IDENT
    ;

agentsDecl
    : 'agents' '{' (agentDecl)* '}'
    ;

agentDecl
    : 'agent' IDENT '{' agentBody '}'
    ;

agentBody
    : (agentKV)*
    ;

agentKV
    : IDENT ':' value
    ;

devicesDecl
    : 'devices' '{' (deviceDecl)* '}'
    ;

deviceDecl
    : 'device' IDENT '{' deviceBody '}'
    ;

deviceBody
    : (deviceKV)*
    ;

viewsDecl
    : 'views' '{' (viewDecl)* '}'
    ;

viewDecl
    : 'view' IDENT 'for' IDENT '{' viewBody '}'
    ;

viewBody
    : (viewKV)*
    ;

value
    : STRING
    | NUMBER
    | mapLiteral
    | arrayLiteral
    | 'true' | 'false'
    ;

mapLiteral
    : '{' (mapKV (',' mapKV)*)? '}'
    ;

mapKV
    : STRING ':' value
    ;

arrayLiteral
    : '[' (value (',' value)*)? ']'
    ;

// -------------------------------
// Expressions (restricted, safe)
// -------------------------------
expr
    : expr '||' expr
    | expr '&&' expr
    | expr '==' expr
    | expr '!=' expr
    | expr '<' expr
    | expr '<=' expr
    | expr '>' expr
    | expr '>=' expr
    | expr '+' expr
    | expr '-' expr
    | expr '*' expr
    | expr '/' expr
    | '(' expr ')'
    | '-' expr
    | IDENT ('.' IDENT)*           // identifier or dotted ref
    | STRING
    | NUMBER
    ;

STRING : '"' (~["\\] | '\\' . )* '"' ;
NUMBER : '-'? [0-9]+ ('.' [0-9]+)? ;
IDENT  : [a-zA-Z_] [a-zA-Z0-9_:-]* ;
WS     : [ \t\r\n]+ -> skip ;
COMMENT: '#' ~[\r\n]* -> skip ;
```

Notes:

* Expression language is intentionally limited (no function calls) to keep policy evaluation safe and deterministic. You may later add safe functions (e.g., `in()`, `contains()`) as builtins.
* Lexer tokens allow `:` and `-` in identifiers for canonical URIs like `role:partner`.

---

# 2) JSON Schema — `ume-module.schema.json`

This JSON Schema validates the top-level module structure (simplified but comprehensive). Save as `ume-module.schema.json`.

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "UME Module",
  "type": "object",
  "required": ["module"],
  "properties": {
    "module": {
      "type": "object",
      "required": ["name", "meta"],
      "properties": {
        "name": { "type": "string" },
        "meta": {
          "type": "object",
          "required": ["version", "author"],
          "properties": {
            "version": { "type": "string" },
            "author": { "type": "string" },
            "description": { "type": "string" }
          }
        },
        "imports": {
          "type": "array",
          "items": { "type": "string" }
        },
        "entities": {
          "type": "array",
          "items": {
            "type": "object",
            "required": ["name", "fields"],
            "properties": {
              "name": { "type": "string" },
              "fields": {
                "type": "array",
                "items": {
                  "type": "object",
                  "required": ["name", "type"],
                  "properties": {
                    "name": { "type": "string" },
                    "type": { "type": "string" },
                    "optional": { "type": "boolean" },
                    "default": {}
                  }
                }
              }
            }
          }
        },
        "instances": {
          "type": "array",
          "items": {
            "type": "object",
            "required": ["type", "id"],
            "properties": {
              "type": { "type": "string" },
              "id": { "type": "string" },
              "values": { "type": "object" }
            }
          }
        },
        "policies": {
          "type": "array",
          "items": {
            "type": "object",
            "required": ["id", "when"],
            "properties": {
              "id": { "type": "string" },
              "meta": { "type": "object" },
              "params": { "type": "object" },
              "when": {
                "type": "array",
                "items": {
                  "type": "object",
                  "required": ["condition", "actions"],
                  "properties": {
                    "condition": { "type": "string" },
                    "actions": {
                      "type": "object",
                      "properties": {
                        "effect": { "type": "string", "enum": ["ALLOW", "DENY", "DEFER"] },
                        "obligations": { "type": "array" },
                        "reason": { "type": "string" }
                      }
                    }
                  }
                }
              }
            }
          }
        },
        "workflows": {
          "type": "array",
          "items": {
            "type": "object",
            "required": ["id", "steps"],
            "properties": {
              "id": { "type": "string" },
              "steps": {
                "type": "array",
                "items": {
                  "type": "object",
                  "required": ["id", "type"],
                  "properties": {
                    "id": { "type": "string" },
                    "type": { "type": "string" },
                    "props": { "type": "object" }
                  }
                }
              },
              "flows": {
                "type": "array",
                "items": { "type": "array", "items": { "type": "string" } }
              }
            }
          }
        },
        "agents": {
          "type": "array",
          "items": {
            "type": "object",
            "required": ["id", "model_ref"],
            "properties": {
              "id": { "type": "string" },
              "model_ref": { "type": "string" },
              "capabilities": { "type": "array", "items": { "type": "string" } }
            }
          }
        },
        "devices": {
          "type": "array",
          "items": {
            "type": "object",
            "required": ["id", "device_type"],
            "properties": {
              "id": { "type": "string" },
              "device_type": { "type": "string" },
              "capabilities": { "type": "array", "items": { "type": "string" } },
              "conn": { "type": "object" }
            }
          }
        }
      }
    }
  }
}
```

You can adapt and expand the schema (add constraints, pattern checks) as you implement more tooling.

---

# 3) Sample CLI — `ume` (prototype commands & examples)

This is a compact CLI specification and example runs. You can implement in Go, Rust, or Python. Commands are idempotent where possible.

```
ume model validate <module-file>           # validate DSL file (uses ANTLR parser)
ume model simulate <module-file> --scenario=<name>  # run policy/workflow sim
ume model publish <module-file> --author=<id>       # publish snapshot to registry
ume model list                                # list published snapshots
ume sdo apply model://<module>@<version>      # instruct UME-SDO to apply model
ume sdo policy-simulate model://... --ctx='{"action":"create_payment","amount":50000}'
ume sdo status <operation-id>                 # poll sdo operation
ume sdo audit export --from=1000 --to=1010    # export audit ledger range
ume os create task --title "Pay vendor" --payload-file pay.json
ume base provision --spec infra-spec.json     # simulate provisioning (dev)
```

Example session (step-by-step):

1. Validate a model file

```
$ ume model validate consulto-v1.ume
[OK] consulto-v1.ume: syntax OK, 0 issues.
```

2. Simulate a scenario (policy check)

```
$ ume model simulate consulto-v1.ume --scenario=create_high_value_engagement
[SIM] Running policy FIN-ENG-APPROVAL ... verdict=DEFER, obligations=require_approval[role:partner]
[SIM] Workflow engagement_onboard: yields approval task for role:partner
```

3. Publish model

```
$ ume model publish consulto-v1.ume --author alice@acme
[PUBLISH] model://consulto-v1@2025-12-05-v1
```

4. Apply model to runtime (UME-SDO)

```
$ ume sdo apply model://consulto-v1@2025-12-05-v1
[APPLY] validation ok. simulation ok. staged apply created operation-id: op-20251205-001
[APPLY] Apply requires approval: policy FIN-ENG-APPROVAL => create task task://501234 assigned to role:partner
```

5. Approver completes task in UME-OS UI (or via CLI)

```
$ ume os tasks approve task://501234 --principal partner:john
[OK] task://501234 approved by partner:john
```

6. UME-SDO completes apply and provisions resources

```
[OP] operation op-20251205-001: PROVISIONING -> COMPLETE
[OP] resources provisioned: res://70077
```

CLI: additional flags and behavior:

* `--dry-run` for non-destructive simulate/apply
* `--model-version` to pin a snapshot
* `--output json` for machine consumption
* `--yes` to auto-approve non-critical prompts (for automation)

---

# 4) Consulting-Firm Tutorial — Step-by-Step (practical)

This is a complete, copy-pasteable tutorial using the DSL and CLI above. It assumes the `ume` CLI and UME-SDO dev environment are available. Use the module file `consulto-v1.ume`.

---

## 4.A Create the model file `consulto-v1.ume`

Create `consulto-v1.ume` with:

```
module consulto-v1 {
  meta {
    version: "2025-12-05-v1"
    author: "alice@acme"
    description: "Consulting firm model for pilot"
  }

  imports [ "finance-common", "hr-core" ]

  entities {
    entity Engagement {
      id: string
      client: ref[Entity]
      value_usd: money{USD}
      margin_target_pct: float
      delivery_team: ref[Team]
      start_date: date
      end_date?: date
    }

    entity Team {
      id: string
      name: string
      members: ref[Principal][]
      budget_usd: int
    }
  }

  instances {
    instance Team "team:eng-core" {
      id: "team:eng-core"
      name: "Engineering Core"
      members: ["principal:alice"]
      budget_usd: 500000
    }
  }

  policies {
    policy FIN-ENG-APPROVAL {
      meta { description: "Require partner approval for high-value engagements" }
      params {
        threshold: money{USD} = 100000
        approver_role: ref[Role] = "role:partner"
      }
      when (action == "create_engagement") {
        if (payload.value_usd > params.threshold) {
          effect: DEFER
          obligations: [
            { type: "require_approval", roles: [params.approver_role] }
          ]
          reason: "High value engagements need partner approval."
        } else {
          effect: ALLOW
        }
      }
    }
  }

  workflows {
    workflow engagement_onboard {
      start -> step1
      step1: human_task "partner_signoff" {
        roles: ["role:partner"]
        timeout: "72h"
      }
      step1 -> step2
      step2: task "provision_team" {
        type: "auto"
        action: "provision_team"
      }
      step2 -> end_success
    }
  }

  agents {
    agent jini-strategist {
      id: "agent:jini-strategist:v1"
      model_ref: "model://jini/strategist/v1"
      capabilities: ["simulate_strategy","suggest_staffing"]
      required_permissions: ["read_model"]
    }
  }
}
```

Save and commit to `models/consulto-v1.ume`.

---

## 4.B Validate the model

```
$ ume model validate consulto-v1.ume
[OK] consulto-v1.ume: syntax OK. 0 issues.
```

If issues exist, fix according to linter messages.

---

## 4.C Simulate a high-value creation

```
$ ume model simulate consulto-v1.ume --scenario='{"action":"create_engagement","payload":{"value_usd":150000}}'
[SIM] Policy FIN-ENG-APPROVAL -> verdict=DEFER, obligations=require_approval(role:partner)
[SIM] Workflow engagement_onboard -> step1: partner_signoff (human task)
```

Simulation output confirms policy behavior and required approval.

---

## 4.D Publish the model (snapshot)

```
$ ume model publish consulto-v1.ume --author alice@acme
[PUBLISH] OK -> model://consulto-v1@2025-12-05-v1
```

UME-MODEL registry shows snapshot. Snapshot is signed by author keys.

---

## 4.E Apply model to UME-SDO (staged apply)

```
$ ume sdo apply model://consulto-v1@2025-12-05-v1 --dry-run=false
[APPLY] validate snapshot... OK
[APPLY] simulate policies... FIN-ENG-APPROVAL => DEFER (obligations require approval)
[APPLY] creating staged change; pending approvals required:
       - policy FIN-ENG-APPROVAL -> create approval task task://501234 assigned to role:partner
Operation op-20251205-001 created.
```

UMe-SDO created an approval task — the apply is gated until approvals completed.

---

## 4.F Approve the obligation (simulated via CLI or UME-OS UI)

Assuming partner John approves:

```
$ ume os tasks approve task://501234 --principal "principal:partner:john"
[OK] task://501234 approved by principal:partner:john
```

UME-SDO re-checks and completes the staged apply:

```
[OP] op-20251205-001: approvals satisfied -> applying changes
[OP] provisioning resources -> res://70077
[OP] op-20251205-001: COMPLETE
```

Audit ledger now includes entries:

* creation of task
* approval event
* provisioning event
* final commit with model snapshot id bound

---

## 4.G Operate: Create an engagement (runtime)

Now a UME-OS user creates an engagement via UI or CLI:

```
$ ume os create engagement --file new-engage.json
# new-engage.json:
{
  "client":"entity:bigco",
  "value_usd":150000,
  "margin_target_pct":20.0,
  "delivery_team":"team:eng-core"
}

Response:
[OK] Engagement created: engagement://e-2025-001 (status: AWAITING_APPROVAL)
```

Since create triggers the policy, UME-SDO created approval task as before. After approval, the workflow runs and UME-SDO orchestrates provisioning, schedule OrgCPU, and UME-OS updates status and dashboards.

---

## 4.H Observe & Audit

Export audit range for the operations:

```
$ ume sdo audit export --from=100012 --to=100020 > audit-export.json
$ cat audit-export.json
[ { "ledger_index":100012, "actor":"principal:alice", "action":"sdo.task.create", ... }, ... ]
```

Use the audit to fulfill compliance requirements.

---

## 4.I Iterate & Update Model

Suppose the business lowers threshold to $75K:

Edit `consulto-v1.ume` params and publish a new version `@2025-12-06-v2`. Follow same validate→simulate→publish→apply flow. If change requires approval, UME-SDO will open the approval workflow defined in governance.

---

# 5) Five Plug-and-Play Templates (full module files)

Each module is a ready-to-import template. Save as `.ume` files under `templates/`.

---

## 5.A Retail Template — `template-retail.ume`

```
module retail-basic-v1 {
  meta { version: "2025-12-05-v1" author: "ume-templates" description: "Retail storefront basic" }

  entities {
    entity Product { id:string, sku:string, price:money{USD}, stock:int, lifecycle:enum{active,discontinued} }
    entity Order { id:string, customer:ref[Entity], items:ref[Product][], total:money{USD}, status:enum{new,paid,shipped,returned} }
    entity Refund { id:string, order:ref[Order], amount:money{USD}, reason:string }
  }

  policies {
    policy REFUND-THRESH {
      params { threshold: money{USD} = 1000 }
      when (action == "create_refund") {
        if (payload.amount > params.threshold) {
          effect: DEFER
          obligations: [ { type:"require_approval", roles:["role:store-manager"] } ]
          reason: "High-value refunds require store manager approval."
        } else { effect: ALLOW }
      }
    }
  }

  workflows {
    workflow pos_refund {
      start -> s1
      s1: human_task "store_manager_approval" { roles: ["role:store-manager"], timeout:"48h" }
      s1 -> s2
      s2: task "issue_refund" { type:"auto", action:"process_refund" }
      s2 -> end_success
    }
  }
}
```

---

## 5.B Consulting Template — `template-consulting.ume`

(Full consulting template — this is the same base used in tutorial)

```
module consulting-core-v1 {
  meta { version:"2025-12-05-v1" author:"ume-templates" description:"Consulting firm core template" }

  imports [ "finance-common", "hr-core" ]

  entities {
    entity Engagement { id:string, client:ref[Entity], value_usd:money{USD}, delivery_team:ref[Team], start_date:date }
    entity Team { id:string, name:string, members:ref[Principal][], budget_usd:int }
  }

  policies {
    policy FIN-ENG-APPROVAL {
      params { threshold: money{USD} = 100000 }
      when (action == "create_engagement") {
        if (payload.value_usd > params.threshold) {
          effect: DEFER
          obligations: [ { type:"require_approval", roles:["role:partner"] } ]
        } else effect: ALLOW
      }
    }
  }

  workflows {
    workflow engagement_onboard {
      start -> s1
      s1: human_task "partner_signoff" { roles:["role:partner"], timeout:"72h" }
      s1 -> s2
      s2: task "provision_team" { type:"auto", action:"provision_team" }
      s2 -> end_success
    }
  }
}
```

---

## 5.C Manufacturing CPS Template — `template-plant.ume`

```
module plant-core-v1 {
  meta { version:"2025-12-05-v1" author:"ume-templates" description:"CPS plant operations template" }

  entities {
    entity Line { id:string, site:ref[Entity], status:enum{operational,stopped,maintenance} }
    entity Sensor { id:string, device:ref[Device], metric:string, threshold:float }
  }

  devices {
    device plant-controller {
      id: "device:plant-ctrl"
      device_type: "cps-controller"
      capabilities: ["telemetry","actuate"]
      conn: { proto:"mqtt", endpoint:"edge://plant-ctrl.local:1883" }
      twin_schema: "twin://plant-controller-v1"
    }
  }

  policies {
    policy EHS-001 {
      when (action == "actuate_device") {
        if (!actor.attributes.certificates contains "EHS") {
          effect: DENY
          reason: "EHS certification required to actuate plant devices."
        } else effect: ALLOW
      }
    }
  }

  workflows {
    workflow emergency_shutdown {
      start -> s1
      s1: event "sensor_overheat" -> s2
      s2: task "shutdown_line" { type:"auto", action:"cmd_shutdown", policy_refs:["policy://EHS-001"] }
      s2 -> end_success
    }
  }
}
```

---

## 5.D Venture Fund Template — `template-fund.ume`

```
module fund-core-v1 {
  meta { version:"2025-12-05-v1" author:"ume-templates" description:"Venture fund fund template" }

  entities {
    entity Fund { id:string, capital_usd:money{USD}, investors:ref[Entity][], gp_team:ref[Team] }
    entity Investment { id:string, startup:ref[Entity], amount_usd:money{USD}, stage:enum{seed,seriesA,seriesB} }
  }

  policies {
    policy INVEST_APPROVAL {
      params { threshold: money{USD} = 1000000 }
      when (action == "create_investment") {
        if (payload.amount_usd > params.threshold) {
          effect: DEFER
          obligations: [ { type:"require_approval", roles:["role:gp"] } ]
        } else effect: ALLOW
      }
    }
  }

  workflows {
    workflow investment_commit {
      start -> s1
      s1: human_task "gp_committee_vote" { roles:["role:gp"], timeout:"168h" }
      s1 -> s2
      s2: task "wire_funds" { type:"auto", action:"wire_funds" }
      s2 -> end_success
    }
  }
}
```

---

## 5.E SaaS Startup Template — `template-saas.ume`

```
module saas-core-v1 {
  meta { version:"2025-12-05-v1" author:"ume-templates" description:"Subscription SaaS template" }

  entities {
    entity Subscription { id:string, customer:ref[Entity], plan:string, monthly_amount:money{USD}, status:enum{trial,active,cancelled} }
    entity Invoice { id:string, subscription:ref[Subscription], amount:money{USD}, due_date:date, status:enum{open,paid,overdue} }
  }

  policies {
    policy BILLING_AUTO_RETRY {
      when (action == "charge_customer") {
        if (payload.retries > 3) {
          effect: DEFER
          obligations: [ { type:"require_approval", roles:["role:billing-manager"] } ]
        } else effect: ALLOW
      }
    }
  }

  workflows {
    workflow billing_cycle {
      start -> s1
      s1: task "generate_invoice" { type:"auto", action:"gen_invoice" }
      s1 -> s2
      s2: task "attempt_charge" { type:"auto", action:"charge_customer", policy_refs:["policy://BILLING_AUTO_RETRY"] }
      s2 -> end_success
    }
  }
}
```

---

# Wrap-up & Next Steps

You now have:

* ANTLR grammar `UmeModel.g4` to build a parser.
* JSON Schema `ume-module.schema.json` for validation of module JSON forms.
* A compact `ume` CLI spec and example flows.
* A full consulting firm tutorial (example model + commands) to test the full cycle.
* Five plug-and-play templates to bootstrap different business types.

If you’d like I can next:

* Generate an **ANTLR parser project** skeleton (Java/Go/Python) with listener stubs and a sample parser run for `consulto-v1.ume`.
* Produce the **JSON Schema → code generator** (TypeScript / Go structs) that maps DSL entities to typed structs.
* Implement the **CLI** in a runnable script (Python Click / Go Cobra) with mock runtime responses for quick demos.
* Create an automated **unit test suite** for the grammar and DSL (sample inputs / negative tests).

Which of those (or others) do you want me to do next?
