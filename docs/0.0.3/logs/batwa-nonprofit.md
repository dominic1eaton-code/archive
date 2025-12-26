Below is the **canonical, coherent, UME-compatible organizational model** for an **urban community development nonprofit**, formally named:

### **batwa-model**

> A UME-platform organizational model representing a community-rooted urban development NGO, designed to plug directly into the **UME programmable organization runtime** and remain consistent with all org-compute primitives, the organization monad, the unified theory of agent, and the nandi-platform doctrine.

---

# ✅ **BATWA-MODEL (Urban Community Development Nonprofit)**

**Alias:** `batwa-model`
**Type:** `ume:OrgModel`
**Description:**
A mission-driven, community-embedded, multi-stakeholder nonprofit that carries out collective urban development, community empowerment, local economic activation, neighborhood resilience, and cooperative infrastructure building.

The model follows the canonical UME organization grammar:

```
OrgModel = {
  identity,
  mission,
  domains,
  roles,
  capabilities,
  artifacts,
  lifecycle,
  governance,
  org-ledger-mappings,
  org-task-mappings,
}
```

---

# 1. **IDENTITY**

```
identity: {
  org_alias: "batwa-model",
  org_type: "urban_community_development_nonprofit",
  legal_form: "501(c)(3)-like_nonprofit",
  scope: "urban_community_economic_infrastructure_social_development",
  tags: ["community", "urban", "nonprofit", "development", "resilience"],
}
```

---

# 2. **MISSION**

```
mission: {
  purpose: "Support, develop, and empower urban communities through cooperative infrastructure, local economic growth, housing stabilization, community-owned assets, and collective agency.",
  theory_of_change: "Strengthening local social networks and community-led development increases resilience, prosperity, and autonomy.",
  agent-theory: {
    foundation: "community-agent = collective-affordant-agent",
    dependence: ["Aff", "Cohesion", "Cooperation", "Resource-Flow"],
  }
}
```

---

# 3. **DOMAINS (Mapped to UME Domain Grammar)**

UME organizations decompose into **OrgDomains**, each expressing structured activities.

```
domains: {
  community_engagement: {
    objectives: [
      "activate local participation",
      "map community needs",
      "coordinate members and volunteers",
    ],
    outputs: ["engagement_reports", "community_mapping_artifacts"]
  },

  housing_stability: {
    objectives: [
      "tenant advocacy",
      "housing stabilization programs",
      "anti-displacement initiatives"
    ],
    outputs: ["housing_assistance_cases", "tenant_resources"]
  },

  local_economy: {
    objectives: [
      "job training",
      "entrepreneur support",
      "community cooperative formation"
    ],
    outputs: ["training_programs", "coop_initiation_artifacts"]
  },

  infrastructure_projects: {
    objectives: [
      "community facility renovations",
      "public space improvements",
      "local infrastructure co-design"
    ],
    outputs: ["design_docs", "project_plans"]
  },

  fundraising_and_development: {
    objectives: [
      "grant writing",
      "donor management",
      "community fundraising"
    ],
    outputs: ["grant_proposals", "donor_reports"]
  }
}
```

---

# 4. **ROLES (Mapped to UME Role Grammar)**

Each role is explicitly a **UME-Agent Role**, consistent with the unified theory of agent.

```
roles: {
  executive_director: {
    capabilities: ["strategic_direction", "represent_org", "funding_overview"],
  },
  community_organizer: {
    capabilities: ["coordinate_members", "run_events", "collect_feedback"],
  },
  housing_advocate: {
    capabilities: ["provide_assistance", "mediate_cases", "maintain_resources"],
  },
  program_manager: {
    capabilities: ["manage_programs", "create_reports", "supervise_teams"],
  },
  development_officer: {
    capabilities: ["write_grants", "manage_donors", "track_funding"],
  },
  volunteer: {
    capabilities: ["support_events", "assist_programs"]
  },
  board_member: {
    capabilities: ["governance", "oversight", "policy_approval"]
  }
}
```

---

# 5. **CAPABILITIES (UME Capability Grammar)**

Capabilities define what tasks the model can execute through UME-runtime.

```
capabilities: {
  run_community_events,
  manage_cases,
  produce_reports,
  develop_grants,
  maintain_stakeholder_relationships,
  initiate_projects,
  coordinate_volunteers,
  track_impact_metrics,
}
```

---

# 6. **ARTIFACTS**

Each artifact maps to an OrgLedger primitive.

```
artifacts: {
  engagement_report: { primitive: "OrgLedger.Document" },
  community_map: { primitive: "OrgLedger.Dataset" },
  housing_case_file: { primitive: "OrgLedger.Case" },
  grant_proposal: { primitive: "OrgLedger.Document" },
  project_plan: { primitive: "OrgLedger.Project" },
  donor_report: { primitive: "OrgLedger.Document" },
  coop_init_record: { primitive: "OrgLedger.LedgerEntry" }
}
```

---

# 7. **LIFECYCLE (Canonical UME OrgLifecycle)**

```
lifecycle: {
  phases: [
    "community-discovery",
    "program-design",
    "funding-acquisition",
    "program-execution",
    "impact-measurement",
    "iteration-and-governance"
  ],
  transitions: {
    "community-discovery" -> "program-design",
    "program-design" -> "funding-acquisition",
    "funding-acquisition" -> "program-execution",
    "program-execution" -> "impact-measurement",
    "impact-measurement" -> "iteration-and-governance",
    "iteration-and-governance" -> "community-discovery"
  }
}
```

---

# 8. **GOVERNANCE (UME Governance Grammar)**

```
governance: {
  board_structure: {
    type: "community_board",
    authority: ["policy", "oversight", "budget_approval"]
  },
  decision_making: "consensus_weighted",
  community_input_channels: ["meetings", "surveys", "assemblies"]
}
```

---

# 9. **ORG-LEDGER MAPPINGS (UME-Runtime Bindings)**

```
org-ledger-mappings: {
  finances -> OrgLedger.FinancialLedger,
  grants -> OrgLedger.DocumentLedger,
  projects -> OrgLedger.ProjectLedger,
  cases -> OrgLedger.CaseLedger,
  community_data -> OrgLedger.DatasetLedger,
}
```

---

# 10. **ORG-TASK MAPPINGS (UME-Runtime Bindings)**

```
org-task-mappings: {
  event_planning -> OrgTask.Workflow,
  case_management -> OrgTask.CaseWorkflow,
  grant_development -> OrgTask.DocumentWorkflow,
  project_execution -> OrgTask.ProjectWorkflow,
  volunteer_coordination -> OrgTask.ActorWorkflow,
}
```

---

# ✅ **batwa-model is now a fully defined UME-platform model**

It is:

* **Canonical** with the unified theory of agent
* **Composable** with all UME primitives
* **Consistent** with org-compute, org-ledger, org-task
* **Integrable** into nandi-platform / kogi-platform design
* **Extensible** for future SDocs, blueprints, or executable org flows

---

If you want, I can also generate:

### ▸ the full **batwa-model UML diagram** (ASCII)

### ▸ the **batwa-model → UME system binding document**

### ▸ the **batwa-model acceptance test suite**

### ▸ the **batwa-model JSON schema** for ume-platform

### ▸ the **batwa-model integrated into the Kogi or Nandi platform**

Just say **y**.
Nice — below are both deliverables ready to plug into the UME runtime.

# Full batwa-model UML diagram (ASCII)

Use this ASCII class/component UML as a canonical view (classes, relationships, cardinality, important attributes). It shows structure (class diagram) and a small component/flow overlay at the bottom showing how the `batwa-model` binds to UME primitives.

```
+=================================================================================+
|                                    batwa-model                                  |
|                         (UME OrgModel : urban_community_development)            |
+=================================================================================+

                               +------------------+
                               | <<OrgModel>>     |
                               | batwa-model      |
                               |------------------|
                               | - id             |
                               | - alias          |
                               | - org_type       |
                               | - legal_form     |
                               | - scope          |
                               | - mission_id     |
                               +------------------+
                                       |
                1                      | 1..*                        1
       +--------------------+-----------+---------------------+------------------+
       |                    |                                 |                  |
+---------------+   +---------------+                  +----------------+   +-----------------+
| <<Identity>>  |   | <<Mission>>   |                  | <<Domains>>    |   | <<Governance>>  |
| identity      |   | mission       |<>--------------->| Domain [*]     |   | governance       |
|---------------|   |---------------|  (references)    | - id           |   |------------------|
| - org_alias    |   | - purpose     |                  | - name         |   | - board_struct   |
| - org_type     |   | - theory_of_change|               | - objectives[] |   | - decision_model |
| - legal_form   |   | - agent_theory |                  | - outputs[]    |   | - channels[]     |
| - scope        |   +---------------+                  +----------------+   +-----------------+
+---------------+                                                            |
                                                                              |
                              +-----------------+-----------------------------+
                              |                 |
                              |                 |
                       +--------------+   +----------------+   +------------------+
                       | <<Roles>>    |   | <<Artifacts>>  |   | <<Capabilities>> |
                       | Role [*]     |   | Artifact [*]   |   | Capability [*]   |
                       |--------------|   |----------------|   |------------------|
                       | - name       |   | - id           |   | - id             |
                       | - perms[]    |   | - primitive    |   | - description    |
                       | - capabilities[]| | - meta        |   |                  |
                       +--------------+   +----------------+   +------------------+
                              | 1..*                | 0..*               | 0..*
                              |                     |                    |
                              |                     |                    |
                        +-------------------------------------------------------+
                        |                      <<Lifecycle>>                  |
                        |  lifecycle.phases: [community-discovery, ...]        |
                        |  transitions: map<phase,phase>                       |
                        +-------------------------------------------------------+
                                       |
                                       |  binds-to
                                       v
+=================================================================================+
|                            batwa-model  →  UME Binding View                     |
+=================================================================================+
|  COMPONENTS:                                                                    |
|   - OrgModel Registry (UME)            : OrgModel.register(org_json)          |
|   - OrgLedger                          : OrgLedger.* (ProjectLedger, etc.)     |
|   - OrgTask Engine                     : OrgTask.start(workflow_spec)         |
|   - OrgAuth/ACL                        : Role ↔ Permission ↔ Actor             |
+---------------------------------------------------------------------------------+
|  KEY MAPPINGS (examples):                                                       |
|   - domains.community_engagement     -> OrgTask.Workflow "community_engage"    |
|   - artifacts.community_map          -> OrgLedger.Dataset                      |
|   - roles.community_organizer        -> Actor principal + ActorCapabilities    |
|   - lifecycle.phase transitions      -> OrgStateMachine transitions           |
+=================================================================================+
```

---

# batwa-model → UME system binding document

Below is a practical, executable binding document you can drop into the UME runtime (semantic mappings, JSON schema, syscall mapping, example ledger entries, task templates, role→permission matrix, lifecycle state machine, and acceptance checks).

---

## 1) High-level binding summary

* **Model alias**: `batwa-model`
* **Target runtime**: `ume-platform` (OrgModel runtime / OrgTask / OrgLedger / OrgAuth)
* **Primary primitives used**:

  * `OrgModel` (model registration)
  * `OrgTask` (task/workflow runtime)
  * `OrgLedger` (document, project, case, financial ledgers)
  * `OrgAuth` (role-based access / capability enforcement)
  * `OrgStateMachine` (lifecycle states & transitions)

---

## 2) Top-level JSON schema (excerpt)

Use this as the canonical schema to register `batwa-model` with `OrgModel.register(...)`.

```json
{
  "$schema": "https://example/ume/orgmodel.schema.json",
  "alias": "batwa-model",
  "org_type": "urban_community_development_nonprofit",
  "legal_form": "501(c)(3)-like_nonprofit",
  "scope": "urban_community_economic_infrastructure_social_development",
  "identity": {
    "org_alias": "batwa-model",
    "tags": ["community","urban","nonprofit","development","resilience"]
  },
  "mission": {
    "purpose": "Support, develop, and empower urban communities through cooperative infrastructure, local economic growth, housing stabilization, community-owned assets, and collective agency.",
    "theory_of_change": "Strengthening local social networks and community-led development increases resilience, prosperity, and autonomy.",
    "agent_theory": {
      "foundation": "community-agent = collective-affordant-agent",
      "dependencies": ["Aff","Cohesion","Cooperation","ResourceFlow"]
    }
  },
  "domains": {
    "community_engagement": {
      "objectives": ["activate local participation","map community needs","coordinate members and volunteers"],
      "outputs": ["engagement_reports","community_mapping_artifacts"]
    }
    /* ... other domains (housing_stability, local_economy, infrastructure_projects, fundraising_and_development) ... */
  },
  "roles": {
    "executive_director": {"capabilities":["strategic_direction","represent_org","funding_overview"]},
    "community_organizer": {"capabilities":["coordinate_members","run_events","collect_feedback"]}
    /* ... */
  },
  "artifacts": {
    "engagement_report": {"primitive":"OrgLedger.Document"},
    "community_map": {"primitive":"OrgLedger.Dataset"},
    "housing_case_file": {"primitive":"OrgLedger.Case"}
  },
  "lifecycle": {
    "phases":["community-discovery","program-design","funding-acquisition","program-execution","impact-measurement","iteration-and-governance"],
    "transitions": {
      "community-discovery":"program-design",
      "program-design":"funding-acquisition",
      "funding-acquisition":"program-execution",
      "program-execution":"impact-measurement",
      "impact-measurement":"iteration-and-governance",
      "iteration-and-governance":"community-discovery"
    }
  }
}
```

> Save the full JSON to `batwa-model.json` and call `OrgModel.register(batwa-model.json)` in the UME runtime.

---

## 3) Syscall / API binding table (suggested names)

These are the UME syscalls (or API calls) the model expects the runtime to provide. If your runtime uses different names, map appropriately.

| Model activity              |      UME Primitive | Example API / Syscall                                        |
| --------------------------- | -----------------: | ------------------------------------------------------------ |
| register organization model |           OrgModel | `OrgModel.register(org_json)`                                |
| fetch model                 |           OrgModel | `OrgModel.get(alias)`                                        |
| start event workflow        |            OrgTask | `OrgTask.start(org_alias, task_template, inputs)`            |
| append engagement report    | OrgLedger.Document | `OrgLedger.appendDocument(org_alias, ledger_type, document)` |
| create project              |  OrgLedger.Project | `OrgLedger.createProject(org_alias, project_spec)`           |
| create housing case         |     OrgLedger.Case | `OrgLedger.createCase(org_alias, case_payload)`              |
| assign role to actor        |            OrgAuth | `OrgAuth.assignRole(org_alias, actor_id, role_name)`         |
| transition lifecycle state  |    OrgStateMachine | `OrgStateMachine.transition(org_alias, from,to,meta)`        |
| query metrics               |    OrgLedger.Query | `OrgLedger.query(org_alias, ledger_type, query)`             |

---

## 4) Role → permission → capability matrix

A condensed mapping of roles to the UME permissions they require, and the capability primitives they should be allowed to invoke.

```
Role: executive_director
  - UME permissions: model:read, model:update, ledger:financial:write, org:governance:approve
  - Capabilities: strategic_direction, represent_org, funding_overview

Role: community_organizer
  - UME permissions: task:execute:event, ledger:document:append, actor:read
  - Capabilities: coordinate_members, run_events, collect_feedback

Role: housing_advocate
  - UME permissions: case:write, case:read, actor:write
  - Capabilities: provide_assistance, mediate_cases, maintain_resources

Role: volunteer
  - UME permissions: task:execute, document:append(limited)
  - Capabilities: support_events, assist_programs

Role: board_member
  - UME permissions: governance:read, governance:vote, financial:read
  - Capabilities: oversight, policy_approval
```

> Implement as `OrgAuth` policies in the UME ACL store. Prefer capability-based enforcement (not solely role names).

---

## 5) OrgLedger mapping (ledger types and example schemas)

Map batwa artifacts to ledger primitives (ledger types) and show example entry schema.

* **OrgLedger.Dataset** — `community_map`

  * Example entry:

  ```json
  {
    "ledger_type": "dataset",
    "id": "community_map_2025_001",
    "title": "NE Neighborhood Resource Map",
    "data_summary": "CSV of households, assets, public spaces, service gaps",
    "created_by": "actor:community_organizer:emma",
    "created_at": "2025-12-05T18:00:00-06:00"
  }
  ```

* **OrgLedger.Case** — `housing_case_file`

  * Example entry:

  ```json
  {
    "ledger_type": "case",
    "case_id": "case-2025-0001",
    "client": {"name":"J. Doe", "anon_id":"anon-1234"},
    "status":"open",
    "assigned_to":"actor:housing_advocate:marcus",
    "notes": [{"ts":"2025-12-04T14:00:00-06:00","actor":"marcus","text":"intake complete"}]
  }
  ```

* **OrgLedger.Project** — `project_plan`

  * Example entry:

  ```json
  {
    "ledger_type":"project",
    "project_id":"proj-emp-center-01",
    "phase":"funding-acquisition",
    "budget": {"requested": 120000, "awarded": 0},
    "owner":"program_manager",
    "artifacts":["proj_design_v1.pdf","budget_v1.xlsx"]
  }
  ```

* **OrgLedger.Document** — `engagement_report`, `grant_proposal`, `donor_report`

  * Document entries should include `document_type`, `version`, `author_actor_id`, `signoff` stamp array for governance approvals.

---

## 6) OrgTask templates (examples)

**Event planning workflow** (`community_event_workflow`)

```yaml
name: community_event_workflow
steps:
  - id: intake
    actor_role: community_organizer
    action: create_event_proposal
    outputs: [event_proposal_doc]
  - id: approve
    actor_role: program_manager
    action: review_and_approve
    condition: proposal_ok
    outputs: [event_plan]
  - id: notify
    actor_role: community_organizer
    action: publish_event_listing
    outputs: [event_listing]
  - id: run_event
    actor_role: volunteer
    action: run_shift
    outputs: [attendance_list, engagement_feedback]
  - id: close
    actor_role: program_manager
    action: append_engagement_report_to_ledger
    outputs: [engagement_report_document]
```

Call: `OrgTask.start("batwa-model", "community_event_workflow", {inputs})`.

**Case management workflow** (`housing_case_workflow`) — uses OrgLedger.Case primitives and a case-specific state machine (`open -> investigation -> intervention -> closed`).

---

## 7) Lifecycle state machine

Define lifecycle states and transition guards. Implement via `OrgStateMachine.register(org_alias, lifecycle_spec)`.

```
States:
  - community-discovery
  - program-design
  - funding-acquisition
  - program-execution
  - impact-measurement
  - iteration-and-governance

Transitions:
  community-discovery -> program-design  [guard: community_input_complete == true]
  program-design -> funding-acquisition [guard: project_proposal_ready == true]
  funding-acquisition -> program-execution [guard: funds_awarded > 0]
  program-execution -> impact-measurement [guard: program_end_date_reached OR metrics_threshold_reached]
  impact-measurement -> iteration-and-governance [guard: impact_report_generated]
  iteration-and-governance -> community-discovery [guard: governance_vote_passed]
```

---

## 8) Acceptance tests / checks (minimal suite)

These are automated checks to validate correct integration.

1. **Model Registration Test**

   * Input: `batwa-model.json`
   * Expect: `OrgModel.register` returns `200 OK` and `model_id`.
2. **Role Assignment Test**

   * Assign `community_organizer` to `actor:emma`
   * Expect: `OrgAuth.getRoles(actor:emma)` includes `community_organizer`.
3. **Workflow Execution Test**

   * Start `community_event_workflow` with minimal inputs
   * Expect: workflow completes (or moves to approval) and `engagement_report` appended to `OrgLedger.Document`.
4. **Ledger Write / Read**

   * Append `community_map` dataset — read back and validate `created_by`, `created_at`.
5. **Lifecycle Transition Guard**

   * Move state from `program-design` to `funding-acquisition` with `project_proposal_ready=true`.
   * Expect: `OrgStateMachine.transition` succeeds; otherwise fails with clear reason.
6. **ACL Enforcement**

   * Attempt `grant_development` (write grant_proposal) as `volunteer` — expect `permission denied`.

Implement as UME acceptance tests (e.g., `OrgTest.runSuite("batwa-model:smoke")`).

---

## 9) Example event flow (end-to-end)

1. **Community Organizer** files `community_map` -> `OrgLedger.Dataset.append(...)`.
2. This creates a project proposal: `OrgTask.start("batwa-model", "proposal_workflow", payload)`.
3. **Program Manager** reviews and moves lifecycle: `OrgStateMachine.transition("batwa-model","community-discovery","program-design")`.
4. **Development Officer** opens grant workflow -> `OrgTask.start(... "grant_development_workflow")`.
5. If funds awarded -> `OrgLedger.Project.create(...)` with `phase=program-execution`.
6. During execution, `housing_case` entries created and updated in `OrgLedger.Case`.
7. On completion, `impact_report` created and appended; governance votes held (via `OrgTask` or `OrgAuth`) to move to iteration.

---

## 10) Implementation notes & best practices

* **Capability-First Auth**: Authorize actions by capability (e.g., `case:write`) rather than string role names only.
* **Immutable Ledger Entries**: Ledger appends should be append-only; use versioning for document updates.
* **Privacy & PII**: Housing cases contain sensitive data — enforce encryption at rest and restricted read ACLs (e.g., only `housing_advocate`, `case_manager`).
* **Actor Identity**: Use `actor:<role>:<actor_id>` canonical URIs to avoid ambiguity across systems.
* **Testing**: Automate acceptance tests as part of CI that runs against a UME staging environment.
* **Observability**: Emit events (`OrgEvent`) on major actions (model.registered, task.started, ledger.appended, state.transition) so monitoring/analytics can consume.

---

## 11) Example quick-start commands (pseudocode)

```js
// Register model
const orgJson = fs.readFileSync("batwa-model.json");
await OrgModel.register(orgJson);

// Assign a role
await OrgAuth.assignRole("batwa-model","actor:emma","community_organizer");

// Start a workflow
await OrgTask.start("batwa-model","community_event_workflow", { event_name:"Block Party" });

// Append document
await OrgLedger.appendDocument("batwa-model","engagement_reports", { title:"Block Party Report", author:"actor:emma", content:"..." });
```

---

## 12) Deliverables you can request next (I can produce immediately)

* Full `batwa-model.json` file (complete, ready to register)
* `batwa-model` acceptance test scripts (ASCI-based test suite)
* ASCII UML sequence diagrams for the `community_event_workflow` or `housing_case_workflow`
* Minimal UME-compatible policy file for `OrgAuth` (RBAC/policy json)
* ASCII mermaid-style diagrams or prettier UML files for inclusion in docs

Tell me which next step you want (or say `y` to make the JSON file + test suite now).
