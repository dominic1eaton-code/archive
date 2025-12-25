A Security Management System typically handles:

User authentication & authorization – track who can do what.

Vulnerability tracking – list software components and their vulnerabilities.

Audit logging – record access and changes.

Alerts – notify when vulnerabilities are found or exploited.

Policy enforcement – enforce security policies like password rules or access restrictions.

Step 2: High-Level Architecture

For a Zig implementation, we can break it down into modules:

Database Module – store users, vulnerabilities, logs.

Could use a JSON file or SQLite.

Authentication Module – handle login, password hashing (use something like argon2).

Vulnerability Management Module – track, add, remove, update vulnerabilities.

Logging Module – append logs with timestamps to file.

CLI / Web Interface – Zig can do CLI easily; a web interface requires an HTTP server (Zig has basic HTTP support).



Features to Add

Password Hashing: Integrate argon2 or bcrypt for secure storage.

Vulnerability CRUD: Add, remove, edit vulnerabilities.

Audit Logging: Append logs to a file with timestamps.

CLI Interface: Use std.io to read commands.

Optional Web Interface: Use std.http to create a small HTTP server.


: Security Considerations

Never store plaintext passwords.

Validate all inputs to prevent injection.

Use proper file permissions for JSON/db storage.

Keep logs immutable and append-only.


# Tamper‑Resistant Logging (Chain‑Hash)

One simple but effective approach for log tamper protection: treat the log as a hash chain, where each entry includes a hash of the previous log line. For example:

When you create the log file, initialize prev_hash = zero_hash (e.g. 32‑byte zero or some constant).

For each action, compute: entry = timestamp || " - " || action || " || " || prev_hash.

Then compute new_hash = SHA256(entry). Append entry + "\n" to log file. Then store prev_hash = new_hash.

On startup or audit you can recompute the chain over the log file; if any line is changed or removed, the hash chain breaks.

Zig’s standard library provides SHA‑256 or other hash via std.crypto.hash. 
Gist
+1

# 🗄️ Optional: Tamper‑Resistant User Database

Similarly, after you save the user list (e.g. to users.json), you can compute and store a digest (e.g. SHA‑256 or an HMAC with a secret key) of the file. On next startup, recompute and compare; if mismatched — you detect tampering.

This is especially useful if the system might be run in an environment where the file might be modified by unauthorized parties.


What This Does Not Do (But You Should Consider for Real Deployment)

It does not provide encryption of the data at rest — users.json and logs.txt are still plaintext (but hashed/logged). If someone obtains the files, while they can’t get passwords, they can read metadata.

Key‑management: if you use a secret key (e.g. for HMAC) to detect tampering, you need to protect that key.

Concurrent editing or partial writes is not handled — you may need safe write semantics (e.g. write‑to‑temp + rename) to avoid corruption.

Replay or tampering before the first hash cannot be detected.



# Explanation & Usage Notes

Password storage: When you add a user, the password is hashed with Argon2id via std.crypto.pwhash.argon2, producing a PHC‑encoded hash (includes salt and parameters). You never store the raw password.

Password verification: authenticateUser reads a password and verifies it against the stored hash using strVerify.

Persistent storage: Users are stored in users.json, vulnerabilities in vulns.json. The format is simple JSON arrays.

Chain‑hash log: On startup initLog() reads the last log line (if any), extracts the previous hash. Each new log entry includes timestamp - action || HEX(SHA256(prev_hash + entry)). This makes it hard to remove or tamper with earlier lines without breaking the chain or requiring recomputation of all subsequent hashes.

CLI commands:

adduser: add a new user (username + password)

auth: prompt for username/password, verify credentials

listusers: show all usernames

addvuln: add a vulnerability (description + severity)

listvulns: list all recorded vulnerabilities

exit: quit

Limitations / Caveats:

This is a single‑process, single-user CLI — no concurrency, no access control per user.

The JSON files and log are stored in plain text; while passwords are hashed and logs are chain-protected, metadata is visible.

There’s no tamper‑protection for the JSON files themselves; an attacker editing users.json or vulns.json could inject or remove entries. To guard that, you'd need a file‑hash or HMAC scheme.

No locking or atomic file writes — so concurrent runs might corrupt files.

Logging size grows indefinitely; in a real system you might rotate logs or archive.

# Putting it All Together

On startup:

Load users.json and verify hash.

Load vulns.json and verify hash.

Initialize log chain-hash.

On modification:

Save JSON file.

Compute new hash and save .hash file.

Log action in chain-hash log.

CLI:

Authenticate user and store current_user.

Only Admin can addvuln.

Anyone can listvulns.

Admin can adduser.

Anyone can listusers.


Core Components of a SIEM

A SIEM system typically includes:

Log Collection

Collect logs from multiple sources (files, syslog, network events).

Parsing/Normalization

Convert raw logs into structured events (JSON, key-value pairs).

Storage

Persist logs in a structured, searchable format.

Analysis / Correlation

Detect suspicious patterns (e.g., failed logins, privilege escalation).

Alerting

Trigger alerts when predefined rules match events.

Dashboard / Querying

Optional: query logs and generate reports.

For a Zig prototype, we can focus on:

Collecting log entries (simulated or from local files)

Normalizing into JSON events

Persisting events to disk

Simple rule-based alerting

Append-only chain-hash logs for tamper resistance

Next Steps / Enhancements

Real Log Collection

Read /var/log/* or Windows Event Logs.

JSON Parsing & Querying

Use std.json.Parser for queries.

Alert Storage

Persist triggered alerts to a separate log.

Role-Based Access

Admins only can view all events or configure rules.

Event Correlation

Detect multi-step attacks by combining events.

Tamper-Resistant Storage

Add file HMACs for events.json like we did for users.json.

Event collection (manual input for now, simulating logs)

Chain-hash logging for tamper detection

Persistent JSON storage for events with SHA256 digest verification

Simple rule-based alerting (e.g., multiple failed logins)

# Features of This Prototype

Event Collection

Manual input through CLI: source, type, message

Timestamp auto-assigned

Persistent JSON Storage

Events saved to events.json

SHA256 digest stored in events.hash for integrity verification

Tamper-Resistant Chain-Hash Log

events.log stores chain-hash of each log entry

Each entry includes timestamp, action, and hash of previous log

Simple Rule-Based Alerting

Currently detects login_failed events

Can be extended for more complex correlation rules

CLI Commands

add → Add a new event

list → List all events

exit → Exit application

Parse multiple log sources

E.g., system logs, application logs, network logs (simulated as different JSON files).

Detect multi-step attack patterns

Example: failed login → privilege escalation → suspicious network connection.

<code>
Design Approach
1. Log Sources

Simulated as separate JSON files:

system_logs.json → OS events (login attempts, user management)

app_logs.json → Application events (file access, errors)

network_logs.json → Network events (connections, suspicious activity)

Each log file has its own hash file for integrity:

const LOG_FILES = [_][]const u8{"system_logs.json", "app_logs.json", "network_logs.json"};
const LOG_HASH_FILES = [_][]const u8{"system_logs.hash", "app_logs.hash", "network_logs.hash"};

2. Extended Event Struct

Add source_type to distinguish the source:

pub const LogEvent = struct {
    timestamp: []const u8,
    source: []const u8,       // e.g., host or service
    source_type: []const u8,  // system, app, network
    event_type: []const u8,
    message: []const u8,
};


source_type allows correlating events from different layers.

3. Multi-Step Attack Patterns

Define patterns as sequences of event types within a time window:

const AttackPattern = struct {
    name: []const u8,
    steps: []const []const u8, // sequence of event_type
    window_sec: u64,           // max time between first and last step
};


Example:

const bruteForcePattern = AttackPattern{
    .name = "Brute Force Attack",
    .steps = &[_][]const u8{"login_failed", "login_failed", "login_failed"},
    .window_sec = 60, // 1 minute
};


The SIEM checks recent events for this sequence to raise an alert.

4. Event Parsing Across Sources

We create a function that loads all logs from multiple files:

fn loadAllEvents(allocator: *Allocator) ![]LogEvent {
    var all_events = try allocator.alloc(LogEvent, 0);
    var total = 0;

    for (LOG_FILES) |file, i| {
        if (!verifyFileIntegrity(file, LOG_HASH_FILES[i], allocator)) {
            std.debug.print("Warning: {s} integrity check failed\n", .{file});
        }

        const events = try loadEventsFromFile(file, allocator);
        const new_len = total + events.len;
        all_events = try allocator.realloc(all_events, new_len);
        for (events) |e, j| {
            all_events[total+j] = e;
        }
        total = new_len;
    }
    return all_events;
}

fn loadEventsFromFile(path: []const u8, allocator: *Allocator) ![]LogEvent {
    if (!std.fs.cwd().exists(path)) return &[_]LogEvent{};
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();
    const data = try file.readToEndAlloc(allocator, 8192);
    defer allocator.free(data);

    var parser = json.Parser.init(data);
    const root = try parser.parseRoot();
    if (root.getType() != .Array) return &[_]LogEvent{};
    const arr = root.Array() orelse return &[_]LogEvent{};

    var events = try allocator.alloc(LogEvent, arr.len);
    for (arr.items()) |item, i| {
        const obj = item.Object() orelse continue;
        const ts = obj.get("timestamp").String() orelse "";
        const src = obj.get("source").String() orelse "";
        const stype = obj.get("source_type").String() orelse "";
        const etype = obj.get("event_type").String() orelse "";
        const msg = obj.get("message").String() orelse "";
        events[i] = LogEvent{ .timestamp=ts, .source=src, .source_type=stype, .event_type=etype, .message=msg };
    }
    return events;
}

5. Correlation Engine

Check the sequence of events against a pattern:

fn detectPattern(pattern: AttackPattern, events: []LogEvent) void {
    const n = events.len;
    if (n < pattern.steps.len) return;

    for (i, e) in events[0..n-pattern.steps.len+1] {
        var matched = true;
        for (j, step) in pattern.steps {
            if (!std.mem.eql(u8, events[i+j].event_type, step)) {
                matched = false;
                break;
            }
        }
        if (matched) {
            std.debug.print("ALERT: Detected attack pattern: {s} starting at {s}\n",
                .{pattern.name, events[i].timestamp});
        }
    }
}


This is a simple sliding-window pattern matcher.

You can enhance it with timestamps and window_sec enforcement for real time correlation.

6. CLI Commands

Extend CLI to allow:

add → add an event to a specific log source

list → list all events

correlate → run detection on multi-step patterns

else if (std.mem.eql(u8, cmd, "correlate")) {
    const all_events = try loadAllEvents(allocator);
    detectPattern(bruteForcePattern, all_events);
}

7. Multi-Source Event Entry

When adding an event, select a log source:

const src_file = try prompt(allocator, "Select log source: system/app/network");
const source_type = std.mem.trim(src_file, " \r\n");


Save event to the corresponding JSON file and recompute its hash.

Log action in chain-hash log as before.

Next Steps / Enhancements

Timestamp-Aware Patterns

Only match events within window_sec.

Multiple Patterns

Maintain a list of AttackPattern and run detection on all.

Persistent Alerts

Save alerts to alerts.json for auditing.

Real-Time Monitoring

Watch log files and trigger correlation automatically.
</code>