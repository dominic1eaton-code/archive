import java.time.LocalDateTime;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.ArrayList;
import java.util.EnumMap;
import java.util.Objects;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.atomic.AtomicLong;
import java.util.stream.Collectors;

package com.work;


/**
 * Simple gig worker task management system.
 * - Thread-safe in-memory storage
 * - Create, assign, start, complete, cancel, update tasks
 * - Query by worker, status, simple summaries and earnings
 */
public class TaskManager {

    public enum Status {
        OPEN, ASSIGNED, IN_PROGRESS, COMPLETED, CANCELLED
    }

    public static class Task {
        private final long id;
        private volatile String title;
        private volatile String description;
        private volatile String workerId; // null when unassigned
        private volatile double pay;
        private volatile Status status;
        private volatile LocalDateTime createdAt;
        private volatile LocalDateTime dueAt;
        private final ConcurrentMap<String, String> metadata = new ConcurrentHashMap<>();

        private Task(long id, String title, String description, LocalDateTime dueAt, double pay, Map<String, String> meta) {
            this.id = id;
            this.title = Objects.requireNonNull(title, "title");
            this.description = description;
            this.dueAt = dueAt;
            this.pay = pay;
            this.status = Status.OPEN;
            this.createdAt = LocalDateTime.now();
            if (meta != null) this.metadata.putAll(meta);
        }

        public long getId() { return id; }
        public String getTitle() { return title; }
        public String getDescription() { return description; }
        public String getWorkerId() { return workerId; }
        public double getPay() { return pay; }
        public Status getStatus() { return status; }
        public LocalDateTime getCreatedAt() { return createdAt; }
        public LocalDateTime getDueAt() { return dueAt; }
        public Map<String,String> getMetadata() { return Collections.unmodifiableMap(metadata); }

        /* synchronous updates on the task object to keep per-task operations safe */
        private synchronized void assignTo(String workerId) {
            this.workerId = workerId;
            this.status = (this.status == Status.OPEN) ? Status.ASSIGNED : this.status;
        }

        private synchronized void start() {
            if (this.status == Status.ASSIGNED || this.status == Status.OPEN) {
                this.status = Status.IN_PROGRESS;
            }
        }

        private synchronized void complete() {
            this.status = Status.COMPLETED;
        }

        private synchronized void cancel() {
            this.status = Status.CANCELLED;
        }

        private synchronized void update(String title, String description, LocalDateTime dueAt, Double pay, Map<String,String> meta) {
            if (title != null) this.title = title;
            if (description != null) this.description = description;
            if (dueAt != null) this.dueAt = dueAt;
            if (pay != null) this.pay = pay;
            if (meta != null) {
                this.metadata.clear();
                this.metadata.putAll(meta);
            }
        }

        @Override
        public String toString() {
            return "Task{" +
                    "id=" + id +
                    ", title='" + title + '\'' +
                    ", workerId='" + workerId + '\'' +
                    ", pay=" + pay +
                    ", status=" + status +
                    ", dueAt=" + dueAt +
                    '}';
        }
    }

    private final ConcurrentMap<Long, Task> tasks = new ConcurrentHashMap<>();
    private final AtomicLong idGenerator = new AtomicLong(1);

    public TaskManager() { }

    public Task createTask(String title, String description, LocalDateTime dueAt, double pay) {
        return createTask(title, description, dueAt, pay, null);
    }

    public Task createTask(String title, String description, LocalDateTime dueAt, double pay, Map<String,String> metadata) {
        long id = idGenerator.getAndIncrement();
        Task t = new Task(id, title, description, dueAt, pay, metadata);
        tasks.put(id, t);
        return t;
    }

    public Task getTask(long id) {
        return tasks.get(id);
    }

    public List<Task> listAll() {
        return new ArrayList<>(tasks.values());
    }

    public List<Task> listByWorker(String workerId) {
        if (workerId == null) return Collections.emptyList();
        return tasks.values().stream()
                .filter(t -> workerId.equals(t.getWorkerId()))
                .collect(Collectors.toList());
    }

    public List<Task> listByStatus(Status status) {
        if (status == null) return Collections.emptyList();
        return tasks.values().stream()
                .filter(t -> t.getStatus() == status)
                .collect(Collectors.toList());
    }

    /**
     * Attempts to assign a task atomically. Returns true when assignment succeeded.
     * If task is CANCELLED or COMPLETED it won't assign.
     */
    public boolean assignTask(long taskId, String workerId) {
        Task t = tasks.get(taskId);
        if (t == null || workerId == null) return false;
        synchronized (t) {
            if (t.getStatus() == Status.COMPLETED || t.getStatus() == Status.CANCELLED) return false;
            t.assignTo(workerId);
            return true;
        }
    }

    public boolean startTask(long taskId, String workerId) {
        Task t = tasks.get(taskId);
        if (t == null) return false;
        synchronized (t) {
            // allow starting only by assigned worker (or if unassigned allow start)
            if (t.getWorkerId() != null && !t.getWorkerId().equals(workerId)) return false;
            if (t.getStatus() == Status.CANCELLED || t.getStatus() == Status.COMPLETED) return false;
            t.start();
            if (t.getWorkerId() == null && workerId != null) t.assignTo(workerId);
            return true;
        }
    }

    public boolean completeTask(long taskId, String workerId) {
        Task t = tasks.get(taskId);
        if (t == null) return false;
        synchronized (t) {
            if (t.getStatus() == Status.CANCELLED || t.getStatus() == Status.COMPLETED) return false;
            // allow only assigned worker (or anyone if unassigned)
            if (t.getWorkerId() != null && !t.getWorkerId().equals(workerId)) return false;
            t.complete();
            if (t.getWorkerId() == null && workerId != null) t.assignTo(workerId);
            return true;
        }
    }

    public boolean cancelTask(long taskId) {
        Task t = tasks.get(taskId);
        if (t == null) return false;
        synchronized (t) {
            if (t.getStatus() == Status.COMPLETED) return false;
            t.cancel();
            return true;
        }
    }

    public boolean updateTask(long taskId, String title, String description, LocalDateTime dueAt, Double pay, Map<String,String> metadata) {
        Task t = tasks.get(taskId);
        if (t == null) return false;
        t.update(title, description, dueAt, pay, metadata);
        return true;
    }

    public double pendingEarningsForWorker(String workerId) {
        if (workerId == null) return 0.0;
        return tasks.values().stream()
                .filter(t -> workerId.equals(t.getWorkerId()))
                .filter(t -> t.getStatus() == Status.ASSIGNED || t.getStatus() == Status.IN_PROGRESS)
                .mapToDouble(Task::getPay)
                .sum();
    }

    public double completedEarningsForWorker(String workerId) {
        if (workerId == null) return 0.0;
        return tasks.values().stream()
                .filter(t -> workerId.equals(t.getWorkerId()))
                .filter(t -> t.getStatus() == Status.COMPLETED)
                .mapToDouble(Task::getPay)
                .sum();
    }

    public Map<Status, Long> statusSummary() {
        Map<Status, Long> summary = new EnumMap<>(Status.class);
        for (Status s : Status.values()) summary.put(s, 0L);
        tasks.values().forEach(t -> summary.compute(t.getStatus(), (k,v) -> v == null ? 1L : v + 1));
        return summary;
    }

    public boolean removeTask(long taskId) {
        return tasks.remove(taskId) != null;
    }

    // Simple search by keyword in title/description
    public List<Task> search(String keyword) {
        if (keyword == null || keyword.isEmpty()) return Collections.emptyList();
        String lower = keyword.toLowerCase();
        return tasks.values().stream()
                .filter(t -> (t.getTitle() != null && t.getTitle().toLowerCase().contains(lower)) ||
                             (t.getDescription() != null && t.getDescription().toLowerCase().contains(lower)))
                .collect(Collectors.toList());
    }
}