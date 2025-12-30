import java.time.Instant;
import java.time.ZoneId;
import java.time.format.DateTimeFormatter;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.UUID;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicReference;

package com.portal;


/**
 * Gig worker dashboard model containing worker summary, active jobs, notifications and helpers.
 * Single-file, thread-friendly, no external dependencies.
 */
public final class Dashboard {
    private static final DateTimeFormatter ISO = DateTimeFormatter.ISO_INSTANT.withZone(ZoneId.of("UTC"));

    private final String workerId;
    private volatile String name;

    // Thread-safe counters/accumulators
    private final AtomicReference<Double> totalEarnings = new AtomicReference<>(0.0);
    private final AtomicInteger completedJobs = new AtomicInteger(0);
    private final AtomicReference<Double> rating = new AtomicReference<>(0.0);

    // Collections optimized for concurrent reads/writes
    private final CopyOnWriteArrayList<Job> activeJobs = new CopyOnWriteArrayList<>();
    private final CopyOnWriteArrayList<Notification> notifications = new CopyOnWriteArrayList<>();

    public Dashboard(String workerId, String name) {
        this.workerId = Objects.requireNonNull(workerId, "workerId");
        this.name = Objects.requireNonNull(name, "name");
    }

    // Basic getters
    public String getWorkerId() { return workerId; }
    public String getName() { return name; }
    public void setName(String newName) { this.name = Objects.requireNonNull(newName, "newName"); }

    public double getTotalEarnings() { return totalEarnings.get(); }
    public int getCompletedJobs() { return completedJobs.get(); }
    public double getRating() { return rating.get(); }

    public List<Job> getActiveJobs() { return List.copyOf(activeJobs); }
    public List<Notification> getNotifications() { return List.copyOf(notifications); }

    // Mutators
    public void addEarnings(double amount) {
        if (amount <= 0) return;
        totalEarnings.updateAndGet(prev -> prev + amount);
    }

    public void addJob(Job job) {
        Objects.requireNonNull(job, "job");
        activeJobs.add(job);
    }

    /**
     * Mark a job completed by id. Will remove from active jobs, increase earnings and
     * update rating using a running average.
     *
     * @param jobId    job id to complete
     * @param earned   earnings from this job (non-negative)
     * @param jobRating rating for this job in [0,5]
     * @return the completed Job if found, otherwise empty
     */
    public Optional<Job> completeJob(String jobId, double earned, double jobRating) {
        if (jobId == null) return Optional.empty();
        for (Job j : activeJobs) {
            if (jobId.equals(j.getId())) {
                if (activeJobs.remove(j)) {
                    // update earnings
                    if (earned > 0) addEarnings(earned);

                    // update rating as weighted running average
                    if (jobRating >= 0 && jobRating <= 5) {
                        synchronized (rating) {
                            double oldRating = rating.get();
                            int prevCompleted = completedJobs.get();
                            double newRating = (oldRating * prevCompleted + jobRating) / (prevCompleted + 1);
                            rating.set(newRating);
                        }
                    }

                    completedJobs.incrementAndGet();
                    j.markCompleted();
                    return Optional.of(j);
                } else {
                    return Optional.empty();
                }
            }
        }
        return Optional.empty();
    }

    public Notification addNotification(String message) {
        Notification n = new Notification(UUID.randomUUID().toString(), message, Instant.now());
        notifications.add(n);
        return n;
    }

    public void markNotificationRead(String notificationId) {
        for (Notification n : notifications) {
            if (n.getId().equals(notificationId)) {
                n.markRead();
                break;
            }
        }
    }

    // Simple textual summary
    public String summary() {
        return String.format("Worker[%s] %s — Earnings: $%.2f, Completed: %d, Rating: %.2f, ActiveJobs: %d",
                workerId, name, getTotalEarnings(), getCompletedJobs(), getRating(), activeJobs.size());
    }

    // Minimal JSON representation (manual quoting, no external libs)
    public String toJson() {
        StringBuilder sb = new StringBuilder(512);
        sb.append("{")
          .append("\"workerId\":\"").append(escape(workerId)).append("\",")
          .append("\"name\":\"").append(escape(name)).append("\",")
          .append("\"totalEarnings\":").append(String.format("%.2f", getTotalEarnings())).append(",")
          .append("\"completedJobs\":").append(getCompletedJobs()).append(",")
          .append("\"rating\":").append(String.format("%.2f", getRating())).append(",");

        sb.append("\"activeJobs\":[");
        for (int i = 0; i < activeJobs.size(); i++) {
            if (i > 0) sb.append(",");
            sb.append(activeJobs.get(i).toJson());
        }
        sb.append("],");

        sb.append("\"notifications\":[");
        for (int i = 0; i < notifications.size(); i++) {
            if (i > 0) sb.append(",");
            sb.append(notifications.get(i).toJson());
        }
        sb.append("]}");
        return sb.toString();
    }

    private static String escape(String s) {
        if (s == null) return "";
        return s.replace("\"", "\\\"").replace("\n", "\\n").replace("\r", "\\r");
    }

    // Nested lightweight Job model
    public static final class Job {
        public enum Status { ACTIVE, COMPLETED }

        private final String id;
        private final String title;
        private final String description;
        private final Instant createdAt;
        private volatile Status status;

        public Job(String id, String title, String description, Instant createdAt) {
            this.id = Objects.requireNonNull(id, "id");
            this.title = Objects.requireNonNull(title, "title");
            this.description = description == null ? "" : description;
            this.createdAt = createdAt == null ? Instant.now() : createdAt;
            this.status = Status.ACTIVE;
        }

        public static Job create(String title, String description) {
            return new Job(UUID.randomUUID().toString(), title, description, Instant.now());
        }

        public String getId() { return id; }
        public String getTitle() { return title; }
        public String getDescription() { return description; }
        public Instant getCreatedAt() { return createdAt; }
        public Status getStatus() { return status; }

        private void markCompleted() { this.status = Status.COMPLETED; }

        public String toJson() {
            return String.format("{\"id\":\"%s\",\"title\":\"%s\",\"description\":\"%s\",\"createdAt\":\"%s\",\"status\":\"%s\"}",
                    escape(id), escape(title), escape(description), ISO.format(createdAt), status.name());
        }
    }

    // Simple notification model
    public static final class Notification {
        private final String id;
        private final String message;
        private final Instant createdAt;
        private volatile boolean read;

        public Notification(String id, String message, Instant createdAt) {
            this.id = Objects.requireNonNull(id, "id");
            this.message = message == null ? "" : message;
            this.createdAt = createdAt == null ? Instant.now() : createdAt;
            this.read = false;
        }

        public String getId() { return id; }
        public String getMessage() { return message; }
        public Instant getCreatedAt() { return createdAt; }
        public boolean isRead() { return read; }
        public void markRead() { this.read = true; }

        public String toJson() {
            return String.format("{\"id\":\"%s\",\"message\":\"%s\",\"createdAt\":\"%s\",\"read\":%s}",
                    escape(id), escape(message), ISO.format(createdAt), read ? "true" : "false");
        }
    }
}