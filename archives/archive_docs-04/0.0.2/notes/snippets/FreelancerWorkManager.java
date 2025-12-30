import java.time.Instant;
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicReference;
import java.util.stream.Collectors;

package com.work;


/**
 * WorkManager - simple freelancer worker management system.
 *
 * Responsibilities:
 * - register / remove freelancers
 * - create / assign / complete tasks
 * - track payments and ratings
 * - search freelancers by skills and availability
 *
 * Thread-safe, in-memory, single-file implementation intended as a starter.
 */
public class WorkManager {

    private final Map<UUID, Freelancer> freelancers = new ConcurrentHashMap<>();
    private final Map<UUID, Task> tasks = new ConcurrentHashMap<>();
    private final Map<UUID, List<PaymentRecord>> payments = new ConcurrentHashMap<>();

    // ========== Freelancer management ==========

    public Freelancer registerFreelancer(String name, Set<String> skills, Availability availability) {
        Objects.requireNonNull(name, "name");
        Objects.requireNonNull(skills, "skills");
        Objects.requireNonNull(availability, "availability");

        Freelancer f = new Freelancer(UUID.randomUUID(), name, new HashSet<>(skills), availability, 0.0, 0);
        freelancers.put(f.id, f);
        return f;
    }

    public boolean removeFreelancer(UUID freelancerId) {
        Objects.requireNonNull(freelancerId, "freelancerId");
        return freelancers.remove(freelancerId) != null;
    }

    public Optional<Freelancer> getFreelancer(UUID freelancerId) {
        return Optional.ofNullable(freelancers.get(freelancerId));
    }

    public List<Freelancer> listFreelancers() {
        return new ArrayList<>(freelancers.values());
    }

    public List<Freelancer> findFreelancersBySkill(String skill) {
        Objects.requireNonNull(skill, "skill");
        String s = skill.toLowerCase(Locale.ROOT);
        return freelancers.values().stream()
                .filter(f -> f.skills.stream().anyMatch(k -> k.toLowerCase(Locale.ROOT).equals(s)))
                .collect(Collectors.toList());
    }

    public void updateAvailability(UUID freelancerId, Availability newAvailability) {
        Objects.requireNonNull(freelancerId, "freelancerId");
        Objects.requireNonNull(newAvailability, "newAvailability");
        freelancers.computeIfPresent(freelancerId, (id, f) -> f.withAvailability(newAvailability));
    }

    // ========== Task management ==========

    public Task createTask(String title, String description, Set<String> requiredSkills, double budget) {
        Objects.requireNonNull(title, "title");
        Objects.requireNonNull(requiredSkills, "requiredSkills");
        if (budget < 0) throw new IllegalArgumentException("budget must be >= 0");

        Task t = new Task(UUID.randomUUID(), title, description, new HashSet<>(requiredSkills), budget, TaskStatus.OPEN, null, Instant.now(), null);
        tasks.put(t.id, t);
        return t;
    }

    public Optional<Task> getTask(UUID taskId) {
        return Optional.ofNullable(tasks.get(taskId));
    }

    public List<Task> listTasks() {
        return new ArrayList<>(tasks.values());
    }

    public boolean assignTask(UUID taskId, UUID freelancerId) {
        Objects.requireNonNull(taskId, "taskId");
        Objects.requireNonNull(freelancerId, "freelancerId");
        Task t = tasks.get(taskId);
        Freelancer f = freelancers.get(freelancerId);
        if (t == null || f == null) return false;
        if (t.status != TaskStatus.OPEN) return false;
        // check skills
        boolean hasSkills = t.requiredSkills.stream().allMatch(req ->
                f.skills.stream().anyMatch(s -> s.equalsIgnoreCase(req))
        );
        if (!hasSkills) return false;
        // assign
        Task updated = t.withAssignment(freelancerId, TaskStatus.ASSIGNED, Instant.now());
        tasks.put(taskId, updated);
        return true;
    }

    public boolean completeTask(UUID taskId, double paymentAmount, int rating) {
        Objects.requireNonNull(taskId, "taskId");
        if (paymentAmount < 0) throw new IllegalArgumentException("paymentAmount must be >= 0");
        if (rating < 0 || rating > 5) throw new IllegalArgumentException("rating must be 0..5");

        Task t = tasks.get(taskId);
        if (t == null || t.status != TaskStatus.ASSIGNED || t.assignedFreelancerId == null) return false;

        // mark complete
        Task completed = t.withCompletion(TaskStatus.COMPLETED, Instant.now());
        tasks.put(taskId, completed);

        // record payment
        UUID fId = t.assignedFreelancerId;
        payments.computeIfAbsent(fId, k -> Collections.synchronizedList(new ArrayList<>()))
                .add(new PaymentRecord(UUID.randomUUID(), fId, taskId, paymentAmount, Instant.now()));

        // update freelancer stats (average rating and total earned)
        freelancers.computeIfPresent(fId, (id, fr) -> {
            double newTotal = fr.totalEarned + paymentAmount;
            int newCount = fr.ratingCount + 1;
            double newAvg = ((fr.averageRating * fr.ratingCount) + rating) / newCount;
            return fr.withRatingAndEarnings(newAvg, newTotal, newCount);
        });

        return true;
    }

    public List<PaymentRecord> getPaymentsForFreelancer(UUID freelancerId) {
        return new ArrayList<>(payments.getOrDefault(freelancerId, Collections.emptyList()));
    }

    public double totalPaidToFreelancer(UUID freelancerId) {
        return payments.getOrDefault(freelancerId, Collections.emptyList())
                .stream().mapToDouble(p -> p.amount).sum();
    }

    // ========== Simple matching helper ==========

    public List<Freelancer> suggestFreelancersForTask(UUID taskId, int maxResults) {
        Objects.requireNonNull(taskId, "taskId");
        Task t = tasks.get(taskId);
        if (t == null) return Collections.emptyList();
        List<Freelancer> candidates = freelancers.values().stream()
                .filter(f -> f.availability == Availability.AVAILABLE)
                .filter(f -> f.skills.stream().map(String::toLowerCase).collect(Collectors.toSet()).containsAll(
                        t.requiredSkills.stream().map(s -> s.toLowerCase(Locale.ROOT)).collect(Collectors.toSet())
                ))
                .sorted(Comparator.comparingDouble(Freelancer::getAverageRating).reversed()
                        .thenComparing(Freelancer::getTotalEarned)) // highest rated first
                .limit(Math.max(0, maxResults))
                .collect(Collectors.toList());
        return candidates;
    }

    // ========== Data classes ==========

    public enum Availability {
        AVAILABLE, BUSY, OFFLINE
    }

    public enum TaskStatus {
        OPEN, ASSIGNED, COMPLETED, CANCELLED
    }

    public static final class Freelancer {
        public final UUID id;
        public final String name;
        public final Set<String> skills;
        public final Availability availability;
        public final double totalEarned;
        public final int ratingCount;
        private final double averageRating;

        public Freelancer(UUID id, String name, Set<String> skills, Availability availability, double totalEarned, int ratingCount) {
            this.id = id;
            this.name = name;
            this.skills = Collections.unmodifiableSet(new HashSet<>(skills));
            this.availability = availability;
            this.totalEarned = totalEarned;
            this.ratingCount = ratingCount;
            this.averageRating = (ratingCount == 0) ? 0.0 : 0.0; // placeholder, updated using withRatingAndEarnings
        }

        private Freelancer(UUID id, String name, Set<String> skills, Availability availability, double totalEarned, int ratingCount, double averageRating) {
            this.id = id;
            this.name = name;
            this.skills = Collections.unmodifiableSet(new HashSet<>(skills));
            this.availability = availability;
            this.totalEarned = totalEarned;
            this.ratingCount = ratingCount;
            this.averageRating = averageRating;
        }

        public Freelancer withAvailability(Availability availability) {
            return new Freelancer(id, name, skills, availability, totalEarned, ratingCount, averageRating);
        }

        public Freelancer withRatingAndEarnings(double avgRating, double newTotalEarned, int newRatingCount) {
            return new Freelancer(id, name, skills, availability, newTotalEarned, newRatingCount, avgRating);
        }

        public double getAverageRating() {
            return averageRating;
        }

        public double getTotalEarned() {
            return totalEarned;
        }

        @Override
        public String toString() {
            return "Freelancer{" +
                    "id=" + id +
                    ", name='" + name + '\'' +
                    ", skills=" + skills +
                    ", availability=" + availability +
                    ", totalEarned=" + totalEarned +
                    ", averageRating=" + averageRating +
                    ", ratingCount=" + ratingCount +
                    '}';
        }
    }

    public static final class Task {
        public final UUID id;
        public final String title;
        public final String description;
        public final Set<String> requiredSkills;
        public final double budget;
        public final TaskStatus status;
        public final UUID assignedFreelancerId;
        public final Instant createdAt;
        public final Instant completedAt;

        public Task(UUID id, String title, String description, Set<String> requiredSkills, double budget,
                    TaskStatus status, UUID assignedFreelancerId, Instant createdAt, Instant completedAt) {
            this.id = id;
            this.title = title;
            this.description = description;
            this.requiredSkills = Collections.unmodifiableSet(new HashSet<>(requiredSkills));
            this.budget = budget;
            this.status = status;
            this.assignedFreelancerId = assignedFreelancerId;
            this.createdAt = createdAt;
            this.completedAt = completedAt;
        }

        public Task withAssignment(UUID freelancerId, TaskStatus newStatus, Instant assignedAt) {
            return new Task(id, title, description, requiredSkills, budget, newStatus, freelancerId, createdAt, null);
        }

        public Task withCompletion(TaskStatus newStatus, Instant completedAt) {
            return new Task(id, title, description, requiredSkills, budget, newStatus, assignedFreelancerId, createdAt, completedAt);
        }

        @Override
        public String toString() {
            return "Task{" +
                    "id=" + id +
                    ", title='" + title + '\'' +
                    ", requiredSkills=" + requiredSkills +
                    ", budget=" + budget +
                    ", status=" + status +
                    ", assigned=" + assignedFreelancerId +
                    ", createdAt=" + createdAt +
                    ", completedAt=" + completedAt +
                    '}';
        }
    }

    public static final class PaymentRecord {
        public final UUID id;
        public final UUID freelancerId;
        public final UUID taskId;
        public final double amount;
        public final Instant paidAt;

        public PaymentRecord(UUID id, UUID freelancerId, UUID taskId, double amount, Instant paidAt) {
            this.id = id;
            this.freelancerId = freelancerId;
            this.taskId = taskId;
            this.amount = amount;
            this.paidAt = paidAt;
        }

        @Override
        public String toString() {
            return "PaymentRecord{" +
                    "id=" + id +
                    ", freelancerId=" + freelancerId +
                    ", taskId=" + taskId +
                    ", amount=" + amount +
                    ", paidAt=" + paidAt +
                    '}';
        }
    }

    // ========== quick demo helper (not required) ==========

    public static void main(String[] args) {
        WorkManager mgr = new WorkManager();
        Freelancer alice = mgr.registerFreelancer("Alice", new HashSet<>(Arrays.asList("java", "spring")), Availability.AVAILABLE);
        Freelancer bob = mgr.registerFreelancer("Bob", new HashSet<>(Arrays.asList("javascript", "react")), Availability.AVAILABLE);

        Task t1 = mgr.createTask("Implement backend", "REST API", new HashSet<>(Arrays.asList("java", "spring")), 1200);
        boolean assigned = mgr.assignTask(t1.id, alice.id);
        System.out.println("Assigned t1 to Alice: " + assigned);

        mgr.completeTask(t1.id, 1200, 5);
        System.out.println("Alice payments: " + mgr.getPaymentsForFreelancer(alice.id));
        System.out.println("Alice profile: " + mgr.getFreelancer(alice.id).orElse(null));
    }
}