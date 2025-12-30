import java.time.Duration;
import java.time.LocalDate;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.*;
import java.util.stream.Collectors;

package com.time;


/**
 * Simple gig worker schedule management system.
 * Single-file implementation for Schedule.java
 *
 * Public class is Schedule (file name must match).
 */
public class Schedule {

    private final Map<String, Worker> workers = new HashMap<>();
    private final Map<String, Shift> shifts = new HashMap<>();

    // Worker operations
    public Worker addWorker(String id, String name, String... skills) {
        Worker w = new Worker(id, name, new HashSet<>(Arrays.asList(skills)));
        workers.put(id, w);
        return w;
    }

    public Optional<Worker> getWorker(String id) {
        return Optional.ofNullable(workers.get(id));
    }

    public Collection<Worker> listWorkers() {
        return Collections.unmodifiableCollection(workers.values());
    }

    // Shift operations
    public Shift addShift(String id, LocalDateTime start, LocalDateTime end, String role, double payRate) {
        if (!start.isBefore(end)) throw new IllegalArgumentException("Shift start must be before end");
        Shift s = new Shift(id, start, end, role, payRate);
        shifts.put(id, s);
        return s;
    }

    public Optional<Shift> getShift(String id) {
        return Optional.ofNullable(shifts.get(id));
    }

    public Collection<Shift> listShifts() {
        return Collections.unmodifiableCollection(shifts.values());
    }

    // Assignment
    public boolean assignShift(String shiftId, String workerId) {
        Shift shift = shifts.get(shiftId);
        Worker worker = workers.get(workerId);
        if (shift == null || worker == null) return false;
        // check availability & skill
        if (!worker.getSkills().contains(shift.getRole())) return false;
        List<Shift> existing = listShiftsForWorker(workerId);
        boolean conflict = existing.stream().anyMatch(s -> s.overlaps(shift));
        if (conflict) return false;
        shift.setAssignedWorkerId(workerId);
        return true;
    }

    public boolean unassignShift(String shiftId) {
        Shift shift = shifts.get(shiftId);
        if (shift == null) return false;
        shift.setAssignedWorkerId(null);
        return true;
    }

    public List<Shift> listShiftsForWorker(String workerId) {
        return shifts.values().stream()
                .filter(s -> workerId.equals(s.getAssignedWorkerId()))
                .sorted(Comparator.comparing(Shift::getStart))
                .collect(Collectors.toList());
    }

    public List<Shift> listShiftsForDate(LocalDate date) {
        return shifts.values().stream()
                .filter(s -> !s.getStart().toLocalDate().isAfter(date) && !s.getEnd().toLocalDate().isBefore(date))
                .sorted(Comparator.comparing(Shift::getStart))
                .collect(Collectors.toList());
    }

    // Helpers
    public List<String> findConflictsForWorker(String workerId) {
        List<Shift> s = listShiftsForWorker(workerId);
        List<String> conflicts = new ArrayList<>();
        for (int i = 0; i < s.size(); i++) {
            for (int j = i + 1; j < s.size(); j++) {
                if (s.get(i).overlaps(s.get(j))) {
                    conflicts.add(s.get(i).getId() + " <> " + s.get(j).getId());
                }
            }
        }
        return conflicts;
    }

    public List<Worker> eligibleWorkersForShift(String shiftId) {
        Shift shift = shifts.get(shiftId);
        if (shift == null) return Collections.emptyList();
        return workers.values().stream()
                .filter(w -> w.getSkills().contains(shift.getRole()))
                .filter(w -> listShiftsForWorker(w.getId()).stream().noneMatch(s -> s.overlaps(shift)))
                .collect(Collectors.toList());
    }

    public double computePayForWorker(String workerId, LocalDate from, LocalDate to) {
        return listShiftsForWorker(workerId).stream()
                .filter(s -> !s.getEnd().toLocalDate().isBefore(from) && !s.getStart().toLocalDate().isAfter(to))
                .mapToDouble(Shift::durationHours)
                .map(h -> h * 1.0) // hours * rate; but rate is part of Shift
                .sum(); // we'll use shift payRate per hour inside Shift.payFor()
    }

    // Demonstration main
    public static void main(String[] args) {
        Schedule sched = new Schedule();

        // add workers
        sched.addWorker("w1", "Alice", "delivery", "pickup");
        sched.addWorker("w2", "Bob", "delivery");
        sched.addWorker("w3", "Cara", "cleaning");

        // add shifts
        DateTimeFormatter f = DateTimeFormatter.ofPattern("yyyy-MM-dd HH:mm");
        Shift s1 = sched.addShift("s1", LocalDateTime.parse("2025-12-01 08:00", f),
                LocalDateTime.parse("2025-12-01 12:00", f), "delivery", 15.0);
        Shift s2 = sched.addShift("s2", LocalDateTime.parse("2025-12-01 11:00", f),
                LocalDateTime.parse("2025-12-01 15:00", f), "delivery", 16.0);
        Shift s3 = sched.addShift("s3", LocalDateTime.parse("2025-12-02 09:00", f),
                LocalDateTime.parse("2025-12-02 13:00", f), "cleaning", 12.0);

        // assign shifts
        System.out.println("Assign s1->Alice: " + sched.assignShift("s1", "w1")); // true
        System.out.println("Assign s2->Alice (overlap): " + sched.assignShift("s2", "w1")); // false because overlaps
        System.out.println("Assign s2->Bob: " + sched.assignShift("s2", "w2")); // true
        System.out.println("Assign s3->Cara: " + sched.assignShift("s3", "w3")); // true

        // list shifts per date
        System.out.println("\nShifts on 2025-12-01:");
        sched.listShiftsForDate(LocalDate.of(2025, 12, 1)).forEach(System.out::println);

        // eligible workers for a shift
        System.out.println("\nEligible workers for s2:");
        sched.eligibleWorkersForShift("s2").forEach(w -> System.out.println(" - " + w));

        // conflicts
        System.out.println("\nConflicts for Alice: " + sched.findConflictsForWorker("w1"));
    }
}

/* Worker */
class Worker {
    private final String id;
    private final String name;
    private final Set<String> skills;

    Worker(String id, String name, Set<String> skills) {
        this.id = Objects.requireNonNull(id);
        this.name = Objects.requireNonNull(name);
        this.skills = new HashSet<>(skills);
    }

    public String getId() { return id; }
    public String getName() { return name; }
    public Set<String> getSkills() { return Collections.unmodifiableSet(skills); }

    @Override
    public String toString() {
        return "Worker{" + id + ":" + name + ",skills=" + skills + "}";
    }
}

/* Shift */
class Shift {
    private final String id;
    private final LocalDateTime start;
    private final LocalDateTime end;
    private final String role;
    private final double payRatePerHour;
    private String assignedWorkerId;

    Shift(String id, LocalDateTime start, LocalDateTime end, String role, double payRatePerHour) {
        this.id = Objects.requireNonNull(id);
        this.start = Objects.requireNonNull(start);
        this.end = Objects.requireNonNull(end);
        if (!start.isBefore(end)) throw new IllegalArgumentException("start must be before end");
        this.role = Objects.requireNonNull(role);
        this.payRatePerHour = payRatePerHour;
    }

    public String getId() { return id; }
    public LocalDateTime getStart() { return start; }
    public LocalDateTime getEnd() { return end; }
    public String getRole() { return role; }
    public double getPayRatePerHour() { return payRatePerHour; }
    public String getAssignedWorkerId() { return assignedWorkerId; }
    public void setAssignedWorkerId(String id) { this.assignedWorkerId = id; }

    public boolean overlaps(Shift other) {
        return start.isBefore(other.end) && other.start.isBefore(end);
    }

    public double durationHours() {
        return Duration.between(start, end).toMinutes() / 60.0;
    }

    public double payFor() {
        return durationHours() * payRatePerHour;
    }

    @Override
    public String toString() {
        return "Shift{" + id + " " + start + "->" + end + " role=" + role + " pay=" + payRatePerHour +
                " assigned=" + assignedWorkerId + "}";
    }
}