import java.io.BufferedReader;
import java.io.IOException;
import java.io.StringReader;
import java.time.LocalDate;
import java.util.Collections;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.UUID;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.locks.ReentrantReadWriteLock;
import java.util.stream.Collectors;

package com.pbms;


/**
 * Portable Benefits Management System (PBMS)
 *
 * Single-file, dependency-free, thread-safe manager for basic benefits operations:
 * - Manage employees and benefit plans
 * - Enroll and cancel enrollments
 * - Compute monthly cost for an employee
 * - Export / import a compact textual state format (PBMSv1)
 *
 * Place in: com.pbms.Pbms
 */
public class Pbms {

    private final Map<String, Employee> employees = new ConcurrentHashMap<>();
    private final Map<String, BenefitPlan> plans = new ConcurrentHashMap<>();
    private final Map<String, Enrollment> enrollments = new ConcurrentHashMap<>();
    private final ReentrantReadWriteLock lock = new ReentrantReadWriteLock();

    public Pbms() {
    }

    // Employee operations
    public Employee addEmployee(String id, String name, LocalDate dateOfBirth, String department) {
        Objects.requireNonNull(id, "id");
        Objects.requireNonNull(name, "name");
        Objects.requireNonNull(dateOfBirth, "dateOfBirth");
        Objects.requireNonNull(department, "department");
        Employee e = new Employee(id, name, dateOfBirth, department);
        lock.writeLock().lock();
        try {
            employees.put(id, e);
        } finally {
            lock.writeLock().unlock();
        }
        return e;
    }

    public Employee getEmployee(String id) {
        lock.readLock().lock();
        try {
            return employees.get(id);
        } finally {
            lock.readLock().unlock();
        }
    }

    // Plan operations
    public BenefitPlan addPlan(String id, String name, double monthlyPremium, Set<String> eligibleDepartments) {
        Objects.requireNonNull(id, "id");
        Objects.requireNonNull(name, "name");
        if (monthlyPremium < 0) throw new IllegalArgumentException("monthlyPremium must be >= 0");
        BenefitPlan p = new BenefitPlan(id, name, monthlyPremium, eligibleDepartments == null ? Collections.emptySet() : eligibleDepartments);
        lock.writeLock().lock();
        try {
            plans.put(id, p);
        } finally {
            lock.writeLock().unlock();
        }
        return p;
    }

    public BenefitPlan getPlan(String id) {
        lock.readLock().lock();
        try {
            return plans.get(id);
        } finally {
            lock.readLock().unlock();
        }
    }

    // Enrollment operations
    public Enrollment enroll(String employeeId, String planId, LocalDate effectiveDate) {
        Objects.requireNonNull(employeeId, "employeeId");
        Objects.requireNonNull(planId, "planId");
        Objects.requireNonNull(effectiveDate, "effectiveDate");

        lock.writeLock().lock();
        try {
            Employee e = employees.get(employeeId);
            BenefitPlan p = plans.get(planId);
            if (e == null) throw new IllegalArgumentException("employee not found: " + employeeId);
            if (p == null) throw new IllegalArgumentException("plan not found: " + planId);
            if (!p.isEligible(e)) throw new IllegalStateException("employee not eligible for plan");

            String id = UUID.randomUUID().toString();
            Enrollment en = new Enrollment(id, employeeId, planId, effectiveDate);
            enrollments.put(id, en);
            return en;
        } finally {
            lock.writeLock().unlock();
        }
    }

    public boolean cancelEnrollment(String enrollmentId, LocalDate cancelDate) {
        Objects.requireNonNull(enrollmentId, "enrollmentId");
        Objects.requireNonNull(cancelDate, "cancelDate");
        lock.writeLock().lock();
        try {
            Enrollment en = enrollments.get(enrollmentId);
            if (en == null) return false;
            if (en.status != EnrollmentStatus.ACTIVE) return false;
            if (cancelDate.isBefore(en.effectiveDate)) return false;
            en.cancelDate = cancelDate;
            en.status = EnrollmentStatus.CANCELLED;
            return true;
        } finally {
            lock.writeLock().unlock();
        }
    }

    public Enrollment getEnrollment(String id) {
        lock.readLock().lock();
        try {
            return enrollments.get(id);
        } finally {
            lock.readLock().unlock();
        }
    }

    // Compute monthly cost for an employee (sum of plan premiums for active enrollments)
    public double calculateMonthlyCost(String employeeId, LocalDate asOfDate) {
        Objects.requireNonNull(employeeId, "employeeId");
        Objects.requireNonNull(asOfDate, "asOfDate");
        lock.readLock().lock();
        try {
            return enrollments.values().stream()
                    .filter(en -> en.employeeId.equals(employeeId))
                    .filter(en -> en.isActiveOn(asOfDate))
                    .mapToDouble(en -> {
                        BenefitPlan p = plans.get(en.planId);
                        return p == null ? 0.0 : p.monthlyPremium;
                    })
                    .sum();
        } finally {
            lock.readLock().unlock();
        }
    }

    // List eligible plans for an employee
    public Set<BenefitPlan> listEligiblePlans(String employeeId) {
        Objects.requireNonNull(employeeId, "employeeId");
        lock.readLock().lock();
        try {
            Employee e = employees.get(employeeId);
            if (e == null) return Collections.emptySet();
            return plans.values().stream()
                    .filter(p -> p.isEligible(e))
                    .collect(Collectors.toSet());
        } finally {
            lock.readLock().unlock();
        }
    }

    // Export state in a compact textual PBMSv1 format. This format is simple and portable.
    public String exportState() {
        StringBuilder sb = new StringBuilder();
        lock.readLock().lock();
        try {
            sb.append("#PBMSv1\n");
            sb.append("#EMPLOYEES\n");
            for (Employee e : employees.values()) {
                sb.append(escape(e.id)).append('|')
                        .append(escape(e.name)).append('|')
                        .append(e.dateOfBirth.toString()).append('|')
                        .append(escape(e.department)).append('\n');
            }
            sb.append("#PLANS\n");
            for (BenefitPlan p : plans.values()) {
                sb.append(escape(p.id)).append('|')
                        .append(escape(p.name)).append('|')
                        .append(p.monthlyPremium).append('|')
                        .append(escape(String.join(",", p.eligibleDepartments))).append('\n');
            }
            sb.append("#ENROLLMENTS\n");
            for (Enrollment en : enrollments.values()) {
                sb.append(escape(en.id)).append('|')
                        .append(escape(en.employeeId)).append('|')
                        .append(escape(en.planId)).append('|')
                        .append(en.effectiveDate.toString()).append('|')
                        .append(en.cancelDate == null ? "" : en.cancelDate.toString()).append('|')
                        .append(en.status.name()).append('\n');
            }
            return sb.toString();
        } finally {
            lock.readLock().unlock();
        }
    }

    // Import state in PBMSv1 format previously exported by exportState.
    public void importState(String data) throws IOException {
        Objects.requireNonNull(data, "data");
        lock.writeLock().lock();
        try (BufferedReader r = new BufferedReader(new StringReader(data))) {
            String line;
            String section = "";
            while ((line = r.readLine()) != null) {
                line = line.trim();
                if (line.isEmpty() || line.startsWith("#PBMSv1")) continue;
                if (line.startsWith("#")) {
                    section = line.substring(1).trim().toUpperCase();
                    continue;
                }
                String[] parts = splitPipe(line);
                switch (section) {
                    case "EMPLOYEES":
                        if (parts.length >= 4) {
                            String id = unescape(parts[0]);
                            String name = unescape(parts[1]);
                            LocalDate dob = LocalDate.parse(parts[2]);
                            String dept = unescape(parts[3]);
                            employees.put(id, new Employee(id, name, dob, dept));
                        }
                        break;
                    case "PLANS":
                        if (parts.length >= 4) {
                            String id = unescape(parts[0]);
                            String name = unescape(parts[1]);
                            double premium = Double.parseDouble(parts[2]);
                            Set<String> eligible = Collections.emptySet();
                            String rawEligible = unescape(parts[3]);
                            if (!rawEligible.isEmpty()) {
                                eligible = Collections.unmodifiableSet(
                                        java.util.Arrays.stream(rawEligible.split(","))
                                                .map(String::trim).filter(s -> !s.isEmpty()).collect(Collectors.toSet()));
                            }
                            plans.put(id, new BenefitPlan(id, name, premium, eligible));
                        }
                        break;
                    case "ENROLLMENTS":
                        if (parts.length >= 6) {
                            String id = unescape(parts[0]);
                            String empId = unescape(parts[1]);
                            String planId = unescape(parts[2]);
                            LocalDate eff = LocalDate.parse(parts[3]);
                            LocalDate cancel = parts[4].isEmpty() ? null : LocalDate.parse(parts[4]);
                            EnrollmentStatus status = EnrollmentStatus.valueOf(parts[5]);
                            Enrollment en = new Enrollment(id, empId, planId, eff);
                            en.cancelDate = cancel;
                            en.status = status;
                            enrollments.put(id, en);
                        }
                        break;
                    default:
                        // ignore unknown
                }
            }
        } finally {
            lock.writeLock().unlock();
        }
    }

    // Utility for splitting a line by '|' preserving empty trailing fields
    private static String[] splitPipe(String line) {
        return line.split("\\|", -1);
    }

    private static String escape(String s) {
        if (s == null) return "";
        return s.replace("\\", "\\\\").replace("|", "\\|").replace("\n", "\\n").replace("\r", "\\r");
    }

    private static String unescape(String s) {
        if (s == null) return "";
        StringBuilder sb = new StringBuilder();
        boolean esc = false;
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            if (esc) {
                switch (c) {
                    case '\\':
                        sb.append('\\');
                        break;
                    case '|':
                        sb.append('|');
                        break;
                    case 'n':
                        sb.append('\n');
                        break;
                    case 'r':
                        sb.append('\r');
                        break;
                    default:
                        sb.append(c);
                }
                esc = false;
            } else if (c == '\\') {
                esc = true;
            } else {
                sb.append(c);
            }
        }
        if (esc) sb.append('\\');
        return sb.toString();
    }

    // --- Data classes ---

    public static final class Employee {
        public final String id;
        public final String name;
        public final LocalDate dateOfBirth;
        public final String department;

        public Employee(String id, String name, LocalDate dateOfBirth, String department) {
            this.id = Objects.requireNonNull(id);
            this.name = Objects.requireNonNull(name);
            this.dateOfBirth = Objects.requireNonNull(dateOfBirth);
            this.department = Objects.requireNonNull(department);
        }

        @Override
        public String toString() {
            return "Employee{" + id + "," + name + "," + dateOfBirth + "," + department + '}';
        }
    }

    public static final class BenefitPlan {
        public final String id;
        public final String name;
        public final double monthlyPremium;
        public final Set<String> eligibleDepartments;

        public BenefitPlan(String id, String name, double monthlyPremium, Set<String> eligibleDepartments) {
            this.id = Objects.requireNonNull(id);
            this.name = Objects.requireNonNull(name);
            this.monthlyPremium = monthlyPremium;
            this.eligibleDepartments = eligibleDepartments == null ? Collections.emptySet() : Collections.unmodifiableSet(eligibleDepartments);
        }

        public boolean isEligible(Employee e) {
            if (eligibleDepartments.isEmpty()) return true;
            return eligibleDepartments.contains(e.department);
        }

        @Override
        public String toString() {
            return "Plan{" + id + "," + name + "," + monthlyPremium + "," + eligibleDepartments + '}';
        }
    }

    public static final class Enrollment {
        public final String id;
        public final String employeeId;
        public final String planId;
        public final LocalDate effectiveDate;
        public volatile LocalDate cancelDate;
        public volatile EnrollmentStatus status;

        Enrollment(String id, String employeeId, String planId, LocalDate effectiveDate) {
            this.id = Objects.requireNonNull(id);
            this.employeeId = Objects.requireNonNull(employeeId);
            this.planId = Objects.requireNonNull(planId);
            this.effectiveDate = Objects.requireNonNull(effectiveDate);
            this.cancelDate = null;
            this.status = EnrollmentStatus.ACTIVE;
        }

        public boolean isActiveOn(LocalDate asOf) {
            if (asOf.isBefore(effectiveDate)) return false;
            if (status == EnrollmentStatus.CANCELLED && cancelDate != null && (asOf.isAfter(cancelDate) || asOf.isEqual(cancelDate) == false && asOf.isAfter(cancelDate))) {
                // if canceled before or on asOf (we treat cancelDate as last effective day: inclusive)
                return asOf.isBefore(cancelDate) || asOf.isEqual(cancelDate);
            }
            return status == EnrollmentStatus.ACTIVE || (status == EnrollmentStatus.CANCELLED && (cancelDate == null || !asOf.isAfter(cancelDate)));
        }

        @Override
        public String toString() {
            return "Enrollment{" + id + "," + employeeId + "," + planId + "," + effectiveDate + "," + cancelDate + "," + status + '}';
        }
    }

    public enum EnrollmentStatus {
        ACTIVE,
        CANCELLED
    }
}