import java.io.Serializable;
import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.UUID;

package com.portal;


/**
 * Represents a gig worker profile.
 * Designed for easy construction via Builder and simple lifecycle updates.
 */
public class Profile implements Serializable {
    private static final long serialVersionUID = 1L;

    private final UUID id;
    private String firstName;
    private String lastName;
    private String displayName;
    private String email;
    private String phone;
    private String bio;
    private List<String> skills;
    private double rating;           // average rating, 0.0 - 5.0
    private int completedJobs;
    private double hourlyRate;
    private String currency;
    private String location;
    private boolean available;
    private final LocalDateTime createdAt;
    private LocalDateTime updatedAt;

    private Profile(Builder b) {
        this.id = b.id != null ? b.id : UUID.randomUUID();
        this.firstName = b.firstName;
        this.lastName = b.lastName;
        this.displayName = b.displayName != null ? b.displayName : deriveDisplayName(b.firstName, b.lastName);
        this.email = b.email;
        this.phone = b.phone;
        this.bio = b.bio;
        this.skills = b.skills != null ? new ArrayList<>(b.skills) : new ArrayList<>();
        this.rating = sanitizeRating(b.rating);
        this.completedJobs = Math.max(0, b.completedJobs);
        this.hourlyRate = Math.max(0.0, b.hourlyRate);
        this.currency = b.currency != null ? b.currency : "USD";
        this.location = b.location;
        this.available = b.available;
        this.createdAt = b.createdAt != null ? b.createdAt : LocalDateTime.now();
        this.updatedAt = this.createdAt;
    }

    private static String deriveDisplayName(String first, String last) {
        if (first == null && last == null) return "Unknown";
        if (first == null) return last;
        if (last == null) return first;
        return first + " " + last;
    }

    private static double sanitizeRating(double r) {
        if (Double.isNaN(r) || r < 0.0) return 0.0;
        return Math.min(5.0, r);
    }

    // --- Builder ---
    public static class Builder {
        private UUID id;
        private String firstName;
        private String lastName;
        private String displayName;
        private String email;
        private String phone;
        private String bio;
        private List<String> skills;
        private double rating;
        private int completedJobs;
        private double hourlyRate;
        private String currency;
        private String location;
        private boolean available = true;
        private LocalDateTime createdAt;

        public Builder id(UUID id) { this.id = id; return this; }
        public Builder firstName(String firstName) { this.firstName = firstName; return this; }
        public Builder lastName(String lastName) { this.lastName = lastName; return this; }
        public Builder displayName(String displayName) { this.displayName = displayName; return this; }
        public Builder email(String email) { this.email = email; return this; }
        public Builder phone(String phone) { this.phone = phone; return this; }
        public Builder bio(String bio) { this.bio = bio; return this; }
        public Builder skills(List<String> skills) { this.skills = skills; return this; }
        public Builder rating(double rating) { this.rating = rating; return this; }
        public Builder completedJobs(int completedJobs) { this.completedJobs = completedJobs; return this; }
        public Builder hourlyRate(double hourlyRate) { this.hourlyRate = hourlyRate; return this; }
        public Builder currency(String currency) { this.currency = currency; return this; }
        public Builder location(String location) { this.location = location; return this; }
        public Builder available(boolean available) { this.available = available; return this; }
        public Builder createdAt(LocalDateTime createdAt) { this.createdAt = createdAt; return this; }

        public Profile build() {
            // basic validation
            if (email != null && !email.contains("@")) {
                throw new IllegalArgumentException("email must be valid or null");
            }
            return new Profile(this);
        }
    }

    // --- Getters ---
    public UUID getId() { return id; }
    public String getFirstName() { return firstName; }
    public String getLastName() { return lastName; }
    public String getDisplayName() { return displayName; }
    public String getEmail() { return email; }
    public String getPhone() { return phone; }
    public String getBio() { return bio; }
    public List<String> getSkills() { return Collections.unmodifiableList(skills); }
    public double getRating() { return rating; }
    public int getCompletedJobs() { return completedJobs; }
    public double getHourlyRate() { return hourlyRate; }
    public String getCurrency() { return currency; }
    public String getLocation() { return location; }
    public boolean isAvailable() { return available; }
    public LocalDateTime getCreatedAt() { return createdAt; }
    public LocalDateTime getUpdatedAt() { return updatedAt; }

    // --- Mutating utilities ---
    public synchronized void addSkill(String skill) {
        if (skill == null || skill.isBlank()) return;
        if (!skills.contains(skill)) {
            skills.add(skill);
            touch();
        }
    }

    public synchronized void removeSkill(String skill) {
        if (skills.remove(skill)) touch();
    }

    public synchronized void updateContact(String email, String phone) {
        if (email != null && !email.contains("@")) throw new IllegalArgumentException("invalid email");
        this.email = email;
        this.phone = phone;
        touch();
    }

    /**
     * Record completion of a job and incorporate a new rating into the average.
     * Thread-safe.
     */
    public synchronized void recordCompletedJobWithRating(double jobRating) {
        if (jobRating < 0.0) jobRating = 0.0;
        if (jobRating > 5.0) jobRating = 5.0;
        double totalScore = this.rating * this.completedJobs;
        this.completedJobs++;
        this.rating = (totalScore + jobRating) / this.completedJobs;
        touch();
    }

    public synchronized void setHourlyRate(double hourlyRate, String currency) {
        if (hourlyRate < 0) throw new IllegalArgumentException("hourlyRate must be >= 0");
        this.hourlyRate = hourlyRate;
        if (currency != null) this.currency = currency;
        touch();
    }

    public synchronized void setAvailability(boolean available) {
        this.available = available;
        touch();
    }

    public synchronized void updateLocation(String location) {
        this.location = location;
        touch();
    }

    public synchronized void updateBio(String bio) {
        this.bio = bio;
        touch();
    }

    private void touch() {
        this.updatedAt = LocalDateTime.now();
    }

    // --- equals / hashCode / toString ---
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof Profile)) return false;
        Profile p = (Profile) o;
        return Objects.equals(id, p.id);
    }

    @Override
    public int hashCode() {
        return Objects.hashCode(id);
    }

    @Override
    public String toString() {
        return "Profile{" +
                "id=" + id +
                ", displayName='" + displayName + '\'' +
                ", email='" + email + '\'' +
                ", skills=" + skills +
                ", rating=" + rating +
                ", completedJobs=" + completedJobs +
                ", hourlyRate=" + hourlyRate + " " + currency +
                ", location='" + location + '\'' +
                ", available=" + available +
                ", createdAt=" + createdAt +
                ", updatedAt=" + updatedAt +
                '}';
    }
}