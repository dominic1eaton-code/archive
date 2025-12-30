/**
 * @license
 * @brief
 * @copyright
 */
import java.io.Serializable;
import java.time.LocalDate;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.UUID;

package com.project;


/**
 * Simple Project model.
 */
public class Project implements Serializable {
    private static final long serialVersionUID = 1L;

    public enum Status {
        PLANNED,
        ACTIVE,
        ON_HOLD,
        COMPLETED,
        CANCELLED
    }

    private final UUID id;
    private String name;
    private String description;
    private LocalDate startDate;
    private LocalDate endDate;
    private Status status;
    private final List<String> members = new ArrayList<>();

    public Project(String name) {
        this(UUID.randomUUID(), name, null, null, Status.PLANNED, null);
    }

    public Project(UUID id, String name) {
        this(id, name, null, null, Status.PLANNED, null);
    }

    public Project(String name, String description, LocalDate startDate, LocalDate endDate, Status status) {
        this(UUID.randomUUID(), name, description, startDate, endDate, status, null);
    }

    public Project(UUID id, String name, String description, LocalDate startDate, LocalDate endDate, Status status, List<String> members) {
        this.id = Objects.requireNonNull(id, "id");
        setName(name);
        this.description = description;
        setStartDate(startDate);
        setEndDate(endDate);
        this.status = status == null ? Status.PLANNED : status;
        if (members != null) {
            this.members.addAll(members);
        }
    }

    public UUID getId() {
        return id;
    }

    public String getName() {
        return name;
    }

    public final void setName(String name) {
        this.name = Objects.requireNonNull(name, "name");
    }

    public String getDescription() {
        return description;
    }

    public void setDescription(String description) {
        this.description = description;
    }

    public LocalDate getStartDate() {
        return startDate;
    }

    public final void setStartDate(LocalDate startDate) {
        if (startDate != null && this.endDate != null && startDate.isAfter(this.endDate)) {
            throw new IllegalArgumentException("startDate cannot be after endDate");
        }
        this.startDate = startDate;
    }

    public LocalDate getEndDate() {
        return endDate;
    }

    public final void setEndDate(LocalDate endDate) {
        if (endDate != null && this.startDate != null && endDate.isBefore(this.startDate)) {
            throw new IllegalArgumentException("endDate cannot be before startDate");
        }
        this.endDate = endDate;
    }

    public Status getStatus() {
        return status;
    }

    public void setStatus(Status status) {
        this.status = status == null ? Status.PLANNED : status;
    }

    public List<String> getMembers() {
        return Collections.unmodifiableList(members);
    }

    public boolean addMember(String member) {
        if (member == null || member.trim().isEmpty()) return false;
        return members.add(member.trim());
    }

    public boolean removeMember(String member) {
        return members.remove(member);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        Project project = (Project) o;
        return id.equals(project.id);
    }

    @Override
    public int hashCode() {
        return id.hashCode();
    }

    @Override
    public String toString() {
        return "Project{" +
                "id=" + id +
                ", name='" + name + '\'' +
                (description != null ? ", description='" + description + '\'' : "") +
                (startDate != null ? ", startDate=" + startDate : "") +
                (endDate != null ? ", endDate=" + endDate : "") +
                ", status=" + status +
                ", members=" + members +
                '}';
    }
}