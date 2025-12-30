import java.io.Serializable;
import java.time.LocalDate;
import java.time.LocalDateTime;
import java.util.*;

package com.app;


/**
 * Simple portfolio profile model.
 * Designed to be stored/serialized by callers; contains small nested models for projects, experience and education.
 */
public class Profile implements Serializable {
    private static final long serialVersionUID = 1L;

    private String id;
    private String fullName;
    private String headline;
    private String summary;
    private String email;
    private String phone;
    private String location;
    private List<String> skills;
    private List<Project> projects;
    private List<Experience> experiences;
    private List<Education> educations;
    private Map<String, String> socialLinks;
    private LocalDateTime createdAt;
    private LocalDateTime updatedAt;

    public Profile() {
        this.skills = new ArrayList<>();
        this.projects = new ArrayList<>();
        this.experiences = new ArrayList<>();
        this.educations = new ArrayList<>();
        this.socialLinks = new LinkedHashMap<>();
        this.createdAt = LocalDateTime.now();
        this.updatedAt = createdAt;
    }

    private Profile(Builder b) {
        this.id = b.id;
        this.fullName = b.fullName;
        this.headline = b.headline;
        this.summary = b.summary;
        this.email = b.email;
        this.phone = b.phone;
        this.location = b.location;
        this.skills = new ArrayList<>(b.skills);
        this.projects = new ArrayList<>(b.projects);
        this.experiences = new ArrayList<>(b.experiences);
        this.educations = new ArrayList<>(b.educations);
        this.socialLinks = new LinkedHashMap<>(b.socialLinks);
        this.createdAt = b.createdAt != null ? b.createdAt : LocalDateTime.now();
        this.updatedAt = b.updatedAt != null ? b.updatedAt : this.createdAt;
    }

    /* Builder */
    public static Builder builder() {
        return new Builder();
    }

    public static final class Builder {
        private String id;
        private String fullName;
        private String headline;
        private String summary;
        private String email;
        private String phone;
        private String location;
        private List<String> skills = new ArrayList<>();
        private List<Project> projects = new ArrayList<>();
        private List<Experience> experiences = new ArrayList<>();
        private List<Education> educations = new ArrayList<>();
        private Map<String, String> socialLinks = new LinkedHashMap<>();
        private LocalDateTime createdAt;
        private LocalDateTime updatedAt;

        private Builder() {}

        public Builder id(String id) { this.id = id; return this; }
        public Builder fullName(String fullName) { this.fullName = fullName; return this; }
        public Builder headline(String headline) { this.headline = headline; return this; }
        public Builder summary(String summary) { this.summary = summary; return this; }
        public Builder email(String email) { this.email = email; return this; }
        public Builder phone(String phone) { this.phone = phone; return this; }
        public Builder location(String location) { this.location = location; return this; }
        public Builder skills(List<String> skills) { this.skills = new ArrayList<>(skills); return this; }
        public Builder addSkill(String skill) { this.skills.add(skill); return this; }
        public Builder projects(List<Project> projects) { this.projects = new ArrayList<>(projects); return this; }
        public Builder addProject(Project project) { this.projects.add(project); return this; }
        public Builder experiences(List<Experience> experiences) { this.experiences = new ArrayList<>(experiences); return this; }
        public Builder addExperience(Experience e) { this.experiences.add(e); return this; }
        public Builder educations(List<Education> educations) { this.educations = new ArrayList<>(educations); return this; }
        public Builder addEducation(Education e) { this.educations.add(e); return this; }
        public Builder socialLinks(Map<String, String> links) { this.socialLinks = new LinkedHashMap<>(links); return this; }
        public Builder addSocialLink(String key, String url) { this.socialLinks.put(key, url); return this; }
        public Builder createdAt(LocalDateTime createdAt) { this.createdAt = createdAt; return this; }
        public Builder updatedAt(LocalDateTime updatedAt) { this.updatedAt = updatedAt; return this; }

        public Profile build() { return new Profile(this); }
    }

    /* Basic mutators */
    public String getId() { return id; }
    public void setId(String id) { this.id = id; touch(); }

    public String getFullName() { return fullName; }
    public void setFullName(String fullName) { this.fullName = fullName; touch(); }

    public String getHeadline() { return headline; }
    public void setHeadline(String headline) { this.headline = headline; touch(); }

    public String getSummary() { return summary; }
    public void setSummary(String summary) { this.summary = summary; touch(); }

    public String getEmail() { return email; }
    public void setEmail(String email) { this.email = email; touch(); }

    public String getPhone() { return phone; }
    public void setPhone(String phone) { this.phone = phone; touch(); }

    public String getLocation() { return location; }
    public void setLocation(String location) { this.location = location; touch(); }

    public List<String> getSkills() { return Collections.unmodifiableList(skills); }
    public void setSkills(Collection<String> skills) { this.skills = new ArrayList<>(skills); touch(); }
    public void addSkill(String skill) { this.skills.add(skill); touch(); }
    public boolean removeSkill(String skill) { boolean r = this.skills.remove(skill); if (r) touch(); return r; }

    public List<Project> getProjects() { return Collections.unmodifiableList(projects); }
    public void setProjects(Collection<Project> projects) { this.projects = new ArrayList<>(projects); touch(); }
    public void addProject(Project project) { this.projects.add(project); touch(); }
    public boolean removeProject(Project project) { boolean r = this.projects.remove(project); if (r) touch(); return r; }

    public List<Experience> getExperiences() { return Collections.unmodifiableList(experiences); }
    public void setExperiences(Collection<Experience> experiences) { this.experiences = new ArrayList<>(experiences); touch(); }
    public void addExperience(Experience e) { this.experiences.add(e); touch(); }
    public boolean removeExperience(Experience e) { boolean r = this.experiences.remove(e); if (r) touch(); return r; }

    public List<Education> getEducations() { return Collections.unmodifiableList(educations); }
    public void setEducations(Collection<Education> educations) { this.educations = new ArrayList<>(educations); touch(); }
    public void addEducation(Education e) { this.educations.add(e); touch(); }
    public boolean removeEducation(Education e) { boolean r = this.educations.remove(e); if (r) touch(); return r; }

    public Map<String, String> getSocialLinks() { return Collections.unmodifiableMap(socialLinks); }
    public void setSocialLinks(Map<String, String> socialLinks) { this.socialLinks = new LinkedHashMap<>(socialLinks); touch(); }
    public void addSocialLink(String provider, String url) { this.socialLinks.put(provider, url); touch(); }
    public String removeSocialLink(String provider) { String r = this.socialLinks.remove(provider); if (r != null) touch(); return r; }

    public LocalDateTime getCreatedAt() { return createdAt; }
    public void setCreatedAt(LocalDateTime createdAt) { this.createdAt = createdAt; }

    public LocalDateTime getUpdatedAt() { return updatedAt; }
    private void touch() { this.updatedAt = LocalDateTime.now(); }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        Profile profile = (Profile) o;
        return Objects.equals(id, profile.id)
                && Objects.equals(fullName, profile.fullName)
                && Objects.equals(email, profile.email);
    }

    @Override
    public int hashCode() {
        return Objects.hash(id, fullName, email);
    }

    @Override
    public String toString() {
        return "Profile{" +
                "id='" + id + '\'' +
                ", fullName='" + fullName + '\'' +
                ", headline='" + headline + '\'' +
                ", email='" + email + '\'' +
                ", skills=" + skills +
                ", projects=" + projects.size() +
                ", experiences=" + experiences.size() +
                ", educations=" + educations.size() +
                ", socialLinks=" + socialLinks.keySet() +
                '}';
    }

    /* Nested simple models */

    public static class Project implements Serializable {
        private static final long serialVersionUID = 1L;
        private String id;
        private String name;
        private String description;
        private String url;
        private LocalDate startDate;
        private LocalDate endDate;
        private List<String> technologies = new ArrayList<>();

        public Project() {}

        public Project(String id, String name, String description) {
            this.id = id;
            this.name = name;
            this.description = description;
        }

        public String getId() { return id; }
        public void setId(String id) { this.id = id; }

        public String getName() { return name; }
        public void setName(String name) { this.name = name; }

        public String getDescription() { return description; }
        public void setDescription(String description) { this.description = description; }

        public String getUrl() { return url; }
        public void setUrl(String url) { this.url = url; }

        public LocalDate getStartDate() { return startDate; }
        public void setStartDate(LocalDate startDate) { this.startDate = startDate; }

        public LocalDate getEndDate() { return endDate; }
        public void setEndDate(LocalDate endDate) { this.endDate = endDate; }

        public List<String> getTechnologies() { return Collections.unmodifiableList(technologies); }
        public void setTechnologies(Collection<String> techs) { this.technologies = new ArrayList<>(techs); }
        public void addTechnology(String tech) { this.technologies.add(tech); }

        @Override
        public String toString() {
            return "Project{" + "id='" + id + '\'' + ", name='" + name + '\'' + '}';
        }
    }

    public static class Experience implements Serializable {
        private static final long serialVersionUID = 1L;
        private String id;
        private String title;
        private String company;
        private LocalDate startDate;
        private LocalDate endDate;
        private String summary;
        private List<String> highlights = new ArrayList<>();

        public Experience() {}

        public String getId() { return id; }
        public void setId(String id) { this.id = id; }

        public String getTitle() { return title; }
        public void setTitle(String title) { this.title = title; }

        public String getCompany() { return company; }
        public void setCompany(String company) { this.company = company; }

        public LocalDate getStartDate() { return startDate; }
        public void setStartDate(LocalDate startDate) { this.startDate = startDate; }

        public LocalDate getEndDate() { return endDate; }
        public void setEndDate(LocalDate endDate) { this.endDate = endDate; }

        public String getSummary() { return summary; }
        public void setSummary(String summary) { this.summary = summary; }

        public List<String> getHighlights() { return Collections.unmodifiableList(highlights); }
        public void addHighlight(String h) { this.highlights.add(h); }

        @Override
        public String toString() {
            return "Experience{" + "title='" + title + '\'' + ", company='" + company + '\'' + '}';
        }
    }

    public static class Education implements Serializable {
        private static final long serialVersionUID = 1L;
        private String id;
        private String institution;
        private String degree;
        private String fieldOfStudy;
        private LocalDate startDate;
        private LocalDate endDate;

        public Education() {}

        public String getId() { return id; }
        public void setId(String id) { this.id = id; }

        public String getInstitution() { return institution; }
        public void setInstitution(String institution) { this.institution = institution; }

        public String getDegree() { return degree; }
        public void setDegree(String degree) { this.degree = degree; }

        public String getFieldOfStudy() { return fieldOfStudy; }
        public void setFieldOfStudy(String fieldOfStudy) { this.fieldOfStudy = fieldOfStudy; }

        public LocalDate getStartDate() { return startDate; }
        public void setStartDate(LocalDate startDate) { this.startDate = startDate; }

        public LocalDate getEndDate() { return endDate; }
        public void setEndDate(LocalDate endDate) { this.endDate = endDate; }

        @Override
        public String toString() {
            return "Education{" + "institution='" + institution + '\'' + ", degree='" + degree + '\'' + '}';
        }
    }
}