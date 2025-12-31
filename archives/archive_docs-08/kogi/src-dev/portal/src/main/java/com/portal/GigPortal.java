import java.time.Instant;
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;
import java.util.stream.Collectors;

package com.portal;


/**
 * Simple in-memory gig worker portal.
 * Use for demonstration or as a lightweight starting point for real implementation.
 */
public class Portal {

    private final Map<Long, Worker> workers = new ConcurrentHashMap<>();
    private final Map<Long, Job> jobs = new ConcurrentHashMap<>();
    private final Map<Long, Application> applications = new ConcurrentHashMap<>();

    private final AtomicLong workerIdGen = new AtomicLong(1);
    private final AtomicLong jobIdGen = new AtomicLong(1);
    private final AtomicLong appIdGen = new AtomicLong(1);

    // Register a worker
    public Worker registerWorker(String name, String email, Set<String> skills) {
        long id = workerIdGen.getAndIncrement();
        Worker w = new Worker(id, name, email, new HashSet<>(skills), Instant.now());
        workers.put(id, w);
        return w;
    }

    // Post a job
    public Job postJob(long posterId, String title, String description, Set<String> requiredSkills, double budget) {
        if (!workers.containsKey(posterId)) {
            throw new NoSuchElementException("Poster/worker not found: " + posterId);
        }
        long id = jobIdGen.getAndIncrement();
        Job j = new Job(id, posterId, title, description, new HashSet<>(requiredSkills), budget, JobStatus.OPEN, Instant.now());
        jobs.put(id, j);
        return j;
    }

    // Search jobs by keyword and/or skills
    public List<Job> searchJobs(Optional<String> keyword, Set<String> skills, int limit) {
        return jobs.values().stream()
                .filter(j -> j.status == JobStatus.OPEN)
                .filter(j -> keyword.map(k -> j.title.toLowerCase().contains(k.toLowerCase())
                        || j.description.toLowerCase().contains(k.toLowerCase())).orElse(true))
                .filter(j -> skills == null || skills.isEmpty() || j.requiredSkills.containsAll(skills))
                .sorted(Comparator.comparing(job -> job.postedAt))
                .limit(Math.max(0, limit))
                .collect(Collectors.toList());
    }

    // Apply to a job
    public Application applyToJob(long workerId, long jobId, String coverLetter, double proposedRate) {
        Worker worker = workers.get(workerId);
        Job job = jobs.get(jobId);
        if (worker == null) throw new NoSuchElementException("Worker not found: " + workerId);
        if (job == null) throw new NoSuchElementException("Job not found: " + jobId);
        if (job.status != JobStatus.OPEN) throw new IllegalStateException("Job is not open: " + jobId);

        long id = appIdGen.getAndIncrement();
        Application app = new Application(id, jobId, workerId, coverLetter, proposedRate, ApplicationStatus.PENDING, Instant.now());
        applications.put(id, app);
        job.applicationIds.add(id);
        return app;
    }

    // Get applications for a job
    public List<Application> getApplicationsForJob(long jobId) {
        Job job = jobs.get(jobId);
        if (job == null) throw new NoSuchElementException("Job not found: " + jobId);
        return job.applicationIds.stream()
                .map(applications::get)
                .filter(Objects::nonNull)
                .collect(Collectors.toList());
    }

    // Accept an application (assigns the worker to the job)
    public void acceptApplication(long applicationId) {
        Application app = applications.get(applicationId);
        if (app == null) throw new NoSuchElementException("Application not found: " + applicationId);
        Job job = jobs.get(app.jobId);
        if (job == null) throw new NoSuchElementException("Job not found: " + app.jobId);
        if (job.status != JobStatus.OPEN) throw new IllegalStateException("Job is not open: " + job.id);

        app.status = ApplicationStatus.ACCEPTED;
        job.status = JobStatus.IN_PROGRESS;
        job.assignedWorkerId = app.workerId;
    }

    // Mark job complete
    public void completeJob(long jobId, double rating, String feedback) {
        Job job = jobs.get(jobId);
        if (job == null) throw new NoSuchElementException("Job not found: " + jobId);
        if (job.status != JobStatus.IN_PROGRESS) throw new IllegalStateException("Job not in progress: " + jobId);
        job.status = JobStatus.COMPLETED;
        job.completedAt = Instant.now();

        // add rating to worker
        Worker w = workers.get(job.assignedWorkerId);
        if (w != null) {
            synchronized (w) {
                w.ratings.add(rating);
                w.feedbacks.add(Optional.ofNullable(feedback).orElse(""));
            }
        }
    }

    // Get basic job listing
    public List<Job> listOpenJobs() {
        return jobs.values().stream()
                .filter(j -> j.status == JobStatus.OPEN)
                .sorted(Comparator.comparing(j -> j.postedAt))
                .collect(Collectors.toList());
    }

    // Get worker profile
    public Worker getWorker(long workerId) {
        Worker w = workers.get(workerId);
        if (w == null) throw new NoSuchElementException("Worker not found: " + workerId);
        return w;
    }

    // Update worker skills
    public Worker updateWorkerSkills(long workerId, Set<String> skills) {
        Worker w = workers.get(workerId);
        if (w == null) throw new NoSuchElementException("Worker not found: " + workerId);
        synchronized (w) {
            w.skills = new HashSet<>(skills);
        }
        return w;
    }

    // Domain classes

    public static class Worker {
        public final long id;
        public String name;
        public String email;
        public Set<String> skills;
        public final Instant registeredAt;
        public final List<Double> ratings = new ArrayList<>();
        public final List<String> feedbacks = new ArrayList<>();

        public Worker(long id, String name, String email, Set<String> skills, Instant registeredAt) {
            this.id = id;
            this.name = name;
            this.email = email;
            this.skills = skills;
            this.registeredAt = registeredAt;
        }

        public double getAverageRating() {
            synchronized (ratings) {
                return ratings.isEmpty() ? 0.0 : ratings.stream().mapToDouble(Double::doubleValue).average().orElse(0.0);
            }
        }
    }

    public static class Job {
        public final long id;
        public final long posterId;
        public String title;
        public String description;
        public Set<String> requiredSkills;
        public double budget;
        public JobStatus status;
        public final Instant postedAt;
        public Instant completedAt;
        public Long assignedWorkerId;
        public final List<Long> applicationIds = new ArrayList<>();

        public Job(long id, long posterId, String title, String description, Set<String> requiredSkills, double budget, JobStatus status, Instant postedAt) {
            this.id = id;
            this.posterId = posterId;
            this.title = title;
            this.description = description;
            this.requiredSkills = requiredSkills;
            this.budget = budget;
            this.status = status;
            this.postedAt = postedAt;
        }
    }

    public static class Application {
        public final long id;
        public final long jobId;
        public final long workerId;
        public final String coverLetter;
        public final double proposedRate;
        public ApplicationStatus status;
        public final Instant appliedAt;

        public Application(long id, long jobId, long workerId, String coverLetter, double proposedRate, ApplicationStatus status, Instant appliedAt) {
            this.id = id;
            this.jobId = jobId;
            this.workerId = workerId;
            this.coverLetter = coverLetter;
            this.proposedRate = proposedRate;
            this.status = status;
            this.appliedAt = appliedAt;
        }
    }

    public enum JobStatus { OPEN, IN_PROGRESS, COMPLETED, CANCELLED }

    public enum ApplicationStatus { PENDING, ACCEPTED, REJECTED }
}