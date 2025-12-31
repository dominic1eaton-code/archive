import java.time.Duration;
import java.time.Instant;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.concurrent.locks.ReentrantLock;

package com.time;


/**
 * Simple gig time manager.
 * Tracks start/stop sessions and provides aggregated durations.
 */
public class TimeManager {

    private final ReentrantLock lock = new ReentrantLock();
    private final List<Session> sessions = new ArrayList<>();
    private Instant currentStart;

    /**
     * Starts a new session. Throws IllegalStateException if already running.
     */
    public void start() {
        lock.lock();
        try {
            if (currentStart != null) {
                throw new IllegalStateException("TimeManager is already running");
            }
            currentStart = Instant.now();
        } finally {
            lock.unlock();
        }
    }

    /**
     * Stops the current session and records it. Throws IllegalStateException if not running.
     */
    public void stop() {
        lock.lock();
        try {
            if (currentStart == null) {
                throw new IllegalStateException("TimeManager is not running");
            }
            Instant end = Instant.now();
            sessions.add(new Session(currentStart, end));
            currentStart = null;
        } finally {
            lock.unlock();
        }
    }

    /**
     * Adds an existing session (useful for importing). start must be before end.
     */
    public void addSession(Instant start, Instant end) {
        if (start == null || end == null || !start.isBefore(end)) {
            throw new IllegalArgumentException("Invalid session interval");
        }
        lock.lock();
        try {
            sessions.add(new Session(start, end));
        } finally {
            lock.unlock();
        }
    }

    /**
     * Returns true if a session is currently running.
     */
    public boolean isRunning() {
        lock.lock();
        try {
            return currentStart != null;
        } finally {
            lock.unlock();
        }
    }

    /**
     * Returns the start time of the current session, if running.
     */
    public Optional<Instant> getCurrentStart() {
        lock.lock();
        try {
            return Optional.ofNullable(currentStart);
        } finally {
            lock.unlock();
        }
    }

    /**
     * Duration of the current ongoing session, or zero if not running.
     */
    public Duration getCurrentSessionDuration() {
        lock.lock();
        try {
            if (currentStart == null) return Duration.ZERO;
            return Duration.between(currentStart, Instant.now());
        } finally {
            lock.unlock();
        }
    }

    /**
     * Total duration across all recorded sessions plus current session if running.
     */
    public Duration getTotalDuration() {
        lock.lock();
        try {
            Duration total = Duration.ZERO;
            for (Session s : sessions) {
                total = total.plus(s.getDuration());
            }
            if (currentStart != null) {
                total = total.plus(Duration.between(currentStart, Instant.now()));
            }
            return total;
        } finally {
            lock.unlock();
        }
    }

    /**
     * Returns an immutable copy of recorded sessions (does not include the running session).
     */
    public List<Session> getSessions() {
        lock.lock();
        try {
            return Collections.unmodifiableList(new ArrayList<>(sessions));
        } finally {
            lock.unlock();
        }
    }

    /**
     * Clears all recorded sessions and stops any running session.
     */
    public void reset() {
        lock.lock();
        try {
            sessions.clear();
            currentStart = null;
        } finally {
            lock.unlock();
        }
    }

    /**
     * Immutable session record.
     */
    public static final class Session {
        private final Instant start;
        private final Instant end;

        public Session(Instant start, Instant end) {
            this.start = start;
            this.end = end;
        }

        public Instant getStart() { return start; }
        public Instant getEnd() { return end; }
        public Duration getDuration() { return Duration.between(start, end); }

        @Override
        public String toString() {
            return "Session[start=" + start + ", end=" + end + ", duration=" + getDuration() + "]";
        }
    }
}