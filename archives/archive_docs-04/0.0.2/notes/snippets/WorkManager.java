import java.util.UUID;
import java.util.concurrent.*;
import java.util.concurrent.atomic.AtomicReference;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;

package com.work;


/**
 * Lightweight WorkManager for submitting, scheduling and monitoring work (Runnables / Callables).
 * - Tracks tasks by id (String UUID)
 * - Supports submit, schedule, cancel, fetch Future, basic metrics and graceful shutdown
 */
public class WorkManager {

    private final ThreadPoolExecutor executor;
    private final ScheduledExecutorService scheduler;
    private final ConcurrentMap<String, Future<?>> tasks = new ConcurrentHashMap<>();

    public WorkManager(int corePoolSize, int maxPoolSize, int queueCapacity, long keepAliveSeconds, ThreadFactory threadFactory) {
        BlockingQueue<Runnable> queue = new LinkedBlockingQueue<>(queueCapacity);
        this.executor = new ThreadPoolExecutor(corePoolSize, maxPoolSize, keepAliveSeconds, TimeUnit.SECONDS, queue, threadFactory, new ThreadPoolExecutor.AbortPolicy());
        this.scheduler = Executors.newSingleThreadScheduledExecutor(new DaemonThreadFactory("workmgr-scheduler-"));
    }

    public WorkManager() {
        this(Math.max(2, Runtime.getRuntime().availableProcessors()),
             Math.max(2, Runtime.getRuntime().availableProcessors()),
             1000,
             60,
             new DaemonThreadFactory("workmgr-worker-"));
    }

    /**
     * Submit a Runnable for immediate execution. Returns a task id.
     */
    public String submit(Runnable runnable) {
        String id = UUID.randomUUID().toString();
        Callable<Void> wrapped = () -> {
            try {
                runnable.run();
                return null;
            } finally {
                tasks.remove(id);
            }
        };
        Future<Void> f = executor.submit(wrapped);
        tasks.put(id, f);
        return id;
    }

    /**
     * Submit a Callable for immediate execution. Returns a task id.
     */
    public <T> String submit(Callable<T> callable) {
        String id = UUID.randomUUID().toString();
        Callable<T> wrapped = () -> {
            try {
                return callable.call();
            } finally {
                tasks.remove(id);
            }
        };
        Future<T> f = executor.submit(wrapped);
        tasks.put(id, f);
        return id;
    }

    /**
     * Schedule a Runnable to execute after a delay. Returns a task id.
     * The scheduled action will submit the real work onto the executor when the delay expires.
     */
    public String schedule(Runnable runnable, long delay, TimeUnit unit) {
        String id = UUID.randomUUID().toString();
        AtomicReference<Future<?>> actualFuture = new AtomicReference<>();

        Runnable scheduledAction = () -> {
            // when scheduled time arrives, submit to main executor and replace mapping
            Future<?> f = executor.submit(() -> {
                try {
                    runnable.run();
                } finally {
                    tasks.remove(id);
                }
            });
            actualFuture.set(f);
            tasks.put(id, f);
        };

        ScheduledFuture<?> scheduledFuture = scheduler.schedule(scheduledAction, delay, unit);
        // store the ScheduledFuture initially so callers can cancel before execution
        tasks.put(id, scheduledFuture);
        return id;
    }

    /**
     * Cancel a task by id. Returns true if cancellation was invoked.
     */
    public boolean cancel(String id) {
        Future<?> f = tasks.remove(id);
        if (f == null) return false;
        return f.cancel(true);
    }

    /**
     * Retrieve the Future associated with a task id, or null if not found.
     * Caller can use Future.get(...) to obtain result or check isDone/isCancelled.
     */
    public Future<?> getFuture(String id) {
        return tasks.get(id);
    }

    /**
     * Basic runtime metrics.
     */
    public int getActiveCount() {
        return executor.getActiveCount();
    }

    public long getCompletedTaskCount() {
        return executor.getCompletedTaskCount();
    }

    public int getQueueSize() {
        return executor.getQueue().size();
    }

    public int getPendingTasks() {
        return tasks.size();
    }

    /**
     * Graceful shutdown: stop accepting new tasks, attempt to complete existing tasks within timeout.
     * Returns true if terminated within the timeout.
     */
    public boolean shutdownGracefully(long timeout, TimeUnit unit) throws InterruptedException {
        scheduler.shutdown(); // no new schedules
        executor.shutdown();  // no new direct submissions
        boolean terminated = executor.awaitTermination(timeout, unit);
        if (!terminated) {
            executor.shutdownNow();
            terminated = executor.awaitTermination(5, TimeUnit.SECONDS);
        }
        // also try to stop scheduler if still alive
        if (!scheduler.isShutdown()) {
            scheduler.shutdownNow();
        }
        return terminated;
    }

    /**
     * Force immediate shutdown: cancel tracked tasks and shutdown executors.
     */
    public void shutdownNow() {
        // cancel tracked tasks
        for (String id : tasks.keySet()) {
            Future<?> f = tasks.remove(id);
            if (f != null) f.cancel(true);
        }
        scheduler.shutdownNow();
        executor.shutdownNow();
    }

    // Simple daemon thread factory used by default
    private static class DaemonThreadFactory implements ThreadFactory {
        private final ThreadFactory defaultFactory = Executors.defaultThreadFactory();
        private final String prefix;
        private final AtomicInteger idx = new AtomicInteger(0);

        DaemonThreadFactory(String prefix) {
            this.prefix = prefix != null ? prefix : "wm-";
        }

        @Override
        public Thread newThread(Runnable r) {
            Thread t = defaultFactory.newThread(r);
            t.setDaemon(true);
            t.setName(prefix + idx.getAndIncrement());
            return t;
        }
    }
}