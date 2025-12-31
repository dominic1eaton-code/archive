import java.util.*;
import java.util.concurrent.CopyOnWriteArrayList;

package com.app;


/**
 * Simple Dashboard model class.
 * - Thread-safe for basic add/remove operations.
 * - Holds a list of widgets and lightweight metadata.
 */
public class Dashboard {
    private final String id;
    private String title;
    private final List<Widget> widgets = new CopyOnWriteArrayList<>();
    private final Map<String, String> metadata = Collections.synchronizedMap(new HashMap<>());
    private volatile Date lastUpdated;

    public Dashboard() {
        this(UUID.randomUUID().toString(), "Dashboard");
    }

    public Dashboard(String id, String title) {
        this.id = Objects.requireNonNull(id, "id");
        this.title = title == null ? "" : title;
        this.lastUpdated = new Date();
    }

    // Basic properties
    public String getId() {
        return id;
    }

    public synchronized String getTitle() {
        return title;
    }

    public synchronized void setTitle(String title) {
        this.title = title == null ? "" : title;
        touch();
    }

    public Date getLastUpdated() {
        return lastUpdated == null ? null : new Date(lastUpdated.getTime());
    }

    // Metadata
    public void putMetadata(String key, String value) {
        metadata.put(key, value);
        touch();
    }

    public String getMetadata(String key) {
        return metadata.get(key);
    }

    public Map<String, String> getAllMetadata() {
        synchronized (metadata) {
            return new HashMap<>(metadata);
        }
    }

    // Widget operations
    public List<Widget> getWidgets() {
        return Collections.unmodifiableList(new ArrayList<>(widgets));
    }

    public boolean addWidget(Widget widget) {
        Objects.requireNonNull(widget, "widget");
        boolean added = widgets.add(widget);
        if (added) touch();
        return added;
    }

    public boolean removeWidgetById(String widgetId) {
        boolean removed = widgets.removeIf(w -> w.getId().equals(widgetId));
        if (removed) touch();
        return removed;
    }

    public Optional<Widget> findWidget(String widgetId) {
        return widgets.stream().filter(w -> w.getId().equals(widgetId)).findFirst();
    }

    public void clearWidgets() {
        widgets.clear();
        touch();
    }

    private void touch() {
        lastUpdated = new Date();
    }

    @Override
    public String toString() {
        return "Dashboard{" +
                "id='" + id + '\'' +
                ", title='" + title + '\'' +
                ", widgets=" + widgets.size() +
                ", lastUpdated=" + lastUpdated +
                '}';
    }

    // Simple nested Widget model
    public static class Widget {
        private final String id;
        private String type;
        private final Map<String, Object> config = new HashMap<>();
        private final Date createdAt;

        public Widget(String type) {
            this(UUID.randomUUID().toString(), type);
        }

        public Widget(String id, String type) {
            this.id = Objects.requireNonNull(id, "id");
            this.type = type == null ? "" : type;
            this.createdAt = new Date();
        }

        public String getId() {
            return id;
        }

        public String getType() {
            return type;
        }

        public void setType(String type) {
            this.type = type == null ? "" : type;
        }

        public Map<String, Object> getConfig() {
            return Collections.unmodifiableMap(new HashMap<>(config));
        }

        public void putConfig(String key, Object value) {
            config.put(key, value);
        }

        public Date getCreatedAt() {
            return new Date(createdAt.getTime());
        }

        @Override
        public String toString() {
            return "Widget{" +
                    "id='" + id + '\'' +
                    ", type='" + type + '\'' +
                    ", config=" + config +
                    ", createdAt=" + createdAt +
                    '}';
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (!(o instanceof Widget)) return false;
            Widget widget = (Widget) o;
            return id.equals(widget.id);
        }

        @Override
        public int hashCode() {
            return Objects.hash(id);
        }
    }
}