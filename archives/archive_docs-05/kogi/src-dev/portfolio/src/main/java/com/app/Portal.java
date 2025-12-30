import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.Instant;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.UUID;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.stream.Collectors;

package com.app;


/**
 * Simple portfolio "Portal" manager.
 * - Thread-safe basic CRUD for assets
 * - Computes total market value
 * - Can serialize to JSON (simple hand-rolled)
 *
 * Put this file at: /d:/dev/ws/kogi/src/portfolio/src/main/java/com/app/Portal.java
 */
public final class Portal {
    private final UUID id;
    private volatile String name;
    private volatile String description;
    private final Instant createdAt;
    private volatile Instant updatedAt;
    private final CopyOnWriteArrayList<Asset> assets = new CopyOnWriteArrayList<>();

    public Portal(String name) {
        this(UUID.randomUUID(), name, "", Instant.now());
    }

    public Portal(UUID id, String name, String description, Instant createdAt) {
        this.id = Objects.requireNonNull(id, "id");
        this.name = Objects.requireNonNull(name, "name");
        this.description = description == null ? "" : description;
        this.createdAt = createdAt == null ? Instant.now() : createdAt;
        this.updatedAt = this.createdAt;
    }

    public UUID getId() {
        return id;
    }

    public synchronized String getName() {
        return name;
    }

    public synchronized void setName(String name) {
        this.name = Objects.requireNonNull(name, "name");
        this.updatedAt = Instant.now();
    }

    public synchronized String getDescription() {
        return description;
    }

    public synchronized void setDescription(String description) {
        this.description = description == null ? "" : description;
        this.updatedAt = Instant.now();
    }

    public Instant getCreatedAt() {
        return createdAt;
    }

    public Instant getUpdatedAt() {
        return updatedAt;
    }

    public List<Asset> listAssets() {
        return Collections.unmodifiableList(assets);
    }

    /**
     * Add or update an asset. If an asset with same symbol exists, it's replaced.
     */
    public synchronized void addOrUpdateAsset(String symbol, String title, double quantity, double pricePerUnit) {
        Objects.requireNonNull(symbol, "symbol");
        if (quantity < 0) throw new IllegalArgumentException("quantity must be >= 0");
        if (pricePerUnit < 0) throw new IllegalArgumentException("pricePerUnit must be >= 0");

        Asset newAsset = new Asset(symbol.trim().toUpperCase(), title == null ? "" : title, quantity, pricePerUnit);
        assets.removeIf(a -> a.getSymbol().equals(newAsset.getSymbol()));
        assets.add(newAsset);
        this.updatedAt = Instant.now();
    }

    /**
     * Remove asset by symbol. Returns true if removed.
     */
    public synchronized boolean removeAsset(String symbol) {
        Objects.requireNonNull(symbol, "symbol");
        boolean removed = assets.removeIf(a -> a.getSymbol().equals(symbol.trim().toUpperCase()));
        if (removed) this.updatedAt = Instant.now();
        return removed;
    }

    /**
     * Find an asset by symbol.
     */
    public Optional<Asset> findAsset(String symbol) {
        if (symbol == null) return Optional.empty();
        String s = symbol.trim().toUpperCase();
        return assets.stream().filter(a -> a.getSymbol().equals(s)).findFirst();
    }

    /**
     * Compute total market value across all assets.
     */
    public double getTotalValue() {
        return assets.stream().mapToDouble(Asset::marketValue).sum();
    }

    /**
     * Serialize to a compact JSON string. This is a simple implementation that escapes quotes.
     */
    public String toJson() {
        StringBuilder sb = new StringBuilder(256);
        sb.append("{");
        appendJsonKV(sb, "id", id.toString()); sb.append(",");
        appendJsonKV(sb, "name", name); sb.append(",");
        appendJsonKV(sb, "description", description); sb.append(",");
        appendJsonKV(sb, "createdAt", createdAt.toString()); sb.append(",");
        appendJsonKV(sb, "updatedAt", updatedAt == null ? "" : updatedAt.toString()); sb.append(",");
        sb.append("\"assets\":[");
        sb.append(assets.stream().map(Asset::toJson).collect(Collectors.joining(",")));
        sb.append("]");
        sb.append("}");
        return sb.toString();
    }

    private static void appendJsonKV(StringBuilder sb, String key, String value) {
        sb.append("\"").append(escapeJson(key)).append("\":");
        sb.append("\"").append(escapeJson(value == null ? "" : value)).append("\"");
    }

    private static String escapeJson(String s) {
        return s.replace("\\", "\\\\").replace("\"", "\\\"").replace("\n", "\\n").replace("\r", "\\r");
    }

    /**
     * Save JSON representation to the given file path (creates parent directories if needed).
     */
    public void saveToFile(Path path) throws IOException {
        Objects.requireNonNull(path, "path");
        if (path.getParent() != null) Files.createDirectories(path.getParent());
        Files.write(path, toJson().getBytes(StandardCharsets.UTF_8));
    }

    @Override
    public String toString() {
        return "Portal{" +
                "id=" + id +
                ", name='" + name + '\'' +
                ", description='" + description + '\'' +
                ", createdAt=" + createdAt +
                ", updatedAt=" + updatedAt +
                ", assets=" + assets.size() +
                '}';
    }

    // --- Nested Asset class ---
    public static final class Asset {
        private final String symbol;
        private final String title;
        private final double quantity;
        private final double pricePerUnit;

        public Asset(String symbol, String title, double quantity, double pricePerUnit) {
            this.symbol = Objects.requireNonNull(symbol, "symbol");
            this.title = title == null ? "" : title;
            this.quantity = quantity;
            this.pricePerUnit = pricePerUnit;
        }

        public String getSymbol() {
            return symbol;
        }

        public String getTitle() {
            return title;
        }

        public double getQuantity() {
            return quantity;
        }

        public double getPricePerUnit() {
            return pricePerUnit;
        }

        public double marketValue() {
            return quantity * pricePerUnit;
        }

        public String toJson() {
            StringBuilder sb = new StringBuilder(128);
            sb.append("{");
            sb.append("\"symbol\":\"").append(escapeJson(symbol)).append("\",");
            sb.append("\"title\":\"").append(escapeJson(title)).append("\",");
            sb.append("\"quantity\":").append(quantity).append(",");
            sb.append("\"pricePerUnit\":").append(pricePerUnit);
            sb.append("}");
            return sb.toString();
        }

        @Override
        public String toString() {
            return "Asset{" +
                    "symbol='" + symbol + '\'' +
                    ", title='" + title + '\'' +
                    ", quantity=" + quantity +
                    ", pricePerUnit=" + pricePerUnit +
                    '}';
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (!(o instanceof Asset)) return false;
            Asset asset = (Asset) o;
            return Double.compare(asset.quantity, quantity) == 0 &&
                    Double.compare(asset.pricePerUnit, pricePerUnit) == 0 &&
                    symbol.equals(asset.symbol) &&
                    title.equals(asset.title);
        }

        @Override
        public int hashCode() {
            return Objects.hash(symbol, title, quantity, pricePerUnit);
        }
    }
}