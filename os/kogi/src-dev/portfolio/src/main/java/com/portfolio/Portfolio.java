import java.io.Serializable;
import java.math.BigDecimal;
import java.time.Instant;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.UUID;

package com.portfolio;


/**
 * Simple Portfolio domain object.
 * Contains lightweight Holding entries and helpers to calculate market value.
 */
public class Portfolio implements Serializable {
    private static final long serialVersionUID = 1L;

    private final UUID id;
    private String owner;
    private String name;
    private String description;
    private final Instant createdAt;
    private final List<Holding> holdings = new ArrayList<>();

    public Portfolio(String owner, String name) {
        this(UUID.randomUUID(), owner, name, null, Instant.now());
    }

    public Portfolio(UUID id, String owner, String name, String description, Instant createdAt) {
        this.id = Objects.requireNonNull(id, "id");
        this.owner = Objects.requireNonNull(owner, "owner");
        this.name = Objects.requireNonNull(name, "name");
        this.description = description;
        this.createdAt = Objects.requireNonNull(createdAt, "createdAt");
    }

    public UUID getId() {
        return id;
    }

    public String getOwner() {
        return owner;
    }

    public void setOwner(String owner) {
        this.owner = Objects.requireNonNull(owner, "owner");
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = Objects.requireNonNull(name, "name");
    }

    public String getDescription() {
        return description;
    }

    public void setDescription(String description) {
        this.description = description;
    }

    public Instant getCreatedAt() {
        return createdAt;
    }

    public void addSolution(String solutionName) {
        // Placeholder for adding a solution to the portfolio
        System.out.println("Solution " + solutionName + " added to portfolio " + name);
    }

    public void removeSolution(String solutionName) {
        // Placeholder for removing a solution from the portfolio
        System.out.println("Solution " + solutionName + " removed from portfolio " + name);
    }

    public List<String> listSolutions() {
        // Placeholder for listing solutions in the portfolio
        return Collections.emptyList();
    }

    public void clearSolutions() {
        // Placeholder for clearing all solutions from the portfolio
        System.out.println("All solutions cleared from portfolio " + name);
    }

    public int getSolutionCount() {
        // Placeholder for getting the count of solutions in the portfolio
        return 0;
    }

    public boolean hasSolution(String solutionName) {
        // Placeholder for checking if a solution exists in the portfolio
        return false;
    }

    public void renameSolution(String oldName, String newName) {
        // Placeholder for renaming a solution in the portfolio
        System.out.println("Solution " + oldName + " renamed to " + newName + " in portfolio " + name);
    }

    public void archiveSolution(String solutionName) {
        // Placeholder for archiving a solution in the portfolio
        System.out.println("Solution " + solutionName + " archived in portfolio " + name);
    }

    public void unarchiveSolution(String solutionName) {
        // Placeholder for unarchiving a solution in the portfolio
        System.out.println("Solution " + solutionName + " unarchived in portfolio " + name);
    }

    public void deleteSolution(String solutionName) {
        // Placeholder for deleting a solution from the portfolio
        System.out.println("Solution " + solutionName + " deleted from portfolio " + name);
    }

    public void duplicateSolution(String solutionName) {
        // Placeholder for duplicating a solution in the portfolio
        System.out.println("Solution " + solutionName + " duplicated in portfolio " + name);
    }

    public void exportSolution(String solutionName, String format) {
        // Placeholder for exporting a solution from the portfolio
        System.out.println("Solution " + solutionName + " exported in format " + format + " from portfolio " + name);
    }

    public void importSolution(String solutionData, String format) {
        // Placeholder for importing a solution into the portfolio
        System.out.println("Solution imported in format " + format + " into portfolio " + name);
    }

    public void shareSolution(String solutionName, String userEmail) {
        // Placeholder for sharing a solution in the portfolio
        System.out.println("Solution " + solutionName + " shared with " + userEmail + " from portfolio " + name);
    }

    public void unshareSolution(String solutionName, String userEmail) {
        // Placeholder for unsharing a solution in the portfolio
        System.out.println("Solution " + solutionName + " unshared with " + userEmail + " from portfolio " + name);
    }

    public void addProject(String projectName) {
        // Placeholder for adding a project to the portfolio
        System.out.println("Project " + projectName + " added to portfolio " + name);
    }

    public void removeProject(String projectName) {
        // Placeholder for removing a project from the portfolio
        System.out.println("Project " + projectName + " removed from portfolio " + name);
    }

    public List<String> listProjects() {
        // Placeholder for listing projects in the portfolio
        return Collections.emptyList();
    }

    public void clearProjects() {
        // Placeholder for clearing all projects from the portfolio
        System.out.println("All projects cleared from portfolio " + name);
    }

    public int getProjectCount() {
        // Placeholder for getting the count of projects in the portfolio
        return 0;
    }

    public boolean hasProject(String projectName) {
        // Placeholder for checking if a project exists in the portfolio
        return false;
    }

    public void renameProject(String oldName, String newName) {
        // Placeholder for renaming a project in the portfolio
        System.out.println("Project " + oldName + " renamed to " + newName + " in portfolio " + name);
    }

    public void archiveProject(String projectName) {
        // Placeholder for archiving a project in the portfolio
        System.out.println("Project " + projectName + " archived in portfolio " + name);
    }

    public void unarchiveProject(String projectName) {
        // Placeholder for unarchiving a project in the portfolio
        System.out.println("Project " + projectName + " unarchived in portfolio " + name);
    }

    public void deleteProject(String projectName) {
        // Placeholder for deleting a project from the portfolio
        System.out.println("Project " + projectName + " deleted from portfolio " + name);
    }

    public void duplicateProject(String projectName) {
        // Placeholder for duplicating a project in the portfolio
        System.out.println("Project " + projectName + " duplicated in portfolio " + name);
    }

    public void exportProject(String projectName, String format) {
        // Placeholder for exporting a project from the portfolio
        System.out.println("Project " + projectName + " exported in format " + format + " from portfolio " + name);
    }

    public void importProject(String projectData, String format) {
        // Placeholder for importing a project into the portfolio
        System.out.println("Project imported in format " + format + " into portfolio " + name);
    }

    public void shareProject(String projectName, String userEmail) {
        // Placeholder for sharing a project in the portfolio
        System.out.println("Project " + projectName + " shared with " + userEmail + " from portfolio " + name);
    }

    public void unshareProject(String projectName, String userEmail) {
        // Placeholder for unsharing a project in the portfolio
        System.out.println("Project " + projectName + " unshared with " + userEmail + " from portfolio " + name);
    }

    public void listSharedUsers(String projectName) {
        // Placeholder for listing users with whom the project is shared
        System.out.println("Listing users shared with project " + projectName + " in portfolio " + name);
    }

    public int getSharedUserCount(String projectName) {
        // Placeholder for getting the count of users with whom the project is shared
        return 0;
    }

    public void clearSharedUsers(String projectName) {
        // Placeholder for clearing all shared users from the project
        System.out.println("All shared users cleared from project " + projectName + " in portfolio " + name);
    }

    public void updateProjectStatus(String projectName, String status) {
        // Placeholder for updating the status of a project in the portfolio
        System.out.println("Project " + projectName + " status updated to " + status + " in portfolio " + name);
    }


    /**
     * Add a holding. If a holding with same symbol exists, it will be merged by increasing quantity
     * and recalculating average price.
     */
    public void addHolding(Holding toAdd) {
        Objects.requireNonNull(toAdd, "holding");
        for (int i = 0; i < holdings.size(); i++) {
            Holding h = holdings.get(i);
            if (h.getSymbol().equalsIgnoreCase(toAdd.getSymbol())) {
                holdings.set(i, h.merge(toAdd));
                return;
            }
        }
        holdings.add(toAdd);
    }

    public boolean removeHolding(String symbol) {
        return holdings.removeIf(h -> h.getSymbol().equalsIgnoreCase(symbol));
    }

    public List<Holding> getHoldings() {
        return Collections.unmodifiableList(holdings);
    }

    /**
     * Calculate total market value of the portfolio.
     * marketPrices map keys are ticker symbols and values are current price per unit.
     * If a price for a holding is missing it will be treated as zero.
     */
    public BigDecimal totalMarketValue(Map<String, BigDecimal> marketPrices) {
        Objects.requireNonNull(marketPrices, "marketPrices");
        BigDecimal sum = BigDecimal.ZERO;
        for (Holding h : holdings) {
            BigDecimal price = marketPrices.getOrDefault(h.getSymbol(), BigDecimal.ZERO);
            sum = sum.add(price.multiply(h.getQuantity()));
        }
        return sum;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        Portfolio portfolio = (Portfolio) o;
        return id.equals(portfolio.id);
    }

    @Override
    public int hashCode() {
        return id.hashCode();
    }

    @Override
    public String toString() {
        return "Portfolio{" +
                "id=" + id +
                ", owner='" + owner + '\'' +
                ", name='" + name + '\'' +
                ", createdAt=" + createdAt +
                ", holdings=" + holdings.size() +
                '}';
    }

    /**
     * Simple representation of an asset holding.
     */
    public static final class Holding implements Serializable {
        private static final long serialVersionUID = 1L;

        private final String symbol;
        private final BigDecimal quantity;
        private final BigDecimal averagePrice;

        public Holding(String symbol, BigDecimal quantity, BigDecimal averagePrice) {
            this.symbol = Objects.requireNonNull(symbol, "symbol").toUpperCase();
            this.quantity = Objects.requireNonNull(quantity, "quantity");
            this.averagePrice = Objects.requireNonNull(averagePrice, "averagePrice");
        }

        public String getSymbol() {
            return symbol;
        }

        public BigDecimal getQuantity() {
            return quantity;
        }

        public BigDecimal getAveragePrice() {
            return averagePrice;
        }

        /**
         * Merge two holdings for the same symbol producing a new Holding with combined quantity
         * and a weighted average price.
         */
        public Holding merge(Holding other) {
            if (!this.symbol.equalsIgnoreCase(other.symbol)) {
                throw new IllegalArgumentException("Can only merge holdings with same symbol");
            }
            BigDecimal totalQty = this.quantity.add(other.quantity);
            if (totalQty.compareTo(BigDecimal.ZERO) == 0) {
                return new Holding(symbol, BigDecimal.ZERO, BigDecimal.ZERO);
            }
            BigDecimal weighted = this.averagePrice.multiply(this.quantity)
                    .add(other.averagePrice.multiply(other.quantity))
                    .divide(totalQty, BigDecimal.ROUND_HALF_EVEN);
            return new Holding(symbol, totalQty, weighted);
        }

        @Override
        public String toString() {
            return "Holding{" +
                    "symbol='" + symbol + '\'' +
                    ", quantity=" + quantity +
                    ", averagePrice=" + averagePrice +
                    '}';
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (!(o instanceof Holding)) return false;
            Holding holding = (Holding) o;
            return symbol.equalsIgnoreCase(holding.symbol);
        }

        @Override
        public int hashCode() {
            return symbol.toUpperCase().hashCode();
        }
    }
}