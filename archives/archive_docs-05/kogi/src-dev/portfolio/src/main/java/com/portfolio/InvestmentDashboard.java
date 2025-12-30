import org.jfree.chart.*;
import org.jfree.chart.plot.*;
import org.jfree.data.category.*;
import org.jfree.data.general.*;
import javax.swing.*;
import java.awt.*;
import java.awt.event.*;
import java.io.File;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.*;
import java.util.List;

// Base Investment class
abstract class Investment {
    protected String name;
    protected double amountInvested;
    protected double currentValue;

    public Investment(String name, double amountInvested) {
        this.name = name;
        this.amountInvested = amountInvested;
        this.currentValue = amountInvested;
    }

    public String getName() { return name; }
    public double getCurrentValue() { return currentValue; }
    public double getAmountInvested() { return amountInvested; }
    public double calculateReturn() { return currentValue - amountInvested; }
}

// Stock class
class Stock extends Investment {
    private double shares;
    private double currentPricePerShare;
    private String sector;
    private double dividendAccumulated = 0;

    public Stock(String name, double shares, double purchasePrice, double currentPrice, String sector) {
        super(name, shares * purchasePrice);
        this.shares = shares;
        this.currentPricePerShare = currentPrice;
        this.sector = sector;
        this.currentValue = shares * currentPrice;
    }

    public String getSector() { return sector; }
    public double getCurrentPricePerShare() { return currentPricePerShare; }

    public void setCurrentPricePerShare(double price) {
        this.currentPricePerShare = price;
        this.currentValue = shares * price + dividendAccumulated;
    }

    public void addDividend(double dividend) {
        dividendAccumulated += dividend;
        currentValue += dividend;
    }

    public double getShares() { return shares; }
}

// Bond class
class Bond extends Investment {
    private double interestRate; // per update

    public Bond(String name, double amountInvested, double interestRate) {
        super(name, amountInvested);
        this.interestRate = interestRate;
    }

    public double getInterestRate() { return interestRate; }
    public void addInterest(double interest) { this.currentValue += interest; }
}

// Portfolio snapshot for historical tracking
class PortfolioSnapshot {
    private LocalDateTime timestamp;
    private double totalValue;
    private String action;

    public PortfolioSnapshot(LocalDateTime timestamp, double totalValue, String action) {
        this.timestamp = timestamp;
        this.totalValue = totalValue;
        this.action = action;
    }

    public LocalDateTime getTimestamp() { return timestamp; }
    public double getTotalValue() { return totalValue; }
    public String getAction() { return action; }
}

// Portfolio class
class Portfolio {
    private List<Investment> investments = new ArrayList<>();
    private List<PortfolioSnapshot> history = new ArrayList<>();
    private List<String> transactionHistory = new ArrayList<>();

    public void addInvestment(Investment inv) {
        investments.add(inv);
        transactionHistory.add("Added: " + inv.getName());
        recordSnapshot("Add " + inv.getName());
    }

    public void removeInvestment(String name) {
        investments.removeIf(inv -> {
            boolean removed = inv.getName().equalsIgnoreCase(name);
            if (removed) transactionHistory.add("Removed: " + inv.getName());
            return removed;
        });
        recordSnapshot("Remove " + name);
    }

    public List<Investment> getInvestments() { return investments; }
    public List<PortfolioSnapshot> getHistory() { return history; }
    public List<String> getTransactionHistory() { return transactionHistory; }

    public double getTotalValue() {
        return investments.stream().mapToDouble(Investment::getCurrentValue).sum();
    }

    public void recordSnapshot(String action) {
        history.add(new PortfolioSnapshot(LocalDateTime.now(), getTotalValue(), action));
    }
}

// Main GUI
public class InvestmentDashboard extends JFrame {
    private Portfolio portfolio = new Portfolio();
    private JPanel chartPanel;
    private JPanel buttonPanel;
    private JTable portfolioTable;
    private Timer simulationTimer;

    // Simulation settings
    private double volatility = 0.05;
    private int updateInterval = 2000;
    private double dividendRate = 0.02;

    public InvestmentDashboard() {
        setTitle("Investment Dashboard");
        setSize(1200, 700);
        setDefaultCloseOperation(EXIT_ON_CLOSE);
        setLayout(new BorderLayout());

        chartPanel = new JPanel(new GridLayout(1, 3));
        add(chartPanel, BorderLayout.EAST);

        buttonPanel = new JPanel();
        add(buttonPanel, BorderLayout.SOUTH);

        portfolioTable = new JTable();
        add(new JScrollPane(portfolioTable), BorderLayout.CENTER);

        initButtons();
        refreshPortfolioView();
        refreshCharts();
    }

    private void initButtons() {
        JButton addStockBtn = new JButton("Add Stock");
        JButton addBondBtn = new JButton("Add Bond");
        JButton simSettingsBtn = new JButton("Simulation Settings");
        JButton startSimBtn = new JButton("Start Simulation");
        JButton stopSimBtn = new JButton("Stop Simulation");
        JButton suggestionsBtn = new JButton("Investment Suggestions");
        JButton saveAllocBtn = new JButton("Save Allocation Chart");
        JButton saveReturnsBtn = new JButton("Save Returns Chart");
        JButton saveGrowthBtn = new JButton("Save Growth Chart");

        buttonPanel.add(addStockBtn);
        buttonPanel.add(addBondBtn);
        buttonPanel.add(simSettingsBtn);
        buttonPanel.add(startSimBtn);
        buttonPanel.add(stopSimBtn);
        buttonPanel.add(suggestionsBtn);
        buttonPanel.add(saveAllocBtn);
        buttonPanel.add(saveReturnsBtn);
        buttonPanel.add(saveGrowthBtn);

        addStockBtn.addActionListener(e -> addStockDialog());
        addBondBtn.addActionListener(e -> addBondDialog());
        simSettingsBtn.addActionListener(e -> showSimulationSettings());
        startSimBtn.addActionListener(e -> startSimulation());
        stopSimBtn.addActionListener(e -> stopSimulation());
        suggestionsBtn.addActionListener(e -> showInvestmentSuggestions());
        saveAllocBtn.addActionListener(e -> saveChartAsImage(createAllocationChart().getChart(), "allocation.png"));
        saveReturnsBtn.addActionListener(e -> saveChartAsImage(createReturnsChart().getChart(), "returns.png"));
        saveGrowthBtn.addActionListener(e -> saveChartAsImage(createGrowthChart().getChart(), "growth.png"));
    }

    private void addStockDialog() {
        JTextField nameField = new JTextField();
        JTextField sharesField = new JTextField();
        JTextField priceField = new JTextField();
        JTextField sectorField = new JTextField();
        Object[] message = {"Name:", nameField, "Shares:", sharesField, "Current Price:", priceField, "Sector:", sectorField};
        if (JOptionPane.showConfirmDialog(this, message, "Add Stock", JOptionPane.OK_CANCEL_OPTION) == JOptionPane.OK_OPTION) {
            try {
                String name = nameField.getText();
                double shares = Double.parseDouble(sharesField.getText());
                double price = Double.parseDouble(priceField.getText());
                String sector = sectorField.getText();
                Stock stock = new Stock(name, shares, price, price, sector);
                portfolio.addInvestment(stock);
                refreshPortfolioView();
                refreshCharts();
            } catch (NumberFormatException ex) {
                JOptionPane.showMessageDialog(this, "Invalid input!");
            }
        }
    }

    private void addBondDialog() {
        JTextField nameField = new JTextField();
        JTextField amountField = new JTextField();
        JTextField rateField = new JTextField();
        Object[] message = {"Name:", nameField, "Amount:", amountField, "Interest Rate (% per update):", rateField};
        if (JOptionPane.showConfirmDialog(this, message, "Add Bond", JOptionPane.OK_CANCEL_OPTION) == JOptionPane.OK_OPTION) {
            try {
                String name = nameField.getText();
                double amount = Double.parseDouble(amountField.getText());
                double rate = Double.parseDouble(rateField.getText());
                Bond bond = new Bond(name, amount, rate);
                portfolio.addInvestment(bond);
                refreshPortfolioView();
                refreshCharts();
            } catch (NumberFormatException ex) {
                JOptionPane.showMessageDialog(this, "Invalid input!");
            }
        }
    }

    private void showSimulationSettings() {
        JTextField volatilityField = new JTextField(String.valueOf(volatility));
        JTextField intervalField = new JTextField(String.valueOf(updateInterval / 1000));
        JTextField dividendField = new JTextField(String.valueOf(dividendRate));
        Object[] message = {"Volatility (0-1):", volatilityField, "Update Interval (seconds):", intervalField,
                            "Dividend Rate (0-1 per update):", dividendField};
        if (JOptionPane.showConfirmDialog(this, message, "Simulation Settings", JOptionPane.OK_CANCEL_OPTION) == JOptionPane.OK_OPTION) {
            try {
                volatility = Double.parseDouble(volatilityField.getText());
                updateInterval = (int) (Double.parseDouble(intervalField.getText()) * 1000);
                dividendRate = Double.parseDouble(dividendField.getText());
                if (simulationTimer != null) simulationTimer.setDelay(updateInterval);
            } catch (NumberFormatException ex) {
                JOptionPane.showMessageDialog(this, "Invalid input!");
            }
        }
    }

    private void startSimulation() {
        if (simulationTimer != null && simulationTimer.isRunning()) return;
        simulationTimer = new Timer(updateInterval, e -> simulateMarket());
        simulationTimer.start();
    }

    private void stopSimulation() {
        if (simulationTimer != null) simulationTimer.stop();
    }

    private void simulateMarket() {
        Map<String, Double> sectorMovements = new HashMap<>();
        for (Investment inv : portfolio.getInvestments()) {
            if (inv instanceof Stock stock) {
                sectorMovements.putIfAbsent(stock.getSector(), (Math.random() * 2 * volatility - volatility));
            }
        }

        for (Investment inv : portfolio.getInvestments()) {
            if (inv instanceof Stock stock) {
                double sectorFactor = sectorMovements.get(stock.getSector());
                double randomFactor = (Math.random() * 2 * volatility - volatility) * 0.5;
                double newPrice = stock.getCurrentPricePerShare() * (1 + sectorFactor + randomFactor);
                stock.setCurrentPricePerShare(newPrice);
                stock.addDividend(stock.getCurrentValue() * dividendRate);
            } else if (inv instanceof Bond bond) {
                double interest = bond.getCurrentValue() * bond.getInterestRate() / 100;
                bond.addInterest(interest);
            }
        }

        triggerMarketEvents();
        portfolio.recordSnapshot("Market Update");
        refreshPortfolioView();
        refreshCharts();
    }

    private void triggerMarketEvents() {
        double chance = Math.random();
        if (chance < 0.01) {
            JOptionPane.showMessageDialog(this, "Market Crash! Stocks down 20%");
            for (Investment inv : portfolio.getInvestments()) {
                if (inv instanceof Stock stock) stock.setCurrentPricePerShare(stock.getCurrentPricePerShare() * 0.8);
            }
        } else if (chance > 0.99) {
            JOptionPane.showMessageDialog(this, "Market Boom! Stocks up 20%");
            for (Investment inv : portfolio.getInvestments()) {
                if (inv instanceof Stock stock) stock.setCurrentPricePerShare(stock.getCurrentPricePerShare() * 1.2);
            }
        }
    }

    private void showInvestmentSuggestions() {
        Investment best = portfolio.getInvestments().stream().max(Comparator.comparingDouble(Investment::calculateReturn)).orElse(null);
        Investment worst = portfolio.getInvestments().stream().min(Comparator.comparingDouble(Investment::calculateReturn)).orElse(null);
        String msg = "Top performer: " + (best != null ? best.getName() : "N/A") + "\n" +
                     "Worst performer: " + (worst != null ? worst.getName() : "N/A") + "\n" +
                     "Consider rebalancing underperformers.";
        JOptionPane.showMessageDialog(this, msg, "Investment Suggestions", JOptionPane.INFORMATION_MESSAGE);
    }

    private void refreshPortfolioView() {
        String[] columns = {"Name", "Current Value", "Amount Invested", "Return"};
        Object[][] data = new Object[portfolio.getInvestments().size()][4];
        int i = 0;
        for (Investment inv : portfolio.getInvestments()) {
            data[i][0] = inv.getName();
            data[i][1] = String.format("%.2f", inv.getCurrentValue());
            data[i][2] = String.format("%.2f", inv.getAmountInvested());
            data[i][3] = String.format("%.2f", inv.calculateReturn());
            i++;
        }
        portfolioTable.setModel(new javax.swing.table.DefaultTableModel(data, columns));
    }

    private void refreshCharts() {
        chartPanel.removeAll();
        chartPanel.add(createAllocationChart());
        chartPanel.add(createReturnsChart());
        chartPanel.add(createGrowthChart());
        chartPanel.revalidate();
        chartPanel.repaint();
    }

    private ChartPanel createAllocationChart() {
        DefaultPieDataset dataset = new DefaultPieDataset();
        for (Investment inv : portfolio.getInvestments()) {
            dataset.setValue(inv.getName(), inv.getCurrentValue());
        }
        JFreeChart chart = ChartFactory.createPieChart("Portfolio Allocation", dataset, true, true, false);
        ChartPanel panel = new ChartPanel(chart);
        panel.addChartMouseListener(new ChartMouseListener() {
            public void chartMouseClicked(ChartMouseEvent e) {
                PiePlot plot = (PiePlot) chart.getPlot();
                Comparable key = plot.getDataset().getKey(0);
                JOptionPane.showMessageDialog(panel, "Clicked: " + key);
            }
            public void chartMouseMoved(ChartMouseEvent e) {}
        });
        return panel;
    }

    private ChartPanel createReturnsChart() {
        DefaultCategoryDataset dataset = new DefaultCategoryDataset();
        for (Investment inv : portfolio.getInvestments()) {
            dataset.addValue(inv.calculateReturn(), "Return", inv.getName());
        }
        return new ChartPanel(ChartFactory.createBarChart("Investment Returns", "Investment", "Return ($)", dataset,
                PlotOrientation.VERTICAL, false, true, false));
    }

    private ChartPanel createGrowthChart() {
        DefaultCategoryDataset dataset = new DefaultCategoryDataset();
        DateTimeFormatter formatter = DateTimeFormatter.ofPattern("HH:mm:ss");
        int step = 1;
        for (PortfolioSnapshot snap : portfolio.getHistory()) {
            dataset.addValue(snap.getTotalValue(), "Total Value", step++ + " (" + snap.getTimestamp().format(formatter) + ")");
        }
        return new ChartPanel(ChartFactory.createLineChart("Portfolio Growth", "Step", "Total Value ($)", dataset,
                PlotOrientation.VERTICAL, false, true, false));
    }

    private void saveChartAsImage(JFreeChart chart, String filename) {
        try {
            ChartUtils.saveChartAsPNG(new File(filename), chart, 600, 400);
            JOptionPane.showMessageDialog(this, "Chart saved as " + filename);
        } catch (Exception e) {
            JOptionPane.showMessageDialog(this, "Error saving chart: " + e.getMessage());
        }
    }

    public static void main(String[] args) {
        SwingUtilities.invokeLater(() -> {
            InvestmentDashboard dashboard = new InvestmentDashboard();
            dashboard.setVisible(true);
        });
    }
}
