import java.util.ArrayList;
import java.util.Scanner;

class Product {
    private int id;
    private String name;
    private String version;
    private double price;

    public Product(int id, String name, String version, double price) {
        this.id = id;
        this.name = name;
        this.version = version;
        this.price = price;
    }

    public int getId() {
        return id;
    }

    public String getName() {
        return name;
    }

    public String getVersion() {
        return version;
    }

    public double getPrice() {
        return price;
    }

    public void setName(String name) {
        this.name = name;
    }

    public void setVersion(String version) {
        this.version = version;
    }

    public void setPrice(double price) {
        this.price = price;
    }

    @Override
    public String toString() {
        return "ID: " + id + ", Name: " + name + ", Version: " + version + ", Price: $" + price;
    }
}

class ProductManager {
    private ArrayList<Product> products = new ArrayList<>();

    public void addProduct(Product product) {
        products.add(product);
        System.out.println("Product added successfully!");
    }

    public void listProducts() {
        if (products.isEmpty()) {
            System.out.println("No products available.");
            return;
        }
        for (Product p : products) {
            System.out.println(p);
        }
    }

    public Product findProductById(int id) {
        for (Product p : products) {
            if (p.getId() == id) return p;
        }
        return null;
    }

    public void updateProduct(int id, String name, String version, double price) {
        Product p = findProductById(id);
        if (p != null) {
            p.setName(name);
            p.setVersion(version);
            p.setPrice(price);
            System.out.println("Product updated successfully!");
        } else {
            System.out.println("Product not found.");
        }
    }

    public void deleteProduct(int id) {
        Product p = findProductById(id);
        if (p != null) {
            products.remove(p);
            System.out.println("Product deleted successfully!");
        } else {
            System.out.println("Product not found.");
        }
    }
}

public class SoftwareProductManagementSystem {
    public static void main(String[] args) {
        Scanner scanner = new Scanner(System.in);
        ProductManager manager = new ProductManager();
        boolean running = true;

        while (running) {
            System.out.println("\n--- Software Product Management System ---");
            System.out.println("1. Add Product");
            System.out.println("2. List Products");
            System.out.println("3. Update Product");
            System.out.println("4. Delete Product");
            System.out.println("5. Exit");
            System.out.print("Choose an option: ");

            int choice = scanner.nextInt();
            scanner.nextLine(); // consume newline

            switch (choice) {
                case 1:
                    System.out.print("Enter product ID: ");
                    int id = scanner.nextInt();
                    scanner.nextLine();
                    System.out.print("Enter product name: ");
                    String name = scanner.nextLine();
                    System.out.print("Enter product version: ");
                    String version = scanner.nextLine();
                    System.out.print("Enter product price: ");
                    double price = scanner.nextDouble();
                    scanner.nextLine();
                    manager.addProduct(new Product(id, name, version, price));
                    break;
                case 2:
                    manager.listProducts();
                    break;
                case 3:
                    System.out.print("Enter product ID to update: ");
                    int updateId = scanner.nextInt();
                    scanner.nextLine();
                    System.out.print("Enter new name: ");
                    String newName = scanner.nextLine();
                    System.out.print("Enter new version: ");
                    String newVersion = scanner.nextLine();
                    System.out.print("Enter new price: ");
                    double newPrice = scanner.nextDouble();
                    scanner.nextLine();
                    manager.updateProduct(updateId, newName, newVersion, newPrice);
                    break;
                case 4:
                    System.out.print("Enter product ID to delete: ");
                    int deleteId = scanner.nextInt();
                    scanner.nextLine();
                    manager.deleteProduct(deleteId);
                    break;
                case 5:
                    running = false;
                    System.out.println("Exiting system. Goodbye!");
                    break;
                default:
                    System.out.println("Invalid option. Try again.");
            }
        }

        scanner.close();
    }
}
