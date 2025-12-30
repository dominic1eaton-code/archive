Skip to content
You said:
create gig worker management system in java
ChatGPT said:
Absolutely! I can help you design and implement a Gig Worker Management System in Java. I’ll outline a simple console-based version first, which you can later extend with a database or GUI if needed. This system will allow you to:

Add gig workers

View all workers

Assign tasks

Track completed tasks

Here’s a clean, modular example:

1. Worker Class
public class Worker {
    private int id;
    private String name;
    private String skill;
    private int tasksCompleted;

    public Worker(int id, String name, String skill) {
        this.id = id;
        this.name = name;
        this.skill = skill;
        this.tasksCompleted = 0;
    }

    // Getters
    public int getId() { return id; }
    public String getName() { return name; }
    public String getSkill() { return skill; }
    public int getTasksCompleted() { return tasksCompleted; }

    // Increment tasks completed
    public void completeTask() {
        tasksCompleted++;
    }

    @Override
    public String toString() {
        return "ID: " + id + ", Name: " + name + ", Skill: " + skill + ", Tasks Completed: " + tasksCompleted;
    }
}
2. Management System Class
import java.util.ArrayList;
import java.util.Scanner;

public class GigWorkerManagement {
    private ArrayList<Worker> workers = new ArrayList<>();
    private Scanner scanner = new Scanner(System.in);
    private int nextId = 1;

    // Add a new worker
    public void addWorker() {
        System.out.print("Enter worker name: ");
        String name = scanner.nextLine();
        System.out.print("Enter worker skill: ");
        String skill = scanner.nextLine();

        Worker worker = new Worker(nextId++, name, skill);
        workers.add(worker);
        System.out.println("Worker added successfully!");
    }

    // Display all workers
    public void viewWorkers() {
        if(workers.isEmpty()) {
            System.out.println("No workers found.");
            return;
        }
        for(Worker w : workers) {
            System.out.println(w);
        }
    }

    // Assign a task to a worker
    public void assignTask() {
        System.out.print("Enter worker ID to assign task: ");
        int id = Integer.parseInt(scanner.nextLine());
        Worker worker = findWorkerById(id);
        if(worker != null) {
            worker.completeTask();
            System.out.println("Task assigned to " + worker.getName());
        } else {
            System.out.println("Worker not found.");
        }
    }

    // Helper method to find worker by ID
    private Worker findWorkerById(int id) {
        for(Worker w : workers) {
            if(w.getId() == id) return w;
        }
        return null;
    }

    // Main menu
    public void menu() {
        while(true) {
            System.out.println("\n=== Gig Worker Management System ===");
            System.out.println("1. Add Worker");
            System.out.println("2. View Workers");
            System.out.println("3. Assign Task");
            System.out.println("4. Exit");
            System.out.print("Choose an option: ");
            String choice = scanner.nextLine();

            switch(choice) {
                case "1": addWorker(); break;
                case "2": viewWorkers(); break;
                case "3": assignTask(); break;
                case "4": System.out.println("Exiting..."); return;
                default: System.out.println("Invalid choice. Try again.");
            }
        }
    }

    public static void main(String[] args) {
        new GigWorkerManagement().menu();
    }
}
✅ Features
Add new gig workers with skills.

View all workers and their tasks.

Assign tasks and track completion.

This is a console-based version. If you want, I can also extend this to include:

Persistent storage using SQLite or MySQL

A GUI interface with Swing or JavaFX

Advanced features like task deadlines, payment tracking, or ratings

Do you want me to make it database-backed next?

You said:
add Advanced features like task deadlines, payment tracking, ratings
ChatGPT said:
Perfect! Let’s take your Gig Worker Management System to the next level by adding task deadlines, payment tracking, and ratings. We’ll redesign it in a modular way with separate classes for Workers and Tasks, since tasks now carry extra information.

Here’s a clean Java implementation:

1. Task Class
import java.time.LocalDate;

public class Task {
    private int id;
    private String description;
    private LocalDate deadline;
    private double payment;
    private boolean completed;

    public Task(int id, String description, LocalDate deadline, double payment) {
        this.id = id;
        this.description = description;
        this.deadline = deadline;
        this.payment = payment;
        this.completed = false;
    }

    public int getId() { return id; }
    public String getDescription() { return description; }
    public LocalDate getDeadline() { return deadline; }
    public double getPayment() { return payment; }
    public boolean isCompleted() { return completed; }

    public void markCompleted() { completed = true; }

    @Override
    public String toString() {
        return "Task ID: " + id +
               ", Description: " + description +
               ", Deadline: " + deadline +
               ", Payment: $" + payment +
               ", Completed: " + completed;
    }
}
2. Worker Class with Ratings
import java.util.ArrayList;

public class Worker {
    private int id;
    private String name;
    private String skill;
    private ArrayList<Task> tasks;
    private double rating;
    private int ratingCount;

    public Worker(int id, String name, String skill) {
        this.id = id;
        this.name = name;
        this.skill = skill;
        this.tasks = new ArrayList<>();
        this.rating = 0.0;
        this.ratingCount = 0;
    }

    public int getId() { return id; }
    public String getName() { return name; }
    public String getSkill() { return skill; }
    public ArrayList<Task> getTasks() { return tasks; }
    public double getRating() { return rating; }

    public void addTask(Task task) {
        tasks.add(task);
    }

    public void completeTask(int taskId) {
        for(Task t : tasks) {
            if(t.getId() == taskId) {
                t.markCompleted();
                System.out.println("Task completed!");
                return;
            }
        }
        System.out.println("Task not found.");
    }

    public void addRating(double newRating) {
        rating = (rating * ratingCount + newRating) / (ratingCount + 1);
        ratingCount++;
    }

    public double getTotalEarnings() {
        return tasks.stream().filter(Task::isCompleted).mapToDouble(Task::getPayment).sum();
    }

    @Override
    public String toString() {
        return "ID: " + id +
               ", Name: " + name +
               ", Skill: " + skill +
               ", Rating: " + String.format("%.2f", rating) +
               ", Total Earnings: $" + String.format("%.2f", getTotalEarnings());
    }
}
3. GigWorkerManagement Class
import java.time.LocalDate;
import java.util.ArrayList;
import java.util.Scanner;

public class GigWorkerManagement {
    private ArrayList<Worker> workers = new ArrayList<>();
    private int nextWorkerId = 1;
    private int nextTaskId = 1;
    private Scanner scanner = new Scanner(System.in);

    // Add worker
    public void addWorker() {
        System.out.print("Enter worker name: ");
        String name = scanner.nextLine();
        System.out.print("Enter worker skill: ");
        String skill = scanner.nextLine();
        workers.add(new Worker(nextWorkerId++, name, skill));
        System.out.println("Worker added successfully!");
    }

    // View workers
    public void viewWorkers() {
        if(workers.isEmpty()) {
            System.out.println("No workers available.");
            return;
        }
        for(Worker w : workers) {
            System.out.println(w);
        }
    }

    // Assign task
    public void assignTask() {
        System.out.print("Enter worker ID: ");
        int workerId = Integer.parseInt(scanner.nextLine());
        Worker worker = findWorkerById(workerId);
        if(worker == null) {
            System.out.println("Worker not found.");
            return;
        }
        System.out.print("Enter task description: ");
        String desc = scanner.nextLine();
        System.out.print("Enter task deadline (YYYY-MM-DD): ");
        LocalDate deadline = LocalDate.parse(scanner.nextLine());
        System.out.print("Enter task payment: ");
        double payment = Double.parseDouble(scanner.nextLine());

        Task task = new Task(nextTaskId++, desc, deadline, payment);
        worker.addTask(task);
        System.out.println("Task assigned successfully!");
    }

    // Complete task
    public void completeTask() {
        System.out.print("Enter worker ID: ");
        int workerId = Integer.parseInt(scanner.nextLine());
        Worker worker = findWorkerById(workerId);
        if(worker == null) {
            System.out.println("Worker not found.");
            return;
        }
        System.out.print("Enter task ID to complete: ");
        int taskId = Integer.parseInt(scanner.nextLine());
        worker.completeTask(taskId);
    }

    // Rate worker
    public void rateWorker() {
        System.out.print("Enter worker ID: ");
        int workerId = Integer.parseInt(scanner.nextLine());
        Worker worker = findWorkerById(workerId);
        if(worker == null) {
            System.out.println("Worker not found.");
            return;
        }
        System.out.print("Enter rating (0.0 to 5.0): ");
        double rating = Double.parseDouble(scanner.nextLine());
        worker.addRating(rating);
        System.out.println("Rating added!");
    }

    // View worker tasks
    public void viewWorkerTasks() {
        System.out.print("Enter worker ID: ");
        int workerId = Integer.parseInt(scanner.nextLine());
        Worker worker = findWorkerById(workerId);
        if(worker == null) {
            System.out.println("Worker not found.");
            return;
        }
        ArrayList<Task> tasks = worker.getTasks();
        if(tasks.isEmpty()) {
            System.out.println("No tasks assigned.");
            return;
        }
        for(Task t : tasks) {
            System.out.println(t);
        }
    }

    private Worker findWorkerById(int id) {
        for(Worker w : workers) {
            if(w.getId() == id) return w;
        }
        return null;
    }

    public void menu() {
        while(true) {
            System.out.println("\n=== Advanced Gig Worker Management System ===");
            System.out.println("1. Add Worker");
            System.out.println("2. View Workers");
            System.out.println("3. Assign Task");
            System.out.println("4. Complete Task");
            System.out.println("5. Rate Worker");
            System.out.println("6. View Worker Tasks");
            System.out.println("7. Exit");
            System.out.print("Choose an option: ");
            String choice = scanner.nextLine();

            switch(choice) {
                case "1": addWorker(); break;
                case "2": viewWorkers(); break;
                case "3": assignTask(); break;
                case "4": completeTask(); break;
                case "5": rateWorker(); break;
                case "6": viewWorkerTasks(); break;
                case "7": System.out.println("Exiting..."); return;
                default: System.out.println("Invalid choice.");
            }
        }
    }

    public static void main(String[] args) {
        new GigWorkerManagement().menu();
    }
}
✅ New Features Added
Task deadlines using LocalDate.

Payment tracking for completed tasks.

Worker ratings, with cumulative averaging.

View worker-specific tasks.

Modular system ready for future database integration.

If you want, I can now upgrade this system with persistent storage (SQLite/MySQL) so tasks, ratings, and earnings are saved between runs. That would make it closer to a real-world application.

Do you want me to do that next?



Attach

Search

Study

Voice
No file chosenNo file chosen
ChatGPT can make mistakes. Check important info.

=============================================================================

Skip to content
You said:
create work management system in java
ChatGPT said:
Absolutely! Let’s create a basic Work Management System in Java. I’ll guide you step by step with a simple console-based version that can be expanded later for GUI or database integration. This system will allow you to:

Add tasks

List tasks

Mark tasks as completed

Delete tasks

Here’s a simple implementation:

import java.util.ArrayList;
import java.util.Scanner;

class Task {
    private String title;
    private String description;
    private boolean completed;

    public Task(String title, String description) {
        this.title = title;
        this.description = description;
        this.completed = false;
    }

    public String getTitle() {
        return title;
    }

    public String getDescription() {
        return description;
    }

    public boolean isCompleted() {
        return completed;
    }

    public void markCompleted() {
        completed = true;
    }

    @Override
    public String toString() {
        return "[" + (completed ? "✔" : "✘") + "] " + title + ": " + description;
    }
}

public class WorkManagementSystem {
    private static ArrayList<Task> tasks = new ArrayList<>();
    private static Scanner scanner = new Scanner(System.in);

    public static void main(String[] args) {
        while (true) {
            showMenu();
            int choice = getChoice();
            handleChoice(choice);
        }
    }

    private static void showMenu() {
        System.out.println("\n--- Work Management System ---");
        System.out.println("1. Add Task");
        System.out.println("2. List Tasks");
        System.out.println("3. Mark Task as Completed");
        System.out.println("4. Delete Task");
        System.out.println("5. Exit");
        System.out.print("Enter your choice: ");
    }

    private static int getChoice() {
        return scanner.nextInt();
    }

    private static void handleChoice(int choice) {
        scanner.nextLine(); // consume newline
        switch (choice) {
            case 1:
                addTask();
                break;
            case 2:
                listTasks();
                break;
            case 3:
                markTaskCompleted();
                break;
            case 4:
                deleteTask();
                break;
            case 5:
                System.out.println("Exiting... Goodbye!");
                System.exit(0);
                break;
            default:
                System.out.println("Invalid choice. Try again.");
        }
    }

    private static void addTask() {
        System.out.print("Enter task title: ");
        String title = scanner.nextLine();
        System.out.print("Enter task description: ");
        String description = scanner.nextLine();
        tasks.add(new Task(title, description));
        System.out.println("Task added successfully!");
    }

    private static void listTasks() {
        if (tasks.isEmpty()) {
            System.out.println("No tasks available.");
            return;
        }
        System.out.println("\n--- Tasks ---");
        for (int i = 0; i < tasks.size(); i++) {
            System.out.println((i + 1) + ". " + tasks.get(i));
        }
    }

    private static void markTaskCompleted() {
        listTasks();
        if (tasks.isEmpty()) return;
        System.out.print("Enter task number to mark completed: ");
        int index = scanner.nextInt() - 1;
        if (index >= 0 && index < tasks.size()) {
            tasks.get(index).markCompleted();
            System.out.println("Task marked as completed!");
        } else {
            System.out.println("Invalid task number.");
        }
    }

    private static void deleteTask() {
        listTasks();
        if (tasks.isEmpty()) return;
        System.out.print("Enter task number to delete: ");
        int index = scanner.nextInt() - 1;
        if (index >= 0 && index < tasks.size()) {
            tasks.remove(index);
            System.out.println("Task deleted!");
        } else {
            System.out.println("Invalid task number.");
        }
    }
}
✅ Features of this system:
Add Task: Enter a title and description.

List Tasks: Shows all tasks with completion status.

Mark Completed: Update a task as done.

Delete Task: Remove tasks from the list.

Exit: Close the program.

If you want, I can also upgrade this system to use a file or database, so tasks are saved even after the program exits. That would make it a more realistic work management system.

Do you want me to do that next?

You said:
upgrade this system to use a file and database
ChatGPT said:
Perfect! Let’s upgrade your Work Management System in two steps:

File-based persistence – tasks are saved to a file and loaded when the program starts.

Database-based persistence – tasks are saved to a database like SQLite for permanent storage and better querying.

We’ll start with file-based persistence first.

1️⃣ File-based Work Management System
Here, we’ll use Java’s ObjectOutputStream and ObjectInputStream to save/load tasks from a file.

import java.io.*;
import java.util.ArrayList;
import java.util.Scanner;

class Task implements Serializable {
    private static final long serialVersionUID = 1L;

    private String title;
    private String description;
    private boolean completed;

    public Task(String title, String description) {
        this.title = title;
        this.description = description;
        this.completed = false;
    }

    public void markCompleted() {
        completed = true;
    }

    public boolean isCompleted() {
        return completed;
    }

    @Override
    public String toString() {
        return "[" + (completed ? "✔" : "✘") + "] " + title + ": " + description;
    }
}

public class WorkManagementSystemFile {
    private static final String FILE_NAME = "tasks.dat";
    private static ArrayList<Task> tasks = new ArrayList<>();
    private static Scanner scanner = new Scanner(System.in);

    public static void main(String[] args) {
        loadTasksFromFile();
        while (true) {
            showMenu();
            int choice = scanner.nextInt();
            scanner.nextLine(); // consume newline
            handleChoice(choice);
        }
    }

    private static void showMenu() {
        System.out.println("\n--- Work Management System ---");
        System.out.println("1. Add Task");
        System.out.println("2. List Tasks");
        System.out.println("3. Mark Task as Completed");
        System.out.println("4. Delete Task");
        System.out.println("5. Exit");
        System.out.print("Enter your choice: ");
    }

    private static void handleChoice(int choice) {
        switch (choice) {
            case 1: addTask(); break;
            case 2: listTasks(); break;
            case 3: markTaskCompleted(); break;
            case 4: deleteTask(); break;
            case 5: saveTasksToFile(); System.exit(0); break;
            default: System.out.println("Invalid choice. Try again.");
        }
    }

    private static void addTask() {
        System.out.print("Enter task title: ");
        String title = scanner.nextLine();
        System.out.print("Enter task description: ");
        String description = scanner.nextLine();
        tasks.add(new Task(title, description));
        System.out.println("Task added successfully!");
    }

    private static void listTasks() {
        if (tasks.isEmpty()) {
            System.out.println("No tasks available.");
            return;
        }
        System.out.println("\n--- Tasks ---");
        for (int i = 0; i < tasks.size(); i++) {
            System.out.println((i + 1) + ". " + tasks.get(i));
        }
    }

    private static void markTaskCompleted() {
        listTasks();
        if (tasks.isEmpty()) return;
        System.out.print("Enter task number to mark completed: ");
        int index = scanner.nextInt() - 1;
        if (index >= 0 && index < tasks.size()) {
            tasks.get(index).markCompleted();
            System.out.println("Task marked as completed!");
        } else {
            System.out.println("Invalid task number.");
        }
    }

    private static void deleteTask() {
        listTasks();
        if (tasks.isEmpty()) return;
        System.out.print("Enter task number to delete: ");
        int index = scanner.nextInt() - 1;
        if (index >= 0 && index < tasks.size()) {
            tasks.remove(index);
            System.out.println("Task deleted!");
        } else {
            System.out.println("Invalid task number.");
        }
    }

    private static void saveTasksToFile() {
        try (ObjectOutputStream oos = new ObjectOutputStream(new FileOutputStream(FILE_NAME))) {
            oos.writeObject(tasks);
            System.out.println("Tasks saved to file!");
        } catch (IOException e) {
            System.out.println("Error saving tasks: " + e.getMessage());
        }
    }

    private static void loadTasksFromFile() {
        File file = new File(FILE_NAME);
        if (!file.exists()) return;
        try (ObjectInputStream ois = new ObjectInputStream(new FileInputStream(FILE_NAME))) {
            tasks = (ArrayList<Task>) ois.readObject();
            System.out.println("Tasks loaded from file.");
        } catch (IOException | ClassNotFoundException e) {
            System.out.println("Error loading tasks: " + e.getMessage());
        }
    }
}
✅ This version saves tasks automatically to a file (tasks.dat) and loads them when you start the program.

2️⃣ Database-based Work Management System (SQLite)
Here’s a quick version using SQLite with JDBC.

Dependencies: Add sqlite-jdbc to your project. If using Maven:

<dependency>
    <groupId>org.xerial</groupId>
    <artifactId>sqlite-jdbc</artifactId>
    <version>3.42.0.0</version>
</dependency>
Java code:

import java.sql.*;
import java.util.Scanner;

public class WorkManagementSystemDB {
    private static final String DB_URL = "jdbc:sqlite:tasks.db";
    private static Scanner scanner = new Scanner(System.in);

    public static void main(String[] args) {
        createTable();
        while (true) {
            showMenu();
            int choice = scanner.nextInt();
            scanner.nextLine(); // consume newline
            handleChoice(choice);
        }
    }

    private static void createTable() {
        String sql = "CREATE TABLE IF NOT EXISTS tasks (" +
                     "id INTEGER PRIMARY KEY AUTOINCREMENT," +
                     "title TEXT NOT NULL," +
                     "description TEXT," +
                     "completed INTEGER DEFAULT 0)";
        try (Connection conn = DriverManager.getConnection(DB_URL);
             Statement stmt = conn.createStatement()) {
            stmt.execute(sql);
        } catch (SQLException e) {
            System.out.println("Error creating table: " + e.getMessage());
        }
    }

    private static void showMenu() {
        System.out.println("\n--- Work Management System ---");
        System.out.println("1. Add Task");
        System.out.println("2. List Tasks");
        System.out.println("3. Mark Task as Completed");
        System.out.println("4. Delete Task");
        System.out.println("5. Exit");
        System.out.print("Enter your choice: ");
    }

    private static void handleChoice(int choice) {
        switch (choice) {
            case 1: addTask(); break;
            case 2: listTasks(); break;
            case 3: markTaskCompleted(); break;
            case 4: deleteTask(); break;
            case 5: System.exit(0); break;
            default: System.out.println("Invalid choice. Try again.");
        }
    }

    private static void addTask() {
        System.out.print("Enter task title: ");
        String title = scanner.nextLine();
        System.out.print("Enter task description: ");
        String description = scanner.nextLine();
        String sql = "INSERT INTO tasks(title, description) VALUES(?, ?)";
        try (Connection conn = DriverManager.getConnection(DB_URL);
             PreparedStatement pstmt = conn.prepareStatement(sql)) {
            pstmt.setString(1, title);
            pstmt.setString(2, description);
            pstmt.executeUpdate();
            System.out.println("Task added successfully!");
        } catch (SQLException e) {
            System.out.println("Error adding task: " + e.getMessage());
        }
    }

    private static void listTasks() {
        String sql = "SELECT * FROM tasks";
        try (Connection conn = DriverManager.getConnection(DB_URL);
             Statement stmt = conn.createStatement();
             ResultSet rs = stmt.executeQuery(sql)) {
            System.out.println("\n--- Tasks ---");
            while (rs.next()) {
                int id = rs.getInt("id");
                String title = rs.getString("title");
                String desc = rs.getString("description");
                boolean completed = rs.getInt("completed") == 1;
                System.out.println(id + ". [" + (completed ? "✔" : "✘") + "] " + title + ": " + desc);
            }
        } catch (SQLException e) {
            System.out.println("Error listing tasks: " + e.getMessage());
        }
    }

    private static void markTaskCompleted() {
        System.out.print("Enter task ID to mark completed: ");
        int id = scanner.nextInt();
        String sql = "UPDATE tasks SET completed = 1 WHERE id = ?";
        try (Connection conn = DriverManager.getConnection(DB_URL);
             PreparedStatement pstmt = conn.prepareStatement(sql)) {
            pstmt.setInt(1, id);
            int rows = pstmt.executeUpdate();
            if (rows > 0) System.out.println("Task marked as completed!");
            else System.out.println("Task not found.");
        } catch (SQLException e) {
            System.out.println("Error updating task: " + e.getMessage());
        }
    }

    private static void deleteTask() {
        System.out.print("Enter task ID to delete: ");
        int id = scanner.nextInt();
        String sql = "DELETE FROM tasks WHERE id = ?";
        try (Connection conn = DriverManager.getConnection(DB_URL);
             PreparedStatement pstmt = conn.prepareStatement(sql)) {
            pstmt.setInt(1, id);
            int rows = pstmt.executeUpdate();
            if (rows > 0) System.out.println("Task deleted!");
            else System.out.println("Task not found.");
        } catch (SQLException e) {
            System.out.println("Error deleting task: " + e.getMessage());
        }
    }
}
✅ This version stores tasks in an SQLite database, giving you persistent storage and the ability to scale later.

I can also combine both file and database options with a user choice, or even make a GUI version using JavaFX or Swing for a full-fledged desktop Work Management System.

Do you want me to build a GUI version next?



Attach

Search

Study

Voice
No file chosenNo file chosen
ChatGPT can make mistakes. Check important info.
