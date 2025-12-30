/**
 * @license
 * @brief
 */
package com.app;

public class Workspace {
    Long id;
    String name;
    String description;
    String owner;

    public Workspace(Long id, String name, String description, String owner) {
        this.id = id;
        this.name = name;
        this.description = description;
        this.owner = owner;
    }

    public Long getId() {
        return id;
    }

    public String getName() {
        return name;
    }

    public String getDescription() {
        return description;
    }

    public String getOwner() {
        return owner;
    }

    @Override
    public String toString() {
        return "Workspace{" +
                "id=" + id +
                ", name='" + name + '\'' +
                ", description='" + description + '\'' +
                ", owner='" + owner + '\'' +
                '}';
    }

    public static void main(String[] args) {
        Workspace ws = new Workspace(1L, "Portfolio Workspace", "Workspace for development", "Alice");
        System.out.println(ws);
    }

    public void displayInfo() {
        System.out.println("Workspace ID: " + id);
        System.out.println("Workspace Name: " + name);
        System.out.println("Description: " + description);
        System.out.println("Owner: " + owner);
    }

    public void updateDescription(String newDescription) {
        this.description = newDescription;
    }

    public boolean isOwnedBy(String ownerName) {
        return this.owner.equals(ownerName);
    }

    public String getSummary() {
        return "Workspace '" + name + "' owned by " + owner;
    }

    public void renameWorkspace(String newName) {
        this.name = newName;
    }

    public void changeOwner(String newOwner) {
        this.owner = newOwner;
    }

    public void clearDescription() {
        this.description = "";
    }

    public boolean hasDescription() {
        return description != null && !description.isEmpty();
    }

    public String getOwnerInfo() {
        return "Owner: " + owner;
    }

    public String getDetailedInfo() {
        return "Workspace ID: " + id + ", Name: " + name + ", Description: " + description + ", Owner: " + owner;
    }

    public void printSummary() {
        System.out.println(getSummary());
    }

    public void printDetailedInfo() {
        System.out.println(getDetailedInfo());
    }

    public void resetWorkspace() {
        this.name = "Untitled";
        this.description = "";
        this.owner = "Unknown";
    }

    public String getWorkspaceInfo() {
        return "Workspace Info - ID: " + id + ", Name: " + name + ", Description: " + description + ", Owner: " + owner;
    }

    public void displayWorkspaceInfo() {
        System.out.println(getWorkspaceInfo());
    }

    public void updateOwner(String newOwner) {
        this.owner = newOwner;
    }

    public void updateName(String newName) {
        this.name = newName;
    }

    public void updateWorkspace(Long id, String name, String description, String owner) {
        this.id = id;
        this.name = name;
        this.description = description;
        this.owner = owner;
    }

    public boolean isWorkspaceOwnedBy(String ownerName) {
        return this.owner.equals(ownerName);
    }

    public String summarizeWorkspace() {
        return "Workspace Summary: " + getSummary();
    }

    public void printWorkspaceSummary() {
        System.out.println(summarizeWorkspace());
    }

    public void displayOwnerInfo() {
        System.out.println(getOwnerInfo());
    }

    public void displayDetailedInfo() {
        System.out.println(getDetailedInfo());
    }

    public void clearWorkspaceDescription() {
        this.description = "";
    }

    public boolean workspaceHasDescription() {
        return hasDescription();
    }

    public void renameWorkspaceTo(String newName) {
        this.name = newName;
    }

    public void changeWorkspaceOwner(String newOwner) {
        this.owner = newOwner;
    }

    public void resetWorkspaceDetails() {
        this.name = "Untitled";
        this.description = "";
        this.owner = "Unknown";
    }

    public String fetchWorkspaceInfo() {
        return getWorkspaceInfo();
    }

    public void showWorkspaceInfo() {
        System.out.println(fetchWorkspaceInfo());
    }

    public void modifyWorkspaceOwner(String newOwner) {
        this.owner = newOwner;
    }

    public void modifyWorkspaceName(String newName) {
        this.name = newName;
    }

    public void modifyWorkspace(Long id, String name, String description, String owner) {
        this.id = id;
        this.name = name;
        this.description = description;
        this.owner = owner;
    }

    public boolean checkWorkspaceOwnership(String ownerName) {
        return this.owner.equals(ownerName);
    }

    public String generateWorkspaceSummary() {
        return "Workspace Summary: " + getSummary();
    }

    public void displayWorkspaceSummary() {
        System.out.println(generateWorkspaceSummary());
    }

    public void showOwnerInformation() {
        System.out.println(getOwnerInfo());
    }

    public void showDetailedInformation() {
        System.out.println(getDetailedInfo());
    }

    public void eraseWorkspaceDescription() {
        this.description = "";
    }
    
    public boolean doesWorkspaceHaveDescription() {
        return hasDescription();
    }

    public void changeWorkspaceNameTo(String newName) {
        this.name = newName;
    }

    public void changeWorkspaceOwnerTo(String newOwner) {
        this.owner = newOwner;
    }

    public void resetWorkspaceInfo() {
        this.name = "Untitled";
        this.description = "";
        this.owner = "Unknown";
    }

    public String retrieveWorkspaceInfo() {
        return getWorkspaceInfo();
    }

    public void presentWorkspaceInfo() {
        System.out.println(retrieveWorkspaceInfo());
    }

    public void createFolder() {
        System.out.println("Creating a folder in the workspace...");
    }

    public void renameFolder(String oldName, String newName) {
        System.out.println("Renaming folder from " + oldName + " to " + newName + "...");
    }

    public void deleteFolder(String folderName) {
        System.out.println("Deleting folder: " + folderName + "...");
    }

    public void listFolders() {
        System.out.println("Listing all folders in the workspace...");
    }

    public void moveFile(String fileName, String targetFolder) {
        System.out.println("Moving file " + fileName + " to folder " + targetFolder + "...");
    }

    public void copyFile(String fileName, String targetFolder) {
        System.out.println("Copying file " + fileName + " to folder " + targetFolder + "...");
    }

    public void renameFile(String oldName, String newName) {
        System.out.println("Renaming file from " + oldName + " to " + newName + "...");
    }

    public void createFile() {
        System.out.println("Creating a file in the workspace...");
    }

    public void deleteFile() {
        System.out.println("Deleting a file from the workspace...");
    }

    public void listFiles() {
        System.out.println("Listing all files in the workspace...");
    }

    public void shareWorkspace() {
        System.out.println("Sharing the workspace with others...");
    }

    public void archiveWorkspace() {
        System.out.println("Archiving the workspace...");
    }

    public void restoreWorkspace() {
        System.out.println("Restoring the workspace from archive...");
    }

    public void backupWorkspace() {
        System.out.println("Backing up the workspace...");
    }

    public void syncWorkspace() {
        System.out.println("Syncing the workspace with cloud...");
    }

    public void exportWorkspace() {
        System.out.println("Exporting the workspace data...");
    }

    public void importWorkspace() {
        System.out.println("Importing data into the workspace...");
    }

    public void collaborateInWorkspace() {
        System.out.println("Collaborating in the workspace...");
    }

    public void monitorWorkspaceActivity() {
        System.out.println("Monitoring workspace activity...");
    }

    public void optimizeWorkspace() {
        System.out.println("Optimizing workspace performance...");
    }

    public void troubleshootWorkspaceIssues() {
        System.out.println("Troubleshooting workspace issues...");
    }
}