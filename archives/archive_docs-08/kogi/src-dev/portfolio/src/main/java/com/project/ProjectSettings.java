/**
 * @license
 * @brief
 */
package com.project;

public class ProjectSettings() {

}

public class ProjectOptions {

}

public class ProjectConfiguration {

}

public class ProjectVersion {
    Int major;
    Int minor;
    Int patch;
    Int extra;
}

/**
 * @brief project model
 */
public class Project {
    private Long id;
    private String name;
    private ProjectSettings settings;
    private Array<String> tags;
    private ProjectVersion version;
    private ProjectCharter charter;
    private ProjectSchedule schedule;
    private ProjectCalender calender;
    private ProjectBoard board;
    private ProjectBook book;
    private ProjectWorkspace workspace;

    public void updateSettings(ProjectSettings newSettings) {
        this.settings = newSettings;
    }

    public void updateOptions()  {

    }
}

public class ProjectTool {

}

public class ProjectChat {
    public void newChat() {

    }

    public void sendMessage() {

    }
}

public class ProjectWorkspace {
    public void createFile() {

    }

    public void removeFile() {

    }

    public void moveFile() {

    }

    public void craateFolder() {

    }

    public void removeFolder() {

    }

    public void moveFolder() [

    ]

    public void uploadFile() {

    }

    public void downloadFile() {

    }
}

public class ProjectCalender {
    Long ID;
    String name;
}

public class ProjectEvent {
    Long ID;
    String name;
}

public class ProjectSchedule {
    Long ID;
    String name;
}

public class ProjectCharter {
    Long ID;
    String name;
}

public class ProjectLibrary {
    Long ID;
    String name;
}