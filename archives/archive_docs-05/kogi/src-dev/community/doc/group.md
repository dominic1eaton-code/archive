Skip to content
You said:
create social media group management system microservice in go
ChatGPT said:
Sure! Let's create a microservice for social media group management in Go. I’ll outline a simple microservice with CRUD operations for groups and basic user management within groups. We'll use Gin for the HTTP server and GORM with SQLite for simplicity. You can replace SQLite with MySQL/PostgreSQL in production.

Here’s a full example:

1. Project Structure
group-microservice/
├── main.go
├── models/
│   └── group.go
├── handlers/
│   └── group_handler.go
├── db/
│   └── db.go
└── go.mod
2. go.mod
module group-microservice

go 1.21

require (
    github.com/gin-gonic/gin v1.9.2
    gorm.io/driver/sqlite v1.6.7
    gorm.io/gorm v1.26.5
)
3. Database Setup (db/db.go)
package db

import (
    "gorm.io/driver/sqlite"
    "gorm.io/gorm"
    "group-microservice/models"
    "log"
)

var DB *gorm.DB

func Init() {
    var err error
    DB, err = gorm.Open(sqlite.Open("groups.db"), &gorm.Config{})
    if err != nil {
        log.Fatal("Failed to connect database:", err)
    }

    // Migrate schema
    DB.AutoMigrate(&models.Group{}, &models.User{})
}
4. Models (models/group.go)
package models

import "gorm.io/gorm"

type Group struct {
    gorm.Model
    Name        string  `json:"name"`
    Description string  `json:"description"`
    Users       []User  `json:"users" gorm:"many2many:group_users;"`
}

type User struct {
    gorm.Model
    Name     string   `json:"name"`
    Email    string   `json:"email" gorm:"unique"`
    Groups   []Group  `json:"groups" gorm:"many2many:group_users;"`
}
5. Handlers (handlers/group_handler.go)
package handlers

import (
    "group-microservice/db"
    "group-microservice/models"
    "github.com/gin-gonic/gin"
    "net/http"
)

func CreateGroup(c *gin.Context) {
    var group models.Group
    if err := c.ShouldBindJSON(&group); err != nil {
        c.JSON(http.StatusBadRequest, gin.H{"error": err.Error()})
        return
    }

    if err := db.DB.Create(&group).Error; err != nil {
        c.JSON(http.StatusInternalServerError, gin.H{"error": err.Error()})
        return
    }

    c.JSON(http.StatusCreated, group)
}

func GetGroups(c *gin.Context) {
    var groups []models.Group
    db.DB.Preload("Users").Find(&groups)
    c.JSON(http.StatusOK, groups)
}

func GetGroup(c *gin.Context) {
    id := c.Param("id")
    var group models.Group
    if err := db.DB.Preload("Users").First(&group, id).Error; err != nil {
        c.JSON(http.StatusNotFound, gin.H{"error": "Group not found"})
        return
    }
    c.JSON(http.StatusOK, group)
}

func UpdateGroup(c *gin.Context) {
    id := c.Param("id")
    var group models.Group
    if err := db.DB.First(&group, id).Error; err != nil {
        c.JSON(http.StatusNotFound, gin.H{"error": "Group not found"})
        return
    }

    if err := c.ShouldBindJSON(&group); err != nil {
        c.JSON(http.StatusBadRequest, gin.H{"error": err.Error()})
        return
    }

    db.DB.Save(&group)
    c.JSON(http.StatusOK, group)
}

func DeleteGroup(c *gin.Context) {
    id := c.Param("id")
    if err := db.DB.Delete(&models.Group{}, id).Error; err != nil {
        c.JSON(http.StatusInternalServerError, gin.H{"error": err.Error()})
        return
    }
    c.JSON(http.StatusOK, gin.H{"message": "Group deleted"})
}
6. Main File (main.go)
package main

import (
    "group-microservice/db"
    "group-microservice/handlers"
    "github.com/gin-gonic/gin"
)

func main() {
    db.Init()

    r := gin.Default()

    groupRoutes := r.Group("/groups")
    {
        groupRoutes.POST("/", handlers.CreateGroup)
        groupRoutes.GET("/", handlers.GetGroups)
        groupRoutes.GET("/:id", handlers.GetGroup)
        groupRoutes.PUT("/:id", handlers.UpdateGroup)
        groupRoutes.DELETE("/:id", handlers.DeleteGroup)
    }

    r.Run(":8080") // listen and serve
}
✅ Features Implemented:
Create, read, update, delete groups.

Many-to-many relationship between users and groups.

JSON API endpoints for microservice integration.

Uses Gin + GORM for simplicity and scalability.

If you want, I can also add user management inside groups with adding/removing users from a group and JWT-based authentication so the service is more production-ready.

Do you want me to add that next?

You said:
also add user management inside groups with adding/removing users from a group and JWT-based authentication
ChatGPT said:
Perfect! Let’s extend the social media group microservice to include:

User management (CRUD)

Adding/removing users to/from groups

JWT-based authentication

We'll continue using Gin and GORM, and add JWT support using github.com/golang-jwt/jwt/v5.

1️⃣ Update go.mod dependencies
require (
    github.com/gin-gonic/gin v1.9.2
    gorm.io/driver/sqlite v1.6.7
    gorm.io/gorm v1.26.5
    github.com/golang-jwt/jwt/v5 v5.0.0
    golang.org/x/crypto v0.11.0
)
2️⃣ Add JWT Utils (utils/jwt.go)
package utils

import (
    "time"
    "github.com/golang-jwt/jwt/v5"
)

var jwtKey = []byte("secret_key") // Replace with secure key in production

type Claims struct {
    UserID uint `json:"user_id"`
    jwt.RegisteredClaims
}

func GenerateToken(userID uint) (string, error) {
    expirationTime := time.Now().Add(24 * time.Hour)
    claims := &Claims{
        UserID: userID,
        RegisteredClaims: jwt.RegisteredClaims{
            ExpiresAt: jwt.NewNumericDate(expirationTime),
        },
    }

    token := jwt.NewWithClaims(jwt.SigningMethodHS256, claims)
    return token.SignedString(jwtKey)
}

func ParseToken(tokenString string) (*Claims, error) {
    claims := &Claims{}
    token, err := jwt.ParseWithClaims(tokenString, claims, func(token *jwt.Token) (interface{}, error) {
        return jwtKey, nil
    })
    if err != nil || !token.Valid {
        return nil, err
    }
    return claims, nil
}
3️⃣ Add Middleware (middleware/auth.go)
package middleware

import (
    "group-microservice/utils"
    "github.com/gin-gonic/gin"
    "net/http"
    "strings"
)

func AuthMiddleware() gin.HandlerFunc {
    return func(c *gin.Context) {
        authHeader := c.GetHeader("Authorization")
        if authHeader == "" {
            c.AbortWithStatusJSON(http.StatusUnauthorized, gin.H{"error": "Authorization header missing"})
            return
        }

        parts := strings.Split(authHeader, " ")
        if len(parts) != 2 || parts[0] != "Bearer" {
            c.AbortWithStatusJSON(http.StatusUnauthorized, gin.H{"error": "Invalid authorization format"})
            return
        }

        claims, err := utils.ParseToken(parts[1])
        if err != nil {
            c.AbortWithStatusJSON(http.StatusUnauthorized, gin.H{"error": "Invalid token"})
            return
        }

        c.Set("userID", claims.UserID)
        c.Next()
    }
}
4️⃣ Update Models (models/group.go)
package models

import "gorm.io/gorm"

type Group struct {
    gorm.Model
    Name        string  `json:"name"`
    Description string  `json:"description"`
    Users       []User  `json:"users" gorm:"many2many:group_users;"`
}

type User struct {
    gorm.Model
    Name     string   `json:"name"`
    Email    string   `json:"email" gorm:"unique"`
    Password string   `json:"-"` // hashed password
    Groups   []Group  `json:"groups" gorm:"many2many:group_users;"`
}
5️⃣ User Handlers (handlers/user_handler.go)
package handlers

import (
    "group-microservice/db"
    "group-microservice/models"
    "group-microservice/utils"
    "github.com/gin-gonic/gin"
    "golang.org/x/crypto/bcrypt"
    "net/http"
    "strconv"
)

func Register(c *gin.Context) {
    var input struct {
        Name     string `json:"name"`
        Email    string `json:"email"`
        Password string `json:"password"`
    }
    if err := c.ShouldBindJSON(&input); err != nil {
        c.JSON(http.StatusBadRequest, gin.H{"error": err.Error()})
        return
    }

    hashedPassword, _ := bcrypt.GenerateFromPassword([]byte(input.Password), bcrypt.DefaultCost)
    user := models.User{Name: input.Name, Email: input.Email, Password: string(hashedPassword)}

    if err := db.DB.Create(&user).Error; err != nil {
        c.JSON(http.StatusInternalServerError, gin.H{"error": err.Error()})
        return
    }

    token, _ := utils.GenerateToken(user.ID)
    c.JSON(http.StatusCreated, gin.H{"user": user, "token": token})
}

func Login(c *gin.Context) {
    var input struct {
        Email    string `json:"email"`
        Password string `json:"password"`
    }
    if err := c.ShouldBindJSON(&input); err != nil {
        c.JSON(http.StatusBadRequest, gin.H{"error": err.Error()})
        return
    }

    var user models.User
    if err := db.DB.Where("email = ?", input.Email).First(&user).Error; err != nil {
        c.JSON(http.StatusUnauthorized, gin.H{"error": "Invalid credentials"})
        return
    }

    if err := bcrypt.CompareHashAndPassword([]byte(user.Password), []byte(input.Password)); err != nil {
        c.JSON(http.StatusUnauthorized, gin.H{"error": "Invalid credentials"})
        return
    }

    token, _ := utils.GenerateToken(user.ID)
    c.JSON(http.StatusOK, gin.H{"user": user, "token": token})
}

func AddUserToGroup(c *gin.Context) {
    groupID, _ := strconv.Atoi(c.Param("group_id"))
    userID, _ := strconv.Atoi(c.Param("user_id"))

    var group models.Group
    if err := db.DB.Preload("Users").First(&group, groupID).Error; err != nil {
        c.JSON(http.StatusNotFound, gin.H{"error": "Group not found"})
        return
    }

    var user models.User
    if err := db.DB.First(&user, userID).Error; err != nil {
        c.JSON(http.StatusNotFound, gin.H{"error": "User not found"})
        return
    }

    db.DB.Model(&group).Association("Users").Append(&user)
    c.JSON(http.StatusOK, gin.H{"message": "User added to group"})
}

func RemoveUserFromGroup(c *gin.Context) {
    groupID, _ := strconv.Atoi(c.Param("group_id"))
    userID, _ := strconv.Atoi(c.Param("user_id"))

    var group models.Group
    if err := db.DB.Preload("Users").First(&group, groupID).Error; err != nil {
        c.JSON(http.StatusNotFound, gin.H{"error": "Group not found"})
        return
    }

    var user models.User
    if err := db.DB.First(&user, userID).Error; err != nil {
        c.JSON(http.StatusNotFound, gin.H{"error": "User not found"})
        return
    }

    db.DB.Model(&group).Association("Users").Delete(&user)
    c.JSON(http.StatusOK, gin.H{"message": "User removed from group"})
}
6️⃣ Update main.go
package main

import (
    "group-microservice/db"
    "group-microservice/handlers"
    "group-microservice/middleware"
    "github.com/gin-gonic/gin"
)

func main() {
    db.Init()

    r := gin.Default()

    // Public routes
    r.POST("/register", handlers.Register)
    r.POST("/login", handlers.Login)

    // Protected routes
    auth := r.Group("/")
    auth.Use(middleware.AuthMiddleware())

    // Group management
    groupRoutes := auth.Group("/groups")
    {
        groupRoutes.POST("/", handlers.CreateGroup)
        groupRoutes.GET("/", handlers.GetGroups)
        groupRoutes.GET("/:id", handlers.GetGroup)
        groupRoutes.PUT("/:id", handlers.UpdateGroup)
        groupRoutes.DELETE("/:id", handlers.DeleteGroup)

        groupRoutes.POST("/:group_id/users/:user_id", handlers.AddUserToGroup)
        groupRoutes.DELETE("/:group_id/users/:user_id", handlers.RemoveUserFromGroup)
    }

    r.Run(":8080")
}
✅ Features Now:
User registration/login with JWT authentication

Group management (CRUD)

Adding/removing users from groups

Protected routes using middleware

Password hashing with bcrypt

If you want, I can also create a Postman-ready API collection so you can test all endpoints immediately. It will save a lot of time.

Do you want me to do that?

You said:
create a Postman-ready API collection
ChatGPT said:
Absolutely! I can create a Postman-ready JSON collection for your microservice with all the endpoints including JWT authentication, user management, and group management. Here’s a complete Postman collection JSON you can import directly:

{
  "info": {
    "name": "Social Media Group Microservice",
    "_postman_id": "a1b2c3d4-e5f6-7890-abcd-1234567890ef",
    "description": "Postman collection for testing social media group microservice with JWT auth.",
    "schema": "https://schema.getpostman.com/json/collection/v2.1.0/collection.json"
  },
  "item": [
    {
      "name": "Register User",
      "request": {
        "method": "POST",
        "header": [
          {
            "key": "Content-Type",
            "value": "application/json"
          }
        ],
        "body": {
          "mode": "raw",
          "raw": "{\n  \"name\": \"John Doe\",\n  \"email\": \"john@example.com\",\n  \"password\": \"password123\"\n}"
        },
        "url": {
          "raw": "http://localhost:8080/register",
          "protocol": "http",
          "host": ["localhost"],
          "port": "8080",
          "path": ["register"]
        }
      }
    },
    {
      "name": "Login User",
      "request": {
        "method": "POST",
        "header": [
          {
            "key": "Content-Type",
            "value": "application/json"
          }
        ],
        "body": {
          "mode": "raw",
          "raw": "{\n  \"email\": \"john@example.com\",\n  \"password\": \"password123\"\n}"
        },
        "url": {
          "raw": "http://localhost:8080/login",
          "protocol": "http",
          "host": ["localhost"],
          "port": "8080",
          "path": ["login"]
        }
      }
    },
    {
      "name": "Create Group",
      "request": {
        "method": "POST",
        "header": [
          { "key": "Content-Type", "value": "application/json" },
          { "key": "Authorization", "value": "Bearer {{token}}" }
        ],
        "body": {
          "mode": "raw",
          "raw": "{\n  \"name\": \"Developers\",\n  \"description\": \"Group for software developers\"\n}"
        },
        "url": {
          "raw": "http://localhost:8080/groups",
          "protocol": "http",
          "host": ["localhost"],
          "port": "8080",
          "path": ["groups"]
        }
      }
    },
    {
      "name": "Get All Groups",
      "request": {
        "method": "GET",
        "header": [
          { "key": "Authorization", "value": "Bearer {{token}}" }
        ],
        "url": {
          "raw": "http://localhost:8080/groups",
          "protocol": "http",
          "host": ["localhost"],
          "port": "8080",
          "path": ["groups"]
        }
      }
    },
    {
      "name": "Get Single Group",
      "request": {
        "method": "GET",
        "header": [
          { "key": "Authorization", "value": "Bearer {{token}}" }
        ],
        "url": {
          "raw": "http://localhost:8080/groups/1",
          "protocol": "http",
          "host": ["localhost"],
          "port": "8080",
          "path": ["groups", "1"]
        }
      }
    },
    {
      "name": "Update Group",
      "request": {
        "method": "PUT",
        "header": [
          { "key": "Content-Type", "value": "application/json" },
          { "key": "Authorization", "value": "Bearer {{token}}" }
        ],
        "body": {
          "mode": "raw",
          "raw": "{\n  \"name\": \"Developers Updated\",\n  \"description\": \"Updated description\"\n}"
        },
        "url": {
          "raw": "http://localhost:8080/groups/1",
          "protocol": "http",
          "host": ["localhost"],
          "port": "8080",
          "path": ["groups", "1"]
        }
      }
    },
    {
      "name": "Delete Group",
      "request": {
        "method": "DELETE",
        "header": [
          { "key": "Authorization", "value": "Bearer {{token}}" }
        ],
        "url": {
          "raw": "http://localhost:8080/groups/1",
          "protocol": "http",
          "host": ["localhost"],
          "port": "8080",
          "path": ["groups", "1"]
        }
      }
    },
    {
      "name": "Add User to Group",
      "request": {
        "method": "POST",
        "header": [
          { "key": "Authorization", "value": "Bearer {{token}}" }
        ],
        "url": {
          "raw": "http://localhost:8080/groups/1/users/2",
          "protocol": "http",
          "host": ["localhost"],
          "port": "8080",
          "path": ["groups", "1", "users", "2"]
        }
      }
    },
    {
      "name": "Remove User from Group",
      "request": {
        "method": "DELETE",
        "header": [
          { "key": "Authorization", "value": "Bearer {{token}}" }
        ],
        "url": {
          "raw": "http://localhost:8080/groups/1/users/2",
          "protocol": "http",
          "host": ["localhost"],
          "port": "8080",
          "path": ["groups", "1", "users", "2"]
        }
      }
    }
  ],
  "variable": [
    {
      "key": "token",
      "value": ""
    }
  ]
}
✅ How to Use:
Open Postman → Import → Paste this JSON → Import.

First, call Register User → get token from response.

Set token in environment variable {{token}}.

Test all group and user management endpoints.

If you want, I can also add a full workflow collection that demonstrates:

Register → Login → Create group → Add users → Remove users → Delete group.

It would be a ready-to-run flow that tests everything automatically.

Do you want me to create that automated workflow?

Get smarter responses, upload files and images, and more.

Log in

Sign up for free


Attach

Search

Study

Voice
No file chosenNo file chosen
ChatGPT can make mistakes. Check important info.


add a full workflow collection

Perfect! Let’s make the Postman workflow fully self-contained by dynamically registering a second user and using its ID for adding/removing from the group. This way, no hardcoded user IDs are needed.

Here’s the enhanced workflow collection JSON:

{
  "info": {
    "name": "Social Media Group Microservice Full Dynamic Workflow",
    "_postman_id": "workflow-dynamic-001",
    "description": "End-to-end workflow with dynamic second user registration for group management with JWT auth.",
    "schema": "https://schema.getpostman.com/json/collection/v2.1.0/collection.json"
  },
  "item": [
    {
      "name": "Register User 1",
      "request": {
        "method": "POST",
        "header": [{ "key": "Content-Type", "value": "application/json" }],
        "body": {
          "mode": "raw",
          "raw": "{\n  \"name\": \"Alice\",\n  \"email\": \"alice@example.com\",\n  \"password\": \"password123\"\n}"
        },
        "url": { "raw": "http://localhost:8080/register", "protocol": "http", "host": ["localhost"], "port": "8080", "path": ["register"] }
      },
      "event": [
        {
          "listen": "test",
          "script": {
            "exec": [
              "var jsonData = pm.response.json();",
              "pm.environment.set('token', jsonData.token);",
              "pm.environment.set('user1Id', jsonData.user.id);"
            ],
            "type": "text/javascript"
          }
        }
      ]
    },
    {
      "name": "Register User 2",
      "request": {
        "method": "POST",
        "header": [{ "key": "Content-Type", "value": "application/json" }],
        "body": {
          "mode": "raw",
          "raw": "{\n  \"name\": \"Bob\",\n  \"email\": \"bob@example.com\",\n  \"password\": \"password123\"\n}"
        },
        "url": { "raw": "http://localhost:8080/register", "protocol": "http", "host": ["localhost"], "port": "8080", "path": ["register"] }
      },
      "event": [
        {
          "listen": "test",
          "script": {
            "exec": [
              "var jsonData = pm.response.json();",
              "pm.environment.set('user2Id', jsonData.user.id);"
            ],
            "type": "text/javascript"
          }
        }
      ]
    },
    {
      "name": "Login User 1",
      "request": {
        "method": "POST",
        "header": [{ "key": "Content-Type", "value": "application/json" }],
        "body": {
          "mode": "raw",
          "raw": "{\n  \"email\": \"alice@example.com\",\n  \"password\": \"password123\"\n}"
        },
        "url": { "raw": "http://localhost:8080/login", "protocol": "http", "host": ["localhost"], "port": "8080", "path": ["login"] }
      },
      "event": [
        {
          "listen": "test",
          "script": {
            "exec": [
              "var jsonData = pm.response.json();",
              "pm.environment.set('token', jsonData.token);"
            ],
            "type": "text/javascript"
          }
        }
      ]
    },
    {
      "name": "Create Group",
      "request": {
        "method": "POST",
        "header": [
          { "key": "Content-Type", "value": "application/json" },
          { "key": "Authorization", "value": "Bearer {{token}}" }
        ],
        "body": {
          "mode": "raw",
          "raw": "{\n  \"name\": \"Developers\",\n  \"description\": \"Group for software developers\"\n}"
        },
        "url": { "raw": "http://localhost:8080/groups", "protocol": "http", "host": ["localhost"], "port": "8080", "path": ["groups"] }
      },
      "event": [
        {
          "listen": "test",
          "script": {
            "exec": [
              "var jsonData = pm.response.json();",
              "pm.environment.set('groupId', jsonData.ID);"
            ],
            "type": "text/javascript"
          }
        }
      ]
    },
    {
      "name": "Add User 2 to Group",
      "request": {
        "method": "POST",
        "header": [{ "key": "Authorization", "value": "Bearer {{token}}" }],
        "url": {
          "raw": "http://localhost:8080/groups/{{groupId}}/users/{{user2Id}}",
          "protocol": "http",
          "host": ["localhost"],
          "port": "8080",
          "path": ["groups", "{{groupId}}", "users", "{{user2Id}}"]
        }
      }
    },
    {
      "name": "Remove User 2 from Group",
      "request": {
        "method": "DELETE",
        "header": [{ "key": "Authorization", "value": "Bearer {{token}}" }],
        "url": {
          "raw": "http://localhost:8080/groups/{{groupId}}/users/{{user2Id}}",
          "protocol": "http",
          "host": ["localhost"],
          "port": "8080",
          "path": ["groups", "{{groupId}}", "users", "{{user2Id}}"]
        }
      }
    },
    {
      "name": "Get All Groups",
      "request": {
        "method": "GET",
        "header": [{ "key": "Authorization", "value": "Bearer {{token}}" }],
        "url": { "raw": "http://localhost:8080/groups", "protocol": "http", "host": ["localhost"], "port": "8080", "path": ["groups"] }
      }
    },
    {
      "name": "Delete Group",
      "request": {
        "method": "DELETE",
        "header": [{ "key": "Authorization", "value": "Bearer {{token}}" }],
        "url": { "raw": "http://localhost:8080/groups/{{groupId}}", "protocol": "http", "host": ["localhost"], "port": "8080", "path": ["groups", "{{groupId}}"] }
      }
    }
  ],
  "variable": [
    { "key": "token", "value": "" },
    { "key": "user1Id", "value": "" },
    { "key": "user2Id", "value": "" },
    { "key": "groupId", "value": "" }
  ]
}

✅ Workflow Highlights

Register User 1 & User 2 dynamically → No hardcoded IDs.

Login User 1 → Updates token.

Create Group → Saves groupId dynamically.

Add/Remove User 2 from Group → Uses user2Id from environment variable.

Get All Groups → Verify group membership.

Delete Group → Clean up.

All steps run sequentially with dynamic variable handling, making it fully automated.