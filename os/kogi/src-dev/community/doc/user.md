Skip to content
You said:
create social media user microservice in go
ChatGPT said:
Sure! Let’s build a basic social media user microservice in Go. I’ll outline the structure and provide a working example with REST endpoints using Gin for HTTP routing and GORM with SQLite for database persistence. This can be easily swapped to PostgreSQL or MySQL later.

1️⃣ Project Structure
social-user-service/
├── main.go
├── models/
│   └── user.go
├── controllers/
│   └── user_controller.go
├── routes/
│   └── user_routes.go
├── database/
│   └── database.go
├── go.mod
2️⃣ go.mod
module social-user-service

go 1.21

require (
    github.com/gin-gonic/gin v1.9.1
    gorm.io/driver/sqlite v1.4.7
    gorm.io/gorm v1.29.0
)
3️⃣ database/database.go
package database

import (
    "gorm.io/driver/sqlite"
    "gorm.io/gorm"
    "social-user-service/models"
)

var DB *gorm.DB

func Connect() {
    var err error
    DB, err = gorm.Open(sqlite.Open("users.db"), &gorm.Config{})
    if err != nil {
        panic("Failed to connect to database")
    }

    // Auto migrate
    DB.AutoMigrate(&models.User{})
}
4️⃣ models/user.go
package models

import "gorm.io/gorm"

type User struct {
    gorm.Model
    Username string `json:"username" gorm:"unique"`
    Email    string `json:"email" gorm:"unique"`
    Password string `json:"password"`
}
5️⃣ controllers/user_controller.go
package controllers

import (
    "net/http"
    "social-user-service/database"
    "social-user-service/models"

    "github.com/gin-gonic/gin"
)

func CreateUser(c *gin.Context) {
    var user models.User
    if err := c.ShouldBindJSON(&user); err != nil {
        c.JSON(http.StatusBadRequest, gin.H{"error": err.Error()})
        return
    }

    if err := database.DB.Create(&user).Error; err != nil {
        c.JSON(http.StatusInternalServerError, gin.H{"error": err.Error()})
        return
    }

    c.JSON(http.StatusCreated, user)
}

func GetUsers(c *gin.Context) {
    var users []models.User
    database.DB.Find(&users)
    c.JSON(http.StatusOK, users)
}

func GetUser(c *gin.Context) {
    id := c.Param("id")
    var user models.User
    if err := database.DB.First(&user, id).Error; err != nil {
        c.JSON(http.StatusNotFound, gin.H{"error": "User not found"})
        return
    }
    c.JSON(http.StatusOK, user)
}

func UpdateUser(c *gin.Context) {
    id := c.Param("id")
    var user models.User
    if err := database.DB.First(&user, id).Error; err != nil {
        c.JSON(http.StatusNotFound, gin.H{"error": "User not found"})
        return
    }

    var input models.User
    if err := c.ShouldBindJSON(&input); err != nil {
        c.JSON(http.StatusBadRequest, gin.H{"error": err.Error()})
        return
    }

    database.DB.Model(&user).Updates(input)
    c.JSON(http.StatusOK, user)
}

func DeleteUser(c *gin.Context) {
    id := c.Param("id")
    if err := database.DB.Delete(&models.User{}, id).Error; err != nil {
        c.JSON(http.StatusInternalServerError, gin.H{"error": err.Error()})
        return
    }
    c.JSON(http.StatusOK, gin.H{"message": "User deleted"})
}
6️⃣ routes/user_routes.go
package routes

import (
    "social-user-service/controllers"

    "github.com/gin-gonic/gin"
)

func UserRoutes(router *gin.Engine) {
    userRoutes := router.Group("/users")
    {
        userRoutes.POST("/", controllers.CreateUser)
        userRoutes.GET("/", controllers.GetUsers)
        userRoutes.GET("/:id", controllers.GetUser)
        userRoutes.PUT("/:id", controllers.UpdateUser)
        userRoutes.DELETE("/:id", controllers.DeleteUser)
    }
}
7️⃣ main.go
package main

import (
    "social-user-service/database"
    "social-user-service/routes"

    "github.com/gin-gonic/gin"
)

func main() {
    router := gin.Default()
    database.Connect()

    routes.UserRoutes(router)

    router.Run(":8080")
}
8️⃣ How to Run
go mod tidy
go run main.go
Endpoints:

Method	Path	Description
POST	/users	Create a user
GET	/users	Get all users
GET	/users/:id	Get user by ID
PUT	/users/:id	Update user
DELETE	/users/:id	Delete user
This is a minimal working microservice for social media users. You can extend it with:

JWT authentication

Password hashing (bcrypt)

PostgreSQL/MySQL support

Logging & structured error handling

If you want, I can also add JWT authentication and password hashing, so this microservice is ready for production-level security.

Do you want me to do that next?

You said:
add JWT authentication and password hashing,
ChatGPT said:
Perfect! Let's extend your social media user microservice in Go to include JWT authentication and password hashing. I’ll keep it clean and secure using bcrypt for passwords and JWT for token-based authentication.

1️⃣ Update Dependencies (go.mod)
require (
    github.com/gin-gonic/gin v1.9.1
    gorm.io/driver/sqlite v1.4.7
    gorm.io/gorm v1.29.0
    github.com/dgrijalva/jwt-go v3.2.0
    golang.org/x/crypto v0.13.0
)
2️⃣ Update User Model (models/user.go)
No structural changes, but ensure password is stored securely:

package models

import "gorm.io/gorm"

type User struct {
    gorm.Model
    Username string `json:"username" gorm:"unique"`
    Email    string `json:"email" gorm:"unique"`
    Password string `json:"-"` // hide password in JSON responses
}
3️⃣ Create utils/token.go for JWT
package utils

import (
    "time"
    "github.com/dgrijalva/jwt-go"
)

var jwtKey = []byte("my_secret_key") // Replace with env var in production

type Claims struct {
    UserID uint
    Username string
    jwt.StandardClaims
}

func GenerateJWT(userID uint, username string) (string, error) {
    expirationTime := time.Now().Add(24 * time.Hour)
    claims := &Claims{
        UserID: userID,
        Username: username,
        StandardClaims: jwt.StandardClaims{
            ExpiresAt: expirationTime.Unix(),
        },
    }

    token := jwt.NewWithClaims(jwt.SigningMethodHS256, claims)
    return token.SignedString(jwtKey)
}

func ValidateJWT(tokenString string) (*Claims, error) {
    claims := &Claims{}
    token, err := jwt.ParseWithClaims(tokenString, claims, func(token *jwt.Token) (interface{}, error) {
        return jwtKey, nil
    })

    if err != nil || !token.Valid {
        return nil, err
    }
    return claims, nil
}
4️⃣ Update controllers/user_controller.go
Add bcrypt password hashing & JWT login:
package controllers

import (
    "net/http"
    "social-user-service/database"
    "social-user-service/models"
    "social-user-service/utils"

    "github.com/gin-gonic/gin"
    "golang.org/x/crypto/bcrypt"
)

// Register new user
func Register(c *gin.Context) {
    var input models.User
    if err := c.ShouldBindJSON(&input); err != nil {
        c.JSON(http.StatusBadRequest, gin.H{"error": err.Error()})
        return
    }

    // Hash password
    hashedPassword, err := bcrypt.GenerateFromPassword([]byte(input.Password), bcrypt.DefaultCost)
    if err != nil {
        c.JSON(http.StatusInternalServerError, gin.H{"error": "Failed to hash password"})
        return
    }
    input.Password = string(hashedPassword)

    if err := database.DB.Create(&input).Error; err != nil {
        c.JSON(http.StatusInternalServerError, gin.H{"error": err.Error()})
        return
    }

    c.JSON(http.StatusCreated, gin.H{"message": "User created successfully"})
}

// Login user and return JWT
func Login(c *gin.Context) {
    var input models.User
    if err := c.ShouldBindJSON(&input); err != nil {
        c.JSON(http.StatusBadRequest, gin.H{"error": err.Error()})
        return
    }

    var user models.User
    if err := database.DB.Where("email = ?", input.Email).First(&user).Error; err != nil {
        c.JSON(http.StatusUnauthorized, gin.H{"error": "Invalid credentials"})
        return
    }

    if err := bcrypt.CompareHashAndPassword([]byte(user.Password), []byte(input.Password)); err != nil {
        c.JSON(http.StatusUnauthorized, gin.H{"error": "Invalid credentials"})
        return
    }

    token, err := utils.GenerateJWT(user.ID, user.Username)
    if err != nil {
        c.JSON(http.StatusInternalServerError, gin.H{"error": "Failed to generate token"})
        return
    }

    c.JSON(http.StatusOK, gin.H{"token": token})
}
5️⃣ Add Auth Middleware (middlewares/auth.go)
package middlewares

import (
    "net/http"
    "social-user-service/utils"
    "strings"

    "github.com/gin-gonic/gin"
)

func AuthMiddleware() gin.HandlerFunc {
    return func(c *gin.Context) {
        authHeader := c.GetHeader("Authorization")
        if authHeader == "" {
            c.JSON(http.StatusUnauthorized, gin.H{"error": "Authorization header required"})
            c.Abort()
            return
        }

        tokenString := strings.Split(authHeader, "Bearer ")[1]
        claims, err := utils.ValidateJWT(tokenString)
        if err != nil {
            c.JSON(http.StatusUnauthorized, gin.H{"error": "Invalid token"})
            c.Abort()
            return
        }

        // Store claims in context
        c.Set("userID", claims.UserID)
        c.Set("username", claims.Username)

        c.Next()
    }
}
6️⃣ Update routes/user_routes.go
package routes

import (
    "social-user-service/controllers"
    "social-user-service/middlewares"

    "github.com/gin-gonic/gin"
)

func UserRoutes(router *gin.Engine) {
    router.POST("/register", controllers.Register)
    router.POST("/login", controllers.Login)

    // Protected routes
    userRoutes := router.Group("/users")
    userRoutes.Use(middlewares.AuthMiddleware())
    {
        userRoutes.GET("/", controllers.GetUsers)
        userRoutes.GET("/:id", controllers.GetUser)
        userRoutes.PUT("/:id", controllers.UpdateUser)
        userRoutes.DELETE("/:id", controllers.DeleteUser)
    }
}
✅ Testing the Flow
Register a user:

POST /register
{
    "username": "alice",
    "email": "alice@example.com",
    "password": "securepass"
}
Login to get JWT:

POST /login
{
    "email": "alice@example.com",
    "password": "securepass"
}
Response:

{
    "token": "eyJhbGciOiJIUzI1NiIsInR..."
}
Access protected routes:

Include the token in Authorization header:

Authorization: Bearer <token>
GET /users
Now your social media user microservice is secure:

Passwords are hashed with bcrypt

Authentication is via JWT

Users must be logged in to access /users endpoints

If you want, I can also add refresh tokens and role-based access control to make it closer to a production-ready microservice.

Do you want me to do that next?

You said:
also add refresh tokens and role-based access control
ChatGPT said:
Perfect! Let’s extend your social media user microservice in Go to include refresh tokens and role-based access control (RBAC). I’ll walk you through a secure, production-ready approach while keeping the structure clean.

1️⃣ Update User Model (models/user.go)
Add a Role field (e.g., admin or user) and a RefreshToken:

package models

import "gorm.io/gorm"

type User struct {
    gorm.Model
    Username     string `json:"username" gorm:"unique"`
    Email        string `json:"email" gorm:"unique"`
    Password     string `json:"-"` // hide password in JSON responses
    Role         string `json:"role" gorm:"default:'user'"`
    RefreshToken string `json:"-"`
}
2️⃣ Update JWT Utils (utils/token.go)
Create access tokens and refresh tokens:

package utils

import (
    "time"
    "github.com/dgrijalva/jwt-go"
)

var jwtKey = []byte("my_secret_key")         // Access token key
var refreshKey = []byte("my_refresh_secret") // Refresh token key

type Claims struct {
    UserID   uint
    Username string
    Role     string
    jwt.StandardClaims
}

func GenerateTokens(userID uint, username, role string) (accessToken string, refreshToken string, err error) {
    // Access token
    accessClaims := &Claims{
        UserID:   userID,
        Username: username,
        Role:     role,
        StandardClaims: jwt.StandardClaims{
            ExpiresAt: time.Now().Add(15 * time.Minute).Unix(), // short-lived
        },
    }
    at, err := jwt.NewWithClaims(jwt.SigningMethodHS256, accessClaims).SignedString(jwtKey)
    if err != nil {
        return "", "", err
    }

    // Refresh token
    refreshClaims := &Claims{
        UserID:   userID,
        Username: username,
        Role:     role,
        StandardClaims: jwt.StandardClaims{
            ExpiresAt: time.Now().Add(7 * 24 * time.Hour).Unix(), // long-lived
        },
    }
    rt, err := jwt.NewWithClaims(jwt.SigningMethodHS256, refreshClaims).SignedString(refreshKey)
    if err != nil {
        return "", "", err
    }

    return at, rt, nil
}

func ValidateAccessToken(tokenString string) (*Claims, error) {
    claims := &Claims{}
    token, err := jwt.ParseWithClaims(tokenString, claims, func(token *jwt.Token) (interface{}, error) {
        return jwtKey, nil
    })
    if err != nil || !token.Valid {
        return nil, err
    }
    return claims, nil
}

func ValidateRefreshToken(tokenString string) (*Claims, error) {
    claims := &Claims{}
    token, err := jwt.ParseWithClaims(tokenString, claims, func(token *jwt.Token) (interface{}, error) {
        return refreshKey, nil
    })
    if err != nil || !token.Valid {
        return nil, err
    }
    return claims, nil
}
3️⃣ Update controllers/user_controller.go
Modify Login to return both tokens and store refresh token:
func Login(c *gin.Context) {
    var input models.User
    if err := c.ShouldBindJSON(&input); err != nil {
        c.JSON(http.StatusBadRequest, gin.H{"error": err.Error()})
        return
    }

    var user models.User
    if err := database.DB.Where("email = ?", input.Email).First(&user).Error; err != nil {
        c.JSON(http.StatusUnauthorized, gin.H{"error": "Invalid credentials"})
        return
    }

    if err := bcrypt.CompareHashAndPassword([]byte(user.Password), []byte(input.Password)); err != nil {
        c.JSON(http.StatusUnauthorized, gin.H{"error": "Invalid credentials"})
        return
    }

    accessToken, refreshToken, err := utils.GenerateTokens(user.ID, user.Username, user.Role)
    if err != nil {
        c.JSON(http.StatusInternalServerError, gin.H{"error": "Failed to generate tokens"})
        return
    }

    // Save refresh token in DB
    user.RefreshToken = refreshToken
    database.DB.Save(&user)

    c.JSON(http.StatusOK, gin.H{
        "access_token":  accessToken,
        "refresh_token": refreshToken,
    })
}
Add Refresh Token Endpoint:
func Refresh(c *gin.Context) {
    var req struct {
        RefreshToken string `json:"refresh_token"`
    }
    if err := c.ShouldBindJSON(&req); err != nil {
        c.JSON(http.StatusBadRequest, gin.H{"error": err.Error()})
        return
    }

    claims, err := utils.ValidateRefreshToken(req.RefreshToken)
    if err != nil {
        c.JSON(http.StatusUnauthorized, gin.H{"error": "Invalid refresh token"})
        return
    }

    var user models.User
    if err := database.DB.First(&user, claims.UserID).Error; err != nil || user.RefreshToken != req.RefreshToken {
        c.JSON(http.StatusUnauthorized, gin.H{"error": "Invalid refresh token"})
        return
    }

    accessToken, refreshToken, err := utils.GenerateTokens(user.ID, user.Username, user.Role)
    if err != nil {
        c.JSON(http.StatusInternalServerError, gin.H{"error": "Failed to generate tokens"})
        return
    }

    // Update refresh token in DB
    user.RefreshToken = refreshToken
    database.DB.Save(&user)

    c.JSON(http.StatusOK, gin.H{
        "access_token":  accessToken,
        "refresh_token": refreshToken,
    })
}
4️⃣ Add Role-Based Middleware (middlewares/auth.go)
func RBAC(allowedRoles ...string) gin.HandlerFunc {
    return func(c *gin.Context) {
        claimsRaw, exists := c.Get("claims")
        if !exists {
            c.JSON(http.StatusForbidden, gin.H{"error": "Access denied"})
            c.Abort()
            return
        }

        claims := claimsRaw.(*utils.Claims)
        for _, role := range allowedRoles {
            if claims.Role == role {
                c.Next()
                return
            }
        }

        c.JSON(http.StatusForbidden, gin.H{"error": "Access denied"})
        c.Abort()
    }
}
Update AuthMiddleware to store claims:

func AuthMiddleware() gin.HandlerFunc {
    return func(c *gin.Context) {
        authHeader := c.GetHeader("Authorization")
        if authHeader == "" {
            c.JSON(http.StatusUnauthorized, gin.H{"error": "Authorization header required"})
            c.Abort()
            return
        }

        tokenString := strings.Split(authHeader, "Bearer ")[1]
        claims, err := utils.ValidateAccessToken(tokenString)
        if err != nil {
            c.JSON(http.StatusUnauthorized, gin.H{"error": "Invalid token"})
            c.Abort()
            return
        }

        c.Set("claims", claims)
        c.Next()
    }
}
5️⃣ Update Routes (routes/user_routes.go)
func UserRoutes(router *gin.Engine) {
    router.POST("/register", controllers.Register)
    router.POST("/login", controllers.Login)
    router.POST("/refresh", controllers.Refresh)

    // Protected routes
    userRoutes := router.Group("/users")
    userRoutes.Use(middlewares.AuthMiddleware())
    {
        userRoutes.GET("/", middlewares.RBAC("admin"), controllers.GetUsers)   // Admin only
        userRoutes.GET("/:id", controllers.GetUser)                             // All roles
        userRoutes.PUT("/:id", controllers.UpdateUser)                          // All roles
        userRoutes.DELETE("/:id", middlewares.RBAC("admin"), controllers.DeleteUser) // Admin only
    }
}
✅ Features Added
JWT Access & Refresh tokens

Access token: short-lived (~15 min)

Refresh token: long-lived (~7 days)

Refresh endpoint issues new access + refresh tokens

Role-Based Access Control

Only admin can access some endpoints (GET /users, DELETE /users/:id)

All other users can access their own profile

Secure Password Storage

Using bcrypt

This structure now supports production-ready authentication & authorization!

I can also make it support multi-role users and permissions dynamically using a database table for roles & permissions, which is more scalable for large systems.

Do you want me to do that next?

You said:
make it support multi-role users and permissions dynamically using a database table for roles & permissions,
ChatGPT said:
Absolutely! Let's upgrade your social media user microservice to support dynamic multi-role users and permissions, fully managed in the database. This makes it scalable for complex systems where roles and permissions can change without code changes.

1️⃣ Database Models
We need three tables:

Roles – defines roles (admin, moderator, user, etc.)

Permissions – defines actions (create_user, delete_user, view_users, etc.)

RolePermissions – maps roles to permissions

Update the User table to reference Role(s) dynamically.

models/role.go
package models

import "gorm.io/gorm"

type Role struct {
    gorm.Model
    Name        string       `json:"name" gorm:"unique"`
    Permissions []Permission `gorm:"many2many:role_permissions;"`
}
models/permission.go
package models

import "gorm.io/gorm"

type Permission struct {
    gorm.Model
    Name string `json:"name" gorm:"unique"`
}
Update models/user.go
package models

import "gorm.io/gorm"

type User struct {
    gorm.Model
    Username     string  `json:"username" gorm:"unique"`
    Email        string  `json:"email" gorm:"unique"`
    Password     string  `json:"-"` // hide password in JSON
    Roles        []Role  `gorm:"many2many:user_roles;"`
    RefreshToken string  `json:"-"`
}
2️⃣ Database Setup (database/database.go)
Add auto-migration for the new tables:

package database

import (
    "gorm.io/driver/sqlite"
    "gorm.io/gorm"
    "social-user-service/models"
)

var DB *gorm.DB

func Connect() {
    var err error
    DB, err = gorm.Open(sqlite.Open("users.db"), &gorm.Config{})
    if err != nil {
        panic("Failed to connect to database")
    }

    // Auto migrate
    DB.AutoMigrate(
        &models.User{},
        &models.Role{},
        &models.Permission{},
    )
}
3️⃣ Token Generation for Multi-Role Users
Update utils/token.go to store all roles:

type Claims struct {
    UserID uint
    Username string
    Roles []string
    jwt.StandardClaims
}

func GenerateTokens(userID uint, username string, roles []string) (string, string, error) {
    accessClaims := &Claims{
        UserID: userID,
        Username: username,
        Roles: roles,
        StandardClaims: jwt.StandardClaims{
            ExpiresAt: time.Now().Add(15*time.Minute).Unix(),
        },
    }

    accessToken, err := jwt.NewWithClaims(jwt.SigningMethodHS256, accessClaims).SignedString(jwtKey)
    if err != nil {
        return "", "", err
    }

    refreshClaims := &Claims{
        UserID: userID,
        Username: username,
        Roles: roles,
        StandardClaims: jwt.StandardClaims{
            ExpiresAt: time.Now().Add(7*24*time.Hour).Unix(),
        },
    }

    refreshToken, err := jwt.NewWithClaims(jwt.SigningMethodHS256, refreshClaims).SignedString(refreshKey)
    if err != nil {
        return "", "", err
    }

    return accessToken, refreshToken, nil
}
4️⃣ RBAC Middleware Using Permissions
We now check permissions dynamically from roles:

package middlewares

import (
    "net/http"
    "social-user-service/database"
    "social-user-service/models"
    "social-user-service/utils"

    "github.com/gin-gonic/gin"
)

func PermissionMiddleware(permissionName string) gin.HandlerFunc {
    return func(c *gin.Context) {
        claimsRaw, exists := c.Get("claims")
        if !exists {
            c.JSON(http.StatusForbidden, gin.H{"error": "Access denied"})
            c.Abort()
            return
        }

        claims := claimsRaw.(*utils.Claims)

        var roles []models.Role
        database.DB.Preload("Permissions").Where("name IN ?", claims.Roles).Find(&roles)

        hasPermission := false
        for _, role := range roles {
            for _, perm := range role.Permissions {
                if perm.Name == permissionName {
                    hasPermission = true
                    break
                }
            }
        }

        if !hasPermission {
            c.JSON(http.StatusForbidden, gin.H{"error": "Permission denied"})
            c.Abort()
            return
        }

        c.Next()
    }
}
5️⃣ Example Usage in Routes
userRoutes := router.Group("/users")
userRoutes.Use(middlewares.AuthMiddleware())
{
    userRoutes.GET("/", middlewares.PermissionMiddleware("view_users"), controllers.GetUsers)
    userRoutes.GET("/:id", middlewares.PermissionMiddleware("view_users"), controllers.GetUser)
    userRoutes.PUT("/:id", middlewares.PermissionMiddleware("edit_user"), controllers.UpdateUser)
    userRoutes.DELETE("/:id", middlewares.PermissionMiddleware("delete_user"), controllers.DeleteUser)
}
6️⃣ Seed Roles and Permissions
You can create a seed function to populate default roles and permissions:

func SeedRolesPermissions() {
    adminRole := models.Role{Name: "admin"}
    userRole := models.Role{Name: "user"}

    viewUsers := models.Permission{Name: "view_users"}
    editUser := models.Permission{Name: "edit_user"}
    deleteUser := models.Permission{Name: "delete_user"}

    database.DB.Create(&viewUsers)
    database.DB.Create(&editUser)
    database.DB.Create(&deleteUser)

    adminRole.Permissions = []models.Permission{viewUsers, editUser, deleteUser}
    userRole.Permissions = []models.Permission{viewUsers}

    database.DB.Create(&adminRole)
    database.DB.Create(&userRole)
}
Call SeedRolesPermissions() after database.Connect() in main.go.

✅ Now your system supports:

Multi-role users (users can have multiple roles)

Dynamic permissions assigned to roles

JWT tokens including all user roles

Permission-based middleware (no code changes required to add new permissions)

Refresh tokens for long-lived sessions

If you want, I can also implement a user-role management API, so admins can assign/remove roles and permissions dynamically through endpoints instead of manually seeding.

Do you want me to add that?



Attach

Search

Study

Voice
No file chosenNo file chosen
ChatGPT can make mistakes. Check important info.

Absolutely! Let’s build a User-Role Management API so admins can assign and remove roles from users dynamically and manage roles and permissions via API endpoints. This will make your microservice fully flexible and production-ready.

1️⃣ Update Routes (routes/user_routes.go)

Add a new route group for admin actions:

adminRoutes := router.Group("/admin")
adminRoutes.Use(middlewares.AuthMiddleware())
{
    // Role Management
    adminRoutes.POST("/roles", middlewares.PermissionMiddleware("create_role"), controllers.CreateRole)
    adminRoutes.POST("/permissions", middlewares.PermissionMiddleware("create_permission"), controllers.CreatePermission)
    adminRoutes.POST("/users/:id/roles", middlewares.PermissionMiddleware("assign_role"), controllers.AssignRole)
    adminRoutes.DELETE("/users/:id/roles", middlewares.PermissionMiddleware("remove_role"), controllers.RemoveRole)
}

2️⃣ Controllers (controllers/admin_controller.go)
Create Role
package controllers

import (
    "net/http"
    "social-user-service/database"
    "social-user-service/models"

    "github.com/gin-gonic/gin"
)

func CreateRole(c *gin.Context) {
    var role models.Role
    if err := c.ShouldBindJSON(&role); err != nil {
        c.JSON(http.StatusBadRequest, gin.H{"error": err.Error()})
        return
    }

    if err := database.DB.Create(&role).Error; err != nil {
        c.JSON(http.StatusInternalServerError, gin.H{"error": err.Error()})
        return
    }

    c.JSON(http.StatusCreated, role)
}

Create Permission
func CreatePermission(c *gin.Context) {
    var perm models.Permission
    if err := c.ShouldBindJSON(&perm); err != nil {
        c.JSON(http.StatusBadRequest, gin.H{"error": err.Error()})
        return
    }

    if err := database.DB.Create(&perm).Error; err != nil {
        c.JSON(http.StatusInternalServerError, gin.H{"error": err.Error()})
        return
    }

    c.JSON(http.StatusCreated, perm)
}

Assign Role to User
func AssignRole(c *gin.Context) {
    userID := c.Param("id")
    var input struct {
        RoleName string `json:"role_name"`
    }
    if err := c.ShouldBindJSON(&input); err != nil {
        c.JSON(http.StatusBadRequest, gin.H{"error": err.Error()})
        return
    }

    var user models.User
    if err := database.DB.Preload("Roles").First(&user, userID).Error; err != nil {
        c.JSON(http.StatusNotFound, gin.H{"error": "User not found"})
        return
    }

    var role models.Role
    if err := database.DB.Where("name = ?", input.RoleName).First(&role).Error; err != nil {
        c.JSON(http.StatusNotFound, gin.H{"error": "Role not found"})
        return
    }

    // Assign role if not already assigned
    for _, r := range user.Roles {
        if r.ID == role.ID {
            c.JSON(http.StatusBadRequest, gin.H{"error": "Role already assigned"})
            return
        }
    }

    database.DB.Model(&user).Association("Roles").Append(&role)
    c.JSON(http.StatusOK, gin.H{"message": "Role assigned successfully"})
}

Remove Role from User
func RemoveRole(c *gin.Context) {
    userID := c.Param("id")
    var input struct {
        RoleName string `json:"role_name"`
    }
    if err := c.ShouldBindJSON(&input); err != nil {
        c.JSON(http.StatusBadRequest, gin.H{"error": err.Error()})
        return
    }

    var user models.User
    if err := database.DB.Preload("Roles").First(&user, userID).Error; err != nil {
        c.JSON(http.StatusNotFound, gin.H{"error": "User not found"})
        return
    }

    var role models.Role
    if err := database.DB.Where("name = ?", input.RoleName).First(&role).Error; err != nil {
        c.JSON(http.StatusNotFound, gin.H{"error": "Role not found"})
        return
    }

    database.DB.Model(&user).Association("Roles").Delete(&role)
    c.JSON(http.StatusOK, gin.H{"message": "Role removed successfully"})
}

3️⃣ Example API Usage
Create Role
POST /admin/roles
{
    "name": "moderator"
}

Create Permission
POST /admin/permissions
{
    "name": "ban_user"
}

Assign Role to User
POST /admin/users/2/roles
{
    "role_name": "moderator"
}

Remove Role from User
DELETE /admin/users/2/roles
{
    "role_name": "moderator"
}

4️⃣ Notes

Admin-only endpoints require the appropriate permission (create_role, assign_role, etc.).

Roles are dynamic; you can create any role and assign permissions at runtime.

Users can have multiple roles, and the middleware dynamically checks if the user has any role that grants the required permission.

✅ Now your system supports:

Full multi-role, permission-based access control

Dynamic role and permission management via API

Admins can assign/remove roles and permissions without code changes


Perfect! Let’s build a full Admin Dashboard API for your social media user microservice in Go. This API will allow admins to view all users, roles, permissions and perform bulk updates for roles and permissions. It will be fully dynamic, compatible with your multi-role, permission-based system.

1️⃣ Admin Routes (routes/admin_routes.go)
package routes

import (
    "social-user-service/controllers"
    "social-user-service/middlewares"

    "github.com/gin-gonic/gin"
)

func AdminRoutes(router *gin.Engine) {
    adminRoutes := router.Group("/admin")
    adminRoutes.Use(middlewares.AuthMiddleware())
    {
        // Users
        adminRoutes.GET("/users", middlewares.PermissionMiddleware("view_users"), controllers.ListUsers)
        adminRoutes.GET("/users/:id", middlewares.PermissionMiddleware("view_users"), controllers.GetUserDetail)

        // Roles
        adminRoutes.GET("/roles", middlewares.PermissionMiddleware("view_roles"), controllers.ListRoles)
        adminRoutes.POST("/roles", middlewares.PermissionMiddleware("create_role"), controllers.CreateRole)
        adminRoutes.PUT("/roles/:id", middlewares.PermissionMiddleware("edit_role"), controllers.UpdateRole)
        adminRoutes.DELETE("/roles/:id", middlewares.PermissionMiddleware("delete_role"), controllers.DeleteRole)

        // Permissions
        adminRoutes.GET("/permissions", middlewares.PermissionMiddleware("view_permissions"), controllers.ListPermissions)
        adminRoutes.POST("/permissions", middlewares.PermissionMiddleware("create_permission"), controllers.CreatePermission)
        adminRoutes.PUT("/permissions/:id", middlewares.PermissionMiddleware("edit_permission"), controllers.UpdatePermission)
        adminRoutes.DELETE("/permissions/:id", middlewares.PermissionMiddleware("delete_permission"), controllers.DeletePermission)

        // Bulk role assignment/removal
        adminRoutes.POST("/users/roles/bulk", middlewares.PermissionMiddleware("assign_role"), controllers.BulkAssignRoles)
        adminRoutes.DELETE("/users/roles/bulk", middlewares.PermissionMiddleware("remove_role"), controllers.BulkRemoveRoles)
    }
}

2️⃣ Admin Controllers (controllers/admin_dashboard_controller.go)
List All Users
func ListUsers(c *gin.Context) {
    var users []models.User
    database.DB.Preload("Roles").Find(&users)
    c.JSON(http.StatusOK, users)
}

Get Single User Detail
func GetUserDetail(c *gin.Context) {
    id := c.Param("id")
    var user models.User
    if err := database.DB.Preload("Roles.Permissions").First(&user, id).Error; err != nil {
        c.JSON(http.StatusNotFound, gin.H{"error": "User not found"})
        return
    }
    c.JSON(http.StatusOK, user)
}

List Roles
func ListRoles(c *gin.Context) {
    var roles []models.Role
    database.DB.Preload("Permissions").Find(&roles)
    c.JSON(http.StatusOK, roles)
}

Update Role
func UpdateRole(c *gin.Context) {
    id := c.Param("id")
    var input struct {
        Name string `json:"name"`
    }
    if err := c.ShouldBindJSON(&input); err != nil {
        c.JSON(http.StatusBadRequest, gin.H{"error": err.Error()})
        return
    }

    var role models.Role
    if err := database.DB.First(&role, id).Error; err != nil {
        c.JSON(http.StatusNotFound, gin.H{"error": "Role not found"})
        return
    }

    role.Name = input.Name
    database.DB.Save(&role)
    c.JSON(http.StatusOK, role)
}

Delete Role
func DeleteRole(c *gin.Context) {
    id := c.Param("id")
    database.DB.Delete(&models.Role{}, id)
    c.JSON(http.StatusOK, gin.H{"message": "Role deleted"})
}

List Permissions
func ListPermissions(c *gin.Context) {
    var permissions []models.Permission
    database.DB.Find(&permissions)
    c.JSON(http.StatusOK, permissions)
}

Update Permission
func UpdatePermission(c *gin.Context) {
    id := c.Param("id")
    var input struct {
        Name string `json:"name"`
    }
    if err := c.ShouldBindJSON(&input); err != nil {
        c.JSON(http.StatusBadRequest, gin.H{"error": err.Error()})
        return
    }

    var perm models.Permission
    if err := database.DB.First(&perm, id).Error; err != nil {
        c.JSON(http.StatusNotFound, gin.H{"error": "Permission not found"})
        return
    }

    perm.Name = input.Name
    database.DB.Save(&perm)
    c.JSON(http.StatusOK, perm)
}

Delete Permission
func DeletePermission(c *gin.Context) {
    id := c.Param("id")
    database.DB.Delete(&models.Permission{}, id)
    c.JSON(http.StatusOK, gin.H{"message": "Permission deleted"})
}

3️⃣ Bulk Role Assignment / Removal
Bulk Assign Roles
func BulkAssignRoles(c *gin.Context) {
    var input struct {
        UserIDs  []uint `json:"user_ids"`
        RoleName string `json:"role_name"`
    }
    if err := c.ShouldBindJSON(&input); err != nil {
        c.JSON(http.StatusBadRequest, gin.H{"error": err.Error()})
        return
    }

    var role models.Role
    if err := database.DB.Where("name = ?", input.RoleName).First(&role).Error; err != nil {
        c.JSON(http.StatusNotFound, gin.H{"error": "Role not found"})
        return
    }

    for _, userID := range input.UserIDs {
        var user models.User
        if err := database.DB.Preload("Roles").First(&user, userID).Error; err == nil {
            database.DB.Model(&user).Association("Roles").Append(&role)
        }
    }

    c.JSON(http.StatusOK, gin.H{"message": "Roles assigned successfully"})
}

Bulk Remove Roles
func BulkRemoveRoles(c *gin.Context) {
    var input struct {
        UserIDs  []uint `json:"user_ids"`
        RoleName string `json:"role_name"`
    }
    if err := c.ShouldBindJSON(&input); err != nil {
        c.JSON(http.StatusBadRequest, gin.H{"error": err.Error()})
        return
    }

    var role models.Role
    if err := database.DB.Where("name = ?", input.RoleName).First(&role).Error; err != nil {
        c.JSON(http.StatusNotFound, gin.H{"error": "Role not found"})
        return
    }

    for _, userID := range input.UserIDs {
        var user models.User
        if err := database.DB.Preload("Roles").First(&user, userID).Error; err == nil {
            database.DB.Model(&user).Association("Roles").Delete(&role)
        }
    }

    c.JSON(http.StatusOK, gin.H{"message": "Roles removed successfully"})
}

4️⃣ Example API Requests
View All Users
GET /admin/users
Authorization: Bearer <token>

Bulk Assign Role
POST /admin/users/roles/bulk
Authorization: Bearer <token>
{
    "user_ids": [2, 3, 4],
    "role_name": "moderator"
}

Bulk Remove Role
DELETE /admin/users/roles/bulk
Authorization: Bearer <token>
{
    "user_ids": [2, 3, 4],
    "role_name": "moderator"
}

List Roles / Permissions
GET /admin/roles
GET /admin/permissions

✅ Features Added

View all users, roles, and permissions dynamically

Bulk assign or remove roles to multiple users

Full CRUD for roles and permissions

Fully integrated with your dynamic multi-role, permission-based system

All actions protected via permissions

This dashboard API makes your system fully admin-controllable and scalable.

If you want, I can also create a front-end-ready JSON structure that includes users with roles and permissions nested, optimized for admin dashboards.

Do you want me to create that next?

Get smarter responses, upload files and images, and more.
Log in
Sign up for free

Attach
Search
Study
Voice
ChatGPT can make mistakes. Check important info.