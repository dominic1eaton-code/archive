Skip to content
You said:
create social media feed microservice in go
ChatGPT said:
Absolutely! Let's build a simple social media feed microservice in Go. I’ll walk you through a clean, minimal design including REST APIs, data models, and in-memory storage for simplicity. Later, you can swap in a database like PostgreSQL or MongoDB.

1. Project Structure
social-feed/
├── main.go
├── models/
│   └── post.go
├── handlers/
│   └── post_handler.go
├── storage/
│   └── post_storage.go
└── go.mod
2. Define Models
models/post.go

package models

import "time"

type Post struct {
    ID        int       `json:"id"`
    User      string    `json:"user"`
    Content   string    `json:"content"`
    CreatedAt time.Time `json:"created_at"`
}
3. Create In-Memory Storage
storage/post_storage.go

package storage

import (
    "errors"
    "sync"
    "time"
    "social-feed/models"
)

type PostStorage struct {
    mu    sync.Mutex
    posts []models.Post
    nextID int
}

func NewPostStorage() *PostStorage {
    return &PostStorage{
        posts:  []models.Post{},
        nextID: 1,
    }
}

func (s *PostStorage) AddPost(user, content string) models.Post {
    s.mu.Lock()
    defer s.mu.Unlock()

    post := models.Post{
        ID:        s.nextID,
        User:      user,
        Content:   content,
        CreatedAt: time.Now(),
    }
    s.posts = append([]models.Post{post}, s.posts...) // prepend for feed order
    s.nextID++
    return post
}

func (s *PostStorage) GetPosts(limit int) []models.Post {
    s.mu.Lock()
    defer s.mu.Unlock()

    if limit > len(s.posts) {
        limit = len(s.posts)
    }
    return s.posts[:limit]
}

func (s *PostStorage) GetPostByID(id int) (models.Post, error) {
    s.mu.Lock()
    defer s.mu.Unlock()

    for _, post := range s.posts {
        if post.ID == id {
            return post, nil
        }
    }
    return models.Post{}, errors.New("post not found")
}
4. Create Handlers
handlers/post_handler.go

package handlers

import (
    "encoding/json"
    "net/http"
    "strconv"
    "social-feed/storage"
)

type PostHandler struct {
    Store *storage.PostStorage
}

func NewPostHandler(store *storage.PostStorage) *PostHandler {
    return &PostHandler{Store: store}
}

func (h *PostHandler) CreatePost(w http.ResponseWriter, r *http.Request) {
    var req struct {
        User    string `json:"user"`
        Content string `json:"content"`
    }
    if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
        http.Error(w, err.Error(), http.StatusBadRequest)
        return
    }

    post := h.Store.AddPost(req.User, req.Content)
    w.Header().Set("Content-Type", "application/json")
    w.WriteHeader(http.StatusCreated)
    json.NewEncoder(w).Encode(post)
}

func (h *PostHandler) ListPosts(w http.ResponseWriter, r *http.Request) {
    limit := 10
    if l := r.URL.Query().Get("limit"); l != "" {
        if val, err := strconv.Atoi(l); err == nil {
            limit = val
        }
    }

    posts := h.Store.GetPosts(limit)
    w.Header().Set("Content-Type", "application/json")
    json.NewEncoder(w).Encode(posts)
}
5. Wire Everything in main.go
package main

import (
    "log"
    "net/http"
    "social-feed/handlers"
    "social-feed/storage"

    "github.com/gorilla/mux"
)

func main() {
    store := storage.NewPostStorage()
    handler := handlers.NewPostHandler(store)

    r := mux.NewRouter()
    r.HandleFunc("/posts", handler.CreatePost).Methods("POST")
    r.HandleFunc("/posts", handler.ListPosts).Methods("GET")

    log.Println("Starting server on :8080")
    log.Fatal(http.ListenAndServe(":8080", r))
}
6. Run the Service
go mod init social-feed
go get github.com/gorilla/mux
go run main.go
7. Test the API
Create Post

curl -X POST http://localhost:8080/posts \
-H "Content-Type: application/json" \
-d '{"user":"alice","content":"Hello world!"}'
List Posts

curl http://localhost:8080/posts
✅ This gives you a working microservice with:

REST API for creating and listing posts

In-memory storage (thread-safe)

Easy to extend with DB, authentication, likes, or comments

I can also provide a version with PostgreSQL and JWT auth next if you want a production-ready microservice.

Do you want me to do that?

You said:
provide a version with PostgreSQL and JWT auth
ChatGPT said:
Perfect! Let’s upgrade your social media feed microservice to use PostgreSQL for persistent storage and JWT authentication for secure user actions. I’ll provide a clean, production-oriented setup in Go.

1. Project Structure
social-feed/
├── main.go
├── models/
│   ├── post.go
│   └── user.go
├── handlers/
│   ├── post_handler.go
│   └── auth_handler.go
├── storage/
│   └── db.go
├── middleware/
│   └── auth_middleware.go
└── go.mod
2. Set Up Models
models/user.go

package models

type User struct {
    ID       int    `json:"id"`
    Username string `json:"username"`
    Password string `json:"-"` // hashed
}
models/post.go

package models

import "time"

type Post struct {
    ID        int       `json:"id"`
    UserID    int       `json:"user_id"`
    Content   string    `json:"content"`
    CreatedAt time.Time `json:"created_at"`
}
3. PostgreSQL Storage Layer
storage/db.go

package storage

import (
    "database/sql"
    "log"
    "social-feed/models"
    _ "github.com/lib/pq"
)

type DB struct {
    Conn *sql.DB
}

func NewDB(connStr string) *DB {
    db, err := sql.Open("postgres", connStr)
    if err != nil {
        log.Fatal(err)
    }
    if err := db.Ping(); err != nil {
        log.Fatal(err)
    }
    return &DB{Conn: db}
}

// User methods
func (db *DB) CreateUser(username, hashedPassword string) (models.User, error) {
    var id int
    err := db.Conn.QueryRow("INSERT INTO users (username, password) VALUES ($1, $2) RETURNING id", username, hashedPassword).Scan(&id)
    return models.User{ID: id, Username: username}, err
}

func (db *DB) GetUserByUsername(username string) (models.User, error) {
    var user models.User
    err := db.Conn.QueryRow("SELECT id, username, password FROM users WHERE username=$1", username).Scan(&user.ID, &user.Username, &user.Password)
    return user, err
}

// Post methods
func (db *DB) CreatePost(userID int, content string) (models.Post, error) {
    var id int
    err := db.Conn.QueryRow("INSERT INTO posts (user_id, content) VALUES ($1, $2) RETURNING id", userID, content).Scan(&id)
    return models.Post{ID: id, UserID: userID, Content: content}, err
}

func (db *DB) GetPosts(limit int) ([]models.Post, error) {
    rows, err := db.Conn.Query("SELECT id, user_id, content, created_at FROM posts ORDER BY created_at DESC LIMIT $1", limit)
    if err != nil {
        return nil, err
    }
    defer rows.Close()

    posts := []models.Post{}
    for rows.Next() {
        var post models.Post
        if err := rows.Scan(&post.ID, &post.UserID, &post.Content, &post.CreatedAt); err != nil {
            return nil, err
        }
        posts = append(posts, post)
    }
    return posts, nil
}
4. JWT Authentication Middleware
middleware/auth_middleware.go

package middleware

import (
    "context"
    "net/http"
    "strings"
    "github.com/golang-jwt/jwt/v5"
)

var jwtSecret = []byte("your-secret-key")

type key string

const UserIDKey key = "userID"

func JWTAuth(next http.Handler) http.Handler {
    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        authHeader := r.Header.Get("Authorization")
        if authHeader == "" {
            http.Error(w, "Missing Authorization header", http.StatusUnauthorized)
            return
        }

        tokenString := strings.TrimPrefix(authHeader, "Bearer ")
        token, err := jwt.Parse(tokenString, func(token *jwt.Token) (interface{}, error) {
            return jwtSecret, nil
        })
        if err != nil || !token.Valid {
            http.Error(w, "Invalid token", http.StatusUnauthorized)
            return
        }

        claims, ok := token.Claims.(jwt.MapClaims)
        if !ok {
            http.Error(w, "Invalid token claims", http.StatusUnauthorized)
            return
        }

        userID := int(claims["user_id"].(float64))
        ctx := context.WithValue(r.Context(), UserIDKey, userID)
        next.ServeHTTP(w, r.WithContext(ctx))
    })
}
5. Auth Handlers
handlers/auth_handler.go

package handlers

import (
    "encoding/json"
    "net/http"
    "time"
    "social-feed/storage"
    "golang.org/x/crypto/bcrypt"
    "github.com/golang-jwt/jwt/v5"
)

var jwtSecret = []byte("your-secret-key")

type AuthHandler struct {
    DB *storage.DB
}

func NewAuthHandler(db *storage.DB) *AuthHandler {
    return &AuthHandler{DB: db}
}

func (h *AuthHandler) Register(w http.ResponseWriter, r *http.Request) {
    var req struct {
        Username string `json:"username"`
        Password string `json:"password"`
    }
    json.NewDecoder(r.Body).Decode(&req)

    hashed, _ := bcrypt.GenerateFromPassword([]byte(req.Password), bcrypt.DefaultCost)
    user, err := h.DB.CreateUser(req.Username, string(hashed))
    if err != nil {
        http.Error(w, err.Error(), http.StatusInternalServerError)
        return
    }
    w.WriteHeader(http.StatusCreated)
    json.NewEncoder(w).Encode(user)
}

func (h *AuthHandler) Login(w http.ResponseWriter, r *http.Request) {
    var req struct {
        Username string `json:"username"`
        Password string `json:"password"`
    }
    json.NewDecoder(r.Body).Decode(&req)

    user, err := h.DB.GetUserByUsername(req.Username)
    if err != nil {
        http.Error(w, "Invalid username or password", http.StatusUnauthorized)
        return
    }

    if bcrypt.CompareHashAndPassword([]byte(user.Password), []byte(req.Password)) != nil {
        http.Error(w, "Invalid username or password", http.StatusUnauthorized)
        return
    }

    token := jwt.NewWithClaims(jwt.SigningMethodHS256, jwt.MapClaims{
        "user_id": user.ID,
        "exp":     time.Now().Add(time.Hour * 72).Unix(),
    })
    tokenString, _ := token.SignedString(jwtSecret)

    json.NewEncoder(w).Encode(map[string]string{"token": tokenString})
}
6. Post Handlers (JWT Protected)
handlers/post_handler.go

package handlers

import (
    "encoding/json"
    "net/http"
    "social-feed/storage"
    "social-feed/middleware"
    "strconv"
)

type PostHandler struct {
    DB *storage.DB
}

func NewPostHandler(db *storage.DB) *PostHandler {
    return &PostHandler{DB: db}
}

func (h *PostHandler) CreatePost(w http.ResponseWriter, r *http.Request) {
    userID := r.Context().Value(middleware.UserIDKey).(int)

    var req struct {
        Content string `json:"content"`
    }
    json.NewDecoder(r.Body).Decode(&req)

    post, err := h.DB.CreatePost(userID, req.Content)
    if err != nil {
        http.Error(w, err.Error(), http.StatusInternalServerError)
        return
    }
    w.WriteHeader(http.StatusCreated)
    json.NewEncoder(w).Encode(post)
}

func (h *PostHandler) ListPosts(w http.ResponseWriter, r *http.Request) {
    limit := 10
    if l := r.URL.Query().Get("limit"); l != "" {
        if val, err := strconv.Atoi(l); err == nil {
            limit = val
        }
    }

    posts, err := h.DB.GetPosts(limit)
    if err != nil {
        http.Error(w, err.Error(), http.StatusInternalServerError)
        return
    }
    json.NewEncoder(w).Encode(posts)
}
7. Main File
main.go

package main

import (
    "log"
    "net/http"
    "social-feed/handlers"
    "social-feed/storage"
    "social-feed/middleware"

    "github.com/gorilla/mux"
)

func main() {
    connStr := "host=localhost port=5432 user=postgres password=postgres dbname=socialfeed sslmode=disable"
    db := storage.NewDB(connStr)

    authHandler := handlers.NewAuthHandler(db)
    postHandler := handlers.NewPostHandler(db)

    r := mux.NewRouter()

    // Auth routes
    r.HandleFunc("/register", authHandler.Register).Methods("POST")
    r.HandleFunc("/login", authHandler.Login).Methods("POST")

    // Post routes (JWT protected)
    postRouter := r.PathPrefix("/posts").Subrouter()
    postRouter.Use(middleware.JWTAuth)
    postRouter.HandleFunc("", postHandler.CreatePost).Methods("POST")
    postRouter.HandleFunc("", postHandler.ListPosts).Methods("GET")

    log.Println("Server running on :8080")
    log.Fatal(http.ListenAndServe(":8080", r))
}
8. PostgreSQL Tables
CREATE TABLE users (
    id SERIAL PRIMARY KEY,
    username VARCHAR(50) UNIQUE NOT NULL,
    password VARCHAR(255) NOT NULL
);

CREATE TABLE posts (
    id SERIAL PRIMARY KEY,
    user_id INT REFERENCES users(id),
    content TEXT NOT NULL,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);
✅ This gives you a production-ready microservice:

PostgreSQL for persistence

JWT authentication

Secure password hashing with bcrypt

Protected endpoints for creating posts

Listing posts publicly or protected

If you want, I can also provide a fully dockerized version with Postgres + Go service ready to run in containers. This is perfect for deployment.

Do you want me to do that next?



Attach

Search

Study

Voice
No file chosenNo file chosen
ChatGPT can make mistakes. Check important info.
