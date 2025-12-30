Skip to content
You said:
create social media comments microservice in go
ChatGPT said:

To create a simple Social Media Comments Microservice in Go, we will design a RESTful API that allows users to post, get, update, and delete comments on a specific social media post.

For this microservice, we will focus on the following features:

    POST: Add a new comment to a post.

    GET: Retrieve all comments for a specific post.

    PUT: Update an existing comment.

    DELETE: Delete a comment.

Prerequisites

    Go installed on your machine (version 1.18 or later).

    Go modules initialized (go mod init).

    A database (we'll use an in-memory database or a simple map for this example to keep it lightweight).

Let's build this step by step.
Step 1: Project Setup

Create a new folder for your project:

mkdir social-media-comments
cd social-media-comments
go mod init social-media-comments

Step 2: Define the Comment Model

Create a file called models.go to define the data model for a comment:

// models.go

package main

import "time"

// Comment represents a single comment on a social media post
type Comment struct {
	ID        string    `json:"id"`
	PostID    string    `json:"post_id"`
	UserID    string    `json:"user_id"`
	Content   string    `json:"content"`
	CreatedAt time.Time `json:"created_at"`
	UpdatedAt time.Time `json:"updated_at"`
}

Step 3: Implement the Comments Service

Now let's create the comment service. We'll use a simple in-memory store (a map) for storing comments.

Create a file comments_service.go:

// comments_service.go

package main

import (
	"errors"
	"sync"
	"time"
)

// In-memory store for comments
var commentsStore = struct {
	sync.RWMutex
	store map[string]*Comment
}{store: make(map[string]*Comment)}

// CreateComment creates a new comment for a post
func CreateComment(postID, userID, content string) (*Comment, error) {
	// Generate a simple unique ID (in a real app, use UUID or similar)
	commentID := time.Now().Format("20060102150405")

	comment := &Comment{
		ID:        commentID,
		PostID:    postID,
		UserID:    userID,
		Content:   content,
		CreatedAt: time.Now(),
		UpdatedAt: time.Now(),
	}

	// Lock and store the comment
	commentsStore.Lock()
	defer commentsStore.Unlock()
	commentsStore.store[commentID] = comment

	return comment, nil
}

// GetComments returns all comments for a post
func GetComments(postID string) ([]*Comment, error) {
	commentsStore.RLock()
	defer commentsStore.RUnlock()

	var comments []*Comment
	for _, comment := range commentsStore.store {
		if comment.PostID == postID {
			comments = append(comments, comment)
		}
	}

	if len(comments) == 0 {
		return nil, errors.New("no comments found for this post")
	}
	return comments, nil
}

// UpdateComment updates a comment's content
func UpdateComment(commentID, content string) (*Comment, error) {
	commentsStore.Lock()
	defer commentsStore.Unlock()

	comment, exists := commentsStore.store[commentID]
	if !exists {
		return nil, errors.New("comment not found")
	}

	comment.Content = content
	comment.UpdatedAt = time.Now()

	return comment, nil
}

// DeleteComment deletes a comment by its ID
func DeleteComment(commentID string) error {
	commentsStore.Lock()
	defer commentsStore.Unlock()

	_, exists := commentsStore.store[commentID]
	if !exists {
		return errors.New("comment not found")
	}

	delete(commentsStore.store, commentID)
	return nil
}

Step 4: Implement the HTTP Handlers

Now we will implement the HTTP API endpoints for the above operations. Create a file handlers.go:

// handlers.go

package main

import (
	"encoding/json"
	"fmt"
	"net/http"
	"github.com/gorilla/mux"
)

// CreateCommentHandler handles creating a new comment
func CreateCommentHandler(w http.ResponseWriter, r *http.Request) {
	var req struct {
		PostID  string `json:"post_id"`
		UserID  string `json:"user_id"`
		Content string `json:"content"`
	}

	// Decode request body into req struct
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, "Invalid request", http.StatusBadRequest)
		return
	}

	comment, err := CreateComment(req.PostID, req.UserID, req.Content)
	if err != nil {
		http.Error(w, "Error creating comment", http.StatusInternalServerError)
		return
	}

	// Respond with the created comment
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusCreated)
	json.NewEncoder(w).Encode(comment)
}

// GetCommentsHandler handles getting all comments for a post
func GetCommentsHandler(w http.ResponseWriter, r *http.Request) {
	postID := mux.Vars(r)["post_id"]

	comments, err := GetComments(postID)
	if err != nil {
		http.Error(w, "Error fetching comments", http.StatusInternalServerError)
		return
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(comments)
}

// UpdateCommentHandler handles updating a comment
func UpdateCommentHandler(w http.ResponseWriter, r *http.Request) {
	commentID := mux.Vars(r)["comment_id"]

	var req struct {
		Content string `json:"content"`
	}

	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, "Invalid request", http.StatusBadRequest)
		return
	}

	comment, err := UpdateComment(commentID, req.Content)
	if err != nil {
		http.Error(w, "Error updating comment", http.StatusInternalServerError)
		return
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(comment)
}

// DeleteCommentHandler handles deleting a comment
func DeleteCommentHandler(w http.ResponseWriter, r *http.Request) {
	commentID := mux.Vars(r)["comment_id"]

	if err := DeleteComment(commentID); err != nil {
		http.Error(w, "Error deleting comment", http.StatusInternalServerError)
		return
	}

	w.WriteHeader(http.StatusNoContent)
}

Step 5: Set Up the Router and Start the Server

Create a main.go file to set up the router and start the HTTP server:

// main.go

package main

import (
	"fmt"
	"log"
	"net/http"
	"github.com/gorilla/mux"
)

func main() {
	// Create a new router
	r := mux.NewRouter()

	// Define the routes
	r.HandleFunc("/comments", CreateCommentHandler).Methods("POST")
	r.HandleFunc("/posts/{post_id}/comments", GetCommentsHandler).Methods("GET")
	r.HandleFunc("/comments/{comment_id}", UpdateCommentHandler).Methods("PUT")
	r.HandleFunc("/comments/{comment_id}", DeleteCommentHandler).Methods("DELETE")

	// Start the server
	fmt.Println("Starting server on :8080...")
	log.Fatal(http.ListenAndServe(":8080", r))
}

Step 6: Install Dependencies

To handle HTTP requests with a router, we will use the gorilla/mux package. You can install it by running:

go get github.com/gorilla/mux

Step 7: Run the Microservice

Now, you can run the Go microservice:

go run main.go

Your server will start and listen on http://localhost:8080.
Example API Requests

Here are some example requests you can use to test the API.

    Create a Comment (POST /comments):

{
  "post_id": "123",
  "user_id": "456",
  "content": "This is a comment"
}

Get Comments for a Post (GET /posts/{post_id}/comments):

    Example URL: /posts/123/comments

Update a Comment (PUT /comments/{comment_id}):

    {
      "content": "Updated comment content"
    }

    Delete a Comment (DELETE /comments/{comment_id}):

        Example URL: /comments/20230101235959

Conclusion

This is a simple social media comments microservice written in Go. For a production system, you would typically replace the in-memory store with a proper database (e.g., PostgreSQL, MongoDB) and add authentication and authorization mechanisms, rate limiting, etc.

Let me know if you'd like to extend or modify this service in any way!


ChatGPT can make mistakes. Check important info.
