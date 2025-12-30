/**
 * @license
 * @brief This file is part of the Project X software package.
 * @copyright Copyright (c) 2024 Project X Contributors
 */
package post

import (
	"time"
)

// Post represents a blog post with a title, content, author, and timestamp.
type Post struct {
	Title     string
	Content   string
	Author    string
	Timestamp time.Time
}

// NewPost creates a new Post instance.
func NewPost(title, content, author string) *Post {
	return &Post{
		Title:     title,
		Content:   content,
		Author:    author,
		Timestamp: time.Now(),
	}
}

// Summary returns a brief summary of the post content.
func (p *Post) Summary() string {
	if len(p.Content) > 100 {
		return p.Content[:100] + "..."
	}
	return p.Content
}

// UpdateContent updates the content of the post and refreshes the timestamp.
func (p *Post) UpdateContent(newContent string) {
	p.Content = newContent
	p.Timestamp = time.Now()
}

// AuthorInfo returns the author's name.
func (p *Post) AuthorInfo() string {
	return p.Author
}
