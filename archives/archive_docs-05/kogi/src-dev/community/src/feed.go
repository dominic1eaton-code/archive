/**
 * @license
 * @brief This file is part of the Project X software package.
 * @copyright Copyright (c) 2024 Project X Contributors
 */
package feed

import (
	"projectx/post"
	"projectx/user"
)

// Feed represents a collection of posts for a user.
type Feed struct {
	Owner *user.User
	Posts []*post.Post
}

// NewFeed creates a new Feed instance for a given user.
func NewFeed(owner *user.User) *Feed {
	return &Feed{
		Owner: owner,
		Posts: []*post.Post{},
	}
}

// AddPost adds a new post to the feed.
func (f *Feed) AddPost(p *post.Post) {
	f.Posts = append(f.Posts, p)
}

// GetPosts returns all posts in the feed.
func (f *Feed) GetPosts() []*post.Post {
	return f.Posts
}

// GetOwner returns the owner of the feed.
func (f *Feed) GetOwner() *user.User {
	return f.Owner
}

// ClearFeed removes all posts from the feed.
func (f *Feed) ClearFeed() {
	f.Posts = []*post.Post{}
}
