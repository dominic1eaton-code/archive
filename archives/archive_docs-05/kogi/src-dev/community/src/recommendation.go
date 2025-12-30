/**
 * @license
 * @brief Recommendation engine
 * @copyright Copyright (c) 2024 Project X Contributors
 */
package recommendation

import (
	"projectx/post"
	"projectx/user"
)

// Recommendation represents a recommended post for a user.
type Recommendation struct {
	Recipient *user.User
	Post      *post.Post
	Score     float64
}

// NewRecommendation creates a new Recommendation instance.
func NewRecommendation(recipient *user.User, post *post.Post, score float64) *Recommendation {
	return &Recommendation{
		Recipient: recipient,
		Post:      post,
		Score:     score,
	}
}

// GetRecipient returns the recipient of the recommendation.
func (r *Recommendation) GetRecipient() *user.User {
	return r.Recipient
}

// GetPost returns the recommended post.
func (r *Recommendation) GetPost() *post.Post {
	return r.Post
}

// GetScore returns the score of the recommendation.
func (r *Recommendation) GetScore() float64 {
	return r.Score
}

// SetScore updates the score of the recommendation.
func (r *Recommendation) SetScore(newScore float64) {
	r.Score = newScore
}

// IsHighScore checks if the recommendation score is above a certain threshold.
func (r *Recommendation) IsHighScore(threshold float64) bool {
	return r.Score >= threshold
}

// UpdatePost updates the recommended post.
func (r *Recommendation) UpdatePost(newPost *post.Post) {
	r.Post = newPost
}

// UpdateRecipient updates the recipient of the recommendation.
func (r *Recommendation) UpdateRecipient(newRecipient *user.User) {
	r.Recipient = newRecipient
}

// ClearRecommendation resets the recommendation details.
func (r *Recommendation) ClearRecommendation() {
	r.Recipient = nil
	r.Post = nil
	r.Score = 0.0
	return &Activity{
		User: u,
		Post: a.Post,
		Type: "muted",
	}
}
