/**
 * @license
 * @brief This file is part of the Project X software package.
 * @copyright Copyright (c) 2024 Project X Contributors
 */
package user

// User represents a user in the system with a username and email.
type User struct {
	Username string
	Email    string
}

// NewUser creates a new User instance.
func NewUser(username, email string) *User {
	return &User{
		Username: username,
		Email:    email,
	}
}

// GetUsername returns the username of the user.
func (u *User) GetUsername() string {
	return u.Username
}

// GetEmail returns the email of the user.
func (u *User) GetEmail() string {
	return u.Email
}

// SetEmail updates the email of the user.
func (u *User) SetEmail(newEmail string) {
	u.Email = newEmail
}
