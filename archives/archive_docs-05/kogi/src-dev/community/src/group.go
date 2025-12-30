/**
 * @license
 * @brief
 * @copyright Copyright (c) 2024 Project X Contributors
 */
package group

import (
	"projectx/user"
)

// Group represents a collection of users.
type Group struct {
	Name  string
	Users []*user.User
}

// NewGroup creates a new Group instance.
func NewGroup(name string) *Group {
	return &Group{
		Name:  name,
		Users: []*user.User{},
	}
}

// AddUser adds a new user to the group.
func (g *Group) AddUser(u *user.User) {
	g.Users = append(g.Users, u)
}

// GetUsers returns all users in the group.
func (g *Group) GetUsers() []*user.User {
	return g.Users
}

// GetName returns the name of the group.
func (g *Group) GetName() string {
	return g.Name
}

// RemoveUser removes a user from the group by username.
func (g *Group) RemoveUser(username string) {
	for i, u := range g.Users {
		if u.GetUsername() == username {
			g.Users = append(g.Users[:i], g.Users[i+1:]...)
			break
		}
	}
}

// ClearGroup removes all users from the group.
func (g *Group) ClearGroup() {
	g.Users = []*user.User{}
}
