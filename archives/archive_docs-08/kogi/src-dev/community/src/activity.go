/**
 * @license
 * @brief This file is part of the Project X software package.
 * @copyright Copyright (c) 2024 Project X Contributors
 */
package activity

import (
	"projectx/post"
	"projectx/user"
	"time"
)

// Activity represents a user activity related to a post.
type Activity struct {
	User      *user.User
	Post      *post.Post
	Action    string
	Timestamp time.Time
}

// NewActivity creates a new Activity instance.
func NewActivity(u *user.User, p *post.Post, action string) *Activity {
	return &Activity{
		User:      u,
		Post:      p,
		Action:    action,
		Timestamp: time.Now(),
	}
}

// GetDetails returns a summary of the activity.
func (a *Activity) GetDetails() string {
	return a.User.GetUsername() + " " + a.Action + " on post titled '" + a.Post.Title + "' at " + a.Timestamp.String()
}

// GetUser returns the user associated with the activity.
func (a *Activity) GetUser() *user.User {
	return a.User
}

// GetPost returns the post associated with the activity.
func (a *Activity) GetPost() *post.Post {
	return a.Post
}

// GetAction returns the action performed in the activity.
func (a *Activity) GetAction() string {
	return a.Action
}

// GetTimestamp returns the timestamp of the activity.
func (a *Activity) GetTimestamp() time.Time {
	return a.Timestamp
}

func (a *Activity) SetAction(newAction string) {
	a.Action = newAction
}

func (a *Activity) SetTimestamp(newTimestamp time.Time) {
	a.Timestamp = newTimestamp
}

func (a *Activity) Follow(u *user.User) *Activity {
	return NewActivity(u, a.Post, "followed")
}

func (a *Activity) Like(u *user.User) *Activity {
	return NewActivity(u, a.Post, "liked")
}

func (a *Activity) Comment(u *user.User) *Activity {
	return NewActivity(u, a.Post, "commented")
}

func (a *Activity) Share(u *user.User) *Activity {
	return NewActivity(u, a.Post, "shared")
}

func (a *Activity) Edit(u *user.User) *Activity {
	return NewActivity(u, a.Post, "edited")
}

func (a *Activity) Delete(u *user.User) *Activity {
	return NewActivity(u, a.Post, "deleted")
}

func (a *Activity) View(u *user.User) *Activity {
	return NewActivity(u, a.Post, "viewed")
}

func (a *Activity) Bookmark(u *user.User) *Activity {
	return NewActivity(u, a.Post, "bookmarked")
}

func (a *Activity) Report(u *user.User) *Activity {
	return NewActivity(u, a.Post, "reported")
}

func (a *Activity) Subscribe(u *user.User) *Activity {
	return NewActivity(u, a.Post, "subscribed")
}

func (a *Activity) Unsubscribe(u *user.User) *Activity {
	return NewActivity(u, a.Post, "unsubscribed")
}

func (a *Activity) Mention(u *user.User) *Activity {
	return NewActivity(u, a.Post, "mentioned")
}

func (a *Activity) Tag(u *user.User) *Activity {
	return NewActivity(u, a.Post, "tagged")
}

func (a *Activity) SharePrivate(u *user.User) *Activity {
	return NewActivity(u, a.Post, "shared privately")
}

func (a *Activity) SharePublic(u *user.User) *Activity {
	return NewActivity(u, a.Post, "shared publicly")
}

func (a *Activity) React(u *user.User, reaction string) *Activity {
	return NewActivity(u, a.Post, "reacted with "+reaction)
}

func (a *Activity) FollowBack(u *user.User) *Activity {
	return NewActivity(u, a.Post, "followed back")
}

func (a *Activity) Unfollow(u *user.User) *Activity {
	return NewActivity(u, a.Post, "unfollowed")
}

func (a *Activity) Pin(u *user.User) *Activity {
	return NewActivity(u, a.Post, "pinned")
}

func (a *Activity) Unpin(u *user.User) *Activity {
	return NewActivity(u, a.Post, "unpinned")
}

func (a *Activity) Save(u *user.User) *Activity {
	return NewActivity(u, a.Post, "saved")
}

func (a *Activity) Unsaved(u *user.User) *Activity {
	return NewActivity(u, a.Post, "unsaved")
}

func (a *Activity) Archive(u *user.User) *Activity {
	return NewActivity(u, a.Post, "archived")
}

func (a *Activity) Unarchive(u *user.User) *Activity {
	return NewActivity(u, a.Post, "unarchived")
}

func (a *Activity) Block(u *user.User) *Activity {
	return NewActivity(u, a.Post, "blocked")
}

func (a *Activity) Unblock(u *user.User) *Activity {
	return NewActivity(u, a.Post, "unblocked")
}

func (a *Activity) FollowUser(u *user.User) *Activity {
	return NewActivity(u, a.Post, "followed user")
}

func (a *Activity) UnfollowUser(u *user.User) *Activity {
	return NewActivity(u, a.Post, "unfollowed user")
}

func (a *Activity) Notify(u *user.User) *Activity {
	return NewActivity(u, a.Post, "notified")
}

func (a *Activity) ShareLink(u *user.User) *Activity {
	return NewActivity(u, a.Post, "shared link")
}

func (a *Activity) Invite(u *user.User) *Activity {
	return NewActivity(u, a.Post, "invited")
}

func (a *Activity) AcceptInvite(u *user.User) *Activity {
	return NewActivity(u, a.Post, "accepted invite")
}

func (a *Activity) DeclineInvite(u *user.User) *Activity {
	return NewActivity(u, a.Post, "declined invite")
}

func (a *Activity) BlockUser(u *user.User) *Activity {
	return NewActivity(u, a.Post, "blocked user")
}

func (a *Activity) UnblockUser(u *user.User) *Activity {
	return NewActivity(u, a.Post, "unblocked user")
}

func (a *Activity) ReportUser(u *user.User) *Activity {
	return NewActivity(u, a.Post, "reported user")
}

func (a *Activity) UnreportUser(u *user.User) *Activity {
	return NewActivity(u, a.Post, "unreported user")
}

func (a *Activity) SubscribeUser(u *user.User) *Activity {
	return NewActivity(u, a.Post, "subscribed to user")
}

func (a *Activity) UnsubscribeUser(u *user.User) *Activity {
	return NewActivity(u, a.Post, "unsubscribed from user")
}

func (a *Activity) MentionUser(u *user.User) *Activity {
	return NewActivity(u, a.Post, "mentioned user")
}

func (a *Activity) TagUser(u *user.User) *Activity {
	return NewActivity(u, a.Post, "tagged user")
}

func (a *Activity) ShareWithFriend(u *user.User, friendName string) *Activity {
	return NewActivity(u, a.Post, "shared with friend "+friendName)
}

func (a *Activity) UnshareWithFriend(u *user.User, friendName string) *Activity {
	return NewActivity(u, a.Post, "unshared with friend "+friendName)
}

func (a *Activity) FollowTopic(u *user.User, topicName string) *Activity {
	return NewActivity(u, a.Post, "followed topic "+topicName)
}

func (a *Activity) UnfollowTopic(u *user.User, topicName string) *Activity {
	return NewActivity(u, a.Post, "unfollowed topic "+topicName)
}

func (a *Activity) SubscribeTopic(u *user.User, topicName string) *Activity {
	return NewActivity(u, a.Post, "subscribed to topic "+topicName)
}

func (a *Activity) UnsubscribeTopic(u *user.User, topicName string) *Activity {
	return NewActivity(u, a.Post, "unsubscribed from topic "+topicName)
}

func (a *Activity) BlockTopic(u *user.User, topicName string) *Activity {
	return NewActivity(u, a.Post, "blocked topic "+topicName)
}

func (a *Activity) UnblockTopic(u *user.User, topicName string) *Activity {
	return NewActivity(u, a.Post, "unblocked topic "+topicName)
}

func (a *Activity) FollowHashtag(u *user.User, hashtag string) *Activity {
	return NewActivity(u, a.Post, "followed hashtag "+hashtag)
}

func (a *Activity) UnfollowHashtag(u *user.User, hashtag string) *Activity {
	return NewActivity(u, a.Post, "unfollowed hashtag "+hashtag)
}

func (a *Activity) SubscribeHashtag(u *user.User, hashtag string) *Activity {
	return NewActivity(u, a.Post, "subscribed to hashtag "+hashtag)
}

func (a *Activity) UnsubscribeHashtag(u *user.User, hashtag string) *Activity {
	return NewActivity(u, a.Post, "unsubscribed from hashtag "+hashtag)
}

func (a *Activity) BlockHashtag(u *user.User, hashtag string) *Activity {
	return NewActivity(u, a.Post, "blocked hashtag "+hashtag)
}

func (a *Activity) UnblockHashtag(u *user.User, hashtag string) *Activity {
	return NewActivity(u, a.Post, "unblocked hashtag "+hashtag)
}

func (a *Activity) NotifyUser(u *user.User, notificationType string) *Activity {
	return NewActivity(u, a.Post, "notified user with "+notificationType)
}

func (a *Activity) UnnotifyUser(u *user.User, notificationType string) *Activity {
	return NewActivity(u, a.Post, "unnotified user with "+notificationType)
}

func (a *Activity) FollowGroup(u *user.User, groupName string) *Activity {
	return NewActivity(u, a.Post, "followed group "+groupName)
}

func (a *Activity) UnfollowGroup(u *user.User, groupName string) *Activity {
	return NewActivity(u, a.Post, "unfollowed group "+groupName)
}

func (a *Activity) InviteToGroup(u *user.User, groupName string) *Activity {
	return NewActivity(u, a.Post, "invited to group "+groupName)
}

func (a *Activity) AcceptGroupInvite(u *user.User, groupName string) *Activity {
	return NewActivity(u, a.Post, "accepted invite to group "+groupName)
}

func (a *Activity) DeclineGroupInvite(u *user.User, groupName string) *Activity {
	return NewActivity(u, a.Post, "declined invite to group "+groupName)
}

func (a *Activity) RemoveFromGroup(u *user.User, groupName string) *Activity {
	return NewActivity(u, a.Post, "removed from group "+groupName)
}

func (a *Activity) AddToGroup(u *user.User, groupName string) *Activity {
	return NewActivity(u, a.Post, "added to group "+groupName)
}

func (a *Activity) PromoteInGroup(u *user.User, groupName string) *Activity {
	return NewActivity(u, a.Post, "promoted in group "+groupName)
}

func (a *Activity) DemoteInGroup(u *user.User, groupName string) *Activity {
	return NewActivity(u, a.Post, "demoted in group "+groupName)
}

func (a *Activity) InviteFriendToGroup(u *user.User, friendName, groupName string) *Activity {
	return NewActivity(u, a.Post, "invited friend "+friendName+" to group "+groupName)
}

func (a *Activity) AcceptFriendGroupInvite(u *user.User, friendName, groupName string) *Activity {
	return NewActivity(u, a.Post, "accepted friend "+friendName+"'s invite to group "+groupName)
}

func (a *Activity) DeclineFriendGroupInvite(u *user.User, friendName, groupName string) *Activity {
	return NewActivity(u, a.Post, "declined friend "+friendName+"'s invite to group "+groupName)
}

func (a *Activity) BanFromGroup(u *user.User, groupName string) *Activity {
	return NewActivity(u, a.Post, "banned from group "+groupName)
}

func (a *Activity) UnbanFromGroup(u *user.User, groupName string) *Activity {
	return NewActivity(u, a.Post, "unbanned from group "+groupName)
}

func (a *Activity) PromoteToAdminInGroup(u *user.User, groupName string) *Activity {
	return NewActivity(u, a.Post, "promoted to admin in group "+groupName)
}

func (a *Activity) DemoteFromAdminInGroup(u *user.User, groupName string) *Activity {
	return NewActivity(u, a.Post, "demoted from admin in group "+groupName)
}

func (a *Activity) InviteUserToGroup(u *user.User, inviteeName, groupName string) *Activity {
	return NewActivity(u, a.Post, "invited user "+inviteeName+" to group "+groupName)
}

func (a *Activity) AcceptUserGroupInvite(u *user.User, inviteeName, groupName string) *Activity {
	return NewActivity(u, a.Post, "accepted user "+inviteeName+"'s invite to group "+groupName)
}

func (a *Activity) DeclineUserGroupInvite(u *user.User, inviteeName, groupName string) *Activity {
	return NewActivity(u, a.Post, "declined user "+inviteeName+"'s invite to group "+groupName)
}

func (a *Activity) AddAdminToGroup(u *user.User, groupName string) *Activity {
	return NewActivity(u, a.Post, "added admin to group "+groupName)
}

func (a *Activity) RemoveAdminFromGroup(u *user.User, groupName string) *Activity {
	return NewActivity(u, a.Post, "removed admin from group "+groupName)
}

func (a *Activity) PromoteToModeratorInGroup(u *user.User, groupName string) *Activity {
	return NewActivity(u, a.Post, "promoted to moderator in group "+groupName)
}

func (a *Activity) DemoteFromModeratorInGroup(u *user.User, groupName string) *Activity {
	return NewActivity(u, a.Post, "demoted from moderator in group "+groupName)
}

func (a *Activity) InviteModeratorToGroup(u *user.User, moderatorName, groupName string) *Activity {
	return NewActivity(u, a.Post, "invited moderator "+moderatorName+" to group "+groupName)
}

func (a *Activity) ArchiveGroup(u *user.User, groupName string) *Activity {
	return NewActivity(u, a.Post, "archived group "+groupName)
}

func (a *Activity) UnarchiveGroup(u *user.User, groupName string) *Activity {
	return NewActivity(u, a.Post, "unarchived group "+groupName)
}

func (a *Activity) CreateGroup(u *user.User, groupName string) *Activity {
	return NewActivity(u, a.Post, "created group "+groupName)
}

func (a *Activity) DeleteGroup(u *user.User, groupName string) *Activity {
	return NewActivity(u, a.Post, "deleted group "+groupName)
}

func (a *Activity) AddModeratorToGroup(u *user.User, moderatorName, groupName string) *Activity {
	return NewActivity(u, a.Post, "added moderator "+moderatorName+" to group "+groupName)
}

func (a *Activity) PromoteModeratorInGroup(u *user.User, moderatorName, groupName string) *Activity {
	return NewActivity(u, a.Post, "promoted moderator "+moderatorName+" in group "+groupName)
}

func (a *Activity) DemoteModeratorInGroup(u *user.User, moderatorName, groupName string) *Activity {
	return NewActivity(u, a.Post, "demoted moderator "+moderatorName+" in group "+groupName)
}

func (a *Activity) BanModeratorFromGroup(u *user.User, moderatorName, groupName string) *Activity {
	return NewActivity(u, a.Post, "banned moderator "+moderatorName+" from group "+groupName)
}

func (a *Activity) UnbanModeratorFromGroup(u *user.User, moderatorName, groupName string) *Activity {
	return NewActivity(u, a.Post, "unbanned moderator "+moderatorName+" from group "+groupName)
}

func (a *Activity) RemoveModeratorFromGroup(u *user.User, moderatorName, groupName string) *Activity {
	return NewActivity(u, a.Post, "removed moderator "+moderatorName+" from group "+groupName)
}

func (a *Activity) AcceptModeratorGroupInvite(u *user.User, moderatorName, groupName string) *Activity {
	return NewActivity(u, a.Post, "accepted moderator "+moderatorName+"'s invite to group "+groupName)
}

func (a *Activity) DeclineModeratorGroupInvite(u *user.User, moderatorName, groupName string) *Activity {
	return NewActivity(u, a.Post, "declined moderator "+moderatorName+"'s invite to group "+groupName)
}

func (a *Activity) ShareWithGroup(u *user.User, groupName string) *Activity {
	return NewActivity(u, a.Post, "shared with group "+groupName)
}

func (a *Activity) LeaveGroup(u *user.User, groupName string) *Activity {
	return NewActivity(u, a.Post, "left group "+groupName)
}

func (a *Activity) JoinGroup(u *user.User, groupName string) *Activity {
	return NewActivity(u, a.Post, "joined group "+groupName)
}

func (a *Activity) UnjoinGroup(u *user.User, groupName string) *Activity {
	return NewActivity(u, a.Post, "unjoined group "+groupName)
}

func (a *Activity) BlockGroup(u *user.User, groupName string) *Activity {
	return NewActivity(u, a.Post, "blocked group "+groupName)
}

func (a *Activity) UnblockGroup(u *user.User, groupName string) *Activity {
	return NewActivity(u, a.Post, "unblocked group "+groupName)
}

func (a *Activity) MuteNotifications(u *user.User) *Activity {
	return NewActivity(u, a.Post, "muted notifications")
}

func (a *Activity) UnmuteNotifications(u *user.User) *Activity {
	return NewActivity(u, a.Post, "unmuted notifications")
}

func (a *Activity) MutePostComments(u *user.User) *Activity {
	return NewActivity(u, a.Post, "muted post comments")
}

func (a *Activity) UnmutePostComments(u *user.User) *Activity {
	return NewActivity(u, a.Post, "unmuted post comments")
}

func (a *Activity) MuteUser(u *user.User) *Activity {
	return NewActivity(u, a.Post, "muted user")
}

func (a *Activity) UnmuteUser(u *user.User) *Activity {
	return NewActivity(u, a.Post, "unmuted user")
}

func (a *Activity) MutePost(u *user.User) *Activity {
	return NewActivity(u, a.Post, "muted post")
}

func (a *Activity) UnmutePost(u *user.User) *Activity {
	return NewActivity(u, a.Post, "unmuted post")
}
