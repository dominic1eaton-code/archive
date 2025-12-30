import java.time.Instant;
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.atomic.AtomicLong;
import java.util.function.Predicate;
import java.util.stream.Collectors;

package com.portal;


/**
 * A simple in-memory social community portal core class.
 * Designed as a starting point for a social network: users, posts, comments, likes, groups, events, notifications.
 *
 * This implementation is thread-friendly but not suitable for production persistence.
 */
public class CommunityPortal {

    private final AtomicLong userIdSeq = new AtomicLong(1);
    private final AtomicLong postIdSeq = new AtomicLong(1);
    private final AtomicLong commentIdSeq = new AtomicLong(1);
    private final AtomicLong groupIdSeq = new AtomicLong(1);
    private final AtomicLong eventIdSeq = new AtomicLong(1);
    private final AtomicLong notifIdSeq = new AtomicLong(1);

    private final Map<Long, User> users = new ConcurrentHashMap<>();
    private final Map<Long, Post> posts = new ConcurrentHashMap<>();
    private final Map<Long, Group> groups = new ConcurrentHashMap<>();
    private final Map<Long, Event> events = new ConcurrentHashMap<>();

    // Public API

    public User registerUser(String displayName, String bio) {
        Objects.requireNonNull(displayName, "displayName");
        long id = userIdSeq.getAndIncrement();
        User u = new User(id, displayName, bio);
        users.put(id, u);
        return u;
    }

    public Post createPost(long authorId, String content) {
        User author = getUserOrThrow(authorId);
        Objects.requireNonNull(content, "content");
        long id = postIdSeq.getAndIncrement();
        Post p = new Post(id, authorId, content, Instant.now());
        posts.put(id, p);
        author.posts.add(id);
        notifyFollowersOfNewPost(author, p);
        return p;
    }

    public Comment commentOnPost(long authorId, long postId, String text) {
        User author = getUserOrThrow(authorId);
        Post post = getPostOrThrow(postId);
        Objects.requireNonNull(text, "text");
        long id = commentIdSeq.getAndIncrement();
        Comment c = new Comment(id, authorId, postId, text, Instant.now());
        post.comments.add(c);
        notifyUser(post.authorId, new Notification(notifIdSeq.getAndIncrement(),
                "New comment", author.displayName + " commented on your post", Instant.now(), postId));
        return c;
    }

    public boolean likePost(long userId, long postId) {
        getUserOrThrow(userId);
        Post post = getPostOrThrow(postId);
        boolean added = post.likes.add(userId);
        if (added) {
            notifyUser(post.authorId, new Notification(notifIdSeq.getAndIncrement(),
                    "New like", "Someone liked your post", Instant.now(), postId));
        }
        return added;
    }

    public boolean follow(long followerId, long targetId) {
        User follower = getUserOrThrow(followerId);
        User target = getUserOrThrow(targetId);
        boolean added = target.followers.add(followerId);
        if (added) {
            follower.following.add(targetId);
            notifyUser(targetId, new Notification(notifIdSeq.getAndIncrement(),
                    "New follower", follower.displayName + " started following you", Instant.now(), null));
        }
        return added;
    }

    public Group createGroup(long creatorId, String name, String description) {
        getUserOrThrow(creatorId);
        Objects.requireNonNull(name, "name");
        long id = groupIdSeq.getAndIncrement();
        Group g = new Group(id, name, description, creatorId, Instant.now());
        g.members.add(creatorId);
        groups.put(id, g);
        return g;
    }

    public boolean joinGroup(long userId, long groupId) {
        getUserOrThrow(userId);
        Group g = getGroupOrThrow(groupId);
        boolean added = g.members.add(userId);
        if (added) {
            notifyUser(g.creatorId, new Notification(notifIdSeq.getAndIncrement(),
                    "Group join", "A user joined your group: " + g.name, Instant.now(), null));
        }
        return added;
    }

    public Event createEvent(long creatorId, Long groupId, String title, String description, Instant time) {
        getUserOrThrow(creatorId);
        if (groupId != null) {
            getGroupOrThrow(groupId);
        }
        Objects.requireNonNull(title, "title");
        long id = eventIdSeq.getAndIncrement();
        Event e = new Event(id, creatorId, groupId, title, description, time);
        events.put(id, e);
        return e;
    }

    public boolean rsvp(long userId, long eventId, RSVPStatus status) {
        getUserOrThrow(userId);
        Event e = getEventOrThrow(eventId);
        e.rsvps.put(userId, status);
        notifyUser(e.creatorId, new Notification(notifIdSeq.getAndIncrement(),
                "Event RSVP", "Someone RSVP'd to your event: " + e.title, Instant.now(), null));
        return true;
    }

    public List<Post> getUserFeed(long userId, int limit) {
        User u = getUserOrThrow(userId);
        Set<Long> sources = new HashSet<>(u.following);
        sources.add(userId); // include own posts
        return posts.values().stream()
                .filter(p -> sources.contains(p.authorId))
                .sorted(Comparator.comparing(Post::getCreatedAt).reversed())
                .limit(Math.max(0, limit))
                .collect(Collectors.toList());
    }

    public List<User> searchUsers(String q, int limit) {
        return search(users.values(), u -> u.displayName.toLowerCase().contains(q.toLowerCase()), limit);
    }

    public List<Post> searchPosts(String q, int limit) {
        return search(posts.values(), p -> p.content.toLowerCase().contains(q.toLowerCase()), limit);
    }

    public List<Group> searchGroups(String q, int limit) {
        return search(groups.values(), g -> g.name.toLowerCase().contains(q.toLowerCase()) ||
                (g.description != null && g.description.toLowerCase().contains(q.toLowerCase())), limit);
    }

    public List<Notification> getNotifications(long userId) {
        return new ArrayList<>(getUserOrThrow(userId).notifications);
    }

    // Internal helpers

    private <T> List<T> search(Collection<T> col, Predicate<T> predicate, int limit) {
        return col.stream().filter(predicate).limit(Math.max(0, limit)).collect(Collectors.toList());
    }

    private void notifyFollowersOfNewPost(User author, Post p) {
        for (Long followerId : author.followers) {
            notifyUser(followerId, new Notification(notifIdSeq.getAndIncrement(),
                    "New post", author.displayName + " posted: " + trim(p.content, 120), Instant.now(), p.id));
        }
    }

    private void notifyUser(long userId, Notification n) {
        User u = users.get(userId);
        if (u != null) {
            u.notifications.add(n);
        }
    }

    private static String trim(String s, int max) {
        if (s == null) return "";
        return s.length() <= max ? s : s.substring(0, max - 3) + "...";
    }

    private User getUserOrThrow(long id) {
        User u = users.get(id);
        if (u == null) throw new NoSuchElementException("User not found: " + id);
        return u;
    }

    private Post getPostOrThrow(long id) {
        Post p = posts.get(id);
        if (p == null) throw new NoSuchElementException("Post not found: " + id);
        return p;
    }

    private Group getGroupOrThrow(long id) {
        Group g = groups.get(id);
        if (g == null) throw new NoSuchElementException("Group not found: " + id);
        return g;
    }

    private Event getEventOrThrow(long id) {
        Event e = events.get(id);
        if (e == null) throw new NoSuchElementException("Event not found: " + id);
        return e;
    }

    // Data classes

    public static class User {
        public final long id;
        public String displayName;
        public String bio;
        public final List<Long> posts = new CopyOnWriteArrayList<>();
        public final Set<Long> followers = Collections.synchronizedSet(new LinkedHashSet<>());
        public final Set<Long> following = Collections.synchronizedSet(new LinkedHashSet<>());
        public final List<Notification> notifications = new CopyOnWriteArrayList<>();

        public User(long id, String displayName, String bio) {
            this.id = id;
            this.displayName = displayName;
            this.bio = bio;
        }

        @Override
        public String toString() {
            return "User{" + "id=" + id + ", displayName='" + displayName + '\'' + '}';
        }
    }

    public static class Post {
        public final long id;
        public final long authorId;
        public final String content;
        private final Instant createdAt;
        public final List<Comment> comments = new CopyOnWriteArrayList<>();
        public final Set<Long> likes = Collections.synchronizedSet(new LinkedHashSet<>());

        public Post(long id, long authorId, String content, Instant createdAt) {
            this.id = id;
            this.authorId = authorId;
            this.content = content;
            this.createdAt = createdAt;
        }

        public Instant getCreatedAt() {
            return createdAt;
        }

        @Override
        public String toString() {
            return "Post{" + "id=" + id + ", authorId=" + authorId + ", content='" + (content.length() > 40 ? content.substring(0, 40) + "..." : content) + '\'' + '}';
        }
    }

    public static class Comment {
        public final long id;
        public final long authorId;
        public final long postId;
        public final String text;
        public final Instant createdAt;

        public Comment(long id, long authorId, long postId, String text, Instant createdAt) {
            this.id = id;
            this.authorId = authorId;
            this.postId = postId;
            this.text = text;
            this.createdAt = createdAt;
        }

        @Override
        public String toString() {
            return "Comment{" + "id=" + id + ", authorId=" + authorId + ", text='" + (text.length() > 40 ? text.substring(0, 40) + "..." : text) + '\'' + '}';
        }
    }

    public static class Group {
        public final long id;
        public final String name;
        public final String description;
        public final long creatorId;
        public final Instant createdAt;
        public final Set<Long> members = Collections.synchronizedSet(new LinkedHashSet<>());

        public Group(long id, String name, String description, long creatorId, Instant createdAt) {
            this.id = id;
            this.name = name;
            this.description = description;
            this.creatorId = creatorId;
            this.createdAt = createdAt;
        }

        @Override
        public String toString() {
            return "Group{" + "id=" + id + ", name='" + name + '\'' + '}';
        }
    }

    public static class Event {
        public final long id;
        public final long creatorId;
        public final Long groupId; // optional
        public final String title;
        public final String description;
        public final Instant time;
        public final Map<Long, RSVPStatus> rsvps = new ConcurrentHashMap<>();

        public Event(long id, long creatorId, Long groupId, String title, String description, Instant time) {
            this.id = id;
            this.creatorId = creatorId;
            this.groupId = groupId;
            this.title = title;
            this.description = description;
            this.time = time;
        }

        @Override
        public String toString() {
            return "Event{" + "id=" + id + ", title='" + title + '\'' + ", time=" + time + '}';
        }
    }

    public enum RSVPStatus {
        YES, NO, MAYBE
    }

    public static class Notification {
        public final long id;
        public final String title;
        public final String message;
        public final Instant createdAt;
        public final Long relatedPostId;

        public Notification(long id, String title, String message, Instant createdAt, Long relatedPostId) {
            this.id = id;
            this.title = title;
            this.message = message;
            this.createdAt = createdAt;
            this.relatedPostId = relatedPostId;
        }

        @Override
        public String toString() {
            return "Notification{" + "id=" + id + ", title='" + title + '\'' + ", message='" + message + '\'' + '}';
        }
    }
}