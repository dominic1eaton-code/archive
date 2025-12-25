JWT-Based Authentication
============================================================

JWTs (JSON Web Tokens) allow:

Stateless authentication

Signed tokens (HMAC or RSA)

Expiration and revocation

We’ll use HMAC-SHA256 signing for simplicity.

1.1 Controller Config

/etc/mini-cd/config.json:

{
  "jwt_secret": "super_secret_random_key_please_change",
  "users": [
    { "username": "admin", "password_hash": "sha256:abcd1234...", "role": "admin" },
    { "username": "developer", "password_hash": "sha256:efgh5678...", "role": "developer" }
  ]
}


jwt_secret is used to sign JWT tokens.

Passwords stored as SHA256 (or bcrypt if you extend later).

Role is one of: admin, developer, viewer.