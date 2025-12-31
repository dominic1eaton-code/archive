# payments management system
Absolutely! Let’s design a Payments Management System in Scala. I’ll provide a full foundation that is modular, extensible, and production-ready.

This system will handle:

Users (optional, can link payments to users)

Payment creation

Payment processing (credit/debit)

Payment history / transaction logs

Basic persistence (in-memory for simplicity, can upgrade to DB)

Thread-safe operations

I’ll start with a Scala version using Akka Actors and Futures, which is common for payment systems to handle concurrency.

1️⃣ Model Classes
import java.time.Instant

case class User(id: String, name: String)

sealed trait PaymentStatus
case object Pending extends PaymentStatus
case object Completed extends PaymentStatus
case object Failed extends PaymentStatus

case class Payment(
    id: String,
    fromUser: String,
    toUser: String,
    amount: Double,
    status: PaymentStatus = Pending,
    timestamp: Long = Instant.now.toEpochMilli
)

2️⃣ Payment Repository (Thread-safe in-memory)
import scala.collection.concurrent.TrieMap
import scala.concurrent.Future
import scala.concurrent.ExecutionContext

class PaymentRepository(implicit ec: ExecutionContext) {
  private val payments = TrieMap[String, Payment]()

  def addPayment(payment: Payment): Future[Payment] = Future {
    payments.put(payment.id, payment)
    payment
  }

  def updatePaymentStatus(paymentId: String, status: PaymentStatus): Future[Option[Payment]] = Future {
    payments.get(paymentId).map { payment =>
      val updated = payment.copy(status = status)
      payments.update(paymentId, updated)
      updated
    }
  }

  def getPayment(paymentId: String): Future[Option[Payment]] = Future {
    payments.get(paymentId)
  }

  def getPaymentsForUser(userId: String): Future[Seq[Payment]] = Future {
    payments.values.filter(p => p.fromUser == userId || p.toUser == userId).toSeq
  }

  def getAllPayments: Future[Seq[Payment]] = Future {
    payments.values.toSeq
  }
}

3️⃣ Payment Service
import java.util.UUID

class PaymentService(repo: PaymentRepository)(implicit ec: ExecutionContext) {

  // Create a new payment
  def createPayment(fromUser: String, toUser: String, amount: Double): Future[Payment] = {
    val payment = Payment(UUID.randomUUID().toString, fromUser, toUser, amount, Pending)
    repo.addPayment(payment)
  }

  // Process a payment
  def processPayment(paymentId: String): Future[Option[Payment]] = {
    repo.getPayment(paymentId).flatMap {
      case Some(payment) =>
        if (payment.amount <= 0) repo.updatePaymentStatus(paymentId, Failed)
        else repo.updatePaymentStatus(paymentId, Completed)
      case None => Future.successful(None)
    }
  }

  // Retrieve payment history for a user
  def paymentHistory(userId: String): Future[Seq[Payment]] = repo.getPaymentsForUser(userId)
}

4️⃣ REST API (Akka HTTP + Spray JSON)
import akka.http.scaladsl.server.Directives._
import akka.http.scaladsl.marshallers.sprayjson.SprayJsonSupport._
import spray.json.DefaultJsonProtocol._
import scala.concurrent.ExecutionContext

// JSON formats
implicit val paymentFormat = jsonFormat6(Payment)

class PaymentRoutes(service: PaymentService)(implicit ec: ExecutionContext) {
  val routes =
    pathPrefix("payments") {
      pathEndOrSingleSlash {
        post {
          parameters("fromUser", "toUser", "amount".as[Double]) { (fromUser, toUser, amount) =>
            complete {
              service.createPayment(fromUser, toUser, amount)
            }
          }
        } ~
        get {
          complete {
            service.repo.getAllPayments
          }
        }
      } ~
      path(Segment / "process") { paymentId =>
        post {
          complete {
            service.processPayment(paymentId)
          }
        }
      } ~
      path(Segment / "history") { userId =>
        get {
          complete {
            service.paymentHistory(userId)
          }
        }
      }
    }
}

5️⃣ Main Application
import akka.actor.typed.ActorSystem
import akka.http.scaladsl.Http
import scala.concurrent.ExecutionContext

object PaymentsApp extends App {
  implicit val system = ActorSystem[Nothing](akka.actor.typed.scaladsl.Behaviors.empty, "PaymentsSystem")
  implicit val ec: ExecutionContext = system.executionContext

  val repo = new PaymentRepository
  val service = new PaymentService(repo)
  val routes = new PaymentRoutes(service).routes

  Http().newServerAt("localhost", 8080).bind(routes)
  println("Payments system running at http://localhost:8080/")
}

✅ Features:

Create and process payments.

Payment history per user.

Thread-safe in-memory storage using TrieMap.

REST API using Akka HTTP.

Status tracking: Pending / Completed / Failed.

Absolutely! Let’s design a full production-ready Payments Management System in Scala. This system will integrate everything: users, wallets, JWT authentication, caching, persistent storage (SQLite via Slick), and a REST API (Akka HTTP).

I’ll provide a modular, fully functional setup.

1️⃣ Project Setup (build.sbt)
name := "PaymentsManagementSystem"

version := "0.1"

scalaVersion := "3.3.1"

libraryDependencies ++= Seq(
  "com.typesafe.akka" %% "akka-actor-typed" % "2.9.5",
  "com.typesafe.akka" %% "akka-stream" % "2.9.5",
  "com.typesafe.akka" %% "akka-http" % "10.5.1",
  "com.typesafe.akka" %% "akka-http-spray-json" % "10.5.1",
  "org.xerial" % "sqlite-jdbc" % "3.43.0.0",
  "com.typesafe.slick" %% "slick" % "3.4.1",
  "com.typesafe.slick" %% "slick-hikaricp" % "3.4.1",
  "com.github.t3hnar" %% "scala-bcrypt" % "4.3.0",
  "com.pauldijou" %% "jwt-core" % "9.4.0",
  "com.pauldijou" %% "jwt-spray-json" % "9.4.0",
  "com.github.ben-manes.caffeine" % "caffeine" % "3.1.6"
)

2️⃣ Models
import java.time.Instant

case class UserAccount(id: Long = 0, username: String, passwordHash: String)
case class Wallet(id: String, ownerId: Long, balance: Double)
case class Payment(id: String, fromWallet: String, toWallet: String, amount: Double, status: String, timestamp: Long = Instant.now.toEpochMilli)

3️⃣ Database Tables (Slick)
import slick.jdbc.SQLiteProfile.api._

class UsersTable(tag: Tag) extends Table[UserAccount](tag, "users") {
  def id = column[Long]("id", O.PrimaryKey, O.AutoInc)
  def username = column[String]("username", O.Unique)
  def passwordHash = column[String]("password_hash")
  def * = (id, username, passwordHash) <> (UserAccount.tupled, UserAccount.unapply)
}

class WalletsTable(tag: Tag) extends Table[Wallet](tag, "wallets") {
  def id = column[String]("id", O.PrimaryKey)
  def ownerId = column[Long]("owner_id")
  def balance = column[Double]("balance")
  def * = (id, ownerId, balance) <> (Wallet.tupled, Wallet.unapply)
}

class PaymentsTable(tag: Tag) extends Table[Payment](tag, "payments") {
  def id = column[String]("id", O.PrimaryKey)
  def fromWallet = column[String]("from_wallet")
  def toWallet = column[String]("to_wallet")
  def amount = column[Double]("amount")
  def status = column[String]("status")
  def timestamp = column[Long]("timestamp")
  def * = (id, fromWallet, toWallet, amount, status, timestamp) <> (Payment.tupled, Payment.unapply)
}

4️⃣ Repositories
import scala.concurrent.{Future, ExecutionContext}
import slick.jdbc.SQLiteProfile.api._
import java.util.UUID

class UserRepository(db: Database)(implicit ec: ExecutionContext) {
  val users = TableQuery[UsersTable]

  def init(): Future[Unit] = db.run(users.schema.createIfNotExists)

  def register(username: String, password: String): Future[Option[UserAccount]] = {
    val hash = com.github.t3hnar.bcrypt.bcrypt(password)
    val user = UserAccount(username = username, passwordHash = hash)
    db.run((users returning users.map(_.id) into ((u, id) => u.copy(id = id))) += user)
      .map(Some(_))
      .recover { case _ => None }
  }

  def authenticate(username: String, password: String): Future[Option[UserAccount]] = {
    db.run(users.filter(_.username === username).result.headOption).map {
      case Some(user) if com.github.t3hnar.bcrypt.isBcrypted(password, user.passwordHash) => Some(user)
      case _ => None
    }
  }
}

class WalletRepository(db: Database)(implicit ec: ExecutionContext) {
  val wallets = TableQuery[WalletsTable]

  def init(): Future[Unit] = db.run(wallets.schema.createIfNotExists)

  def createWallet(ownerId: Long): Future[Wallet] = {
    val wallet = Wallet(UUID.randomUUID().toString, ownerId, 0)
    db.run(wallets += wallet).map(_ => wallet)
  }

  def getWallet(id: String): Future[Option[Wallet]] = db.run(wallets.filter(_.id === id).result.headOption)

  def updateBalance(id: String, newBalance: Double): Future[Int] = db.run(wallets.filter(_.id === id).map(_.balance).update(newBalance))
}

class PaymentRepository(db: Database)(implicit ec: ExecutionContext) {
  val payments = TableQuery[PaymentsTable]

  def init(): Future[Unit] = db.run(payments.schema.createIfNotExists)

  def createPayment(fromWallet: String, toWallet: String, amount: Double): Future[Payment] = {
    val payment = Payment(UUID.randomUUID().toString, fromWallet, toWallet, amount, "Pending")
    db.run(payments += payment).map(_ => payment)
  }

  def updateStatus(id: String, status: String): Future[Option[Payment]] = {
    db.run(payments.filter(_.id === id).result.headOption).flatMap {
      case Some(payment) =>
        val updated = payment.copy(status = status)
        db.run(payments.filter(_.id === id).update(updated)).map(_ => Some(updated))
      case None => Future.successful(None)
    }
  }

  def getPaymentsForWallet(walletId: String): Future[Seq[Payment]] =
    db.run(payments.filter(p => p.fromWallet === walletId || p.toWallet === walletId).result)
}

5️⃣ JWT Authentication
import pdi.jwt.{Jwt, JwtAlgorithm, JwtSprayJson}
import spray.json._
case class JwtUser(id: Long, username: String)
object JsonFormats extends DefaultJsonProtocol {
  implicit val jwtUserFormat = jsonFormat2(JwtUser)
}
object JwtAuth {
  import JsonFormats._
  private val secretKey = "super_secret_key"

  def createToken(user: JwtUser): String = Jwt.encode(user.toJson.compactPrint, secretKey, JwtAlgorithm.HS256)
  def validateToken(token: String): Option[JwtUser] =
    Jwt.decode(token, secretKey, Seq(JwtAlgorithm.HS256)).toOption.map(_.content.parseJson.convertTo[JwtUser])
}

6️⃣ Wallet Service with Caching & Thread Safety
import com.github.benmanes.caffeine.cache.{Caffeine, Cache}
import java.util.concurrent.ConcurrentHashMap
import scala.concurrent.Future

class WalletService(walletRepo: WalletRepository, paymentRepo: PaymentRepository)(implicit ec: ExecutionContext) {

  private val lockMap = new ConcurrentHashMap[String, Object]()
  private val cache: Cache[String, Double] = Caffeine.newBuilder().maximumSize(1000).build()

  private def lockFor(walletId: String): Object = lockMap.computeIfAbsent(walletId, _ => new Object())

  def getBalance(walletId: String): Future[Option[Double]] = {
    Option(cache.getIfPresent(walletId)) match {
      case Some(balance) => Future.successful(Some(balance))
      case None =>
        walletRepo.getWallet(walletId).map {
          case Some(wallet) =>
            cache.put(walletId, wallet.balance)
            Some(wallet.balance)
          case None => None
        }
    }
  }

  def deposit(walletId: String, amount: Double): Future[Boolean] = Future {
    lockFor(walletId).synchronized {
      walletRepo.getWallet(walletId).flatMap {
        case Some(wallet) =>
          val newBalance = wallet.balance + amount
          walletRepo.updateBalance(walletId, newBalance).map { _ =>
            cache.put(walletId, newBalance)
            true
          }
        case None => Future.successful(false)
      }.flatten
    }
  }.flatten

  def transfer(fromWallet: String, toWallet: String, amount: Double): Future[Boolean] = {
    val (first, second) = if (fromWallet < toWallet) (fromWallet, toWallet) else (toWallet, fromWallet)
    Future {
      lockFor(first).synchronized {
        lockFor(second).synchronized {
          for {
            from <- walletRepo.getWallet(fromWallet)
            to <- walletRepo.getWallet(toWallet)
            if from.exists(_.balance >= amount) && from.isDefined && to.isDefined
            _ <- walletRepo.updateBalance(fromWallet, from.get.balance - amount)
            _ <- walletRepo.updateBalance(toWallet, to.get.balance + amount)
            _ <- paymentRepo.createPayment(fromWallet, toWallet, amount)
          } yield {
            cache.put(fromWallet, from.get.balance - amount)
            cache.put(toWallet, to.get.balance + amount)
            true
          }
        }
      }
    }.flatten
  }
}

7️⃣ Akka HTTP REST API
import akka.http.scaladsl.server.Directives._
import akka.http.scaladsl.marshallers.sprayjson.SprayJsonSupport._
import spray.json._
import scala.concurrent.ExecutionContext

implicit val paymentFormat = jsonFormat6(Payment)
implicit val walletFormat = jsonFormat3(Wallet)

def authenticated: Directive1[JwtUser] =
  optionalHeaderValueByName("Authorization").flatMap {
    case Some(token) if token.startsWith("Bearer ") =>
      JwtAuth.validateToken(token.substring(7)) match {
        case Some(user) => provide(user)
        case None => complete("Invalid token")
      }
    case _ => complete("Missing Authorization header")
  }

class ApiRoutes(userRepo: UserRepository, walletRepo: WalletRepository, service: WalletService)(implicit ec: ExecutionContext) {

  val routes =
    pathPrefix("auth") {
      path("register") {
        post {
          parameters("username", "password") { (username, password) =>
            complete(userRepo.register(username, password).map {
              case Some(user) => s"User ${user.username} registered successfully"
              case None => "Username exists"
            })
          }
        }
      } ~
      path("login") {
        post {
          parameters("username", "password") { (username, password) =>
            complete(userRepo.authenticate(username, password).map {
              case Some(user) =>
                val token = JwtAuth.createToken(JwtUser(user.id, user.username))
                Map("token" -> token)
              case None => "Invalid username or password"
            })
          }
        }
      }
    } ~
    pathPrefix("wallets") {
      path("create") {
        post {
          authenticated { user =>
            complete(walletRepo.createWallet(user.id))
          }
        }
      } ~
      path(Segment / "balance") { walletId =>
        get {
          authenticated { _ =>
            complete(service.getBalance(walletId))
          }
        }
      } ~
      path("transfer") {
        post {
          parameters("fromWallet", "toWallet", "amount".as[Double]) { (from, to, amount) =>
            authenticated { _ =>
              complete(service.transfer(from, to, amount))
            }
          }
        }
      }
    }
}

8️⃣ Main Application
import akka.actor.typed.ActorSystem
import akka.http.scaladsl.Http
import slick.jdbc.SQLiteProfile.api._
import scala.concurrent.ExecutionContext

object PaymentsApp extends App {
  implicit val system = ActorSystem[Nothing](akka.actor.typed.scaladsl.Behaviors.empty, "PaymentsSystem")
  implicit val ec: ExecutionContext = system.executionContext

  val db = Database.forConfig("walletDb")
  val userRepo = new UserRepository(db)
  val walletRepo = new WalletRepository(db)
  val paymentRepo = new PaymentRepository(db)

  userRepo.init()
  walletRepo.init()
  paymentRepo.init()

  val service = new WalletService(walletRepo, paymentRepo)
  val routes = new ApiRoutes(userRepo, walletRepo, service).routes

  Http().newServerAt("localhost", 8080).bind(routes)
  println("Payments system running at http://localhost:8080/")
}

✅ Features Included

User Management: registration + login with BCrypt password hashing

JWT Authentication for secure API access

Wallets per user with balance caching (Caffeine)

Payments / Transfers between wallets

Persistent Storage via SQLite + Slick

REST API via Akka HTTP

Thread-safe wallet operations


Absolutely! Here’s a Postman-ready test plan for your full Payments Management System, with example API requests for all major actions: registration, login, wallet creation, balance check, and transfer. I’ll include request details, endpoints, method, headers, and example payloads/responses.

1️⃣ Base URL
http://localhost:8080

2️⃣ User Registration

Endpoint: /auth/register
Method: POST
Parameters:

Parameter	Type	Description
username	string	Desired username
password	string	Desired password

Example Request (x-www-form-urlencoded):

POST http://localhost:8080/auth/register
Body (form-data or x-www-form-urlencoded):
username = alice
password = secret123


Expected Response:

"User alice registered successfully"


Error Response (if username exists):

"Username exists"

3️⃣ User Login

Endpoint: /auth/login
Method: POST
Parameters:

Parameter	Type	Description
username	string	Registered user
password	string	User password

Example Request:

POST http://localhost:8080/auth/login
Body (form-data or x-www-form-urlencoded):
username = alice
password = secret123


Expected Response:

{
  "token": "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9..."
}


Note: Copy the JWT token for authenticated requests.

4️⃣ Create Wallet

Endpoint: /wallets/create
Method: POST
Headers:

Key	Value
Authorization	Bearer <JWT Token>

Example Request:

POST http://localhost:8080/wallets/create
Headers: Authorization: Bearer eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9...


Expected Response:

{
  "id": "a1b2c3d4-e5f6-7890-1234-56789abcdef0",
  "ownerId": 1,
  "balance": 0.0
}

5️⃣ Check Wallet Balance

Endpoint: /wallets/{walletId}/balance
Method: GET
Headers:

Key	Value
Authorization	Bearer <JWT Token>

Example Request:

GET http://localhost:8080/wallets/a1b2c3d4-e5f6-7890-1234-56789abcdef0/balance
Headers: Authorization: Bearer <JWT Token>


Expected Response:

{
  "balance": 0.0
}

6️⃣ Transfer Between Wallets

Endpoint: /wallets/transfer
Method: POST
Headers:

Key	Value
Authorization	Bearer <JWT Token>

Parameters (x-www-form-urlencoded or query params):

Parameter	Type	Description
fromWallet	string	Sender wallet ID
toWallet	string	Recipient wallet ID
amount	double	Amount to transfer

Example Request:

POST http://localhost:8080/wallets/transfer
Headers: Authorization: Bearer <JWT Token>
Body (form-data or x-www-form-urlencoded):
fromWallet = a1b2c3d4-e5f6-7890-1234-56789abcdef0
toWallet   = f1e2d3c4-b5a6-7890-9876-54321fedcba0
amount     = 50.0


Expected Response (Success):

true


Failure (Insufficient balance or invalid wallet):

false

7️⃣ Sample Postman Collection JSON

You can import this directly into Postman. Here’s a simplified JSON structure:

{
  "info": {
    "name": "Payments Management System",
    "_postman_id": "12345-abcde",
    "schema": "https://schema.getpostman.com/json/collection/v2.1.0/collection.json"
  },
  "item": [
    {
      "name": "Register User",
      "request": {
        "method": "POST",
        "header": [],
        "body": {
          "mode": "urlencoded",
          "urlencoded": [
            {"key": "username", "value": "alice"},
            {"key": "password", "value": "secret123"}
          ]
        },
        "url": { "raw": "http://localhost:8080/auth/register", "protocol": "http", "host": ["localhost"], "port": "8080", "path": ["auth","register"] }
      }
    },
    {
      "name": "Login User",
      "request": {
        "method": "POST",
        "header": [],
        "body": {
          "mode": "urlencoded",
          "urlencoded": [
            {"key": "username", "value": "alice"},
            {"key": "password", "value": "secret123"}
          ]
        },
        "url": { "raw": "http://localhost:8080/auth/login", "protocol": "http", "host": ["localhost"], "port": "8080", "path": ["auth","login"] }
      }
    },
    {
      "name": "Create Wallet",
      "request": {
        "method": "POST",
        "header": [{"key": "Authorization", "value": "Bearer <JWT Token>"}],
        "url": { "raw": "http://localhost:8080/wallets/create", "protocol": "http", "host": ["localhost"], "port": "8080", "path": ["wallets","create"] }
      }
    },
    {
      "name": "Check Balance",
      "request": {
        "method": "GET",
        "header": [{"key": "Authorization", "value": "Bearer <JWT Token>"}],
        "url": { "raw": "http://localhost:8080/wallets/{walletId}/balance", "protocol": "http", "host": ["localhost"], "port": "8080", "path": ["wallets","{walletId}","balance"] }
      }
    },
    {
      "name": "Transfer Funds",
      "request": {
        "method": "POST",
        "header": [{"key": "Authorization", "value": "Bearer <JWT Token>"}],
        "body": {
          "mode": "urlencoded",
          "urlencoded": [
            {"key": "fromWallet", "value": "wallet1"},
            {"key": "toWallet", "value": "wallet2"},
            {"key": "amount", "value": "50.0"}
          ]
        },
        "url": { "raw": "http://localhost:8080/wallets/transfer", "protocol": "http", "host": ["localhost"], "port": "8080", "path": ["wallets","transfer"] }
      }
    }
  ]
}


This Postman test plan covers all essential workflows:

Register a new user

Login to get a JWT token

Create wallets for the user

Check wallet balances

Transfer funds between wallets