https://chyp.com/2012/04/10/book-corner-money-real-quick-the-story-of-m-pesa/
https://www.quora.com/What-does-the-M-Pesa-technology-stack-look-like




M-Pesa, a mobile money transfer and payment service launched in Kenya, uses a robust technology stack that enables its wide range of financial services. While specific details about the technology stack may not be publicly disclosed, the following components are generally understood to be part of M-Pesa's architecture:

1. Mobile Platform

    Mobile Application: M-Pesa has a user-friendly mobile application that allows users to send money, pay bills, and access other financial services.
    USSD Technology: For users without smartphones, M-Pesa offers services via Unstructured Supplementary Service Data (USSD), enabling transactions through simple menu-based interactions.

2. Backend Infrastructure

    Core Banking System: M-Pesa operates on a core banking system that manages customer accounts, balances, and transaction processing.
    Database Management: Relational databases (such as Oracle or MySQL) are likely used to store transaction records, user data, and service logs.
    Transaction Processing Engine: A robust engine that handles real-time transaction processing to ensure swift and secure money transfers.

3. APIs and Integration

    RESTful APIs: M-Pesa provides APIs for third-party integration, allowing businesses to connect their services with M-Pesa for payment processing.
    Web Services: SOAP or RESTful web services may be utilized for communication between M-Pesa and external systems.

4. Security Infrastructure

    Encryption: Strong encryption methods are employed to secure transactions and protect user data.
    Authentication: Multi-factor authentication and other security measures ensure that only authorized users can access accounts and perform transactions.

5. Network and Communication

    Telecom Partnerships: M-Pesa operates through partnerships with local telecommunications companies, leveraging their networks for service delivery.
    Cloud Services: Depending on the deployment strategy, cloud infrastructure could be utilized for scalability and reliability.

6. Analytics and Monitoring

    Data Analytics: M-Pesa likely uses analytics tools to monitor transaction patterns, detect fraud, and improve service offerings.
    Monitoring Tools: Systems are in place to monitor the health of the service, ensuring uptime and performance.

7. User Support and Management

    Customer Service Platforms: Tools for managing customer interactions and support requests.
    Feedback Mechanisms: Systems for gathering user feedback to enhance service features and usability.

Conclusion

The M-Pesa technology stack combines mobile technology, a robust backend infrastructure, secure communication protocols, and analytics capabilities to deliver a reliable and widely used mobile money service. Its success has led to the adoption of similar models in various countries, making it a significant case study in mobile financial services.



##


The first generation m-pesa technology stack was implemented using .NET on SQL Server with MSMQ for the messaging layer (holding incoming and outgoing SMSs) and some Java running on the SIM cards. The main constraint in the early days (2005) was man-power, with 5 developers to implement the entire system in a few months, so ease of implementation and using a familiar toolset was key. It was completely unexpected that it would be as successful as it was. This explains the use of MS-DTC, which makes it very simple to rollback a transaction containing both MSMQ and database operations, but which has scalability issues due to long-lived transactions. It also explains why so much of the business logic was in database sprocs - the database developer had more time spare than the backend developer (i.e. me).

From a deployment point of view the system usually consists of a number of in-country local integration servers (LISs) linked to SMSCs (averaging 2.5 in/out SMSs per request and up to 400 requests per second), USSD gateways, Airtime gateways, etc. These forward messages to a remote server. On high performance installations a server cluster handles the MSMQ message queues. A software entity known as the TranProc reads the message queues, decrypts and decodes messages, invokes the database, determines the response messages and sends them to the outgoing queues. Multiple TranProcs can run in parallel.

A number of software features boosted the flexibility/usability of the system such as the unified identity/role model used to represent actors (e.g. registered customers, unregistered customers, agent stores and assistants, field officers, etc.), downloadable menus so different users could use the same SIM app and new features could be rolled out without great disruption, rollback of requests if response messages weren't delivered within a set time of the original request being received so users would experience a consistent service and know if they hadn't received a response in that time then they were safe to try again. Many of the features in the first generation were retained by the original development team when they set up a separate company, now morphed into RedCloud Technologies, to develop a higher performance and more configurable system.

An update to m-pesa, called R9, increased the performance by reducing the use of MS-DTC and pulling business logic out of the database.

I don't know much about the technology stack used in the second generation of m-pesa, developed by Huawei, that has been rolled out recently.


##

Mpesa is actually an STK menu. It is an application embedded into the SIM of the network operators simcard and linked to a server to allow you interact with features based on command initiated by the user. As opposed to many mobile money transfers that are app based, this means that every SIM card released to the market must have an Mpesa menu.

Success of Mpesa, many people believe it is the global first mobile money transfer, no, before it, NTT Docomo had a money transfer in place, in Philippines they had Padala, etc, it is best marketed and this has dwarfed many technologies that may have been seen to be competing.

Again the success of Mpesa can be attributed to its availability. It is more available in every shop that sells anything, if you can spot coca COLA, you will definitely spot an Mpesa service around it, I believe many people have built better solutions but they lack one thing, availability and proper marketing.


##

Bank ATMs are extremely expensive to procure, operate and maintain. So therefore, you just don't find many of them in the developing world. They exist, they just usually aren't conveniently located (or just as likely, are out of cash, or aren't functioning, etc.)

However, about 1,000 ksh (worth about $12) is enough compensation to incent a qualified person in Kenya to spend a day sitting in an inexpensive steel cage serving as an M-PESA agent (like a bank teller). Many agents operate a store or other business and providing M-PESA deposit and withdrawal is an additional task that the owner or cashier on duty provides.

Therefore, the cost of providing this mobile banking teller service in Kenya is low enough that the M-PESA network reports having at least 40,000 locations of them (and more recent estimates are that the actual number of agents is closer to 80,000 now)

So M-PESA has arrived at its level of success today after receiving enormous benefit from "being there first" and from providing a more convenient service than what the competition (banks and money transfer services) offer.

Getting to this point was not instant (M-PESA was launched more than 7 years ago) nor cheap -- Safaricom has invested an incredible amount into building its network of agents, marketing the service, building and operating the technology, and dealing with regulators. If M-PESA weren't a component of Safaricom's service that increased mobile subscriber revenue, then M-PESA might never have been launched. So M-PESA was essentially a service that was subsidized to help build marketshare and revenue for Safaricom's mobile voice and data network.

Bitcoin is much different. Bitcoin is a protocol. There is no "Bitcoin, Inc." type of corporation that pays to market how Bitcoin is used. Additionally, it is relatively young. While exchanges have existed as far back as four years ago, users haven't enjoyed the convenience of being able to walk a few blocks (or kilometers even) to reach an "agent" who can convert Bitcoins to cash or vice-versa.

But that doesn't mean Bitcoin gain traction and become a useful alternative to M-PESA. To get there will require more exchange points. M-PESA agents do receive as commission a share of the revenue that Safaricom receives for M-PESA withdrawals. But that commission is just a fraction of the revenue Safaricom gets. The transaction volume is enough that many agents can earn a competitive wage when providing this service, but Safaricom is definitely gets the better end of the bargain.

With Bitcoin, an exchange agent can be an individual offering to buy and/or sell bitcoins in exchange for cash. With M-PESA, the fees for service are established by Safaricom --- so the agent in some remote village gets the same commission per-transaction that a busy agent in a busy city center would get. The ability for an exchanger to set their own prices when buying and selling means competition will drive better pricing in the busy metro areas and the potential for larger fees will help to ensure that even the rural areas are served. M-PESA has likely maxxed out at 80,000 agents. There are 44 million people in Kenya -- that means there could be several million who provide exchange between Bitcoin and fiat. There's no approval process or fees that must be paid to provide Bitcoin exchange service, so even someone who just wants to do a couple trades a month could be an agent if they so choose.

M-PESA has the benefit of being operated by the mobile provider Safaricom. SMS text messages, a crucial communications channel used by M-PESA, are not secure. But because Safaricom owns the mobile phone network, M-PESA had no problem obtaining the requirements (i.e., certificates/credentials and access) needed to operate the simtoolkit (STK) based service and there is not much of a risk of spoofing of text messages (especially with the Republic of Kenya owning part of the telecom). Bitcoin doesn't have that benefit, and thus needs the power of cryptography on the mobile device to be effective with secure communications. This means smartphones. So Bitcoin can't gain traction quickly until a decent chunk of the population uses smartphones.

There are certain developments that could become catalysts for fast adoption. Perhaps Bitcoin has a role in Kenya when the cashless matatu rules go into effect (scheduled July 2014). Or perhaps hardware wallets make storage and use of Bitcoin easy and cheap enough that more of the population can consider it. A rapidly devaluing Kenyan shilling (KES) might jolt Bitcoin forward, as an alternate store of value.

So while Bitcoin today is essentially non-existant in Kenya today, there are many reasons it could go quickly from zero to full-bore in a short amount of time. But for the next months and possibly a couple years, Bitcoin is no threat to usurp M-PESA as a major money transfer and payments network.

##

