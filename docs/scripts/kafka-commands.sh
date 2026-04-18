# kafka commands

docker run -p 9092:9092 apache/kafka:latest

docker run -d --name kafka -p 9092:9092 apache/kafka:latest

docker exec -it kafka /opt/kafka/bin/kafka-topics.sh  --create --topic quickstart-events --bootstrap-server localhost:9092

docker exec -it kafka /opt/kafka/bin/kafka-console-producer.sh --topic quickstart-events --bootstrap-server localhost:9092

docker exec -it kafka /opt/kafka/bin/kafka-console-consumer.sh --topic quickstart-events --from-beginning --bootstrap-server localhost:9092

docker exec -it kafka /opt/kafka/bin/kafka-topics.sh --list --bootstrap-server localhost:9092

docker logs -f kafka

docker rm -f kafka
