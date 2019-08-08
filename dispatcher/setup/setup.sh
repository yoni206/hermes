sudo usermod -a -G docker $USER
docker -t image .
COPY .. /dispatcher
