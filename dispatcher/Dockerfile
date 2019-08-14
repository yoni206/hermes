FROM ubuntu:18.04

RUN apt-get update
RUN apt-get install -y ca-certificates

# Certificate setup
COPY ZscalerRootCertificate-2048-SHA256.crt /usr/local/share/ca-certificates/
RUN update-ca-certificates
RUN mkdir ~/.pip
RUN printf "[global]\ncert=/usr/local/share/ca-certificates/ZscalerRootCertificate-2048-SHA256.crt" > ~/.pip/pip.conf

RUN apt-get update \
  && apt-get install -y python3-pip python3-dev \
  && cd /usr/local/bin \
  && ln -s /usr/bin/python3 python \
  && pip3 install --upgrade pip \
  && apt-get install unzip

RUN pip3 install flask

EXPOSE 5000

COPY dispatcher /dispatcher

WORKDIR /dispatcher

CMD python3 server.py

