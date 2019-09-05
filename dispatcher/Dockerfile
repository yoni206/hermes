FROM ubuntu:18.04


# Certificate setup
COPY ZscalerRootCertificate-2048-SHA256.crt /usr/local/share/ca-certificates/
RUN apt-get update \
  && apt-get install -y ca-certificates \
  && update-ca-certificates \
  && mkdir ~/.pip \
  && printf "[global]\ncert=/usr/local/share/ca-certificates/ZscalerRootCertificate-2048-SHA256.crt" > ~/.pip/pip.conf

RUN apt-get update \
  && apt-get install -y python3-pip python3-dev \
  && cd /usr/local/bin \
  && ln -s /usr/bin/python3 python \
  && pip3 install --upgrade pip \
  && apt-get install unzip \
  && apt-get install -y wget libgomp1 \
  && pip3 install flask

# Setups for Kind2
RUN cp /dispatcher/solvers/releases/z3-4.8.5-x64-ubuntu-16.04/bin/z3 /bin/ && \
    cp /dispatcher/solvers/releases/yices-2.6.1/bin/yices-smt2 /bin/ && \
    cp /dispatcher/solvers/releases/cvc4_master /bin/cvc4

COPY dispatcher /dispatcher

WORKDIR /dispatcher

EXPOSE 5000

CMD ./run_server.sh

