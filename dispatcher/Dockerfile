FROM ubuntu:18.04

RUN apt-get update

RUN apt-get update \
  && apt-get install -y python3-pip python3-dev \
  && cd /usr/local/bin \
  && ln -s /usr/bin/python3 python \
  && pip3 install --upgrade pip \
  && apt-get install unzip

RUN apt-get install -y wget libgomp1

RUN pip3 install flask

EXPOSE 5000

COPY dispatcher /dispatcher

RUN cp /dispatcher/solvers/releases/z3-4.8.5-x64-ubuntu-16.04/bin/z3 /bin/ && \
    cp /dispatcher/solvers/releases/yices-2.6.1/bin/yices-smt2 /bin/ && \
    cp /dispatcher/solvers/releases/cvc4_master /bin/cvc4 && \
    cd /dispatcher && make

WORKDIR /dispatcher