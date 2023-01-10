FROM ubuntu:jammy

RUN set -xe; \
    export DEBIAN_FRONTEND=noninteractive; \
    apt-get update; \
    apt-get install -y \
      cmake \
      build-essential \
      git \
      clang-tidy \
      clang-format \
      libspdlog-dev \
      liblttng-ust-dev \
      libboost-dev \
      lttng-tools \
      doxygen \
      graphviz \
    ; \
    mkdir /cactus-rt

COPY scripts /cactus-rt/scripts

WORKDIR /cactus-rt

CMD ["/cactus-rt/scripts/run.sh"]
