FROM ubuntu:22.04

RUN apt-get update && apt-get install -y bash \
  libboost-filesystem1.74.0 libc6 libgcc-s1 libgl1 libglu1-mesa \
  libgmp10 libmpfr6 libqt5core5a libqt5gui5 libqt5opengl5 libqt5printsupport5 \
  libqt5widgets5 libstdc++6 sudo gcc

RUN mkdir /installdir
RUN mkdir /workdir
COPY ./fluctuat_1502.0ubuntu1_amd64.deb /installdir/
COPY ./fluctuat-1502.0ubuntu1_install.sh /installdir/

RUN dpkg -i /installdir/fluctuat_1502.0ubuntu1_amd64.deb
RUN bash /installdir/fluctuat-1502.0ubuntu1_install.sh
COPY fluctuat.lic /opt/fluctuat/
ENV FLUCTUATHOME=/opt/fluctuat
ENV PATH="$PATH:/opt/fluctuat/bin"

ENV DISPLAY=host.docker.internal:0

COPY ./benchmarks /workdir/

WORKDIR /workdir

