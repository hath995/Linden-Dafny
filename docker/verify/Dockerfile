# linden-verify: re-verify the whole Linden workspace from source in a clean
# container, with the same toolchain the registry worker uses: stock Dafny 4.11.0
# and the z3 4.12.1 it bundles.
#
#   docker build -t linden-verify docker/verify                       # clones main
#   docker build -t linden-verify --build-arg LINDEN_REF=<sha> docker/verify
#   docker run --rm --memory=48g -v "$PWD/out:/out" linden-verify
#
# To run an unpushed commit, mount a local checkout. The suite clones its
# committed HEAD, so uncommitted files and local caches are left out:
#
#   docker run --rm --memory=48g -v "$PWD:/linden-src:ro" -v "$PWD/out:/out" linden-verify
#
# See README.md in this directory for the knobs and the expected cost.
FROM ubuntu:24.04

# Empty = the latest lem on apt.lemmata.sh.
ARG LEM_VERSION=
ARG DAFNY_VERSION=4.11.0
ARG LINDEN_REPO=https://github.com/hath995/Linden-Dafny.git
ARG LINDEN_REF=main

ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update \
 && apt-get install -y --no-install-recommends ca-certificates curl gpg git \
 && curl -fsSL https://apt.lemmata.sh/lemmata-release.pub \
      | gpg --dearmor -o /usr/share/keyrings/lemmata-archive-keyring.gpg \
 && echo "deb [signed-by=/usr/share/keyrings/lemmata-archive-keyring.gpg] https://apt.lemmata.sh stable main" \
      > /etc/apt/sources.list.d/lemmata.list \
 && apt-get update \
 && apt-get install -y --no-install-recommends "lem${LEM_VERSION:+=$LEM_VERSION}" \
 && rm -rf /var/lib/apt/lists/*

# lem downloads the official self-contained Dafny release, which bundles .NET, z3
# 4.12.1 and the standard libraries. lem checks it against a SHA-256 pinned in the
# lem binary and refuses on a mismatch.
ENV LEMMATA_TOOLCHAINS=/opt/lemmata/toolchains
RUN lem toolchain install "${DAFNY_VERSION}" \
 && chmod -R a+rX /opt/lemmata

# lem prefers $LEM_DAFNY over every other dafny. The shim only caps the z3 worker
# count (DAFNY_MAX_CORES) and otherwise runs the pinned toolchain unchanged.
COPY dafny-capped /usr/local/bin/dafny-capped
COPY run-suite.sh /usr/local/bin/run-suite
RUN chmod 755 /usr/local/bin/dafny-capped /usr/local/bin/run-suite
ENV DAFNY_REAL=/opt/lemmata/toolchains/${DAFNY_VERSION}/dafny/dafny \
    LEM_DAFNY=/usr/local/bin/dafny-capped \
    DAFNY_MAX_CORES=4 \
    LEM_JOBS=1 \
    LEM_BUILD_TIMEOUT=30m
RUN "$DAFNY_REAL" --version && dafny-capped --version

RUN useradd -m -s /bin/bash linden && mkdir -p /out && chown linden /out
USER linden
WORKDIR /home/linden

# The baked source. A /linden-src mount replaces it at run time.
# LINDEN_REPO may also be a local repository mounted into the build with
# `podman build -v <checkout>:/linden-src:ro --build-arg LINDEN_REPO=/linden-src`,
# which is how a commit is baked before it is pushed. Such an image is for local
# testing only: its clone carries every local branch, so never publish it.
# safe.directory lets git read a repo owned by another uid.
RUN git config --global --add safe.directory '*' \
 && git clone --filter=blob:none "${LINDEN_REPO}" Linden-Dafny \
 && git -C Linden-Dafny checkout --detach "${LINDEN_REF}" \
 && git -C Linden-Dafny log -1 --format='baked Linden-Dafny %H (%cd)'

LABEL org.opencontainers.image.title="linden-verify" \
      org.opencontainers.image.description="Re-verifies every Linden package from source with stock Dafny 4.11.0 (z3 4.12.1), then audits for axioms and assumes" \
      org.opencontainers.image.source="https://github.com/hath995/Linden-Dafny" \
      org.opencontainers.image.revision="${LINDEN_REF}"

ENTRYPOINT ["run-suite"]
