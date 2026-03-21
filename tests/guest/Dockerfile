FROM ubuntu:24.04

RUN apt-get update && apt-get install -y \
    build-essential \
    golang-go \
    jq \
    python3-minimal \
    sqlite3 \
    tar \
    && rm -rf /var/lib/apt/lists/*

COPY . /source-files

RUN mkdir -p /guest-tests/bin \
    && for src in /source-files/func/*.c; do \
    out="/guest-tests/bin/$(basename "${src%.c}")"; \
    gcc -O2 -Wall -Wextra -o "${out}" "${src}"; \
    done \
    && for src in /source-files/go/*.go; do \
    [ -e "${src}" ] || continue; \
    out="/guest-tests/bin/$(basename "${src%.go}")"; \
    go build -trimpath -ldflags='-s -w' -o "${out}" "${src}"; \
    done \
    && for script in /source-files/scripts/*; do \
    cp "${script}" "/guest-tests/bin/$(basename "${script}")"; \
    done \
    && chmod +x /guest-tests/bin/* \
    && chmod +x /source-files/run-test.sh

WORKDIR /guest-tests/bin

ENTRYPOINT ["/source-files/run-test.sh"]
CMD ["passive_migrate"]
