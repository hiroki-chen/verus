FROM ubuntu:24.04

RUN apt-get update && apt-get install -y \
    build-essential \
    && rm -rf /var/lib/apt/lists/*

COPY . /source-files

RUN mkdir -p /guest-tests/bin \
    && for src in /source-files/func/*.c; do \
    out="/guest-tests/bin/$(basename "${src%.c}")"; \
    gcc -O2 -Wall -Wextra -o "${out}" "${src}"; \
    done \
    && chmod +x /source-files/run-test.sh

WORKDIR /guest-tests/bin

ENTRYPOINT ["/source-files/run-test.sh"]
CMD ["passive_migrate"]
