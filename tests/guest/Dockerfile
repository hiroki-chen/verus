ARG BASE_IMAGE=ubuntu:24.04
FROM ${BASE_IMAGE}

# ENV DEBIAN_FRONTEND=noninteractive
# ENV TZ=Etc/UTC

RUN apt-get update && apt-get install -y \
    build-essential \
    bison \
    curl \
    gawk \
    gdb \
    golang-go \
    jq \
    libbz2-dev \
    python3-minimal \
    libffi-dev \
    libgdbm-dev \
    liblzma-dev \
    libncursesw5-dev \
    libreadline-dev \
    libsqlite3-dev \
    libssl-dev \
    sqlite3 \
    strace \
    tar \
    tk-dev \
    zlib1g-dev \
    libexpat1-dev \
    uuid-dev \
    && rm -rf /var/lib/apt/lists/*

COPY . /source-files

RUN mkdir -p /guest-tests/bin \
    && for src in /source-files/func/*.c; do \
    out="/guest-tests/bin/$(basename "${src%.c}")"; \
    gcc -O2 -Wall -Wextra -o "${out}" "${src}" -ldl -pthread -lexpat -lz -lm; \
    done \
    && gcc -O2 -Wall -Wextra -no-pie -o /guest-tests/bin/thread_local_smoke_nopie /source-files/func/thread_local_smoke.c -ldl -pthread -lexpat -lz -lm \
    && gcc -O2 -Wall -Wextra -no-pie -o /guest-tests/bin/copy_reloc_smoke_nopie /source-files/func/copy_reloc_smoke.c -ldl -pthread -lexpat -lz -lm \
    && gcc -O2 -Wall -Wextra -no-pie -o /guest-tests/bin/localtime_smoke_nopie /source-files/func/localtime_smoke.c -ldl -pthread -lexpat -lz -lm \
    && gcc -O2 -Wall -Wextra -no-pie -o /guest-tests/bin/read_localtime_file_smoke_nopie /source-files/func/read_localtime_file_smoke.c -ldl -pthread -lexpat -lz -lm \
    && gcc -O2 -Wall -Wextra -no-pie -o /guest-tests/bin/stdio_seek_read_smoke_nopie /source-files/func/stdio_seek_read_smoke.c -ldl -pthread -lexpat -lz -lm \
    && gcc -O2 -Wall -Wextra -no-pie -o /guest-tests/bin/tz_globals_smoke_nopie /source-files/func/tz_globals_smoke.c -ldl -pthread -lexpat -lz -lm \
    && gcc -O2 -Wall -Wextra -no-pie -o /guest-tests/bin/python_init_like_smoke_nopie /source-files/func/python_init_like_smoke.c -ldl -pthread -lexpat -lz -lm \
    && gcc -O2 -Wall -Wextra -no-pie -o /guest-tests/bin/python_runtime_early_smoke_nopie /source-files/func/python_runtime_early_smoke.c -ldl -pthread -lexpat -lz -lm \
    && gcc -O2 -Wall -Wextra -no-pie -o /guest-tests/bin/python_exec_like_smoke_nopie /source-files/func/python_exec_like_smoke.c -ldl -pthread -lexpat -lz -lm \
    && gcc -O2 -Wall -Wextra -no-pie -o /guest-tests/bin/python_reloc_heavy_smoke_nopie /source-files/func/python_reloc_heavy_smoke.c -ldl -pthread -lexpat -lz -lm \
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
