FROM postgres:18.7-alpine AS build
RUN apk add --no-cache build-base
WORKDIR /src/query-schema
COPY Makefile query_schema.control ./
COPY src/ ./src/
COPY sql/ ./sql/
COPY test/ ./test/
RUN make with_llvm=no && make with_llvm=no install

FROM build AS test
RUN mkdir -p /tmp/query-schema-regress && chown -R postgres /src/query-schema /tmp/query-schema-regress
USER postgres
RUN initdb -D /tmp/pgdata >/dev/null \
  && pg_ctl -D /tmp/pgdata -o "-k /tmp -c listen_addresses=''" -w start >/dev/null \
  && (make with_llvm=no installcheck PGHOST=/tmp || (cat /tmp/query-schema-regress/regression.diffs; false)); \
  status=$?; pg_ctl -D /tmp/pgdata -w stop >/dev/null; exit $status

FROM scratch AS package
COPY --from=build /usr/local/lib/postgresql/query_schema.so /usr/local/lib/postgresql/
COPY --from=build /usr/local/share/postgresql/extension/query_schema.control /usr/local/share/postgresql/extension/query_schema--1.0.sql /usr/local/share/postgresql/extension/
