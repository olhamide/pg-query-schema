# query_schema

A Postgres extension that describes a query's result as an [Effect](https://effect.website) Schema, using the Postgres analyzer. It is meant for local development only.

```sql
CREATE EXTENSION query_schema;

SELECT query_schema($$
  SELECT u.email, l.title
  FROM users u
  LEFT JOIN listings l ON l.seller_id = u.id
$$);
```

```ts
Schema.Struct({
  email: Schema.String,
  title: Schema.NullOr(Schema.String),
})
```

`query_shape(query)` returns the same information as one row per field, with the Postgres type, nullability and notes.

## What it knows

- Nullability from outer joins, `WHERE` and `FILTER` conditions, `CASE` branches, `coalesce`, aggregates, subqueries and CTEs.
- Types by context: top-level values as `@effect/sql-pg` decodes them, values inside `json_build_object` and `json_agg` as Postgres converts them to JSON.
- Enums as `Schema.Literals`, arrays, `row_to_json`, and `RETURNING` clauses.
- Anything it cannot prove non-null is reported as nullable.

## Install

Releases ship prebuilt files for Postgres 18 on Alpine, for amd64 and arm64:

```dockerfile
FROM postgres:18.7-alpine
ARG TARGETARCH
ADD https://github.com/olhamide/pg-query-schema/releases/download/v1.0.0/query_schema-pg18-alpine-${TARGETARCH}.tar.gz /tmp/query_schema.tar.gz
RUN tar -xzf /tmp/query_schema.tar.gz -C / && rm /tmp/query_schema.tar.gz
```

## Develop

```sh
docker build --target test .
```
