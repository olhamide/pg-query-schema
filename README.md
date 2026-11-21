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

- Nullability from outer joins, `LATERAL` joins, `WHERE` and `FILTER` conditions, `CASE` branches, `coalesce`, aggregates, subqueries, CTEs and `UNION`, `INTERSECT` and `EXCEPT`.
- A `LEFT JOIN LATERAL ... ON true` over a subquery that always returns one row, such as `coalesce(json_agg(...), '[]')` or `count(*)`, is never null.
- Types by context: top-level values as `@effect/sql-pg` decodes them, values inside `json_build_object` and `json_agg` as Postgres converts them to JSON.
- Enums as `Schema.Literals`, arrays (including multidimensional arrays inside JSON), composite types inside JSON, `row_to_json`, and `RETURNING` clauses.
- Anything it cannot prove non-null is reported as nullable.

## Bigints inside JSON

`int8` values inside JSON arrive as JSON numbers, so they decode to a `bigint` through `Schema.Int`. A value beyond 2^53 has already lost precision when the JSON is parsed, so it fails to decode instead of returning a wrong number. Cast it to `::text` to keep the full range; `int8::text` is described as `Schema.BigIntFromString`. The generated schema uses `SchemaGetter`:

```ts
import { Schema, SchemaGetter } from "effect"
```

## Columns @effect/sql-pg cannot decode

`@effect/sql-pg` reads results in the binary format and fails on types it has no codec for, such as `money`, `tsvector`, `point`, ranges, `bit`, composite types, records, multidimensional arrays, arrays of enums and extension types like `vector`. `query_schema` raises a warning for these columns and `query_shape` adds a note. Select them as `::text`, or wrap them in `to_json`.

## Install

Releases ship prebuilt files for Postgres 18 on Alpine, for amd64 and arm64:

```dockerfile
FROM postgres:18.7-alpine
ARG TARGETARCH
ADD https://github.com/olhamide/pg-query-schema/releases/download/v1.1.0/query_schema-pg18-alpine-${TARGETARCH}.tar.gz /tmp/query_schema.tar.gz
RUN tar -xzf /tmp/query_schema.tar.gz -C / && rm /tmp/query_schema.tar.gz
```

## Develop

```sh
docker build --target test .
```
