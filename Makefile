EXTENSION = query_schema
DATA = sql/query_schema--1.1.sql sql/query_schema--1.0--1.1.sql
MODULE_big = query_schema
OBJS = src/query-schema.o
REGRESS = query-schema
REGRESS_OPTS = --inputdir=test --outputdir=/tmp/query-schema-regress

PG_CONFIG ?= pg_config
PGXS := $(shell $(PG_CONFIG) --pgxs)
include $(PGXS)
