\echo Use "CREATE EXTENSION query_schema" to load this file. \quit

CREATE FUNCTION query_schema(query text)
RETURNS text
AS 'MODULE_PATHNAME', 'query_schema'
LANGUAGE C STRICT VOLATILE;

CREATE FUNCTION query_shape(query text)
RETURNS TABLE (path text, pg_type text, nullable boolean, schema text, note text)
AS 'MODULE_PATHNAME', 'query_shape'
LANGUAGE C STRICT VOLATILE;
