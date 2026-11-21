CREATE EXTENSION query_schema;
CREATE TYPE listing_status AS ENUM ('draft', 'active', 'sold');
CREATE TABLE users (id int PRIMARY KEY, email text NOT NULL, bio text, created_at timestamptz NOT NULL);
CREATE TABLE listings (
  id int PRIMARY KEY,
  seller_id int NOT NULL REFERENCES users,
  title text NOT NULL,
  price_kobo bigint NOT NULL,
  status listing_status NOT NULL,
  tags text[] NOT NULL,
  rating numeric,
  sold_at timestamptz,
  published_on date
);
CREATE TABLE photos (id int PRIMARY KEY, listing_id int NOT NULL REFERENCES listings, url text NOT NULL);

SELECT * FROM query_shape($$
  SELECT u.id, u.email, u.bio, l.title, p.url
  FROM users u
  LEFT JOIN listings l ON l.seller_id = u.id
  LEFT JOIN photos p ON p.listing_id = l.id
$$);

SELECT * FROM query_shape($$
  SELECT l.title, u.email FROM listings l RIGHT JOIN users u ON u.id = l.seller_id
$$);

SELECT * FROM query_shape($$
  SELECT u.email, l.title FROM users u LEFT JOIN listings l ON l.seller_id = u.id WHERE l.id IS NOT NULL
$$);

SELECT * FROM query_shape($$
  SELECT u.id, u.email,
    count(l.id) AS listing_count,
    max(l.price_kobo) AS top_price,
    coalesce(json_agg(json_build_object(
      'id', l.id,
      'title', l.title,
      'priceKobo', l.price_kobo,
      'priceKoboText', l.price_kobo::text,
      'status', l.status,
      'tags', l.tags,
      'rating', l.rating,
      'soldAt', l.sold_at,
      'publishedOn', l.published_on,
      'photos', coalesce((SELECT json_agg(json_build_object('url', p.url)) FROM photos p WHERE p.listing_id = l.id), '[]')
    ) ORDER BY l.id) FILTER (WHERE l.id IS NOT NULL), '[]') AS listings
  FROM users u
  LEFT JOIN listings l ON l.seller_id = u.id
  GROUP BY u.id, u.email
$$);

SELECT query_schema($$
  SELECT u.id, u.created_at,
    coalesce(json_agg(json_build_object('title', l.title, 'soldAt', l.sold_at)) FILTER (WHERE l.id IS NOT NULL), '[]') AS listings
  FROM users u LEFT JOIN listings l ON l.seller_id = u.id
  GROUP BY u.id
$$);

SELECT * FROM query_shape($$
  SELECT json_agg(json_build_object('id', l.id)) AS naive FROM users u LEFT JOIN listings l ON l.seller_id = u.id
$$);

SELECT * FROM query_shape($$
  WITH sellers AS (SELECT id, email FROM users)
  SELECT s.id, s.email, (SELECT count(*) FROM listings) AS total, (SELECT title FROM listings LIMIT 1) AS any_title
  FROM sellers s
$$);

SELECT * FROM query_shape($$
  SELECT row_to_json(l) AS listing, to_json(u.created_at) AS created, json_agg(p) AS photos
  FROM listings l JOIN users u ON u.id = l.seller_id LEFT JOIN photos p ON p.listing_id = l.id
  GROUP BY l.id, u.created_at
$$);

SELECT * FROM query_shape($$
  SELECT lower(u.email) AS email, coalesce(u.bio, '') AS bio, u.bio || '!' AS shout, now() AS at,
    CASE WHEN u.bio IS NULL THEN 'none' ELSE 'some' END AS kind, u.created_at::date AS day,
    l.status, l.rating, l.tags, l.published_on
  FROM users u JOIN listings l ON l.seller_id = u.id
  WHERE u.id = $1 AND l.status = $2
$$);

SELECT * FROM query_shape($$
  INSERT INTO users (id, email, created_at) VALUES ($1, $2, now()) RETURNING id, bio, created_at
$$);

SELECT * FROM query_shape($$ SELECT 1; SELECT 2 $$);
SELECT * FROM query_shape($$ VACUUM $$);

SELECT * FROM query_shape($$
  SELECT
    CASE WHEN l.id IS NULL THEN NULL ELSE json_build_object('id', l.id, 'title', l.title, 'soldAt', l.sold_at) END AS listing,
    CASE WHEN l.id IS NOT NULL THEN l.title END AS title_when_present
  FROM users u LEFT JOIN listings l ON l.seller_id = u.id
$$);

CREATE TYPE money_pair AS (amount bigint, label text);
CREATE TABLE ledger (id int PRIMARY KEY, amounts bigint[] NOT NULL, grid int[][], pair money_pair, cash money, doc tsvector);

SELECT query_schema($$
  SELECT u.id, p.listings, c.n, x.one
  FROM users u
  LEFT JOIN LATERAL (SELECT coalesce(json_agg(json_build_object('id', l.id, 'priceKobo', l.price_kobo)), '[]') AS listings FROM listings l WHERE l.seller_id = u.id) p ON true
  LEFT JOIN LATERAL (SELECT count(*) AS n FROM listings l WHERE l.seller_id = u.id) c ON true
  LEFT JOIN LATERAL (SELECT 1 AS one) x ON true
$$);

SELECT * FROM query_shape($$
  SELECT u.id, p.n, t.title
  FROM users u
  LEFT JOIN LATERAL (SELECT count(*) AS n FROM listings l WHERE l.seller_id = u.id) p ON p.n > 0
  LEFT JOIN LATERAL (SELECT title FROM listings l WHERE l.seller_id = u.id LIMIT 1) t ON true
$$);

SELECT * FROM query_shape($$
  SELECT json_build_object('amounts', l.amounts, 'grid', l.grid, 'pair', l.pair, 'count', count(*) OVER ()) AS j FROM ledger l
$$);

SELECT * FROM query_shape($$ SELECT l.amounts, l.grid, l.pair, l.cash, l.doc, (l.id, l.cash) AS r FROM ledger l $$);

SELECT query_schema($$ SELECT l.cash, l.pair FROM ledger l $$);

SELECT * FROM query_shape($$
  SELECT email::text AS v FROM users UNION ALL SELECT bio FROM users
$$);

SELECT * FROM query_shape($$
  SELECT email::text AS v FROM users INTERSECT SELECT bio FROM users
$$);

SELECT * FROM query_shape($$
  SELECT bio IS DISTINCT FROM 'x' AS d, g, n FROM users, generate_series(1, 2) WITH ORDINALITY AS s(g, n)
$$);
