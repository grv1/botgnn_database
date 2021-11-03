--
-- PostgreSQL database dump
--

SET client_encoding = 'SQL_ASCII';
SET check_function_bodies = false;
SET client_min_messages = warning;

--
-- Name: SCHEMA public; Type: COMMENT; Schema: -; Owner: postgres
--

COMMENT ON SCHEMA public IS 'Standard public schema';


SET search_path = public, pg_catalog;

SET default_tablespace = '';

SET default_with_oids = true;

--
-- Name: p; Type: TABLE; Schema: public; Owner: hcorrada; Tablespace: 
--

CREATE TABLE p (
    x character(1)
);


ALTER TABLE public.p OWNER TO hcorrada;

--
-- Name: q; Type: TABLE; Schema: public; Owner: hcorrada; Tablespace: 
--

CREATE TABLE q (
    x character(1),
    y character(1)
);


ALTER TABLE public.q OWNER TO hcorrada;

--
-- Name: r1; Type: TABLE; Schema: public; Owner: hcorrada; Tablespace: 
--

CREATE TABLE r1 (
    x character(1)
);


ALTER TABLE public.r1 OWNER TO hcorrada;

--
-- Name: r2; Type: TABLE; Schema: public; Owner: hcorrada; Tablespace: 
--

CREATE TABLE r2 (
    x character(1)
);


ALTER TABLE public.r2 OWNER TO hcorrada;

--
-- Name: r3; Type: TABLE; Schema: public; Owner: hcorrada; Tablespace: 
--

CREATE TABLE r3 (
    x character(1)
);


ALTER TABLE public.r3 OWNER TO hcorrada;

--
-- Name: r4; Type: TABLE; Schema: public; Owner: hcorrada; Tablespace: 
--

CREATE TABLE r4 (
    x character(1)
);


ALTER TABLE public.r4 OWNER TO hcorrada;

--
-- Name: seed_table_id; Type: SEQUENCE; Schema: public; Owner: hcorrada
--

CREATE SEQUENCE seed_table_id
    INCREMENT BY 1
    NO MAXVALUE
    NO MINVALUE
    CACHE 1;


ALTER TABLE public.seed_table_id OWNER TO hcorrada;

--
-- Name: seed_table_id; Type: SEQUENCE SET; Schema: public; Owner: hcorrada
--

SELECT pg_catalog.setval('seed_table_id', 2, true);


--
-- Data for Name: p; Type: TABLE DATA; Schema: public; Owner: hcorrada
--

COPY p (x) FROM stdin;
x
a
\.


--
-- Data for Name: q; Type: TABLE DATA; Schema: public; Owner: hcorrada
--

COPY q (x, y) FROM stdin;
x	y
x	z
a	b
a	c
\.


--
-- Data for Name: r1; Type: TABLE DATA; Schema: public; Owner: hcorrada
--

COPY r1 (x) FROM stdin;
y
b
\.


--
-- Data for Name: r2; Type: TABLE DATA; Schema: public; Owner: hcorrada
--

COPY r2 (x) FROM stdin;
y
c
\.


--
-- Data for Name: r3; Type: TABLE DATA; Schema: public; Owner: hcorrada
--

COPY r3 (x) FROM stdin;
z
\.


--
-- Data for Name: r4; Type: TABLE DATA; Schema: public; Owner: hcorrada
--

COPY r4 (x) FROM stdin;
z
c
\.


--
-- Name: public; Type: ACL; Schema: -; Owner: postgres
--

REVOKE ALL ON SCHEMA public FROM PUBLIC;
REVOKE ALL ON SCHEMA public FROM postgres;
GRANT ALL ON SCHEMA public TO postgres;
GRANT ALL ON SCHEMA public TO PUBLIC;


--
-- PostgreSQL database dump complete
--

