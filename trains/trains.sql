--
-- PostgreSQL database dump
--

SET client_encoding = 'UNICODE';
SET check_function_bodies = false;
SET client_min_messages = warning;

--
-- Name: SCHEMA public; Type: COMMENT; Schema: -; Owner: hcorrada
--

COMMENT ON SCHEMA public IS 'Standard public schema';


SET search_path = public, pg_catalog;

SET default_tablespace = '';

SET default_with_oids = true;

--
-- Name: closed; Type: TABLE; Schema: public; Owner: hcorrada; Tablespace: 
--

CREATE TABLE closed (
    car character varying
);


ALTER TABLE public.closed OWNER TO hcorrada;

--
-- Name: double; Type: TABLE; Schema: public; Owner: hcorrada; Tablespace: 
--

CREATE TABLE "double" (
    car character varying
);


ALTER TABLE public."double" OWNER TO hcorrada;

--
-- Name: eastbound; Type: TABLE; Schema: public; Owner: hcorrada; Tablespace: 
--

CREATE TABLE eastbound (
    train character varying
);


ALTER TABLE public.eastbound OWNER TO hcorrada;

--
-- Name: eastbound_seed; Type: TABLE; Schema: public; Owner: hcorrada; Tablespace: 
--

CREATE TABLE eastbound_seed (
    id bigint,
    var_1 character varying
);


ALTER TABLE public.eastbound_seed OWNER TO hcorrada;

--
-- Name: has_car; Type: TABLE; Schema: public; Owner: hcorrada; Tablespace: 
--

CREATE TABLE has_car (
    train character varying,
    car character varying
);


ALTER TABLE public.has_car OWNER TO hcorrada;

--
-- Name: infront; Type: TABLE; Schema: public; Owner: hcorrada; Tablespace: 
--

CREATE TABLE infront (
    c1 character varying,
    c2 character varying
);


ALTER TABLE public.infront OWNER TO hcorrada;

--
-- Name: jagged; Type: TABLE; Schema: public; Owner: hcorrada; Tablespace: 
--

CREATE TABLE jagged (
    car character varying
);


ALTER TABLE public.jagged OWNER TO hcorrada;

--
-- Name: load; Type: TABLE; Schema: public; Owner: hcorrada; Tablespace: 
--

CREATE TABLE "load" (
    car character varying,
    name character varying,
    count integer
);


ALTER TABLE public."load" OWNER TO hcorrada;

--
-- Name: long; Type: TABLE; Schema: public; Owner: hcorrada; Tablespace: 
--

CREATE TABLE long (
    car character varying
);


ALTER TABLE public.long OWNER TO hcorrada;

--
-- Name: open; Type: TABLE; Schema: public; Owner: hcorrada; Tablespace: 
--

CREATE TABLE open (
    car character varying
);


ALTER TABLE public.open OWNER TO hcorrada;

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

SELECT pg_catalog.setval('seed_table_id', 1, true);


--
-- Name: shape; Type: TABLE; Schema: public; Owner: hcorrada; Tablespace: 
--

CREATE TABLE shape (
    car character varying,
    name character varying
);


ALTER TABLE public.shape OWNER TO hcorrada;

--
-- Name: short; Type: TABLE; Schema: public; Owner: hcorrada; Tablespace: 
--

CREATE TABLE short (
    car character varying
);


ALTER TABLE public.short OWNER TO hcorrada;

--
-- Name: wheels; Type: TABLE; Schema: public; Owner: hcorrada; Tablespace: 
--

CREATE TABLE wheels (
    car character varying,
    count integer
);


ALTER TABLE public.wheels OWNER TO hcorrada;

--
-- Data for Name: closed; Type: TABLE DATA; Schema: public; Owner: hcorrada
--

COPY closed (car) FROM stdin;
car_12
car_23
car_43
car_52
car_53
car_61
car_81
\.


--
-- Data for Name: double; Type: TABLE DATA; Schema: public; Owner: hcorrada
--

COPY "double" (car) FROM stdin;
car_42
car_51
car_71
\.


--
-- Data for Name: eastbound; Type: TABLE DATA; Schema: public; Owner: hcorrada
--

COPY eastbound (train) FROM stdin;
east1
east2
east3
east4
east5
\.


--
-- Data for Name: eastbound_seed; Type: TABLE DATA; Schema: public; Owner: hcorrada
--

COPY eastbound_seed (id, var_1) FROM stdin;
1	east2
\.


--
-- Data for Name: has_car; Type: TABLE DATA; Schema: public; Owner: hcorrada
--

COPY has_car (train, car) FROM stdin;
east1	car_11
east1	car_12
east1	car_13
east1	car_14
east2	car_21
east2	car_22
east2	car_23
east4	car_41
east4	car_42
east4	car_43
east4	car_44
east5	car_51
east5	car_52
east5	car_53
west6	car_61
west6	car_62
west7	car_71
west7	car_72
west7	car_73
west8	car_81
west8	car_82
west10	car_101
west10	car_102
\.


--
-- Data for Name: infront; Type: TABLE DATA; Schema: public; Owner: hcorrada
--

COPY infront (c1, c2) FROM stdin;
east1	car_11
car_11	car_12
car_12	car_13
car_13	car_14
east2	car_21
car_21	car_22
car_22	car_23
east4	car_41
car_41	car_42
car_42	car_43
car_43	car_44
east5	car_51
car_51	car_52
car_52	car_53
west6	car_61
car_61	car_62
west7	car_71
car_71	car_72
car_72	car_73
west8	car_81
car_81	car_82
west10	car_101
car_101	car_102
\.


--
-- Data for Name: jagged; Type: TABLE DATA; Schema: public; Owner: hcorrada
--

COPY jagged (car) FROM stdin;
car_73
\.


--
-- Data for Name: load; Type: TABLE DATA; Schema: public; Owner: hcorrada
--

COPY "load" (car, name, count) FROM stdin;
car_11	rectangle	3
car_12	triangle	1
car_13	hexagon	1
car_14	circle	1
car_21	triangle	1
car_22	rectangle	1
car_23	circle	2
car_41	triangle	1
car_42	triangle	1
car_43	rectangle	1
car_44	rectangle	1
car_51	triangle	1
car_52	rectangle	1
car_53	circle	1
car_61	circle	3
car_62	triangle	1
car_71	circle	1
car_72	triangle	1
car_73	nil	0
car_81	rectangle	1
car_82	circle	1
car_101	rectangle	1
car_102	rectangle	2
\.


--
-- Data for Name: long; Type: TABLE DATA; Schema: public; Owner: hcorrada
--

COPY long (car) FROM stdin;
car_11
car_13
car_52
car_61
car_73
car_81
car_102
\.


--
-- Data for Name: open; Type: TABLE DATA; Schema: public; Owner: hcorrada
--

COPY open (car) FROM stdin;
car_11
car_13
car_14
car_21
car_22
car_41
car_42
car_44
car_51
car_62
car_71
car_72
car_82
car_101
car_102
\.


--
-- Data for Name: shape; Type: TABLE DATA; Schema: public; Owner: hcorrada
--

COPY shape (car, name) FROM stdin;
car_11	rectangle
car_12	rectangle
car_13	rectangle
car_14	rectangle
car_21	u_shaped
car_22	u_shaped
car_23	rectangle
car_41	u_shaped
car_42	rectangle
car_43	elipse
car_44	rectangle
car_51	rectangle
car_52	rectangle
car_53	rectangle
car_61	rectangle
car_62	rectangle
car_71	rectangle
car_72	u_shaped
car_73	rectangle
car_81	rectangle
car_82	u_shaped
car_101	u_shaped
car_102	rectangle
\.


--
-- Data for Name: short; Type: TABLE DATA; Schema: public; Owner: hcorrada
--

COPY short (car) FROM stdin;
car_12
car_14
car_21
car_22
car_23
car_41
car_42
car_43
car_44
car_51
car_53
car_62
car_71
car_72
car_82
car_101
\.


--
-- Data for Name: wheels; Type: TABLE DATA; Schema: public; Owner: hcorrada
--

COPY wheels (car, count) FROM stdin;
car_11	2
car_12	2
car_13	3
car_14	2
car_21	2
car_22	2
car_23	2
car_41	2
car_42	2
car_43	2
car_44	2
car_51	2
car_52	3
car_53	2
car_61	2
car_62	2
car_71	2
car_72	2
car_73	2
car_81	3
car_82	2
car_101	2
car_102	2
\.


--
-- Name: public; Type: ACL; Schema: -; Owner: hcorrada
--

REVOKE ALL ON SCHEMA public FROM PUBLIC;
REVOKE ALL ON SCHEMA public FROM hcorrada;
GRANT ALL ON SCHEMA public TO hcorrada;
GRANT ALL ON SCHEMA public TO PUBLIC;


--
-- PostgreSQL database dump complete
--

