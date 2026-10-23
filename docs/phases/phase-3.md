# Phase 3: Networking, detailed plan

**Goal:** the kernel fetches documents from the network. Every byte that
arrives from a server is parsed by proven code: HTTP/1.1 (RFC 9110 and
RFC 9112), DNS messages (RFC 1035), and TLS as decided in 3.0. Every parser
and every decision (what request to send, which cookies to attach, whether
to follow a redirect) is a pure function or a pure state machine proven in
Verus; the sockets, timers and threads around them are a short Tier 0
shell whose line count the README reports, as for the Phase 2 host shell.

*Exit:* a verified `curl` clone: `cargo run -p clazel -- fetch URL` resolves
the host, connects, speaks TLS, sends the request, and prints the status
line, the fields and the body, with every parser on that path at tier 2.

Nothing in this phase renders anything. The body is bytes; HTML is Phase 4.

## Exit criteria

Phase 3 is done when all of these hold on macOS arm64 and Linux x86-64:

1. `clazel-http`, `clazel-dns` and `clazel-fetch` are at **tier 2**,
   accepted by `cargo xtask check` (every mutation a certified `killed`,
   conformance tests, an independent transcription each), and the TLS
   crate is at the tier 3.0 decides.
2. `cargo run -p clazel -- fetch https://example.com/` prints the response
   of a real server, through the proven DNS, TLS, HTTP and client code and
   the network shell only. `fetch` follows redirects and stores and sends
   cookies through the Phase 2 jar: the `http-state` parser corpus (222
   rows) passes over a real socket against an in-process server (3.8), and
   the WPT `cookies/` tests that needed a server in Phase 2 run the same way.
3. `clazel-fetch` proves `theorem_wire_cookies` (3.6): the only bytes derived
   from the cookie jar that reach the wire for a request to host *h* are the
   cookie string RFC 6265bis §5.8 retrieves for that request; and
   `clazel-kernel`'s Phase 2 theorems still hold with network events (3.7).
4. `scripts/verify.sh` exits 0, with the README table showing the new rows
   and the network shell's line count.
5. CLAUDE.md, VERIFICATION.md, DEPENDENCIES.md and the checker match the
   TLS decision recorded in 3.0.

## What is proven, and what is assumed

1. **Proven (Verus):** response parsing and request serialization
   (`clazel-http`), chunked decoding, DNS message encoding and decoding,
   the client state machine from a URL to the request bytes and from the
   response bytes to a result (`clazel-fetch`), including redirects and the
   cookie steps; and, per 3.0, the TLS record and handshake parsers.
2. **Small and unproven (Tier 0, listed in the TCB):** the network shell:
   UDP to the resolver, TCP, the TLS I/O loop, timeouts. Its one security
   duty is to carry bytes between the right socket and the right state
   machine, and never to look inside them. It never touches the cookie jar:
   the `Cookie` header arrives in the request bytes the proven code built.
3. **Assumed (TCB):** the OS, the cryptography library, and whatever 3.0
   adds (a TLS library, or nothing).

Not covered by any theorem, and said so: timing, resource exhaustion, and
everything outside the phase: HTTP/2 and HTTP/3, caching (RFC 9111),
proxies, HSTS, authentication, compression (the client sends no
`Accept-Encoding`, so a conforming server sends identity), `Upgrade`,
EDNS(0), DNSSEC, DNS over TLS or HTTPS, and IPv6 happy eyeballs (the shell
tries addresses in order).

## Crates

| Crate | Tier (target) | Standard | Contents |
|-------|---------------|----------|----------|
| `clazel-http` | 2 | RFC 9110 §5, §8.6, §10.2.2; RFC 9112 §2 to §7 | field syntax, message framing, chunked coding, request serialization |
| `clazel-dns` | 2 | RFC 1035 §2.3, §3, §4; RFC 1034 §3.6.2; RFC 3596 | message format, name compression, query building, answer extraction |
| `clazel-tls` | per 3.0 | RFC 8446 | TLS 1.3 client, or the glue around a library (3.0) |
| `clazel-fetch` | 2 | (ours); Fetch §4.4 to §4.6 in part; RFC 6265bis §5.2, §5.3, §5.7, §5.8 HTTP parts; RFC 9110 §15.4 | the client state machine: URL to request, response to result, redirects, cookies |
| `clazel-net` | 0 | — | the network shell: resolver, TCP, TLS I/O; counted like the host shell |

Section numbers are from the documents at the time of writing; each spec
header pins the exact RFC or commit it transcribes.

Each Tier 2 crate starts as `tier = 0, target-tier = 2`. `clazel-net` is
Tier 0 because it does I/O; the plan keeps every decision out of it.

## Dependencies on Phase 2

Phase 2 is merged; its remaining open point (2.16 on Linux and CI) does not
block anything here. Used: `clazel-url` (the request target, `Host`, and
resolving `Location`), `clazel-cookie` (storage and retrieval with the
HTTP request contexts Phase 2 left abstract: the table in phase-2.md item
2.9 lists which parts of RFC 6265bis are this phase's), `clazel-origin`
(same-site for redirect chains), `clazel-psl` (through `clazel-cookie`),
`clazel-kernel` (3.7 adds network events to the step function) and the host
shell `clazel` (3.8 adds the network thread).

As in Phase 2, each crate is written against abstract records first and
joined to the real functions last: `clazel-fetch` takes the HTTP parser and
the URL functions as parameters, exactly as the kernel took `UrlFns`, so its
proofs do not wait for 3.2 and its theorem is stated once.

## Work items

Ordered by dependency. Size: S is under a day, M a few days, L a week or
more. Each item follows CLAUDE.md rule 3: spec and contracts in one commit,
then the implementation and proof. Items marked **waits on 3.0** must not
start before the maintainer's decision is recorded there.

### 3.0 The TLS decision (S)

The roadmap says "TLS via rustls with verified crypto", and CLAUDE.md rule 8
says shipped dependencies are allowed only for cryptography from verified
libraries, OS and windowing bindings, and GPU access. rustls is a parser of
untrusted bytes (records, handshake messages, certificates), so the two
conflict, and the maintainer must choose. The options, to be filled in with
checked facts (versions, dependency counts, what each library has proven)
before the decision is asked for:

**Option A: rustls as a listed exception.** Add `rustls`, `webpki`,
`rustls-pki-types` and a crypto provider as `shipped` rows, with a new rule
8 clause naming TLS as the second exception (after `clazel-sys`) and
listing rustls in VERIFICATION.md's TCB, as the OS kernel is. The provider
must be one whose primitives are formally verified where such exist (the
`aws-lc-rs` provider wraps AWS-LC, parts of which are verified with SAW; a
libcrux or HACL\* provider, if one covers a full TLS 1.3 cipher suite, is
the better fit for the policy). Costs: tens of thousands of lines of
unverified parsing in the TCB; every version bump re-audits nothing; the
provider's own dependency tree.

**Option B: our own TLS 1.3 client, Tier 2.** RFC 8446: the record layer
(§5), handshake messages (§4), key schedule (§7.1), one cipher suite
(`TLS_CHACHA20_POLY1305_SHA256` or `TLS_AES_128_GCM_SHA256`) and one key
exchange (X25519), with the primitives from a verified library (libcrux or
`hacl-rs`) as the only shipped dependency, and X.509 certificate parsing
(RFC 5280, DER) and path validation (§6) as our own Tier 2 crates. The
state machine is a transducer like `clazel-fetch`'s. Costs: it is the
largest item in the roadmap so far, likely several phases' worth of proof
work, and the certificate part alone is comparable to the URL parser.

**Option C: A now, B later.** Take A, with the exception written as
temporary and a roadmap entry for B, so the `curl` clone and Phase 4's
text-mode browser do not wait for a TLS proof. The shell keeps TLS behind
one trait so the replacement is a swap.

**Recommendation:** C, with the exception recorded exactly (the rows, the
rule 8 text, the TCB entry) so that the README's "100% safe Rust" and
"every parser of untrusted input carries proofs" claims are qualified
wherever they appear until B lands. The decision, its date and its grounds
are recorded here, as 2.0 did.

### 3.1 HTTP field syntax (M)

`crates/clazel-http`, module `field/`. RFC 9110 §5.1 field names (and that
they are compared case-insensitively), §5.2 field lines and the combined
field value (comma-joined in order; `Set-Cookie` excluded, as §5.3's note
says: it is a list of its own, one field line per cookie), §5.5 field
values (what octets are allowed; leading and trailing whitespace is not part
of the value), §5.6.1 lists (the `#` rule, with empty elements dropped),
§5.6.2 tokens, §5.6.3 whitespace (OWS, RWS, BWS), §5.6.4 quoted strings
(and `quoted-pair`), §5.6.6 parameters, §8.6 the `Content-Length` grammar
(`1*DIGIT`, the list case where every element is the same value), and the
`Transfer-Encoding` and `Connection` list values 3.2 needs.

Spec functions take `Seq<u8>` (fields are octets, RFC 9110 §5.5). Lemmas: a
token contains no delimiter; unquoting a quoted string of a token-free
value and quoting it again round-trips; a combined value splits back into
its field lines when none contains a comma; `Content-Length` with repeated
identical values equals the single value.

Independent: the Fetch Standard §2.2 "HTTP" definitions (header names,
header values, "HTTP token code point", "collect an HTTP quoted string",
"get, decode, and split"), a different body's text for the same grammar,
proven equal on the inputs both define (the lemma states the class). Where
Fetch and RFC 9110 differ (Fetch strips only HTTP tab or space; the
`#` rule's treatment of empty elements), the difference is stated in the
lemma, not hidden.

Mutations seeded for each grammar rule. Conformance for this item is 3.3's.

### 3.2 HTTP/1.1 message framing (L)

`clazel-http`, module `message/`. RFC 9112 §2.1 message format, §2.2
message parsing (the leading CRLF rule, no whitespace between start-line and
first field line, what to do with a bare CR), §2.3 version, §4 status line
(status code exactly three digits; the reason phrase is kept but never
interpreted), §5 field line parsing with §5.1's rejection of whitespace
between field name and colon, and §5.2 obsolete line folding replaced by SP
as a user agent must, §6 message body: §6.1 `Transfer-Encoding` (only
`chunked`, and only as the final coding; anything else is unsupported and
closes the connection), §6.2 `Content-Length`, §6.3 message body length
(steps 1 to 8, as a client: 1xx, 204 and 304 and HEAD responses have no
body; `Transfer-Encoding` and `Content-Length` together is an error, the
smuggling case of §11.2, never resolved in favour of either), §7.1 chunked
transfer coding (chunk size in hex, chunk extensions parsed and ignored,
the trailer section parsed and dropped, §7.1.3 decoding), and §9.3 and
§9.6: when the response ends by connection close.

Request side: §3 request line, `Host` (RFC 9110 §7.2) and the fields 3.6
chooses, as a serializer `serialize_request(request) -> Seq<u8>`, with a
lemma that what it writes parses back as the same request (the request
parser exists only for this lemma and the differential test; the browser
never parses requests).

Modelling choices, listed in the spec header: the spec is a function over
the *complete* received bytes to one of `Incomplete`, `Invalid` or a parsed
response plus the bytes after it; the executable parser is incremental (it
takes bytes as they arrive and keeps a state) and is proven equal to the
spec on the concatenation of everything it was given, and to give
`Incomplete` on every proper prefix of a message it accepts, so that no
decision is ever made before the bytes that justify it have arrived. Limits
are modelling choices too, each stated with its number: the longest
status line, field line and field section accepted, the largest
`Content-Length` and chunk size (a `u64`, with overflow an error), and the
largest body. The parser never reserves more memory than the bytes it has
received, as the CBOR decoder does.

Independent: RFC 7230 §3 (the obsoleted text of the same protocol, by the
same working group, so weaker than a second body) for framing, and the
Fetch Standard's "HTTP-network fetch" step that reads the body for the
cases of §6.3, proven equal where the texts agree, with the differences
listed (RFC 7230 allowed obs-fold in a request; RFC 9112 does not).

### 3.3 HTTP conformance (M)

`tests/conformance_http.rs`: a differential test against `httparse` (the
parser hyper uses; no dependencies; a `test` row) on random messages,
mutated messages and the vendored corpora, comparing status, every field,
and where we reject whether `httparse` does; and the llhttp fixtures
(Node's HTTP parser, `test/response/*.md` and the chunked and
`Content-Length` cases of `test/request/*.md` that a client also sees),
vendored at a pinned commit with their license and converted by a
`cargo xtask testdata` converter that reads the fixed markdown shape and
fails if it changes. Every RFC 9112 §7.1 and §11 example appears as a case.
Expected failures (cases where llhttp is lenient by design) are listed with
reasons and never counted as passes. The summary lines follow
`xtask/src/conformance.rs`. Miri runs the unit tests.

After 3.1 to 3.3: **raise `clazel-http` to tier 2.**

### 3.4 DNS message format (M)

`crates/clazel-dns`. RFC 1035 §4.1.1 header (ID, QR, OPCODE, AA, TC, RD, RA,
Z must be zero, RCODE, the four counts), §4.1.2 question, §4.1.3 resource
record, §4.1.4 message compression (a pointer must point to an earlier
octet of the message than the pointer itself, which gives the decoder a
`decreases` clause and makes a forward or self pointer an error; the
standard says "a prior occurrence", and the comment at that spot says why
"prior" means a lower offset), §2.3.4 size limits (labels at most 63
octets, names at most 255, UDP messages at most 512), §2.3.3 case (names
compare case-insensitively; the decoder keeps what the server sent),
§3.2.2 and §3.2.4 TYPE and CLASS values (A, CNAME, AAAA from RFC 3596 §2;
IN), §3.3.1 CNAME, §3.4.1 A, RFC 3596 §2.2 AAAA, §4.2.2 the two-octet TCP
length prefix (for TC=1 fallback, RFC 7766 §8).

Functions: `encode_query(id, name) -> Seq<u8>` (a standard query, RD=1, one
question of type A or AAAA, class IN, no compression; the name is ASCII
already, `clazel-url` having applied IDNA), `decode_message(bytes) ->
Option<Message>`, and `answer_addresses(query, message) -> Option<Seq<Addr>>`,
which accepts a message only if its ID and question equal the query's
(RFC 5452 §4 to §6), its RCODE is 0 or 3 (NXDOMAIN gives the empty answer),
and returns the addresses of the records in the answer section whose owner
is the query name or a CNAME target reached from it within the answer
section (RFC 1034 §3.6.2); records in the authority and additional sections
are never used, and a CNAME chain that does not end in the answer section
gives no addresses (the shell may re-query the last target, RFC 1034 §5.3.3
step 3a). Lemmas: decoding a query we encoded gives it back; a decoded name
is at most 255 octets with labels at most 63; `answer_addresses` returns
only addresses from the answer section.

Independent: RFC 883 §4 (the predecessor, same wire format, different
text), proven equal to the decoder on every message, with any difference
listed; if the texts turn out identical in substance, say so and record the
transcription as same-RFC, as `clazel-ipc` did for RFC 7049.

Conformance: a differential against an independent crate with the fewest
dependencies that parses full messages (candidates: `simple-dns`,
`dns-parser`; the agent picks and the DEPENDENCIES.md row says why) on
random and mutated messages; a vendored corpus of real resolver responses
(captured once, stored as hex under `tests/data/` with a `SOURCE.md`
saying how, since no official suite exists), including a truncated one, a
NXDOMAIN, a CNAME chain and an AAAA answer; and the RFC 1035 §4.1.4
compression example. **Raise `clazel-dns` to tier 2.**

### 3.5 TLS (L to XL, waits on 3.0)

Per 3.0. Under A or C: `clazel-tls` is Tier 0 glue (a trait with `connect`,
`read`, `write`, `close` and the peer's verified certificate chain's
outcome), the `shipped` rows, the rule 8 text and the TCB entry; the
network shell's TLS loop is counted with it. Under B: the record layer and
handshake parsers as their own items, added here when chosen.

### 3.6 The client state machine (L)

`crates/clazel-fetch`. A pure transducer: `start(url, jar, now, context)`
gives the first action (`Connect { host, port, tls }`), and
`step(state, input)` maps an input (`Connected`, `Bytes(b)`, `Closed`,
`Error`) to actions (`Send(bytes)`, `Close`, `Done(response)`,
`Fail(reason)`) and the next state; the jar is part of the state and comes
back updated. It takes the HTTP functions (3.2) and URL functions as
parameters, as the kernel takes `UrlFns`, and `clazel-fetch` joins them to
the real ones in its last commit, like 2.13.

What it decides, each cited: the request (RFC 9112 §3.2.1 origin-form
target from the URL's path and query; `Host` from the URL, RFC 9110 §7.2;
`Connection: close`, one request per connection in this phase; `Accept:
*/*`; `User-Agent`), the `Cookie` field from RFC 6265bis §5.8.3 with the
HTTP request context of §5.2 (a navigation, top-level, GET, the redirect
chain's same-site status as §5.2.1 computes it), `Set-Cookie` field lines
of the response stored one by one by §5.7 as HTTP (never for a 1xx
response, §5.3), the `Secure` requirement from whether the connection is
TLS, redirects (RFC 9110 §15.4: 301, 302, 303, 307 and 308 with a
`Location`, resolved against the request URL by the URL parser; at most 20,
Fetch §4.4 step 5; a redirect to a non-HTTP(S) scheme fails), and failure
on anything else (an unsupported transfer coding, an invalid message, a
response that is not complete when the connection closes, unless §6.3
step 8 says close ends it).

Proven: `theorem_wire_cookies`, that in every trace the bytes of every
`Send` are the serialization of a request whose only jar-derived part is
the `Cookie` field value, and that value is §5.8's retrieval for that
request's URL and context; `theorem_jar_frame`, that the jar changes only
by §5.7 storage of the response's own `Set-Cookie` lines (so the Phase 2
root lemmas carry over); totality (at most 21 requests per fetch) and that
no action is emitted before the bytes that justify it (from 3.2's prefix
lemma). Mutations for each decision. Independent: the Fetch Standard's
"HTTP-redirect fetch" and the cookie steps of "HTTP-network-or-cache
fetch", transcribed and proven to give the same request sequence on a
stated class (no caching, GET only, no CORS).

### 3.7 Kernel integration (M)

`clazel-kernel`: a `Navigate` (and the user's `NavigateTab`) now produces an
output `Fetch { tab, url }` instead of an immediate commit; a new event
`Fetched { tab, outcome }` carries 3.6's result and commits the body (as
the `Commit` message's script field for now; Phase 4 gives it a document)
or an error. The jar updates happen in 3.6's transducer, which the kernel
runs as part of the fetch: so the kernel owns the jar, and the shell never
sees it. Restate the Phase 2 theorems with the new event and output: a
`Fetched` event is attributed to its tab's lock, like a frame to its
socket; a redirect is a navigation the user is treated as having made (the
same declassification 2.11 states). Each theorem keeps its certified
mutation. The IPC schema is unchanged. The kernel's WPT `cookies/` run adds
the rows that needed `Set-Cookie` from HTTP.

### 3.8 The network shell and the `curl` clone (M)

`crates/clazel-net` (Tier 0, counted): the resolver (nameservers read from
`/etc/resolv.conf` on both platforms, a query over UDP with a random ID,
one retry, TCP on TC=1; `127.0.0.1` and `::1` and IP-literal hosts need no
query), TCP connect with a timeout, the TLS loop (3.5), and the loop that
drives 3.6's transducer: read bytes, call `step`, carry out actions. The
shell contains no parsing of its own; `resolv.conf` is read by a proven
function in `clazel-dns` (RFC 1035 has no format for it; the `nameserver`
line grammar is ours, listed as a modelling choice). `clazel fetch URL`
prints the status line, the fields and the body. Tests, all without the
Internet: an in-process server (`std::net::TcpListener`) that serves the
`http-state` parser corpus the way its upstream server does (`Set-Cookie`
lines, then a redirect to `/cookie-parser-result`, which the row's
expected `Cookie` header checks), and the WPT `cookies/` rows that needed a
server; a hostile server (bytes that are not HTTP, a body that never ends,
a redirect loop, a chunk size of 2^64) that must give `Fail` and never a
panic or unbounded memory. The demo (`fetch https://example.com/`) needs the
Internet and is run locally, like the Phase 2 demo.

### 3.9 Status and README (S)

`cargo xtask report --write`, the network shell's line count next to the
host shell's, the Phase 3 note in README.md, this file's Status table and
ROADMAP.md.

## Order of work

```
3.0 TLS decision ───────────────────────────────────────> 3.5 TLS ─────┐
3.1 field syntax ─> 3.2 framing ─> 3.3 conformance ──┐                 │
3.4 DNS ──────────────────────────────────────────────┼─> 3.8 shell + curl clone ─> 3.9
                                                     └─> 3.6 client ─> 3.7 kernel ─┘
```

3.1, 3.4 and the research for 3.0 start at once; 3.6 can start against
abstract parameters as soon as 3.1's field types exist.

## Status

| Item | State |
|------|-------|
| 3.0 TLS decision | options drafted; facts to check; waits on the maintainer |
| 3.1 HTTP field syntax | not started |
| 3.2 HTTP/1.1 message framing | not started |
| 3.3 HTTP conformance | not started |
| 3.4 DNS message format | not started |
| 3.5 TLS | waits on 3.0 |
| 3.6 Client state machine | not started |
| 3.7 Kernel integration | not started |
| 3.8 Network shell and `curl` clone | not started |
| 3.9 Status and README | not started |

## Risks

- **TLS dominates.** Under option B the phase is several times its size;
  under A or C the README's safe-Rust and proof claims need qualifying
  text, and the project ships tens of thousands of unverified lines. 3.0
  states both costs so the maintainer chooses with them in view.
- **Incremental parsing proofs.** The prefix lemma (no decision before the
  data) is new; the UTF-8 decoder's "restore to the queue" modelling and
  the CBOR decoder's bounded-reservation lemma are the nearest precedents.
  If a single state machine is too slow for Verus, split it by section
  (status line, fields, body) as the URL parser was split by state.
- **Limits are policy.** Every maximum (field section size, body size,
  chunk size) is a choice the standard leaves open; each is a listed
  modelling choice with a number, never an unstated constant.
- **No Internet in CI.** Every test runs against in-process servers; only
  the demo reaches a real server, and it runs locally, as in Phase 2.
- **`Secure` needs TLS.** Until 3.5 lands, cookie tests over the socket run
  on `http://`, and `Secure` cookies are exercised only in the kernel's
  tests, which set the flag directly.
- **The resolver is environment-dependent.** `resolv.conf` differs across
  systems and may be absent (macOS keeps it generated); the shell fails
  closed with a message, and the demo documents it.
