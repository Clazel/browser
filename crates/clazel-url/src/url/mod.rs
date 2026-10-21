//! URLs (URL §4): the URL record (§4.1), the basic URL parser (§4.4) and
//! the URL serializer (§4.5).
//!
//! - [`spec`]: a step-by-step transcription of the standard, one spec
//!   function per parser state.
//! - [`termination`]: why the parser's state machine terminates.
//! - [`contract`]: what the executable functions are proven to satisfy.
//! - [`record`]: the exec URL record, `ParsedUrl`, and string helpers.
//! - [`machine`]: the exec parser's variables and how one exec run relates
//!   to one spec run.
//! - [`states_scheme`], [`states_authority`], [`states_path`],
//!   [`states_query`]: one proven exec function per state.
//! - [`path_ops`]: appending, shortening, Windows drive letters.
//! - [`parse`]: the exec basic URL parser; [`serialize`]: the serializers.
//! - [`lemmas`]: facts proven about the spec (totality, §4.1's record
//!   invariants); [`examples`]: the standard's and RFC 3986's examples,
//!   evaluated.
//! - [`independent`]: a second transcription, from RFC 3986 (Appendix B,
//!   §5.2, §5.3), and the class of bases and references on which it is
//!   proven to agree with the basic URL parser; [`runs`]: the lemmas about
//!   parser runs that proof uses.

pub mod contract;
pub mod examples;
pub mod independent;
pub mod lemmas;
pub mod machine;
pub mod parse;
pub mod path_ops;
pub mod record;
pub mod runs;
pub mod serialize;
pub mod spec;
pub mod states_authority;
pub mod states_path;
pub mod states_query;
pub mod states_scheme;
pub mod termination;
