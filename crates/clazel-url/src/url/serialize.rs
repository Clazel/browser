//! The executable URL serializer and URL path serializer (URL §4.5),
//! proven to meet [`super::contract`]. The step comments live in
//! [`super::spec`].

use super::record::{ParsedPath, ParsedUrl};
#[allow(unused_imports)]
use super::spec::*;
use crate::host::record::{append, copy};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The URL path serializer (URL §4.5).
pub fn url_path_serializer(path: &ParsedPath) -> (output: Vec<u32>)
    ensures
        super::contract::url_path_serializer_ensures(path@, output@),
{
    match path {
        ParsedPath::Opaque(s) => copy(s.as_slice()),
        ParsedPath::List(l) => {
            let ghost v = super::record::segments_view(l@);
            let mut output: Vec<u32> = Vec::new();
            let mut i: usize = 0;
            assert(v.subrange(0, 0) =~= Seq::<Seq<u32>>::empty());
            assert(output@ =~= seq![]);
            while i < l.len()
                invariant
                    i <= l.len(),
                    v == super::record::segments_view(l@),
                    output@ == serialize_segments(v.subrange(0, i as int)),
                decreases l.len() - i,
            {
                output.push(0x2F);
                if let Some(s) = super::record::segment(l.as_slice(), i) {
                    append(&mut output, s.as_slice());
                }
                assert(v.subrange(0, i + 1).drop_last() =~= v.subrange(0, i as int));
                assert(v.subrange(0, i + 1).last() == l@[i as int]@);
                // Never saturates: i is below a length.
                i = i.saturating_add(1);
            }
            assert(v.subrange(0, l@.len() as int) =~= v);
            output
        },
    }
}

impl ParsedUrl {
    /// The URL serializer (URL §4.5), with exclude fragment.
    pub fn serialize(&self, exclude_fragment: bool) -> (output: Vec<u32>)
        ensures
            super::contract::url_serializer_ensures(self@, exclude_fragment, output@),
    {
        let ghost url = self@;
        // 1.
        let mut output = copy(self.scheme.as_slice());
        output.push(0x3A);
        let ghost o1 = url.scheme + seq![0x3Au32];
        assert(output@ =~= o1);
        // 2.
        if let Some(host) = &self.host {
            {
                // 2.1
                output.push(0x2F);
                output.push(0x2F);
                let ghost o21 = o1 + seq![0x2Fu32, 0x2F];
                assert(output@ =~= o21);
                // 2.2
                if !self.username.is_empty() || !self.password.is_empty() {
                    append(&mut output, self.username.as_slice());
                    let ghost o221 = o21 + url.username;
                    assert(output@ =~= o221);
                    if !self.password.is_empty() {
                        output.push(0x3A);
                        append(&mut output, self.password.as_slice());
                        assert(output@ =~= o221 + seq![0x3Au32] + url.password);
                    }
                    output.push(0x40);
                }
                let ghost o22 = output@;
                // 2.3
                let h = host.serialize();
                append(&mut output, h.as_slice());
                let ghost o23 = o22 + crate::host::spec::host_serializer(url.host->Some_0);
                assert(output@ =~= o23);
                // 2.4
                if let Some(port) = self.port {
                    output.push(0x3A);
                    crate::host::serialize::push_decimal(port as u32, &mut output);
                    assert(output@ =~= o23 + seq![0x3Au32] + crate::host::spec::serialize_integer(port as nat));
                }
            }
        }
        let ghost o2 = output@;
        assert(o2 == match url.host {
            Some(host) => {
                let output = o1 + seq![0x2Fu32, 0x2F];
                let output = if includes_credentials(url) {
                    let output = output + url.username;
                    let output = if url.password.len() > 0 {
                        output + seq![0x3Au32] + url.password
                    } else {
                        output
                    };
                    output + seq![0x40u32]
                } else {
                    output
                };
                let output = output + crate::host::spec::host_serializer(host);
                match url.port {
                    Some(port) => output + seq![0x3Au32] + crate::host::spec::serialize_integer(port),
                    None => output,
                }
            },
            None => o1,
        });
        proof {
            match &self.path {
                ParsedPath::List(l) => {
                    assert(super::record::segments_view(l@).len() == l@.len());
                    if l@.len() > 0 {
                        assert(super::record::segments_view(l@)[0] == l@[0]@);
                    }
                },
                ParsedPath::Opaque(_) => {},
            }
        }
        // 3.
        if let (None, ParsedPath::List(l)) = (&self.host, &self.path) {
            let first_empty = match super::record::segment(l.as_slice(), 0) {
                Some(s) => s.is_empty(),
                None => false,
            };
            if l.len() > 1 && first_empty {
                assert(super::record::segments_view(l@)[0] == l@[0]@);
                output.push(0x2F);
                output.push(0x2E);
                assert(output@ =~= o2 + seq![0x2Fu32, 0x2E]);
            }
        }
        let ghost o3 = output@;
        assert(o3 == if url.host is None && (url.path matches UrlPath::List(p) && p.len() > 1 && p[0].len() == 0) {
            o2 + seq![0x2Fu32, 0x2E]
        } else {
            o2
        });
        // 4.
        let p = url_path_serializer(&self.path);
        append(&mut output, p.as_slice());
        let ghost o4 = output@;
        assert(o4 == o3 + super::spec::url_path_serializer(url.path));
        // 5.
        if let Some(query) = &self.query {
            output.push(0x3F);
            append(&mut output, query.as_slice());
            assert(output@ =~= o4 + seq![0x3Fu32] + query@);
        }
        let ghost o5 = output@;
        // 6.
        if let (false, Some(fragment)) = (exclude_fragment, &self.fragment) {
            output.push(0x23);
            append(&mut output, fragment.as_slice());
            assert(output@ =~= o5 + seq![0x23u32] + fragment@);
        }
        // 7.
        output
    }
}

} // verus!
