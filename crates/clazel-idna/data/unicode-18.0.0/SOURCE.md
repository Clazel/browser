# Unicode 18.0.0 data for UTS #46 processing

Version: Unicode 18.0.0 (UTS #46 revision 36, 2026-08-31)
License: Unicode License v3 (`LICENSE.md`, copied from https://www.unicode.org/license.txt)

Each file is copied byte for byte from unicode.org. Upstream URLs:

- https://www.unicode.org/Public/18.0.0/idna/IdnaMappingTable.txt
  (Date: 2026-06-29, 15:25:07 GMT)
- https://www.unicode.org/Public/18.0.0/ucd/UnicodeData.txt
- https://www.unicode.org/Public/18.0.0/ucd/DerivedNormalizationProps.txt
  (Date: 2026-02-03, 23:09:53 GMT)
- https://www.unicode.org/Public/18.0.0/ucd/extracted/DerivedBidiClass.txt
  (Date: 2026-07-02, 16:50:27 GMT)
- https://www.unicode.org/Public/18.0.0/ucd/extracted/DerivedJoiningType.txt

`cargo xtask check` hashes every file and fails if one differs from the
line below, or if the directory holds anything else:

SHA-256: a03b1eb38032268c696406a83f0972d6a815acd2c8d4151d42ec0fda70ffced1 IdnaMappingTable.txt
SHA-256: 0736451de439ae7baf1425136617da495e09ee5afbe6e394374db7009ea08950 UnicodeData.txt
SHA-256: 98ac7f67d985fe781e317f6182e885e94cabb0c314769e6dd73e48b226931ccd DerivedNormalizationProps.txt
SHA-256: d9e23222522551348ea1ccfbb4f62efbf98982afb95840f8959c08ed992c5607 DerivedBidiClass.txt
SHA-256: e2408ff2c92b175b0f7bf62c989bbb54c7b077528fe31f8d69b96fa09e7d61ed DerivedJoiningType.txt

Unicode 18.0.0 is the version WPT's `url/resources/IdnaTestV2.json` was
generated from (WPT commit `13748c36fdf9dd77cd0b34dd6b244256b365ea60`,
"Update IDNA Test JSON to Unicode 18.0.0").

`xtask/src/unicode.rs` turns these files into
`crates/clazel-idna/src/uts46/data.rs`; the generated file's header lists
what it derives. To update: copy the files of a newer version, change the
directory name, URLs and hashes, and run `cargo xtask tables`.

What each file provides:
- IdnaMappingTable.txt: UTS #46 §5's Status and mapping of every code point.
- UnicodeData.txt: Decomposition_Mapping (canonical ones only),
  Canonical_Combining_Class, General_Category (for "Mark").
- DerivedNormalizationProps.txt: Full_Composition_Exclusion (the other
  properties in it are not read).
- DerivedBidiClass.txt: Bidi_Class, for CheckBidi (RFC 5893 §2).
- DerivedJoiningType.txt: Joining_Type, for CheckJoiners (RFC 5892
  Appendix A.1).
