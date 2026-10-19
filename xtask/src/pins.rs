//! Pinned tool versions from `scripts/toolchains.env`.

/// Parsed `KEY=VALUE` pairs.
pub struct Pins {
    entries: Vec<(String, String)>,
}

pub const PATH: &str = "scripts/toolchains.env";

impl Pins {
    /// Read the pins file from the repo root.
    pub fn load() -> Result<Self, String> {
        let text = std::fs::read_to_string(PATH).map_err(|e| format!("{PATH}: {e}"))?;
        Ok(Self::parse(&text))
    }

    fn parse(text: &str) -> Self {
        let entries = text
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty() && !l.starts_with('#'))
            .filter_map(|l| l.split_once('='))
            .map(|(k, v)| (k.trim().to_owned(), v.trim().to_owned()))
            .collect();
        Self { entries }
    }

    /// The value of `key`, or an error naming the missing key.
    pub fn get(&self, key: &str) -> Result<&str, String> {
        self.entries
            .iter()
            .find(|(k, _)| k == key)
            .map(|(_, v)| v.as_str())
            .ok_or_else(|| format!("{PATH}: missing {key}"))
    }
}

#[cfg(test)]
mod tests {
    use super::Pins;

    #[test]
    fn parses_and_skips_comments() {
        let p = Pins::parse("# c\nA=1\n\n B = two \nbad line\n");
        assert_eq!(p.get("A"), Ok("1"));
        assert_eq!(p.get("B"), Ok("two"));
        assert!(p.get("bad line").is_err());
    }
}
