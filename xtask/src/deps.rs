//! Dependency allowlist (Phase 0 item 0.7). The allowlist is the table in
//! `docs/DEPENDENCIES.md`, which also documents the rules checked here.

use std::collections::{BTreeMap, BTreeSet};
use std::process::Command;

use serde_json::Value;

pub const PATH: &str = "docs/DEPENDENCIES.md";
const BEGIN: &str = "<!-- BEGIN ALLOWLIST";
const END: &str = "<!-- END ALLOWLIST -->";
const CRATES_IO: &str = "registry+https://github.com/rust-lang/crates.io-index";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Class {
    Shipped,
    Proof,
    Tooling,
}

/// One allowlist row.
#[derive(Debug)]
pub struct Row {
    pub name: String,
    pub version: String,
    pub class: Class,
}

/// Parse the allowlist table between the markers in `text`.
pub fn parse_allowlist(text: &str) -> Result<Vec<Row>, String> {
    let start = text
        .find(BEGIN)
        .ok_or_else(|| format!("{PATH}: no {BEGIN} marker"))?;
    let body = text.get(start..).unwrap_or_default();
    let end = body
        .find(END)
        .ok_or_else(|| format!("{PATH}: no {END} marker"))?;
    let mut rows = Vec::new();
    for line in body.get(..end).unwrap_or_default().lines().skip(1) {
        let line = line.trim();
        if !line.starts_with('|') {
            continue;
        }
        let cells: Vec<&str> = line.trim_matches('|').split('|').map(str::trim).collect();
        let [name, version, class, why] = cells.as_slice() else {
            return Err(format!("{PATH}: expected 4 columns in: {line}"));
        };
        if *name == "Package" || name.chars().all(|c| c == '-') {
            continue;
        }
        let class = match *class {
            "shipped" => Class::Shipped,
            "proof" => Class::Proof,
            "tooling" => Class::Tooling,
            other => return Err(format!("{PATH}: {name}: unknown class {other:?}")),
        };
        if why.is_empty() {
            return Err(format!("{PATH}: {name} {version}: empty \"Why\""));
        }
        rows.push(Row {
            name: (*name).to_owned(),
            version: (*version).to_owned(),
            class,
        });
    }
    Ok(rows)
}

struct Package {
    name: String,
    version: String,
    source: Option<String>,
}

/// The resolved graph from `cargo metadata`.
struct Graph {
    packages: BTreeMap<String, Package>,
    edges: BTreeMap<String, Vec<String>>,
    members: BTreeSet<String>,
}

fn load_graph() -> Result<Graph, String> {
    let out = Command::new("cargo")
        .args(["metadata", "--format-version", "1", "--locked"])
        .output()
        .map_err(|e| format!("cannot run cargo metadata: {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "cargo metadata failed:\n{}",
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    let meta: Value = serde_json::from_slice(&out.stdout)
        .map_err(|e| format!("cargo metadata output is not JSON: {e}"))?;
    let str_of = |v: &Value, k: &str| v.get(k).and_then(Value::as_str).map(str::to_owned);
    let mut packages = BTreeMap::new();
    for p in meta
        .get("packages")
        .and_then(Value::as_array)
        .ok_or("cargo metadata: no packages")?
    {
        let id = str_of(p, "id").ok_or("package without id")?;
        packages.insert(
            id,
            Package {
                name: str_of(p, "name").ok_or("package without name")?,
                version: str_of(p, "version").ok_or("package without version")?,
                source: str_of(p, "source"),
            },
        );
    }
    let mut edges = BTreeMap::new();
    for n in meta
        .get("resolve")
        .and_then(|r| r.get("nodes"))
        .and_then(Value::as_array)
        .ok_or("cargo metadata: no resolve graph")?
    {
        let id = str_of(n, "id").ok_or("node without id")?;
        // Every edge counts, whatever its kind or platform: a package that
        // is locked is code we have agreed to depend on.
        let deps = n
            .get("deps")
            .and_then(Value::as_array)
            .map(|ds| ds.iter().filter_map(|d| str_of(d, "pkg")).collect())
            .unwrap_or_default();
        edges.insert(id, deps);
    }
    let members = meta
        .get("workspace_members")
        .and_then(Value::as_array)
        .map(|ms| {
            ms.iter()
                .filter_map(|m| m.as_str().map(str::to_owned))
                .collect()
        })
        .unwrap_or_default();
    Ok(Graph {
        packages,
        edges,
        members,
    })
}

/// Check the resolved graph against the allowlist. `tooling` holds the names
/// of workspace crates marked `tooling = true`. Returns a summary line.
pub fn check(tooling: &BTreeSet<String>) -> Result<String, Vec<String>> {
    let text = std::fs::read_to_string(PATH).map_err(|e| vec![format!("{PATH}: {e}")])?;
    let rows = parse_allowlist(&text).map_err(|e| vec![e])?;
    let graph = load_graph().map_err(|e| vec![e])?;
    let mut problems = Vec::new();

    let mut allowed: BTreeMap<(&str, &str), Class> = BTreeMap::new();
    for r in &rows {
        if allowed
            .insert((r.name.as_str(), r.version.as_str()), r.class)
            .is_some()
        {
            problems.push(format!("{PATH}: {} {} listed twice", r.name, r.version));
        }
    }

    // Rules 1 and 2: every third-party package listed, every row used.
    let mut used: BTreeSet<(&str, &str)> = BTreeSet::new();
    for (id, p) in &graph.packages {
        if graph.members.contains(id) {
            continue;
        }
        if p.source.as_deref() != Some(CRATES_IO) {
            problems.push(format!(
                "{} {}: not from crates.io (source {:?})",
                p.name, p.version, p.source
            ));
        }
        let key = (p.name.as_str(), p.version.as_str());
        if allowed.contains_key(&key) {
            used.insert(key);
        } else {
            problems.push(format!(
                "{} {}: not on the allowlist in {PATH}",
                p.name, p.version
            ));
        }
    }
    for r in &rows {
        if !used.contains(&(r.name.as_str(), r.version.as_str())) {
            problems.push(format!(
                "{PATH}: {} {} is listed but not in the dependency graph (stale row)",
                r.name, r.version
            ));
        }
    }

    // Rule 3: walk from browser crates. Outside vstd only `shipped` is
    // allowed; inside vstd's subtree `proof` is allowed too.
    let roots = graph
        .members
        .iter()
        .filter(|id| {
            graph
                .packages
                .get(*id)
                .is_some_and(|p| !tooling.contains(&p.name))
        })
        .map(|id| (id.clone(), false));
    let mut pending: Vec<(String, bool)> = roots.collect();
    let mut seen: BTreeSet<(String, bool)> = BTreeSet::new();
    while let Some((id, in_proof)) = pending.pop() {
        if !seen.insert((id.clone(), in_proof)) {
            continue;
        }
        let Some(p) = graph.packages.get(&id) else {
            continue;
        };
        let mut in_proof = in_proof;
        if !graph.members.contains(&id) {
            in_proof = in_proof || p.name == "vstd";
            let class = allowed.get(&(p.name.as_str(), p.version.as_str()));
            let ok = match class {
                Some(Class::Shipped) => true,
                Some(Class::Proof) => in_proof,
                Some(Class::Tooling) => false,
                None => true, // already reported under rule 1
            };
            if !ok {
                problems.push(format!(
                    "{} {}: class {:?} but reachable from browser crates{}",
                    p.name,
                    p.version,
                    class.copied().unwrap_or(Class::Shipped),
                    if in_proof {
                        " (inside vstd)"
                    } else {
                        " outside vstd"
                    }
                ));
            }
        }
        for dep in graph.edges.get(&id).into_iter().flatten() {
            pending.push((dep.clone(), in_proof));
        }
    }

    if problems.is_empty() {
        let count = |c: Class| rows.iter().filter(|r| r.class == c).count();
        Ok(format!(
            "{} third-party packages: {} shipped, {} proof, {} tooling",
            rows.len(),
            count(Class::Shipped),
            count(Class::Proof),
            count(Class::Tooling)
        ))
    } else {
        Err(problems)
    }
}

#[cfg(test)]
mod tests {
    use super::{Class, parse_allowlist};

    #[test]
    fn parses_rows_between_markers() -> Result<(), String> {
        let text = "| ignored | 1 | shipped | outside |\n\
                    <!-- BEGIN ALLOWLIST: x -->\n\
                    | Package | Version | Class | Why |\n\
                    |---------|---------|-------|-----|\n\
                    | a | 1.0.0 | proof | because |\n\
                    | b | 2.0.0 | tooling | because |\n\
                    <!-- END ALLOWLIST -->\n";
        let rows = parse_allowlist(text)?;
        assert_eq!(rows.len(), 2);
        assert!(matches!(rows.first(), Some(r) if r.name == "a" && r.class == Class::Proof));
        Ok(())
    }

    #[test]
    fn rejects_bad_rows() {
        let wrap = |row: &str| format!("<!-- BEGIN ALLOWLIST -->\n{row}\n<!-- END ALLOWLIST -->");
        assert!(parse_allowlist(&wrap("| a | 1 | shiped | x |")).is_err());
        assert!(parse_allowlist(&wrap("| a | 1 | proof |  |")).is_err());
        assert!(parse_allowlist(&wrap("| a | 1 | proof |")).is_err());
    }
}
