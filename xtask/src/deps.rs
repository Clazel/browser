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
    Test,
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
            "test" => Class::Test,
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

/// One resolved dependency edge.
struct Edge {
    to: String,
    /// Every way this edge is declared is `[dev-dependencies]`, so the code
    /// it reaches is compiled only into tests.
    dev_only: bool,
}

/// The resolved graph from `cargo metadata`.
struct Graph {
    packages: BTreeMap<String, Package>,
    edges: BTreeMap<String, Vec<Edge>>,
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
        // is locked is code we have agreed to depend on. The kind decides
        // only which class it may have (rule 3).
        let deps = n
            .get("deps")
            .and_then(Value::as_array)
            .map(|ds| {
                ds.iter()
                    .filter_map(|d| {
                        let kinds = d.get("dep_kinds").and_then(Value::as_array)?;
                        Some(Edge {
                            to: str_of(d, "pkg")?,
                            dev_only: !kinds.is_empty()
                                && kinds
                                    .iter()
                                    .all(|k| k.get("kind").and_then(Value::as_str) == Some("dev")),
                        })
                    })
                    .collect()
            })
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

    problems.extend(reach_problems(&graph, &allowed, tooling));

    if problems.is_empty() {
        let count = |c: Class| rows.iter().filter(|r| r.class == c).count();
        Ok(format!(
            "{} third-party packages: {} shipped, {} proof, {} test, {} tooling",
            rows.len(),
            count(Class::Shipped),
            count(Class::Proof),
            count(Class::Test),
            count(Class::Tooling)
        ))
    } else {
        Err(problems)
    }
}

/// How a package was reached from a browser crate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Via {
    /// Through `vstd`.
    proof: bool,
    /// Through a `[dev-dependencies]` edge of a workspace crate.
    test: bool,
}

/// Rule 3: walk from browser crates and check each package's class against
/// how it is reached. `proof` is allowed inside vstd's subtree, `test` only
/// below a dev-only edge out of a workspace crate, `shipped` anywhere.
fn reach_problems(
    graph: &Graph,
    allowed: &BTreeMap<(&str, &str), Class>,
    tooling: &BTreeSet<String>,
) -> Vec<String> {
    let mut problems = Vec::new();
    let start = Via {
        proof: false,
        test: false,
    };
    let mut pending: Vec<(String, Via)> = graph
        .members
        .iter()
        .filter(|id| {
            graph
                .packages
                .get(*id)
                .is_some_and(|p| !tooling.contains(&p.name))
        })
        .map(|id| (id.clone(), start))
        .collect();
    let mut seen: BTreeSet<(String, Via)> = BTreeSet::new();
    while let Some((id, via)) = pending.pop() {
        if !seen.insert((id.clone(), via)) {
            continue;
        }
        let Some(p) = graph.packages.get(&id) else {
            continue;
        };
        let member = graph.members.contains(&id);
        let mut via = via;
        if !member {
            via.proof = via.proof || p.name == "vstd";
            let class = allowed.get(&(p.name.as_str(), p.version.as_str()));
            let ok = match class {
                Some(Class::Shipped) | None => true, // None: reported under rule 1
                // A proof package may also sit below a dev-only edge: both
                // are compiled into no shipped binary (a package used both
                // ways takes the stricter class, `proof`).
                Some(Class::Proof) => via.proof || via.test,
                Some(Class::Test) => via.test,
                Some(Class::Tooling) => false,
            };
            if !ok {
                let route = match (via.proof, via.test) {
                    (false, false) => "through normal dependencies",
                    (true, false) => "inside vstd",
                    (false, true) => "through dev-dependencies",
                    (true, true) => "inside vstd, through dev-dependencies",
                };
                problems.push(format!(
                    "{} {}: class {:?} but reachable from browser crates {route}",
                    p.name,
                    p.version,
                    class.copied().unwrap_or(Class::Shipped),
                ));
            }
        }
        for e in graph.edges.get(&id).into_iter().flatten() {
            // Only a workspace crate's own dev-dependencies are test-only;
            // cargo never resolves a third-party package's dev-dependencies.
            let test = via.test || (member && e.dev_only);
            pending.push((e.to.clone(), Via { test, ..via }));
        }
    }
    problems
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use super::{Class, Edge, Graph, Package, parse_allowlist, reach_problems};

    /// A browser crate `app` and a tooling crate `xtask`, with `edges` as
    /// (from, to, dev_only); every other name is a third-party package.
    fn graph(edges: &[(&str, &str, bool)]) -> Graph {
        let mut packages = BTreeMap::new();
        let mut map: BTreeMap<String, Vec<Edge>> = BTreeMap::new();
        for (from, to, dev_only) in edges {
            for n in [from, to] {
                packages.insert(
                    (*n).to_owned(),
                    Package {
                        name: (*n).to_owned(),
                        version: "1.0.0".to_owned(),
                        source: None,
                    },
                );
            }
            map.entry((*from).to_owned()).or_default().push(Edge {
                to: (*to).to_owned(),
                dev_only: *dev_only,
            });
        }
        Graph {
            packages,
            edges: map,
            members: ["app".to_owned(), "xtask".to_owned()].into(),
        }
    }

    fn allow<'a>(rows: &[(&'a str, Class)]) -> BTreeMap<(&'a str, &'a str), Class> {
        rows.iter().map(|(n, c)| ((*n, "1.0.0"), *c)).collect()
    }

    fn tooling() -> BTreeSet<String> {
        ["xtask".to_owned()].into()
    }

    #[test]
    fn test_class_allowed_only_below_dev_edges() {
        let rows = allow(&[("diff", Class::Test), ("cfg", Class::Test)]);
        // app -[dev]-> diff -> cfg: fine, the whole subtree is test-only.
        let dev = graph(&[("app", "diff", true), ("diff", "cfg", false)]);
        assert!(reach_problems(&dev, &rows, &tooling()).is_empty());
        // Planted violation: the same package through a normal edge.
        let normal = graph(&[("app", "diff", false), ("diff", "cfg", false)]);
        let problems = reach_problems(&normal, &rows, &tooling());
        assert_eq!(problems.len(), 2, "{problems:?}");
        assert!(
            problems
                .iter()
                .all(|p| p.contains("through normal dependencies"))
        );
        // Reached both ways: the normal edge still fails.
        let both = graph(&[("app", "diff", true), ("app", "cfg", false)]);
        assert_eq!(reach_problems(&both, &rows, &tooling()).len(), 1);
    }

    #[test]
    fn dev_edges_of_third_party_packages_do_not_count() {
        let rows = allow(&[("lib", Class::Shipped), ("cfg", Class::Test)]);
        let g = graph(&[("app", "lib", false), ("lib", "cfg", true)]);
        assert_eq!(reach_problems(&g, &rows, &tooling()).len(), 1);
    }

    #[test]
    fn proof_packages_may_also_be_reached_below_dev_edges() {
        let rows = allow(&[
            ("vstd", Class::Proof),
            ("syn", Class::Proof),
            ("diff", Class::Test),
        ]);
        // syn is inside vstd and below a dev-only edge: both are fine.
        let g = graph(&[
            ("app", "vstd", false),
            ("vstd", "syn", false),
            ("app", "diff", true),
            ("diff", "syn", false),
        ]);
        assert!(reach_problems(&g, &rows, &tooling()).is_empty());
        // Through a normal edge it still fails.
        let bad = graph(&[("app", "syn", false)]);
        assert_eq!(reach_problems(&bad, &rows, &tooling()).len(), 1);
    }

    #[test]
    fn tooling_and_proof_rules_unchanged() {
        let rows = allow(&[
            ("vstd", Class::Proof),
            ("syn", Class::Proof),
            ("json", Class::Tooling),
        ]);
        let ok = graph(&[
            ("app", "vstd", false),
            ("vstd", "syn", false),
            ("xtask", "json", false),
        ]);
        assert!(reach_problems(&ok, &rows, &tooling()).is_empty());
        let bad = graph(&[("app", "syn", false), ("app", "json", true)]);
        assert_eq!(reach_problems(&bad, &rows, &tooling()).len(), 2);
    }

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
