#![feature(allocator_api)]

use std::sync::Once;

use deko_core::mm::DEKO_FRAME_ALLOCATOR_FULL;
use deko_core::policy::DekoPolicyEngine;

static INIT: Once = Once::new();
static mut HEAP_BUFFER: Option<Vec<u8>> = None;

fn align_up(addr: u64, align: u64) -> u64 { (addr + align - 1) & !(align - 1) }

fn setup_allocator() {
    INIT.call_once(|| unsafe {
        let total_size = 0x20_00000 + 0x10000;
        let buffer = vec![0u8; total_size];

        let raw_start = buffer.as_ptr() as u64;
        let aligned_start = align_up(raw_start, 0x10000);
        let offset = (aligned_start - raw_start) as usize;
        let aligned_length = (total_size - offset) as u64;

        DEKO_FRAME_ALLOCATOR_FULL.init(aligned_start, aligned_length);
        HEAP_BUFFER = Some(buffer);
    });
}

fn valid_policy_bytes() -> &'static [u8] {
    br#"
[lattice]
levels = ["public", "app_internal", "secret"]
relations = [["public", "app_internal"], ["app_internal", "secret"]]
bot = "public"
top = "secret"
"#
}

fn valid_policy_with_redundant_edge_bytes() -> &'static [u8] {
    br#"
[lattice]
levels = ["public", "app_internal", "secret"]
relations = [
  ["public", "app_internal"],
  ["app_internal", "secret"],
  ["public", "secret"],
]
bot = "public"
top = "secret"
"#
}

fn valid_policy_with_diamond_bytes() -> &'static [u8] {
    br#"
[lattice]
levels = ["public", "service_a", "service_b", "secret"]
relations = [
  ["public", "service_a"],
  ["public", "service_b"],
  ["service_a", "secret"],
  ["service_b", "secret"],
]
bot = "public"
top = "secret"
"#
}

fn valid_policy_with_sixteen_levels_bytes() -> &'static [u8] {
    br#"
[lattice]
levels = [
  "l0_public",
  "l1_a", "l1_b", "l1_c",
  "l2_a1", "l2_a2", "l2_b1", "l2_b2", "l2_c1", "l2_c2",
  "l3_x", "l3_y", "l3_z", "l3_w",
  "l4_secret",
]
relations = [
  ["l0_public", "l1_a"],
  ["l0_public", "l1_b"],
  ["l0_public", "l1_c"],

  ["l1_a", "l2_a1"],
  ["l1_a", "l2_a2"],
  ["l1_b", "l2_b1"],
  ["l1_b", "l2_b2"],
  ["l1_c", "l2_c1"],
  ["l1_c", "l2_c2"],

  ["l2_a1", "l3_x"],
  ["l2_a2", "l3_x"],
  ["l2_b1", "l3_y"],
  ["l2_b2", "l3_y"],
  ["l2_c1", "l3_z"],
  ["l2_c2", "l3_w"],

  ["l3_x", "l4_secret"],
  ["l3_y", "l4_secret"],
  ["l3_z", "l4_secret"],
  ["l3_w", "l4_secret"],
]
bot = "l0_public"
top = "l4_secret"
"#
}

fn invalid_unknown_relation_level_bytes() -> &'static [u8] {
    br#"
[lattice]
levels = ["public", "app_internal", "secret"]
relations = [["public", "unknown_level"]]
bot = "public"
top = "secret"
"#
}

fn invalid_duplicate_level_bytes() -> &'static [u8] {
    br#"
[lattice]
levels = ["public", "secret", "secret"]
relations = [["public", "secret"]]
bot = "public"
top = "secret"
"#
}

fn invalid_bottom_bytes() -> &'static [u8] {
    br#"
[lattice]
levels = ["public", "app_internal", "secret"]
relations = [["public", "app_internal"], ["app_internal", "secret"]]
bot = "missing_bottom"
top = "secret"
"#
}

fn invalid_top_bytes() -> &'static [u8] {
    br#"
[lattice]
levels = ["public", "app_internal", "secret"]
relations = [["public", "app_internal"], ["app_internal", "secret"]]
bot = "public"
top = "missing_top"
"#
}

fn invalid_cycle_bytes() -> &'static [u8] {
    br#"
[lattice]
levels = ["public", "secret"]
relations = [["public", "secret"], ["secret", "public"]]
bot = "public"
top = "secret"
"#
}

fn invalid_missing_join_meet_bytes() -> &'static [u8] {
    br#"
[lattice]
levels = ["left", "right"]
relations = []
bot = "left"
top = "right"
"#
}

fn direct_edges<Row: AsRef<[bool]>>(flows: &[Row]) -> Vec<(usize, usize)> {
    let n = flows.len();
    let mut edges = Vec::new();

    for src in 0..n {
        let src_row = flows[src].as_ref();
        for dst in 0..n {
            if src == dst || !src_row[dst] {
                continue;
            }

            let mut covered = false;
            for mid in 0..n {
                if mid != src && mid != dst && src_row[mid] && flows[mid].as_ref()[dst] {
                    covered = true;
                    break;
                }
            }

            if !covered {
                edges.push((src, dst));
            }
        }
    }

    edges
}

fn render_lattice<Row: AsRef<[bool]>>(level_names: &[String], flows: &[Row]) -> String {
    let edges = direct_edges(flows);
    let n = level_names.len();

    if n == 0 {
        return "<empty lattice>".to_string();
    }

    let mut indegree = vec![0usize; n];
    for &(_, dst) in &edges {
        indegree[dst] += 1;
    }

    let mut layers: Vec<Vec<usize>> = Vec::new();
    let mut seen = vec![false; n];
    loop {
        let mut layer = Vec::new();
        for node in 0..n {
            if seen[node] {
                continue;
            }
            let ready = edges.iter().filter(|&&(src, dst)| dst == node && !seen[src]).count() == 0;
            if ready {
                layer.push(node);
            }
        }

        if layer.is_empty() {
            break;
        }

        for &node in &layer {
            seen[node] = true;
        }
        layers.push(layer);
    }

    if seen.iter().any(|seen| !seen) {
        return format!("direct edges: {:?}", edges);
    }

    let mut lines = Vec::new();
    let reversed_layers = layers.iter().rev().collect::<Vec<_>>();

    for (layer_idx, layer) in reversed_layers.iter().enumerate() {
        lines.push(format!(
            "Layer {}: {}",
            reversed_layers.len() - 1 - layer_idx,
            layer
                .iter()
                .map(|&idx| level_names[idx].as_str())
                .collect::<Vec<_>>()
                .join(", ")
        ));

        for &node in *layer {
            let lowers = edges
                .iter()
                .filter(|&&(_, dst)| dst == node)
                .map(|&(src, _)| level_names[src].as_str())
                .collect::<Vec<_>>();
            if !lowers.is_empty() {
                lines.push(format!("  {} <- {}", level_names[node], lowers.join(", ")));
            }
        }

        if layer_idx + 1 != reversed_layers.len() {
            lines.push(String::new());
        }
    }

    lines.push(format!("direct edges: {:?}", edges));
    lines.join("\n")
}

fn expect_policy_accepts(name: &str, bytes: &[u8]) {
    let engine = DekoPolicyEngine::init_from_bytes(bytes)
        .unwrap_or_else(|_| panic!("{name}: policy should build a policy engine"));
    assert!(engine.default_domain.is_some(), "valid policy should install a default domain");
    let lattice = engine
        .default_lattice()
        .unwrap_or_else(|| panic!("{name}: valid policy should compile a default lattice"));
    let level_names: Vec<String> =
        lattice.level_names.iter().map(|name| String::from_utf8_lossy(name).into_owned()).collect();
    println!(
        "{name}: compiled lattice: levels={:?}, bot={:?}, top={:?}, flows={:?}",
        level_names, lattice.bot, lattice.top, lattice.flows
    );
    println!("{name}: lattice graph:\n{}", render_lattice(&level_names, &lattice.flows));
}

fn expect_policy_rejects(name: &str, bytes: &[u8]) {
    let result = DekoPolicyEngine::init_from_bytes(bytes);
    assert!(result.is_err(), "{name}: invalid policy should be rejected");
}

fn main() {
    setup_allocator();

    expect_policy_accepts("linear_chain", valid_policy_bytes());
    expect_policy_accepts("redundant_transitive_edge", valid_policy_with_redundant_edge_bytes());
    expect_policy_accepts("diamond_lattice", valid_policy_with_diamond_bytes());
    expect_policy_accepts("sixteen_level_lattice", valid_policy_with_sixteen_levels_bytes());

    expect_policy_rejects("unknown_relation_level", invalid_unknown_relation_level_bytes());
    expect_policy_rejects("duplicate_level_name", invalid_duplicate_level_bytes());
    expect_policy_rejects("invalid_bottom", invalid_bottom_bytes());
    expect_policy_rejects("invalid_top", invalid_top_bytes());
    expect_policy_rejects("cycle_breaks_partial_order", invalid_cycle_bytes());
    expect_policy_rejects("missing_join_or_meet", invalid_missing_join_meet_bytes());

    println!("lattice tests passed");
}
