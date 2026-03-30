use deko_policy_format::encode_lattice_v1_blob;
use serde::Deserialize;

#[derive(Debug, Deserialize)]
struct RawPolicyConfigToml {
    lattice: RawLatticeConfigToml,
}

#[derive(Debug, Deserialize)]
struct RawLatticeConfigToml {
    levels: Vec<String>,
    relations: Vec<[String; 2]>,
    bot: String,
    top: String,
}

#[derive(Debug)]
pub enum PolicyCompileError {
    InvalidUtf8(std::str::Utf8Error),
    InvalidToml(toml::de::Error),
    UnknownLevel(String),
    EncodeFailed(String),
}

impl core::fmt::Display for PolicyCompileError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::InvalidUtf8(err) => write!(f, "invalid utf8 policy: {err}"),
            Self::InvalidToml(err) => write!(f, "invalid toml policy: {err}"),
            Self::UnknownLevel(level) => write!(f, "unknown lattice level: {level}"),
            Self::EncodeFailed(err) => write!(f, "failed to encode policy blob: {err}"),
        }
    }
}

impl std::error::Error for PolicyCompileError {}

fn find_level_index(levels: &[String], name: &str) -> Result<u32, PolicyCompileError> {
    levels
        .iter()
        .position(|level| level == name)
        .map(|idx| idx as u32)
        .ok_or_else(|| PolicyCompileError::UnknownLevel(name.to_string()))
}

pub fn compile_policy_toml_to_blob(policy_bytes: &[u8]) -> Result<Vec<u8>, PolicyCompileError> {
    let content = std::str::from_utf8(policy_bytes).map_err(PolicyCompileError::InvalidUtf8)?;
    let raw: RawPolicyConfigToml =
        toml::from_str(content).map_err(PolicyCompileError::InvalidToml)?;

    let levels: Vec<&[u8]> = raw.lattice.levels.iter().map(|level| level.as_bytes()).collect();

    let mut relations = Vec::with_capacity(raw.lattice.relations.len());
    for relation in &raw.lattice.relations {
        let lhs = find_level_index(&raw.lattice.levels, &relation[0])?;
        let rhs = find_level_index(&raw.lattice.levels, &relation[1])?;
        relations.push((lhs, rhs));
    }

    let bot_level_idx = find_level_index(&raw.lattice.levels, &raw.lattice.bot)?;
    let top_level_idx = find_level_index(&raw.lattice.levels, &raw.lattice.top)?;

    encode_lattice_v1_blob(&levels, &relations, bot_level_idx, top_level_idx)
        .map_err(|err| PolicyCompileError::EncodeFailed(format!("{err:?}")))
}
