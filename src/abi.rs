//! Stage 1, facts: the contract's ABI from Foundry's build output
//! (`out/<File>.sol/<Contract>.json`). It lists every public function with
//! parameter names and types, inherited ones included, plus the constructor.

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::path::Path;

#[derive(Debug, Clone, Deserialize, PartialEq)]
pub struct Param {
    #[serde(default)]
    pub name: String,
    #[serde(rename = "type")]
    pub ty: String,
    #[serde(rename = "internalType", default)]
    pub internal_type: String,
}

impl Param {
    /// `Some("IERC20")` for a parameter declared with a contract or interface type.
    pub fn contract_type(&self) -> Option<&str> {
        self.internal_type.strip_prefix("contract ")
    }

    pub fn is_address(&self) -> bool {
        self.ty == "address"
    }

    /// Types the scaffold can fill with fuzzed values.
    pub fn is_supported(&self) -> bool {
        let t = self.ty.as_str();
        // Enums, structs and user-defined value types need casts the scaffold
        // does not write: their internal type differs from the ABI type.
        let plain = self.internal_type.is_empty()
            || self.internal_type == self.ty
            || self.internal_type == "address payable"
            || self.contract_type().is_some();
        let scalar = t == "address"
            || t == "bool"
            || (t.starts_with("uint") && !t.contains('['))
            || (t.starts_with("int") && !t.contains('['))
            || (t.starts_with("bytes") && t.len() > 5 && !t.contains('['));
        plain && scalar
    }

    /// Solidity spelling of the type, e.g. `uint256`, `address`, `IERC20`.
    pub fn solidity_type(&self) -> String {
        match self.contract_type() {
            Some(c) => c.to_string(),
            None => self.ty.clone(),
        }
    }
}

#[derive(Debug, Clone, Deserialize, PartialEq)]
pub struct Item {
    #[serde(rename = "type")]
    pub kind: String,
    #[serde(default)]
    pub name: String,
    #[serde(default)]
    pub inputs: Vec<Param>,
    #[serde(default)]
    pub outputs: Vec<Param>,
    #[serde(rename = "stateMutability", default)]
    pub mutability: String,
}

impl Item {
    pub fn is_function(&self) -> bool {
        self.kind == "function"
    }
    pub fn is_view(&self) -> bool {
        self.mutability == "view" || self.mutability == "pure"
    }
    /// `deposit(uint256 assets, address receiver) returns (uint256)`
    pub fn signature(&self) -> String {
        let list = |ps: &[Param]| {
            ps.iter()
                .map(|p| {
                    if p.name.is_empty() {
                        p.solidity_type()
                    } else {
                        format!("{} {}", p.solidity_type(), p.name)
                    }
                })
                .collect::<Vec<_>>()
                .join(", ")
        };
        let mut s = format!("{}({})", self.name, list(&self.inputs));
        if !self.outputs.is_empty() {
            s.push_str(&format!(" returns ({})", list(&self.outputs)));
        }
        s
    }
}

#[derive(Debug, Clone)]
pub struct Abi {
    pub items: Vec<Item>,
}

#[derive(Deserialize)]
struct Artifact {
    abi: Vec<Item>,
}

impl Abi {
    pub fn parse(json: &str) -> Result<Self> {
        let a: Artifact = serde_json::from_str(json).context("artifact has no readable `abi`")?;
        Ok(Self { items: a.abi })
    }

    /// Reads `out/<file_name>/<contract>.json` under the repo.
    pub fn load(repo: &Path, file_name: &str, contract: &str) -> Result<Self> {
        let path = repo
            .join("out")
            .join(file_name)
            .join(format!("{contract}.json"));
        let json = std::fs::read_to_string(&path).with_context(|| {
            format!(
                "reading {} (is the contract named after its file?)",
                path.display()
            )
        })?;
        Self::parse(&json)
    }

    pub fn constructor(&self) -> Vec<Param> {
        self.items
            .iter()
            .find(|i| i.kind == "constructor")
            .map(|i| i.inputs.clone())
            .unwrap_or_default()
    }

    /// Functions that change state: the handler calls these.
    pub fn mutating(&self) -> Vec<&Item> {
        self.items
            .iter()
            .filter(|i| i.is_function() && !i.is_view())
            .collect()
    }

    /// View and pure functions: what an assertion can read.
    pub fn views(&self) -> Vec<&Item> {
        self.items
            .iter()
            .filter(|i| i.is_function() && i.is_view())
            .collect()
    }

    pub fn has(&self, name: &str, inputs: &[&str]) -> bool {
        self.items.iter().any(|i| {
            i.is_function()
                && i.name == name
                && i.inputs.len() == inputs.len()
                && i.inputs.iter().zip(inputs).all(|(p, t)| p.ty == *t)
        })
    }
}

/// A uint256 state variable with a slot of its own, from the build's storage
/// layout (`--extra-output storageLayout`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Stored {
    pub label: String,
    pub slot: String,
}

#[derive(Deserialize)]
struct LayoutArtifact {
    #[serde(rename = "storageLayout", default)]
    storage_layout: Option<Layout>,
}

#[derive(Deserialize)]
struct Layout {
    #[serde(default)]
    storage: Vec<Var>,
}

#[derive(Deserialize)]
struct Var {
    label: String,
    slot: String,
    #[serde(default)]
    offset: u64,
    #[serde(rename = "type")]
    ty: String,
}

/// The contract's running totals: uint256 state variables named like
/// `_totalClaimableShares`, other than the token's own supply. Private ones
/// included: the proof reads them from storage. Empty without a layout.
pub fn stored_totals(json: &str) -> Vec<Stored> {
    let Ok(a) = serde_json::from_str::<LayoutArtifact>(json) else {
        return Vec::new();
    };
    let Some(layout) = a.storage_layout else {
        return Vec::new();
    };
    layout
        .storage
        .into_iter()
        .filter(|v| {
            let bare = v.label.trim_start_matches('_').to_ascii_lowercase();
            v.ty == "t_uint256"
                && v.offset == 0
                && bare.starts_with("total")
                && bare != "totalsupply"
        })
        .map(|v| Stored {
            label: v.label,
            slot: v.slot,
        })
        .collect()
}

/// `stored_totals` of `out/<file_name>/<contract>.json` under the repo.
pub fn load_stored_totals(repo: &Path, file_name: &str, contract: &str) -> Vec<Stored> {
    let path = repo
        .join("out")
        .join(file_name)
        .join(format!("{contract}.json"));
    std::fs::read_to_string(path)
        .map(|json| stored_totals(&json))
        .unwrap_or_default()
}

#[cfg(test)]
pub(crate) const OZ_VAULT_ABI: &str = r#"{"abi":[
 {"type":"constructor","inputs":[{"name":"asset_","type":"address","internalType":"contract IERC20"}],"stateMutability":"nonpayable"},
 {"type":"function","name":"approve","inputs":[{"name":"spender","type":"address","internalType":"address"},{"name":"value","type":"uint256","internalType":"uint256"}],"outputs":[{"name":"","type":"bool","internalType":"bool"}],"stateMutability":"nonpayable"},
 {"type":"function","name":"balanceOf","inputs":[{"name":"account","type":"address","internalType":"address"}],"outputs":[{"name":"","type":"uint256","internalType":"uint256"}],"stateMutability":"view"},
 {"type":"function","name":"convertToAssets","inputs":[{"name":"shares","type":"uint256","internalType":"uint256"}],"outputs":[{"name":"","type":"uint256","internalType":"uint256"}],"stateMutability":"view"},
 {"type":"function","name":"deposit","inputs":[{"name":"assets","type":"uint256","internalType":"uint256"},{"name":"receiver","type":"address","internalType":"address"}],"outputs":[{"name":"","type":"uint256","internalType":"uint256"}],"stateMutability":"nonpayable"},
 {"type":"function","name":"redeem","inputs":[{"name":"shares","type":"uint256","internalType":"uint256"},{"name":"receiver","type":"address","internalType":"address"},{"name":"owner","type":"address","internalType":"address"}],"outputs":[{"name":"","type":"uint256","internalType":"uint256"}],"stateMutability":"nonpayable"},
 {"type":"function","name":"totalAssets","inputs":[],"outputs":[{"name":"","type":"uint256","internalType":"uint256"}],"stateMutability":"view"},
 {"type":"function","name":"totalSupply","inputs":[],"outputs":[{"name":"","type":"uint256","internalType":"uint256"}],"stateMutability":"view"},
 {"type":"function","name":"permit","inputs":[{"name":"owner","type":"address","internalType":"address"},{"name":"spender","type":"address","internalType":"address"},{"name":"value","type":"uint256","internalType":"uint256"},{"name":"deadline","type":"uint256","internalType":"uint256"},{"name":"v","type":"uint8","internalType":"uint8"},{"name":"r","type":"bytes32","internalType":"bytes32"},{"name":"s","type":"bytes32","internalType":"bytes32"}],"outputs":[],"stateMutability":"nonpayable"},
 {"type":"function","name":"batch","inputs":[{"name":"amounts","type":"uint256[]","internalType":"uint256[]"}],"outputs":[],"stateMutability":"nonpayable"},
 {"type":"event","name":"Deposit","inputs":[],"anonymous":false}
]}"#;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn splits_constructor_mutating_and_view_functions() {
        let abi = Abi::parse(OZ_VAULT_ABI).unwrap();
        let ctor = abi.constructor();
        assert_eq!(ctor.len(), 1);
        assert_eq!(ctor[0].contract_type(), Some("IERC20"));
        let mutating: Vec<_> = abi.mutating().iter().map(|i| i.name.as_str()).collect();
        assert_eq!(
            mutating,
            ["approve", "deposit", "redeem", "permit", "batch"]
        );
        let views: Vec<_> = abi.views().iter().map(|i| i.name.as_str()).collect();
        assert_eq!(
            views,
            ["balanceOf", "convertToAssets", "totalAssets", "totalSupply"]
        );
    }

    #[test]
    fn writes_readable_signatures() {
        let abi = Abi::parse(OZ_VAULT_ABI).unwrap();
        let redeem = abi.items.iter().find(|i| i.name == "redeem").unwrap();
        assert_eq!(
            redeem.signature(),
            "redeem(uint256 shares, address receiver, address owner) returns (uint256)"
        );
    }

    #[test]
    fn finds_running_totals_in_the_storage_layout() {
        let json = r#"{"abi":[],"storageLayout":{"storage":[
          {"label":"_balances","slot":"0","offset":0,"type":"t_mapping(t_address,t_uint256)"},
          {"label":"_totalSupply","slot":"2","offset":0,"type":"t_uint256"},
          {"label":"_totalPendingRedeemShares","slot":"7","offset":0,"type":"t_uint256"},
          {"label":"totalFees","slot":"8","offset":0,"type":"t_uint128"},
          {"label":"_totalClaimableShares","slot":"10","offset":0,"type":"t_uint256"},
          {"label":"_owner","slot":"11","offset":0,"type":"t_address"}
        ]}}"#;
        let t = stored_totals(json);
        let labels: Vec<_> = t
            .iter()
            .map(|s| (s.label.as_str(), s.slot.as_str()))
            .collect();
        assert_eq!(
            labels,
            [
                ("_totalPendingRedeemShares", "7"),
                ("_totalClaimableShares", "10")
            ]
        );
        assert!(stored_totals(r#"{"abi":[]}"#).is_empty());
    }

    #[test]
    fn arrays_and_enums_are_not_supported() {
        let p = |ty: &str, it: &str| Param {
            name: "x".into(),
            ty: ty.into(),
            internal_type: it.into(),
        };
        assert!(p("uint256", "uint256").is_supported());
        assert!(p("bytes32", "bytes32").is_supported());
        assert!(!p("uint256[]", "uint256[]").is_supported());
        assert!(!p("uint8", "enum Vault.Mode").is_supported());
        assert!(!p("bytes", "bytes").is_supported());
        assert!(!p("string", "string").is_supported());
    }
}
