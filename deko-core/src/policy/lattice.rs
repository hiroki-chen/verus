use core::fmt;

use deko_macros::DekoDebug;
use deko_std::fmt::DekoDebug;
use deko_std::std_extra::slice::{bytes_eq, bytes_eq_spec};
use deko_std::wf::WellFormed;
use vstd::prelude::*;

#[cfg(feature = "alloc")]
use crate::collections::update_vec;
#[cfg(feature = "alloc")]
use crate::collections::Vec;
use crate::kinfo;
#[cfg(feature = "alloc")]
use crate::mm::frame_allocator::DekoAllocatorApi;

verus! {

#[cfg(feature = "alloc")]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LatticeConfigToml {
    pub levels: Vec<Vec<u8>>,
    pub relations: Vec<(Vec<u8>, Vec<u8>)>,
    pub bot: Vec<u8>,
    pub top: Vec<u8>,
}

#[cfg(feature = "alloc")]
impl DekoDebug for LatticeConfigToml {
    #[verifier::external_body]
    fn deko_debug<W: deko_std::prelude::DekoWriter>(&self, writer: &W) {
        writer.write_str("LatticeConfigToml { levels: ");
        self.levels.deko_debug(writer);
        writer.write_str(", relations: ");
        self.relations.deko_debug(writer);
        writer.write_str(", bot: ");
        self.bot.deko_debug(writer);
        writer.write_str(", top: ");
        self.top.deko_debug(writer);
        writer.write_str(" }");
    }
}

#[cfg(feature = "alloc")]
impl WellFormed for LatticeConfigToml {
    /// States that the parser-produced lattice configuration is structurally
    /// well-formed as a collection of allocator-backed vectors.
    open spec fn wf(&self) -> bool {
        self.levels.wf() && self.relations.wf() && self.bot.wf() && self.top.wf()
    }
}

#[cfg(feature = "alloc")]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LevelId(pub usize);

impl WellFormed for LevelId {
    /// `LevelId` is just an index wrapper, so its standalone well-formedness is trivial.
    open spec fn wf(&self) -> bool {
        true
    }
}

#[cfg(feature = "alloc")]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteLattice {
    pub level_names: Vec<Vec<u8>>,
    pub bot: LevelId,
    pub top: LevelId,
    pub flows: Vec<Vec<bool>>,
}

#[cfg(feature = "alloc")]
#[derive(Clone, Debug, PartialEq, Eq, DekoDebug)]
pub enum FiniteLatticeBuildError {
    EmptyLevels,
    DuplicateLevelName(Vec<u8>),
    UnknownLevel(Vec<u8>),
    InvalidBottom(Vec<u8>),
    InvalidTop(Vec<u8>),
    NotPartialOrder { lhs: usize, rhs: usize },
    MissingBottomReachability { level: usize },
    MissingTopReachability { level: usize },
    MissingJoin { lhs: usize, rhs: usize },
    MissingMeet { lhs: usize, rhs: usize },
}

#[cfg(feature = "alloc")]
#[verus_verify]
impl FiniteLattice {
    /// Returns the number of levels carried by this finite lattice instance.
    ///
    /// This is the canonical size used by all index-based specifications.
    #[verifier::inline]
    pub open spec fn level_count(&self) -> usize {
        self.level_names@.len() as usize
    }

    /// Checks whether a concrete [`LevelId`] points at an in-bounds row/column
    /// of the lattice adjacency matrix.
    #[verifier::inline]
    pub open spec fn valid_level(&self, level: LevelId) -> bool {
        level.0 < self.level_count()
    }

    /// States that `flows` is a square `n x n` matrix whose dimension matches
    /// the number of declared level names.
    pub open spec fn square(&self) -> bool {
        &&& self.flows@.len() == self.level_count() as nat
        &&& forall|i: int|
            0 <= i < self.flows@.len() ==> #[trigger] self.flows@[i]@.len()
                == self.level_count() as nat
    }

    pub open spec fn flows_to_spec(&self, lhs: LevelId, rhs: LevelId) -> bool
        recommends
            self.square(),
            self.valid_level(lhs),
            self.valid_level(rhs),
    {
        self.flows@[lhs.0 as int]@[rhs.0 as int]
    }

    /// States that `ub` is an upper bound of `lhs` and `rhs`.
    pub open spec fn upper_bound(&self, lhs: LevelId, rhs: LevelId, ub: LevelId) -> bool
        recommends
            self.square(),
            self.valid_level(lhs),
            self.valid_level(rhs),
            self.valid_level(ub),
    {
        self.flows_to_spec(lhs, ub) && self.flows_to_spec(rhs, ub)
    }

    /// States that `lb` is a lower bound of `lhs` and `rhs`.
    pub open spec fn lower_bound(&self, lhs: LevelId, rhs: LevelId, lb: LevelId) -> bool
        recommends
            self.square(),
            self.valid_level(lhs),
            self.valid_level(rhs),
            self.valid_level(lb),
    {
        self.flows_to_spec(lb, lhs) && self.flows_to_spec(lb, rhs)
    }

    /// Characterizes the least upper bound of `lhs` and `rhs`.
    ///
    /// The candidate must first be an upper bound, and then be below every
    /// other upper bound.
    pub open spec fn is_join_of(&self, lhs: LevelId, rhs: LevelId, join: LevelId) -> bool
        recommends
            self.square(),
            self.valid_level(lhs),
            self.valid_level(rhs),
            self.valid_level(join),
    {
        &&& self.upper_bound(lhs, rhs, join)
        &&& forall|ub: LevelId|
            self.valid_level(ub) && #[trigger] self.upper_bound(lhs, rhs, ub)
                ==> self.flows_to_spec(join, ub)
    }

    /// Characterizes the greatest lower bound of `lhs` and `rhs`.
    pub open spec fn is_meet_of(&self, lhs: LevelId, rhs: LevelId, meet: LevelId) -> bool
        recommends
            self.square(),
            self.valid_level(lhs),
            self.valid_level(rhs),
            self.valid_level(meet),
    {
        &&& self.lower_bound(lhs, rhs, meet)
        &&& forall|lb: LevelId|
            self.valid_level(lb) && #[trigger] self.lower_bound(lhs, rhs, lb)
                ==> self.flows_to_spec(lb, meet)
    }

    /// States that a valid pair has both a join and a meet in this lattice.
    ///
    /// This is the compact existence predicate used by `wf()` and the runtime
    /// join/meet validation loop.
    pub open spec fn has_join_and_meet(&self, lhs: LevelId, rhs: LevelId) -> bool
        recommends
            self.square(),
            self.valid_level(lhs),
            self.valid_level(rhs),
    {
        exists|j: LevelId, m: LevelId|
            #![auto]
            self.valid_level(j) && self.valid_level(m) && self.is_join_of(lhs, rhs, j)
                && self.is_meet_of(lhs, rhs, m)
    }

    /// States that among the first `rel_count` declared relations in `cfg`,
    /// there is an edge from level index `src` to level index `dst`.
    pub open spec fn relation_declared_prefix(
        cfg: &LatticeConfigToml,
        rel_count: nat,
        src: int,
        dst: int,
    ) -> bool
        recommends
            0 <= src < cfg.levels@.len(),
            0 <= dst < cfg.levels@.len(),
            rel_count <= cfg.relations@.len(),
    {
        exists|rel: int|
            #![auto]
            0 <= rel < rel_count as int && bytes_eq_spec(cfg.relations@[rel].0@, cfg.levels@[src]@)
                && bytes_eq_spec(cfg.relations@[rel].1@, cfg.levels@[dst]@)
    }

    /// States that the full configuration declares an explicit edge from `src`
    /// to `dst`.
    pub open spec fn relation_declared(cfg: &LatticeConfigToml, src: int, dst: int) -> bool
        recommends
            0 <= src < cfg.levels@.len(),
            0 <= dst < cfg.levels@.len(),
    {
        Self::relation_declared_prefix(cfg, cfg.relations@.len(), src, dst)
    }

    /// The base relation induced by the configuration before transitive closure:
    /// all reflexive edges plus all user-declared edges.
    pub open spec fn config_base_edge(cfg: &LatticeConfigToml, src: int, dst: int) -> bool
        recommends
            0 <= src < cfg.levels@.len(),
            0 <= dst < cfg.levels@.len(),
    {
        src == dst || Self::relation_declared(cfg, src, dst)
    }

    /// The square adjacency matrix corresponding to the raw policy
    /// configuration before closure and order checks.
    pub open spec fn config_matrix(cfg: &LatticeConfigToml) -> Seq<Seq<bool>> {
        Seq::new(
            cfg.levels@.len(),
            |i: int| Seq::new(cfg.levels@.len(), |j: int| Self::config_base_edge(cfg, i, j)),
        )
    }

    /// States that this executable lattice value is exactly the lattice
    /// described by `cfg`, not merely some arbitrary well-formed lattice.
    ///
    /// Concretely, the lattice must have the same cardinality as `cfg`, the
    /// configured bottom/top names must resolve to the stored indices, and the
    /// final flow matrix must equal the transitive closure of the configuration
    /// base matrix.
    pub open spec fn realizes_config(&self, cfg: &LatticeConfigToml) -> bool {
        &&& self.square()
        &&& self.level_count() == cfg.levels@.len() as usize
        &&& self.valid_level(self.bot)
        &&& self.valid_level(self.top)
        &&& bytes_eq_spec(cfg.levels@[self.bot.0 as int]@, cfg.bot@)
        &&& bytes_eq_spec(cfg.levels@[self.top.0 as int]@, cfg.top@)
        &&& forall|i: int, j: int|
            0 <= i < self.flows@.len() && 0 <= j < self.flows@.len()
                ==> #[trigger] self.flows@[i]@[j] == Self::tc_prefix(
                Self::config_matrix(cfg),
                cfg.levels@.len(),
                i,
                j,
            )
    }

    /// Chooses whether to interpret `candidate` as an upper-bound witness or a
    /// lower-bound witness, so later proofs can share one abstraction.
    pub open spec fn bound_for(
        &self,
        lhs: LevelId,
        rhs: LevelId,
        candidate: LevelId,
        upper: bool,
    ) -> bool
        recommends
            self.square(),
            self.valid_level(lhs),
            self.valid_level(rhs),
            self.valid_level(candidate),
    {
        if upper {
            self.upper_bound(lhs, rhs, candidate)
        } else {
            self.lower_bound(lhs, rhs, candidate)
        }
    }

    /// Compiles a declarative finite-lattice description into the canonical
    /// adjacency-matrix representation, then checks that the result satisfies
    /// the bounded-lattice invariants before returning it.
    ///
    /// Typical usage is:
    /// 1. Build a [`LatticeConfigToml`] from parsed policy input.
    /// 2. Call [`FiniteLattice::compile`] to validate and materialize it.
    /// 3. Query the resulting lattice with [`FiniteLattice::flows_to`],
    ///    [`FiniteLattice::join`], and [`FiniteLattice::meet`].
    ///
    /// For example, a parser can deserialize policy bytes into
    /// [`crate::policy::config::PolicyConfigToml`], then pass `policy.lattice` here to obtain the
    /// finite lattice object used by later IFC checks.
    #[verus_spec(r =>
        ensures
            r matches Ok(lattice) ==> lattice.wf() && lattice.realizes_config(cfg),
    )]
    pub fn compile(cfg: &LatticeConfigToml) -> Result<Self, FiniteLatticeBuildError> {
        if cfg.levels.is_empty() {
            return Err(FiniteLatticeBuildError::EmptyLevels);
        }
        Self::validate_distinct_levels(cfg)?;
        proof {
            assert forall|i: int, j: int|
                #![auto]
                0 <= i < cfg.levels@.len() && 0 <= j < cfg.levels@.len() && i
                    != j implies cfg.levels@[i]@ != cfg.levels@[j]@ by {
                if 0 <= i < cfg.levels@.len() && 0 <= j < cfg.levels@.len() && i != j {
                    if i < j {
                        assert(cfg.levels@[i]@ != cfg.levels@[j]@);
                    } else {
                        assert(cfg.levels@[j]@ != cfg.levels@[i]@);
                    }
                }
            }
        }
        let (bot_idx, top_idx) = Self::resolve_bounds(cfg)?;
        let mut flows = Self::build_reflexive_flows(&cfg.levels);
        proof {
            assert(bot_idx < cfg.levels@.len());
            assert(top_idx < cfg.levels@.len());
            assert(flows@.len() == cfg.levels@.len());
        }
        Self::apply_relations(cfg, &mut flows)?;
        proof {
            assert forall|i: int| 0 <= i < flows@.len() implies #[trigger] Self::diag_cell(
                flows@,
                i,
            ) by {
                assert(flows@[i]@[i]);
                assert(Self::diag_cell(flows@, i));
            }
        }
        let ghost base = flows@;
        Self::close_and_validate_order(&mut flows)?;
        proof {
            assert(flows@.len() == cfg.levels@.len());
            assert(bot_idx < flows@.len());
            assert(top_idx < flows@.len());
            assert forall|i: int, j: int|
                0 <= i < flows@.len() && 0 <= j < flows@.len() implies #[trigger] flows@[i]@[j]
                == Self::tc_prefix(Self::config_matrix(cfg), cfg.levels@.len(), i, j) by {
                if 0 <= i < flows@.len() && 0 <= j < flows@.len() {
                    assert(base[i]@[j] == Self::config_matrix(cfg)[i][j]);
                    assert(Self::flow_matrix_view(base)[i][j] == Self::config_matrix(cfg)[i][j]);
                    Self::lemma_tc_prefix_extensional(
                        Self::flow_matrix_view(base),
                        Self::config_matrix(cfg),
                        cfg.levels@.len(),
                        i,
                        j,
                    );
                    assert(flows@[i]@[j] == Self::tc_prefix(
                        Self::flow_matrix_view(base),
                        cfg.levels@.len(),
                        i,
                        j,
                    ));
                }
            }
        }
        Self::validate_bounds(&flows, bot_idx, top_idx)?;
        Self::finish_lattice(cfg, bot_idx, top_idx, flows)
    }

    /// Checks that `cfg.levels` contains no duplicate level names.
    #[verus_spec(r =>
        ensures
            r is Ok ==> forall|i: int, j: int|
                #![auto]
                0 <= i < cfg.levels@.len() && i < j < cfg.levels@.len()
                    ==> cfg.levels@[i]@ != cfg.levels@[j]@,
    )]
    fn validate_distinct_levels(cfg: &LatticeConfigToml) -> Result<(), FiniteLatticeBuildError> {
        let n = cfg.levels.len();
        let mut i = 0;
        #[verus_spec(
            invariant
                n == cfg.levels@.len(),
                i <= n,
                forall|a: int, b: int|
                    #![auto]
                    0 <= a < i as int && a < b < n as int ==> cfg.levels@[a]@ != cfg.levels@[b]@,
            decreases n - i,
        )]
        while i < n {
            let mut j = i + 1;
            #[verus_spec(
                invariant
                    n == cfg.levels@.len(),
                    i < n,
                    i + 1 <= j <= n,
                    forall|b: int|
                        #![auto]
                        i < b < j as int ==> cfg.levels@[i as int]@ != cfg.levels@[b]@,
                    forall|a: int, b: int|
                        #![auto]
                        0 <= a < i as int && a < b < n as int ==> cfg.levels@[a]@
                            != cfg.levels@[b]@,
                decreases n - j,
            )]
            while j < n {
                if cfg.levels[i] == cfg.levels[j] {
                    return Err(FiniteLatticeBuildError::DuplicateLevelName(cfg.levels[i].clone()));
                }
                j += 1;
            }
            i += 1;
        }
        Ok(())
    }

    /// Resolves the configured `bot` and `top` names into concrete indices in
    /// `cfg.levels`.
    #[verus_spec(r =>
        ensures
            r matches Ok((bot_idx, top_idx)) ==> bot_idx < cfg.levels@.len() && top_idx < cfg.levels@.len()
                && bytes_eq_spec(cfg.levels@[bot_idx as int]@, cfg.bot@)
                && bytes_eq_spec(cfg.levels@[top_idx as int]@, cfg.top@),
    )]
    fn resolve_bounds(cfg: &LatticeConfigToml) -> Result<(usize, usize), FiniteLatticeBuildError> {
        let bot_idx = match Self::lookup_level(&cfg.levels, &cfg.bot) {
            Some(i) => i,
            None => return Err(FiniteLatticeBuildError::InvalidBottom(cfg.bot.clone())),
        };
        let top_idx = match Self::lookup_level(&cfg.levels, &cfg.top) {
            Some(i) => i,
            None => return Err(FiniteLatticeBuildError::InvalidTop(cfg.top.clone())),
        };
        Ok((bot_idx, top_idx))
    }

    /// Builds the initial reflexive adjacency matrix with no user-declared
    /// non-diagonal edges yet applied.
    #[verus_spec(r =>
        ensures
            r.wf(),
            r@.len() == levels@.len(),
            forall|i: int| 0 <= i < r@.len() ==> #[trigger] r@[i]@.len() == levels@.len(),
            forall|i: int, j: int|
                0 <= i < levels@.len() && 0 <= j < levels@.len() ==> #[trigger] r@[i]@[j] == (i == j),
    )]
    fn build_reflexive_flows(levels: &[Vec<u8>]) -> Vec<Vec<bool>> {
        let n = levels.len();
        let mut flows: Vec<Vec<bool>> = Vec::with_capacity_in(n, DekoAllocatorApi {  });
        let mut i = 0;
        #[verus_spec(
            invariant
                flows.wf(),
                flows@.len() == i,
                n == levels@.len(),
                i <= n,
                forall|r: int| 0 <= r < flows@.len() ==> #[trigger] flows@[r]@.len() == n,
                forall|r: int, c: int|
                    0 <= r < flows@.len() && 0 <= c < n as int ==> #[trigger] flows@[r]@[c] == (r
                        == c),
            decreases n - i,
        )]
        while i < n {
            let mut row: Vec<bool> = Vec::with_capacity_in(n, DekoAllocatorApi {  });
            let mut j = 0;
            #[verus_spec(
                invariant
                    row.wf(),
                    row@.len() == j,
                    j <= n,
                    forall|c: int| 0 <= c < j as int ==> #[trigger] row@[c] == (c == i as int),
                decreases n - j,
            )]
            while j < n {
                row.push(i == j);
                j += 1;
            }
            proof {
                assert(row@.len() == n);
            }
            flows.push(row);
            i += 1;
        }
        flows
    }

    /// Applies every explicitly declared relation from `cfg` into the mutable
    /// adjacency matrix.
    ///
    /// The postcondition is intentionally exact: on success the matrix equals
    /// the reflexive base graph induced by the configuration.
    #[verus_spec(r =>
        requires
            old(flows).wf(),
            old(flows)@.len() == cfg.levels@.len(),
            forall|i: int, j: int|
                #![auto]
                0 <= i < cfg.levels@.len() && 0 <= j < cfg.levels@.len() && i != j ==> cfg.levels@[i]@
                    != cfg.levels@[j]@,
            forall|i: int|
                0 <= i < old(flows)@.len()
                    ==> #[trigger] old(flows)@[i]@.len() == cfg.levels@.len(),
            forall|i: int, j: int|
                0 <= i < old(flows)@.len() && 0 <= j < old(flows)@.len() ==> #[trigger]
                    old(flows)@[i]@[j] == (i == j),
        ensures
            r is Ok ==> flows.wf(),
            r is Ok ==> flows@.len() == cfg.levels@.len(),
            r is Ok ==> forall|i: int| 0 <= i < flows@.len() ==> #[trigger] flows@[i]@.len() == cfg.levels@.len(),
            r is Ok ==> forall|i: int, j: int|
                0 <= i < flows@.len() && 0 <= j < flows@.len() ==> #[trigger] flows@[i]@[j]
                    == (i == j || Self::relation_declared_prefix(
                    cfg,
                    cfg.relations@.len(),
                    i,
                    j,
                )),
    )]
    fn apply_relations(cfg: &LatticeConfigToml, flows: &mut Vec<Vec<bool>>) -> Result<
        (),
        FiniteLatticeBuildError,
    > {
        let n = cfg.levels.len();
        proof {
            assert forall|r: int, c: int|
                0 <= r < n as int && 0 <= c < n as int implies #[trigger] flows@[r]@[c] == (r == c
                || Self::relation_declared_prefix(cfg, 0, r, c)) by {
                if 0 <= r < n as int && 0 <= c < n as int {
                    assert(flows@[r]@[c] == (r == c));
                    Self::lemma_relation_declared_prefix_zero(cfg, r, c);
                }
            }
        }
        let mut rel = 0;
        #[verus_spec(
            invariant
                flows.wf(),
                n == cfg.levels@.len(),
                flows@.len() == n,
                rel <= cfg.relations@.len(),
                forall|a: int, b: int|
                    #![auto]
                    0 <= a < cfg.levels@.len() && 0 <= b < cfg.levels@.len() && a != b
                        ==> cfg.levels@[a]@ != cfg.levels@[b]@,
                forall|r: int| 0 <= r < flows@.len() ==> #[trigger] flows@[r]@.len() == n,
                forall|r: int, c: int|
                    0 <= r < n as int && 0 <= c < n as int ==> #[trigger] flows@[r]@[c] == (r == c
                        || Self::relation_declared_prefix(cfg, rel as nat, r, c)),
            decreases cfg.relations.len() - rel,
        )]
        while rel < cfg.relations.len() {
            let (lhs_name, rhs_name) = &cfg.relations[rel];
            let lhs = match Self::lookup_level(&cfg.levels, lhs_name) {
                Some(i) => i,
                None => return Err(FiniteLatticeBuildError::UnknownLevel(lhs_name.clone())),
            };
            let rhs = match Self::lookup_level(&cfg.levels, rhs_name) {
                Some(i) => i,
                None => return Err(FiniteLatticeBuildError::UnknownLevel(rhs_name.clone())),
            };
            let ghost prev = flows@;
            let mut row = flows.remove(lhs);
            update_vec(&mut row, rhs, true);
            proof {
                assert(row@.len() == n);
                assert(row@[lhs as int]);
                assert(bytes_eq_spec(cfg.relations@[rel as int].0@, cfg.levels@[lhs as int]@));
                assert(bytes_eq_spec(cfg.relations@[rel as int].1@, cfg.levels@[rhs as int]@));
            }
            flows.insert(lhs, row);
            proof {
                assert forall|r: int, c: int|
                    0 <= r < n as int && 0 <= c < n as int implies #[trigger] flows@[r]@[c] == (r
                    == c || Self::relation_declared_prefix(cfg, (rel + 1) as nat, r, c)) by {
                    if 0 <= r < n as int && 0 <= c < n as int {
                        Self::lemma_relation_declared_prefix_step(cfg, rel as nat, r, c);
                        if r == lhs as int {
                            if c == rhs as int {
                                assert(bytes_eq_spec(
                                    cfg.relations@[rel as int].0@,
                                    cfg.levels@[r]@,
                                ));
                                assert(bytes_eq_spec(
                                    cfg.relations@[rel as int].1@,
                                    cfg.levels@[c]@,
                                ));
                                assert(flows@[r]@[c]);
                            } else {
                                assert(flows@[r]@[c] == prev[r]@[c]);
                                if bytes_eq_spec(cfg.relations@[rel as int].1@, cfg.levels@[c]@) {
                                    assert(bytes_eq_spec(
                                        cfg.relations@[rel as int].1@,
                                        cfg.levels@[rhs as int]@,
                                    ));
                                    Self::lemma_unique_level_name(
                                        cfg,
                                        rhs as int,
                                        c,
                                        cfg.relations@[rel as int].1@,
                                    );
                                }
                            }
                        } else {
                            assert(flows@[r]@[c] == prev[r]@[c]);
                            if bytes_eq_spec(cfg.relations@[rel as int].0@, cfg.levels@[r]@) {
                                assert(bytes_eq_spec(
                                    cfg.relations@[rel as int].0@,
                                    cfg.levels@[lhs as int]@,
                                ));
                                Self::lemma_unique_level_name(
                                    cfg,
                                    lhs as int,
                                    r,
                                    cfg.relations@[rel as int].0@,
                                );
                            }
                        }
                    }
                }
            }
            rel += 1;
        }
        Ok(())
    }

    /// Closes the base relation transitively and rejects antisymmetry
    /// violations, turning the matrix into a verified partial order.
    #[verus_spec(r =>
        requires
            old(flows).wf(),
            forall|i: int|
                0 <= i < old(flows)@.len() ==> #[trigger] old(flows)@[i]@.len()
                    == old(flows)@.len(),
            forall|i: int| 0 <= i < old(flows)@.len() ==> #[trigger] Self::diag_cell(old(flows)@, i),
        ensures
            r is Ok ==> flows.wf(),
            r is Ok ==> flows@.len() == old(flows)@.len(),
            r is Ok ==> forall|i: int| 0 <= i < flows@.len() ==> #[trigger] flows@[i]@.len() == flows@.len(),
            r is Ok ==> forall|i: int, j: int|
                0 <= i < flows@.len() && 0 <= j < flows@.len() ==> #[trigger] flows@[i]@[j]
                    == Self::tc_prefix(
                    Self::flow_matrix_view(old(flows)@),
                    old(flows)@.len(),
                    i,
                    j,
                ),
            r is Ok ==> forall|i: int| #![auto] 0 <= i < flows@.len() ==> flows@[i]@[i],
            r is Ok ==> forall|a: int, b: int|
                #![auto]
                0 <= a < flows@.len() && 0 <= b < flows@.len() && a != b ==> !(flows@[a][b] && flows@[b][a]),
            r is Ok ==> forall|a: int, b: int, c: int|
                #![auto]
                0 <= a < flows@.len() && 0 <= b < flows@.len() && 0 <= c < flows@.len()
                    && flows@[a][b] && flows@[b][c] ==> flows@[a][c],
    )]
    fn close_and_validate_order(flows: &mut Vec<Vec<bool>>) -> Result<(), FiniteLatticeBuildError> {
        let ghost pre = flows@;
        Self::transitive_closure(flows);
        let n = flows.len();
        let mut i = 0;
        #[verus_spec(
            invariant
                flows.wf(),
                flows@.len() == n,
                i <= n,
                forall|r: int| 0 <= r < flows@.len() ==> #[trigger] flows@[r]@.len() == n,
                forall|a: int, b: int|
                    #![auto]
                    0 <= a < i as int && 0 <= b < n as int && a != b ==> !(flows@[a][b]
                        && flows@[b][a]),
            decreases n - i,
        )]
        while i < n {
            let mut j = 0;
            #[verus_spec(
                invariant
                    flows.wf(),
                    flows@.len() == n,
                    i < n,
                    j <= n,
                    forall|r: int| 0 <= r < flows@.len() ==> #[trigger] flows@[r]@.len() == n,
                    forall|a: int, b: int|
                        #![auto]
                        0 <= a < i as int && 0 <= b < n as int && a != b ==> !(flows@[a][b]
                            && flows@[b][a]),
                    forall|b: int|
                        #![auto]
                        0 <= b < j as int && i as int != b ==> !(flows@[i as int][b]
                            && flows@[b][i as int]),
                decreases n - j,
            )]
            while j < n {
                if i != j && flows[i][j] && flows[j][i] {
                    return Err(FiniteLatticeBuildError::NotPartialOrder { lhs: i, rhs: j });
                }
                j += 1;
            }
            i += 1;
        }
        proof {
            assert forall|i: int| #![auto] 0 <= i < flows@.len() implies flows@[i]@[i] by {
                assert(Self::diag_cell(pre, i));
                assert(Self::flow_matrix_view(pre)[i][i]);
                assert(flows@[i]@[i]);
            }
        }
        Ok(())
    }

    /// Checks the bounded-lattice side conditions that every level is above
    /// `bot` and below `top`.
    #[verus_spec(r =>
        requires
            flows.wf(),
            bot_idx < flows@.len(),
            top_idx < flows@.len(),
            forall|i: int| 0 <= i < flows@.len() ==> #[trigger] flows@[i]@.len() == flows@.len(),
        ensures
            r is Ok ==> forall|i: int| 0 <= i < flows@.len() ==> #[trigger] flows@[bot_idx as int][i],
            r is Ok ==> forall|i: int| 0 <= i < flows@.len() ==> #[trigger] flows@[i][top_idx as int],
    )]
    fn validate_bounds(flows: &Vec<Vec<bool>>, bot_idx: usize, top_idx: usize) -> Result<
        (),
        FiniteLatticeBuildError,
    > {
        let n = flows.len();
        let mut i = 0;
        #[verus_spec(
            invariant
                flows.wf(),
                flows@.len() == n,
                i <= n,
                bot_idx < n,
                top_idx < n,
                forall|r: int| 0 <= r < flows@.len() ==> #[trigger] flows@[r]@.len() == n,
                forall|a: int| 0 <= a < i as int ==> #[trigger] flows@[bot_idx as int][a],
                forall|a: int| 0 <= a < i as int ==> #[trigger] flows@[a][top_idx as int],
            decreases n - i,
        )]
        while i < n {
            if !flows[bot_idx][i] {
                return Err(FiniteLatticeBuildError::MissingBottomReachability { level: i });
            }
            if !flows[i][top_idx] {
                return Err(FiniteLatticeBuildError::MissingTopReachability { level: i });
            }
            i += 1;
        }
        proof {
            assert forall|i: int|
                #![auto]
                0 <= i < flows@.len() implies flows@[bot_idx as int][i] by {
                assert(flows@[bot_idx as int][i]);
            }
            assert forall|i: int|
                #![auto]
                0 <= i < flows@.len() implies flows@[i][top_idx as int] by {
                assert(flows@[i][top_idx as int]);
            }
        }
        Ok(())
    }

    /// Consumes the verified matrix and packages it into the final
    /// [`FiniteLattice`] value, then validates join/meet existence.
    #[verus_spec(r =>
        requires
            flows.wf(),
            flows@.len() == cfg.levels@.len(),
            bot_idx < cfg.levels@.len(),
            top_idx < cfg.levels@.len(),
            bytes_eq_spec(cfg.levels@[bot_idx as int]@, cfg.bot@),
            bytes_eq_spec(cfg.levels@[top_idx as int]@, cfg.top@),
            forall|i: int| 0 <= i < flows@.len() ==> #[trigger] flows@[i]@.len() == cfg.levels@.len(),
            forall|i: int, j: int|
                0 <= i < flows@.len() && 0 <= j < flows@.len() ==> #[trigger] flows@[i]@[j]
                    == Self::tc_prefix(
                    Self::config_matrix(cfg),
                    cfg.levels@.len(),
                    i,
                    j,
                ),
            forall|l: LevelId| l.0 < flows@.len() ==> #[trigger] flows@[l.0 as int][l.0 as int],
            forall|l1: LevelId, l2: LevelId|
                l1.0 < flows@.len() && l2.0 < flows@.len() && flows@[l1.0 as int][l2.0 as int]
                    && flows@[l2.0 as int][l1.0 as int] ==> l1 == l2,
            forall|l1: LevelId, l2: LevelId, l3: LevelId|
                #![auto]
                l1.0 < flows@.len() && l2.0 < flows@.len() && l3.0 < flows@.len()
                    && flows@[l1.0 as int][l2.0 as int] && flows@[l2.0 as int][l3.0 as int]
                    ==> flows@[l1.0 as int][l3.0 as int],
            forall|i: int| 0 <= i < flows@.len() ==> #[trigger] flows@[bot_idx as int][i],
            forall|i: int| 0 <= i < flows@.len() ==> #[trigger] flows@[i][top_idx as int],
        ensures
            r matches Ok(lattice) ==> lattice.wf() && lattice.realizes_config(cfg),
    )]
    fn finish_lattice(
        cfg: &LatticeConfigToml,
        bot_idx: usize,
        top_idx: usize,
        flows: Vec<Vec<bool>>,
    ) -> Result<Self, FiniteLatticeBuildError> {
        let n = cfg.levels.len();
        let lattice = Self {
            level_names: cfg.levels.clone(),
            bot: LevelId(bot_idx),
            top: LevelId(top_idx),
            flows,
        };

        lattice.validate_joins_and_meets()?;
        proof {
            assert(lattice.square());
            assert(lattice.level_count() == n);
            assert(lattice.valid_level(lattice.bot));
            assert(lattice.valid_level(lattice.top));
            assert forall|i: int, j: int|
                0 <= i < lattice.flows@.len() && 0 <= j
                    < lattice.flows@.len() implies #[trigger] lattice.flows@[i]@[j]
                == Self::tc_prefix(Self::config_matrix(cfg), cfg.levels@.len(), i, j) by {
                if 0 <= i < lattice.flows@.len() && 0 <= j < lattice.flows@.len() {
                    assert(lattice.flows@[i]@[j] == Self::tc_prefix(
                        Self::config_matrix(cfg),
                        cfg.levels@.len(),
                        i,
                        j,
                    ));
                }
            }
            assert forall|l1: LevelId, l2: LevelId|
                #![auto]
                lattice.valid_level(l1) && lattice.valid_level(
                    l2,
                ) implies lattice.has_join_and_meet(l1, l2) by {}
            assert forall|l: LevelId|
                lattice.valid_level(l) implies #[trigger] lattice.flows_to_spec(l, l) by {
                let idx = l.0;
                assert(idx < n);
                assert(lattice.flows@[idx as int][idx as int]);
            }
            assert forall|l1: LevelId, l2: LevelId|
                lattice.valid_level(l1) && lattice.valid_level(l2) && lattice.flows_to_spec(l1, l2)
                    && lattice.flows_to_spec(l2, l1) implies l1 == l2 by {
                let a = l1.0 as int;
                let b = l2.0 as int;
                assert(0 <= a < n as int);
                assert(0 <= b < n as int);
                if l1 != l2 {
                    assert(a != b);
                    assert(!(lattice.flows@[a][b] && lattice.flows@[b][a]));
                }
            }
            assert forall|l1: LevelId, l2: LevelId, l3: LevelId|
                #![auto]
                lattice.valid_level(l1) && lattice.valid_level(l2) && lattice.valid_level(l3)
                    && lattice.flows_to_spec(l1, l2) && lattice.flows_to_spec(
                    l2,
                    l3,
                ) implies lattice.flows_to_spec(l1, l3) by {
                let a = l1.0 as int;
                let b = l2.0 as int;
                let c = l3.0 as int;
                assert(0 <= a < n as int);
                assert(0 <= b < n as int);
                assert(0 <= c < n as int);
                assert(lattice.flows@[a][c]);
            }
            assert forall|l: LevelId| #![auto] lattice.valid_level(l) implies lattice.flows_to_spec(
                lattice.bot,
                l,
            ) by {
                let idx = l.0;
                assert(idx < n);
                assert(lattice.flows@[bot_idx as int][idx as int]);
            }
            assert forall|l: LevelId| #![auto] lattice.valid_level(l) implies lattice.flows_to_spec(
                l,
                lattice.top,
            ) by {
                let idx = l.0;
                assert(idx < n);
                assert(top_idx < n);
                assert(lattice.flows@[idx as int][top_idx as int]);
            }
            assert(bytes_eq_spec(cfg.levels@[bot_idx as int]@, cfg.bot@));
            assert(bytes_eq_spec(cfg.levels@[top_idx as int]@, cfg.top@));
            lemma_wf_from_components(lattice);
            assert(lattice.realizes_config(cfg));
        }
        Ok(lattice)
    }

    /// Executes the pure `flows_to_spec` relation against the runtime matrix.
    #[verifier::when_used_as_spec(flows_to_spec)]
    #[verus_spec(r =>
        requires
            self.square(),
            self.valid_level(lhs),
            self.valid_level(rhs),
        ensures
            r == self.flows_to_spec(lhs, rhs),
    )]
    pub fn flows_to(&self, lhs: LevelId, rhs: LevelId) -> bool {
        self.flows[lhs.0][rhs.0]
    }

    /// Searches for the least upper bound of `lhs` and `rhs` in the finite
    /// representation, if one is present.
    #[verus_spec(r =>
        requires
            self.square(),
            self.valid_level(lhs),
            self.valid_level(rhs),
        ensures
            r matches Some(level) ==> self.valid_level(level) && self.is_join_of(lhs, rhs, level),
    )]
    pub fn join(&self, lhs: LevelId, rhs: LevelId) -> Option<LevelId> {
        match self.unique_best_bound(lhs, rhs, true) {
            Some(i) => {
                let level = LevelId(i);
                proof {
                    assert(self.valid_level(level));
                }
                Some(level)
            },
            None => None,
        }
    }

    /// Searches for the greatest lower bound of `lhs` and `rhs` in the finite
    /// representation, if one is present.
    #[verus_spec(r =>
        requires
            self.square(),
            self.valid_level(lhs),
            self.valid_level(rhs),
        ensures
            r matches Some(level) ==> self.valid_level(level) && self.is_meet_of(lhs, rhs, level),
    )]
    pub fn meet(&self, lhs: LevelId, rhs: LevelId) -> Option<LevelId> {
        match self.unique_best_bound(lhs, rhs, false) {
            Some(i) => {
                let level = LevelId(i);
                proof {
                    assert(self.valid_level(level));
                }
                Some(level)
            },
            None => None,
        }
    }

    /// Looks up a level name in `levels` and returns its unique index if found.
    #[verus_spec(r =>
        ensures
            r matches Some(i) ==> i < levels@.len() && bytes_eq_spec(levels@[i as int]@, name@),
            r is None ==> forall|i: int|
                #![auto]
                0 <= i < levels@.len() ==> !bytes_eq_spec(levels@[i]@, name@),
    )]
    fn lookup_level(levels: &[Vec<u8>], name: &[u8]) -> Option<usize> {
        let mut i = 0;
        #[verus_spec(
            invariant
                0 <= i <= levels.len(),
                forall|j: int|
                    #![auto]
                    0 <= j < i as int ==> !bytes_eq_spec(levels@[j]@, name@),
            decreases levels.len() - i,
        )]
        while i < levels.len() {
            if bytes_eq(levels[i].as_slice(), name) {
                proof {
                    assert(bytes_eq_spec(levels@[i as int]@, name@));
                }
                return Some(i);
            }
            i += 1;
        }
        None
    }

    /// Warshall-style reachability predicate.
    ///
    /// `tc_prefix(matrix, k, i, j)` means that `j` is reachable from `i` after
    /// allowing only the first `k` nodes as intermediate pivots.
    pub open spec fn tc_prefix(matrix: Seq<Seq<bool>>, k: nat, i: int, j: int) -> bool
        decreases k,
    {
        if k == 0 {
            matrix[i][j]
        } else {
            let pivot = (k - 1) as int;
            ||| Self::tc_prefix(matrix, (k - 1) as nat, i, j)
            ||| (Self::tc_prefix(matrix, (k - 1) as nat, i, pivot) && Self::tc_prefix(
                matrix,
                (k - 1) as nat,
                pivot,
                j,
            ))
        }
    }

    /// Converts the executable `Vec<Vec<bool>>` representation into the pure
    /// `Seq<Seq<bool>>` matrix used in specifications and proofs.
    #[verifier::inline]
    pub open spec fn flow_matrix_view(flows: Seq<Vec<bool>>) -> Seq<Seq<bool>> {
        flows.map_values(|row: Vec<bool>| row@)
    }

    /// Convenience accessor for a diagonal cell in the proof-level matrix view.
    pub closed spec fn diag_cell(flows: Seq<Vec<bool>>, i: int) -> bool
        recommends
            0 <= i < flows.len(),
            i < flows[i]@.len(),
    {
        Self::flow_matrix_view(flows)[i][i]
    }

    /// Bridges one executable cell access with the corresponding pure matrix
    /// cell in [`flow_matrix_view`].
    proof fn lemma_flow_matrix_view_cell(flows: Seq<Vec<bool>>, i: int, j: int)
        requires
            0 <= i < flows.len(),
            0 <= j < flows[i]@.len(),
        ensures
            Self::flow_matrix_view(flows)[i][j] == flows[i]@[j],
    {
    }

    /// Shows that no declared edge exists when we inspect an empty prefix of
    /// the relation list.
    proof fn lemma_relation_declared_prefix_zero(cfg: &LatticeConfigToml, src: int, dst: int)
        requires
            0 <= src < cfg.levels@.len(),
            0 <= dst < cfg.levels@.len(),
        ensures
            !Self::relation_declared_prefix(cfg, 0, src, dst),
    {
    }

    /// Lifts pointwise equality of two base matrices into equality of their
    /// `tc_prefix` closures at any fixed pivot depth.
    proof fn lemma_tc_prefix_extensional(
        matrix1: Seq<Seq<bool>>,
        matrix2: Seq<Seq<bool>>,
        k: nat,
        i: int,
        j: int,
    )
        requires
            0 <= i < matrix1.len(),
            0 <= j < matrix1.len(),
            k <= matrix1.len(),
            matrix1.len() == matrix2.len(),
            forall|r: int| #![auto] 0 <= r < matrix1.len() ==> matrix1[r].len() == matrix1.len(),
            forall|r: int| #![auto] 0 <= r < matrix2.len() ==> matrix2[r].len() == matrix2.len(),
            forall|r: int, c: int|
                0 <= r < matrix1.len() && 0 <= c < matrix1.len() ==> matrix1[r][c] == matrix2[r][c],
        ensures
            Self::tc_prefix(matrix1, k, i, j) == Self::tc_prefix(matrix2, k, i, j),
        decreases k,
    {
        if k > 0 {
            let pivot = (k - 1) as int;
            Self::lemma_tc_prefix_extensional(matrix1, matrix2, (k - 1) as nat, i, j);
            Self::lemma_tc_prefix_extensional(matrix1, matrix2, (k - 1) as nat, i, pivot);
            Self::lemma_tc_prefix_extensional(matrix1, matrix2, (k - 1) as nat, pivot, j);
        }
    }

    /// Unrolls one step of `relation_declared_prefix`, separating the previous
    /// prefix from the newly added declared edge.
    proof fn lemma_relation_declared_prefix_step(
        cfg: &LatticeConfigToml,
        rel_count: nat,
        src: int,
        dst: int,
    )
        requires
            0 <= src < cfg.levels@.len(),
            0 <= dst < cfg.levels@.len(),
            rel_count < cfg.relations@.len(),
        ensures
            Self::relation_declared_prefix(cfg, (rel_count + 1) as nat, src, dst) == (
            Self::relation_declared_prefix(cfg, rel_count, src, dst) || (bytes_eq_spec(
                cfg.relations@[rel_count as int].0@,
                cfg.levels@[src]@,
            ) && bytes_eq_spec(cfg.relations@[rel_count as int].1@, cfg.levels@[dst]@))),
    {
    }

    /// Uses global uniqueness of level names to show that two indices carrying
    /// the same name must in fact be the same index.
    proof fn lemma_unique_level_name(cfg: &LatticeConfigToml, i: int, j: int, name: Seq<u8>)
        requires
            forall|a: int, b: int|
                #![auto]
                0 <= a < cfg.levels@.len() && 0 <= b < cfg.levels@.len() && a != b
                    ==> cfg.levels@[a]@ != cfg.levels@[b]@,
            0 <= i < cfg.levels@.len(),
            0 <= j < cfg.levels@.len(),
            bytes_eq_spec(cfg.levels@[i]@, name),
            bytes_eq_spec(cfg.levels@[j]@, name),
        ensures
            i == j,
    {
        if i != j {
            if i < j {
                assert(cfg.levels@[i]@ != cfg.levels@[j]@);
            } else {
                assert(cfg.levels@[j]@ != cfg.levels@[i]@);
            }
            assert(cfg.levels@[i]@ == name);
            assert(cfg.levels@[j]@ == name);
        }
    }

    /// Helper predicate for the middle-loop invariants in transitive closure:
    /// it describes cells that are still in the untouched suffix of later rows.
    pub open spec fn row_suffix_cell(cur_row: int, n: nat, r: int, c: int) -> bool {
        cur_row < r && r < n as int && 0 <= c && c < n as int
    }

    /// Shows that adding more pivots to Warshall closure never removes an
    /// already-present base edge.
    proof fn lemma_tc_prefix_contains_base(matrix: Seq<Seq<bool>>, k: nat, i: int, j: int)
        requires
            0 <= i < matrix.len(),
            0 <= j < matrix.len(),
            forall|r: int| #![auto] 0 <= r < matrix.len() ==> matrix[r].len() == matrix.len(),
            matrix[i][j],
        ensures
            Self::tc_prefix(matrix, k, i, j),
        decreases k,
    {
        if k > 0 {
            Self::lemma_tc_prefix_contains_base(matrix, (k - 1) as nat, i, j);
        }
    }

    /// Reaching the current pivot does not itself require using that pivot as
    /// an intermediate node.
    proof fn lemma_tc_prefix_pivot_col(matrix: Seq<Seq<bool>>, k: nat, i: int)
        requires
            0 <= i < matrix.len(),
            k < matrix.len(),
            forall|r: int| #![auto] 0 <= r < matrix.len() ==> matrix[r].len() == matrix.len(),
        ensures
            Self::tc_prefix(matrix, (k + 1) as nat, i, k as int) == Self::tc_prefix(
                matrix,
                k,
                i,
                k as int,
            ),
    {
    }

    /// Dual to [`lemma_tc_prefix_pivot_col`]: leaving the pivot also does not
    /// require recursively reusing that same pivot.
    proof fn lemma_tc_prefix_pivot_row(matrix: Seq<Seq<bool>>, k: nat, j: int)
        requires
            0 <= j < matrix.len(),
            k < matrix.len(),
            forall|r: int| #![auto] 0 <= r < matrix.len() ==> matrix[r].len() == matrix.len(),
        ensures
            Self::tc_prefix(matrix, (k + 1) as nat, k as int, j) == Self::tc_prefix(
                matrix,
                k,
                k as int,
                j,
            ),
    {
    }

    /// Expands one Warshall iteration into the familiar
    /// `old || (to_pivot && from_pivot)` recurrence.
    proof fn lemma_tc_prefix_step(matrix: Seq<Seq<bool>>, k: nat, i: int, j: int)
        requires
            0 <= i < matrix.len(),
            0 <= j < matrix.len(),
            k < matrix.len(),
            forall|r: int| #![auto] 0 <= r < matrix.len() ==> matrix[r].len() == matrix.len(),
        ensures
            Self::tc_prefix(matrix, (k + 1) as nat, i, j) == (Self::tc_prefix(matrix, k, i, j) || (
            Self::tc_prefix(matrix, k, i, k as int) && Self::tc_prefix(matrix, k, k as int, j))),
    {
    }

    /// Shows that once pivot `p` is already admitted among the first `k`
    /// pivots, `tc_prefix(k)` is closed under composing paths through `p`.
    ///
    /// This is the key bridge from the Warshall algorithm to the transitivity
    /// postcondition of `transitive_closure`.
    #[verifier::spinoff_prover]
    proof fn lemma_tc_prefix_closed_under_pivot(
        matrix: Seq<Seq<bool>>,
        k: nat,
        p: int,
        i: int,
        j: int,
    )
        requires
            0 <= i < matrix.len(),
            0 <= j < matrix.len(),
            0 <= p < k,
            k <= matrix.len(),
            forall|r: int| #![auto] 0 <= r < matrix.len() ==> matrix[r].len() == matrix.len(),
            Self::tc_prefix(matrix, k, i, p),
            Self::tc_prefix(matrix, k, p, j),
        ensures
            Self::tc_prefix(matrix, k, i, j),
        decreases k,
    {
        let last = (k - 1) as int;
        if p == last {
            Self::lemma_tc_prefix_pivot_col(matrix, (k - 1) as nat, i);
            Self::lemma_tc_prefix_pivot_row(matrix, (k - 1) as nat, j);
            Self::lemma_tc_prefix_step(matrix, (k - 1) as nat, i, j);
        } else {
            Self::lemma_tc_prefix_step(matrix, (k - 1) as nat, i, p);
            Self::lemma_tc_prefix_step(matrix, (k - 1) as nat, p, j);
            Self::lemma_tc_prefix_step(matrix, (k - 1) as nat, i, j);
            Self::lemma_tc_prefix_step(matrix, (k - 1) as nat, i, last);
            Self::lemma_tc_prefix_step(matrix, (k - 1) as nat, last, j);
            if Self::tc_prefix(matrix, (k - 1) as nat, i, p) {
                if Self::tc_prefix(matrix, (k - 1) as nat, p, j) {
                    Self::lemma_tc_prefix_closed_under_pivot(matrix, (k - 1) as nat, p, i, j);
                } else {
                    assert(Self::tc_prefix(matrix, (k - 1) as nat, p, last));
                    assert(Self::tc_prefix(matrix, (k - 1) as nat, last, j));
                    Self::lemma_tc_prefix_closed_under_pivot(matrix, (k - 1) as nat, p, i, last);
                }
            } else {
                assert(Self::tc_prefix(matrix, (k - 1) as nat, i, last));
                assert(Self::tc_prefix(matrix, (k - 1) as nat, last, p));
                if Self::tc_prefix(matrix, (k - 1) as nat, p, j) {
                    Self::lemma_tc_prefix_closed_under_pivot(matrix, (k - 1) as nat, p, last, j);
                } else {
                    assert(Self::tc_prefix(matrix, (k - 1) as nat, p, last));
                    assert(Self::tc_prefix(matrix, (k - 1) as nat, last, j));
                }
            }
        }
    }

    /// Runs in-place Floyd-Warshall over the adjacency matrix.
    ///
    /// On return, every original edge is preserved and the resulting matrix is
    /// transitively closed.
    #[verus_spec(r =>
        requires
            old(flows).wf(),
            forall|i: int| 0 <= i < old(flows)@.len() ==> #[trigger] old(flows)@[i]@.len()
                == old(flows)@.len(),
        ensures
            flows.wf(),
            flows@.len() == old(flows)@.len(),
            forall|i: int| 0 <= i < flows@.len() ==> #[trigger] flows@[i]@.len() == flows@.len(),
            forall|i: int, j: int|
                0 <= i < flows@.len() && 0 <= j < flows@.len() ==> #[trigger] flows@[i]@[j]
                    == Self::tc_prefix(
                    Self::flow_matrix_view(old(flows)@),
                    old(flows)@.len(),
                    i,
                    j,
                ),
            forall|i: int, j: int|
                0 <= i < flows@.len() && 0 <= j < flows@.len()
                    && Self::flow_matrix_view(old(flows)@)[i][j]
                    ==> flows@[i]@[j],
            forall|i: int, j: int, k: int|
                #![auto]
                0 <= i < flows@.len() && 0 <= j < flows@.len() && 0 <= k < flows@.len()
                    && flows@[i]@[j] && flows@[j]@[k] ==> flows@[i]@[k],
    )]
    #[verifier::spinoff_prover]
    fn transitive_closure(flows: &mut Vec<Vec<bool>>) {
        broadcast use vstd::std_specs::vec::group_vec_axioms;

        let n = flows.len();
        let ghost base = Self::flow_matrix_view(flows@);
        let mut k = 0;
        // Outer loop: after iteration `k`, `flows` matches `tc_prefix(base, k, .., ..)`.
        #[verus_spec(
            invariant
                flows.wf(),
                n == flows@.len(),
                k <= n,
                forall|r: int|
                    0 <= r < flows@.len() ==> #[trigger] flows@[r]@.len() == flows@.len(),
                forall|i: int, j: int|
                    0 <= i < n as int && 0 <= j < n as int ==> #[trigger] flows@[i]@[j]
                        == Self::tc_prefix(base, k as nat, i, j),
            decreases n - k,
        )]
        while k < n {
            let mut i = 0;
            // Middle loop: rows before `i` have already been updated to pivot `k`.
            #[verus_spec(
                invariant
                    flows.wf(),
                    n == flows@.len(),
                    k < n,
                    i <= n,
                    forall|r: int|
                        0 <= r < flows@.len() ==> #[trigger] flows@[r]@.len() == flows@.len(),
                    forall|r: int, c: int|
                        0 <= r < i as int && 0 <= c < n as int ==> #[trigger] flows@[r]@[c]
                            == Self::tc_prefix(base, (k + 1) as nat, r, c),
                    forall|r: int, c: int|
                        i as int <= r < n as int && 0 <= c < n as int ==> #[trigger] flows@[r]@[c]
                            == Self::tc_prefix(base, k as nat, r, c),
                decreases n - i,
            )]
            while i < n {
                let ik = flows[i][k];
                let mut j = 0;
                // Inner loop: columns before `j` in row `i` already reflect pivot `k`.
                #[verus_spec(
                    invariant
                        flows.wf(),
                        n == flows@.len(),
                        k < n,
                        i < n,
                        j <= n,
                        ik == Self::tc_prefix(base, k as nat, i as int, k as int),
                        forall|r: int|
                            0 <= r < flows@.len() ==> #[trigger] flows@[r]@.len() == flows@.len(),
                        forall|c: int|
                            0 <= c < n as int ==> #[trigger] flows@[k as int]@[c]
                                == Self::tc_prefix(base, k as nat, k as int, c),
                        forall|r: int, c: int|
                            0 <= r < i as int && 0 <= c < n as int ==> #[trigger] flows@[r]@[c]
                                == Self::tc_prefix(base, (k + 1) as nat, r, c),
                        forall|c: int|
                            0 <= c < j as int ==> #[trigger] flows@[i as int]@[c]
                                == Self::tc_prefix(base, (k + 1) as nat, i as int, c),
                        forall|c: int|
                            j as int <= c < n as int ==> #[trigger] flows@[i as int]@[c]
                                == Self::tc_prefix(base, k as nat, i as int, c),
                        forall|r: int, c: int|
                            Self::row_suffix_cell(i as int, n as nat, r, c)
                                ==> #[trigger] flows@[r]@[c] == Self::tc_prefix(
                                base,
                                k as nat,
                                r,
                                c,
                            ),
                    decreases n - j,
                )]
                while j < n {
                    let kj = flows[k][j];
                    let mut row = flows.remove(i);
                    let new_val = row[j] || (ik && kj);
                    update_vec(&mut row, j, new_val);
                    flows.insert(i, row);
                    j += 1;
                }
                i += 1;
            }
            k += 1;
        }

        proof {
            assert(k == n);
            // At loop exit we have the full closure `tc_prefix(base, n, .., ..)`.
            assert forall|i: int, j: int|
                #![auto]
                0 <= i < flows@.len() && 0 <= j < flows@.len() implies flows@[i]@[j]
                == Self::tc_prefix(base, n as nat, i, j) by {};
            assert forall|i: int, j: int|
                #![auto]
                0 <= i < flows@.len() && 0 <= j < flows@.len()
                    && base[i][j] implies flows@[i]@[j] by {
                Self::lemma_tc_prefix_contains_base(base, n as nat, i, j);
            }
            assert forall|i: int, j: int, m: int|
                #![auto]
                0 <= i < flows@.len() && 0 <= j < flows@.len() && 0 <= m < flows@.len()
                    && flows@[i]@[j] && flows@[j]@[m] implies flows@[i]@[m] by {
                Self::lemma_tc_prefix_closed_under_pivot(base, n as nat, j, i, m);
            }
        }
    }

    /// Checks that every pair of valid levels has both a join and a meet in
    /// the finite matrix representation.
    #[verus_spec(r =>
        requires
            self.square(),
        ensures
            r matches Ok(()) ==> forall|l1: LevelId, l2: LevelId|
                self.valid_level(l1) && self.valid_level(l2) ==> self.has_join_and_meet(l1, l2),
    )]
    #[verifier::spinoff_prover]
    fn validate_joins_and_meets(&self) -> Result<(), FiniteLatticeBuildError> {
        let n = self.level_names.len();
        let mut lhs = 0;
        // Sweep all pairs and accumulate the prefix fact:
        // every pair seen so far already has both a join and a meet.
        #[verus_spec(
            invariant
                self.square(),
                n == self.level_names.len(),
                lhs <= n,
                forall|a: int, b: int|
                    0 <= a < lhs as int && 0 <= b < n as int ==> #[trigger] self.has_join_and_meet(
                        LevelId(a as usize),
                        LevelId(b as usize),
                    ),
            decreases n - lhs,
        )]
        while lhs < n {
            let mut rhs = 0;
            #[verus_spec(
                invariant
                    self.square(),
                    n == self.level_names.len(),
                    lhs < n,
                    forall|a: int, b: int|
                        0 <= a < lhs as int && 0 <= b < n as int
                            ==> #[trigger] self.has_join_and_meet(
                            LevelId(a as usize),
                            LevelId(b as usize),
                        ),
                    forall|b: int|
                        0 <= b < rhs as int ==> #[trigger] self.has_join_and_meet(
                            LevelId(lhs),
                            LevelId(b as usize),
                        ),
                decreases n - rhs,
            )]
            while rhs < n {
                let join = self.join(LevelId(lhs), LevelId(rhs));
                if join.is_none() {
                    return Err(FiniteLatticeBuildError::MissingJoin { lhs, rhs });
                }
                let meet = self.meet(LevelId(lhs), LevelId(rhs));
                if meet.is_none() {
                    return Err(FiniteLatticeBuildError::MissingMeet { lhs, rhs });
                }
                match join {
                    Some(j) => {
                        match meet {
                            Some(m) => {
                                proof {
                                    assert(self.has_join_and_meet(LevelId(lhs), LevelId(rhs)));
                                }
                            },
                            None => {},
                        }
                    },
                    None => {},
                }
                rhs += 1;
            }
            lhs += 1;
        }

        proof {
            // The loop invariants are phrased over integer prefixes; here we repackage them
            // into the abstract `LevelId`-quantified statement used by `wf`.
            assert(lhs == n);
            assert forall|l1: LevelId, l2: LevelId|
                self.valid_level(l1) && self.valid_level(l2) implies self.has_join_and_meet(
                l1,
                l2,
            ) by {
                let a = l1.0 as int;
                let b = l2.0 as int;
                assert(0 <= a);
                assert(a < lhs as int);
                assert(0 <= b);
                assert(b < n as int);
                assert(self.has_join_and_meet(LevelId(a as usize), LevelId(b as usize)));
                assert(LevelId(a as usize) == l1);
                assert(LevelId(b as usize) == l2);
            }
        }

        Ok(())
    }

    /// Enumerates all candidate bounds and returns the unique best upper bound
    /// or lower bound, depending on `upper`.
    ///
    /// This is the executable search routine underlying runtime `join` and
    /// `meet`.
    #[verus_spec(r =>
        requires
            self.square(),
            self.valid_level(lhs),
            self.valid_level(rhs),
        ensures
            r matches Some(i) ==> i < self.level_count()
                && (upper ==> self.is_join_of(lhs, rhs, LevelId(i)))
                && (!upper ==> self.is_meet_of(lhs, rhs, LevelId(i))),
    )]
    #[verifier::spinoff_prover]
    fn unique_best_bound(&self, lhs: LevelId, rhs: LevelId, upper: bool) -> Option<usize> {
        let n = self.level_names.len();
        let mut cand = 0;
        // Try each level as a candidate bound until we find one that dominates every other
        // bound of the same kind. That gives least-upper-bound or greatest-lower-bound.
        #[verus_spec(
            invariant
                self.square(),
                self.valid_level(lhs),
                self.valid_level(rhs),
                n == self.level_names.len(),
                cand <= n,
            decreases n - cand,
        )]
        while cand < n {
            let is_bound = if upper {
                self.flows[lhs.0][cand] && self.flows[rhs.0][cand]
            } else {
                self.flows[cand][lhs.0] && self.flows[cand][rhs.0]
            };

            if is_bound {
                let mut all_bounds_above = true;
                let mut other = 0;
                // Scan all other levels and check that any competing bound is above `cand`
                // (or below `cand` in the meet case).
                #[verus_spec(
                    invariant
                        self.square(),
                        self.valid_level(lhs),
                        self.valid_level(rhs),
                        n == self.level_names.len(),
                        cand < n,
                        self.bound_for(lhs, rhs, LevelId(cand), upper),
                        other <= n,
                        all_bounds_above ==> forall|j: LevelId|
                            self.valid_level(j) && j.0 < other && #[trigger] self.bound_for(
                                lhs,
                                rhs,
                                j,
                                upper,
                            ) ==> if upper {
                                self.flows_to_spec(LevelId(cand), j)
                            } else {
                                self.flows_to_spec(j, LevelId(cand))
                            },
                    decreases n - other,
                )]
                while other < n {
                    let other_is_bound = if upper {
                        self.flows[lhs.0][other] && self.flows[rhs.0][other]
                    } else {
                        self.flows[other][lhs.0] && self.flows[other][rhs.0]
                    };

                    if other_is_bound {
                        let cand_is_best = if upper {
                            self.flows[cand][other]
                        } else {
                            self.flows[other][cand]
                        };
                        if !cand_is_best {
                            all_bounds_above = false;
                        }
                    }
                    other += 1;
                }

                if all_bounds_above {
                    proof {
                        assert(other == n);
                        assert(cand < self.level_count());
                        assert(self.valid_level(LevelId(cand)));
                        assert(self.bound_for(lhs, rhs, LevelId(cand), upper));
                        assert(if upper {
                            self.upper_bound(lhs, rhs, LevelId(cand))
                        } else {
                            self.lower_bound(lhs, rhs, LevelId(cand))
                        });
                        assert forall|x: LevelId|
                            self.valid_level(x) && #[trigger] self.bound_for(
                                lhs,
                                rhs,
                                x,
                                upper,
                            ) implies if upper {
                            self.flows_to_spec(LevelId(cand), x)
                        } else {
                            self.flows_to_spec(x, LevelId(cand))
                        } by {
                            assert(LevelId(x.0) == x);
                            assert(x.0 < n);
                            assert((x.0 as int) < (other as int));
                            assert(0 <= (x.0 as int));
                            assert(self.bound_for(lhs, rhs, LevelId(x.0), upper));
                            assert(forall|j: LevelId|
                                self.valid_level(j) && j.0 < other && #[trigger] self.bound_for(
                                    lhs,
                                    rhs,
                                    j,
                                    upper,
                                ) ==> if upper {
                                    self.flows_to_spec(LevelId(cand), j)
                                } else {
                                    self.flows_to_spec(j, LevelId(cand))
                                });
                            assert(if upper {
                                self.flows_to_spec(LevelId(cand), x)
                            } else {
                                self.flows_to_spec(x, LevelId(cand))
                            });
                        }
                        if upper {
                            // In the upper-bound branch, "best among all upper bounds" is
                            // exactly the definition of join.
                            assert(self.is_join_of(lhs, rhs, LevelId(cand))) by {
                                assert(upper);
                                assert(self.upper_bound(lhs, rhs, LevelId(cand)));
                                assert forall|ub: LevelId|
                                    self.valid_level(ub) && #[trigger] self.upper_bound(
                                        lhs,
                                        rhs,
                                        ub,
                                    ) implies self.flows_to_spec(LevelId(cand), ub) by {
                                    assert(self.bound_for(lhs, rhs, ub, upper));
                                }
                            }
                        } else {
                            // Dually, in the lower-bound branch we obtain the meet.
                            assert(self.is_meet_of(lhs, rhs, LevelId(cand))) by {
                                assert(!upper);
                                assert(self.lower_bound(lhs, rhs, LevelId(cand)));
                                assert forall|lb: LevelId|
                                    self.valid_level(lb) && #[trigger] self.lower_bound(
                                        lhs,
                                        rhs,
                                        lb,
                                    ) implies self.flows_to_spec(lb, LevelId(cand)) by {
                                    assert(self.bound_for(lhs, rhs, lb, upper));
                                }
                            }
                        }
                    }
                    return Some(cand);
                }
            }
            cand += 1;
        }

        None
    }
}

#[cfg(feature = "alloc")]
impl WellFormed for FiniteLattice {
    /// Bundles the full bounded-lattice contract for the concrete finite
    /// representation.
    ///
    /// A well-formed finite lattice has a square matrix, valid bottom/top
    /// indices, a partial order, explicit bounds, and existence of join/meet
    /// for every valid pair.
    open spec fn wf(&self) -> bool {
        // `wf` packages exactly the structure we need from a finite bounded lattice:
        // a partial order with bottom/top plus existence of joins and meets.
        &&& self.level_names.wf()
        &&& self.flows.wf()
        &&& self.level_count() > 0
        &&& self.square()
        &&& self.valid_level(self.bot)
        &&& self.valid_level(self.top)
        &&& forall|l: LevelId| self.valid_level(l) ==> #[trigger] self.flows_to_spec(l, l)
        &&& forall|l1: LevelId, l2: LevelId|
            self.valid_level(l1) && self.valid_level(l2) && self.flows_to_spec(l1, l2)
                && self.flows_to_spec(l2, l1) ==> l1 == l2
        &&& forall|l1: LevelId, l2: LevelId, l3: LevelId|
            #![auto]
            self.valid_level(l1) && self.valid_level(l2) && self.valid_level(l3)
                && self.flows_to_spec(l1, l2) && self.flows_to_spec(l2, l3) ==> self.flows_to_spec(
                l1,
                l3,
            )
        &&& forall|l: LevelId| #![auto] self.valid_level(l) ==> self.flows_to_spec(self.bot, l)
        &&& forall|l: LevelId| #![auto] self.valid_level(l) ==> self.flows_to_spec(l, self.top)
        &&& forall|l1: LevelId, l2: LevelId|
            self.valid_level(l1) && self.valid_level(l2) ==> self.has_join_and_meet(l1, l2)
    }
}

#[cfg(feature = "alloc")]
#[verus_spec(r =>
    requires
        this.square(),
        this.valid_level(this.bot),
        this.valid_level(this.top),
        forall|l: LevelId| this.valid_level(l) ==> #[trigger] this.flows_to_spec(l, l),
        forall|l1: LevelId, l2: LevelId|
            this.valid_level(l1) && this.valid_level(l2) && this.flows_to_spec(l1, l2)
                && this.flows_to_spec(l2, l1) ==> l1 == l2,
        forall|l1: LevelId, l2: LevelId, l3: LevelId|
            #![auto]
            this.valid_level(l1) && this.valid_level(l2) && this.valid_level(l3)
                && this.flows_to_spec(l1, l2) && this.flows_to_spec(l2, l3) ==> this.flows_to_spec(
                l1,
                l3,
            ),
        forall|l: LevelId| #![auto] this.valid_level(l) ==> this.flows_to_spec(this.bot, l),
        forall|l: LevelId| #![auto] this.valid_level(l) ==> this.flows_to_spec(l, this.top),
        forall|l1: LevelId, l2: LevelId|
            this.valid_level(l1) && this.valid_level(l2) ==> this.has_join_and_meet(l1, l2),
    ensures
        this.wf(),
)]
#[verifier::spinoff_prover]
/// Repackages the individual bounded-lattice axioms into the bundled `wf()`
/// predicate of [`FiniteLattice`].
pub proof fn lemma_wf_from_components(this: FiniteLattice) {
    assert(this.wf());
}

#[cfg(feature = "alloc")]
#[verus_spec(r =>
    requires
        this.wf(),
        this.valid_level(level),
    ensures
        this.flows_to_spec(level, level),
)]
#[verifier::spinoff_prover]
/// Extracts reflexivity from the bundled `wf()` predicate.
pub proof fn lemma_finite_lattice_reflexive(this: FiniteLattice, level: LevelId) {
}

#[cfg(feature = "alloc")]
#[verus_spec(r =>
    requires
        this.wf(),
        this.valid_level(lhs),
        this.valid_level(rhs),
        this.flows_to_spec(lhs, rhs),
        this.flows_to_spec(rhs, lhs),
    ensures
        lhs == rhs,
)]
#[verifier::spinoff_prover]
/// Extracts antisymmetry from the bundled `wf()` predicate.
pub proof fn lemma_finite_lattice_antisymmetric(this: FiniteLattice, lhs: LevelId, rhs: LevelId) {
}

#[cfg(feature = "alloc")]
#[verus_spec(r =>
    requires
        this.wf(),
        this.valid_level(lhs),
        this.valid_level(mid),
        this.valid_level(rhs),
        this.flows_to_spec(lhs, mid),
        this.flows_to_spec(mid, rhs),
    ensures
        this.flows_to_spec(lhs, rhs),
)]
#[verifier::spinoff_prover]
/// Extracts transitivity from the bundled `wf()` predicate.
pub proof fn lemma_finite_lattice_transitive(
    this: FiniteLattice,
    lhs: LevelId,
    mid: LevelId,
    rhs: LevelId,
) {
}

/// A generic instance-based bounded lattice interface for information-flow
/// labels.
///
/// Implementations expose the order relation and the lattice operators as
/// total spec functions, and then discharge the usual lattice laws through the
/// proof methods below.
pub trait SecurityLattice<Level: WellFormed + Copy + PartialEq>: WellFormed {
    /// Checks whether a label is a valid element of this lattice instance.
    spec fn valid_level(&self, level: Level) -> bool;

    /// Returns the least element of the lattice.
    spec fn bot(&self) -> Level;

    /// Returns the greatest element of the lattice.
    spec fn top(&self) -> Level;

    /// The partial-order relation of the lattice.
    spec fn flows_to(&self, lhs: Level, rhs: Level) -> bool
        recommends
            self.wf(),
            self.valid_level(lhs),
            self.valid_level(rhs),
    ;

    /// The least upper bound operator.
    spec fn join(&self, lhs: Level, rhs: Level) -> Level
        recommends
            self.wf(),
            self.valid_level(lhs),
            self.valid_level(rhs),
    ;

    /// The greatest lower bound operator.
    spec fn meet(&self, lhs: Level, rhs: Level) -> Level
        recommends
            self.wf(),
            self.valid_level(lhs),
            self.valid_level(rhs),
    ;

    /// Proof obligation for reflexivity of the lattice order.
    proof fn lemma_reflexive(&self, level: Level)
        requires
            self.wf(),
            self.valid_level(level),
        ensures
            self.flows_to(level, level),
    ;

    /// Proof obligation for antisymmetry of the lattice order.
    proof fn lemma_antisymmetric(&self, lhs: Level, rhs: Level)
        requires
            self.wf(),
            self.valid_level(lhs),
            self.valid_level(rhs),
        ensures
            self.flows_to(lhs, rhs) && self.flows_to(rhs, lhs) ==> lhs == rhs,
    ;

    /// Proof obligation for transitivity of the lattice order.
    proof fn lemma_transitive(&self, lhs: Level, mid: Level, rhs: Level)
        requires
            self.wf(),
            self.valid_level(lhs),
            self.valid_level(mid),
            self.valid_level(rhs),
        ensures
            self.flows_to(lhs, mid) && self.flows_to(mid, rhs) ==> self.flows_to(lhs, rhs),
    ;

    /// Proof obligation stating that `bot()` and `top()` are valid bounds.
    proof fn lemma_bot_top(&self, level: Level)
        requires
            self.wf(),
            self.valid_level(level),
        ensures
            self.valid_level(self.bot()),
            self.valid_level(self.top()),
            self.flows_to(self.bot(), level),
            self.flows_to(level, self.top()),
    ;

    /// Proof obligation stating that `join(lhs, rhs)` is the least upper bound.
    proof fn lemma_join_is_lub(&self, lhs: Level, rhs: Level, upper_bound: Level)
        requires
            self.wf(),
            self.valid_level(lhs),
            self.valid_level(rhs),
            self.valid_level(upper_bound),
        ensures
            self.valid_level(self.join(lhs, rhs)),
            self.flows_to(lhs, self.join(lhs, rhs)),
            self.flows_to(rhs, self.join(lhs, rhs)),
            self.flows_to(lhs, upper_bound) && self.flows_to(rhs, upper_bound) ==> self.flows_to(
                self.join(lhs, rhs),
                upper_bound,
            ),
    ;

    /// Proof obligation stating that `meet(lhs, rhs)` is the greatest lower bound.
    proof fn lemma_meet_is_glb(&self, lhs: Level, rhs: Level, lower_bound: Level)
        requires
            self.wf(),
            self.valid_level(lhs),
            self.valid_level(rhs),
            self.valid_level(lower_bound),
        ensures
            self.valid_level(self.meet(lhs, rhs)),
            self.flows_to(self.meet(lhs, rhs), lhs),
            self.flows_to(self.meet(lhs, rhs), rhs),
            self.flows_to(lower_bound, lhs) && self.flows_to(lower_bound, rhs) ==> self.flows_to(
                lower_bound,
                self.meet(lhs, rhs),
            ),
    ;
}

#[cfg(feature = "alloc")]
impl SecurityLattice<LevelId> for FiniteLattice {
    /// Reuses the concrete index-validity predicate from [`FiniteLattice`].
    open spec fn valid_level(&self, level: LevelId) -> bool {
        FiniteLattice::valid_level(self, level)
    }

    /// Returns the stored bottom index.
    open spec fn bot(&self) -> LevelId {
        self.bot
    }

    /// Returns the stored top index.
    open spec fn top(&self) -> LevelId {
        self.top
    }

    /// Reuses the concrete matrix relation as the trait-level order relation.
    open spec fn flows_to(&self, lhs: LevelId, rhs: LevelId) -> bool {
        self.flows_to_spec(lhs, rhs)
    }

    /// Chooses the join witness guaranteed to exist by `wf()`.
    open spec fn join(&self, lhs: LevelId, rhs: LevelId) -> LevelId {
        choose|level: LevelId| #![auto] self.valid_level(level) && self.is_join_of(lhs, rhs, level)
    }

    /// Chooses the meet witness guaranteed to exist by `wf()`.
    open spec fn meet(&self, lhs: LevelId, rhs: LevelId) -> LevelId {
        choose|level: LevelId| #![auto] self.valid_level(level) && self.is_meet_of(lhs, rhs, level)
    }

    /// Discharges the trait reflexivity obligation from `FiniteLattice::wf()`.
    proof fn lemma_reflexive(&self, level: LevelId) {
        assert(self.square());
        lemma_finite_lattice_reflexive(*self, level);
    }

    /// Discharges the trait antisymmetry obligation from `FiniteLattice::wf()`.
    proof fn lemma_antisymmetric(&self, lhs: LevelId, rhs: LevelId) {
        assert(self.square());
        assert(self.flows_to(lhs, rhs) && self.flows_to(rhs, lhs) ==> lhs == rhs) by {
            if self.flows_to(lhs, rhs) && self.flows_to(rhs, lhs) {
                lemma_finite_lattice_antisymmetric(*self, lhs, rhs);
            }
        }
    }

    /// Discharges the trait transitivity obligation from `FiniteLattice::wf()`.
    proof fn lemma_transitive(&self, lhs: LevelId, mid: LevelId, rhs: LevelId) {
        assert(self.square());
        assert(self.flows_to(lhs, mid) && self.flows_to(mid, rhs) ==> self.flows_to(lhs, rhs)) by {
            if self.flows_to(lhs, mid) && self.flows_to(mid, rhs) {
                lemma_finite_lattice_transitive(*self, lhs, mid, rhs);
            }
        }
    }

    /// Discharges the explicit `bot`/`top` bound obligation from `FiniteLattice::wf()`.
    proof fn lemma_bot_top(&self, level: LevelId) {
        assert(self.flows_to(self.bot(), level));
        assert(self.flows_to(level, self.top()));
    }

    /// Discharges the trait join/LUB obligation using the witness chosen from
    /// `FiniteLattice::wf()`.
    proof fn lemma_join_is_lub(&self, lhs: LevelId, rhs: LevelId, upper_bound: LevelId) {
        assert(self.square());
        assert(self.valid_level(lhs));
        assert(self.valid_level(rhs));
        assert(self.valid_level(upper_bound));
        assert(self.has_join_and_meet(lhs, rhs));
        let join = <FiniteLattice as SecurityLattice<LevelId>>::join(self, lhs, rhs);
        assert(self.valid_level(join) && self.is_join_of(lhs, rhs, join));
        assert(self.flows_to(lhs, upper_bound) && self.flows_to(rhs, upper_bound) ==> self.flows_to(
            <FiniteLattice as SecurityLattice<LevelId>>::join(self, lhs, rhs),
            upper_bound,
        )) by {
            if self.flows_to(lhs, upper_bound) && self.flows_to(rhs, upper_bound) {
                assert(self.upper_bound(lhs, rhs, upper_bound));
                assert(self.is_join_of(lhs, rhs, join));
                assert(self.flows_to_spec(join, upper_bound));
            }
        }
    }

    /// Discharges the trait meet/GLB obligation using the witness chosen from
    /// `FiniteLattice::wf()`.
    proof fn lemma_meet_is_glb(&self, lhs: LevelId, rhs: LevelId, lower_bound: LevelId) {
        assert(self.square());
        assert(self.valid_level(lhs));
        assert(self.valid_level(rhs));
        assert(self.valid_level(lower_bound));
        assert(self.has_join_and_meet(lhs, rhs));
        let meet = <FiniteLattice as SecurityLattice<LevelId>>::meet(self, lhs, rhs);
        assert(self.valid_level(meet) && self.is_meet_of(lhs, rhs, meet));
        assert(self.flows_to(lower_bound, lhs) && self.flows_to(lower_bound, rhs) ==> self.flows_to(
            lower_bound,
            <FiniteLattice as SecurityLattice<LevelId>>::meet(self, lhs, rhs),
        )) by {
            if self.flows_to(lower_bound, lhs) && self.flows_to(lower_bound, rhs) {
                assert(self.lower_bound(lhs, rhs, lower_bound));
                assert(self.is_meet_of(lhs, rhs, meet));
                assert(self.flows_to_spec(lower_bound, meet));
            }
        }
    }
}

#[verifier::inline]
/// A pure helper for IFC "upgrade" checks: upgrades are exactly flows allowed
/// by the lattice order.
pub open spec fn valid_upgrade<Level: WellFormed + Copy + PartialEq, L: SecurityLattice<Level>>(
    lattice: &L,
    from: Level,
    to: Level,
) -> bool
    recommends
        lattice.wf(),
        lattice.valid_level(from),
        lattice.valid_level(to),
{
    lattice.flows_to(from, to)
}

#[verifier::inline]
/// A pure helper for IFC "downgrade" checks: the downgrade must be explicitly
/// authorized by a declassifier and flow in the reverse direction.
pub open spec fn valid_downgrade<Level: WellFormed + Copy + PartialEq, L: SecurityLattice<Level>>(
    lattice: &L,
    from: Level,
    to: Level,
    has_declassifier: bool,
) -> bool
    recommends
        lattice.wf(),
        lattice.valid_level(from),
        lattice.valid_level(to),
{
    has_declassifier && lattice.flows_to(to, from)
}

} // verus!
#[cfg(feature = "alloc")]
impl fmt::Display for FiniteLatticeBuildError {
    /// Renders human-readable build errors for diagnostics and policy-load
    /// failure reporting.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyLevels => write!(f, "lattice.levels must not be empty"),
            Self::DuplicateLevelName(name) => write!(f, "duplicate lattice level {:?}", name),
            Self::UnknownLevel(name) => write!(f, "unknown lattice level {:?}", name),
            Self::InvalidBottom(name) => write!(f, "invalid lattice bottom {:?}", name),
            Self::InvalidTop(name) => write!(f, "invalid lattice top {:?}", name),
            Self::NotPartialOrder { lhs, rhs } => {
                write!(f, "lattice relation is not antisymmetric between {} and {}", lhs, rhs)
            }
            Self::MissingBottomReachability { level } => {
                write!(f, "bottom does not flow to level {}", level)
            }
            Self::MissingTopReachability { level } => {
                write!(f, "level {} does not flow to top", level)
            }
            Self::MissingJoin { lhs, rhs } => {
                write!(f, "no unique join for levels {} and {}", lhs, rhs)
            }
            Self::MissingMeet { lhs, rhs } => {
                write!(f, "no unique meet for levels {} and {}", lhs, rhs)
            }
        }
    }
}
