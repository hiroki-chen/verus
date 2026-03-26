use core::fmt;

use deko_std::std_extra::slice::{bytes_eq, bytes_eq_spec};
use deko_std::wf::WellFormed;
use vstd::prelude::*;

#[cfg(feature = "alloc")]
use crate::collections::update_vec;
#[cfg(feature = "alloc")]
use crate::collections::Vec;
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
impl WellFormed for LatticeConfigToml {
    open spec fn wf(&self) -> bool {
        self.levels.wf() && self.relations.wf() && self.bot.wf() && self.top.wf()
    }
}

#[cfg(feature = "alloc")]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LevelId(pub usize);

impl WellFormed for LevelId {
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
#[derive(Clone, Debug, PartialEq, Eq)]
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
    #[verifier::inline]
    pub open spec fn level_count(&self) -> usize {
        self.level_names@.len() as usize
    }

    #[verifier::inline]
    pub open spec fn valid_level(&self, level: LevelId) -> bool {
        level.0 < self.level_count()
    }

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

    #[verifier::inline]
    pub open spec fn upper_bound(&self, lhs: LevelId, rhs: LevelId, ub: LevelId) -> bool
        recommends
            self.square(),
            self.valid_level(lhs),
            self.valid_level(rhs),
            self.valid_level(ub),
    {
        self.flows_to_spec(lhs, ub) && self.flows_to_spec(rhs, ub)
    }

    #[verifier::inline]
    pub open spec fn lower_bound(&self, lhs: LevelId, rhs: LevelId, lb: LevelId) -> bool
        recommends
            self.square(),
            self.valid_level(lhs),
            self.valid_level(rhs),
            self.valid_level(lb),
    {
        self.flows_to_spec(lb, lhs) && self.flows_to_spec(lb, rhs)
    }

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

    pub open spec fn has_join_and_meet(&self, lhs: LevelId, rhs: LevelId) -> bool
        recommends
            self.square(),
            self.valid_level(lhs),
            self.valid_level(rhs),
    {
        exists|j: LevelId, m: LevelId|
            self.valid_level(j) && self.valid_level(m) && self.is_join_of(lhs, rhs, j)
                && self.is_meet_of(lhs, rhs, m)
    }

    #[verifier::inline]
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
            r matches Ok(lattice) ==> lattice.wf(),
    )]
    pub fn compile(cfg: &LatticeConfigToml) -> Result<Self, FiniteLatticeBuildError> {
        broadcast use vstd::std_specs::vec::group_vec_axioms;

        if cfg.levels.is_empty() {
            return Err(FiniteLatticeBuildError::EmptyLevels);
        }
        let n = cfg.levels.len();
        let mut i = 0;
        while i < n
            invariant
                n == cfg.levels@.len(),
                i <= n,
            decreases n - i,
        {
            let mut j = i + 1;
            while j < n
                invariant
                    n == cfg.levels@.len(),
                    i < n,
                    i + 1 <= j <= n,
                decreases n - j,
            {
                if cfg.levels[i] == cfg.levels[j] {
                    return Err(FiniteLatticeBuildError::DuplicateLevelName(cfg.levels[i].clone()));
                }
                j += 1;
            }
            i += 1;
        }

        let bot_idx = match Self::lookup_level(&cfg.levels, &cfg.bot) {
            Some(i) => i,
            None => return Err(FiniteLatticeBuildError::InvalidBottom(cfg.bot.clone())),
        };
        let top_idx = match Self::lookup_level(&cfg.levels, &cfg.top) {
            Some(i) => i,
            None => return Err(FiniteLatticeBuildError::InvalidTop(cfg.top.clone())),
        };

        let mut flows: Vec<Vec<bool>> = Vec::with_capacity_in(n, DekoAllocatorApi {  });
        let mut i = 0;
        while i < n
            invariant
                flows.wf(),
                flows@.len() == i,
                i <= n,
                forall|r: int| 0 <= r < flows@.len() ==> #[trigger] flows@[r]@.len() == n,
                forall|r: int| 0 <= r < flows@.len() ==> flows@[r][r],
            decreases n - i,
        {
            let mut row: Vec<bool> = Vec::with_capacity_in(n, DekoAllocatorApi {  });
            let mut j = 0;
            while j < n
                invariant
                    row.wf(),
                    row@.len() == j,
                    j <= n,
                    forall|c: int| 0 <= c < j as int ==> #[trigger] row@[c] == (c == i as int),
                decreases n - j,
            {
                row.push(i == j);
                j += 1;
            }
            proof {
                assert(row@.len() == n);
                assert(row@[i as int]);
            }
            flows.push(row);
            i += 1;
        }

        let mut rel = 0;
        while rel < cfg.relations.len()
            invariant
                flows.wf(),
                n == cfg.levels@.len(),
                flows@.len() == n,
                rel <= cfg.relations@.len(),
                forall|r: int| 0 <= r < flows@.len() ==> #[trigger] flows@[r]@.len() == n,
                forall|r: int| 0 <= r < n as int ==> flows@[r][r],
            decreases cfg.relations.len() - rel,
        {
            let (lhs_name, rhs_name) = &cfg.relations[rel];
            let lhs = match Self::lookup_level(&cfg.levels, lhs_name) {
                Some(i) => i,
                None => return Err(FiniteLatticeBuildError::UnknownLevel(lhs_name.clone())),
            };
            let rhs = match Self::lookup_level(&cfg.levels, rhs_name) {
                Some(i) => i,
                None => return Err(FiniteLatticeBuildError::UnknownLevel(rhs_name.clone())),
            };
            let mut row = flows.remove(lhs);
            update_vec(&mut row, rhs, true);
            proof {
                assert(row@.len() == n);
                if lhs == rhs {
                    assert(row@[lhs as int]);
                } else {
                    assert(row@[lhs as int]);
                }
            }
            flows.insert(lhs, row);
            rel += 1;
        }

        let ghost pre_tc = Self::flow_matrix_view(flows@);
        proof {
            assert forall|r: int| 0 <= r < n as int implies pre_tc[r][r] by {
                assert(flows@[r][r]);
            }
        }

        // To remove any reduandant edges and ensure transitivity,
        // we compute the transitive closure of the input relation.
        //
        // This also makes it easier to check the lattice invariants
        // in the next steps, since we can rely on the fact that all
        // implied flows are already present in the matrix.
        //
        // See https://en.wikipedia.org/wiki/Floyd%E2%80%93Warshall_algorithm
        Self::transitive_closure(&mut flows);
        proof {
            assert forall|r: int| 0 <= r < n as int implies flows@[r][r] by {
                assert(pre_tc[r][r]);
            }
        }

        let mut i = 0;
        while i < n
            invariant
                flows.wf(),
                flows@.len() == n,
                i <= n,
                forall|r: int| 0 <= r < flows@.len() ==> #[trigger] flows@[r]@.len() == n,
                forall|a: int, b: int|
                    0 <= a < i as int && 0 <= b < n as int && a != b ==> !(flows@[a][b]
                        && flows@[b][a]),
            decreases n - i,
        {
            let mut j = 0;
            while j < n
                invariant
                    flows.wf(),
                    flows@.len() == n,
                    i < n,
                    j <= n,
                    forall|r: int| 0 <= r < flows@.len() ==> #[trigger] flows@[r]@.len() == n,
                    forall|a: int, b: int|
                        0 <= a < i as int && 0 <= b < n as int && a != b ==> !(flows@[a][b]
                            && flows@[b][a]),
                    forall|b: int|
                        0 <= b < j as int && i as int != b ==> !(flows@[i as int][b]
                            && flows@[b][i as int]),
                decreases n - j,
            {
                if i != j && flows[i][j] && flows[j][i] {
                    return Err(FiniteLatticeBuildError::NotPartialOrder { lhs: i, rhs: j });
                }
                j += 1;
            }
            i += 1;
        }

        let mut i = 0;
        while i < n
            invariant
                flows.wf(),
                flows@.len() == n,
                i <= n,
                bot_idx < n,
                top_idx < n,
                forall|r: int| 0 <= r < flows@.len() ==> #[trigger] flows@[r]@.len() == n,
                forall|a: int|
                    0 <= a < i as int ==> flows@[bot_idx as int][a] && flows@[a][top_idx as int],
            decreases n - i,
        {
            if !flows[bot_idx][i] {
                return Err(FiniteLatticeBuildError::MissingBottomReachability { level: i });
            }
            if !flows[i][top_idx] {
                return Err(FiniteLatticeBuildError::MissingTopReachability { level: i });
            }
            i += 1;
        }

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
            assert forall|l1: LevelId, l2: LevelId|
                lattice.valid_level(l1) && lattice.valid_level(
                    l2,
                ) implies lattice.has_join_and_meet(l1, l2) by {}
            assert forall|l: LevelId|
                lattice.valid_level(l) implies #[trigger] lattice.flows_to_spec(l, l) by {
                let idx = l.0;
                assert(lattice.valid_level(l));
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
            assert forall|l: LevelId| lattice.valid_level(l) implies lattice.flows_to_spec(
                lattice.bot,
                l,
            ) by {
                let idx = l.0;
                assert(lattice.valid_level(l));
                assert(idx < n);
                assert(lattice.flows@[bot_idx as int][idx as int]
                    && lattice.flows@[idx as int][top_idx as int]);
            }
            assert forall|l: LevelId| lattice.valid_level(l) implies lattice.flows_to_spec(
                l,
                lattice.top,
            ) by {
                let idx = l.0;
                assert(lattice.valid_level(l));
                assert(idx < n);
                assert(lattice.flows@[bot_idx as int][idx as int]
                    && lattice.flows@[idx as int][top_idx as int]);
            }
            lemma_wf_from_components(lattice);
        }
        Ok(lattice)
    }

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

    #[verus_spec(r =>
        ensures
            r matches Some(i) ==> i < levels@.len() && bytes_eq_spec(levels@[i as int]@, name@),
            r is None ==> forall|i: int|
                0 <= i < levels@.len() ==> !bytes_eq_spec(levels@[i]@, name@),
    )]
    fn lookup_level(levels: &[Vec<u8>], name: &[u8]) -> Option<usize> {
        let mut i = 0;
        while i < levels.len()
            invariant
                0 <= i <= levels.len(),
                forall|j: int| 0 <= j < i as int ==> !bytes_eq_spec(levels@[j]@, name@),
            decreases levels.len() - i,
        {
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

    // Warshall-style spec: after exposing the first `k` pivots, can `i` reach `j`?
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

    // Convert the executable `Vec<Vec<bool>>` state into the pure matrix view used by proofs.
    pub open spec fn flow_matrix_view(flows: Seq<Vec<bool>>) -> Seq<Seq<bool>> {
        flows.map_values(|row: Vec<bool>| row@)
    }

    pub open spec fn row_suffix_cell(cur_row: int, n: nat, r: int, c: int) -> bool {
        cur_row < r && r < n as int && 0 <= c && c < n as int
    }

    // Any base edge remains present after adding more and more pivots.
    proof fn lemma_tc_prefix_contains_base(matrix: Seq<Seq<bool>>, k: nat, i: int, j: int)
        requires
            0 <= i < matrix.len(),
            0 <= j < matrix.len(),
            forall|r: int| 0 <= r < matrix.len() ==> matrix[r].len() == matrix.len(),
            matrix[i][j],
        ensures
            Self::tc_prefix(matrix, k, i, j),
        decreases k,
    {
        if k > 0 {
            Self::lemma_tc_prefix_contains_base(matrix, (k - 1) as nat, i, j);
        }
    }

    // Reaching the current pivot does not need the pivot itself as an intermediate node.
    proof fn lemma_tc_prefix_pivot_col(matrix: Seq<Seq<bool>>, k: nat, i: int)
        requires
            0 <= i < matrix.len(),
            k < matrix.len(),
            forall|r: int| 0 <= r < matrix.len() ==> matrix[r].len() == matrix.len(),
        ensures
            Self::tc_prefix(matrix, (k + 1) as nat, i, k as int) == Self::tc_prefix(
                matrix,
                k,
                i,
                k as int,
            ),
    {
    }

    // Dually, leaving the current pivot also does not need that pivot recursively.
    proof fn lemma_tc_prefix_pivot_row(matrix: Seq<Seq<bool>>, k: nat, j: int)
        requires
            0 <= j < matrix.len(),
            k < matrix.len(),
            forall|r: int| 0 <= r < matrix.len() ==> matrix[r].len() == matrix.len(),
        ensures
            Self::tc_prefix(matrix, (k + 1) as nat, k as int, j) == Self::tc_prefix(
                matrix,
                k,
                k as int,
                j,
            ),
    {
    }

    // One Warshall step either preserves an old path or creates a new one through pivot `k`.
    proof fn lemma_tc_prefix_step(matrix: Seq<Seq<bool>>, k: nat, i: int, j: int)
        requires
            0 <= i < matrix.len(),
            0 <= j < matrix.len(),
            k < matrix.len(),
            forall|r: int| 0 <= r < matrix.len() ==> matrix[r].len() == matrix.len(),
        ensures
            Self::tc_prefix(matrix, (k + 1) as nat, i, j) == (Self::tc_prefix(matrix, k, i, j) || (
            Self::tc_prefix(matrix, k, i, k as int) && Self::tc_prefix(matrix, k, k as int, j))),
    {
    }

    // Once pivot `p` is already among the first `k` pivots, `tc_prefix(k)` is closed under
    // composing paths through `p`. This is the bridge from Warshall closure to transitivity.
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
            forall|r: int| 0 <= r < matrix.len() ==> matrix[r].len() == matrix.len(),
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

    /// The Floyd-Warshall algorithm for computing the transitive closure of the flow relation in-place.
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
                0 <= i < flows@.len() && 0 <= j < flows@.len()
                    && Self::flow_matrix_view(old(flows)@)[i][j]
                    ==> flows@[i]@[j],
            forall|i: int, j: int, k: int|
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
        while k < n
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
        {
            let mut i = 0;
            // Middle loop: rows before `i` have already been updated to pivot `k`.
            while i < n
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
            {
                let ik = flows[i][k];
                let mut j = 0;
                // Inner loop: columns before `j` in row `i` already reflect pivot `k`.
                while j < n
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
                {
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
                0 <= i < flows@.len() && 0 <= j < flows@.len() implies flows@[i]@[j]
                == Self::tc_prefix(base, n as nat, i, j) by {};
            assert forall|i: int, j: int|
                0 <= i < flows@.len() && 0 <= j < flows@.len()
                    && base[i][j] implies flows@[i]@[j] by {
                Self::lemma_tc_prefix_contains_base(base, n as nat, i, j);
            }
            assert forall|i: int, j: int, m: int|
                0 <= i < flows@.len() && 0 <= j < flows@.len() && 0 <= m < flows@.len()
                    && flows@[i]@[j] && flows@[j]@[m] implies flows@[i]@[m] by {
                Self::lemma_tc_prefix_closed_under_pivot(base, n as nat, j, i, m);
            }
        }
    }

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
        while lhs < n
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
        {
            let mut rhs = 0;
            while rhs < n
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
            {
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
        while cand < n
            invariant
                self.square(),
                self.valid_level(lhs),
                self.valid_level(rhs),
                n == self.level_names.len(),
                cand <= n,
            decreases n - cand,
        {
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
                while other < n
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
                {
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
            self.valid_level(l1) && self.valid_level(l2) && self.valid_level(l3)
                && self.flows_to_spec(l1, l2) && self.flows_to_spec(l2, l3) ==> self.flows_to_spec(
                l1,
                l3,
            )
        &&& forall|l: LevelId| self.valid_level(l) ==> self.flows_to_spec(self.bot, l)
        &&& forall|l: LevelId| self.valid_level(l) ==> self.flows_to_spec(l, self.top)
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
            this.valid_level(l1) && this.valid_level(l2) && this.valid_level(l3)
                && this.flows_to_spec(l1, l2) && this.flows_to_spec(l2, l3) ==> this.flows_to_spec(
                l1,
                l3,
            ),
        forall|l: LevelId| this.valid_level(l) ==> this.flows_to_spec(this.bot, l),
        forall|l: LevelId| this.valid_level(l) ==> this.flows_to_spec(l, this.top),
        forall|l1: LevelId, l2: LevelId|
            this.valid_level(l1) && this.valid_level(l2) ==> this.has_join_and_meet(l1, l2),
    ensures
        this.wf(),
)]
#[verifier::spinoff_prover]
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
// Extract reflexivity from the bundled `wf` predicate.
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
// Extract antisymmetry from the bundled `wf` predicate.
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
// Extract transitivity from the bundled `wf` predicate.
pub proof fn lemma_finite_lattice_transitive(
    this: FiniteLattice,
    lhs: LevelId,
    mid: LevelId,
    rhs: LevelId,
) {
}

/// A generic bounded lattice interface for information-flow labels.
pub trait SecurityLattice<Level: WellFormed + Copy + PartialEq>: WellFormed {
    spec fn valid_level(&self, level: Level) -> bool;

    spec fn bot(&self) -> Level;

    spec fn top(&self) -> Level;

    spec fn flows_to(&self, lhs: Level, rhs: Level) -> bool
        recommends
            self.wf(),
            self.valid_level(lhs),
            self.valid_level(rhs),
    ;

    spec fn join(&self, lhs: Level, rhs: Level) -> Level
        recommends
            self.wf(),
            self.valid_level(lhs),
            self.valid_level(rhs),
    ;

    spec fn meet(&self, lhs: Level, rhs: Level) -> Level
        recommends
            self.wf(),
            self.valid_level(lhs),
            self.valid_level(rhs),
    ;

    // Every valid label must flow to itself.
    proof fn lemma_reflexive(&self, level: Level)
        requires
            self.wf(),
            self.valid_level(level),
        ensures
            self.flows_to(level, level),
    ;

    // Mutual flow can only happen between equal valid labels.
    proof fn lemma_antisymmetric(&self, lhs: Level, rhs: Level)
        requires
            self.wf(),
            self.valid_level(lhs),
            self.valid_level(rhs),
        ensures
            self.flows_to(lhs, rhs) && self.flows_to(rhs, lhs) ==> lhs == rhs,
    ;

    // Flow is closed under composition on valid labels.
    proof fn lemma_transitive(&self, lhs: Level, mid: Level, rhs: Level)
        requires
            self.wf(),
            self.valid_level(lhs),
            self.valid_level(mid),
            self.valid_level(rhs),
        ensures
            self.flows_to(lhs, mid) && self.flows_to(mid, rhs) ==> self.flows_to(lhs, rhs),
    ;

    // The lattice exposes explicit bottom and top elements.
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

    // `join` is the least upper bound for any pair of valid labels.
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

    // `meet` is the greatest lower bound for any pair of valid labels.
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
    open spec fn valid_level(&self, level: LevelId) -> bool {
        FiniteLattice::valid_level(self, level)
    }

    open spec fn bot(&self) -> LevelId {
        self.bot
    }

    open spec fn top(&self) -> LevelId {
        self.top
    }

    open spec fn flows_to(&self, lhs: LevelId, rhs: LevelId) -> bool {
        self.flows_to_spec(lhs, rhs)
    }

    open spec fn join(&self, lhs: LevelId, rhs: LevelId) -> LevelId {
        choose|level: LevelId| self.valid_level(level) && self.is_join_of(lhs, rhs, level)
    }

    open spec fn meet(&self, lhs: LevelId, rhs: LevelId) -> LevelId {
        choose|level: LevelId| self.valid_level(level) && self.is_meet_of(lhs, rhs, level)
    }

    // Finite-lattice `wf` already packages reflexivity.
    proof fn lemma_reflexive(&self, level: LevelId) {
        assert(self.square());
        lemma_finite_lattice_reflexive(*self, level);
    }

    // Finite-lattice `wf` already packages antisymmetry.
    proof fn lemma_antisymmetric(&self, lhs: LevelId, rhs: LevelId) {
        assert(self.square());
        assert(self.flows_to(lhs, rhs) && self.flows_to(rhs, lhs) ==> lhs == rhs) by {
            if self.flows_to(lhs, rhs) && self.flows_to(rhs, lhs) {
                lemma_finite_lattice_antisymmetric(*self, lhs, rhs);
            }
        }
    }

    // Finite-lattice `wf` already packages transitivity.
    proof fn lemma_transitive(&self, lhs: LevelId, mid: LevelId, rhs: LevelId) {
        assert(self.square());
        assert(self.flows_to(lhs, mid) && self.flows_to(mid, rhs) ==> self.flows_to(lhs, rhs)) by {
            if self.flows_to(lhs, mid) && self.flows_to(mid, rhs) {
                lemma_finite_lattice_transitive(*self, lhs, mid, rhs);
            }
        }
    }

    // Bottom and top are explicit fields whose order properties are included in `wf`.
    proof fn lemma_bot_top(&self, level: LevelId) {
        assert(self.flows_to(self.bot(), level));
        assert(self.flows_to(level, self.top()));
    }

    // Joins exist for every valid pair by `wf`, and the chosen witness satisfies the LUB laws.
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

    // Meets exist for every valid pair by `wf`, and the chosen witness satisfies the GLB laws.
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

#[verus_spec(r =>
    ensures
        valid_upgrade::<Level, L>(lattice, from, to) ==> lattice.flows_to(from, to),
)]
// Expand the helper predicate back into the underlying lattice flow relation.
pub proof fn lemma_valid_upgrade_sound<
    Level: WellFormed + Copy + PartialEq,
    L: SecurityLattice<Level>,
>(lattice: &L, from: Level, to: Level) {
    assert(valid_upgrade::<Level, L>(lattice, from, to) ==> lattice.flows_to(from, to))
        by (compute);
}

#[verus_spec(r =>
    ensures
        valid_downgrade::<Level, L>(lattice, from, to, has_declassifier) ==> has_declassifier
            && lattice.flows_to(to, from),
)]
// Expand downgrade validity into its two concrete obligations.
pub proof fn lemma_valid_downgrade_sound<
    Level: WellFormed + Copy + PartialEq,
    L: SecurityLattice<Level>,
>(lattice: &L, from: Level, to: Level, has_declassifier: bool) {
    assert(valid_downgrade::<Level, L>(lattice, from, to, has_declassifier) ==> has_declassifier
        && lattice.flows_to(to, from)) by (compute);
}

} // verus!
#[cfg(feature = "alloc")]
impl fmt::Display for FiniteLatticeBuildError {
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
