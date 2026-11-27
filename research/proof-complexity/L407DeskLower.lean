import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Data.Finsupp.Encodable
import PEqualNP.Defs
import Mathlib.FieldTheory.Finite.Polynomial

-- Accepted project source: PEqualNP.ProofComplexity.Helpers.ExpanderGraph
/-!
# Helpers: the permutation model of a bounded-degree bipartite graph (for L-pcx-043)

`b` permutations of `Fin (n+1)` give a bipartite graph with `n+1` pigeons and `n` holes:
pigeon `i` is joined to hole `j` when some permutation sends `i` to `j` (the extra point
`Fin.last n` is dropped). Every pigeon then has at most `b` holes and every hole at most `b`
pigeons. L-pcx-043 shows by counting that some choice of `b = 8` permutations is a boundary
expander.

The interface statements of the counting proof are recorded here as `Prop` definitions so
that the parts can be proved separately and assembled.
-/

namespace PEqualNP.ProofComplexity.Helpers

open PEqualNP.Expanders

/-- The bipartite graph of `b` permutations of `Fin (n+1)`, the point `Fin.last n` dropped. -/
def permGraph {n b : ℕ} (σ : Fin b → Equiv.Perm (Fin (n + 1))) : BipGraph (n + 1) n :=
  fun i => Finset.univ.filter (fun j : Fin n => ∃ k, σ k i = j.castSucc)

/-- The permutation count (an upper bound suffices): the permutations of a finite type that
map `T` into `Y`. -/
def PermCountStmt : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (T Y : Finset α),
    (Finset.univ.filter (fun σ : Equiv.Perm α => ∀ x ∈ T, σ x ∈ Y)).card ≤
      Y.card.descFactorial T.card * (Fintype.card α - T.card).factorial

/-- The union bound is below one: for some `s₀ ≥ 5`, for all large `n`, the expected number of
left sets of size `1 ≤ t ≤ n / s₀` whose 8 images all lie in one set of `5 t` points is
below one. -/
def ArithStmt : Prop :=
  ∃ s₀ n₀ : ℕ, 5 ≤ s₀ ∧ ∀ n : ℕ, n₀ ≤ n →
    ∑ t ∈ Finset.Icc 1 (n / s₀),
      ((n + 1).choose t : ℝ) * ((n + 1).choose (5 * t) : ℝ) *
        (((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ)) ^ 8 < 1

end PEqualNP.ProofComplexity.Helpers

-- Accepted project source: PEqualNP.ProofComplexity.Helpers.ExpanderDet
/-!
# Helpers: deterministic facts about the permutation graph (for L-pcx-043)

* `permGraph_leftDegLe`, `permGraph_rightDegLe`: the graph of `b` permutations has left and
  right degree at most `b`.
* `permGraph_trap`: if a left set `T` (with `5 |T| ≤ n + 1`) of the graph of 8 permutations has
  fewer than `2 |T|` unique neighbours, then all 8 images of `T` lie in one set of exactly
  `5 |T|` points. Counting edges by holes: `|unique| ≥ 2 |N| - 8 |T|` for the neighbourhood
  `N`, so `|N| < 5 |T|`, and the images lie in `N` together with the dropped point.
-/

namespace PEqualNP.ProofComplexity.Helpers

open PEqualNP.Expanders

theorem permGraph_leftDegLe {n b : ℕ} (σ : Fin b → Equiv.Perm (Fin (n + 1))) :
    PEqualNP.Expanders.LeftDegLe (permGraph σ) b := by
  intro i
  have hsub : (permGraph σ i).map Fin.castSuccEmb ⊆ Finset.univ.image (fun k => σ k i) := by
    intro x hx
    simp only [Finset.mem_map, permGraph, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.coe_castSuccEmb] at hx
    obtain ⟨j, ⟨k, hk⟩, rfl⟩ := hx
    exact Finset.mem_image.2 ⟨k, Finset.mem_univ _, hk⟩
  calc (permGraph σ i).card = ((permGraph σ i).map Fin.castSuccEmb).card := (Finset.card_map _).symm
    _ ≤ (Finset.univ.image (fun k => σ k i)).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin b)).card := Finset.card_image_le
    _ = b := by simp

theorem permGraph_rightDegLe {n b : ℕ} (σ : Fin b → Equiv.Perm (Fin (n + 1))) :
    PEqualNP.Expanders.RightDegLe (permGraph σ) b := by
  intro j
  have hsub : rightNbrs (permGraph σ) j ⊆
      Finset.univ.image (fun k => (σ k).symm j.castSucc) := by
    intro i hi
    simp only [rightNbrs, permGraph, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨k, hk⟩ := hi
    exact Finset.mem_image.2 ⟨k, Finset.mem_univ _, by rw [← hk]; simp⟩
  calc (rightNbrs (permGraph σ) j).card
      ≤ (Finset.univ.image (fun k => (σ k).symm j.castSucc)).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin b)).card := Finset.card_image_le
    _ = b := by simp

theorem permGraph_trap {n : ℕ} (σ : Fin 8 → Equiv.Perm (Fin (n + 1))) (T : Finset (Fin (n + 1)))
    (hT : 5 * T.card ≤ n + 1)
    (hbad : (PEqualNP.Expanders.uniqueNbrs (permGraph σ) T).card < 2 * T.card) :
    ∃ Y : Finset (Fin (n + 1)), Y.card = 5 * T.card ∧ ∀ k, ∀ x ∈ T, σ k x ∈ Y := by
  set G := permGraph σ with hG
  set N := T.biUnion G with hN
  set U := uniqueNbrs G T with hU
  -- edges counted by holes
  have he : ∑ i ∈ T, (G i).card = ∑ j ∈ N, (T.filter (fun i => j ∈ G i)).card := by
    have h1 : ∀ i ∈ T, (G i).card = ∑ j ∈ N, if j ∈ G i then 1 else 0 := by
      intro i hi
      rw [← Finset.card_filter]
      congr 1
      ext j
      simp only [Finset.mem_filter, hN, Finset.mem_biUnion]
      exact ⟨fun h => ⟨⟨i, hi, h⟩, h⟩, fun h => h.2⟩
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.card_filter]
  have hle8 : ∑ i ∈ T, (G i).card ≤ 8 * T.card := by
    have := Finset.sum_le_card_nsmul T (fun i => (G i).card) 8
      (fun i _ => permGraph_leftDegLe σ i)
    simpa [mul_comm] using this
  have hpt : ∀ j ∈ N, 2 ≤ (T.filter (fun i => j ∈ G i)).card + if j ∈ U then 1 else 0 := by
    intro j hj
    have hpos : 0 < (T.filter (fun i => j ∈ G i)).card := by
      rw [hN, Finset.mem_biUnion] at hj
      obtain ⟨i, hi, hji⟩ := hj
      exact Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨hi, hji⟩⟩
    by_cases h1 : (T.filter (fun i => j ∈ G i)).card = 1
    · have : j ∈ U := by
        simp only [hU, uniqueNbrs, Finset.mem_filter, Finset.mem_univ, true_and]
        exact h1
      simp [this, h1]
    · split_ifs <;> omega
  have hsum : 2 * N.card ≤ ∑ i ∈ T, (G i).card + U.card := by
    have h2 : ∑ j ∈ N, 2 ≤ ∑ j ∈ N,
        ((T.filter (fun i => j ∈ G i)).card + if j ∈ U then 1 else 0) :=
      Finset.sum_le_sum hpt
    rw [Finset.sum_add_distrib, ← Finset.card_filter, ← he] at h2
    have h3 : (N.filter (fun j => j ∈ U)).card ≤ U.card :=
      Finset.card_le_card (fun j hj => (Finset.mem_filter.1 hj).2)
    simp only [Finset.sum_const, smul_eq_mul] at h2
    omega
  have hNc : N.card + 1 ≤ 5 * T.card := by omega
  set Y0 := N.map Fin.castSuccEmb ∪ {Fin.last n} with hY0
  have hY0c : Y0.card ≤ 5 * T.card := by
    calc Y0.card ≤ (N.map Fin.castSuccEmb).card + ({Fin.last n} : Finset _).card :=
          Finset.card_union_le _ _
      _ = N.card + 1 := by simp
      _ ≤ 5 * T.card := hNc
  obtain ⟨Y, hY0Y, hYc⟩ := Finset.exists_superset_card_eq hY0c (by simpa using hT)
  refine ⟨Y, hYc, fun k x hx => hY0Y ?_⟩
  induction h : σ k x using Fin.lastCases with
  | last => simp [hY0]
  | cast j =>
    have hj : j ∈ N := by
      rw [hN, Finset.mem_biUnion]
      refine ⟨x, hx, ?_⟩
      simp only [hG, permGraph, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨k, h⟩
    simp only [hY0, Finset.mem_union, Finset.mem_map, Fin.coe_castSuccEmb]
    exact Or.inl ⟨j, hj, rfl⟩

end PEqualNP.ProofComplexity.Helpers

-- Accepted project source: PEqualNP.ProofComplexity.Helpers.ExpanderPerm
/-!
# Counting permutations that map a set into a set

`permCount` proves `PermCountStmt`: the number of permutations of a finite type sending every
point of `T` into `Y` is at most `Y.card.descFactorial T.card * (card α - T.card)!`.

Proof: restrict each such permutation to `T`; the restriction is an injection `T → Y`, of which
there are `Y.card.descFactorial T.card`. Two permutations with the same restriction differ by a
permutation fixing `T` pointwise, and those are the permutations of the complement of `T`.
-/

namespace PEqualNP.ProofComplexity.Helpers

open Finset

theorem permCount : PermCountStmt := by
  intro α _ _ T Y
  classical
  set S := Finset.univ.filter (fun σ : Equiv.Perm α => ∀ x ∈ T, σ x ∈ Y) with hS
  let f : Equiv.Perm α → (T → α) := fun σ x => σ x
  let t : Finset (T → α) :=
    Finset.univ.filter (fun g => Function.Injective g ∧ ∀ x, g x ∈ Y)
  have hmaps : ∀ σ ∈ S, f σ ∈ t := by
    intro σ hσ
    simp only [hS, mem_filter, mem_univ, true_and] at hσ
    simp only [t, mem_filter, mem_univ, true_and]
    refine ⟨?_, fun x => hσ x.1 x.2⟩
    intro a b hab
    exact Subtype.ext (σ.injective hab)
  -- the target has at most `descFactorial` elements
  have ht : #t ≤ Y.card.descFactorial T.card := by
    have hinj : Function.Injective
        (fun g : t => (⟨fun x => ⟨g.1 x, ((mem_filter.mp g.2).2.2 x)⟩,
          fun a b hab => (mem_filter.mp g.2).2.1 (congrArg Subtype.val hab)⟩ : T ↪ Y)) := by
      intro g h hgh
      apply Subtype.ext
      funext x
      exact congrArg Subtype.val (DFunLike.congr_fun hgh x)
    have := Fintype.card_le_of_injective _ hinj
    rw [Fintype.card_embedding_eq] at this
    simpa using this
  -- each fiber has at most `(card α - card T)!` elements
  have hfib : ∀ g ∈ t, #{σ ∈ S | f σ = g} ≤ (Fintype.card α - T.card).factorial := by
    intro g _
    rcases Finset.eq_empty_or_nonempty {σ ∈ S | f σ = g} with h | ⟨σ₀, hσ₀⟩
    · rw [h]; simp
    have hσ₀g : f σ₀ = g := (mem_filter.mp hσ₀).2
    let P := {τ : Equiv.Perm α // ∀ a, ¬ (a ∉ T) → τ a = a}
    have hcardP : Fintype.card P = (Fintype.card α - T.card).factorial := by
      rw [← Fintype.card_congr (Equiv.Perm.subtypeEquivSubtypePerm (fun a => a ∉ T)),
        Fintype.card_perm]
      congr 1
      rw [Fintype.card_subtype_compl, Fintype.card_coe]
    let F : {σ // σ ∈ ({σ ∈ S | f σ = g} : Finset _)} → P := fun σ =>
      ⟨σ₀⁻¹ * σ.1, by
        intro a ha
        have ha' : a ∈ T := not_not.mp ha
        have h1 : f σ.1 = g := (mem_filter.mp σ.2).2
        have h2 : σ.1 a = σ₀ a := by
          have e := congrFun (h1.trans hσ₀g.symm) ⟨a, ha'⟩
          simpa [f] using e
        simp [Equiv.Perm.mul_apply, h2]⟩
    have hF : Function.Injective F := by
      intro a b hab
      apply Subtype.ext
      have := congrArg Subtype.val hab
      simpa [F] using this
    have := Fintype.card_le_of_injective F hF
    rw [hcardP, Fintype.card_coe] at this
    exact this
  have := Finset.card_le_mul_card_image_of_maps_to hmaps _ hfib
  calc #S ≤ (Fintype.card α - T.card).factorial * #t := this
    _ ≤ (Fintype.card α - T.card).factorial * Y.card.descFactorial T.card :=
        Nat.mul_le_mul_left _ ht
    _ = _ := Nat.mul_comm _ _

end PEqualNP.ProofComplexity.Helpers

-- Accepted project source: PEqualNP.ProofComplexity.Helpers.ExpanderArith
/-!
# Helpers: the arithmetic of the expander union bound (for L-pcx-043)

`ArithStmt` holds with `s₀ = 100000` and `n₀ = 0`. With `N = n + 1` and `1 ≤ t ≤ n / s₀`:
`C(N, r) ≤ (3 N / r)^r` (from `N^r / r!` and `r^r / r! ≤ e^r < 3^r`), the falling factorial
ratio is at most `(10 t / N)^t`, so each term is at most `(23328000 t^2 / N^2)^t ≤ (1/4)^t`,
and the geometric sum from `1` is at most `1/3`.
-/

namespace PEqualNP.ProofComplexity.Helpers

open Finset

/-- A crude binomial bound: `C(N, r) ≤ (3 N / r)^r` for `r ≥ 1`. -/
lemma arith_choose_le (N r : ℕ) (hr : 0 < r) : (N.choose r : ℝ) ≤ (3 * N / r) ^ r := by
  have h1 : (N.choose r : ℝ) ≤ (N : ℝ) ^ r / r.factorial := Nat.choose_le_pow_div r N
  have h2 : (r : ℝ) ^ r / r.factorial ≤ Real.exp r :=
    Real.pow_div_factorial_le_exp (r : ℝ) (by positivity) r
  have h3 : Real.exp r ≤ 3 ^ r := by
    have : Real.exp (r : ℝ) = Real.exp 1 ^ r := by rw [← Real.exp_nat_mul]; simp
    rw [this]
    gcongr
    linarith [Real.exp_one_lt_d9]
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hf : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hrr : (0 : ℝ) < (r : ℝ) ^ r := by positivity
  calc (N.choose r : ℝ) ≤ (N : ℝ) ^ r / r.factorial := h1
    _ = (N : ℝ) ^ r / (r : ℝ) ^ r * ((r : ℝ) ^ r / r.factorial) := by field_simp
    _ ≤ (N : ℝ) ^ r / (r : ℝ) ^ r * 3 ^ r := by gcongr; exact h2.trans h3
    _ = (3 * N / r) ^ r := by rw [div_pow, mul_pow]; ring

/-- The falling factorial ratio: for `1 ≤ t` and `2 t ≤ N`, it is at most `(10 t / N)^t`. -/
lemma arith_ratio_le (N t : ℕ) (ht : 1 ≤ t) (hN : 2 * t ≤ N) :
    ((5 * t).descFactorial t : ℝ) / (N.descFactorial t : ℝ) ≤ (10 * t / N) ^ t := by
  have hnum : ((5 * t).descFactorial t : ℝ) ≤ ((5 * t : ℕ) : ℝ) ^ t := by
    exact_mod_cast Nat.descFactorial_le_pow _ _
  have hden0 : ((N + 1 - t : ℕ) : ℝ) ^ t ≤ (N.descFactorial t : ℝ) := by
    exact_mod_cast Nat.pow_sub_le_descFactorial N t
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hsub : (N : ℝ) / 2 ≤ ((N + 1 - t : ℕ) : ℝ) := by
    have hle : t ≤ N + 1 := by omega
    rw [Nat.cast_sub hle]
    have : (2 * t : ℝ) ≤ N := by exact_mod_cast hN
    push_cast
    linarith
  have hden : ((N : ℝ) / 2) ^ t ≤ (N.descFactorial t : ℝ) :=
    (pow_le_pow_left₀ (by positivity) hsub t).trans hden0
  calc ((5 * t).descFactorial t : ℝ) / (N.descFactorial t : ℝ)
      ≤ ((5 * t : ℕ) : ℝ) ^ t / ((N : ℝ) / 2) ^ t :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = (10 * t / N) ^ t := by
        rw [← div_pow]
        congr 1
        push_cast
        field_simp
        ring

/-- Each term of the union bound is at most `(1/4)^t` when `100000 t ≤ n`. -/
lemma arith_term_le (n t : ℕ) (ht : 1 ≤ t) (hts : t * 100000 ≤ n) :
    ((n + 1).choose t : ℝ) * ((n + 1).choose (5 * t) : ℝ) *
        (((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ)) ^ 8 ≤
      (1 / 4 : ℝ) ^ t := by
  have htpos : (0 : ℝ) < t := by
    have : 0 < t := by omega
    exact_mod_cast this
  have hN : ((n + 1 : ℕ) : ℝ) ≥ 100000 * t := by
    have : t * 100000 ≤ n + 1 := by omega
    have h : ((t * 100000 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h ⊢
    linarith
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have h1 := arith_choose_le (n + 1) t (by omega)
  have h2 := arith_choose_le (n + 1) (5 * t) (by omega)
  have h3 := arith_ratio_le (n + 1) t ht (by omega)
  set N : ℝ := ((n + 1 : ℕ) : ℝ) with hNdef
  have hratio0 : (0 : ℝ) ≤ ((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ) := by
    positivity
  have h5 : ((5 * t : ℕ) : ℝ) = 5 * (t : ℝ) := by push_cast; ring
  rw [h5] at h2
  have hbase : (3 * N / t) * (3 * N / (5 * t)) ^ 5 * (10 * t / N) ^ 8 = 23328000 * t ^ 2 / N ^ 2 := by
    field_simp
    ring
  have hq : (23328000 : ℝ) * t ^ 2 / N ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hq0 : (0 : ℝ) ≤ (3 * N / t) * (3 * N / (5 * t)) ^ 5 * (10 * t / N) ^ 8 := by positivity
  calc ((n + 1).choose t : ℝ) * ((n + 1).choose (5 * t) : ℝ) *
        (((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ)) ^ 8
      ≤ (3 * N / t) ^ t * (3 * N / (5 * t)) ^ (5 * t) * ((10 * t / N) ^ t) ^ 8 := by
        gcongr
    _ = ((3 * N / t) * (3 * N / (5 * t)) ^ 5 * (10 * t / N) ^ 8) ^ t := by
        rw [pow_mul (3 * N / (5 * t)) 5 t, ← pow_mul (10 * t / N) t 8, mul_comm t 8,
          pow_mul (10 * t / N) 8 t, mul_pow, mul_pow]
    _ ≤ (1 / 4 : ℝ) ^ t := by
        rw [hbase] at hq0 ⊢
        exact pow_le_pow_left₀ hq0 hq t

/-- The union bound of L-pcx-043 is below one, with `s₀ = 100000` and `n₀ = 0`. -/
theorem arith : ArithStmt := by
  refine ⟨100000, 0, by norm_num, fun n _ => ?_⟩
  calc ∑ t ∈ Finset.Icc 1 (n / 100000),
        ((n + 1).choose t : ℝ) * ((n + 1).choose (5 * t) : ℝ) *
          (((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ)) ^ 8
      ≤ ∑ t ∈ Finset.Icc 1 (n / 100000), (1 / 4 : ℝ) ^ t := by
        apply Finset.sum_le_sum
        intro t ht
        rw [Finset.mem_Icc] at ht
        exact arith_term_le n t ht.1 ((Nat.le_div_iff_mul_le (by norm_num)).1 ht.2)
    _ = ∑ t ∈ Finset.Ico 1 (n / 100000 + 1), (1 / 4 : ℝ) ^ t := by
        rw [Finset.Ico_add_one_right_eq_Icc]
    _ ≤ (1 / 4 : ℝ) ^ 1 / (1 - 1 / 4) := geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
    _ < 1 := by norm_num

end PEqualNP.ProofComplexity.Helpers

-- Accepted project source: PEqualNP.ProofComplexity.Helpers.ExpanderAssembly
/-!
# Helpers: assembling L-pcx-043 from its parts

The counting union bound. With `b = 8` permutations, a choice `σ` is bad when some left set
`T` of at most `n / s₀` pigeons has fewer than `2 |T|` unique neighbours. The deterministic
lemma (hypothesis `hT`) traps all 8 images of such a `T` in a set `Y` of `5 |T|` points; the
permutation count (`PermCountStmt`) bounds the choices trapping `T` in `Y`, and the arithmetic
(`ArithStmt`) shows the union bound is below the number of all choices. So some choice is good.
-/

namespace PEqualNP.ProofComplexity.Helpers

open PEqualNP.Expanders

theorem expander_of_parts (hP : PermCountStmt) (hA : ArithStmt)
    (hL : ∀ {n b : ℕ} (σ : Fin b → Equiv.Perm (Fin (n + 1))),
      PEqualNP.Expanders.LeftDegLe (permGraph σ) b)
    (hR : ∀ {n b : ℕ} (σ : Fin b → Equiv.Perm (Fin (n + 1))),
      PEqualNP.Expanders.RightDegLe (permGraph σ) b)
    (hT : ∀ {n : ℕ} (σ : Fin 8 → Equiv.Perm (Fin (n + 1))) (T : Finset (Fin (n + 1))),
      5 * T.card ≤ n + 1 →
      (PEqualNP.Expanders.uniqueNbrs (permGraph σ) T).card < 2 * T.card →
      ∃ Y : Finset (Fin (n + 1)), Y.card = 5 * T.card ∧ ∀ k, ∀ x ∈ T, σ k x ∈ Y) :
    ∃ (b s₀ n₀ : ℕ), 0 < s₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      ∃ G : PEqualNP.Expanders.BipGraph (n + 1) n,
        PEqualNP.Expanders.LeftDegLe G b ∧ PEqualNP.Expanders.RightDegLe G b ∧
        PEqualNP.Expanders.IsBdryExpander G (n / s₀) 2 := by
  classical
  obtain ⟨s₀, n₀, h5, hsum⟩ := hA
  refine ⟨8, s₀, n₀, by omega, ?_⟩
  intro n hn
  have hs1 := hsum n hn
  have hsn : 5 * (n / s₀) ≤ n := by
    have h1 := Nat.div_mul_le_self n s₀
    have h2 : 5 * (n / s₀) ≤ n / s₀ * s₀ := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_left (n / s₀) h5
    omega
  set s := n / s₀ with hs
  suffices h : ∃ σ : Fin 8 → Equiv.Perm (Fin (n + 1)), IsBdryExpander (permGraph σ) s 2 by
    obtain ⟨σ, hσ⟩ := h
    exact ⟨permGraph σ, hL σ, hR σ, hσ⟩
  by_contra hno
  push Not at hno
  -- the permutations trapping `T` in `Y`
  let A : Finset (Fin (n + 1)) → Finset (Fin (n + 1)) → Finset (Equiv.Perm (Fin (n + 1))) :=
    fun T Y => Finset.univ.filter (fun τ => ∀ x ∈ T, τ x ∈ Y)
  let U : Finset (Fin 8 → Equiv.Perm (Fin (n + 1))) :=
    (Finset.Icc 1 s).biUnion (fun t =>
      (Finset.powersetCard t (Finset.univ : Finset (Fin (n + 1)))).biUnion (fun T =>
        (Finset.powersetCard (5 * t) (Finset.univ : Finset (Fin (n + 1)))).biUnion (fun Y =>
          Fintype.piFinset (fun _ : Fin 8 => A T Y))))
  have hsub : (Finset.univ : Finset (Fin 8 → Equiv.Perm (Fin (n + 1)))) ⊆ U := by
    intro σ _
    have hbad := hno σ
    unfold IsBdryExpander at hbad
    push Not at hbad
    obtain ⟨T, hTs, hTlt⟩ := hbad
    have ht1 : 1 ≤ T.card := by
      rcases Nat.eq_zero_or_pos T.card with h0 | h0
      · rw [h0] at hTlt; omega
      · exact h0
    obtain ⟨Y, hYc, hY⟩ := hT σ T (by omega) hTlt
    simp only [U, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_powersetCard,
      Fintype.mem_piFinset]
    refine ⟨T.card, ⟨ht1, hTs⟩, T, ⟨Finset.subset_univ _, rfl⟩, Y,
      ⟨Finset.subset_univ _, hYc⟩, ?_⟩
    intro k
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun x hx => hY k x hx
  have hAcard : ∀ t, ∀ T ∈ Finset.powersetCard t (Finset.univ : Finset (Fin (n + 1))),
      ∀ Y ∈ Finset.powersetCard (5 * t) (Finset.univ : Finset (Fin (n + 1))),
      (A T Y).card ≤ (5 * t).descFactorial t * (n + 1 - t).factorial := by
    intro t T hT' Y hY'
    rw [Finset.mem_powersetCard] at hT' hY'
    have h := hP (Fin (n + 1)) T Y
    rw [hT'.2, hY'.2, Fintype.card_fin] at h
    convert h
  have hUcard : U.card ≤ ∑ t ∈ Finset.Icc 1 s, (n + 1).choose t * ((n + 1).choose (5 * t) *
      ((5 * t).descFactorial t * (n + 1 - t).factorial) ^ 8) := by
    refine (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun t _ => ?_)
    refine (Finset.card_biUnion_le).trans ?_
    calc _ ≤ ∑ T ∈ Finset.powersetCard t (Finset.univ : Finset (Fin (n + 1))),
          (n + 1).choose (5 * t) * ((5 * t).descFactorial t * (n + 1 - t).factorial) ^ 8 := by
          apply Finset.sum_le_sum
          intro T hT'
          refine (Finset.card_biUnion_le).trans ?_
          calc _ ≤ ∑ Y ∈ Finset.powersetCard (5 * t) (Finset.univ : Finset (Fin (n + 1))),
                ((5 * t).descFactorial t * (n + 1 - t).factorial) ^ 8 := by
                apply Finset.sum_le_sum
                intro Y hY'
                rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
                exact Nat.pow_le_pow_left (hAcard t T hT' Y hY') 8
            _ = _ := by
                rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
                  Fintype.card_fin, smul_eq_mul]
      _ = _ := by
          rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
            Fintype.card_fin, smul_eq_mul]
  have hcardΩ : (Finset.univ : Finset (Fin 8 → Equiv.Perm (Fin (n + 1)))).card =
      ((n + 1).factorial) ^ 8 := by
    rw [Finset.card_univ, Fintype.card_pi, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Fintype.card_perm, Fintype.card_fin]
  have hle : ((n + 1).factorial) ^ 8 ≤ ∑ t ∈ Finset.Icc 1 s, (n + 1).choose t *
      ((n + 1).choose (5 * t) * ((5 * t).descFactorial t * (n + 1 - t).factorial) ^ 8) :=
    hcardΩ ▸ (Finset.card_le_card hsub).trans hUcard
  have hleR : (((n + 1).factorial : ℕ) : ℝ) ^ 8 ≤ ∑ t ∈ Finset.Icc 1 s,
      ((n + 1).choose t : ℝ) * (((n + 1).choose (5 * t) : ℝ) *
        (((5 * t).descFactorial t : ℝ) * ((n + 1 - t).factorial : ℝ)) ^ 8) := by
    exact_mod_cast hle
  have hid : ∑ t ∈ Finset.Icc 1 s,
      ((n + 1).choose t : ℝ) * (((n + 1).choose (5 * t) : ℝ) *
        (((5 * t).descFactorial t : ℝ) * ((n + 1 - t).factorial : ℝ)) ^ 8) =
      (((n + 1).factorial : ℕ) : ℝ) ^ 8 * ∑ t ∈ Finset.Icc 1 s,
        ((n + 1).choose t : ℝ) * ((n + 1).choose (5 * t) : ℝ) *
          (((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ)) ^ 8 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_Icc] at ht
    have htn : t ≤ n + 1 := by omega
    have hEF : ((n + 1 - t).factorial : ℝ) * ((n + 1).descFactorial t : ℝ) =
        (((n + 1).factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_mul_descFactorial htn
    have hE : ((n + 1).descFactorial t : ℝ) ≠ 0 := by
      have : (n + 1).descFactorial t ≠ 0 := by
        rw [Ne, Nat.descFactorial_eq_zero_iff_lt]; omega
      exact_mod_cast this
    rw [← hEF]
    field_simp
  have hpos : (0 : ℝ) < (((n + 1).factorial : ℕ) : ℝ) ^ 8 := by
    have := Nat.factorial_pos (n + 1)
    positivity
  have hlt := mul_lt_mul_of_pos_left hs1 hpos
  rw [hid] at hleR
  linarith

end PEqualNP.ProofComplexity.Helpers

-- Accepted project source: PEqualNP.ProofComplexity.L043
namespace PEqualNP.ProofComplexity

/-- L-pcx-043: bounded-degree bipartite boundary expanders with `n + 1` pigeons and `n` holes
exist for all large `n`, by counting over 8 random permutations. -/
theorem L043 : ∃ (b s₀ n₀ : ℕ), 0 < s₀ ∧ ∀ n : ℕ, n₀ ≤ n → ∃ G : PEqualNP.Expanders.BipGraph (n + 1) n, PEqualNP.Expanders.LeftDegLe G b ∧ PEqualNP.Expanders.RightDegLe G b ∧ PEqualNP.Expanders.IsBdryExpander G (n / s₀) 2 :=
  Helpers.expander_of_parts Helpers.permCount Helpers.arith
    (fun σ => Helpers.permGraph_leftDegLe σ) (fun σ => Helpers.permGraph_rightDegLe σ)
    (fun σ T hT hbad => Helpers.permGraph_trap σ T hT hbad)

end PEqualNP.ProofComplexity

-- Accepted project source: PEqualNP.ProofComplexity.Helpers.PCToolkit
/-!
# Helpers: a toolkit for polynomial calculus over the two-element field

Basic facts about `PCDerivable`:

* `pcDerivable_mono`: more axioms and a larger degree bound keep derivations;
* `pcDerivable_mul_left`: a derived line may be multiplied by any polynomial `q`, at the
  cost of raising the degree bound to `q.totalDegree + g.totalDegree`;
* `pcDerivable_eval_eq_zero`, `pcRefutable_no_common_zero`: soundness;
* `pcDerivable_replay`: a substitution of polynomials of degree at most `T` for the
  variables, together with a multiplier `w` of degree at most `s`, turns a derivation of
  degree `D` into one of degree `T * D + s`, as soon as the images of the axioms are
  derivable;
* `bitPHPSystem_injective`, `bitPHPSystem_no_common_zero`: the common zeros of the bit
  pigeonhole system are the injective maps from pigeons to holes.
-/

namespace PEqualNP.ProofComplexity.Helpers

open MvPolynomial

variable {σ τ : Type}

/-- Monotonicity of polynomial calculus in the axioms and in the degree bound. -/
theorem pcDerivable_mono {F F' : Set (MvPolynomial σ (ZMod 2))} {B B' : ℕ}
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F B p) (hB : B ≤ B') (hF : F ⊆ F') :
    PCDerivable F' B' p := by
  induction h with
  | ax hp hdeg => exact .ax (hF hp) (hdeg.trans hB)
  | zero => exact .zero
  | add _ _ ih1 ih2 => exact .add ih1 ih2
  | mulX j _ hdeg ih => exact .mulX j ih (hdeg.trans hB)

/-- Multiplication of a derived line by a monomial, inside a fixed degree bound. -/
theorem pcDerivable_monomial_mul {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    (a : σ →₀ ℕ) : ∀ {g : MvPolynomial σ (ZMod 2)}, PCDerivable F B g →
      (a.sum fun _ e => e) + g.totalDegree ≤ B → PCDerivable F B (monomial a 1 * g) := by
  induction a using Finsupp.induction_linear with
  | zero =>
    intro g hg _
    have : (monomial (0 : σ →₀ ℕ) (1 : ZMod 2)) = 1 := rfl
    rw [this, one_mul]
    exact hg
  | add a b iha ihb =>
    intro g hg hdeg
    have hsplit : monomial (a + b) (1 : ZMod 2) * g = monomial a 1 * (monomial b 1 * g) := by
      rw [← mul_assoc, monomial_mul_monomial, one_mul]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)] at hdeg
    have hb : (monomial b (1 : ZMod 2) * g).totalDegree
        ≤ (b.sum fun _ e => e) + g.totalDegree :=
      (totalDegree_mul _ _).trans (Nat.add_le_add_right (totalDegree_monomial_le b 1) _)
    rw [hsplit]
    exact iha (ihb hg (by omega)) (by omega)
  | single j n =>
    induction n with
    | zero =>
      intro g hg _
      have : (monomial (Finsupp.single j 0) (1 : ZMod 2)) = 1 := by simp
      rw [this, one_mul]
      exact hg
    | succ n ih =>
      intro g hg hdeg
      have hsplit : monomial (Finsupp.single j (n + 1)) (1 : ZMod 2) * g
          = X j * (monomial (Finsupp.single j n) 1 * g) := by
        rw [← mul_assoc, X, monomial_mul_monomial, one_mul, ← Finsupp.single_add,
          add_comm 1 n]
      have hd1 : ((Finsupp.single j (n + 1)).sum fun _ e => e) = n + 1 :=
        Finsupp.sum_single_index rfl
      have hd2 : ((Finsupp.single j n).sum fun _ e => e) = n :=
        Finsupp.sum_single_index rfl
      rw [hd1] at hdeg
      have hlow : (monomial (Finsupp.single j n) (1 : ZMod 2) * g).totalDegree
          ≤ n + g.totalDegree :=
        (totalDegree_mul _ _).trans (Nat.add_le_add_right
          ((totalDegree_monomial_le _ 1).trans_eq hd2) _)
      rw [hsplit]
      refine .mulX j (ih hg (by omega)) ?_
      refine (totalDegree_mul _ _).trans ?_
      have := totalDegree_X (R := ZMod 2) j
      omega

/-- Finite sums of derived lines are derived. -/
theorem pcDerivable_sum {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ} {ι : Type}
    (s : Finset ι) (f : ι → MvPolynomial σ (ZMod 2)) (h : ∀ i ∈ s, PCDerivable F B (f i)) :
    PCDerivable F B (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PCDerivable.zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact .add (h i (Finset.mem_insert_self i s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

/-- Multiplication of a derived line by an arbitrary polynomial: the degree bound grows to
at most the sum of the two degrees. -/
theorem pcDerivable_mul_left {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    {g : MvPolynomial σ (ZMod 2)} (hg : PCDerivable F B g) (q : MvPolynomial σ (ZMod 2)) :
    PCDerivable F (max B (q.totalDegree + g.totalDegree)) (q * g) := by
  have hg' : PCDerivable F (max B (q.totalDegree + g.totalDegree)) g :=
    pcDerivable_mono hg (le_max_left _ _) subset_rfl
  have hq : q * g = ∑ a ∈ q.support, monomial a (q.coeff a) * g := by
    conv_lhs => rw [q.as_sum]
    rw [Finset.sum_mul]
  rw [hq]
  refine pcDerivable_sum _ _ fun a ha => ?_
  have hc : q.coeff a = 1 := by
    have h0 : q.coeff a ≠ 0 := mem_support_iff.mp ha
    generalize q.coeff a = c at h0
    revert h0; revert c; decide
  rw [hc]
  refine pcDerivable_monomial_mul a hg' ?_
  have : (a.sum fun _ e => e) ≤ q.totalDegree := le_totalDegree ha
  exact (Nat.add_le_add_right this _).trans (le_max_right _ _)

/-- Soundness of polynomial calculus: a common zero of the axioms is a zero of every derived
line. -/
theorem pcDerivable_eval_eq_zero {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F B p) (a : σ → ZMod 2)
    (ha : ∀ f ∈ F, eval a f = 0) : eval a p = 0 := by
  induction h with
  | ax hp _ => exact ha _ hp
  | zero => simp
  | add _ _ ih1 ih2 => simp [ih1, ih2]
  | mulX j _ _ ih => simp [ih]

/-- A refutable system has no common zero. -/
theorem pcRefutable_no_common_zero {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    (h : PCRefutable F B) : ¬ ∃ a : σ → ZMod 2, ∀ f ∈ F, eval a f = 0 := by
  rintro ⟨a, ha⟩
  have := pcDerivable_eval_eq_zero h a ha
  simp at this

/-- A substitution of polynomials of degree at most `T` multiplies the degree by at most
`T`. -/
theorem totalDegree_bind₁_le (φ : σ → MvPolynomial τ (ZMod 2)) {T : ℕ}
    (hφ : ∀ j, (φ j).totalDegree ≤ T) (p : MvPolynomial σ (ZMod 2)) :
    (bind₁ φ p).totalDegree ≤ T * p.totalDegree := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine totalDegree_finsetSum_le fun a ha => ?_
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ a.support, (φ i ^ a i).totalDegree
      ≤ ∑ i ∈ a.support, T * a i := Finset.sum_le_sum fun i _ =>
        (totalDegree_pow _ _).trans (by rw [mul_comm]; exact Nat.mul_le_mul_right _ (hφ i))
    _ = T * ∑ i ∈ a.support, a i := by rw [Finset.mul_sum]
    _ ≤ T * p.totalDegree := Nat.mul_le_mul_left _ (le_totalDegree ha)

/-- Weighted replay of a derivation under a substitution. Let `φ` substitute polynomials of
degree at most `T` for the variables and let `w` be a multiplier of degree at most `s`. If
the image `w * bind₁ φ a` of every axiom `a` of degree at most `D` is derivable from `G` in
degree `T * D + s`, then so is the image of every line derivable from `F` in degree `D`. -/
theorem pcDerivable_replay {F : Set (MvPolynomial σ (ZMod 2))}
    {G : Set (MvPolynomial τ (ZMod 2))} {T D s : ℕ}
    (φ : σ → MvPolynomial τ (ZMod 2)) (hφ : ∀ j, (φ j).totalDegree ≤ T)
    (w : MvPolynomial τ (ZMod 2)) (hw : w.totalDegree ≤ s)
    (hax : ∀ a ∈ F, a.totalDegree ≤ D → PCDerivable G (T * D + s) (w * bind₁ φ a))
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F D p) :
    PCDerivable G (T * D + s) (w * bind₁ φ p) := by
  induction h with
  | ax hp hdeg => exact hax _ hp hdeg
  | zero => simpa using PCDerivable.zero
  | add _ _ ih1 ih2 =>
    rw [map_add, mul_add]
    exact .add ih1 ih2
  | @mulX j p _ hdeg ih =>
    by_cases hp0 : p = 0
    · subst hp0
      simpa using PCDerivable.zero
    have hXp : (X j * p).totalDegree = 1 + p.totalDegree := by
      rw [totalDegree_mul_of_isDomain (X_ne_zero j) hp0, totalDegree_X]
    have hrw : w * bind₁ φ (X j * p) = φ j * (w * bind₁ φ p) := by
      rw [map_mul, bind₁_X_right]
      ring
    rw [hrw]
    have hb := totalDegree_bind₁_le φ hφ p
    have hwb : (w * bind₁ φ p).totalDegree ≤ s + T * p.totalDegree :=
      (totalDegree_mul _ _).trans (Nat.add_le_add hw hb)
    have hbound : (φ j).totalDegree + (w * bind₁ φ p).totalDegree ≤ T * D + s := by
      have h1 : T * (1 + p.totalDegree) ≤ T * D :=
        Nat.mul_le_mul_left _ (hXp ▸ hdeg)
      have h2 := hφ j
      rw [mul_add, mul_one] at h1
      omega
    have := pcDerivable_mul_left ih (φ j)
    rwa [max_eq_left hbound] at this

/-- A common zero of the bit pigeonhole system sends different pigeons to different holes. -/
theorem bitPHPSystem_injective {m l : ℕ} (a : Fin m × Fin l → ZMod 2)
    (ha : ∀ f ∈ bitPHPSystem m l, eval a f = 0) :
    Function.Injective (fun (i : Fin m) (t : Fin l) => a (i, t)) := by
  intro i i' hii
  by_contra hne
  have h := ha _ (Or.inr ⟨i, i', hne, rfl⟩)
  rw [map_prod] at h
  obtain ⟨t, -, ht⟩ := Finset.prod_eq_zero_iff.mp h
  have hEq : a (i, t) = a (i', t) := congrFun hii t
  simp only [map_add, map_one, eval_X, hEq] at ht
  generalize a (i', t) = c at ht
  revert ht; revert c; decide

/-- With more pigeons than holes, the bit pigeonhole system has no common zero. -/
theorem bitPHPSystem_no_common_zero {m l : ℕ} (hml : 2 ^ l < m) :
    ¬ ∃ a : Fin m × Fin l → ZMod 2, ∀ f ∈ bitPHPSystem m l, eval a f = 0 := by
  rintro ⟨a, ha⟩
  have := Fintype.card_le_of_injective _ (bitPHPSystem_injective a ha)
  simp at this
  omega

end PEqualNP.ProofComplexity.Helpers

-- Accepted project source: PEqualNP.ProofComplexity.Helpers.PseudoReduction
/-!
# Helpers: the pseudo-reduction criterion for polynomial calculus degree lower bounds

`not_pcRefutable_of_pseudoReduction`: Razborov's criterion (1998). A linear operator `R` on
polynomials over `ZMod 2` that kills every axiom of degree at most `D`, that satisfies
`R (X v * m) = R (X v * R m)` for every monomial `m` of degree less than `D`, and that does
not kill `1`, witnesses that the system has no polynomial calculus refutation of degree `D`.
-/

namespace PEqualNP.ProofComplexity.Helpers

open MvPolynomial

/-- Razborov's pseudo-reduction criterion: a linear operator that kills the axioms of degree
at most `D`, commutes with multiplication by a variable in the sense
`R (X v * m) = R (X v * R m)` on monomials `m` of degree less than `D`, and does not kill
`1`, rules out a polynomial calculus refutation of degree `D`. -/
theorem not_pcRefutable_of_pseudoReduction {σ : Type}
    {F : Set (MvPolynomial σ (ZMod 2))} {D : ℕ}
    (R : MvPolynomial σ (ZMod 2) →ₗ[ZMod 2] MvPolynomial σ (ZMod 2))
    (hax : ∀ f ∈ F, f.totalDegree ≤ D → R f = 0)
    (hmul : ∀ (v : σ) (a : σ →₀ ℕ), a.degree + 1 ≤ D →
      R (X v * monomial a 1) = R (X v * R (monomial a 1)))
    (hone : R 1 ≠ 0) :
    ¬ PCRefutable F D := by
  -- The multiplication rule extends from monomials to linear combinations of them.
  have hsum : ∀ (v : σ) (s : Finset (σ →₀ ℕ)) (c : (σ →₀ ℕ) → ZMod 2),
      (∀ a ∈ s, a.degree + 1 ≤ D) →
      R (X v * ∑ a ∈ s, c a • monomial a 1) =
        R (X v * R (∑ a ∈ s, c a • monomial a 1)) := by
    intro v s c hs
    simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul]
    exact Finset.sum_congr rfl fun a ha => by rw [hmul v a (hs a ha)]
  have key : ∀ {p : MvPolynomial σ (ZMod 2)}, PCDerivable F D p → R p = 0 := by
    intro p h
    induction h with
    | ax hp hdeg => exact hax _ hp hdeg
    | zero => exact map_zero R
    | add _ _ ih1 ih2 => rw [map_add, ih1, ih2, add_zero]
    | @mulX j p _ hdeg ih =>
      by_cases hp0 : p = 0
      · rw [hp0, mul_zero, map_zero]
      · have hdeg' : p.totalDegree + 1 ≤ D := by
          rw [totalDegree_mul_of_isDomain (X_ne_zero j) hp0, totalDegree_X] at hdeg
          omega
        have hp : p = ∑ a ∈ p.support, p.coeff a • monomial a (1 : ZMod 2) := by
          conv_lhs => rw [p.as_sum]
          exact Finset.sum_congr rfl fun a _ => by rw [smul_monomial, smul_eq_mul, mul_one]
        have hs : ∀ a ∈ p.support, a.degree + 1 ≤ D := by
          intro a ha
          have h1 : a.degree ≤ p.totalDegree := le_totalDegree ha
          omega
        have h2 := hsum j p.support (fun a => p.coeff a) hs
        rw [← hp, ih, mul_zero, map_zero] at h2
        exact h2
  intro href
  exact hone (key href)

end PEqualNP.ProofComplexity.Helpers

-- Accepted project source: PEqualNP.ProofComplexity.Helpers.MomentReduction
/-!
# Helpers: reduction of the polynomial calculus degree bound for the functional pigeonhole
principle to a statement about moments of partial matchings

The file reduces the statement "the functional pigeonhole system has no polynomial calculus
refutation of degree `B` over `ZMod 2`" to a purely combinatorial statement, `MomentExt`,
about families of values in `ZMod 2` indexed by partial matchings.

* `staticSpan F k`: the linear span of the monomial multiples of the polynomials of `F` of
  total degree at most `k` (the static, Nullstellensatz style, closure in degree `k`).
* `pcDerivable_mem_staticSpan`: if `staticSpan F (k + 1)` meets the polynomials of degree at
  most `k` inside `staticSpan F k` for every `k < B`, every line derivable in degree `B` is in
  `staticSpan F B`.
* `IsPartialMatching`, `MomentConsistent`, `MomentExt`: the combinatorial notions.
* `momentFunctional z`: the linear functional attached to a family `z`; it vanishes on
  `staticSpan (funPHPSystem m N) k` when `z` is `k`-consistent
  (`momentFunctional_staticSpan`).
* `momentConsistent_of_dual`, `dual_eq_momentFunctional`: conversely, every linear functional
  that vanishes on the static span of degree `k` agrees, on polynomials of degree at most
  `k`, with the functional of a `k`-consistent family.
* `staticSpan_funPHP_inter`: the extension property `MomentExt m N k` gives the intersection
  property at level `k`.
* `no_pc_refutation_of_momentExt`: the reduction.
* `momentExt_zero`, `not_momentExt_zero_of_no_holes`, `not_momentExt_two_one_one`: sanity
  checks on `MomentExt`.
-/

namespace PEqualNP.ProofComplexity.Helpers

open MvPolynomial

/-! ### The static span and the passage from derivations to the static span -/

section Static

variable {σ : Type}

/-- The static span of degree `k`: the linear span of the products `monomial a 1 * f` with
`f` in `F` whose total degree is at most `k`. -/
noncomputable def staticSpan (F : Set (MvPolynomial σ (ZMod 2))) (k : ℕ) :
    Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) :=
  Submodule.span (ZMod 2)
    {q | ∃ (a : σ →₀ ℕ) (f : MvPolynomial σ (ZMod 2)),
      f ∈ F ∧ (monomial a 1 * f).totalDegree ≤ k ∧ q = monomial a 1 * f}

theorem monomial_one_mul_X (a : σ →₀ ℕ) (v : σ) :
    monomial a (1 : ZMod 2) * X v = monomial (a + Finsupp.single v 1) 1 := by
  rw [X, monomial_mul_monomial, mul_one]

/-- The total degree of a monomial with coefficient one is the degree of its exponent. -/
theorem totalDegree_monomial_one (a : σ →₀ ℕ) :
    (monomial a (1 : ZMod 2)).totalDegree = a.degree := by
  rw [totalDegree_monomial _ one_ne_zero]
  rfl

/-- A variable times a member of the static span of degree `k` is in the static span of
degree `k + 1`. -/
theorem X_mul_mem_staticSpan {F : Set (MvPolynomial σ (ZMod 2))} {k : ℕ} (j : σ)
    {g : MvPolynomial σ (ZMod 2)} (hg : g ∈ staticSpan F k) :
    X j * g ∈ staticSpan F (k + 1) := by
  induction hg using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨a, f, hf, hdeg, rfl⟩ := hq
    have heq : X j * (monomial a 1 * f) =
        monomial (a + Finsupp.single j 1) (1 : ZMod 2) * f := by
      rw [← monomial_one_mul_X]
      ring
    refine Submodule.subset_span ⟨a + Finsupp.single j 1, f, hf, ?_, heq⟩
    rw [← heq]
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X]
    omega
  | zero => simp
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ _ hx

/-- From the dynamic calculus to the static span. If, for every `k < B`, the members of the
static span of degree `k + 1` that have degree at most `k` are in the static span of degree
`k`, then every line derivable in degree `B` is in the static span of degree `B`. -/
theorem pcDerivable_mem_staticSpan {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    (hint : ∀ k < B, ∀ p, p ∈ staticSpan F (k + 1) → p.totalDegree ≤ k → p ∈ staticSpan F k)
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F B p) : p ∈ staticSpan F B := by
  induction h with
  | @ax p hp hdeg =>
    exact Submodule.subset_span ⟨0, p, hp, by simpa using hdeg, by simp⟩
  | zero => exact Submodule.zero_mem _
  | add _ _ ih1 ih2 => exact Submodule.add_mem _ ih1 ih2
  | @mulX j p _ hdeg ih =>
    by_cases hp0 : p = 0
    · subst hp0
      simp
    have hXp : (X j * p).totalDegree = 1 + p.totalDegree := by
      rw [totalDegree_mul_of_isDomain (X_ne_zero j) hp0, totalDegree_X]
    obtain ⟨k, rfl⟩ : ∃ k, B = k + 1 := ⟨B - 1, by omega⟩
    exact X_mul_mem_staticSpan j (hint k (Nat.lt_succ_self k) p ih (by omega))

/-- Under the intersection property, a constant in the static span of degree `B` is in the
static span of degree `0`. -/
theorem one_mem_staticSpan_zero {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    (hint : ∀ k < B, ∀ p, p ∈ staticSpan F (k + 1) → p.totalDegree ≤ k → p ∈ staticSpan F k)
    (h : (1 : MvPolynomial σ (ZMod 2)) ∈ staticSpan F B) :
    (1 : MvPolynomial σ (ZMod 2)) ∈ staticSpan F 0 := by
  induction B with
  | zero => exact h
  | succ k ih =>
    exact ih (fun k' hk' => hint k' (by omega)) (hint k (by omega) 1 h (by simp))

/-- Two linear functionals that agree on the monomials of degree at most `k` agree on the
polynomials of total degree at most `k`. -/
theorem dual_eq_of_monomial_eq {k : ℕ}
    (f g : MvPolynomial σ (ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (h : ∀ a : σ →₀ ℕ, a.degree ≤ k → f (monomial a 1) = g (monomial a 1))
    (p : MvPolynomial σ (ZMod 2)) (hp : p.totalDegree ≤ k) : f p = g p := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hm : monomial a (p.coeff a) = p.coeff a • monomial a (1 : ZMod 2) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hm, map_smul, map_smul, h a ((le_totalDegree ha).trans hp)]

theorem support_add_single_one [DecidableEq σ] (a : σ →₀ ℕ) (v : σ) :
    (a + Finsupp.single v 1).support = insert v a.support := by
  ext u
  by_cases h : v = u
  · subst h
    simp
  · simp [Ne.symm h]

theorem card_support_le_degree (a : σ →₀ ℕ) : a.support.card ≤ a.degree := by
  rw [Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun v hv => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)

end Static

/-! ### Partial matchings, consistent moment families, the extension property -/

section Matching

variable {m N : ℕ}

/-- A partial matching: a finite set of pairs (row, column) in which different pairs have
different rows and different columns. -/
def IsPartialMatching (T : Finset (Fin m × Fin N)) : Prop :=
  ∀ a ∈ T, ∀ b ∈ T, (a.1 = b.1 ∨ a.2 = b.2) → a = b

/-- A family `z` of values in `ZMod 2` is `k`-consistent if, for every partial matching `T`
with fewer than `k` pairs and every row `i` not used by `T`, the value at `T` is the sum,
over the columns `j` not used by `T`, of the values at `insert (i, j) T`. Only the values of
`z` at partial matchings with at most `k` pairs matter. -/
def MomentConsistent (m N k : ℕ) (z : Finset (Fin m × Fin N) → ZMod 2) : Prop :=
  ∀ T : Finset (Fin m × Fin N), IsPartialMatching T → T.card < k →
    ∀ i : Fin m, (∀ a ∈ T, a.1 ≠ i) →
      z T = ∑ j ∈ Finset.univ.filter (fun j : Fin N => ∀ a ∈ T, a.2 ≠ j), z (insert (i, j) T)

/-- The extension property at level `k`: every `k`-consistent family agrees, on the partial
matchings with at most `k` pairs, with a `(k + 1)`-consistent family. -/
def MomentExt (m N k : ℕ) : Prop :=
  ∀ z : Finset (Fin m × Fin N) → ZMod 2, MomentConsistent m N k z →
    ∃ z' : Finset (Fin m × Fin N) → ZMod 2, MomentConsistent m N (k + 1) z' ∧
      ∀ T : Finset (Fin m × Fin N), IsPartialMatching T → T.card ≤ k → z' T = z T

theorem isPartialMatching_empty : IsPartialMatching (∅ : Finset (Fin m × Fin N)) := by
  intro a ha
  simp at ha

theorem IsPartialMatching.mono {S T : Finset (Fin m × Fin N)} (hT : IsPartialMatching T)
    (hST : S ⊆ T) : IsPartialMatching S :=
  fun a ha b hb h => hT a (hST ha) b (hST hb) h

/-- Adding a pair in an unused row keeps a partial matching exactly when the column is
unused. -/
theorem isPartialMatching_insert_iff {S : Finset (Fin m × Fin N)} (hS : IsPartialMatching S)
    {i : Fin m} (hrow : ∀ a ∈ S, a.1 ≠ i) (j : Fin N) :
    IsPartialMatching (insert (i, j) S) ↔ ∀ a ∈ S, a.2 ≠ j := by
  constructor
  · intro h a ha haj
    have := h a (Finset.mem_insert_of_mem ha) (i, j) (Finset.mem_insert_self _ _) (Or.inr haj)
    exact hrow a ha (by rw [this])
  · intro hcol a ha b hb hab
    rcases Finset.mem_insert.mp ha with rfl | ha' <;> rcases Finset.mem_insert.mp hb with rfl | hb'
    · rfl
    · rcases hab with h | h
      · exact absurd h.symm (hrow b hb')
      · exact absurd h.symm (hcol b hb')
    · rcases hab with h | h
      · exact absurd h (hrow a ha')
      · exact absurd h (hcol a ha')
    · exact hS a ha' b hb' hab

/-- Adding a second pair in a used row destroys a partial matching. -/
theorem not_isPartialMatching_insert {S : Finset (Fin m × Fin N)} {i : Fin m} {j j0 : Fin N}
    (h0 : (i, j0) ∈ S) (hj : j ≠ j0) : ¬ IsPartialMatching (insert (i, j) S) := by
  intro h
  have := h (i, j) (Finset.mem_insert_self _ _) (i, j0) (Finset.mem_insert_of_mem h0)
    (Or.inl rfl)
  exact hj (congrArg Prod.snd this)

open Classical in
/-- The weight of a set of pairs under a family `z`: the value of `z` at a partial matching,
and zero at a set that is not a partial matching. -/
noncomputable def momentWeight (z : Finset (Fin m × Fin N) → ZMod 2)
    (S : Finset (Fin m × Fin N)) : ZMod 2 :=
  if IsPartialMatching S then z S else 0

theorem momentWeight_of_not {z : Finset (Fin m × Fin N) → ZMod 2}
    {S : Finset (Fin m × Fin N)} (h : ¬ IsPartialMatching S) : momentWeight z S = 0 :=
  ite_eq_right h

theorem momentWeight_of_matching {z : Finset (Fin m × Fin N) → ZMod 2}
    {S : Finset (Fin m × Fin N)} (h : IsPartialMatching S) : momentWeight z S = z S :=
  ite_eq_left h

/-- The row identity for weights: for a `k`-consistent family, the weights of the sets
`insert (i, j) S` over all columns `j` sum to the weight of `S`, as soon as `S` has fewer
than `k` pairs when it is a partial matching. -/
theorem momentWeight_row_sum {z : Finset (Fin m × Fin N) → ZMod 2} {k : ℕ}
    (hz : MomentConsistent m N k z) (S : Finset (Fin m × Fin N))
    (hS : IsPartialMatching S → S.card < k) (i : Fin m) :
    ∑ j : Fin N, momentWeight z (insert (i, j) S) = momentWeight z S := by
  by_cases hM : IsPartialMatching S
  · by_cases hrow : ∀ a ∈ S, a.1 ≠ i
    · rw [momentWeight_of_matching hM, hz S hM (hS hM) i hrow, Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hc : ∀ a ∈ S, a.2 ≠ j
      · rw [ite_eq_left hc,
          momentWeight_of_matching ((isPartialMatching_insert_iff hM hrow j).mpr hc)]
      · rw [ite_eq_right hc, momentWeight_of_not
          (fun h => hc ((isPartialMatching_insert_iff hM hrow j).mp h))]
    · push Not at hrow
      obtain ⟨⟨i', j0⟩, ha, hi⟩ := hrow
      simp only at hi
      subst hi
      rw [Finset.sum_eq_single j0]
      · rw [Finset.insert_eq_of_mem ha]
      · intro j _ hj
        exact momentWeight_of_not (not_isPartialMatching_insert ha hj)
      · intro h
        exact absurd (Finset.mem_univ _) h
  · rw [momentWeight_of_not hM]
    refine Finset.sum_eq_zero fun j _ => ?_
    exact momentWeight_of_not fun h => hM (h.mono (Finset.subset_insert _ _))

/-! ### The functional of a moment family -/

/-- The linear functional of a family `z`: a monomial goes to the weight of its support. -/
noncomputable def momentFunctional (z : Finset (Fin m × Fin N) → ZMod 2) :
    MvPolynomial (Fin m × Fin N) (ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  (basisMonomials (Fin m × Fin N) (ZMod 2)).constr (ZMod 2)
    fun a => momentWeight z a.support

theorem momentFunctional_monomial (z : Finset (Fin m × Fin N) → ZMod 2)
    (a : Fin m × Fin N →₀ ℕ) :
    momentFunctional z (monomial a 1) = momentWeight z a.support := by
  have h := (basisMonomials (Fin m × Fin N) (ZMod 2)).constr_basis (ZMod 2)
    (fun a => momentWeight z a.support) a
  rw [coe_basisMonomials] at h
  exact h

/-- The row axiom of pigeon `i`. -/
theorem rowAxiom_totalDegree_le (i : Fin m) :
    ((∑ j : Fin N, X (i, j)) + 1 : MvPolynomial (Fin m × Fin N) (ZMod 2)).totalDegree ≤ 1 := by
  refine (totalDegree_add _ _).trans (max_le ?_ (by simp))
  refine totalDegree_finsetSum_le fun j _ => ?_
  rw [totalDegree_X]

theorem one_le_rowAxiom_totalDegree (hN : 1 ≤ N) (i : Fin m) :
    1 ≤ ((∑ j : Fin N, X (i, j)) + 1 : MvPolynomial (Fin m × Fin N) (ZMod 2)).totalDegree := by
  by_contra hlt
  have h0 : ((∑ j : Fin N, X (i, j)) + 1 :
      MvPolynomial (Fin m × Fin N) (ZMod 2)).totalDegree = 0 := by omega
  rw [totalDegree_eq_zero_iff_eq_C] at h0
  have e0 := congrArg (eval (fun _ : Fin m × Fin N => (0 : ZMod 2))) h0
  have e1 := congrArg
    (eval (fun v : Fin m × Fin N => if v = (i, (⟨0, hN⟩ : Fin N)) then (1 : ZMod 2) else 0)) h0
  simp only [map_add, map_sum, eval_X, map_one, eval_C, Finset.sum_const_zero, zero_add] at e0 e1
  rw [← e0] at e1
  simp [Prod.mk.injEq] at e1

theorem monomial_one_mul_rowAxiom (a : Fin m × Fin N →₀ ℕ) (i : Fin m) :
    monomial a (1 : ZMod 2) * ((∑ j : Fin N, X (i, j)) + 1) =
      (∑ j : Fin N, monomial (a + Finsupp.single (i, j) 1) 1) + monomial a 1 := by
  rw [mul_add, mul_one, Finset.mul_sum]
  simp only [monomial_one_mul_X]

/-- The functional of a `k`-consistent family vanishes on the static span of degree `k` of
the functional pigeonhole system. -/
theorem momentFunctional_staticSpan (hN : 1 ≤ N) {z : Finset (Fin m × Fin N) → ZMod 2}
    {k : ℕ} (hz : MomentConsistent m N k z) {p : MvPolynomial (Fin m × Fin N) (ZMod 2)}
    (hp : p ∈ staticSpan (funPHPSystem m N) k) : momentFunctional z p = 0 := by
  induction hp using Submodule.span_induction with
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]
  | mem q hq =>
    obtain ⟨a, f, hf, hdeg, rfl⟩ := hq
    rcases hf with ⟨v, rfl⟩ | ⟨i, j, j', hne, rfl⟩ | ⟨i, i', j, hne, rfl⟩ | ⟨i, rfl⟩
    · rw [mul_add, ← mul_assoc, monomial_one_mul_X, monomial_one_mul_X, map_add,
        momentFunctional_monomial, momentFunctional_monomial, support_add_single_one,
        support_add_single_one, Finset.insert_idem v a.support]
      exact CharTwo.add_self_eq_zero _
    · rw [← mul_assoc, monomial_one_mul_X, monomial_one_mul_X, momentFunctional_monomial,
        support_add_single_one, support_add_single_one]
      refine momentWeight_of_not fun h => hne ?_
      have := h (i, j) (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) (i, j')
        (Finset.mem_insert_self _ _) (Or.inl rfl)
      exact congrArg Prod.snd this
    · rw [← mul_assoc, monomial_one_mul_X, monomial_one_mul_X, momentFunctional_monomial,
        support_add_single_one, support_add_single_one]
      refine momentWeight_of_not fun h => hne ?_
      have := h (i, j) (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) (i', j)
        (Finset.mem_insert_self _ _) (Or.inr rfl)
      exact congrArg Prod.fst this
    · have hrow := one_le_rowAxiom_totalDegree (m := m) hN i
      have hne0 :
          ((∑ j : Fin N, X (i, j)) + 1 : MvPolynomial (Fin m × Fin N) (ZMod 2)) ≠ 0 := by
        intro h0
        rw [h0, totalDegree_zero] at hrow
        omega
      have hmon : monomial a (1 : ZMod 2) ≠ 0 := by
        rw [Ne, monomial_eq_zero]
        exact one_ne_zero
      rw [totalDegree_mul_of_isDomain hmon hne0, totalDegree_monomial_one] at hdeg
      have hcard := card_support_le_degree a
      rw [monomial_one_mul_rowAxiom, map_add, map_sum, momentFunctional_monomial]
      simp only [momentFunctional_monomial, support_add_single_one]
      rw [momentWeight_row_sum hz a.support (fun _ => by omega) i]
      exact CharTwo.add_self_eq_zero _

/-! ### From a functional that vanishes on the static span to a consistent family -/

/-- The exponent of the multilinear monomial of a set of variables. -/
noncomputable def indMon (T : Finset (Fin m × Fin N)) : Fin m × Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => if v ∈ T then 1 else 0

theorem indMon_apply (T : Finset (Fin m × Fin N)) (v : Fin m × Fin N) :
    indMon T v = if v ∈ T then 1 else 0 := rfl

theorem indMon_support (T : Finset (Fin m × Fin N)) : (indMon T).support = T := by
  ext v
  simp [indMon_apply]

theorem indMon_degree (T : Finset (Fin m × Fin N)) : (indMon T).degree = T.card := by
  rw [Finsupp.degree_eq_sum]
  simp [indMon_apply]

theorem indMon_insert {T : Finset (Fin m × Fin N)} {v : Fin m × Fin N} (hv : v ∉ T) :
    indMon (insert v T) = indMon T + Finsupp.single v 1 := by
  ext u
  by_cases h : u = v
  · subst h
    simp [indMon_apply, hv]
  · simp [indMon_apply, h]

theorem eq_indMon_support {a : Fin m × Fin N →₀ ℕ} (h : ∀ v, a v ≤ 1) :
    a = indMon a.support := by
  ext v
  have := h v
  by_cases h0 : a v = 0
  · simp [indMon_apply, h0]
  · simp [indMon_apply, h0]
    omega

/-- A functional that vanishes on the static span of degree `k` does not see multiplicities:
on a monomial of degree at most `k` it has the value of the multilinear monomial with the
same support. -/
theorem dual_monomial_eq_indMon {k : ℕ}
    {φ : MvPolynomial (Fin m × Fin N) (ZMod 2) →ₗ[ZMod 2] ZMod 2}
    (hφ : ∀ q ∈ staticSpan (funPHPSystem m N) k, φ q = 0) :
    ∀ (n : ℕ) (a : Fin m × Fin N →₀ ℕ), a.degree = n → a.degree ≤ k →
      φ (monomial a 1) = φ (monomial (indMon a.support) 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a han hak
    by_cases h : ∀ v, a v ≤ 1
    · rw [← eq_indMon_support h]
    push Not at h
    obtain ⟨v, hv⟩ := h
    have hle : Finsupp.single v 2 ≤ a := by
      intro u
      by_cases huv : v = u
      · subst huv
        rw [Finsupp.single_eq_same]
        omega
      · simp [huv]
    obtain ⟨b, hb⟩ : ∃ b, a = b + Finsupp.single v 2 :=
      ⟨a - Finsupp.single v 2, (tsub_add_cancel_of_le hle).symm⟩
    set c := b + Finsupp.single v 1 with hc
    have hac : a = c + Finsupp.single v 1 := by
      rw [hb, hc, add_assoc, ← Finsupp.single_add]
    have hdeg : a.degree = c.degree + 1 := by
      rw [hac, map_add, Finsupp.degree_single]
    have hq : monomial b (1 : ZMod 2) * (X v * X v + X v) = monomial a 1 + monomial c 1 := by
      rw [mul_add, ← mul_assoc, monomial_one_mul_X, monomial_one_mul_X, ← hc, ← hac]
    have hmem : monomial a (1 : ZMod 2) + monomial c 1 ∈ staticSpan (funPHPSystem m N) k := by
      refine Submodule.subset_span ⟨b, _, Or.inl ⟨v, rfl⟩, ?_, hq.symm⟩
      rw [hq]
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · rw [totalDegree_monomial_one]
        exact hak
      · rw [totalDegree_monomial_one]
        omega
    have h0 := hφ _ hmem
    rw [map_add, CharTwo.add_eq_zero] at h0
    have hsupp : a.support = c.support := by
      rw [hac, support_add_single_one, Finset.insert_eq_of_mem]
      rw [Finsupp.mem_support_iff, hc]
      simp
    rw [h0, hsupp]
    exact ih c.degree (by omega) c rfl (by omega)

/-- A functional that vanishes on the static span of degree `k` vanishes on the monomials of
degree at most `k` whose support is not a partial matching. -/
theorem dual_monomial_eq_zero {k : ℕ}
    {φ : MvPolynomial (Fin m × Fin N) (ZMod 2) →ₗ[ZMod 2] ZMod 2}
    (hφ : ∀ q ∈ staticSpan (funPHPSystem m N) k, φ q = 0)
    (a : Fin m × Fin N →₀ ℕ) (hak : a.degree ≤ k) (hM : ¬ IsPartialMatching a.support) :
    φ (monomial a 1) = 0 := by
  unfold IsPartialMatching at hM
  push Not at hM
  obtain ⟨u, hu, v, hv, huv, hne⟩ := hM
  have hle : Finsupp.single u 1 + Finsupp.single v 1 ≤ a := by
    intro w
    have h1 := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hu)
    have h2 := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)
    by_cases hwu : u = w
    · subst hwu
      simpa [Finsupp.single_apply, Ne.symm hne] using h1
    · by_cases hwv : v = w
      · subst hwv
        simpa [Finsupp.single_apply, hne] using h2
      · simp [hwu, hwv]
  obtain ⟨b, hb⟩ : ∃ b, a = b + (Finsupp.single u 1 + Finsupp.single v 1) :=
    ⟨a - (Finsupp.single u 1 + Finsupp.single v 1), (tsub_add_cancel_of_le hle).symm⟩
  have hq : monomial b (1 : ZMod 2) * (X u * X v) = monomial a 1 := by
    rw [← mul_assoc, monomial_one_mul_X, monomial_one_mul_X, hb, add_assoc]
  have hF : (X u * X v : MvPolynomial (Fin m × Fin N) (ZMod 2)) ∈ funPHPSystem m N := by
    obtain ⟨i, j⟩ := u
    obtain ⟨i', j'⟩ := v
    rcases huv with h | h
    · simp only at h
      subst h
      exact Or.inr (Or.inl ⟨i, j, j', fun h => hne (by rw [h]), rfl⟩)
    · simp only at h
      subst h
      exact Or.inr (Or.inr (Or.inl ⟨i, i', j, fun h => hne (by rw [h]), rfl⟩))
  refine hφ _ (Submodule.subset_span ⟨b, _, hF, ?_, hq.symm⟩)
  rw [hq, totalDegree_monomial_one]
  exact hak

/-- The values of a functional that vanishes on the static span of degree `k`, at the
multilinear monomials, form a `k`-consistent family. -/
theorem momentConsistent_of_dual {k : ℕ}
    {φ : MvPolynomial (Fin m × Fin N) (ZMod 2) →ₗ[ZMod 2] ZMod 2}
    (hφ : ∀ q ∈ staticSpan (funPHPSystem m N) k, φ q = 0) :
    MomentConsistent m N k fun T => φ (monomial (indMon T) 1) := by
  intro T hT hcard i hrow
  have hnot : ∀ j : Fin N, (i, j) ∉ T := fun j hj => hrow _ hj rfl
  have hmem : monomial (indMon T) (1 : ZMod 2) * ((∑ j : Fin N, X (i, j)) + 1) ∈
      staticSpan (funPHPSystem m N) k := by
    refine Submodule.subset_span ⟨indMon T, _, Or.inr (Or.inr (Or.inr ⟨i, rfl⟩)), ?_, rfl⟩
    refine (totalDegree_mul _ _).trans ?_
    have h1 := rowAxiom_totalDegree_le (N := N) i
    rw [totalDegree_monomial_one, indMon_degree]
    omega
  have h0 := hφ _ hmem
  rw [monomial_one_mul_rowAxiom, map_add, CharTwo.add_eq_zero, map_sum] at h0
  show φ (monomial (indMon T) 1) = _
  rw [← h0, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← indMon_insert (hnot j)]
  by_cases hc : ∀ a ∈ T, a.2 ≠ j
  · rw [ite_eq_left hc]
  · rw [ite_eq_right hc]
    refine dual_monomial_eq_zero hφ _ ?_ ?_
    · rw [indMon_degree, Finset.card_insert_of_notMem (hnot j)]
      omega
    · rw [indMon_support]
      exact fun h => hc ((isPartialMatching_insert_iff hT hrow j).mp h)

/-- A functional that vanishes on the static span of degree `k` agrees with the functional
of its family of values on the polynomials of degree at most `k`. -/
theorem dual_eq_momentFunctional {k : ℕ}
    {φ : MvPolynomial (Fin m × Fin N) (ZMod 2) →ₗ[ZMod 2] ZMod 2}
    (hφ : ∀ q ∈ staticSpan (funPHPSystem m N) k, φ q = 0)
    (p : MvPolynomial (Fin m × Fin N) (ZMod 2)) (hp : p.totalDegree ≤ k) :
    φ p = momentFunctional (fun T => φ (monomial (indMon T) 1)) p := by
  refine dual_eq_of_monomial_eq _ _ (fun a ha => ?_) p hp
  rw [momentFunctional_monomial]
  by_cases hM : IsPartialMatching a.support
  · rw [momentWeight_of_matching hM]
    exact dual_monomial_eq_indMon hφ _ a rfl ha
  · rw [momentWeight_of_not hM]
    exact dual_monomial_eq_zero hφ a ha hM

/-! ### The intersection property and the reduction -/

/-- The extension property at level `k` gives the intersection property at level `k`: a
member of the static span of degree `k + 1` of total degree at most `k` is in the static span
of degree `k`. -/
theorem staticSpan_funPHP_inter (hN : 1 ≤ N) {k : ℕ} (hext : MomentExt m N k)
    (p : MvPolynomial (Fin m × Fin N) (ZMod 2))
    (hp : p ∈ staticSpan (funPHPSystem m N) (k + 1)) (hdeg : p.totalDegree ≤ k) :
    p ∈ staticSpan (funPHPSystem m N) k := by
  by_contra hnot
  obtain ⟨φ, hφp, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hφ : ∀ q ∈ staticSpan (funPHPSystem m N) k, φ q = 0 := by
    intro q hq
    have : φ q ∈ (staticSpan (funPHPSystem m N) k).map φ := Submodule.mem_map_of_mem hq
    rw [hmap] at this
    exact (Submodule.mem_bot _).mp this
  obtain ⟨z', hz', hagree⟩ := hext _ (momentConsistent_of_dual hφ)
  apply hφp
  rw [dual_eq_momentFunctional hφ p hdeg, ← momentFunctional_staticSpan hN hz' hp]
  refine dual_eq_of_monomial_eq _ _ (fun a ha => ?_) p hdeg
  rw [momentFunctional_monomial, momentFunctional_monomial]
  by_cases hM : IsPartialMatching a.support
  · rw [momentWeight_of_matching hM, momentWeight_of_matching hM]
    exact (hagree _ hM ((card_support_le_degree a).trans ha)).symm
  · rw [momentWeight_of_not hM, momentWeight_of_not hM]

/-- The reduction. If the extension property for moment families holds at every level below
`B`, the functional pigeonhole system with at least one hole has no polynomial calculus
refutation of degree `B` over `ZMod 2`. -/
theorem no_pc_refutation_of_momentExt :
    ∀ m N B : ℕ, 1 ≤ N → (∀ k < B, MomentExt m N k) →
      ¬ PCRefutable (funPHPSystem m N) B := by
  intro m N B hN hext href
  have hint : ∀ k < B, ∀ p, p ∈ staticSpan (funPHPSystem m N) (k + 1) → p.totalDegree ≤ k →
      p ∈ staticSpan (funPHPSystem m N) k :=
    fun k hk p => staticSpan_funPHP_inter hN (hext k hk) p
  have h0 := one_mem_staticSpan_zero hint (pcDerivable_mem_staticSpan hint href)
  have hz : MomentConsistent m N 0 fun _ => 1 := by
    intro T _ hcard
    omega
  have hval := momentFunctional_staticSpan hN hz h0
  have h1 : (1 : MvPolynomial (Fin m × Fin N) (ZMod 2)) = monomial 0 1 := rfl
  rw [h1, momentFunctional_monomial, Finsupp.support_zero,
    momentWeight_of_matching isPartialMatching_empty] at hval
  exact one_ne_zero hval

/-! ### Sanity checks on the extension property -/

/-- At level `0` the extension property holds as soon as there is a hole: put the value of
the empty matching on the pairs of column `0`. -/
theorem momentExt_zero (m N : ℕ) (hN : 1 ≤ N) : MomentExt m N 0 := by
  intro z _
  refine ⟨fun T => if T = ∅ then z ∅ else
    if ∃ i : Fin m, T = {(i, (⟨0, hN⟩ : Fin N))} then z ∅ else 0, ?_, ?_⟩
  · intro T _ hcard i _
    have hT : T = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hT
    simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, Finset.filter_true,
      ite_true, insert_empty_eq, Finset.singleton_ne_empty, ite_false]
    rw [Finset.sum_eq_single (⟨0, hN⟩ : Fin N)]
    · rw [ite_eq_left ⟨i, rfl⟩]
    · intro j _ hj
      refine ite_eq_right ?_
      rintro ⟨i', h⟩
      rw [Finset.singleton_inj] at h
      exact hj (congrArg Prod.snd h)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro T _ hcard
    have hT : T = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hT
    simp

/-- Without holes and with at least one pigeon the extension property fails at level `0`:
the row identity forces the value of the empty matching to be zero. -/
theorem not_momentExt_zero_of_no_holes (m : ℕ) (hm : 1 ≤ m) : ¬ MomentExt m 0 0 := by
  intro h
  obtain ⟨z', hz', hagree⟩ := h (fun _ => 1) (fun T _ hcard => by omega)
  have h1 := hz' ∅ isPartialMatching_empty (by simp) ⟨0, hm⟩ (by simp)
  rw [hagree ∅ isPartialMatching_empty (by simp)] at h1
  simp at h1

/-- With two pigeons and one hole the extension property fails at level `1`. -/
theorem not_momentExt_two_one_one : ¬ MomentExt 2 1 1 := by
  intro h
  have hz : MomentConsistent 2 1 1 fun _ => 1 := by
    intro T _ hcard i _
    have hT : T = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hT
    simp
  obtain ⟨z', hz', hagree⟩ := h _ hz
  have hM : IsPartialMatching ({((0 : Fin 2), (0 : Fin 1))} : Finset (Fin 2 × Fin 1)) := by
    intro a ha b hb _
    rw [Finset.mem_singleton] at ha hb
    rw [ha, hb]
  have h1 := hz' {((0 : Fin 2), (0 : Fin 1))} hM (by simp) 1 (by simp)
  rw [hagree _ hM (by simp)] at h1
  have hempty : (Finset.univ.filter fun j : Fin 1 =>
      ∀ a ∈ ({((0 : Fin 2), (0 : Fin 1))} : Finset (Fin 2 × Fin 1)), a.2 ≠ j) = ∅ := by
    decide
  rw [hempty, Finset.sum_empty] at h1
  exact one_ne_zero h1

end Matching

end PEqualNP.ProofComplexity.Helpers

-- Accepted project source: PEqualNP.ProofComplexity.Helpers.EchelonNF
/-!
# Helpers: echelon normal form modulo a subspace

Generic linear algebra on the monomial basis of `MvPolynomial σ (ZMod 2)`, used by the route
to L-pcx-046 (helper H2).

* `monoKey`, `MonoLt`: a well-founded linear order on exponent vectors that refines degree
  (key `a ↦ (a.degree, code a)` in `ℕ ×ₗ ℕ` with `code` an injection into `ℕ`).
* `IsStd U a`: the monomial `a` is standard for the subspace `U`, i.e.
  `monomial a 1 ∉ U ⊔ span {monomial b 1 : MonoLt b a}`.
* `nf U`: the projection onto the span of the standard monomials along `U`. It is the unique
  polynomial supported on standard monomials congruent to its argument modulo `U`; its monomials
  are at most the top monomial of the argument, so it does not raise the total degree.
-/

namespace PEqualNP.ProofComplexity.Helpers

open MvPolynomial

variable {σ : Type} [Countable σ]

/-- The key of an exponent vector: its degree, then an injective code. -/
noncomputable def monoKey (a : σ →₀ ℕ) : ℕ ×ₗ ℕ :=
  toLex (a.degree, Classical.choose (Countable.exists_injective_nat (σ →₀ ℕ)) a)

/-- The monomial order: compare keys. -/
def MonoLt (b a : σ →₀ ℕ) : Prop := monoKey b < monoKey a

theorem monoKey_injective : Function.Injective (monoKey (σ := σ)) := by
  intro a b h
  have h2 := congrArg (fun x => (ofLex x).2) h
  simp only [monoKey, ofLex_toLex] at h2
  exact Classical.choose_spec (Countable.exists_injective_nat (σ →₀ ℕ)) h2

theorem monoLt_of_degree_lt {a b : σ →₀ ℕ} (h : b.degree < a.degree) : MonoLt b a := by
  unfold MonoLt monoKey
  exact Prod.Lex.toLex_lt_toLex.2 (Or.inl h)

theorem degree_le_of_monoLt {a b : σ →₀ ℕ} (h : MonoLt b a) : b.degree ≤ a.degree := by
  unfold MonoLt monoKey at h
  rcases Prod.Lex.toLex_lt_toLex.1 h with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

theorem monoLt_wellFounded : WellFounded (MonoLt (σ := σ)) :=
  InvImage.wf monoKey wellFounded_lt

theorem monoLt_trans {a b c : σ →₀ ℕ} (h1 : MonoLt a b) (h2 : MonoLt b c) : MonoLt a c :=
  lt_trans (α := ℕ ×ₗ ℕ) h1 h2

/-- A monomial is standard for `U` if it is not congruent modulo `U` to a combination of
smaller monomials. -/
def IsStd (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (a : σ →₀ ℕ) : Prop :=
  monomial a (1 : ZMod 2) ∉ U ⊔ restrictSupport (ZMod 2) {b | MonoLt b a}

/-- The span of the standard monomials. -/
noncomputable def echelonStd (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) :
    Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) :=
  restrictSupport (ZMod 2) {a | IsStd U a}

omit [Countable σ] in
theorem echelon_restrictSupport_le {s : Set (σ →₀ ℕ)}
    {P : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))}
    (h : ∀ b ∈ s, monomial b (1 : ZMod 2) ∈ P) : restrictSupport (ZMod 2) s ≤ P := by
  rw [restrictSupport_eq_span]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨b, hb, rfl⟩
  exact h b hb

/-- No nonzero polynomial supported on standard monomials lies in `U`. -/
theorem echelon_disjoint (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) :
    Disjoint (echelonStd U) U := by
  classical
  rw [Submodule.disjoint_def]
  intro h hS hU
  by_contra hne
  have hsupp : h.support.Nonempty := by
    rwa [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image h.support monoKey hsupp
  have hstd : IsStd U a := ((mem_restrictSupport_iff (R := ZMod 2)).1 hS) ha
  apply hstd
  have key : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  have hc : h.coeff a = 1 := key _ (mem_support_iff.1 ha)
  have hw : h - monomial a 1 ∈ restrictSupport (ZMod 2) {b | MonoLt b a} := by
    rw [mem_restrictSupport_iff]
    intro b hb
    have hb' : (h - monomial a 1).coeff b ≠ 0 := mem_support_iff.1 hb
    rw [coeff_sub, coeff_monomial] at hb'
    by_cases hab : a = b
    · subst hab
      simp [hc] at hb'
    · rw [if_neg hab, sub_zero] at hb'
      have hbS : b ∈ h.support := mem_support_iff.2 hb'
      exact lt_of_le_of_ne (hmax b hbS) (fun e => hab (monoKey_injective e).symm)
  have heq : monomial a (1 : ZMod 2) = h - (h - monomial a 1) := (sub_sub_cancel _ _).symm
  rw [heq]
  exact Submodule.sub_mem _ (Submodule.mem_sup_left hU) (Submodule.mem_sup_right hw)

/-- Every monomial is congruent modulo `U` to a standard combination of monomials at most it. -/
theorem echelon_monomial_mem (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (a : σ →₀ ℕ) :
    monomial a (1 : ZMod 2) ∈
      U ⊔ (echelonStd U ⊓ restrictSupport (ZMod 2) {b | b = a ∨ MonoLt b a}) := by
  induction a using (monoLt_wellFounded (σ := σ)).induction
  rename_i a ih
  by_cases hs : IsStd U a
  · apply Submodule.mem_sup_right
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · exact (monomial_mem_restrictSupport (R := ZMod 2)).2 (Or.inl hs)
    · exact (monomial_mem_restrictSupport (R := ZMod 2)).2 (Or.inl (Or.inl rfl))
  · have hmem : monomial a (1 : ZMod 2) ∈ U ⊔ restrictSupport (ZMod 2) {b | MonoLt b a} :=
      Classical.byContradiction fun h => hs h
    have hle : U ⊔ restrictSupport (ZMod 2) {b | MonoLt b a} ≤
        U ⊔ (echelonStd U ⊓ restrictSupport (ZMod 2) {b | b = a ∨ MonoLt b a}) := by
      refine sup_le le_sup_left ?_
      refine echelon_restrictSupport_le ?_
      intro b hb
      refine (sup_le_sup_left (inf_le_inf_left _ (restrictSupport_mono (R := ZMod 2) ?_)) U)
        (ih b hb)
      intro c hc
      rcases hc with rfl | hc
      · exact Or.inr hb
      · exact Or.inr (monoLt_trans hc hb)
    exact hle hmem

theorem echelon_le_of_downClosed (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    {s : Set (σ →₀ ℕ)} (hs : ∀ a ∈ s, ∀ b, MonoLt b a → b ∈ s) :
    restrictSupport (ZMod 2) s ≤ U ⊔ (echelonStd U ⊓ restrictSupport (ZMod 2) s) := by
  refine echelon_restrictSupport_le ?_
  intro a ha
  refine (sup_le_sup_left (inf_le_inf_left _ (restrictSupport_mono (R := ZMod 2) ?_)) U)
    (echelon_monomial_mem U a)
  intro b hb
  rcases hb with hb | hb
  · rw [hb]; exact ha
  · exact hs a ha b hb

theorem echelon_isCompl (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) :
    IsCompl (echelonStd U) U := by
  refine ⟨echelon_disjoint U, ?_⟩
  rw [codisjoint_iff, eq_top_iff]
  intro f _
  have hf : f ∈ restrictSupport (ZMod 2) (Set.univ : Set (σ →₀ ℕ)) := by
    rw [mem_restrictSupport_iff]
    exact Set.subset_univ _
  have h := echelon_le_of_downClosed U (s := Set.univ) (fun _ _ _ _ => trivial) hf
  have hle : U ⊔ (echelonStd U ⊓ restrictSupport (ZMod 2) (Set.univ : Set (σ →₀ ℕ))) ≤
      echelonStd U ⊔ U :=
    sup_le le_sup_right (inf_le_left.trans le_sup_left)
  exact hle h

/-- The echelon normal form modulo `U`: projection onto the standard span along `U`. -/
noncomputable def nf (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) :
    MvPolynomial σ (ZMod 2) →ₗ[ZMod 2] MvPolynomial σ (ZMod 2) :=
  Submodule.projection (echelonStd U) U (echelon_isCompl U)

theorem nf_mem_echelonStd (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (f : MvPolynomial σ (ZMod 2)) : nf U f ∈ echelonStd U :=
  Submodule.projection_apply_mem (echelon_isCompl U) f

theorem nf_sub_mem (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (f : MvPolynomial σ (ZMod 2)) : f - nf U f ∈ U :=
  Submodule.sub_projection_mem (echelon_isCompl U) f

theorem nf_support_isStd (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (f : MvPolynomial σ (ZMod 2)) : ∀ a ∈ (nf U f).support, IsStd U a :=
  fun _ ha => ((mem_restrictSupport_iff (R := ZMod 2)).1 (nf_mem_echelonStd U f)) ha

theorem nf_unique (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    {f g : MvPolynomial σ (ZMod 2)} (hg : ∀ a ∈ g.support, IsStd U a) (hfg : f - g ∈ U) :
    nf U f = g := by
  have hgS : g ∈ echelonStd U := (mem_restrictSupport_iff (R := ZMod 2)).2 fun a ha => hg a ha
  have h1 : nf U f - g ∈ echelonStd U := Submodule.sub_mem _ (nf_mem_echelonStd U f) hgS
  have h2 : nf U f - g ∈ U := by
    have h3 := Submodule.sub_mem _ hfg (nf_sub_mem U f)
    rwa [sub_sub_sub_cancel_left] at h3
  exact sub_eq_zero.1 ((Submodule.disjoint_def.1 (echelon_disjoint U)) _ h1 h2)

theorem nf_eq_zero_iff (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (f : MvPolynomial σ (ZMod 2)) : nf U f = 0 ↔ f ∈ U := by
  constructor
  · intro h
    have h3 := nf_sub_mem U f
    rwa [h, sub_zero] at h3
  · intro h
    exact nf_unique U (by simp) (by rwa [sub_zero])

/-- If `f` lies in `restrictSupport s` with `s` closed downwards under `MonoLt`, so does
`nf U f`. -/
theorem nf_mem_of_downClosed (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    {s : Set (σ →₀ ℕ)} (hs : ∀ a ∈ s, ∀ b, MonoLt b a → b ∈ s)
    {f : MvPolynomial σ (ZMod 2)} (hf : f ∈ restrictSupport (ZMod 2) s) :
    nf U f ∈ restrictSupport (ZMod 2) s := by
  obtain ⟨u, hu, g, hg, hug⟩ := Submodule.mem_sup.1 (echelon_le_of_downClosed U hs hf)
  have hgs := Submodule.mem_inf.1 hg
  have hnf : nf U f = g := by
    refine nf_unique U (fun c hc => (mem_restrictSupport_iff (R := ZMod 2)).1 hgs.1 hc) ?_
    rw [← hug, add_sub_cancel_right]
    exact hu
  rw [hnf]
  exact hgs.2

theorem nf_monomial_support (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (a : σ →₀ ℕ) : ∀ b ∈ (nf U (monomial a 1)).support, b = a ∨ MonoLt b a := by
  have hd : ∀ c ∈ {b | b = a ∨ MonoLt b a}, ∀ b, MonoLt b c → b ∈ {b | b = a ∨ MonoLt b a} := by
    intro c hc b hb
    rcases hc with hc | hc
    · rw [hc] at hb
      exact Or.inr hb
    · exact Or.inr (monoLt_trans hb hc)
  have hm : monomial a (1 : ZMod 2) ∈ restrictSupport (ZMod 2) {b | b = a ∨ MonoLt b a} :=
    (monomial_mem_restrictSupport (R := ZMod 2)).2 (Or.inl (Or.inl rfl))
  intro b hb
  exact (mem_restrictSupport_iff (R := ZMod 2)).1 (nf_mem_of_downClosed U hd hm) hb

omit [Countable σ] in
theorem echelon_sum_eq_degree (b : σ →₀ ℕ) : (b.sum fun _ e => e) = b.degree := by
  rw [Finsupp.degree_apply]
  rfl

theorem totalDegree_nf_le (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (f : MvPolynomial σ (ZMod 2)) : (nf U f).totalDegree ≤ f.totalDegree := by
  have hd : ∀ c ∈ {b : σ →₀ ℕ | b.degree ≤ f.totalDegree}, ∀ b, MonoLt b c →
      b ∈ {b : σ →₀ ℕ | b.degree ≤ f.totalDegree} :=
    fun _ hc _ hb => le_trans (degree_le_of_monoLt hb) hc
  have hf : f ∈ restrictSupport (ZMod 2) {b : σ →₀ ℕ | b.degree ≤ f.totalDegree} := by
    rw [mem_restrictSupport_iff]
    intro b hb
    exact (echelon_sum_eq_degree b).symm.trans_le (le_totalDegree hb)
  have hg := (mem_restrictSupport_iff (R := ZMod 2)).1 (nf_mem_of_downClosed U hd hf)
  unfold totalDegree
  exact Finset.sup_le fun b hb => (echelon_sum_eq_degree b).trans_le (hg hb)

end PEqualNP.ProofComplexity.Helpers

-- Accepted project source: PEqualNP.ProofComplexity.Helpers.ExpanderSupp
/-!
# Helpers: the expansion closure of a set of holes, and peeling (for L-pcx-046)

For a bipartite graph `G` (pigeons on the left, holes on the right) and a set of holes `H`:

* a pigeon set `T` is contained in `H` (`ContainedIn G s H T`) when `T.card ≤ s` and every
  unique neighbour of `T` is in `H`;
* `supp G s H` is the union of all pigeon sets contained in `H`;
* `SuppClosed G s K S`: every `T ⊋ S` with `T.card ≤ s` has a unique neighbour outside
  `K ∪ N(S)`, where `N(S) = S.biUnion G`.

On an `(s, 2)` boundary expander and with `H.card ≤ s`: `supp G s H` is itself contained in
`H`, `2 * (supp G s H).card ≤ H.card`, and `supp G s H` is closed for `H`. Closedness passes
to any `K' ⊆ K ∪ N(S)`, and gives a pigeon to peel: a `p ∈ T \ S` with a hole of `G p` outside
`K` and not adjacent to the rest of `T`.
-/

namespace PEqualNP.ProofComplexity.Helpers

open PEqualNP.Expanders

variable {m N : ℕ} (G : BipGraph m N)

/-- `T` is contained in the hole set `H`: at most `s` pigeons, all unique neighbours in `H`. -/
def ContainedIn (s : ℕ) (H : Finset (Fin N)) (T : Finset (Fin m)) : Prop :=
  T.card ≤ s ∧ uniqueNbrs G T ⊆ H

open Classical in
/-- The support of `H`: the union of all pigeon sets contained in `H`. -/
noncomputable def supp (s : ℕ) (H : Finset (Fin N)) : Finset (Fin m) :=
  Finset.univ.filter (fun i => ∃ T, i ∈ T ∧ ContainedIn G s H T)

open Classical in
lemma mem_supp {s : ℕ} {H : Finset (Fin N)} {i : Fin m} :
    i ∈ supp G s H ↔ ∃ T, i ∈ T ∧ ContainedIn G s H T := by
  simp [supp]

/-- `S` is closed for `K`: every strictly larger pigeon set of size at most `s` has a unique
neighbour outside `K ∪ N(S)`. -/
def SuppClosed (s : ℕ) (K : Finset (Fin N)) (S : Finset (Fin m)) : Prop :=
  ∀ T : Finset (Fin m), S ⊂ T → T.card ≤ s → ¬ uniqueNbrs G T ⊆ K ∪ S.biUnion G

lemma mem_uniqueNbrs {T : Finset (Fin m)} {j : Fin N} :
    j ∈ uniqueNbrs G T ↔ (T.filter (fun i => j ∈ G i)).card = 1 := by
  simp [uniqueNbrs]

theorem uniqueNbrs_union_subset (A B : Finset (Fin m)) :
    uniqueNbrs G (A ∪ B) ⊆ uniqueNbrs G A ∪ uniqueNbrs G B := by
  intro j hj
  rw [mem_uniqueNbrs, Finset.filter_union] at hj
  rw [Finset.mem_union, mem_uniqueNbrs, mem_uniqueNbrs]
  by_cases hA : (A.filter (fun i => j ∈ G i)).card = 0
  · right
    rw [Finset.card_eq_zero] at hA
    rw [hA, Finset.empty_union] at hj
    exact hj
  · left
    have h1 : (A.filter (fun i => j ∈ G i)).card ≤ 1 :=
      hj ▸ Finset.card_le_card Finset.subset_union_left
    omega

/-- A contained set has at most half as many pigeons as `H` has holes. -/
lemma two_mul_card_le_of_containedIn {s : ℕ} (hG : IsBdryExpander G s 2)
    {H : Finset (Fin N)} {T : Finset (Fin m)} (hT : ContainedIn G s H T) :
    2 * T.card ≤ H.card :=
  (hG T hT.1).trans (Finset.card_le_card hT.2)

lemma containedIn_union {s : ℕ} (hG : IsBdryExpander G s 2) {H : Finset (Fin N)}
    (hH : H.card ≤ s) {A B : Finset (Fin m)} (hA : ContainedIn G s H A)
    (hB : ContainedIn G s H B) : ContainedIn G s H (A ∪ B) := by
  refine ⟨?_, ?_⟩
  · have h1 := two_mul_card_le_of_containedIn G hG hA
    have h2 := two_mul_card_le_of_containedIn G hG hB
    have h3 := Finset.card_union_le A B
    omega
  · exact (uniqueNbrs_union_subset G A B).trans (Finset.union_subset hA.2 hB.2)

lemma containedIn_empty (s : ℕ) (H : Finset (Fin N)) :
    ContainedIn G s H (∅ : Finset (Fin m)) := by
  refine ⟨by simp, ?_⟩
  intro j hj
  simp [uniqueNbrs] at hj

theorem supp_containedIn {s : ℕ} (hG : IsBdryExpander G s 2) {H : Finset (Fin N)}
    (hH : H.card ≤ s) : ContainedIn G s H (supp G s H) := by
  -- every subset of the support lies in a contained set
  have key : ∀ U : Finset (Fin m), U ⊆ supp G s H →
      ∃ T, U ⊆ T ∧ T ⊆ supp G s H ∧ ContainedIn G s H T := by
    intro U
    induction U using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨∅, Finset.empty_subset _, Finset.empty_subset _, containedIn_empty G s H⟩
    | insert i U _ ih =>
      intro hU
      obtain ⟨T, hUT, hTS, hT⟩ := ih ((Finset.subset_insert i U).trans hU)
      have hi : i ∈ supp G s H := hU (Finset.mem_insert_self i U)
      obtain ⟨Ti, hiTi, hTi⟩ := (mem_supp G).mp hi
      have hTiS : Ti ⊆ supp G s H := fun k hk =>
        (mem_supp G).mpr ⟨Ti, hk, hTi⟩
      refine ⟨Ti ∪ T, ?_, Finset.union_subset hTiS hTS, containedIn_union G hG hH hTi hT⟩
      exact Finset.insert_subset (Finset.mem_union_left _ hiTi)
        (hUT.trans Finset.subset_union_right)
  obtain ⟨T, h1, h2, hT⟩ := key (supp G s H) (Finset.Subset.refl _)
  rw [← Finset.Subset.antisymm h2 h1]
  exact hT

theorem two_mul_card_supp_le {s : ℕ} (hG : IsBdryExpander G s 2) {H : Finset (Fin N)}
    (hH : H.card ≤ s) : 2 * (supp G s H).card ≤ H.card :=
  two_mul_card_le_of_containedIn G hG (supp_containedIn G hG hH)

/-- A unique neighbour of `T ⊇ S` that is adjacent to `S` is a unique neighbour of `S`. -/
lemma mem_uniqueNbrs_of_subset {S T : Finset (Fin m)} (hST : S ⊆ T) {j : Fin N}
    (hj : j ∈ uniqueNbrs G T) (hjS : j ∈ S.biUnion G) : j ∈ uniqueNbrs G S := by
  rw [mem_uniqueNbrs] at hj ⊢
  obtain ⟨i, hiS, hji⟩ := Finset.mem_biUnion.mp hjS
  have h1 : (S.filter (fun i => j ∈ G i)).card ≤ 1 :=
    hj ▸ Finset.card_le_card (Finset.filter_subset_filter _ hST)
  have h2 : 0 < (S.filter (fun i => j ∈ G i)).card :=
    Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hiS, hji⟩⟩
  omega

theorem suppClosed_supp {s : ℕ} (hG : IsBdryExpander G s 2) {H : Finset (Fin N)}
    (hH : H.card ≤ s) : SuppClosed G s H (supp G s H) := by
  intro T hST hT hsub
  have hS := supp_containedIn G hG hH
  have hTH : uniqueNbrs G T ⊆ H := by
    intro j hj
    rcases Finset.mem_union.mp (hsub hj) with h | h
    · exact h
    · exact hS.2 (mem_uniqueNbrs_of_subset G hST.subset hj h)
  have hTS : T ⊆ supp G s H := fun k hk =>
    (mem_supp G).mpr ⟨T, hk, hT, hTH⟩
  exact (Finset.not_subset.mp hST.2).elim fun k ⟨hkT, hkS⟩ => hkS (hTS hkT)

theorem SuppClosed.mono {s : ℕ} {K K' : Finset (Fin N)} {S : Finset (Fin m)}
    (h : SuppClosed G s K S) (hK : K' ⊆ K ∪ S.biUnion G) : SuppClosed G s K' S := by
  intro T hST hT hsub
  apply h T hST hT
  intro j hj
  rcases Finset.mem_union.mp (hsub hj) with h1 | h1
  · exact hK h1
  · exact Finset.mem_union_right _ h1

theorem SuppClosed.peel {s : ℕ} {K : Finset (Fin N)} {S T : Finset (Fin m)}
    (h : SuppClosed G s K S) (hST : S ⊂ T) (hT : T.card ≤ s) :
    ∃ p ∈ T, p ∉ S ∧ ∃ j ∈ G p, j ∉ K ∧ j ∉ (T.erase p).biUnion G := by
  obtain ⟨j, hj, hjK⟩ := Finset.not_subset.mp (h T hST hT)
  rw [Finset.mem_union, not_or] at hjK
  obtain ⟨hjK, hjS⟩ := hjK
  rw [mem_uniqueNbrs, Finset.card_eq_one] at hj
  obtain ⟨p, hp⟩ := hj
  have hpmem : p ∈ T.filter (fun i => j ∈ G i) := hp ▸ Finset.mem_singleton_self p
  obtain ⟨hpT, hjp⟩ := Finset.mem_filter.mp hpmem
  refine ⟨p, hpT, ?_, j, hjp, hjK, ?_⟩
  · intro hpS
    exact hjS (Finset.mem_biUnion.mpr ⟨p, hpS, hjp⟩)
  · intro hj'
    obtain ⟨q, hq, hjq⟩ := Finset.mem_biUnion.mp hj'
    obtain ⟨hqp, hqT⟩ := Finset.mem_erase.mp hq
    have : q ∈ T.filter (fun i => j ∈ G i) := Finset.mem_filter.mpr ⟨hqT, hjq⟩
    rw [hp, Finset.mem_singleton] at this
    exact hqp this

lemma uniqueNbrs_singleton (i : Fin m) : uniqueNbrs G {i} = G i := by
  ext j
  rw [mem_uniqueNbrs]
  by_cases hj : j ∈ G i
  · simp [Finset.filter_singleton, hj]
  · simp [Finset.filter_singleton, hj]

theorem mem_supp_self {s : ℕ} (hs : 1 ≤ s) (i : Fin m) {H : Finset (Fin N)}
    (hi : G i ⊆ H) : i ∈ supp G s H :=
  (mem_supp G).mpr ⟨{i}, Finset.mem_singleton_self i,
    by simpa using hs, by rw [uniqueNbrs_singleton]; exact hi⟩

end PEqualNP.ProofComplexity.Helpers

-- Accepted project source: PEqualNP.ProofComplexity.Helpers.LocalSat
/-!
# Helpers: local satisfiability on a pigeonhole graph (helper module, proofs only)

Helper H4 of the route to L-pcx-046 (`notes/pcx-046-route.md`). For a bipartite graph `G` and
a set `S` of pigeons:

* `localSat G S α`: the point `α` respects every hole and seats every pigeon of `S`;
* `locIdeal G S`: the polynomials vanishing at every such point. It contains the Boolean
  axioms, the hole products and the pigeon clauses of `S`, is closed under multiplication by a
  variable, grows with `S`, and does not contain `1` when `S = ∅`;
* `monoHoles G a`: the holes of the edges of a monomial;
* `pigeonClause G i`: the pigeon clause of `i`, as it stands in `graphPHP G`;
* `cnfSystem_graphPHP_cases`: the three shapes of a member of `cnfSystem (graphPHP G)`.
-/

namespace PEqualNP.ProofComplexity.Helpers

open MvPolynomial
open PEqualNP.Expanders

variable {m N : ℕ} (G : BipGraph m N)

/-- The point `α` respects every hole (two edges at one hole with different pigeons are never
both `1`) and every pigeon of `S` has an edge with value `1`. -/
def localSat (S : Finset (Fin m)) (α : GEdge G → ZMod 2) : Prop :=
  (∀ e e' : GEdge G, e.1.2 = e'.1.2 → e.1.1 ≠ e'.1.1 → α e * α e' = 0) ∧
  ∀ i ∈ S, ∃ e : GEdge G, e.1.1 = i ∧ α e = 1

/-- The polynomials vanishing at every point that satisfies `localSat G S`. -/
noncomputable def locIdeal (S : Finset (Fin m)) :
    Submodule (ZMod 2) (MvPolynomial (GEdge G) (ZMod 2)) :=
  ⨅ (α : GEdge G → ZMod 2) (_ : localSat G S α),
    LinearMap.ker (MvPolynomial.aeval (R := ZMod 2) α).toLinearMap

theorem mem_locIdeal {S : Finset (Fin m)} {f : MvPolynomial (GEdge G) (ZMod 2)} :
    f ∈ locIdeal G S ↔ ∀ α, localSat G S α → eval α f = 0 := by
  simp only [locIdeal, Submodule.mem_iInf, LinearMap.mem_ker, AlgHom.toLinearMap_apply]
  rfl

/-- The holes of the edges of a monomial. -/
def monoHoles (a : GEdge G →₀ ℕ) : Finset (Fin N) := a.support.image (fun e => e.1.2)

/-- The pigeon clause of `i`: all positive literals on the edges at `i`. -/
def pigeonClause (i : Fin m) : Clause (GEdge G) :=
  Finset.univ.filter (fun l : Literal (GEdge G) => l.1.1.1 = i ∧ l.2 = true)

theorem locIdeal_mono {S S' : Finset (Fin m)} (h : S ⊆ S') : locIdeal G S ≤ locIdeal G S' := by
  intro f hf
  rw [mem_locIdeal] at hf ⊢
  exact fun α hα => hf α ⟨hα.1, fun i hi => hα.2 i (h hi)⟩

theorem X_mul_mem_locIdeal {S : Finset (Fin m)} (v : GEdge G)
    {f : MvPolynomial (GEdge G) (ZMod 2)} (hf : f ∈ locIdeal G S) : X v * f ∈ locIdeal G S := by
  rw [mem_locIdeal] at hf ⊢
  intro α hα
  rw [map_mul, hf α hα, mul_zero]

theorem bool_mem_locIdeal (S : Finset (Fin m)) (v : GEdge G) :
    X v * X v + X v ∈ locIdeal G S := by
  rw [mem_locIdeal]
  intro α _
  have h : ∀ x : ZMod 2, x * x + x = 0 := by decide
  simpa using h (α v)

theorem hole_mem_locIdeal (S : Finset (Fin m)) {e e' : GEdge G}
    (h1 : e.1.2 = e'.1.2) (h2 : e.1.1 ≠ e'.1.1) : X e * X e' ∈ locIdeal G S := by
  rw [mem_locIdeal]
  intro α hα
  simpa using hα.1 e e' h1 h2

theorem pigeon_mem_locIdeal {S : Finset (Fin m)} {i : Fin m} (hi : i ∈ S) :
    clausePoly (pigeonClause G i) ∈ locIdeal G S := by
  rw [mem_locIdeal]
  intro α hα
  obtain ⟨e, he, hαe⟩ := hα.2 i hi
  have h2 : (1 : ZMod 2) + 1 = 0 := by decide
  rw [clausePoly, map_prod]
  refine Finset.prod_eq_zero (i := ((e, true) : Literal (GEdge G))) ?_ ?_
  · simp [pigeonClause, he]
  · simp [hαe, h2]

theorem one_not_mem_locIdeal_empty : (1 : MvPolynomial (GEdge G) (ZMod 2)) ∉ locIdeal G ∅ := by
  rw [mem_locIdeal]
  intro h
  have h0 := h (fun _ => 0) ⟨fun _ _ _ _ => mul_zero _, fun i hi => absurd hi (by simp)⟩
  rw [map_one] at h0
  exact one_ne_zero h0

theorem card_monoHoles_le (a : GEdge G →₀ ℕ) : (monoHoles G a).card ≤ a.degree := by
  refine Finset.card_image_le.trans ?_
  rw [Finsupp.degree_apply, Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun v hv => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)

/-- The polynomial of the pigeon clause is the product of `1 + X e` over its literals. -/
theorem localSat_clausePoly_pigeonClause (i : Fin m) :
    clausePoly (pigeonClause G i)
      = ∏ l ∈ pigeonClause G i, (1 + X l.1 : MvPolynomial (GEdge G) (ZMod 2)) := by
  rw [clausePoly]
  refine Finset.prod_congr rfl fun l hl => ?_
  have hl2 : l.2 = true := (Finset.mem_filter.mp hl).2.2
  simp only [hl2, ite_true]

/-- The literals of the pigeon clause of `i` are in bijection with the holes of `i`. -/
theorem localSat_card_pigeonClause (i : Fin m) : (pigeonClause G i).card = (G i).card := by
  refine Finset.card_bij (fun l _ => l.1.1.2) ?_ ?_ ?_
  · intro l hl
    have h := (Finset.mem_filter.mp hl).2.1
    have := l.1.2
    rwa [h] at this
  · rintro ⟨⟨⟨p, j⟩, hpj⟩, b⟩ hl ⟨⟨⟨p', j'⟩, hpj'⟩, b'⟩ hl' hjj
    have h := (Finset.mem_filter.mp hl).2
    have h' := (Finset.mem_filter.mp hl').2
    simp only at h h' hjj
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rfl, rfl⟩ := h'
    subst hjj
    rfl
  · intro j hj
    exact ⟨((⟨(i, j), hj⟩ : GEdge G), true), by simp [pigeonClause], rfl⟩

theorem totalDegree_pigeonClause (i : Fin m) :
    (clausePoly (pigeonClause G i)).totalDegree = (G i).card := by
  classical
  have hdeg : ∀ v : GEdge G, (1 + X v : MvPolynomial (GEdge G) (ZMod 2)).totalDegree = 1 := by
    intro v
    rw [totalDegree_add_eq_right_of_totalDegree_lt
      (by rw [totalDegree_one, totalDegree_X]; exact Nat.zero_lt_one), totalDegree_X]
  have hne : ∀ v : GEdge G, (1 + X v : MvPolynomial (GEdge G) (ZMod 2)) ≠ 0 := by
    intro v h0
    have := hdeg v
    rw [h0, totalDegree_zero] at this
    exact Nat.zero_ne_one this
  rw [localSat_clausePoly_pigeonClause, ← localSat_card_pigeonClause]
  generalize pigeonClause G i = s
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha,
      totalDegree_mul_of_isDomain (hne _) (Finset.prod_ne_zero_iff.mpr fun l _ => hne _),
      ih, hdeg, add_comm]

theorem monoHoles_pigeonClause (i : Fin m) :
    ∀ a ∈ (clausePoly (pigeonClause G i)).support, monoHoles G a ⊆ G i := by
  classical
  intro a ha j hj
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
  have hv : e ∈ (clausePoly (pigeonClause G i)).vars :=
    (mem_vars_iff_mem_support e).mpr ⟨a, ha, he⟩
  rw [localSat_clausePoly_pigeonClause] at hv
  obtain ⟨l, hl, hel⟩ := Finset.mem_biUnion.mp (vars_prod _ hv)
  have hel' := vars_add_subset _ _ hel
  rw [vars_one, vars_X, Finset.empty_union, Finset.mem_singleton] at hel'
  have h := (Finset.mem_filter.mp hl).2.1
  subst hel'
  have := l.1.2
  rwa [h] at this

theorem cnfSystem_graphPHP_cases {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f ∈ cnfSystem (graphPHP G)) :
    (∃ v, f = X v * X v + X v) ∨ (∃ i, f = clausePoly (pigeonClause G i)) ∨
    ∃ e e' : GEdge G, e.1.2 = e'.1.2 ∧ e.1.1 ≠ e'.1.1 ∧ f = X e * X e' := by
  rcases hf with ⟨v, rfl⟩ | ⟨C, hC, rfl⟩
  · exact Or.inl ⟨v, rfl⟩
  · rcases hC with ⟨i, rfl⟩ | ⟨e, e', h1, h2, rfl⟩
    · exact Or.inr (Or.inl ⟨i, rfl⟩)
    · refine Or.inr (Or.inr ⟨e, e', h1, h2, ?_⟩)
      have hne : ((e, false) : Literal (GEdge G)) ≠ (e', false) := by
        intro h
        exact h2 (by rw [(Prod.mk.inj h).1])
      rw [clausePoly, Finset.prod_pair hne]
      simp

end PEqualNP.ProofComplexity.Helpers

-- Accepted project source: PEqualNP.ProofComplexity.Helpers.LocalNF
/-!
# Helpers: the local normal form facts on a pigeonhole graph (helper module, proofs only)

Helper H5 of the route to L-pcx-046 (`notes/pcx-046-route.md`, section 1.5). With
`nf (locIdeal G S)` the echelon normal form modulo the polynomials vanishing on the points that
respect every hole and seat every pigeon of `S`:

* `nf_locIdeal_holes` (locality): the monomials of the normal form of a monomial `a` have their
  holes among the holes of `a` and the neighbours of `S`;
* `nf_locIdeal_insert` (peel one pigeon): adding a pigeon `p` with a neighbour `j` that is
  neither a neighbour of `S` nor a hole of `a` does not change the normal form of `a`;
* `nf_locIdeal_ext` (extension): if `S` is closed for `K`, the normal form of a monomial with
  holes in `K` is the same for every `T` between `S` and size `s`.

The two substitutions are `bind₁` maps: `localNF_zeroOut` sets to zero every variable whose hole
is outside a set of holes, and `localNF_override` rewrites one hole `j` (the edge from `p` is
set to one, the other edges at `j` to zero).
-/

namespace PEqualNP.ProofComplexity.Helpers

open MvPolynomial
open PEqualNP.Expanders

variable {m N : ℕ} (G : BipGraph m N)

/-- Evaluating a substituted polynomial is evaluating at the substituted point. -/
theorem localNF_eval_bind₁ {σ : Type} (α : σ → ZMod 2) (φ : σ → MvPolynomial σ (ZMod 2))
    (f : MvPolynomial σ (ZMod 2)) :
    eval α (bind₁ φ f) = eval (fun e => eval α (φ e)) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p e hp => rw [map_mul, map_mul, map_mul, hp, bind₁_X_right, eval_X]

/-- A polynomial is the sum of its terms; the image of a sum of terms under a linear map. -/
theorem localNF_map_eq_sum (L : MvPolynomial (GEdge G) (ZMod 2) →ₐ[ZMod 2]
    MvPolynomial (GEdge G) (ZMod 2)) (w : MvPolynomial (GEdge G) (ZMod 2)) :
    L w = ∑ c ∈ w.support, L (monomial c (w.coeff c)) := by
  conv_lhs => rw [← support_sum_monomial_coeff w]
  rw [map_sum]

/-! ### Zeroing the variables whose hole is outside `K` -/

/-- The substitution that sets to zero every variable whose hole is outside `K`. -/
noncomputable def localNF_zeroOut (K : Finset (Fin N)) (e : GEdge G) :
    MvPolynomial (GEdge G) (ZMod 2) :=
  if e.1.2 ∈ K then X e else 0

theorem localNF_zeroOut_monomial (K : Finset (Fin N)) (b : GEdge G →₀ ℕ) (c : ZMod 2) :
    bind₁ (localNF_zeroOut G K) (monomial b c)
      = if monoHoles G b ⊆ K then monomial b c else 0 := by
  rw [bind₁_monomial]
  split_ifs with h
  · have hprod : ∏ e ∈ b.support, localNF_zeroOut G K e ^ b e
        = ∏ e ∈ b.support, (X e : MvPolynomial (GEdge G) (ZMod 2)) ^ b e := by
      refine Finset.prod_congr rfl fun e he => ?_
      rw [localNF_zeroOut, ite_eq_left (h (Finset.mem_image_of_mem _ he))]
    rw [hprod, monomial_eq]
    rfl
  · obtain ⟨x, hx, hxK⟩ := Finset.not_subset.mp h
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.prod_eq_zero he, mul_zero]
    rw [localNF_zeroOut, ite_eq_right hxK, zero_pow (Finsupp.mem_support_iff.mp he)]

theorem localNF_zeroOut_mem {S : Finset (Fin m)} {K : Finset (Fin N)} (hK : S.biUnion G ⊆ K)
    {f : MvPolynomial (GEdge G) (ZMod 2)} (hf : f ∈ locIdeal G S) :
    bind₁ (localNF_zeroOut G K) f ∈ locIdeal G S := by
  rw [mem_locIdeal] at hf ⊢
  intro α hα
  rw [localNF_eval_bind₁]
  refine hf _ ⟨?_, ?_⟩
  · intro e e' h1 h2
    show eval α (localNF_zeroOut G K e) * eval α (localNF_zeroOut G K e') = 0
    by_cases h : e.1.2 ∈ K
    · by_cases h' : e'.1.2 ∈ K
      · rw [localNF_zeroOut, localNF_zeroOut, ite_eq_left h, ite_eq_left h', eval_X, eval_X]
        exact hα.1 e e' h1 h2
      · rw [localNF_zeroOut, localNF_zeroOut, ite_eq_right h', map_zero, mul_zero]
    · rw [localNF_zeroOut, ite_eq_right h, map_zero, zero_mul]
  · intro i hi
    obtain ⟨e, he, h1⟩ := hα.2 i hi
    have hmem : e.1.2 ∈ K := by
      refine hK (Finset.mem_biUnion.mpr ⟨i, hi, ?_⟩)
      rw [← he]
      exact e.2
    refine ⟨e, he, ?_⟩
    show eval α (localNF_zeroOut G K e) = 1
    rw [localNF_zeroOut, ite_eq_left hmem, eval_X, h1]

theorem localNF_zeroOut_eq (K : Finset (Fin N)) (r : MvPolynomial (GEdge G) (ZMod 2)) :
    bind₁ (localNF_zeroOut G K) r
      = ∑ b ∈ r.support.filter (fun b => monoHoles G b ⊆ K), monomial b (r.coeff b) := by
  rw [localNF_map_eq_sum, Finset.sum_filter]
  exact Finset.sum_congr rfl fun b _ => localNF_zeroOut_monomial G K b _

theorem localNF_support_sum_filter (K : Finset (Fin N)) (r : MvPolynomial (GEdge G) (ZMod 2)) :
    (∑ b ∈ r.support.filter (fun b => monoHoles G b ⊆ K),
        monomial b (r.coeff b)).support
      ⊆ r.support.filter (fun b => monoHoles G b ⊆ K) := by
  intro b hb
  obtain ⟨c, hc, hbc⟩ := Finset.mem_biUnion.mp (support_sum hb)
  have hbc' := Finset.mem_singleton.mp (support_monomial_subset hbc)
  rw [hbc']
  exact hc

/-- Locality: the monomials of the normal form of `a` modulo `locIdeal G S` have their holes
among the holes of `a` and the neighbours of `S`. -/
theorem nf_locIdeal_holes (S : Finset (Fin m)) (a : GEdge G →₀ ℕ) :
    ∀ b ∈ (nf (locIdeal G S) (monomial a 1)).support,
      monoHoles G b ⊆ monoHoles G a ∪ S.biUnion G := by
  have hsub := localNF_support_sum_filter G (monoHoles G a ∪ S.biUnion G)
    (nf (locIdeal G S) (monomial a 1))
  have heq : nf (locIdeal G S) (monomial a 1)
      = ∑ b ∈ (nf (locIdeal G S) (monomial a 1)).support.filter
          (fun b => monoHoles G b ⊆ monoHoles G a ∪ S.biUnion G),
          monomial b ((nf (locIdeal G S) (monomial a 1)).coeff b) := by
    refine nf_unique (locIdeal G S) ?_ ?_
    · intro b hb
      exact nf_support_isStd (locIdeal G S) (monomial a 1) b (Finset.mem_filter.mp (hsub hb)).1
    · have h := localNF_zeroOut_mem G (S := S) (K := monoHoles G a ∪ S.biUnion G)
        Finset.subset_union_right (nf_sub_mem (locIdeal G S) (monomial a 1))
      rw [map_sub, localNF_zeroOut_monomial, ite_eq_left Finset.subset_union_left,
        localNF_zeroOut_eq] at h
      exact h
  intro b hb
  have hb' : b ∈ (∑ b ∈ (nf (locIdeal G S) (monomial a 1)).support.filter
      (fun b => monoHoles G b ⊆ monoHoles G a ∪ S.biUnion G),
      monomial b ((nf (locIdeal G S) (monomial a 1)).coeff b)).support := by
    rw [← heq]
    exact hb
  exact (Finset.mem_filter.mp (hsub hb')).2

/-! ### Overriding one hole -/

/-- The substitution at hole `j`: the edge from `p` becomes one, the other edges at `j` become
zero, every other variable is kept. -/
noncomputable def localNF_override (p : Fin m) (j : Fin N) (e : GEdge G) :
    MvPolynomial (GEdge G) (ZMod 2) :=
  if e.1.2 = j then (if e.1.1 = p then 1 else 0) else X e

/-- A monomial with the edges at hole `j` dropped. -/
noncomputable def localNF_drop (j : Fin N) (c : GEdge G →₀ ℕ) : GEdge G →₀ ℕ :=
  c.filter (fun e => e.1.2 ≠ j)

theorem localNF_override_monomial_of_notMem (p : Fin m) {j : Fin N} {b : GEdge G →₀ ℕ}
    (hb : j ∉ monoHoles G b) (c : ZMod 2) :
    bind₁ (localNF_override G p j) (monomial b c) = monomial b c := by
  rw [bind₁_monomial]
  have hprod : ∏ e ∈ b.support, localNF_override G p j e ^ b e
      = ∏ e ∈ b.support, (X e : MvPolynomial (GEdge G) (ZMod 2)) ^ b e := by
    refine Finset.prod_congr rfl fun e he => ?_
    have hne : e.1.2 ≠ j := fun h => hb (h ▸ Finset.mem_image_of_mem _ he)
    rw [localNF_override, ite_eq_right hne]
  rw [hprod, monomial_eq]
  rfl

theorem localNF_override_mem {S : Finset (Fin m)} {p : Fin m} {j : Fin N} (hj : j ∈ G p)
    (hjS : j ∉ S.biUnion G) {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f ∈ locIdeal G (insert p S)) :
    bind₁ (localNF_override G p j) f ∈ locIdeal G S := by
  rw [mem_locIdeal] at hf ⊢
  intro α hα
  rw [localNF_eval_bind₁]
  refine hf _ ⟨?_, ?_⟩
  · intro e e' h1 h2
    show eval α (localNF_override G p j e) * eval α (localNF_override G p j e') = 0
    by_cases h : e.1.2 = j
    · have h' : e'.1.2 = j := h1 ▸ h
      by_cases hp : e.1.1 = p
      · have hp' : ¬ e'.1.1 = p := fun h3 => h2 (hp.trans h3.symm)
        rw [localNF_override, localNF_override, ite_eq_left h', ite_eq_right hp', map_zero,
          mul_zero]
      · rw [localNF_override, ite_eq_left h, ite_eq_right hp, map_zero, zero_mul]
    · have h' : ¬ e'.1.2 = j := fun h3 => h (h1.trans h3)
      rw [localNF_override, localNF_override, ite_eq_right h, ite_eq_right h', eval_X, eval_X]
      exact hα.1 e e' h1 h2
  · intro i hi
    rcases Finset.mem_insert.mp hi with h | h
    · refine ⟨⟨(p, j), hj⟩, h.symm, ?_⟩
      show eval α (localNF_override G p j ⟨(p, j), hj⟩) = 1
      rw [localNF_override, ite_eq_left rfl, ite_eq_left rfl, map_one]
    · obtain ⟨e, he, h1⟩ := hα.2 i h
      have hne : ¬ e.1.2 = j := by
        intro h3
        refine hjS (Finset.mem_biUnion.mpr ⟨i, h, ?_⟩)
        rw [← he, ← h3]
        exact e.2
      refine ⟨e, he, ?_⟩
      show eval α (localNF_override G p j e) = 1
      rw [localNF_override, ite_eq_right hne, eval_X, h1]

/-- The image of a monomial under the override is zero or the monomial with the edges at `j`
dropped. -/
theorem localNF_override_monomial_one (p : Fin m) (j : Fin N) (c : GEdge G →₀ ℕ) :
    bind₁ (localNF_override G p j) (monomial c 1) = 0 ∨
      bind₁ (localNF_override G p j) (monomial c 1) = monomial (localNF_drop G j c) 1 := by
  rw [bind₁_monomial, C_1, one_mul]
  by_cases hz : ∃ e ∈ c.support, e.1.2 = j ∧ ¬ e.1.1 = p
  · obtain ⟨e, he, h1, h2⟩ := hz
    left
    refine Finset.prod_eq_zero he ?_
    rw [localNF_override, ite_eq_left h1, ite_eq_right h2, zero_pow (Finsupp.mem_support_iff.mp he)]
  · right
    have hz' : ∀ e ∈ c.support, e.1.2 = j → e.1.1 = p := fun e he h =>
      by_contra fun h2 => hz ⟨e, he, h, h2⟩
    rw [monomial_eq, C_1, one_mul, Finsupp.prod, localNF_drop, Finsupp.support_filter,
      Finset.prod_filter]
    refine Finset.prod_congr rfl fun e he => ?_
    by_cases h : e.1.2 = j
    · rw [ite_eq_right (not_not.mpr h), localNF_override, ite_eq_left h,
        ite_eq_left (hz' e he h), one_pow]
    · rw [ite_eq_left h, Finsupp.filter_apply_pos (p := fun e : GEdge G => e.1.2 ≠ j) (f := c) h,
        localNF_override, ite_eq_right h]

/-- Dropping the edges at a hole gives the same monomial or one of smaller degree. -/
theorem localNF_drop_eq_or_degree_lt (j : Fin N) (c : GEdge G →₀ ℕ) :
    localNF_drop G j c = c ∨ (localNF_drop G j c).degree < c.degree := by
  have hsplit : localNF_drop G j c + c.filter (fun e => ¬ e.1.2 ≠ j) = c :=
    Finsupp.filter_add_filter_not c _
  by_cases h0 : c.filter (fun e => ¬ e.1.2 ≠ j) = 0
  · left
    rw [h0, add_zero] at hsplit
    exact hsplit
  · right
    have hdeg : (localNF_drop G j c).degree + (c.filter (fun e => ¬ e.1.2 ≠ j)).degree
        = c.degree := by
      rw [← map_add, hsplit]
    have hpos : 0 < (c.filter (fun e => ¬ e.1.2 ≠ j)).degree :=
      Nat.pos_of_ne_zero fun h => h0 ((Finsupp.degree_eq_zero_iff _).mp h)
    omega

/-- The override maps the span of the monomials below `b` into itself. -/
theorem localNF_override_mem_restrictSupport (p : Fin m) (j : Fin N) {b : GEdge G →₀ ℕ}
    {w : MvPolynomial (GEdge G) (ZMod 2)}
    (hw : w ∈ restrictSupport (ZMod 2) {d : GEdge G →₀ ℕ | MonoLt d b}) :
    bind₁ (localNF_override G p j) w
      ∈ restrictSupport (ZMod 2) {d : GEdge G →₀ ℕ | MonoLt d b} := by
  rw [localNF_map_eq_sum]
  refine Submodule.sum_mem _ fun c hc => ?_
  have hcb : MonoLt c b :=
    (show (↑w.support : Set (GEdge G →₀ ℕ)) ⊆ {d | MonoLt d b} from hw) (Finset.mem_coe.mpr hc)
  have hsm : monomial c (w.coeff c)
      = w.coeff c • (monomial c 1 : MvPolynomial (GEdge G) (ZMod 2)) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hsm, map_smul]
  refine Submodule.smul_mem _ _ ?_
  rcases localNF_override_monomial_one G p j c with h | h
  · rw [h]
    exact Submodule.zero_mem _
  · rw [h]
    refine (show (↑(monomial (localNF_drop G j c) (1 : ZMod 2)).support : Set (GEdge G →₀ ℕ))
      ⊆ {d | MonoLt d b} from ?_)
    intro d hd
    have hd' : d = localNF_drop G j c :=
      Finset.mem_singleton.mp (support_monomial_subset (Finset.mem_coe.mp hd))
    rw [hd']
    show MonoLt (localNF_drop G j c) b
    rcases localNF_drop_eq_or_degree_lt G j c with h' | h'
    · rw [h']
      exact hcb
    · exact monoLt_of_degree_lt (lt_of_lt_of_le h' (degree_le_of_monoLt hcb))

/-- Peel one pigeon: adding a pigeon `p` with a neighbour `j` that is neither a neighbour of `S`
nor a hole of `a` does not change the normal form of `a`. -/
theorem nf_locIdeal_insert {S : Finset (Fin m)} {p : Fin m} {j : Fin N}
    (hp : p ∉ S) (hj : j ∈ G p) (hjS : j ∉ S.biUnion G) {a : GEdge G →₀ ℕ}
    (ha : j ∉ monoHoles G a) :
    nf (locIdeal G (insert p S)) (monomial a 1) = nf (locIdeal G S) (monomial a 1) := by
  have _ := hp
  refine nf_unique (locIdeal G (insert p S)) ?_ ?_
  · intro b hb hmem
    have hstd := nf_support_isStd (locIdeal G S) (monomial a 1) b hb
    refine hstd ?_
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hmem
    have hbj : j ∉ monoHoles G b := by
      intro h
      rcases Finset.mem_union.mp (nf_locIdeal_holes G S a b hb h) with h' | h'
      · exact ha h'
      · exact hjS h'
    have himg := congrArg (bind₁ (localNF_override G p j)) huw
    rw [map_add, localNF_override_monomial_of_notMem G p hbj] at himg
    rw [← himg]
    exact Submodule.add_mem_sup (localNF_override_mem G hj hjS hu)
      (localNF_override_mem_restrictSupport G p j hw)
  · exact locIdeal_mono G (Finset.subset_insert p S)
      (nf_sub_mem (locIdeal G S) (monomial a 1))

/-- Extension: if `S` is closed for `K`, the normal form of a monomial with holes in `K` is the
same modulo `locIdeal G T` for every `T` with `S ⊆ T` and `T.card ≤ s`. -/
theorem nf_locIdeal_ext {s : ℕ} {K : Finset (Fin N)} {S T : Finset (Fin m)}
    (hcl : SuppClosed G s K S) (hST : S ⊆ T) (hT : T.card ≤ s)
    {a : GEdge G →₀ ℕ} (ha : monoHoles G a ⊆ K) :
    nf (locIdeal G T) (monomial a 1) = nf (locIdeal G S) (monomial a 1) := by
  have key : ∀ n : ℕ, ∀ T : Finset (Fin m), S ⊆ T → T.card ≤ s → T.card = n →
      nf (locIdeal G T) (monomial a 1) = nf (locIdeal G S) (monomial a 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro T hST hT hn
      by_cases hTS : T = S
      · rw [hTS]
      · have hlt : S ⊂ T := hST.ssubset_of_ne (Ne.symm hTS)
        obtain ⟨p, hpT, hpS, j, hj, hjK, hjT⟩ := SuppClosed.peel (G := G) hcl hlt hT
        have h1 := nf_locIdeal_insert G (S := T.erase p) (p := p) (j := j) (by simp) hj hjT
          (a := a) (fun h => hjK (ha h))
        rw [Finset.insert_erase hpT] at h1
        rw [h1]
        refine ih (T.erase p).card ?_ (T.erase p) ?_ ?_ rfl
        · rw [← hn]
          exact Finset.card_erase_lt_of_mem hpT
        · exact Finset.subset_erase.mpr ⟨hST, hpS⟩
        · exact (Finset.card_erase_le).trans hT
  exact key T.card T hST hT rfl

end PEqualNP.ProofComplexity.Helpers

-- Accepted project source: PEqualNP.ProofComplexity.Helpers.GraphPHPReduction
/-!
# Helpers: the pseudo reduction operator of graph pigeonhole (helper module, proofs only)

Helper H6 of the route to L-pcx-046 (`notes/pcx-046-route.md`), the assembly. For a bipartite
graph `G` and a size bound `s`:

* `pseudoR G s`: the linear operator sending a monomial `a` to its echelon normal form modulo
  the local ideal of the support of the holes of `a`;
* `pseudoR_eq_nf`: on a polynomial of small degree whose monomials have their holes in
  `K ∪ N(supp K)`, the operator is the normal form modulo the local ideal of `supp K`;
* `pseudoR_mul`, `pseudoR_axiom`, `pseudoR_one`: the three properties of Razborov's criterion;
* `graphPHP_no_pc_refutation`: on an `(s, 2)` boundary expander with `1 ≤ s` and `D ≤ s`, the
  pigeonhole formula has no polynomial calculus refutation of degree `D` over `ZMod 2`.
-/

namespace PEqualNP.ProofComplexity.Helpers

open MvPolynomial
open PEqualNP.Expanders

variable {m N : ℕ} (G : BipGraph m N)

/-- The pseudo reduction operator: a monomial goes to its normal form modulo the local ideal
of the support of its holes. -/
noncomputable def pseudoR (s : ℕ) :
    MvPolynomial (GEdge G) (ZMod 2) →ₗ[ZMod 2] MvPolynomial (GEdge G) (ZMod 2) :=
  (basisMonomials (GEdge G) (ZMod 2)).constr (ZMod 2)
    (fun a => nf (locIdeal G (supp G s (monoHoles G a))) (monomial a 1))

theorem pseudoR_monomial (s : ℕ) (a : GEdge G →₀ ℕ) :
    pseudoR G s (monomial a 1) = nf (locIdeal G (supp G s (monoHoles G a))) (monomial a 1) := by
  have h := Module.Basis.constr_basis (basisMonomials (GEdge G) (ZMod 2)) (ZMod 2)
    (fun a => nf (locIdeal G (supp G s (monoHoles G a))) (monomial a 1)) a
  simpa only [pseudoR, coe_basisMonomials] using h

/-- The holes of `a` times a variable: one more hole. -/
theorem monoHoles_add_single (a : GEdge G →₀ ℕ) (v : GEdge G) :
    monoHoles G (a + Finsupp.single v 1) = insert v.1.2 (monoHoles G a) := by
  unfold monoHoles
  rw [support_add_single_one, Finset.image_insert]

/-- If every variable of `f` has its hole in `K`, so has every monomial of `f`. -/
theorem monoHoles_subset_of_vars {f : MvPolynomial (GEdge G) (ZMod 2)} {K : Finset (Fin N)}
    (h : ∀ e ∈ f.vars, e.1.2 ∈ K) : ∀ a ∈ f.support, monoHoles G a ⊆ K := by
  classical
  intro a ha j hj
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
  exact h e ((mem_vars_iff_mem_support e).mpr ⟨a, ha, he⟩)

/-- The common lemma of the route, on one monomial. -/
theorem pseudoR_monomial_eq_nf {s D : ℕ} (hG : IsBdryExpander G s 2) (hD : D ≤ s)
    {K : Finset (Fin N)} (hK : K.card ≤ D) {a : GEdge G →₀ ℕ} (ha : a.degree ≤ D)
    (haK : monoHoles G a ⊆ K ∪ (supp G s K).biUnion G) :
    pseudoR G s (monomial a 1) = nf (locIdeal G (supp G s K)) (monomial a 1) := by
  rw [pseudoR_monomial]
  have h3 := card_monoHoles_le G a
  have hH : (monoHoles G a).card ≤ s := h3.trans (ha.trans hD)
  have hKs : K.card ≤ s := hK.trans hD
  have h1 := two_mul_card_supp_le G hG hH
  have h2 := two_mul_card_supp_le G hG hKs
  have hT : (supp G s (monoHoles G a) ∪ supp G s K).card ≤ s := by
    have := Finset.card_union_le (supp G s (monoHoles G a)) (supp G s K)
    omega
  have e1 := nf_locIdeal_ext G (suppClosed_supp G hG hH) Finset.subset_union_left hT
    (subset_refl (monoHoles G a))
  have e2 := nf_locIdeal_ext G (SuppClosed.mono G (suppClosed_supp G hG hKs) haK)
    Finset.subset_union_right hT (subset_refl (monoHoles G a))
  exact e1.symm.trans e2

theorem pseudoR_eq_nf {s D : ℕ} (hG : IsBdryExpander G s 2) (hD : D ≤ s)
    {K : Finset (Fin N)} (hK : K.card ≤ D) {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f.totalDegree ≤ D)
    (hfK : ∀ a ∈ f.support, monoHoles G a ⊆ K ∪ (supp G s K).biUnion G) :
    pseudoR G s f = nf (locIdeal G (supp G s K)) f := by
  have hf' : f = ∑ a ∈ f.support, f.coeff a • monomial a (1 : ZMod 2) := by
    conv_lhs => rw [f.as_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [smul_monomial, smul_eq_mul, mul_one]
  have e : ∀ L : MvPolynomial (GEdge G) (ZMod 2) →ₗ[ZMod 2] MvPolynomial (GEdge G) (ZMod 2),
      L f = ∑ a ∈ f.support, f.coeff a • L (monomial a 1) := by
    intro L
    conv_lhs => rw [hf']
    simp only [map_sum, map_smul]
  rw [e (pseudoR G s), e (nf (locIdeal G (supp G s K)))]
  exact Finset.sum_congr rfl fun a ha => by
    rw [pseudoR_monomial_eq_nf G hG hD hK ((le_totalDegree ha).trans hf) (hfK a ha)]

theorem pseudoR_mul {s D : ℕ} (hG : IsBdryExpander G s 2) (hD : D ≤ s)
    (v : GEdge G) (a : GEdge G →₀ ℕ) (ha : a.degree + 1 ≤ D) :
    pseudoR G s (X v * monomial a 1) = pseudoR G s (X v * pseudoR G s (monomial a 1)) := by
  have hdeg : (a + Finsupp.single v 1).degree = a.degree + 1 := by
    rw [map_add, Finsupp.degree_single]
  have hK0 : (monoHoles G (a + Finsupp.single v 1)).card ≤ D :=
    (card_monoHoles_le G _).trans (by omega)
  have hmono : X v * monomial a (1 : ZMod 2) = monomial (a + Finsupp.single v 1) 1 := by
    rw [mul_comm, monomial_one_mul_X]
  have haK0 : monoHoles G a ⊆ monoHoles G (a + Finsupp.single v 1) := by
    rw [monoHoles_add_single]
    exact Finset.subset_insert _ _
  have e1 : pseudoR G s (monomial a 1)
      = nf (locIdeal G (supp G s (monoHoles G (a + Finsupp.single v 1)))) (monomial a 1) :=
    pseudoR_monomial_eq_nf G hG hD hK0 (by omega) (haK0.trans Finset.subset_union_left)
  have e2 : pseudoR G s (X v * monomial a 1)
      = nf (locIdeal G (supp G s (monoHoles G (a + Finsupp.single v 1))))
          (X v * monomial a 1) := by
    rw [hmono]
    exact pseudoR_monomial_eq_nf G hG hD hK0 (by omega) Finset.subset_union_left
  have hq : (nf (locIdeal G (supp G s (monoHoles G (a + Finsupp.single v 1))))
      (monomial a 1)).totalDegree ≤ a.degree :=
    (totalDegree_nf_le _ _).trans (totalDegree_monomial_one a).le
  have e3 : pseudoR G s (X v * nf (locIdeal G (supp G s (monoHoles G (a + Finsupp.single v 1))))
        (monomial a 1))
      = nf (locIdeal G (supp G s (monoHoles G (a + Finsupp.single v 1))))
          (X v * nf (locIdeal G (supp G s (monoHoles G (a + Finsupp.single v 1))))
            (monomial a 1)) := by
    refine pseudoR_eq_nf G hG hD hK0 ?_ ?_
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X]
      omega
    · intro b hb
      rw [mul_comm, support_mul_X] at hb
      obtain ⟨c, hc, rfl⟩ := Finset.mem_map.mp hb
      have hc' := nf_locIdeal_holes G _ a c hc
      rw [addRightEmbedding_apply, monoHoles_add_single]
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · refine Finset.mem_union_left _ ?_
        rw [monoHoles_add_single]
        exact Finset.mem_insert_self _ _
      · rcases Finset.mem_union.mp (hc' hj) with h | h
        · exact Finset.mem_union_left _ (haK0 h)
        · exact Finset.mem_union_right _ h
  rw [e1, e2, e3]
  have hmem : X v * monomial a 1
      - X v * nf (locIdeal G (supp G s (monoHoles G (a + Finsupp.single v 1)))) (monomial a 1)
      ∈ locIdeal G (supp G s (monoHoles G (a + Finsupp.single v 1))) := by
    rw [← mul_sub]
    exact X_mul_mem_locIdeal G v (nf_sub_mem _ _)
  have h0 := (nf_eq_zero_iff _ _).mpr hmem
  rw [map_sub, sub_eq_zero] at h0
  exact h0

/-- A member of the local ideal of `supp K` whose monomials have their holes in `K` is killed. -/
theorem pseudoR_eq_zero_of_mem {s : ℕ} (hG : IsBdryExpander G s 2)
    {K : Finset (Fin N)} (hK : K.card ≤ s) {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f.totalDegree ≤ s) (hfK : ∀ a ∈ f.support, monoHoles G a ⊆ K)
    (hmem : f ∈ locIdeal G (supp G s K)) : pseudoR G s f = 0 := by
  rw [pseudoR_eq_nf G hG le_rfl hK hf (fun a ha => (hfK a ha).trans Finset.subset_union_left)]
  exact (nf_eq_zero_iff _ _).mpr hmem

theorem pseudoR_axiom {s D : ℕ} (hG : IsBdryExpander G s 2) (hs : 1 ≤ s) (hD : D ≤ s)
    {f : MvPolynomial (GEdge G) (ZMod 2)} (hf : f ∈ cnfSystem (graphPHP G))
    (hdeg : f.totalDegree ≤ D) : pseudoR G s f = 0 := by
  rcases cnfSystem_graphPHP_cases G hf with ⟨v, rfl⟩ | ⟨i, rfl⟩ | ⟨e, e', h1, h2, rfl⟩
  · refine pseudoR_eq_zero_of_mem G hG (K := {v.1.2}) (by simpa using hs) (hdeg.trans hD)
      (monoHoles_subset_of_vars G ?_) (bool_mem_locIdeal G _ v)
    intro u hu
    rcases Finset.mem_union.mp (vars_add_subset _ _ hu) with h | h
    · rcases Finset.mem_union.mp (vars_mul _ _ h) with h | h <;>
      · rw [vars_X, Finset.mem_singleton] at h
        rw [h]
        exact Finset.mem_singleton_self _
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h]
      exact Finset.mem_singleton_self _
  · refine pseudoR_eq_zero_of_mem G hG (K := G i) ?_ (hdeg.trans hD)
      (monoHoles_pigeonClause G i)
      (pigeon_mem_locIdeal G (mem_supp_self G hs i (subset_refl _)))
    rw [← totalDegree_pigeonClause G i]
    exact hdeg.trans hD
  · refine pseudoR_eq_zero_of_mem G hG (K := {e.1.2}) (by simpa using hs) (hdeg.trans hD)
      (monoHoles_subset_of_vars G ?_) (hole_mem_locIdeal G _ h1 h2)
    intro u hu
    rcases Finset.mem_union.mp (vars_mul _ _ hu) with h | h
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h]
      exact Finset.mem_singleton_self _
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h, ← h1]
      exact Finset.mem_singleton_self _

theorem pseudoR_one {s : ℕ} (hG : IsBdryExpander G s 2) : pseudoR G s 1 ≠ 0 := by
  have hm : monoHoles G (0 : GEdge G →₀ ℕ) = ∅ := by
    unfold monoHoles
    rw [Finsupp.support_zero, Finset.image_empty]
  have h0 : supp G s (monoHoles G (0 : GEdge G →₀ ℕ)) = ∅ := by
    rw [hm]
    have h := two_mul_card_supp_le G hG (H := ∅) (Nat.zero_le s)
    rw [Finset.card_empty] at h
    exact Finset.card_eq_zero.mp (by omega)
  have h1 : pseudoR G s 1 = nf (locIdeal G ∅) 1 := by
    have h := pseudoR_monomial G s 0
    rw [h0] at h
    exact h
  rw [h1]
  exact fun h => one_not_mem_locIdeal_empty G ((nf_eq_zero_iff _ _).mp h)

theorem graphPHP_no_pc_refutation {s D : ℕ} (hG : IsBdryExpander G s 2) (hs : 1 ≤ s)
    (hD : D ≤ s) : ¬ PCRefutable (cnfSystem (graphPHP G)) D :=
  not_pcRefutable_of_pseudoReduction (pseudoR G s)
    (fun _ hf hdeg => pseudoR_axiom G hG hs hD hf hdeg)
    (fun v a ha => pseudoR_mul G hG hD v a ha)
    (pseudoR_one G hG)

end PEqualNP.ProofComplexity.Helpers

-- Accepted project source: PEqualNP.ProofComplexity.Helpers.FunLocalSat
/-!
# Helpers: functional local satisfiability on a pigeonhole graph (helper module, proofs only)

Helper F4 of the route to the functional graph pigeonhole bound
(`notes/pcx-fun-graph-php-route.md`), the functional twin of `LocalSat`. For a bipartite graph
`G` and a set `S` of pigeons:

* `funLocalSat G S α`: the point `α` satisfies `localSat G S` and no pigeon (of `S` or not) has
  two edges at different holes both with value `1`;
* `funLocIdeal G S`: the polynomials vanishing at every such point. It contains `locIdeal G S`,
  the functional products, is closed under multiplication by a variable, grows with `S`, and
  does not contain `1` when `S = ∅`;
* `monoPigeons G a`: the pigeons of the edges of a monomial; `monoNbrs G a`: the holes adjacent
  to one of them (the footprint of the functional route);
* `cnfSystem_funGraphPHP_cases`: the four shapes of a member of `cnfSystem (funGraphPHP G)`.
-/

namespace PEqualNP.ProofComplexity.Helpers

open MvPolynomial
open PEqualNP.Expanders

variable {m N : ℕ} (G : BipGraph m N)

/-- The point `α` satisfies `localSat G S` and is functional: two edges at one pigeon with
different holes are never both `1`. -/
def funLocalSat (S : Finset (Fin m)) (α : GEdge G → ZMod 2) : Prop :=
  localSat G S α ∧
  ∀ e e' : GEdge G, e.1.1 = e'.1.1 → e.1.2 ≠ e'.1.2 → α e * α e' = 0

/-- The polynomials vanishing at every point that satisfies `funLocalSat G S`. -/
noncomputable def funLocIdeal (S : Finset (Fin m)) :
    Submodule (ZMod 2) (MvPolynomial (GEdge G) (ZMod 2)) :=
  ⨅ (α : GEdge G → ZMod 2) (_ : funLocalSat G S α),
    LinearMap.ker (MvPolynomial.aeval (R := ZMod 2) α).toLinearMap

theorem mem_funLocIdeal {S : Finset (Fin m)} {f : MvPolynomial (GEdge G) (ZMod 2)} :
    f ∈ funLocIdeal G S ↔ ∀ α, funLocalSat G S α → eval α f = 0 := by
  simp only [funLocIdeal, Submodule.mem_iInf, LinearMap.mem_ker, AlgHom.toLinearMap_apply]
  rfl

theorem locIdeal_le_funLocIdeal (S : Finset (Fin m)) : locIdeal G S ≤ funLocIdeal G S := by
  intro f hf
  rw [mem_locIdeal] at hf
  rw [mem_funLocIdeal]
  exact fun α hα => hf α hα.1

theorem funLocIdeal_mono {S S' : Finset (Fin m)} (h : S ⊆ S') :
    funLocIdeal G S ≤ funLocIdeal G S' := by
  intro f hf
  rw [mem_funLocIdeal] at hf ⊢
  exact fun α hα => hf α ⟨⟨hα.1.1, fun i hi => hα.1.2 i (h hi)⟩, hα.2⟩

theorem X_mul_mem_funLocIdeal {S : Finset (Fin m)} (v : GEdge G)
    {f : MvPolynomial (GEdge G) (ZMod 2)} (hf : f ∈ funLocIdeal G S) :
    X v * f ∈ funLocIdeal G S := by
  rw [mem_funLocIdeal] at hf ⊢
  intro α hα
  rw [map_mul, hf α hα, mul_zero]

theorem fun_mem_funLocIdeal (S : Finset (Fin m)) {e e' : GEdge G}
    (h1 : e.1.1 = e'.1.1) (h2 : e.1.2 ≠ e'.1.2) : X e * X e' ∈ funLocIdeal G S := by
  rw [mem_funLocIdeal]
  intro α hα
  simpa using hα.2 e e' h1 h2

theorem one_not_mem_funLocIdeal_empty :
    (1 : MvPolynomial (GEdge G) (ZMod 2)) ∉ funLocIdeal G ∅ := by
  rw [mem_funLocIdeal]
  intro h
  have h0 := h (fun _ => 0)
    ⟨⟨fun _ _ _ _ => mul_zero _, fun i hi => absurd hi (by simp)⟩, fun _ _ _ _ => mul_zero _⟩
  rw [map_one] at h0
  exact one_ne_zero h0

/-- The pigeons of the edges of a monomial. -/
def monoPigeons (a : GEdge G →₀ ℕ) : Finset (Fin m) := a.support.image (fun e => e.1.1)

/-- The holes adjacent to a pigeon of a monomial. -/
def monoNbrs (a : GEdge G →₀ ℕ) : Finset (Fin N) := (monoPigeons G a).biUnion G

theorem card_monoNbrs_le {d : ℕ} (hd : LeftDegLe G d) (a : GEdge G →₀ ℕ) :
    (monoNbrs G a).card ≤ d * a.degree := by
  have h1 : (monoNbrs G a).card ≤ (monoPigeons G a).card * d :=
    Finset.card_biUnion_le_card_mul _ _ _ fun i _ => hd i
  have h2 : (monoPigeons G a).card ≤ a.degree := by
    refine Finset.card_image_le.trans ?_
    rw [Finsupp.degree_apply, Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun v hv => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)
  calc (monoNbrs G a).card ≤ (monoPigeons G a).card * d := h1
    _ ≤ a.degree * d := Nat.mul_le_mul_right d h2
    _ = d * a.degree := Nat.mul_comm _ _

theorem monoNbrs_add_single (a : GEdge G →₀ ℕ) (v : GEdge G) :
    monoNbrs G (a + Finsupp.single v 1) = monoNbrs G a ∪ G v.1.1 := by
  ext j
  simp only [monoNbrs, monoPigeons, Finset.mem_biUnion, Finset.mem_image, Finset.mem_union,
    Finsupp.mem_support_iff, Finsupp.add_apply]
  constructor
  · rintro ⟨i, ⟨e, he, rfl⟩, hj⟩
    by_cases hev : e = v
    · exact Or.inr (hev ▸ hj)
    · refine Or.inl ⟨e.1.1, ⟨e, ?_, rfl⟩, hj⟩
      rwa [Finsupp.single_apply, ite_eq_right (Ne.symm hev), add_zero] at he
  · rintro (⟨i, ⟨e, he, rfl⟩, hj⟩ | hj)
    · exact ⟨e.1.1, ⟨e, fun h0 => he (Nat.eq_zero_of_add_eq_zero_right h0), rfl⟩, hj⟩
    · exact ⟨v.1.1, ⟨v, by rw [Finsupp.single_eq_same]; omega, rfl⟩, hj⟩

theorem monoNbrs_subset_of_monoPigeons {a b : GEdge G →₀ ℕ} {S : Finset (Fin m)}
    (h : monoPigeons G b ⊆ monoPigeons G a ∪ S) :
    monoNbrs G b ⊆ monoNbrs G a ∪ S.biUnion G := by
  intro j hj
  obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.mp hj
  rcases Finset.mem_union.mp (h hi) with h' | h'
  · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, h', hji⟩)
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, h', hji⟩)

theorem monoNbrs_pigeonClause (i : Fin m) :
    ∀ a ∈ (clausePoly (pigeonClause G i)).support, monoNbrs G a ⊆ G i := by
  classical
  intro a ha j hj
  obtain ⟨i', hi', hji⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi'
  have hv : e ∈ (clausePoly (pigeonClause G i)).vars :=
    (mem_vars_iff_mem_support e).mpr ⟨a, ha, he⟩
  rw [localSat_clausePoly_pigeonClause] at hv
  obtain ⟨l, hl, hel⟩ := Finset.mem_biUnion.mp (vars_prod _ hv)
  have hel' := vars_add_subset _ _ hel
  rw [vars_one, vars_X, Finset.empty_union, Finset.mem_singleton] at hel'
  have h := (Finset.mem_filter.mp hl).2.1
  subst hel'
  rwa [h] at hji

theorem cnfSystem_funGraphPHP_cases {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f ∈ cnfSystem (funGraphPHP G)) :
    (∃ v, f = X v * X v + X v) ∨ (∃ i, f = clausePoly (pigeonClause G i)) ∨
    (∃ e e' : GEdge G, e.1.2 = e'.1.2 ∧ e.1.1 ≠ e'.1.1 ∧ f = X e * X e') ∨
    ∃ e e' : GEdge G, e.1.1 = e'.1.1 ∧ e.1.2 ≠ e'.1.2 ∧ f = X e * X e' := by
  rcases hf with ⟨v, rfl⟩ | ⟨C, hC, rfl⟩
  · exact Or.inl ⟨v, rfl⟩
  · rcases hC with hC | ⟨e, e', h1, h2, rfl⟩
    · rcases cnfSystem_graphPHP_cases G (Or.inr ⟨C, hC, rfl⟩) with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · refine Or.inr (Or.inr (Or.inr ⟨e, e', h1, h2, ?_⟩))
      have hne : ((e, false) : Literal (GEdge G)) ≠ (e', false) := by
        intro h
        exact h2 (by rw [(Prod.mk.inj h).1])
      rw [clausePoly, Finset.prod_pair hne]
      simp

end PEqualNP.ProofComplexity.Helpers

-- Accepted project source: PEqualNP.ProofComplexity.Helpers.FunLocalNF
/-!
# Helpers: the local normal form facts of functional pigeonhole (helper module, proofs only)

Helper F5 of the route to the functional graph pigeonhole bound
(`notes/pcx-fun-graph-php-route.md`, section 2.2), the functional twin of `LocalNF`. With
`nf (funLocIdeal G S)` the echelon normal form modulo the polynomials vanishing on the
functional points that respect every hole and seat every pigeon of `S`:

* `nf_funLocIdeal_pigeons` (pigeon locality): the monomials of the normal form of a monomial `a`
  have their pigeons among the pigeons of `a` and `S`;
* `nf_funLocIdeal_insert` (peel one pigeon): adding a pigeon `p` with a neighbour `j` that is
  neither a neighbour of `S` nor a neighbour of a pigeon of `a` does not change the normal form
  of `a`;
* `nf_funLocIdeal_ext` (extension): if `S` is closed for `K`, the normal form of a monomial
  whose pigeons have their neighbours in `K` is the same for every `T` between `S` and size `s`.

The two substitutions are `bind₁` maps: `funNF_zeroOut` sets to zero every variable whose pigeon
is outside a set of pigeons, and `funNF_override` seats `p` in `j` (the edge from `p` to `j` is
set to one, the other edges at `p` and the other edges at `j` to zero).
-/

namespace PEqualNP.ProofComplexity.Helpers

open MvPolynomial
open PEqualNP.Expanders

variable {m N : ℕ} (G : BipGraph m N)

/-! ### Zeroing the variables whose pigeon is outside `Q` -/

/-- The substitution that sets to zero every variable whose pigeon is outside `Q`. -/
noncomputable def funNF_zeroOut (Q : Finset (Fin m)) (e : GEdge G) :
    MvPolynomial (GEdge G) (ZMod 2) :=
  if e.1.1 ∈ Q then X e else 0

theorem funNF_zeroOut_monomial (Q : Finset (Fin m)) (b : GEdge G →₀ ℕ) (c : ZMod 2) :
    bind₁ (funNF_zeroOut G Q) (monomial b c)
      = if monoPigeons G b ⊆ Q then monomial b c else 0 := by
  rw [bind₁_monomial]
  split_ifs with h
  · have hprod : ∏ e ∈ b.support, funNF_zeroOut G Q e ^ b e
        = ∏ e ∈ b.support, (X e : MvPolynomial (GEdge G) (ZMod 2)) ^ b e := by
      refine Finset.prod_congr rfl fun e he => ?_
      rw [funNF_zeroOut, ite_eq_left (h (Finset.mem_image_of_mem _ he))]
    rw [hprod, monomial_eq]
    rfl
  · obtain ⟨x, hx, hxQ⟩ := Finset.not_subset.mp h
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.prod_eq_zero he, mul_zero]
    rw [funNF_zeroOut, ite_eq_right hxQ, zero_pow (Finsupp.mem_support_iff.mp he)]

theorem funNF_zeroOut_mem {S Q : Finset (Fin m)} (hQ : S ⊆ Q)
    {f : MvPolynomial (GEdge G) (ZMod 2)} (hf : f ∈ funLocIdeal G S) :
    bind₁ (funNF_zeroOut G Q) f ∈ funLocIdeal G S := by
  rw [mem_funLocIdeal] at hf ⊢
  intro α hα
  rw [localNF_eval_bind₁]
  have key : ∀ e e' : GEdge G, α e * α e' = 0 →
      eval α (funNF_zeroOut G Q e) * eval α (funNF_zeroOut G Q e') = 0 := by
    intro e e' h0
    by_cases h : e.1.1 ∈ Q
    · by_cases h' : e'.1.1 ∈ Q
      · rw [funNF_zeroOut, funNF_zeroOut, ite_eq_left h, ite_eq_left h', eval_X, eval_X]
        exact h0
      · rw [funNF_zeroOut, funNF_zeroOut, ite_eq_right h', map_zero, mul_zero]
    · rw [funNF_zeroOut, ite_eq_right h, map_zero, zero_mul]
  refine hf _ ⟨⟨?_, ?_⟩, ?_⟩
  · intro e e' h1 h2
    exact key e e' (hα.1.1 e e' h1 h2)
  · intro i hi
    obtain ⟨e, he, h1⟩ := hα.1.2 i hi
    have hmem : e.1.1 ∈ Q := by
      rw [he]
      exact hQ hi
    refine ⟨e, he, ?_⟩
    show eval α (funNF_zeroOut G Q e) = 1
    rw [funNF_zeroOut, ite_eq_left hmem, eval_X, h1]
  · intro e e' h1 h2
    exact key e e' (hα.2 e e' h1 h2)

theorem funNF_zeroOut_eq (Q : Finset (Fin m)) (r : MvPolynomial (GEdge G) (ZMod 2)) :
    bind₁ (funNF_zeroOut G Q) r
      = ∑ b ∈ r.support.filter (fun b => monoPigeons G b ⊆ Q), monomial b (r.coeff b) := by
  rw [localNF_map_eq_sum, Finset.sum_filter]
  exact Finset.sum_congr rfl fun b _ => funNF_zeroOut_monomial G Q b _

theorem funNF_support_sum_filter (Q : Finset (Fin m)) (r : MvPolynomial (GEdge G) (ZMod 2)) :
    (∑ b ∈ r.support.filter (fun b => monoPigeons G b ⊆ Q),
        monomial b (r.coeff b)).support
      ⊆ r.support.filter (fun b => monoPigeons G b ⊆ Q) := by
  intro b hb
  obtain ⟨c, hc, hbc⟩ := Finset.mem_biUnion.mp (support_sum hb)
  have hbc' := Finset.mem_singleton.mp (support_monomial_subset hbc)
  rw [hbc']
  exact hc

/-- Pigeon locality: the monomials of the normal form of `a` modulo `funLocIdeal G S` have their
pigeons among the pigeons of `a` and `S`. -/
theorem nf_funLocIdeal_pigeons (S : Finset (Fin m)) (a : GEdge G →₀ ℕ) :
    ∀ b ∈ (nf (funLocIdeal G S) (monomial a 1)).support,
      monoPigeons G b ⊆ monoPigeons G a ∪ S := by
  have hsub := funNF_support_sum_filter G (monoPigeons G a ∪ S)
    (nf (funLocIdeal G S) (monomial a 1))
  have heq : nf (funLocIdeal G S) (monomial a 1)
      = ∑ b ∈ (nf (funLocIdeal G S) (monomial a 1)).support.filter
          (fun b => monoPigeons G b ⊆ monoPigeons G a ∪ S),
          monomial b ((nf (funLocIdeal G S) (monomial a 1)).coeff b) := by
    refine nf_unique (funLocIdeal G S) ?_ ?_
    · intro b hb
      exact nf_support_isStd (funLocIdeal G S) (monomial a 1) b
        (Finset.mem_filter.mp (hsub hb)).1
    · have h := funNF_zeroOut_mem G (S := S) (Q := monoPigeons G a ∪ S)
        Finset.subset_union_right (nf_sub_mem (funLocIdeal G S) (monomial a 1))
      rw [map_sub, funNF_zeroOut_monomial, ite_eq_left Finset.subset_union_left,
        funNF_zeroOut_eq] at h
      exact h
  intro b hb
  have hb' : b ∈ (∑ b ∈ (nf (funLocIdeal G S) (monomial a 1)).support.filter
      (fun b => monoPigeons G b ⊆ monoPigeons G a ∪ S),
      monomial b ((nf (funLocIdeal G S) (monomial a 1)).coeff b)).support := by
    rw [← heq]
    exact hb
  exact (Finset.mem_filter.mp (hsub hb')).2

/-! ### Seating one pigeon in one hole -/

/-- The substitution that seats `p` in `j`: the edge from `p` to `j` becomes one, the other
edges at `p` and the other edges at `j` become zero, every other variable is kept. -/
noncomputable def funNF_override (p : Fin m) (j : Fin N) (e : GEdge G) :
    MvPolynomial (GEdge G) (ZMod 2) :=
  if e.1.1 = p then (if e.1.2 = j then 1 else 0) else (if e.1.2 = j then 0 else X e)

theorem funNF_override_monomial_of_notMem {p : Fin m} {j : Fin N} {b : GEdge G →₀ ℕ}
    (hp : p ∉ monoPigeons G b) (hb : j ∉ monoHoles G b) (c : ZMod 2) :
    bind₁ (funNF_override G p j) (monomial b c) = monomial b c := by
  rw [bind₁_monomial]
  have hprod : ∏ e ∈ b.support, funNF_override G p j e ^ b e
      = ∏ e ∈ b.support, (X e : MvPolynomial (GEdge G) (ZMod 2)) ^ b e := by
    refine Finset.prod_congr rfl fun e he => ?_
    have hne1 : e.1.1 ≠ p := fun h => hp (h ▸ Finset.mem_image_of_mem _ he)
    have hne2 : e.1.2 ≠ j := fun h => hb (h ▸ Finset.mem_image_of_mem _ he)
    rw [funNF_override, ite_eq_right hne1, ite_eq_right hne2]
  rw [hprod, monomial_eq]
  rfl

theorem funNF_override_mem {S : Finset (Fin m)} {p : Fin m} {j : Fin N} (hp : p ∉ S)
    (hj : j ∈ G p) (hjS : j ∉ S.biUnion G) {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f ∈ funLocIdeal G (insert p S)) :
    bind₁ (funNF_override G p j) f ∈ funLocIdeal G S := by
  rw [mem_funLocIdeal] at hf ⊢
  intro α hα
  rw [localNF_eval_bind₁]
  have hval : ∀ e : GEdge G, eval α (funNF_override G p j e)
      = if e.1.1 = p then (if e.1.2 = j then 1 else 0) else (if e.1.2 = j then 0 else α e) := by
    intro e
    rw [funNF_override]
    split_ifs <;> simp
  refine hf _ ⟨⟨?_, ?_⟩, ?_⟩
  · intro e e' h1 h2
    show eval α (funNF_override G p j e) * eval α (funNF_override G p j e') = 0
    by_cases hj1 : e.1.2 = j
    · have hj2 : e'.1.2 = j := h1.symm.trans hj1
      by_cases hp1 : e.1.1 = p
      · have hp2 : ¬ e'.1.1 = p := fun h3 => h2 (hp1.trans h3.symm)
        rw [hval e', ite_eq_right hp2, ite_eq_left hj2, mul_zero]
      · rw [hval e, ite_eq_right hp1, ite_eq_left hj1, zero_mul]
    · have hj2 : ¬ e'.1.2 = j := fun h3 => hj1 (h1.trans h3)
      by_cases hp1 : e.1.1 = p
      · rw [hval e, ite_eq_left hp1, ite_eq_right hj1, zero_mul]
      · by_cases hp2 : e'.1.1 = p
        · rw [hval e', ite_eq_left hp2, ite_eq_right hj2, mul_zero]
        · rw [hval e, hval e', ite_eq_right hp1, ite_eq_right hj1, ite_eq_right hp2,
            ite_eq_right hj2]
          exact hα.1.1 e e' h1 h2
  · intro i hi
    rcases Finset.mem_insert.mp hi with h | h
    · refine ⟨⟨(p, j), hj⟩, h.symm, ?_⟩
      show eval α (funNF_override G p j ⟨(p, j), hj⟩) = 1
      rw [hval, ite_eq_left rfl, ite_eq_left rfl]
    · obtain ⟨e, he, h1⟩ := hα.1.2 i h
      have hne1 : ¬ e.1.1 = p := by
        intro h3
        rw [he] at h3
        exact hp (h3 ▸ h)
      have hne2 : ¬ e.1.2 = j := by
        intro h3
        refine hjS (Finset.mem_biUnion.mpr ⟨i, h, ?_⟩)
        rw [← he, ← h3]
        exact e.2
      refine ⟨e, he, ?_⟩
      show eval α (funNF_override G p j e) = 1
      rw [hval, ite_eq_right hne1, ite_eq_right hne2, h1]
  · intro e e' h1 h2
    show eval α (funNF_override G p j e) * eval α (funNF_override G p j e') = 0
    by_cases hp1 : e.1.1 = p
    · have hp2 : e'.1.1 = p := h1.symm.trans hp1
      by_cases hj1 : e.1.2 = j
      · have hj2 : ¬ e'.1.2 = j := fun h3 => h2 (hj1.trans h3.symm)
        rw [hval e', ite_eq_left hp2, ite_eq_right hj2, mul_zero]
      · rw [hval e, ite_eq_left hp1, ite_eq_right hj1, zero_mul]
    · have hp2 : ¬ e'.1.1 = p := fun h3 => hp1 (h1.trans h3)
      by_cases hj1 : e.1.2 = j
      · rw [hval e, ite_eq_right hp1, ite_eq_left hj1, zero_mul]
      · by_cases hj2 : e'.1.2 = j
        · rw [hval e', ite_eq_right hp2, ite_eq_left hj2, mul_zero]
        · rw [hval e, hval e', ite_eq_right hp1, ite_eq_right hj1, ite_eq_right hp2,
            ite_eq_right hj2]
          exact hα.2 e e' h1 h2

/-- The image of a monomial under the override is zero or the monomial with the edges at `j`
dropped. -/
theorem funNF_override_monomial_one (p : Fin m) (j : Fin N) (c : GEdge G →₀ ℕ) :
    bind₁ (funNF_override G p j) (monomial c 1) = 0 ∨
      bind₁ (funNF_override G p j) (monomial c 1) = monomial (localNF_drop G j c) 1 := by
  rw [bind₁_monomial, C_1, one_mul]
  by_cases hz : ∃ e ∈ c.support, (e.1.1 = p ∧ ¬ e.1.2 = j) ∨ (¬ e.1.1 = p ∧ e.1.2 = j)
  · obtain ⟨e, he, h⟩ := hz
    left
    refine Finset.prod_eq_zero he ?_
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [funNF_override, ite_eq_left h1, ite_eq_right h2,
        zero_pow (Finsupp.mem_support_iff.mp he)]
    · rw [funNF_override, ite_eq_right h1, ite_eq_left h2,
        zero_pow (Finsupp.mem_support_iff.mp he)]
  · right
    have hz1 : ∀ e ∈ c.support, e.1.1 = p → e.1.2 = j := fun e he h =>
      by_contra fun h2 => hz ⟨e, he, Or.inl ⟨h, h2⟩⟩
    have hz2 : ∀ e ∈ c.support, e.1.2 = j → e.1.1 = p := fun e he h =>
      by_contra fun h2 => hz ⟨e, he, Or.inr ⟨h2, h⟩⟩
    rw [monomial_eq, C_1, one_mul, Finsupp.prod, localNF_drop, Finsupp.support_filter,
      Finset.prod_filter]
    refine Finset.prod_congr rfl fun e he => ?_
    by_cases h : e.1.2 = j
    · rw [ite_eq_right (not_not.mpr h), funNF_override, ite_eq_left (hz2 e he h),
        ite_eq_left h, one_pow]
    · have hne : ¬ e.1.1 = p := fun h3 => h (hz1 e he h3)
      rw [ite_eq_left h, Finsupp.filter_apply_pos (p := fun e : GEdge G => e.1.2 ≠ j) (f := c) h,
        funNF_override, ite_eq_right hne, ite_eq_right h]

/-- The override maps the span of the monomials below `b` into itself. -/
theorem funNF_override_mem_restrictSupport (p : Fin m) (j : Fin N) {b : GEdge G →₀ ℕ}
    {w : MvPolynomial (GEdge G) (ZMod 2)}
    (hw : w ∈ restrictSupport (ZMod 2) {d : GEdge G →₀ ℕ | MonoLt d b}) :
    bind₁ (funNF_override G p j) w
      ∈ restrictSupport (ZMod 2) {d : GEdge G →₀ ℕ | MonoLt d b} := by
  rw [localNF_map_eq_sum]
  refine Submodule.sum_mem _ fun c hc => ?_
  have hcb : MonoLt c b :=
    (show (↑w.support : Set (GEdge G →₀ ℕ)) ⊆ {d | MonoLt d b} from hw) (Finset.mem_coe.mpr hc)
  have hsm : monomial c (w.coeff c)
      = w.coeff c • (monomial c 1 : MvPolynomial (GEdge G) (ZMod 2)) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hsm, map_smul]
  refine Submodule.smul_mem _ _ ?_
  rcases funNF_override_monomial_one G p j c with h | h
  · rw [h]
    exact Submodule.zero_mem _
  · rw [h]
    refine (show (↑(monomial (localNF_drop G j c) (1 : ZMod 2)).support : Set (GEdge G →₀ ℕ))
      ⊆ {d | MonoLt d b} from ?_)
    intro d hd
    have hd' : d = localNF_drop G j c :=
      Finset.mem_singleton.mp (support_monomial_subset (Finset.mem_coe.mp hd))
    rw [hd']
    show MonoLt (localNF_drop G j c) b
    rcases localNF_drop_eq_or_degree_lt G j c with h' | h'
    · rw [h']
      exact hcb
    · exact monoLt_of_degree_lt (lt_of_lt_of_le h' (degree_le_of_monoLt hcb))

/-- Peel one pigeon: adding a pigeon `p` with a neighbour `j` that is neither a neighbour of `S`
nor a neighbour of a pigeon of `a` does not change the normal form of `a`. -/
theorem nf_funLocIdeal_insert {S : Finset (Fin m)} {p : Fin m} {j : Fin N}
    (hp : p ∉ S) (hj : j ∈ G p) (hjS : j ∉ S.biUnion G) {a : GEdge G →₀ ℕ}
    (ha : j ∉ monoNbrs G a) :
    nf (funLocIdeal G (insert p S)) (monomial a 1) = nf (funLocIdeal G S) (monomial a 1) := by
  refine nf_unique (funLocIdeal G (insert p S)) ?_ ?_
  · intro b hb hmem
    have hstd := nf_support_isStd (funLocIdeal G S) (monomial a 1) b hb
    refine hstd ?_
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hmem
    have hloc := nf_funLocIdeal_pigeons G S a b hb
    have hbp : p ∉ monoPigeons G b := by
      intro h
      rcases Finset.mem_union.mp (hloc h) with h' | h'
      · exact ha (Finset.mem_biUnion.mpr ⟨p, h', hj⟩)
      · exact hp h'
    have hbj : j ∉ monoHoles G b := by
      intro h
      obtain ⟨e, he, hej⟩ := Finset.mem_image.mp h
      have hje : j ∈ G e.1.1 := by
        rw [← hej]
        exact e.2
      rcases Finset.mem_union.mp (hloc (Finset.mem_image_of_mem _ he)) with h' | h'
      · exact ha (Finset.mem_biUnion.mpr ⟨e.1.1, h', hje⟩)
      · exact hjS (Finset.mem_biUnion.mpr ⟨e.1.1, h', hje⟩)
    have himg := congrArg (bind₁ (funNF_override G p j)) huw
    rw [map_add, funNF_override_monomial_of_notMem G hbp hbj] at himg
    rw [← himg]
    exact Submodule.add_mem_sup (funNF_override_mem G hp hj hjS hu)
      (funNF_override_mem_restrictSupport G p j hw)
  · exact funLocIdeal_mono G (Finset.subset_insert p S)
      (nf_sub_mem (funLocIdeal G S) (monomial a 1))

/-- Extension: if `S` is closed for `K`, the normal form of a monomial whose pigeons have their
neighbours in `K` is the same modulo `funLocIdeal G T` for every `T` with `S ⊆ T` and
`T.card ≤ s`. -/
theorem nf_funLocIdeal_ext {s : ℕ} {K : Finset (Fin N)} {S T : Finset (Fin m)}
    (hcl : SuppClosed G s K S) (hST : S ⊆ T) (hT : T.card ≤ s)
    {a : GEdge G →₀ ℕ} (ha : monoNbrs G a ⊆ K) :
    nf (funLocIdeal G T) (monomial a 1) = nf (funLocIdeal G S) (monomial a 1) := by
  have key : ∀ n : ℕ, ∀ T : Finset (Fin m), S ⊆ T → T.card ≤ s → T.card = n →
      nf (funLocIdeal G T) (monomial a 1) = nf (funLocIdeal G S) (monomial a 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro T hST hT hn
      by_cases hTS : T = S
      · rw [hTS]
      · have hlt : S ⊂ T := hST.ssubset_of_ne (Ne.symm hTS)
        obtain ⟨p, hpT, hpS, j, hj, hjK, hjT⟩ := SuppClosed.peel (G := G) hcl hlt hT
        have h1 := nf_funLocIdeal_insert G (S := T.erase p) (p := p) (j := j) (by simp) hj hjT
          (a := a) (fun h => hjK (ha h))
        rw [Finset.insert_erase hpT] at h1
        rw [h1]
        refine ih (T.erase p).card ?_ (T.erase p) ?_ ?_ rfl
        · rw [← hn]
          exact Finset.card_erase_lt_of_mem hpT
        · exact Finset.subset_erase.mpr ⟨hST, hpS⟩
        · exact (Finset.card_erase_le).trans hT
  exact key T.card T hST hT rfl

end PEqualNP.ProofComplexity.Helpers

-- Accepted project source: PEqualNP.ProofComplexity.Helpers.FunGraphPHPReduction
/-!
# Helpers: the pseudo reduction operator of functional graph pigeonhole (helper module, proofs only)

Helper F6 of the route to L-pcx-049 (`notes/pcx-fun-graph-php-route.md`), the assembly, and the
functional twin of `GraphPHPReduction`. For a bipartite graph `G` and a size bound `s`:

* `funPseudoR G s`: the linear operator sending a monomial `a` to its echelon normal form modulo
  the functional local ideal of the support of the footprint `monoNbrs G a` (the holes adjacent
  to a pigeon of `a`);
* `funPseudoR_monomial_eq_nf`, `funPseudoR_eq_nf`: on a polynomial whose monomials have a small
  footprint inside `K ∪ N(supp K)`, the operator is the normal form modulo the functional local
  ideal of `supp K`;
* `funPseudoR_mul`, `funPseudoR_axiom`, `funPseudoR_one`: the three properties of Razborov's
  criterion;
* `funGraphPHP_no_pc_refutation`: on an `(s, 2)` boundary expander of left degree at most `d`
  with `1 ≤ s` and `d * D ≤ s`, the functional pigeonhole formula has no polynomial calculus
  refutation of degree `D` over `ZMod 2`.
-/

namespace PEqualNP.ProofComplexity.Helpers

open MvPolynomial
open PEqualNP.Expanders

variable {m N : ℕ} (G : BipGraph m N)

/-- The functional pseudo reduction operator: a monomial goes to its normal form modulo the
functional local ideal of the support of its footprint. -/
noncomputable def funPseudoR (s : ℕ) :
    MvPolynomial (GEdge G) (ZMod 2) →ₗ[ZMod 2] MvPolynomial (GEdge G) (ZMod 2) :=
  (basisMonomials (GEdge G) (ZMod 2)).constr (ZMod 2)
    (fun a => nf (funLocIdeal G (supp G s (monoNbrs G a))) (monomial a 1))

theorem funPseudoR_monomial (s : ℕ) (a : GEdge G →₀ ℕ) :
    funPseudoR G s (monomial a 1)
      = nf (funLocIdeal G (supp G s (monoNbrs G a))) (monomial a 1) := by
  have h := Module.Basis.constr_basis (basisMonomials (GEdge G) (ZMod 2)) (ZMod 2)
    (fun a => nf (funLocIdeal G (supp G s (monoNbrs G a))) (monomial a 1)) a
  simpa only [funPseudoR, coe_basisMonomials] using h

/-- If every variable of `f` has the holes of its pigeon in `K`, every monomial of `f` has its
footprint in `K`. -/
theorem monoNbrs_subset_of_vars {f : MvPolynomial (GEdge G) (ZMod 2)} {K : Finset (Fin N)}
    (h : ∀ e ∈ f.vars, G e.1.1 ⊆ K) : ∀ a ∈ f.support, monoNbrs G a ⊆ K := by
  classical
  intro a ha j hj
  obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi
  exact h e ((mem_vars_iff_mem_support e).mpr ⟨a, ha, he⟩) hji

/-- The common lemma of the route, on one monomial: `B` bounds both footprints. -/
theorem funPseudoR_monomial_eq_nf {s B : ℕ} (hG : IsBdryExpander G s 2) (hB : B ≤ s)
    {K : Finset (Fin N)} (hK : K.card ≤ B) {a : GEdge G →₀ ℕ}
    (ha : (monoNbrs G a).card ≤ B)
    (haK : monoNbrs G a ⊆ K ∪ (supp G s K).biUnion G) :
    funPseudoR G s (monomial a 1) = nf (funLocIdeal G (supp G s K)) (monomial a 1) := by
  rw [funPseudoR_monomial]
  have hH : (monoNbrs G a).card ≤ s := ha.trans hB
  have hKs : K.card ≤ s := hK.trans hB
  have h1 := two_mul_card_supp_le G hG hH
  have h2 := two_mul_card_supp_le G hG hKs
  have hT : (supp G s (monoNbrs G a) ∪ supp G s K).card ≤ s := by
    have := Finset.card_union_le (supp G s (monoNbrs G a)) (supp G s K)
    omega
  have e1 := nf_funLocIdeal_ext G (suppClosed_supp G hG hH) Finset.subset_union_left hT
    (subset_refl (monoNbrs G a))
  have e2 := nf_funLocIdeal_ext G (SuppClosed.mono G (suppClosed_supp G hG hKs) haK)
    Finset.subset_union_right hT (subset_refl (monoNbrs G a))
  exact e1.symm.trans e2

/-- An operator and a normal form that agree on the monomials of `f` agree on `f`. -/
theorem funPseudoR_eq_nf_of_monomials {s : ℕ}
    (U : Submodule (ZMod 2) (MvPolynomial (GEdge G) (ZMod 2)))
    {f : MvPolynomial (GEdge G) (ZMod 2)}
    (h : ∀ a ∈ f.support, funPseudoR G s (monomial a 1) = nf U (monomial a 1)) :
    funPseudoR G s f = nf U f := by
  have hf' : f = ∑ a ∈ f.support, f.coeff a • monomial a (1 : ZMod 2) := by
    conv_lhs => rw [f.as_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [smul_monomial, smul_eq_mul, mul_one]
  have e : ∀ L : MvPolynomial (GEdge G) (ZMod 2) →ₗ[ZMod 2] MvPolynomial (GEdge G) (ZMod 2),
      L f = ∑ a ∈ f.support, f.coeff a • L (monomial a 1) := by
    intro L
    conv_lhs => rw [hf']
    simp only [map_sum, map_smul]
  rw [e (funPseudoR G s), e (nf U)]
  exact Finset.sum_congr rfl fun a ha => by rw [h a ha]

theorem funPseudoR_eq_nf {s d D : ℕ} (hG : IsBdryExpander G s 2) (hd : LeftDegLe G d)
    (hB : d * D ≤ s) {K : Finset (Fin N)} (hK : K.card ≤ d * D)
    {f : MvPolynomial (GEdge G) (ZMod 2)} (hf : f.totalDegree ≤ D)
    (hfK : ∀ a ∈ f.support, monoNbrs G a ⊆ K ∪ (supp G s K).biUnion G) :
    funPseudoR G s f = nf (funLocIdeal G (supp G s K)) f :=
  funPseudoR_eq_nf_of_monomials G _ fun a ha =>
    funPseudoR_monomial_eq_nf G hG hB hK
      ((card_monoNbrs_le G hd a).trans
        (Nat.mul_le_mul_left d ((le_totalDegree ha).trans hf))) (hfK a ha)

theorem funPseudoR_mul {s d D : ℕ} (hG : IsBdryExpander G s 2) (hd : LeftDegLe G d)
    (hB : d * D ≤ s) (v : GEdge G) (a : GEdge G →₀ ℕ) (ha : a.degree + 1 ≤ D) :
    funPseudoR G s (X v * monomial a 1)
      = funPseudoR G s (X v * funPseudoR G s (monomial a 1)) := by
  have hdeg : (a + Finsupp.single v 1).degree = a.degree + 1 := by
    rw [map_add, Finsupp.degree_single]
  have hK0 : (monoNbrs G (a + Finsupp.single v 1)).card ≤ d * D :=
    (card_monoNbrs_le G hd _).trans (Nat.mul_le_mul_left d (by omega))
  have hKa : (monoNbrs G a).card ≤ d * D :=
    (card_monoNbrs_le G hd _).trans (Nat.mul_le_mul_left d (by omega))
  have hmono : X v * monomial a (1 : ZMod 2) = monomial (a + Finsupp.single v 1) 1 := by
    rw [mul_comm, monomial_one_mul_X]
  have haK0 : monoNbrs G a ⊆ monoNbrs G (a + Finsupp.single v 1) := by
    rw [monoNbrs_add_single]
    exact Finset.subset_union_left
  have e1 : funPseudoR G s (monomial a 1)
      = nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1)))) (monomial a 1) :=
    funPseudoR_monomial_eq_nf G hG hB hK0 hKa (haK0.trans Finset.subset_union_left)
  have e2 : funPseudoR G s (X v * monomial a 1)
      = nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))))
          (X v * monomial a 1) := by
    rw [hmono]
    exact funPseudoR_monomial_eq_nf G hG hB hK0 hK0 Finset.subset_union_left
  have hq : (nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))))
      (monomial a 1)).totalDegree ≤ a.degree :=
    (totalDegree_nf_le _ _).trans (totalDegree_monomial_one a).le
  have e3 : funPseudoR G s
        (X v * nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))))
          (monomial a 1))
      = nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))))
          (X v * nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))))
            (monomial a 1)) := by
    refine funPseudoR_eq_nf G hG hd hB hK0 ?_ ?_
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X]
      omega
    · intro b hb
      rw [mul_comm, support_mul_X] at hb
      obtain ⟨c, hc, rfl⟩ := Finset.mem_map.mp hb
      have hc' := monoNbrs_subset_of_monoPigeons G (nf_funLocIdeal_pigeons G _ a c hc)
      rw [addRightEmbedding_apply, monoNbrs_add_single]
      intro j hj
      rcases Finset.mem_union.mp hj with hj | hj
      · rcases Finset.mem_union.mp (hc' hj) with h | h
        · exact Finset.mem_union_left _ (haK0 h)
        · exact Finset.mem_union_right _ h
      · refine Finset.mem_union_left _ ?_
        rw [monoNbrs_add_single]
        exact Finset.mem_union_right _ hj
  rw [e1, e2, e3]
  have hmem : X v * monomial a 1
      - X v * nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))))
          (monomial a 1)
      ∈ funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))) := by
    rw [← mul_sub]
    exact X_mul_mem_funLocIdeal G v (nf_sub_mem _ _)
  have h0 := (nf_eq_zero_iff _ _).mpr hmem
  rw [map_sub, sub_eq_zero] at h0
  exact h0

/-- A member of the functional local ideal of `supp K` whose monomials have their footprint in
`K` is killed. -/
theorem funPseudoR_eq_zero_of_mem {s : ℕ} (hG : IsBdryExpander G s 2)
    {K : Finset (Fin N)} (hK : K.card ≤ s) {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hfK : ∀ a ∈ f.support, monoNbrs G a ⊆ K)
    (hmem : f ∈ funLocIdeal G (supp G s K)) : funPseudoR G s f = 0 := by
  rw [funPseudoR_eq_nf_of_monomials G (funLocIdeal G (supp G s K)) fun a ha =>
    funPseudoR_monomial_eq_nf G hG le_rfl hK ((Finset.card_le_card (hfK a ha)).trans hK)
      ((hfK a ha).trans Finset.subset_union_left)]
  exact (nf_eq_zero_iff _ _).mpr hmem

/-- A product of two variables has degree two. -/
theorem totalDegree_X_mul_X (e e' : GEdge G) :
    (X e * X e' : MvPolynomial (GEdge G) (ZMod 2)).totalDegree = 2 := by
  have h : (X e * X e' : MvPolynomial (GEdge G) (ZMod 2))
      = monomial (Finsupp.single e 1 + Finsupp.single e' 1) 1 := by
    have hX : (X e : MvPolynomial (GEdge G) (ZMod 2)) = monomial (Finsupp.single e 1) 1 := rfl
    rw [hX, monomial_one_mul_X]
  rw [h, totalDegree_monomial_one, map_add, Finsupp.degree_single, Finsupp.degree_single]

theorem funPseudoR_axiom {s d D : ℕ} (hG : IsBdryExpander G s 2) (hd : LeftDegLe G d)
    (hs : 1 ≤ s) (hB : d * D ≤ s) {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f ∈ cnfSystem (funGraphPHP G)) (hdeg : f.totalDegree ≤ D) : funPseudoR G s f = 0 := by
  have hcard : ∀ i, 1 ≤ D → (G i).card ≤ d * D := fun i hD =>
    (hd i).trans (Nat.le_mul_of_pos_right d hD)
  rcases cnfSystem_funGraphPHP_cases G hf with
    ⟨v, rfl⟩ | ⟨i, rfl⟩ | ⟨e, e', h1, h2, rfl⟩ | ⟨e, e', h1, h2, rfl⟩
  · have h2 : (X v * X v + X v : MvPolynomial (GEdge G) (ZMod 2)).totalDegree = 2 := by
      rw [totalDegree_add_eq_left_of_totalDegree_lt, totalDegree_X_mul_X]
      rw [totalDegree_X_mul_X, totalDegree_X]
      omega
    refine funPseudoR_eq_zero_of_mem G hG (K := G v.1.1) ((hcard _ (by omega)).trans hB)
      (monoNbrs_subset_of_vars G ?_)
      (locIdeal_le_funLocIdeal G _ (bool_mem_locIdeal G _ v))
    intro u hu
    rcases Finset.mem_union.mp (vars_add_subset _ _ hu) with h | h
    · rcases Finset.mem_union.mp (vars_mul _ _ h) with h | h <;>
      · rw [vars_X, Finset.mem_singleton] at h
        rw [h]
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h]
  · have hi : (G i).card ≤ D := by
      rw [← totalDegree_pigeonClause G i]
      exact hdeg
    have hi' : (G i).card ≤ s := by
      rcases Nat.eq_zero_or_pos D with h0 | h0
      · omega
      · exact (hcard i h0).trans hB
    exact funPseudoR_eq_zero_of_mem G hG (K := G i) hi' (monoNbrs_pigeonClause G i)
      (locIdeal_le_funLocIdeal G _
        (pigeon_mem_locIdeal G (mem_supp_self G hs i (subset_refl _))))
  · rw [totalDegree_X_mul_X] at hdeg
    have hK : (G e.1.1 ∪ G e'.1.1).card ≤ s := by
      have h3 := Finset.card_union_le (G e.1.1) (G e'.1.1)
      have h4 := hd e.1.1
      have h5 := hd e'.1.1
      have h6 : d * 2 ≤ d * D := Nat.mul_le_mul_left d hdeg
      omega
    refine funPseudoR_eq_zero_of_mem G hG (K := G e.1.1 ∪ G e'.1.1) hK
      (monoNbrs_subset_of_vars G ?_)
      (locIdeal_le_funLocIdeal G _ (hole_mem_locIdeal G _ h1 h2))
    intro u hu
    rcases Finset.mem_union.mp (vars_mul _ _ hu) with h | h
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h]
      exact Finset.subset_union_left
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h]
      exact Finset.subset_union_right
  · rw [totalDegree_X_mul_X] at hdeg
    refine funPseudoR_eq_zero_of_mem G hG (K := G e.1.1) ((hcard _ (by omega)).trans hB)
      (monoNbrs_subset_of_vars G ?_) (fun_mem_funLocIdeal G _ h1 h2)
    intro u hu
    rcases Finset.mem_union.mp (vars_mul _ _ hu) with h | h
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h]
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h, ← h1]

theorem funPseudoR_one {s : ℕ} (hG : IsBdryExpander G s 2) : funPseudoR G s 1 ≠ 0 := by
  have hm : monoNbrs G (0 : GEdge G →₀ ℕ) = ∅ := by
    unfold monoNbrs monoPigeons
    rw [Finsupp.support_zero, Finset.image_empty, Finset.biUnion_empty]
  have h0 : supp G s (monoNbrs G (0 : GEdge G →₀ ℕ)) = ∅ := by
    rw [hm]
    have h := two_mul_card_supp_le G hG (H := ∅) (Nat.zero_le s)
    rw [Finset.card_empty] at h
    exact Finset.card_eq_zero.mp (by omega)
  have h1 : funPseudoR G s 1 = nf (funLocIdeal G ∅) 1 := by
    have h := funPseudoR_monomial G s 0
    rw [h0] at h
    exact h
  rw [h1]
  exact fun h => one_not_mem_funLocIdeal_empty G ((nf_eq_zero_iff _ _).mp h)

theorem funGraphPHP_no_pc_refutation {s d D : ℕ} (hG : IsBdryExpander G s 2)
    (hd : LeftDegLe G d) (hs : 1 ≤ s) (hB : d * D ≤ s) :
    ¬ PCRefutable (cnfSystem (funGraphPHP G)) D :=
  not_pcRefutable_of_pseudoReduction (funPseudoR G s)
    (fun _ hf hdeg => funPseudoR_axiom G hG hd hs hB hf hdeg)
    (fun v a ha => funPseudoR_mul G hG hd hB v a ha)
    (funPseudoR_one G hG)

end PEqualNP.ProofComplexity.Helpers

-- Accepted project source: PEqualNP.ProofComplexity.L049
namespace PEqualNP.ProofComplexity

/-- L-pcx-049: on a bipartite graph of left degree at most `d` where every set of at most `s`
pigeons has twice its size in unique neighbouring holes, the functional pigeonhole CNF has no
polynomial calculus refutation over F2 of degree `D` when `1 ≤ s` and `d * D ≤ s`. -/
theorem L049 : ∀ (m N : ℕ) (G : PEqualNP.Expanders.BipGraph m N) (s d D : ℕ), PEqualNP.Expanders.IsBdryExpander G s 2 → PEqualNP.Expanders.LeftDegLe G d → 1 ≤ s → d * D ≤ s → ¬ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem (PEqualNP.Expanders.funGraphPHP G)) D :=
  fun _ _ G _ _ _ hG hd hs hB => Helpers.funGraphPHP_no_pc_refutation G hG hd hs hB

end PEqualNP.ProofComplexity

namespace SmoothClauseSearch

open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V] [Fintype V]

def flip (v : V) (x : V → Bool) : V → Bool := Function.update x v (!x v)

omit [Fintype V] in
private theorem flipTwice (v : V) : Function.Involutive (flip v) := by
  intro x
  funext u
  by_cases eq : u = v
  · subst u
    simp [flip]
  · simp [flip, Function.update_of_ne eq]

def Smooth (μ : (V → Bool) → ℝ) (R : ℕ) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ 0 < ∑ x, μ x ∧ ∀ x v, μ x ≤ (R : ℝ) * μ (flip v x)

noncomputable def cylinder (x : V → Bool) (pins : Finset V) : Finset (V → Bool) := by
  classical
  exact Finset.univ.filter fun y => ∀ v ∈ pins, y v = x v

/-- Conditioning on one coordinate costs at most a factor of `R+1`. -/
private theorem pinMass (μ : (V → Bool) → ℝ) (R : ℕ) (smooth : Smooth μ R)
    (src : Finset (V → Bool)) (v : V) (bit : Bool)
    (stable : ∀ y, flip v y ∈ src ↔ y ∈ src) :
    (∑ y ∈ src, μ y) ≤ ((R : ℝ) + 1) * ∑ y ∈ src.filter (fun y => y v = bit), μ y := by
  classical
  let pass := src.filter fun y => y v = bit
  let fail := src.filter fun y => ¬ y v = bit
  have opposite (y : V → Bool) : flip v y v = bit ↔ y v ≠ bit := by
    simp only [flip, Function.update_self]
    cases y v <;> cases bit <;> decide
  have onto : fail.image (flip v) = pass := by
    ext y
    simp only [Finset.mem_image, fail, pass, Finset.mem_filter]
    constructor
    · rintro ⟨z, ⟨mem, wrong⟩, rfl⟩
      exact ⟨(stable z).mpr mem, (opposite z).mpr wrong⟩
    · intro mem
      refine ⟨flip v y, ⟨(stable y).mpr mem.1, ?_⟩, flipTwice v y⟩
      intro eq
      exact (opposite y).mp eq mem.2
  have failBound : (∑ y ∈ fail, μ y) ≤ (R : ℝ) * ∑ y ∈ pass, μ y := by
    calc
      _ ≤ ∑ y ∈ fail, (R : ℝ) * μ (flip v y) := Finset.sum_le_sum fun y _ => smooth.2.2 y v
      _ = ∑ y ∈ fail.image (flip v), (R : ℝ) * μ y := by
        rw [Finset.sum_image]
        exact fun _ _ _ _ eq => (flipTwice v).injective eq
      _ = _ := by rw [onto, Finset.mul_sum]
  have splitMass : (∑ y ∈ pass, μ y) + (∑ y ∈ fail, μ y) = ∑ y ∈ src, μ y :=
    Finset.sum_filter_add_sum_filter_not src (fun y => y v = bit) _
  change _ ≤ ((R : ℝ) + 1) * ∑ y ∈ pass, μ y
  rw [← splitMass, add_mul, one_mul]
  linarith

theorem conditionalCylinderMass (μ : (V → Bool) → ℝ) (R : ℕ) (smooth : Smooth μ R)
    (src : Finset (V → Bool)) (x : V → Bool) (pins : Finset V)
    (stable : ∀ v ∈ pins, ∀ y, flip v y ∈ src ↔ y ∈ src) :
    (∑ y ∈ src, μ y) ≤ ((R : ℝ) + 1)^pins.card * ∑ y ∈ src ∩ cylinder x pins, μ y := by
  classical
  induction pins using Finset.induction_on with
  | empty => simp [cylinder]
  | @insert v pins fresh prior =>
    have previous := prior (fun u hu => stable u (Finset.mem_insert_of_mem hu))
    have keepPinned (y : V → Bool) : flip v y ∈ cylinder x pins ↔ y ∈ cylinder x pins := by
      simp only [cylinder, Finset.mem_filter, Finset.mem_univ, true_and, flip]
      apply forall₂_congr
      intro u hu
      have different : u ≠ v := fun eq => fresh (eq ▸ hu)
      rw [Function.update_of_ne different]
    have keeps (y : V → Bool) : flip v y ∈ src ∩ cylinder x pins ↔ y ∈ src ∩ cylinder x pins := by
      simp only [Finset.mem_inter, stable v (Finset.mem_insert_self _ _) y, keepPinned]
    have addPin : (src ∩ cylinder x pins).filter (fun y => y v = x v) =
        src ∩ cylinder x (insert v pins) := by
      ext y
      simp [cylinder, and_left_comm, and_comm]
    have mass := pinMass μ R smooth (src ∩ cylinder x pins) v (x v) keeps
    rw [addPin] at mass
    rw [Finset.card_insert_of_notMem fresh, pow_succ, mul_assoc]
    exact previous.trans (mul_le_mul_of_nonneg_left mass (by positivity))

theorem cylinderMass (μ : (V → Bool) → ℝ) (R : ℕ) (smooth : Smooth μ R)
    (x : V → Bool) (pins : Finset V) :
    (∑ y, μ y) ≤ ((R : ℝ) + 1)^pins.card * ∑ y ∈ cylinder x pins, μ y := by
  simpa using conditionalCylinderMass μ R smooth Finset.univ x pins (by simp)

/-- One true literal in each clause suffices to preserve all of them. -/
theorem satisfyingCylinder (C : Finset (Clause V)) (x : V → Bool)
    (sat : ∀ cl ∈ C, ClauseSat x cl) :
    ∃ pins : Finset V, pins.card ≤ C.card ∧
      ∀ y ∈ cylinder x pins, ∀ cl ∈ C, ClauseSat y cl := by
  classical
  induction C using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp⟩
  | @insert cl C fresh prior =>
    obtain ⟨pins, count, holds⟩ := prior (fun a ha => sat a (Finset.mem_insert_of_mem ha))
    obtain ⟨l, inClause, trueL⟩ := sat cl (Finset.mem_insert_self _ _)
    refine ⟨insert l.1 pins, ?_, ?_⟩
    · exact (Finset.card_insert_le _ _).trans (by rw [Finset.card_insert_of_notMem fresh]; omega)
    · intro y mem a ha
      have agrees : ∀ u ∈ insert l.1 pins, y u = x u := (Finset.mem_filter.mp mem).2
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact ⟨l, inClause, (agrees l.1 (Finset.mem_insert_self _ _)).trans trueL⟩
      · exact holds y (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          fun u hu => agrees u (Finset.mem_insert_of_mem hu)⟩) a ha

/-- A satisfiable union of listed clauses gives an accuracy ceiling. -/
theorem accuracyLeUnion (μ : (V → Bool) → ℝ) (R h : ℕ) (smooth : Smooth μ R)
    (C : Finset (Clause V)) (x : V → Bool) (sat : ∀ cl ∈ C, ClauseSat x cl)
    (bad : Finset (V → Bool)) (allSatisfiedBad : ∀ y, (∀ cl ∈ C, ClauseSat y cl) → y ∈ bad)
    (accurate : (2 : ℝ)^h * (∑ y ∈ bad, μ y) ≤ ∑ y, μ y) :
    h ≤ Nat.clog 2 (R+1) * C.card := by
  classical
  obtain ⟨pins, count, satis⟩ := satisfyingCylinder C x sat
  have mass := cylinderMass μ R smooth x pins
  have sub : cylinder x pins ⊆ bad := fun y mem => allSatisfiedBad y (satis y mem)
  have more : (∑ y ∈ cylinder x pins, μ y) ≤ ∑ y ∈ bad, μ y :=
    Finset.sum_le_sum_of_subset_of_nonneg sub (fun y _ _ => smooth.1 y)
  have positive : 0 < ∑ y ∈ bad, μ y := by
    by_contra! nonpos
    exact (not_le_of_gt smooth.2.1) (mass.trans (mul_nonpos_of_nonneg_of_nonpos
      (by positivity) (more.trans nonpos)))
  have ceiling : (2 : ℝ)^h ≤ ((R : ℝ)+1)^pins.card := by
    apply le_of_mul_le_mul_right _ positive
    exact accurate.trans (mass.trans (mul_le_mul_of_nonneg_left more (by positivity)))
  have power : ((R : ℝ)+1) ≤ (2 : ℝ)^Nat.clog 2 (R+1) := by
    exact_mod_cast (Nat.le_pow_clog (by decide : 1 < 2) (R+1))
  have bound : (2 : ℝ)^h ≤ (2 : ℝ)^(Nat.clog 2 (R+1) * C.card) := calc
    _ ≤ ((R : ℝ)+1)^pins.card := ceiling
    _ ≤ ((2 : ℝ)^Nat.clog 2 (R+1))^pins.card := by gcongr
    _ ≤ _ := by
      rw [← pow_mul]
      gcongr
      norm_num
  exact (pow_le_pow_iff_right₀ (by norm_num : 1 < (2 : ℝ))).mp bound

noncomputable def hitsEveryRow (rows : List (Finset V)) : Finset (V → Bool) := by
  classical
  exact Finset.univ.filter fun y => ∀ row ∈ rows, ∃ v ∈ row, y v = true

/-- On disjoint rows, the mass of seeing no all-zero row decays geometrically
even when the source coordinates are correlated. -/
theorem allRowsHitMass (μ : (V → Bool) → ℝ) (R d : ℕ) (smooth : Smooth μ R)
    (rows : List (Finset V)) (disjoint : rows.Pairwise Disjoint)
    (width : ∀ row ∈ rows, row.card ≤ d) :
    let Z := ((R : ℝ) + 1)^d
    Z^rows.length * (∑ y ∈ hitsEveryRow rows, μ y) ≤ (Z-1)^rows.length * ∑ y, μ y := by
  classical
  let Z := ((R : ℝ) + 1)^d
  have oneBase : 1 ≤ (R : ℝ) + 1 := by
    have nonneg : 0 ≤ (R : ℝ) := by positivity
    linarith
  have large : 1 ≤ Z := one_le_pow₀ oneBase
  have base : 0 ≤ Z := le_trans (by norm_num) large
  have residual : 0 ≤ Z-1 := sub_nonneg.mpr large
  change Z^rows.length * (∑ y ∈ hitsEveryRow rows, μ y) ≤ (Z-1)^rows.length * ∑ y, μ y
  induction rows with
  | nil => simp [hitsEveryRow]
  | cons row rows prior =>
    obtain ⟨apart, tail⟩ := List.pairwise_cons.mp disjoint
    let src := hitsEveryRow rows
    let zero := cylinder (fun _ : V => false) row
    have memSrc (y : V → Bool) : y ∈ src ↔ ∀ r ∈ rows, ∃ v ∈ r, y v = true := by
      simp [src, hitsEveryRow]
    have stable (v : V) (inRow : v ∈ row) (y : V → Bool) : flip v y ∈ src ↔ y ∈ src := by
      simp only [memSrc]
      apply forall₂_congr
      intro r hr
      apply exists_congr
      intro u
      apply and_congr_right
      intro hu
      have ne : u ≠ v := fun eq => (Finset.disjoint_left.mp (apart r hr)) inRow (eq ▸ hu)
      simp [flip, Function.update_of_ne ne]
    have cond := conditionalCylinderMass μ R smooth src (fun _ => false) row stable
    change (∑ y ∈ src, μ y) ≤ ((R : ℝ)+1)^row.card * (∑ y ∈ src ∩ zero, μ y) at cond
    have scaled : (∑ y ∈ src, μ y) ≤ Z * (∑ y ∈ src ∩ zero, μ y) := by
      apply cond.trans (mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun y _ => smooth.1 y))
      exact pow_right_mono₀ oneBase (width row (by simp))
    have hasHit (y : V → Bool) : (∃ v ∈ row, y v = true) ↔ y ∉ zero := by
      simp [zero, cylinder, not_forall, not_imp]
    have keep : src.filter (fun y => y ∉ zero) = hitsEveryRow (row :: rows) := by
      ext y
      simp only [Finset.mem_filter, memSrc, hitsEveryRow, Finset.mem_univ, true_and,
        List.forall_mem_cons, and_comm]
      exact and_congr (by simpa only [and_comm] using (hasHit y).symm) Iff.rfl
    have drop : src.filter (fun y => ¬ y ∉ zero) = src ∩ zero := by
      ext y
      simp
    have split : (∑ y ∈ hitsEveryRow (row :: rows), μ y) + (∑ y ∈ src ∩ zero, μ y) = ∑ y ∈ src, μ y := by
      rw [← keep, ← drop]
      exact Finset.sum_filter_add_sum_filter_not _ _ _
    have step : Z * (∑ y ∈ hitsEveryRow (row :: rows), μ y) ≤ (Z-1) * (∑ y ∈ src, μ y) := by
      linarith only [scaled, congrArg (fun x : ℝ => Z*x) split, split]
    have previous := prior tail (fun r hr => width r (List.mem_cons_of_mem _ hr))
    change _ ≤ (Z-1)^rows.length * ∑ y, μ y at previous
    calc
      _ = Z^rows.length * (Z * (∑ y ∈ hitsEveryRow (row :: rows), μ y)) := by
        rw [List.length_cons, pow_succ, mul_assoc]
      _ ≤ Z^rows.length * ((Z-1) * ∑ y ∈ src, μ y) :=
        mul_le_mul_of_nonneg_left step (pow_nonneg base _)
      _ = (Z-1) * (Z^rows.length * ∑ y ∈ src, μ y) := by ring
      _ ≤ (Z-1) * ((Z-1)^rows.length * ∑ y, μ y) := mul_le_mul_of_nonneg_left previous residual
      _ = _ := by rw [List.length_cons, pow_succ]; ring

private theorem halfAfterBlock (n : ℕ) (pos : 0 < n) :
    (((n : ℝ)-1)/(n : ℝ))^n ≤ 1/2 := by
  obtain one | large := eq_or_lt_of_le (Nat.succ_le_of_lt pos)
  · subst n
    norm_num
  · have oneLt : 1 < (n : ℝ) := by exact_mod_cast large
    have denom : 0 < (n : ℝ)-1 := sub_pos.mpr oneLt
    have ratio : 1 ≤ (n : ℝ)/((n : ℝ)-1) := (le_div_iff₀ denom).mpr (by linarith)
    have bern := one_add_mul_sub_le_pow (by linarith : -1 ≤ (n : ℝ)/((n : ℝ)-1)) n
    have term : (n : ℝ) * ((n : ℝ)/((n : ℝ)-1)-1) = (n : ℝ)/((n : ℝ)-1) := by
      field_simp [ne_of_gt denom]
      ring
    rw [term] at bern
    have two : (2 : ℝ) ≤ ((n : ℝ)/((n : ℝ)-1))^n := by linarith
    rw [div_pow] at two ⊢
    have h := (le_div_iff₀ (pow_pos denom n)).mp two
    apply (div_le_iff₀ (pow_pos (by linarith : 0 < (n : ℝ)) n)).mpr
    linarith

theorem rowTestingAccuracy (μ : (V → Bool) → ℝ) (R d h : ℕ) (smooth : Smooth μ R)
    (rows : List (Finset V)) (disjoint : rows.Pairwise Disjoint)
    (width : ∀ row ∈ rows, row.card ≤ d) (enough : (R+1)^d*h ≤ rows.length) :
    (2 : ℝ)^h * (∑ y ∈ hitsEveryRow rows, μ y) ≤ ∑ y, μ y := by
  let n := (R+1)^d
  let Z : ℝ := n
  let q := (Z-1)/Z
  have nPos : 0 < n := by dsimp [n]; positivity
  have zPos : 0 < Z := by
    change 0 < (n : ℝ)
    exact_mod_cast nPos
  have zOne : 1 ≤ Z := by
    change 1 ≤ (n : ℝ)
    exact_mod_cast Nat.succ_le_of_lt nPos
  have qNonneg : 0 ≤ q := div_nonneg (by linarith) zPos.le
  have qOne : q ≤ 1 := (div_le_iff₀ zPos).mpr (by linarith)
  have zEq : ((R : ℝ)+1)^d = Z := by simp [Z, n, Nat.cast_pow]
  have raw := allRowsHitMass μ R d smooth rows disjoint width
  dsimp only at raw
  rw [zEq] at raw
  have mass : (∑ y ∈ hitsEveryRow rows, μ y) ≤ q^rows.length * ∑ y, μ y := by
    dsimp only [q]
    rw [div_pow, div_mul_eq_mul_div]
    exact (le_div_iff₀ (pow_pos zPos _)).mpr (by simpa only [mul_comm] using raw)
  have half : q^n ≤ (1/2 : ℝ) := halfAfterBlock n nPos
  have decay : q^rows.length ≤ (1/2 : ℝ)^h := calc
    _ ≤ q^(n*h) := pow_le_pow_of_le_one qNonneg qOne enough
    _ = (q^n)^h := pow_mul _ _ _
    _ ≤ _ := pow_le_pow_left₀ (pow_nonneg qNonneg _) half h
  calc
    _ ≤ (2 : ℝ)^h * (q^rows.length * ∑ y, μ y) :=
      mul_le_mul_of_nonneg_left mass (by positivity)
    _ ≤ (2 : ℝ)^h * ((1/2 : ℝ)^h * ∑ y, μ y) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right decay smooth.2.1.le) (by positivity)
    _ = _ := by rw [← mul_assoc, ← mul_pow]; norm_num

end SmoothClauseSearch

-- Supporting lemmas from PEqualNP/ProofComplexity/Helpers/PCToolkit.lean
-- and BoolVanish.lean, under a local namespace.
namespace ClauseSearchPC.Toolkit

open MvPolynomial PEqualNP.ProofComplexity

variable {σ : Type}

/-- Monotonicity of polynomial calculus in the axioms and in the degree bound. -/
theorem pcDerivable_mono {F F' : Set (MvPolynomial σ (ZMod 2))} {B B' : ℕ}
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F B p) (hB : B ≤ B') (hF : F ⊆ F') :
    PCDerivable F' B' p := by
  induction h with
  | ax hp hdeg => exact .ax (hF hp) (hdeg.trans hB)
  | zero => exact .zero
  | add _ _ ih1 ih2 => exact .add ih1 ih2
  | mulX j _ hdeg ih => exact .mulX j ih (hdeg.trans hB)

/-- Multiplication of a derived line by a monomial, inside a fixed degree bound. -/
theorem pcDerivable_monomial_mul {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    (a : σ →₀ ℕ) : ∀ {g : MvPolynomial σ (ZMod 2)}, PCDerivable F B g →
      (a.sum fun _ e => e) + g.totalDegree ≤ B → PCDerivable F B (monomial a 1 * g) := by
  induction a using Finsupp.induction_linear with
  | zero =>
    intro g hg _
    have : (monomial (0 : σ →₀ ℕ) (1 : ZMod 2)) = 1 := rfl
    rw [this, one_mul]
    exact hg
  | add a b iha ihb =>
    intro g hg hdeg
    have hsplit : monomial (a + b) (1 : ZMod 2) * g = monomial a 1 * (monomial b 1 * g) := by
      rw [← mul_assoc, monomial_mul_monomial, one_mul]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)] at hdeg
    have hb : (monomial b (1 : ZMod 2) * g).totalDegree
        ≤ (b.sum fun _ e => e) + g.totalDegree :=
      (totalDegree_mul _ _).trans (Nat.add_le_add_right (totalDegree_monomial_le b 1) _)
    rw [hsplit]
    exact iha (ihb hg (by omega)) (by omega)
  | single j n =>
    induction n with
    | zero =>
      intro g hg _
      have : (monomial (Finsupp.single j 0) (1 : ZMod 2)) = 1 := by simp
      rw [this, one_mul]
      exact hg
    | succ n ih =>
      intro g hg hdeg
      have hsplit : monomial (Finsupp.single j (n + 1)) (1 : ZMod 2) * g
          = X j * (monomial (Finsupp.single j n) 1 * g) := by
        rw [← mul_assoc, X, monomial_mul_monomial, one_mul, ← Finsupp.single_add,
          add_comm 1 n]
      have hd1 : ((Finsupp.single j (n + 1)).sum fun _ e => e) = n + 1 :=
        Finsupp.sum_single_index rfl
      have hd2 : ((Finsupp.single j n).sum fun _ e => e) = n :=
        Finsupp.sum_single_index rfl
      rw [hd1] at hdeg
      have hlow : (monomial (Finsupp.single j n) (1 : ZMod 2) * g).totalDegree
          ≤ n + g.totalDegree :=
        (totalDegree_mul _ _).trans (Nat.add_le_add_right
          ((totalDegree_monomial_le _ 1).trans_eq hd2) _)
      rw [hsplit]
      refine .mulX j (ih hg (by omega)) ?_
      refine (totalDegree_mul _ _).trans ?_
      have := totalDegree_X (R := ZMod 2) j
      omega

/-- Finite sums of derived lines are derived. -/
theorem pcDerivable_sum {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ} {ι : Type}
    (s : Finset ι) (f : ι → MvPolynomial σ (ZMod 2)) (h : ∀ i ∈ s, PCDerivable F B (f i)) :
    PCDerivable F B (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PCDerivable.zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact .add (h i (Finset.mem_insert_self i s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

/-- Multiplication of a derived line by an arbitrary polynomial: the degree bound grows to
at most the sum of the two degrees. -/
theorem pcDerivable_mul_left {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    {g : MvPolynomial σ (ZMod 2)} (hg : PCDerivable F B g) (q : MvPolynomial σ (ZMod 2)) :
    PCDerivable F (max B (q.totalDegree + g.totalDegree)) (q * g) := by
  have hg' : PCDerivable F (max B (q.totalDegree + g.totalDegree)) g :=
    pcDerivable_mono hg (le_max_left _ _) subset_rfl
  have hq : q * g = ∑ a ∈ q.support, monomial a (q.coeff a) * g := by
    conv_lhs => rw [q.as_sum]
    rw [Finset.sum_mul]
  rw [hq]
  refine pcDerivable_sum _ _ fun a ha => ?_
  have hc : q.coeff a = 1 := by
    have h0 : q.coeff a ≠ 0 := mem_support_iff.mp ha
    generalize q.coeff a = c at h0
    revert h0; revert c; decide
  rw [hc]
  refine pcDerivable_monomial_mul a hg' ?_
  have : (a.sum fun _ e => e) ≤ q.totalDegree := le_totalDegree ha
  exact (Nat.add_le_add_right this _).trans (le_max_right _ _)

/-- Soundness of polynomial calculus: a common zero of the axioms is a zero of every derived
line. -/
theorem pcDerivable_eval_eq_zero {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F B p) (a : σ → ZMod 2)
    (ha : ∀ f ∈ F, eval a f = 0) : eval a p = 0 := by
  induction h with
  | ax hp _ => exact ha _ hp
  | zero => simp
  | add _ _ ih1 ih2 => simp [ih1, ih2]
  | mulX j _ _ ih => simp [ih]

end ClauseSearchPC.Toolkit

namespace ClauseSearchPC.Toolkit.BoolVanish

open MvPolynomial PEqualNP.ProofComplexity ClauseSearchPC.Toolkit

variable {σ : Type}

/-- The Boolean axioms. -/
noncomputable def boolAxioms (σ : Type) : Set (MvPolynomial σ (ZMod 2)) :=
  Set.range fun v : σ => X v * X v + X v

/-- Clamp every exponent to at most `1`. -/
noncomputable def mlin (a : σ →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.mapRange (fun n => min n 1) (by simp) a

theorem mlin_apply (a : σ →₀ ℕ) (v : σ) : mlin a v = min (a v) 1 := by
  simp [mlin]

theorem boolDerivable_monomial (d : ℕ) :
    ∀ (n : ℕ) (a : σ →₀ ℕ), (a.sum fun _ e => e) = n → n ≤ d →
      PCDerivable (boolAxioms σ) d (monomial a 1 + monomial (mlin a) 1) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a hn hd
  by_cases hall : ∀ v, a v ≤ 1
  · have : mlin a = a := by
      ext v; rw [mlin_apply]; have := hall v; omega
    rw [this, ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
    exact .zero
  simp only [not_forall, not_le] at hall
  obtain ⟨v, hv⟩ := hall
  set b := a - Finsupp.single v 2 with hb
  have ha : a = b + Finsupp.single v 2 := by
    ext w
    simp only [hb, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    split_ifs with h
    · subst h; omega
    · omega
  set a' := b + Finsupp.single v 1 with ha'
  have hsum : ∀ c : σ →₀ ℕ, ∀ k, ((c + Finsupp.single v k).sum fun _ e => e)
      = (c.sum fun _ e => e) + k := by
    intro c k
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
  have hmlin : mlin a' = mlin a := by
    ext w
    simp only [mlin_apply, ha, ha', Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> omega
  have hna : (a.sum fun _ e => e) = (b.sum fun _ e => e) + 2 := by rw [ha, hsum]
  have hna' : (a'.sum fun _ e => e) = (b.sum fun _ e => e) + 1 := by rw [ha', hsum]
  have hstep : PCDerivable (boolAxioms σ) d (monomial a 1 + monomial a' 1) := by
    have hid : monomial a (1 : ZMod 2) + monomial a' 1
        = monomial b 1 * (X v * X v + X v) := by
      rw [mul_add, X, monomial_mul_monomial, monomial_mul_monomial, monomial_mul_monomial,
        ← Finsupp.single_add, ha, ha', one_mul, one_mul]
    rw [hid]
    have hax : PCDerivable (boolAxioms σ) d (X v * X v + X v) := by
      refine .ax ⟨v, rfl⟩ ?_
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_X]; omega
      · rw [totalDegree_X]; omega
    refine pcDerivable_monomial_mul b hax ?_
    have : (X v * X v + X v : MvPolynomial σ (ZMod 2)).totalDegree ≤ 2 := by
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_X]
      · rw [totalDegree_X]; omega
    omega
  have hrest := ih _ (by omega) a' rfl (by omega)
  rw [hmlin] at hrest
  have := PCDerivable.add hstep hrest
  have e : monomial a (1 : ZMod 2) + monomial a' 1 + (monomial a' 1 + monomial (mlin a) 1)
      = monomial a 1 + monomial (mlin a) 1 := by
    rw [add_assoc, ← add_assoc (monomial a' 1), ← two_smul (ZMod 2) (monomial a' 1),
      show (2 : ZMod 2) = 0 from rfl, zero_smul, zero_add]
  rwa [e] at this

/-- A multilinear polynomial over `ZMod 2` vanishing at every point is zero. -/
theorem eq_zero_of_multilinear (q : MvPolynomial σ (ZMod 2))
    (hq : ∀ a ∈ q.support, ∀ v, a v ≤ 1) (h0 : ∀ x : σ → ZMod 2, eval x q = 0) : q = 0 := by
  classical
  obtain ⟨s, r, rfl⟩ := exists_finset_rename q
  have hinj : Function.Injective (Subtype.val : s → σ) := Subtype.val_injective
  have hr : r = 0 := by
    refine MvPolynomial.eq_zero_of_eval_eq_zero s (ZMod 2) r (fun y => ?_) ?_
    · have := h0 (fun v => if h : v ∈ s then y ⟨v, h⟩ else 0)
      rw [eval_rename] at this
      have hy : ((fun v => if h : v ∈ s then y ⟨v, h⟩ else 0) ∘ Subtype.val) = y := by
        funext w
        simp
      rwa [hy] at this
    · rw [mem_restrictDegree]
      intro c hc i
      have hc' : Finsupp.mapDomain Subtype.val c ∈ (rename Subtype.val r).support := by
        rw [mem_support_iff, coeff_rename_mapDomain _ hinj]
        exact mem_support_iff.mp hc
      have := hq _ hc' i
      rw [Finsupp.mapDomain_apply_of_injective hinj] at this
      simpa using this
  rw [hr, map_zero]

theorem vanish_derivable : ∀ (σ : Type) (F : Set (MvPolynomial σ (ZMod 2))) (d : ℕ) (p : MvPolynomial σ (ZMod 2)), (∀ v : σ, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F) → p.totalDegree ≤ d → (∀ x : σ → ZMod 2, MvPolynomial.eval x p = 0) → PEqualNP.ProofComplexity.PCDerivable F d p := by
  classical
  intro σ F d p hF hd hvan
  set p' : MvPolynomial σ (ZMod 2) :=
    ∑ a ∈ p.support, monomial (mlin a) (p.coeff a) with hp'
  have hcoeff : ∀ a ∈ p.support, p.coeff a = 1 := by
    intro a ha
    have h0 : p.coeff a ≠ 0 := mem_support_iff.mp ha
    generalize p.coeff a = c at h0
    revert h0; revert c; decide
  have hder : PCDerivable (boolAxioms σ) d (p + p') := by
    have : p + p' = ∑ a ∈ p.support, (monomial a 1 + monomial (mlin a) 1) := by
      conv_lhs => rw [p.as_sum]
      rw [hp', ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [hcoeff a ha]
    rw [this]
    refine pcDerivable_sum _ _ fun a ha => boolDerivable_monomial d _ a rfl ?_
    exact (le_totalDegree ha).trans hd
  have hbool : ∀ x : σ → ZMod 2, ∀ f ∈ boolAxioms σ, eval x f = 0 := by
    rintro x f ⟨v, rfl⟩
    simp only [map_add, map_mul, eval_X]
    generalize x v = c
    revert c; decide
  have hp'0 : p' = 0 := by
    refine eq_zero_of_multilinear p' ?_ ?_
    · intro c hc v
      obtain ⟨a, -, hca⟩ := Finset.mem_biUnion.mp (support_sum hc)
      rw [support_monomial] at hca
      split_ifs at hca
      · simp at hca
      · rw [Finset.mem_singleton.mp hca, mlin_apply]; omega
    · intro x
      have h1 := pcDerivable_eval_eq_zero hder x (hbool x)
      rwa [map_add, hvan x, zero_add] at h1
  have hpp : p = p + p' := by rw [hp'0, add_zero]
  rw [hpp]
  refine pcDerivable_mono hder le_rfl ?_
  rintro f ⟨v, rfl⟩
  exact hF v

end ClauseSearchPC.Toolkit.BoolVanish

namespace ClauseSearchPC

open MvPolynomial PEqualNP.ProofComplexity ClauseSearchPC.Toolkit

variable {V : Type}

abbrev Poly (V : Type) := MvPolynomial V (ZMod 2)

private theorem degreeOnePlus (p : Poly V) : (1 + p).totalDegree ≤ p.totalDegree :=
  (totalDegree_add _ _).trans (by simp)

private theorem clauseDegree (C : Clause V) : (clausePoly C).totalDegree ≤ C.card := by
  classical
  unfold clausePoly
  have bound (l : Literal V) :
      (if l.2 = true then 1 + X l.1 else (X l.1 : Poly V)).totalDegree ≤ 1 := by
    split_ifs
    · exact (degreeOnePlus _).trans_eq (totalDegree_X _)
    · exact (totalDegree_X _).le
  calc
    _ ≤ ∑ l ∈ C, (if l.2 = true then 1 + X l.1 else (X l.1 : Poly V)).totalDegree :=
      totalDegree_finsetProd _ _
    _ ≤ ∑ _l ∈ C, 1 := Finset.sum_le_sum (fun l _ => bound l)
    _ = _ := by simp

private theorem addSelf (p : Poly V) : p + p = 0 := by
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]

noncomputable def allSatisfied (out : Finset (Clause V)) : Poly V :=
  ∏ cl ∈ out, (1 + clausePoly cl)

private theorem degreeAllSatisfied (out : Finset (Clause V)) (w : ℕ)
    (width : ∀ cl ∈ out, cl.card ≤ w) : (allSatisfied out).totalDegree ≤ w * out.card := by
  unfold allSatisfied
  calc
    _ ≤ ∑ cl ∈ out, (1 + clausePoly cl).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ _cl ∈ out, w := Finset.sum_le_sum (fun cl mem =>
      (degreeOnePlus _).trans ((clauseDegree cl).trans (width cl mem)))
    _ = _ := by simp [Nat.mul_comm]

/-- Multiplying an indicator by the simultaneous clause-satisfaction
polynomial changes it by a bounded-degree consequence of those clauses. -/
private theorem replaceByIndicator (F : Set (Clause V)) (p : Poly V)
    (out : Finset (Clause V)) (w B : ℕ) (inside : ∀ cl ∈ out, cl ∈ F)
    (width : ∀ cl ∈ out, cl.card ≤ w) (budget : p.totalDegree + w * out.card ≤ B) :
    PCDerivable (cnfSystem F) B (p * allSatisfied out + p) := by
  classical
  induction out using Finset.induction_on with
  | empty =>
    simpa [allSatisfied, addSelf] using (PCDerivable.zero (F := cnfSystem F) (B := B))
  | @insert cl out new prior =>
    have widthTail c (hc : c ∈ out) := width c (Finset.mem_insert_of_mem hc)
    have widthHead := width cl (Finset.mem_insert_self cl out)
    rw [Finset.card_insert_of_notMem new, Nat.mul_succ] at budget
    have previous := prior (fun c hc => inside c (Finset.mem_insert_of_mem hc)) widthTail (by omega)
    have axiomCl : PCDerivable (cnfSystem F) B (clausePoly cl) :=
      .ax (Or.inr ⟨cl, inside cl (Finset.mem_insert_self cl out), rfl⟩)
        ((clauseDegree cl).trans (widthHead.trans (by omega)))
    have partDegree := (totalDegree_mul p (allSatisfied out)).trans
      (Nat.add_le_add_left (degreeAllSatisfied out w widthTail) _)
    have clauseBound := (clauseDegree cl).trans widthHead
    have added := pcDerivable_mul_left axiomCl (p * allSatisfied out)
    have extra := pcDerivable_mono added (max_le le_rfl (by omega)) subset_rfl
    rw [allSatisfied, Finset.prod_insert new, ← allSatisfied]
    have identity : p * ((1 + clausePoly cl) * allSatisfied out) + p =
        (p * allSatisfied out + p) + (p * allSatisfied out) * clausePoly cl := by ring
    rw [identity]
    exact .add previous extra

/-- Exact clause search on a partition with indicators of degree at most
`r`, using lists of up to `k` clauses of width `w`, refutes the CNF in
polynomial calculus of degree at most `r + w*k`. -/
theorem refuteFromIndicators {I : Type} (F : Set (Clause V)) (cells : Finset I)
    (indicator : I → Poly V) (out : I → Finset (Clause V)) (r w k : ℕ)
    (degree : ∀ i ∈ cells, (indicator i).totalDegree ≤ r)
    (width : ∀ i ∈ cells, ∀ cl ∈ out i, cl ∈ F ∧ cl.card ≤ w)
    (capacity : ∀ i ∈ cells, (out i).card ≤ k)
    (partition : ∀ x : V → ZMod 2, ∑ i ∈ cells, eval x (indicator i) = 1)
    (correct : ∀ i ∈ cells, ∀ x : V → ZMod 2, eval x (indicator i) = 1 →
      ∃ cl ∈ out i, eval x (clausePoly cl) = 1) : PCRefutable (cnfSystem F) (r + w*k) := by
  classical
  let B := r + w*k
  have boolean (v : V) : X v * X v + X v ∈ cnfSystem F := Or.inl ⟨v, rfl⟩
  have derive (i : I) (mem : i ∈ cells) : PCDerivable (cnfSystem F) B (indicator i) := by
    have localWidth cl (h : cl ∈ out i) := (width i mem cl h).2
    have count := Nat.mul_le_mul_left w (capacity i mem)
    have budget : (indicator i).totalDegree + w*(out i).card ≤ B := Nat.add_le_add (degree i mem) count
    let product := indicator i * allSatisfied (out i)
    have degreeProduct : product.totalDegree ≤ B :=
      (totalDegree_mul _ _).trans ((Nat.add_le_add_left (degreeAllSatisfied _ w localWidth) _).trans budget)
    have van (x : V → ZMod 2) : eval x product = 0 := by
      change eval x (indicator i * allSatisfied (out i)) = 0
      rw [map_mul]
      by_cases eq : eval x (indicator i) = 1
      · obtain ⟨cl, hit, hfalse⟩ := correct i mem x eq
        have outputZero : eval x (allSatisfied (out i)) = 0 := by
          rw [allSatisfied, map_prod]
          exact Finset.prod_eq_zero hit (by rw [map_add, map_one, hfalse]; decide)
        rw [outputZero, mul_zero]
      · have zero : eval x (indicator i) = 0 := by
          generalize eval x (indicator i) = a at eq ⊢
          revert a
          decide
        rw [zero, zero_mul]
    have zeroLine := BoolVanish.vanish_derivable V (cnfSystem F) B product boolean degreeProduct van
    have delta := replaceByIndicator F (indicator i) (out i) w B
      (fun cl h => (width i mem cl h).1) localWidth budget
    have result := PCDerivable.add delta zeroLine
    have cancel : product + indicator i + product = indicator i := calc
      _ = indicator i + (product + product) := by ac_rfl
      _ = _ := by rw [addSelf, add_zero]
    change PCDerivable (cnfSystem F) B (product + indicator i + product) at result
    rwa [cancel] at result
  let total := ∑ i ∈ cells, indicator i
  have deriveTotal : PCDerivable (cnfSystem F) B total := pcDerivable_sum cells indicator derive
  have totalDegreeBound : total.totalDegree ≤ r := totalDegree_finsetSum_le degree
  have vanished := BoolVanish.vanish_derivable V (cnfSystem F) B (total + 1) boolean
    ((totalDegree_add _ _).trans (max_le (totalDegreeBound.trans (Nat.le_add_right _ _)) (by simp)))
    (fun x => by change eval x ((∑ i ∈ cells, indicator i) + 1) = 0
                 rw [map_add, map_sum, map_one, partition x]; decide)
  have contradiction := PCDerivable.add deriveTotal vanished
  have cancel : total + (total + 1) = 1 := by rw [← add_assoc, addSelf, zero_add]
  rwa [cancel] at contradiction

private theorem bitCases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

private theorem productBit (a b : ZMod 2) : a * b = 1 ↔ a = 1 ∧ b = 1 := by
  revert a b
  decide

theorem clauseFalse (cl : Clause V) (x : V → ZMod 2) :
    eval x (clausePoly cl) = 1 ↔ ¬ ClauseSat (fun v => decide (x v = 1)) cl := by
  classical
  have factor (a : ZMod 2) (b : Bool) :
      (if b = true then 1 + a else a) = 1 ↔ decide (a = 1) ≠ b := by
    revert a b
    decide
  induction cl using Finset.induction_on with
  | empty => simp [clausePoly, ClauseSat]
  | @insert l cl fresh prev =>
    have head : eval x (if l.2 = true then 1 + X l.1 else (X l.1 : Poly V)) = 1 ↔
        decide (x l.1 = 1) ≠ l.2 := by
      rw [apply_ite (eval x)]
      simpa using factor (x l.1) l.2
    have insertSat : ClauseSat (fun v => decide (x v = 1)) (insert l cl) ↔
        decide (x l.1 = 1) = l.2 ∨ ClauseSat (fun v => decide (x v = 1)) cl := by
      simp only [ClauseSat, Finset.mem_insert]
      constructor
      · rintro ⟨a, (rfl | hit), value⟩
        · exact Or.inl value
        · exact Or.inr ⟨a, hit, value⟩
      · rintro (hit | ⟨a, mem, hit⟩)
        · exact ⟨l, Or.inl rfl, hit⟩
        · exact ⟨a, Or.inr mem, hit⟩
    have split : clausePoly (insert l cl) =
        (if l.2 = true then 1 + X l.1 else X l.1) * clausePoly cl := by
      simp only [clausePoly, Finset.prod_insert fresh]
    rw [split, map_mul, productBit]
    exact (and_congr head prev).trans (not_or.symm.trans (not_congr insertSat.symm))

noncomputable def affineCell (equations : List (Poly V)) : Poly V :=
  (equations.map fun p => 1 + p).prod

private theorem affineCellDegree (equations : List (Poly V))
    (degree : ∀ p ∈ equations, p.totalDegree ≤ 1) : (affineCell equations).totalDegree ≤ equations.length := by
  induction equations with
  | nil => simp [affineCell]
  | cons p equations prior =>
    have first := (degreeOnePlus p).trans (degree p (List.mem_cons_self ..))
    have rest := prior (fun q mem => degree q (List.mem_cons_of_mem _ mem))
    simpa only [affineCell, List.map_cons, List.prod_cons, List.length_cons, Nat.add_comm] using
      ((totalDegree_mul (1+p) (affineCell equations)).trans (Nat.add_le_add first rest))

private theorem affineCellTruth (equations : List (Poly V)) (x : V → ZMod 2) :
    eval x (affineCell equations) = 1 ↔ ∀ p ∈ equations, eval x p = 0 := by
  have bit (a : ZMod 2) : 1+a = 1 ↔ a = 0 := by
    revert a
    decide
  induction equations with
  | nil => simp [affineCell]
  | cons p equations prior =>
    change eval x ((1+p)*affineCell equations) = 1 ↔ _
    rw [map_mul, productBit, map_add, map_one]
    simpa only [List.forall_mem_cons] using and_congr (bit (eval x p)) prior

/-- If every assignment belongs to a unique affine cell and the list for
that cell always contains a violated clause, the cell and list budgets
give a polynomial calculus degree bound. -/
theorem refuteFromAffinePartition {I : Type} (F : Set (Clause V)) (cells : Finset I)
    (equations : I → List (Poly V)) (out : I → Finset (Clause V)) (r w k : ℕ)
    (affine : ∀ i ∈ cells, ∀ p ∈ equations i, p.totalDegree ≤ 1)
    (codim : ∀ i ∈ cells, (equations i).length ≤ r)
    (width : ∀ i ∈ cells, ∀ cl ∈ out i, cl ∈ F ∧ cl.card ≤ w)
    (capacity : ∀ i ∈ cells, (out i).card ≤ k)
    (partition : ∀ x : V → ZMod 2, ∃! i : {j // j ∈ cells}, ∀ p ∈ equations i.val, eval x p = 0)
    (correct : ∀ i ∈ cells, ∀ x : V → ZMod 2, (∀ p ∈ equations i, eval x p = 0) →
      ∃ cl ∈ out i, ¬ ClauseSat (fun v => decide (x v = 1)) cl) :
    PCRefutable (cnfSystem F) (r + w*k) := by
  classical
  let indicator i := affineCell (equations i)
  refine refuteFromIndicators F cells indicator out r w k
    (fun i hi => (affineCellDegree _ (affine i hi)).trans (codim i hi)) width capacity ?_ ?_
  · intro x
    obtain ⟨⟨i, hi⟩, belongs, unique⟩ := partition x
    rw [Finset.sum_eq_single i]
    · exact (affineCellTruth _ x).mpr belongs
    · intro j hj diff
      rcases bitCases (eval x (indicator j)) with zero | one
      · exact zero
      · exact (diff (congrArg Subtype.val (unique ⟨j, hj⟩ ((affineCellTruth _ x).mp one)))).elim
    · exact (fun miss => (miss hi).elim)
  · intro i hi x one
    obtain ⟨cl, mem, notSat⟩ := correct i hi x ((affineCellTruth _ x).mp one)
    exact ⟨cl, mem, (clauseFalse cl x).mpr notSat⟩

section QuotientEquations

variable [Fintype V] [DecidableEq V]

noncomputable def linearPolynomial (l : (V → ZMod 2) →ₗ[ZMod 2] ZMod 2) : Poly V :=
  ∑ v, C (l (Pi.single v 1)) * X v

private theorem linearDegree (l : (V → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    (linearPolynomial l).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro v _
  exact (totalDegree_mul _ _).trans (by simp)

private theorem evalLinear (l : (V → ZMod 2) →ₗ[ZMod 2] ZMod 2) (x : V → ZMod 2) :
    eval x (linearPolynomial l) = l x := by
  classical
  have expands : (∑ v, x v • (Pi.single v 1 : V → ZMod 2)) = x := by
    ext u
    simp [Pi.single_apply, Pi.smul_apply]
  calc
    _ = l (∑ v, x v • (Pi.single v 1 : V → ZMod 2)) := by
      simp [linearPolynomial, mul_comm]
    _ = _ := congrArg l expands

/-- A coset has one linear equation per dimension of the quotient. -/
theorem equationsForTranslate (U : Submodule (ZMod 2) (V → ZMod 2)) (origin : V → ZMod 2) :
    ∃ equations : List (Poly V),
      equations.length = Module.finrank (ZMod 2) ((V → ZMod 2) ⧸ U) ∧
      (∀ p ∈ equations, p.totalDegree ≤ 1) ∧
      ∀ x, (∀ p ∈ equations, eval x p = 0) ↔ x - origin ∈ U := by
  classical
  let basis := Module.finBasis (ZMod 2) ((V → ZMod 2) ⧸ U)
  let coord i := (basis.coord i).comp U.mkQ
  let equation i := linearPolynomial (coord i) - C (coord i origin)
  refine ⟨List.ofFn equation, by simp, ?_, ?_⟩
  · intro p mem
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp mem
    exact (totalDegree_sub_C_le _ _).trans (linearDegree _)
  · intro x
    have eqEval (i : Fin (Module.finrank (ZMod 2) ((V → ZMod 2) ⧸ U))) :
        eval x (equation i) = 0 ↔ coord i x = coord i origin := by
      simp [equation, evalLinear, sub_eq_zero]
    have quotient : U.mkQ x = U.mkQ origin ↔ x - origin ∈ U := by
      rw [← sub_eq_zero, ← map_sub]
      exact Submodule.Quotient.mk_eq_zero U
    rw [← quotient]
    constructor
    · intro all
      apply basis.repr.injective
      ext i
      exact (eqEval i).mp (all (equation i) (List.mem_ofFn.mpr ⟨i, rfl⟩))
    · intro eq p mem
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp mem
      exact (eqEval i).mpr (congrArg (basis.coord i) eq)

theorem refuteFromCosets {I : Type} (F : Set (Clause V)) (cells : Finset I)
    (origin : I → V → ZMod 2) (U : I → Submodule (ZMod 2) (V → ZMod 2))
    (out : I → Finset (Clause V)) (r w k : ℕ)
    (codim : ∀ i ∈ cells, Module.finrank (ZMod 2) ((V → ZMod 2) ⧸ U i) ≤ r)
    (width : ∀ i ∈ cells, ∀ cl ∈ out i, cl ∈ F ∧ cl.card ≤ w)
    (capacity : ∀ i ∈ cells, (out i).card ≤ k)
    (partition : ∀ x, ∃! i : {j // j ∈ cells}, x - origin i.val ∈ U i.val)
    (correct : ∀ i ∈ cells, ∀ x, x - origin i ∈ U i →
      ∃ cl ∈ out i, ¬ ClauseSat (fun v => decide (x v = 1)) cl) :
    PCRefutable (cnfSystem F) (r + w*k) := by
  classical
  choose eqs length small truth using fun i : I => equationsForTranslate (U i) (origin i)
  exact refuteFromAffinePartition F cells eqs out r w k (fun i _ => small i)
    (fun i mem => (length i).trans_le (codim i mem)) width capacity
    (fun x => by simpa only [truth] using partition x)
    (fun i hi x all => correct i hi x ((truth i x).mp all))

omit [DecidableEq V] in
private theorem refineCodimension {Y : Type} [AddCommGroup Y] [Module (ZMod 2) Y]
    (U : Submodule (ZMod 2) (V → ZMod 2)) (M : (V → ZMod 2) →ₗ[ZMod 2] Y) :
    Module.finrank (ZMod 2) ((V → ZMod 2) ⧸ (U ⊓ LinearMap.ker M)) =
      Module.finrank (ZMod 2) ((V → ZMod 2) ⧸ U) +
        Module.finrank (ZMod 2) (LinearMap.range (M.comp U.subtype)) := by
  let M' := M.comp U.subtype
  let U' := U ⊓ LinearMap.ker M
  let into : U' →ₗ[ZMod 2] LinearMap.ker M' :=
    { toFun := fun z => ⟨⟨z.val, z.property.1⟩, z.property.2⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let iden := LinearEquiv.ofBijective into ⟨by
       intro z u eq
       exact Subtype.ext (congrArg (fun a : LinearMap.ker M' => a.val.val) eq), by
       intro z
       exact ⟨⟨z.val.val, ⟨z.val.property, z.property⟩⟩, rfl⟩⟩
  have first := U.finrank_quotient_add_finrank
  have refined := U'.finrank_quotient_add_finrank
  have rankNull := M'.finrank_range_add_finrank_ker
  have equal := LinearEquiv.finrank_eq iden
  change Module.finrank (ZMod 2) ((V → ZMod 2) ⧸ U') =
    Module.finrank (ZMod 2) ((V → ZMod 2) ⧸ U) + Module.finrank (ZMod 2) (LinearMap.range M')
  omega

/-- Refine each coset by its message. The local rank of the message map is
the additional codimension, regardless of the message dimension. -/
theorem refuteFromPiecewiseMessages {I Y : Type} [AddCommGroup Y] [Module (ZMod 2) Y]
    (F : Set (Clause V)) (cells : Finset I)
    (origin : I → V → ZMod 2) (U : I → Submodule (ZMod 2) (V → ZMod 2))
    (offset : I → Y) (M : I → (V → ZMod 2) →ₗ[ZMod 2] Y)
    (out : Y → Finset (Clause V)) (r s w k : ℕ)
    (codim : ∀ i ∈ cells, Module.finrank (ZMod 2) ((V → ZMod 2) ⧸ U i) ≤ r)
    (ranks : ∀ i ∈ cells, Module.finrank (ZMod 2) (LinearMap.range ((M i).comp (U i).subtype)) ≤ s)
    (partition : ∀ x, ∃! i : {j // j ∈ cells}, x - origin i.val ∈ U i.val)
    (width : ∀ i ∈ cells, ∀ x, x - origin i ∈ U i →
      ∀ cl ∈ out (offset i + M i (x - origin i)), cl ∈ F ∧ cl.card ≤ w)
    (capacity : ∀ i ∈ cells, ∀ x, x - origin i ∈ U i →
      (out (offset i + M i (x - origin i))).card ≤ k)
    (correct : ∀ i ∈ cells, ∀ x, x - origin i ∈ U i →
      ∃ cl ∈ out (offset i + M i (x - origin i)), ¬ ClauseSat (fun v => decide (x v = 1)) cl) :
    PCRefutable (cnfSystem F) (r + s + w*k) := by
  classical
  let word i (x : V → ZMod 2) := offset i + M i (x - origin i)
  let inputs i := (Finset.univ : Finset (V → ZMod 2)).filter fun x => x - origin i ∈ U i
  let refined := cells.biUnion fun i => (inputs i).image fun x => (i, word i x)
  have live (p : I × Y) : p ∈ refined ↔ p.1 ∈ cells ∧
      ∃ x, x - origin p.1 ∈ U p.1 ∧ word p.1 x = p.2 := by
    constructor
    · intro mem
      obtain ⟨i, hi, image⟩ := Finset.mem_biUnion.mp mem
      obtain ⟨x, xin, rfl⟩ := Finset.mem_image.mp image
      exact ⟨hi, x, (Finset.mem_filter.mp xin).2, rfl⟩
    · rintro ⟨hi, x, xin, eq⟩
      exact Finset.mem_biUnion.mpr ⟨p.1, hi, Finset.mem_image.mpr
        ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, xin⟩, Prod.ext rfl eq⟩⟩
  let J := {p : I × Y // p ∈ refined}
  have origins (p : J) : ∃ x, x - origin p.val.1 ∈ U p.val.1 ∧ word p.val.1 x = p.val.2 :=
    ((live p.val).mp p.property).2
  choose newOrigin originProperty using origins
  let newU (p : J) := U p.val.1 ⊓ LinearMap.ker (M p.val.1)
  have hits (p : J) (x : V → ZMod 2) : x - newOrigin p ∈ newU p ↔
      x - origin p.val.1 ∈ U p.val.1 ∧ word p.val.1 x = p.val.2 := by
    have translate : x - newOrigin p = (x - origin p.val.1) - (newOrigin p - origin p.val.1) := by abel
    have sameCoset : x - newOrigin p ∈ U p.val.1 ↔ x - origin p.val.1 ∈ U p.val.1 := by
      rw [translate]
      exact (U p.val.1).sub_mem_iff_left (originProperty p).1
    have sameWord : x - newOrigin p ∈ LinearMap.ker (M p.val.1) ↔ word p.val.1 x = p.val.2 := by
      rw [translate, LinearMap.mem_ker, map_sub, sub_eq_zero, ← (originProperty p).2]
      simp only [word, add_right_inj]
    exact and_congr sameCoset sameWord
  have firstMem (p : J) : p.val.1 ∈ cells := ((live p.val).mp p.property).1
  apply refuteFromCosets F (Finset.univ : Finset J) newOrigin newU (fun p => out p.val.2) (r+s) w k
  · intro p _
    change Module.finrank (ZMod 2) ((V → ZMod 2) ⧸ (U p.val.1 ⊓ LinearMap.ker (M p.val.1))) ≤ r+s
    rw [refineCodimension]
    exact Nat.add_le_add (codim _ (firstMem p)) (ranks _ (firstMem p))
  · intro p _
    rw [← (originProperty p).2]
    exact width _ (firstMem p) _ (originProperty p).1
  · intro p _
    rw [← (originProperty p).2]
    exact capacity _ (firstMem p) _ (originProperty p).1
  · intro x
    obtain ⟨⟨i, hi⟩, inCell, unique⟩ := partition x
    let p : J := ⟨(i, word i x), (live _).mpr ⟨hi, x, inCell, rfl⟩⟩
    refine ⟨⟨p, Finset.mem_univ _⟩, (hits p x).mpr ⟨inCell, rfl⟩, ?_⟩
    intro q contains
    have ⟨contains0, wordEq⟩ := (hits q.val x).mp contains
    have idEq : q.val.val.1 = i := congrArg Subtype.val (unique ⟨q.val.val.1, firstMem q.val⟩ contains0)
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext idEq (wordEq.symm.trans (congrArg (fun j => word j x) idEq))
  · intro p _ x mem
    have ⟨old, eq⟩ := (hits p x).mp mem
    rw [← eq]
    exact correct _ (firstMem p) _ old

/-- A failed input extends to a whole affine set of failures. Besides the
cell and message constraints, each satisfied clause costs at most one
additional coordinate constraint. -/
theorem cosetAroundFailure {Y : Type} [AddCommGroup Y] [Module (ZMod 2) Y]
    (origin x₀ : V → ZMod 2) (U : Submodule (ZMod 2) (V → ZMod 2))
    (M : (V → ZMod 2) →ₗ[ZMod 2] Y) (out : Finset (Clause V))
    (mem : x₀ - origin ∈ U) (satisfied : ∀ cl ∈ out, ClauseSat (fun v => decide (x₀ v = 1)) cl) :
    ∃ W : Submodule (ZMod 2) (V → ZMod 2),
      Module.finrank (ZMod 2) ((V → ZMod 2) ⧸ W) ≤
        Module.finrank (ZMod 2) ((V → ZMod 2) ⧸ U) +
          Module.finrank (ZMod 2) (LinearMap.range (M.comp U.subtype)) + out.card ∧
      ∀ x, x - x₀ ∈ W → x - origin ∈ U ∧ M (x - origin) = M (x₀ - origin) ∧
        ∀ cl ∈ out, ClauseSat (fun v => decide (x v = 1)) cl := by
  classical
  have chooseLiteral (c : {cl // cl ∈ out}) :
      ∃ l ∈ c.val, decide (x₀ l.1 = 1) = l.2 := satisfied c.val c.property
  choose lit hit value using chooseLiteral
  let pins := Finset.univ.image fun c => (lit c).1
  have count : pins.card ≤ out.card := (Finset.card_image_le).trans_eq (by simp)
  let fix : (V → ZMod 2) →ₗ[ZMod 2] (pins → ZMod 2) :=
    LinearMap.pi fun v : pins => LinearMap.proj v.val
  let fiber := U ⊓ LinearMap.ker M
  let W := fiber ⊓ LinearMap.ker fix
  refine ⟨W, ?_, ?_⟩
  · have extra := Submodule.finrank_le (LinearMap.range (fix.comp fiber.subtype))
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at extra
    change Module.finrank (ZMod 2) ((V → ZMod 2) ⧸ (fiber ⊓ LinearMap.ker fix)) ≤ _
    rw [refineCodimension]
    change Module.finrank (ZMod 2) ((V → ZMod 2) ⧸ (U ⊓ LinearMap.ker M)) + _ ≤ _
    rw [refineCodimension]
    exact Nat.add_le_add_left (extra.trans count) _
  · intro x hx
    obtain ⟨⟨inU, equal⟩, pinned⟩ := hx
    have split : x - origin = (x - x₀) + (x₀ - origin) := by abel
    have old : x - origin ∈ U := split ▸ U.add_mem inU mem
    have same : M (x - origin) = M (x₀ - origin) := by
      rw [split, map_add, LinearMap.mem_ker.mp equal, zero_add]
    refine ⟨old, same, fun cl hc => ?_⟩
    let c : {cl // cl ∈ out} := ⟨cl, hc⟩
    have inPins : (lit c).1 ∈ pins := Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have fixed := congrFun (LinearMap.mem_ker.mp pinned) (⟨_, inPins⟩ : pins)
    have atBit : x (lit c).1 = x₀ (lit c).1 := sub_eq_zero.mp fixed
    exact ⟨lit c, hit c, by simpa only [atBit] using value c⟩

end QuotientEquations

end ClauseSearchPC

namespace ClauseSearchCircuitCells

open PEqualNP.ProofComplexity PEqualNP.CircuitLowerBounds

variable {V : Type}

-- Affine forms and the one-gate evaluation lemma are from the accepted L-pcx-401.
/-- An affine form over the two-element field: coefficients and a constant. -/
abbrev Af (V : Type) := (V → ZMod 2) × ZMod 2

/-- The value of an affine form. -/
def av [Fintype V] (f : Af V) (y : V → ZMod 2) : ZMod 2 := (∑ v, f.1 v * y v) + f.2

lemma av_add [Fintype V] (f g : Af V) (y : V → ZMod 2) : av (f + g) y = av f y + av g y := by
  simp only [av, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

lemma av_zero [Fintype V] (y : V → ZMod 2) : av (0 : Af V) y = 0 := by
  simp [av]

lemma av_one [Fintype V] (y : V → ZMod 2) : av (((0 : V → ZMod 2), (1 : ZMod 2)) : Af V) y = 1 := by
  simp [av]

lemma av_list_sum [Fintype V] (l : List (Af V)) (y : V → ZMod 2) :
    av l.sum y = (l.map (fun f => av f y)).sum := by
  induction l with
  | nil => simp [av_zero]
  | cons f l ih => simp [List.sum_cons, av_add, ih]

lemma av_vadd [Fintype V] (f : Af V) (y u : V → ZMod 2) :
    av f (y + u) = av f y + ∑ v, f.1 v * u v := by
  simp only [av, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

def isNL (g : Gate) : Bool :=
  match g.op with
  | .and => true
  | .or => true
  | _ => false

def nl (gs : List Gate) : ℕ := gs.countP isNL

def rd (w : List (Af V)) (l : List ℕ) : List (Af V) := l.map (fun i => w.getD i 0)

def qform (g : Gate) (w : List (Af V)) : Af V := (rd w g.inputs).headD 0

def stepOp : GateOp → List (Af V) → Bool → Af V
  | .and, l, β => if β then l.getD 1 0 else 0
  | .or, l, β => if β then ((0 : V → ZMod 2), (1 : ZMod 2)) else l.getD 1 0
  | .not, l, _ => ((0 : V → ZMod 2), (1 : ZMod 2)) + l.headD 0
  | .mod _, l, _ => ((0 : V → ZMod 2), (1 : ZMod 2)) + l.sum
  | .maj, _, _ => 0

def stepF (g : Gate) (w : List (Af V)) (β : Bool) : Af V := stepOp g.op (rd w g.inputs) β

def Shape (g : Gate) : Prop :=
  ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨ g.op = .mod 2 ∨
    (g.op = .not ∧ g.inputs.length = 1)

def Agree [Fintype V] (w : List (Af V)) (wb : List Bool) (y : V → ZMod 2) : Prop :=
  w.length = wb.length ∧ ∀ i, av (w.getD i 0) y = ((wb.getD i false).toNat : ZMod 2)

lemma agree_append [Fintype V] {w : List (Af V)} {wb : List Bool} {y : V → ZMod 2}
    (hA : Agree w wb y) {a : Af V} {c : Bool} (hac : av a y = (c.toNat : ZMod 2)) :
    Agree (w ++ [a]) (wb ++ [c]) y := by
  obtain ⟨hl, h⟩ := hA
  refine ⟨by simp [hl], fun i => ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rcases lt_trichotomy i w.length with hi | hi | hi
  · rw [List.getElem?_append_left hi, List.getElem?_append_left (hl ▸ hi),
      ← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
    exact h i
  · subst hi
    rw [List.getElem?_append_right le_rfl, List.getElem?_append_right (le_of_eq hl.symm)]
    simp [hl, hac]
  · rw [List.getElem?_append_right hi.le, List.getElem?_append_right (hl ▸ hi.le)]
    have h1 : [a][i - w.length]? = none := by
      rw [List.getElem?_eq_none_iff]; simp; omega
    have h2 : [c][i - wb.length]? = none := by
      rw [List.getElem?_eq_none_iff]; simp; omega
    rw [h1, h2]
    simp [av_zero]

lemma count_cast (l : List Bool) :
    ((l.count true : ℕ) : ZMod 2) = (l.map (fun c => (c.toNat : ZMod 2))).sum := by
  induction l with
  | nil => simp
  | cons c l ih =>
    cases c
    · simp [ih]
    · simp [ih]
      ring

lemma mod_cast2 (c : ℕ) : ((decide (c % 2 = 0)).toNat : ZMod 2) = 1 + (c : ZMod 2) := by
  rw [← ZMod.natCast_mod c 2]
  rcases Nat.mod_two_eq_zero_or_one c with h | h <;> rw [h] <;> decide

lemma step_ok [Fintype V] (y : V → ZMod 2) (g : Gate) (hg : Shape g) (w : List (Af V))
    (wb : List Bool) (hA : ∀ i, av (w.getD i 0) y = ((wb.getD i false).toNat : ZMod 2))
    (β : Bool) (hβ : isNL g = true → (β = true ↔ av (qform g w) y = 1)) :
    av (stepF g w β) y = ((g.op.eval (g.inputs.map fun i => wb.getD i false)).toNat : ZMod 2) := by
  rcases hg with ⟨hop, hlen⟩ | hop | ⟨hop, hlen⟩
  · obtain ⟨i, j, hij⟩ := List.length_eq_two.mp hlen
    have hnl : isNL g = true := by
      rcases hop with h | h <;> simp [isNL, h]
    have hb := hβ hnl
    simp only [qform, rd, hij, List.map_cons, List.map_nil, List.headD_cons] at hb
    rw [hA i] at hb
    have hi := hA i
    have hj := hA j
    rcases hop with h | h
    · simp only [stepF, rd, hij, h, List.map_cons, List.map_nil, stepOp, GateOp.eval]
      cases hwi : wb.getD i false <;> cases β <;> simp_all [av_zero]
    · simp only [stepF, rd, hij, h, List.map_cons, List.map_nil, stepOp, GateOp.eval]
      cases hwi : wb.getD i false <;> cases β <;> simp_all [av_one]
  · simp only [stepF, rd, hop, stepOp, GateOp.eval]
    rw [av_add, av_one, av_list_sum, mod_cast2, count_cast, List.map_map, List.map_map]
    congr 2
    apply List.map_congr_left
    intro i _
    exact hA i
  · obtain ⟨i, hi⟩ := List.length_eq_one_iff.mp hlen
    simp only [stepF, rd, hop, hi, stepOp, GateOp.eval, List.map_cons, List.map_nil,
      List.headD_cons]
    rw [av_add, av_one, hA i]
    cases wb.getD i false <;> decide

lemma init_agree [Fintype V] [DecidableEq V] (n : ℕ) (order : Fin n → V) (y : V → ZMod 2) :
    Agree ([0, ((0 : V → ZMod 2), (1 : ZMod 2))] ++
      List.ofFn (fun i : Fin n => ((Pi.single (order i) (1 : ZMod 2) : V → ZMod 2), (0 : ZMod 2))))
      ([false, true] ++ List.ofFn (fun i : Fin n => decide (y (order i) = 1))) y := by
  refine ⟨by simp, fun i => ?_⟩
  have hz : ∀ c : ZMod 2, c = ((decide (c = 1)).toNat : ZMod 2) := by decide
  rcases i with _ | _ | k
  · simp [av_zero]
  · simp [av_one]
  · simp only [List.cons_append, List.nil_append, List.getD_cons_succ]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      List.getElem?_ofFn]
    by_cases hk : k < n
    · simp only [hk, dite_true, Option.getD_some]
      rw [← hz]
      simp [av, Pi.single_apply]
    · simp [hk, av_zero]

def concreteStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def firstBit (g : Gate) (w : List Bool) : Bool :=
  (g.inputs.map fun i => w.getD i false).headD false

def concreteTrace : List Gate → List Bool → List Bool
  | [], _ => []
  | g :: gs, w =>
    let trace := concreteTrace gs (concreteStep w g)
    if isNL g then firstBit g w :: trace else trace

def specialize : List Gate → List (Af V) → List Bool → List (Af V) × List (Af V × Bool)
  | [], w, _ => (w, [])
  | g :: gs, w, bs =>
    if isNL g then
      let bit := bs.headD false
      let part := specialize gs (w ++ [stepF g w bit]) (bs.drop 1)
      (part.1, (qform g w, bit) :: part.2)
    else specialize gs (w ++ [stepF g w false]) bs

def fits [Fintype V] (x : V → ZMod 2) (qs : List (Af V × Bool)) : Prop :=
  ∀ q ∈ qs, av q.1 x = (q.2.toNat : ZMod 2)

theorem traceLength (gs : List Gate) (w : List Bool) : (concreteTrace gs w).length = nl gs := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    by_cases read : isNL g = true <;> simp [concreteTrace, nl, read, ih]

theorem specializationLength (gs : List Gate) (w : List (Af V)) (bs : List Bool) :
    (specialize gs w bs).2.length = nl gs := by
  induction gs generalizing w bs with
  | nil => rfl
  | cons g gs ih =>
    by_cases read : isNL g = true <;> simp [specialize, nl, read, ih]

private theorem qformAgree [Fintype V] (g : Gate) {w : List (Af V)} {wb : List Bool}
    {x : V → ZMod 2} (agree : Agree w wb x) : av (qform g w) x = (firstBit g wb).toNat := by
  cases h : g.inputs with
  | nil => simp [qform, rd, firstBit, h, av_zero]
  | cons i rest => simpa [qform, rd, firstBit, h] using agree.2 i

/-- A specialization fits exactly those inputs with the given concrete
nonlinear trace. On that set its affine wires evaluate to the real wires. -/
theorem specializationCorrect [Fintype V] (x : V → ZMod 2) (gs : List Gate)
    (w : List (Af V)) (wb bs : List Bool) (shape : ∀ g ∈ gs, Shape g)
    (agree : Agree w wb x) (length : bs.length = nl gs) :
    (fits x (specialize gs w bs).2 ↔ concreteTrace gs wb = bs) ∧
      (fits x (specialize gs w bs).2 → Agree (specialize gs w bs).1 (gs.foldl concreteStep wb) x) := by
  induction gs generalizing w wb bs with
  | nil =>
    have empty : bs = [] := List.length_eq_zero_iff.mp length
    subst bs
    simpa [specialize, fits, concreteTrace] using agree
  | cons g gs ih =>
    have gate := shape g (by simp)
    have tail : ∀ g ∈ gs, Shape g := fun h mem => shape h (List.mem_cons_of_mem _ mem)
    by_cases read : isNL g = true
    · have more : nl (g :: gs) = nl gs + 1 := by simp [nl, read]
      cases bs with
      | nil => simp [more] at length
      | cons b bs =>
        have lenTail : bs.length = nl gs := by simpa [more] using length
        let w' := w ++ [stepF g w b]
        let wb' := concreteStep wb g
        have inputEq : av (qform g w) x = (b.toNat : ZMod 2) ↔ firstBit g wb = b := by
          rw [qformAgree g agree]
          cases firstBit g wb <;> cases b <;> decide
        have next (value : firstBit g wb = b) : Agree w' wb' x := by
          apply agree_append agree
          apply step_ok x g gate w wb agree.2 b
          intro _
          rw [(inputEq.mpr value)]
          cases b <;> decide
        simp only [specialize, read, ite_true, List.headD_cons, List.drop_one, List.tail_cons,
          fits, List.forall_mem_cons, concreteTrace, List.cons.injEq, List.foldl_cons]
        change ((av (qform g w) x = (b.toNat : ZMod 2) ∧ fits x (specialize gs w' bs).2) ↔
            firstBit g wb = b ∧ concreteTrace gs wb' = bs) ∧
          ((av (qform g w) x = (b.toNat : ZMod 2) ∧ fits x (specialize gs w' bs).2) →
            Agree (specialize gs w' bs).1 (gs.foldl concreteStep wb') x)
        rw [inputEq]
        refine ⟨?_, ?_⟩
        · exact and_congr_right (fun value => (ih w' wb' bs tail (next value) lenTail).1)
        · rintro ⟨value, rest⟩
          exact (ih w' wb' bs tail (next value) lenTail).2 rest
    · have lenTail : bs.length = nl gs := by simpa [nl, read] using length
      have next : Agree (w ++ [stepF g w false]) (concreteStep wb g) x :=
        agree_append agree (step_ok x g gate w wb agree.2 false (fun h => (read h).elim))
      simpa [specialize, concreteTrace, read] using ih _ _ bs tail next lenTail

noncomputable def linearPart [Fintype V] (f : Af V) : (V → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  ∑ v, f.1 v • LinearMap.proj v

private theorem linearApply [Fintype V] (f : Af V) (x : V → ZMod 2) :
    linearPart f x = ∑ v, f.1 v * x v := by
  simp [linearPart, LinearMap.sum_apply]

private theorem diffAffine [Fintype V] (f : Af V) (x y : V → ZMod 2) :
    av f x - av f y = linearPart f (x-y) := by
  have add := av_vadd f y (x-y)
  have split : y + (x-y) = x := by abel
  rw [split] at add
  rw [linearApply]
  exact sub_eq_iff_eq_add.mpr (add.trans (add_comm _ _))

noncomputable def constraintMap [Fintype V] (qs : List (Af V × Bool)) :
    (V → ZMod 2) →ₗ[ZMod 2] (Fin qs.length → ZMod 2) :=
  LinearMap.pi fun i => linearPart (qs.get i).1

private theorem cosetOfFits [Fintype V] (qs : List (Af V × Bool)) {origin : V → ZMod 2}
    (atOrigin : fits origin qs) (x : V → ZMod 2) :
    fits x qs ↔ x - origin ∈ LinearMap.ker (constraintMap qs) := by
  rw [LinearMap.mem_ker, funext_iff]
  constructor
  · intro holds i
    change linearPart (qs.get i).1 (x-origin) = 0
    have here := List.get_mem qs i
    rw [← diffAffine, holds _ here, atOrigin _ here, sub_self]
  · intro holds q mem
    obtain ⟨i, eq⟩ := List.mem_iff_get.mp mem
    subst q
    have vanish : linearPart (qs.get i).1 (x-origin) = 0 := holds i
    rw [← diffAffine] at vanish
    exact (sub_eq_zero.mp vanish).trans (atOrigin _ (List.get_mem qs i))

private theorem rankConstraints [Fintype V] (qs : List (Af V × Bool)) :
    Module.finrank (ZMod 2) ((V → ZMod 2) ⧸ LinearMap.ker (constraintMap qs)) ≤ qs.length := by
  have codim := (LinearMap.ker (constraintMap qs)).finrank_quotient_add_finrank
  have rankNull := (constraintMap qs).finrank_range_add_finrank_ker
  have rangeLe := Submodule.finrank_le (LinearMap.range (constraintMap qs))
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at rangeLe
  omega

noncomputable def affineInputs [DecidableEq V] {n : ℕ} (order : Fin n → V) : List (Af V) :=
  [0, ((0 : V → ZMod 2), (1 : ZMod 2))] ++
    List.ofFn (fun i : Fin n => ((Pi.single (order i) (1 : ZMod 2) : V → ZMod 2), (0 : ZMod 2)))

def concreteInputs {n : ℕ} (order : Fin n → V) (x : V → ZMod 2) : List Bool :=
  [false,true] ++ List.ofFn (fun i : Fin n => decide (x (order i) = 1))

def message {n b : ℕ} (H : Circuit) (order : Fin n → V) (pick : Fin b → ℕ) (x : V → ZMod 2) :
    Fin b → ZMod 2 := fun j => ((H.wires (concreteInputs order x)).getD (pick j) false).toNat

/-- Split a circuit into affine cells by the first-input bits at its AND
and OR gates. Within a cell the selected output wires form an affine map. -/
theorem circuitPartition [Fintype V] [DecidableEq V] {n b : ℕ} (H : Circuit)
    (shape : ∀ g ∈ H.gates, Shape g) (order : Fin n → V) (pick : Fin b → ℕ) :
    ∃ (cells : Finset (Fin (nl H.gates) → Bool))
      (origin : (Fin (nl H.gates) → Bool) → V → ZMod 2)
      (U : (Fin (nl H.gates) → Bool) → Submodule (ZMod 2) (V → ZMod 2))
      (M : (Fin (nl H.gates) → Bool) → (V → ZMod 2) →ₗ[ZMod 2] (Fin b → ZMod 2)),
      (∀ i ∈ cells, Module.finrank (ZMod 2) ((V → ZMod 2) ⧸ U i) ≤ nl H.gates) ∧
      (∀ x, ∃! i : {j // j ∈ cells}, x - origin i.val ∈ U i.val) ∧
      ∀ i ∈ cells, ∀ x, x - origin i ∈ U i →
        message H order pick x = message H order pick (origin i) + M i (x - origin i) := by
  classical
  let J := Fin (nl H.gates) → Bool
  let run (i : J) := specialize H.gates (affineInputs order) (List.ofFn i)
  let cells := (Finset.univ : Finset J).filter fun i => ∃ x, fits x (run i).2
  have chooseOrigin (i : J) : ∃ origin, i ∈ cells → fits origin (run i).2 := by
    by_cases mem : i ∈ cells
    · obtain ⟨x, ok⟩ := (Finset.mem_filter.mp mem).2
      exact ⟨x, fun _ => ok⟩
    · exact ⟨0, fun bad => (mem bad).elim⟩
  choose origin atOrigin using chooseOrigin
  let U (i : J) := LinearMap.ker (constraintMap (run i).2)
  let form (i : J) (j : Fin b) := (run i).1.getD (pick j) 0
  let M (i : J) : (V → ZMod 2) →ₗ[ZMod 2] (Fin b → ZMod 2) :=
    LinearMap.pi fun j => linearPart (form i j)
  have fitsOrigin (i : J) (hi : i ∈ cells) (x : V → ZMod 2) :
      fits x (run i).2 ↔ x - origin i ∈ U i := cosetOfFits _ (atOrigin i hi) x
  have runSound (i : J) (x : V → ZMod 2) :
      (fits x (run i).2 ↔ concreteTrace H.gates (concreteInputs order x) = List.ofFn i) ∧
        (fits x (run i).2 → Agree (run i).1 (H.wires (concreteInputs order x)) x) :=
    specializationCorrect x H.gates _ _ _ shape (init_agree n order x) List.length_ofFn
  refine ⟨cells, origin, U, M, ?_, ?_, ?_⟩
  · intro i _
    exact (rankConstraints (run i).2).trans_eq (specializationLength _ _ _)
  · intro x
    let trace := concreteTrace H.gates (concreteInputs order x)
    have len : trace.length = nl H.gates := traceLength _ _
    let i : J := fun k => trace.get (Fin.cast len.symm k)
    have traceEq : trace = List.ofFn i := by
      apply List.ext_getElem (len.trans (List.length_ofFn (f := i)).symm)
      intro k hk hki
      simp [i, List.getElem_ofFn]
    have inTrace (j : J) : fits x (run j).2 ↔ trace = List.ofFn j := (runSound j x).1
    have hi : i ∈ cells := Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, (inTrace i).mpr traceEq⟩
    refine ⟨⟨i, hi⟩, (fitsOrigin i hi x).mp ((inTrace i).mpr traceEq), ?_⟩
    intro j hj
    exact Subtype.ext (List.ofFn_injective (((inTrace j.val).mp ((fitsOrigin j.val j.property x).mpr hj)).symm.trans traceEq))
  · intro i hi x hx
    have agreed := (runSound i x).2 ((fitsOrigin i hi x).mpr hx)
    have atBase := (runSound i (origin i)).2 (atOrigin i hi)
    funext j
    have lhs := agreed.2 (pick j)
    have rhs := atBase.2 (pick j)
    change av (form i j) x = message H order pick x j at lhs
    change av (form i j) (origin i) = message H order pick (origin i) j at rhs
    have relation := diffAffine (form i j) x (origin i)
    change message H order pick x j = message H order pick (origin i) j + linearPart (form i j) (x - origin i)
    rw [← lhs, ← rhs]
    exact sub_eq_iff_eq_add.mp relation |>.trans (add_comm _ _)

end ClauseSearchCircuitCells

namespace ClauseSearchAffineMass

open Finset

-- Adapted from the fiber mass proof and coordinate-basis bound in L-pcx-406.
variable {V : Type} [Fintype V] [DecidableEq V] {r : ℕ}

def unit (v : V) : V → ZMod 2 := fun u => if u = v then (1 : ZMod 2) else 0

def wt (x : V → ZMod 2) : ℕ := (univ.filter (fun v : V => x v ≠ 0)).card

noncomputable def len (H : (V → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) (s : Fin r → ZMod 2) : ℕ :=
  sInf {k : ℕ | ∃ x : V → ZMod 2, H x = s ∧ wt x = k}

lemma z2 (a : ZMod 2) (h : a ≠ 0) : a = 1 := by
  revert a h; decide

lemma add_self' {W : Type} (x : W → ZMod 2) : x + x = 0 := by
  funext v
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize x v = a
  revert a; decide

omit [DecidableEq V] in
lemma len_le (H : (V → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) {x : V → ZMod 2} {s : Fin r → ZMod 2}
    (hx : H x = s) : len H s ≤ wt x :=
  Nat.sInf_le ⟨x, hx, rfl⟩

omit [DecidableEq V] in
lemma len_spec (H : (V → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) (hH : Function.Surjective H)
    (s : Fin r → ZMod 2) : ∃ x, H x = s ∧ wt x = len H s := by
  obtain ⟨x, hx⟩ := hH s
  exact Nat.sInf_mem (s := {k : ℕ | ∃ x : V → ZMod 2, H x = s ∧ wt x = k}) ⟨_, x, hx, rfl⟩

lemma eq_sum_unit (w : V → ZMod 2) : w = ∑ v ∈ univ.filter (fun v : V => w v ≠ 0), unit v := by
  funext u
  simp only [Finset.sum_apply, unit, Finset.sum_ite_eq, mem_filter, mem_univ, true_and]
  by_cases h : w u = 0
  · simp [h]
  · simp [z2 _ h]

omit [Fintype V] in
lemma chain (R : ℝ) (hR : 0 ≤ R) (μ : (V → ZMod 2) → ℝ) (_hμ0 : ∀ x, 0 ≤ μ x)
    (hμ : ∀ x v, μ x ≤ R * μ (x + unit v)) (S : Finset V) :
    ∀ z, μ z ≤ R ^ S.card * μ (z + ∑ v ∈ S, unit v) := by
  induction S using Finset.induction_on with
  | empty => intro z; simp
  | insert a S ha ih =>
    intro z
    rw [Finset.sum_insert ha, card_insert_of_notMem ha]
    calc μ z ≤ R ^ S.card * μ (z + ∑ v ∈ S, unit v) := ih z
      _ ≤ R ^ S.card * (R * μ (z + ∑ v ∈ S, unit v + unit a)) :=
          mul_le_mul_of_nonneg_left (hμ _ _) (pow_nonneg hR _)
      _ = R ^ (S.card + 1) * μ (z + (unit a + ∑ v ∈ S, unit v)) := by
          rw [pow_succ, mul_assoc, add_comm (unit a), ← add_assoc]

lemma chain' (R : ℝ) (hR : 0 ≤ R) (μ : (V → ZMod 2) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
    (hμ : ∀ x v, μ x ≤ R * μ (x + unit v)) (w z : V → ZMod 2) :
    μ z ≤ R ^ wt w * μ (z + w) := by
  have := chain R hR μ hμ0 hμ (univ.filter (fun v : V => w v ≠ 0)) z
  rwa [← eq_sum_unit w] at this

lemma translate {M : Type} [AddCommMonoid M] (H : (V → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (y s xs : _) (hxs : H xs = s) (f : (V → ZMod 2) → M) :
    ∑ x ∈ univ.filter (fun x => H x = y), f (x + xs) = ∑ x ∈ univ.filter (fun x => H x + y = s), f x := by
  apply Finset.sum_nbij' (fun x => x + xs) (fun x => x + xs)
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    rw [map_add, hx, hxs, add_right_comm, add_self', zero_add]
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    have : H x = s + y := by rw [← hx, add_assoc, add_self', add_zero]
    rw [map_add, this, hxs, add_right_comm, add_self', zero_add]
  · intro x _; simp only [add_assoc, add_self', add_zero]
  · intro x _; simp only [add_assoc, add_self', add_zero]
  · intro x _; rfl

lemma part3 (H : (V → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) (hH : Function.Surjective H)
    (R : ℕ) (y : Fin r → ZMod 2) (μ : (V → ZMod 2) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
    (hμ : ∀ x v, μ x ≤ (R : ℝ) * μ (x + unit v)) :
    (∑ x, μ x) ≤ ((∑ s : Fin r → ZMod 2, R ^ (len H s) : ℕ) : ℝ) *
      ∑ x ∈ univ.filter (fun x => H x = y), μ x := by
  rw [← Finset.sum_fiberwise univ (fun x => H x + y) μ]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro s _
  obtain ⟨xs, hxs, hw⟩ := len_spec H hH s
  rw [← translate H y s xs hxs μ, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  have := chain' (R : ℝ) (Nat.cast_nonneg R) μ hμ0 hμ xs (x + xs)
  rwa [add_assoc, add_self', add_zero, hw] at this

lemma sum_pow_wt (κ : Type) [Fintype κ] [DecidableEq κ] (R : ℕ) :
    ∑ T : κ → ZMod 2, R ^ (univ.filter (fun k => T k ≠ 0)).card = (R + 1) ^ Fintype.card κ := by
  have h1 : ∀ T : κ → ZMod 2, R ^ (univ.filter (fun k => T k ≠ 0)).card =
      ∏ k, (if T k ≠ 0 then R else 1) := by
    intro T
    rw [Finset.prod_ite, prod_const, prod_const_one, mul_one]
  simp_rw [h1]
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun _ : κ => (univ : Finset (ZMod 2))) (fun _ t => if t ≠ 0 then R else 1)]
  have h2 : ∑ t : ZMod 2, (if t ≠ 0 then R else 1) = R + 1 := by
    show ∑ t : Fin 2, (if t ≠ 0 then R else 1) = R + 1
    rw [Fin.sum_univ_two]; simp [add_comm]
  simp only [h2, prod_const, card_univ]

lemma x_sum_unit (x : V → ZMod 2) : x = ∑ v, x v • unit v := by
  funext u
  simp [Finset.sum_apply, unit]

lemma span_top (H : (V → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) (hH : Function.Surjective H) :
    Submodule.span (ZMod 2) (Set.range (fun v => H (unit v))) = ⊤ := by
  rw [eq_top_iff]
  intro s _
  obtain ⟨x, rfl⟩ := hH s
  rw [x_sum_unit x, map_sum]
  exact Submodule.sum_mem _ fun v _ => by
    rw [map_smul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, rfl⟩)

lemma basis_setup (H : (V → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) (hH : Function.Surjective H) :
    ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (a : κ → V) (b : Module.Basis κ (ZMod 2) (Fin r → ZMod 2)),
      Function.Injective a ∧ (∀ k, b k = H (unit (a k))) ∧ Fintype.card κ = r := by
  classical
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' (ZMod 2) (fun v => H (unit v))
  have : Finite κ := Finite.of_injective a ha
  let _ : Fintype κ := Fintype.ofFinite κ
  have htop : ⊤ ≤ Submodule.span (ZMod 2) (Set.range ((fun v => H (unit v)) ∘ a)) := by
    rw [hsp, span_top H hH]
  let b := Module.Basis.mk hli htop
  refine ⟨κ, inferInstance, inferInstance, a, b, ha, fun k => by simp [b], ?_⟩
  have := Module.finrank_eq_card_basis b
  simpa using this.symm

lemma len_basis_le (H : (V → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) {κ : Type} [Fintype κ] [DecidableEq κ]
    (a : κ → V) (b : Module.Basis κ (ZMod 2) (Fin r → ZMod 2)) (_ha : Function.Injective a)
    (hb : ∀ k, b k = H (unit (a k))) (T : κ → ZMod 2) :
    len H (b.equivFun.symm T) ≤ (univ.filter (fun k => T k ≠ 0)).card := by
  let x : V → ZMod 2 := ∑ k, T k • unit (a k)
  have hx : H x = b.equivFun.symm T := by
    simp [x, map_sum, map_smul, Module.Basis.equivFun_symm_apply, hb]
  refine (len_le H hx).trans ?_
  unfold wt
  calc (univ.filter (fun v => x v ≠ 0)).card ≤ ((univ.filter (fun k => T k ≠ 0)).image a).card := by
        apply card_le_card
        intro v hv
        rw [mem_filter] at hv
        have hv2 := hv.2
        simp only [x, Finset.sum_apply, Pi.smul_apply, unit, smul_eq_mul, mul_ite, mul_one, mul_zero] at hv2
        obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv2
        rw [mem_image]
        refine ⟨k, ?_, ?_⟩
        · rw [mem_filter]; refine ⟨mem_univ _, ?_⟩
          intro h0; apply hk; simp [h0]
        · by_contra hne; apply hk; simp [Ne.symm hne]
    _ ≤ _ := card_image_le

private theorem weightBound (H : (V → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (surj : Function.Surjective H) (R : ℕ) (ratio : 1 ≤ R) :
    (∑ s : Fin r → ZMod 2, R ^ len H s) ≤ (R+1)^r := by
  classical
  obtain ⟨κ, _, _, a, b, injective, basis, card⟩ := basis_setup H surj
  have left : (∑ s : Fin r → ZMod 2, R ^ len H s) = ∑ t : κ → ZMod 2, R ^ len H (b.equivFun.symm t) :=
    (Equiv.sum_comp b.equivFun.symm.toEquiv (fun s => R ^ len H s)).symm
  have right : (R+1)^r = ∑ t : κ → ZMod 2, R^(univ.filter (fun k => t k ≠ 0)).card := by
    rw [sum_pow_wt, card]
  rw [left, right]
  exact Finset.sum_le_sum fun t _ => Nat.pow_le_pow_right ratio (len_basis_le H a b injective basis t)

noncomputable def coset (U : Submodule (ZMod 2) (V → ZMod 2)) (origin : V → ZMod 2) :
    Finset (V → ZMod 2) := by
  classical
  exact univ.filter (fun x => x-origin ∈ U)

/-- A translated submodule of codimension r has at least (R+1)^(-r)
of the mass of any smooth source on the Boolean cube. -/
theorem cosetMass (U : Submodule (ZMod 2) (V → ZMod 2)) (origin : V → ZMod 2)
    (R : ℕ) (ratio : 1 ≤ R) (μ : (V → ZMod 2) → ℝ) (nonnegative : ∀ x, 0 ≤ μ x)
    (smooth : ∀ x v, μ x ≤ (R : ℝ) * μ (x + unit v)) :
    (∑ x, μ x) ≤ ((R : ℝ)+1)^Module.finrank (ZMod 2) ((V → ZMod 2) ⧸ U) *
      ∑ x ∈ coset U origin, μ x := by
  classical
  let B := Module.finBasis (ZMod 2) ((V → ZMod 2) ⧸ U)
  let H := B.equivFun.toLinearMap.comp U.mkQ
  have surj : Function.Surjective H := B.equivFun.surjective.comp U.mkQ_surjective
  have eqFiber : univ.filter (fun x => H x = H origin) = coset U origin := by
    ext x
    simp only [coset, Finset.mem_filter, Finset.mem_univ, true_and]
    have quotient : U.mkQ x = U.mkQ origin ↔ x-origin ∈ U := by
      rw [← sub_eq_zero, ← map_sub]
      exact Submodule.Quotient.mk_eq_zero U
    exact B.equivFun.injective.eq_iff.trans quotient
  have capped := weightBound H surj R ratio
  have factor : ((∑ s, R^len H s : ℕ) : ℝ) ≤ ((R : ℝ)+1)^Module.finrank (ZMod 2) ((V → ZMod 2) ⧸ U) := by
    exact_mod_cast capped
  have mass := part3 H surj R (H origin) μ nonnegative smooth
  rw [eqFiber] at mass
  exact mass.trans (mul_le_mul_of_nonneg_right factor (Finset.sum_nonneg (fun x _ => nonnegative x)))

def asBools (z : V → ZMod 2) : V → Bool := fun v => decide (z v = 1)

def asField (x : V → Bool) : V → ZMod 2 := fun v => (x v).toNat

def boolEquiv : (V → ZMod 2) ≃ (V → Bool) where
  toFun := asBools
  invFun := asField
  left_inv z := funext fun v => by
    change ((decide (z v=1)).toNat : ZMod 2) = z v
    generalize z v = a
    revert a
    decide
  right_inv x := funext fun v => by
    change decide (((x v).toNat : ZMod 2) = 1) = x v
    generalize x v = b
    revert b
    decide

omit [Fintype V] in
private theorem translateFlip (z : V → ZMod 2) (v : V) :
    asBools (z + unit v) = Function.update (asBools z) v (!(asBools z v)) := by
  funext w
  by_cases eq : w = v
  · subst w
    simp only [asBools, unit, Pi.add_apply, ite_true, Function.update_self]
    generalize z v = a
    revert a
    decide
  · simp [asBools, unit, eq, Function.update_of_ne]

/-- If an entire affine coset is bad, its codimension bounds the accuracy
exponent on every source with the stipulated neighboring mass ratios. -/
theorem accuracyLeCodimension (U : Submodule (ZMod 2) (V → ZMod 2)) (origin : V → ZMod 2)
    (R h : ℕ) (ratio : 1 ≤ R) (μ : (V → Bool) → ℝ) (nonnegative : ∀ x, 0 ≤ μ x)
    (positive : 0 < ∑ x, μ x) (smooth : ∀ x v, μ x ≤ (R : ℝ) * μ (Function.update x v (!(x v))))
    (bad : Finset (V → Bool)) (includes : ∀ x, x-origin ∈ U → asBools x ∈ bad)
    (accurate : (2 : ℝ)^h * (∑ x ∈ bad, μ x) ≤ ∑ x, μ x) :
    h ≤ Nat.clog 2 (R+1) * Module.finrank (ZMod 2) ((V → ZMod 2) ⧸ U) := by
  classical
  let region := coset U origin
  let codim := Module.finrank (ZMod 2) ((V → ZMod 2) ⧸ U)
  have mass := cosetMass U origin R ratio (μ ∘ asBools) (fun x => nonnegative (asBools x)) (by
    intro x v
    simpa only [Function.comp_apply, translateFlip] using smooth (asBools x) v)
  change (∑ x, μ (boolEquiv x)) ≤ ((R : ℝ)+1)^codim * (∑ x ∈ region, μ (asBools x)) at mass
  rw [Equiv.sum_comp boolEquiv μ] at mass
  have subset : region.image asBools ⊆ bad := by
    rintro _ mem
    obtain ⟨x, here, rfl⟩ := Finset.mem_image.mp mem
    exact includes x (by simpa [region, coset] using here)
  have compares : (∑ x ∈ region, μ (asBools x)) ≤ ∑ x ∈ bad, μ x := by
    have more := Finset.sum_le_sum_of_subset_of_nonneg (f := μ) subset (fun x _ _ => nonnegative x)
    have injective : Function.Injective (asBools : (V → ZMod 2) → (V → Bool)) := boolEquiv.injective
    rwa [Finset.sum_image (fun _ _ _ _ eq => injective eq)] at more
  have bound : (∑ x, μ x) ≤ ((R : ℝ)+1)^codim * (∑ x ∈ bad, μ x) :=
    mass.trans (mul_le_mul_of_nonneg_left compares (by positivity))
  have massPositive : 0 < ∑ x ∈ bad, μ x := by
    by_contra! nonpos
    exact (not_le_of_gt positive) (bound.trans (mul_nonpos_of_nonneg_of_nonpos (by positivity) nonpos))
  have exp : (2 : ℝ)^h ≤ ((R : ℝ)+1)^codim :=
    le_of_mul_le_mul_right (accurate.trans bound) massPositive
  have factor : ((R : ℝ)+1) ≤ (2 : ℝ)^Nat.clog 2 (R+1) := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) (R+1)
  have lifted : (2 : ℝ)^h ≤ (2 : ℝ)^(Nat.clog 2 (R+1) * codim) := by
    rw [pow_mul]
    exact exp.trans (pow_le_pow_left₀ (by positivity) factor _)
  exact (pow_le_pow_iff_right₀ (by norm_num : 1 < (2 : ℝ))).mp lifted

end ClauseSearchAffineMass

namespace ClauseSearchLower

open PEqualNP.CircuitLowerBounds PEqualNP.ProofComplexity
open ClauseSearchCircuitCells ClauseSearchAffineMass

variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable def flat {b : ℕ} (S : Finset (Fin b → ZMod 2)) : ℕ :=
  sSup {d : ℕ | ∃ (U : Submodule (ZMod 2) (Fin b → ZMod 2)) (y : Fin b → ZMod 2),
    Module.finrank (ZMod 2) U = d ∧ ∀ u ∈ U, y + u ∈ S}

omit [Fintype V] [DecidableEq V] in
private theorem codeRank {b : ℕ} (S : Finset (Fin b → ZMod 2))
    (U : Submodule (ZMod 2) (V → ZMod 2)) (M : (V → ZMod 2) →ₗ[ZMod 2] (Fin b → ZMod 2))
    (y : Fin b → ZMod 2) (valid : ∀ u ∈ U, y + M u ∈ S) :
    Module.finrank (ZMod 2) (LinearMap.range (M.comp U.subtype)) ≤ flat S := by
  have bdd : BddAbove {d : ℕ | ∃ (W : Submodule (ZMod 2) (Fin b → ZMod 2)) (a : Fin b → ZMod 2),
      Module.finrank (ZMod 2) W = d ∧ ∀ u ∈ W, a + u ∈ S} := by
    refine ⟨b, ?_⟩
    rintro d ⟨W, _, rfl, _⟩
    simpa using Submodule.finrank_le W
  apply le_csSup bdd
  refine ⟨LinearMap.range (M.comp U.subtype), y, rfl, ?_⟩
  intro u hu
  obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hu
  exact valid v.val v.property

/-- The combined nonlinear, message-flat, and maximum-list budget controls
the accuracy exponent whenever the underlying CNF has the specified PC
degree lower bound. -/
theorem accuracyLeNonlinearBudget {n b : ℕ} (F : Set (Clause V)) (H : Circuit)
    (shape : ∀ g ∈ H.gates, Shape g) (order : Fin n → V) (pick : Fin b → ℕ) (T w : ℕ)
    (nonlinear : nl H.gates ≤ T) (S : Finset (Fin b → ZMod 2))
    (out : (Fin b → ZMod 2) → Finset (Clause V)) (cap : (Fin b → ZMod 2) → ℕ)
    (allowed : ∀ x, message H order pick x ∈ S)
    (lists : ∀ y ∈ S, (out y).card ≤ cap y ∧ ∀ cl ∈ out y, cl ∈ F ∧ cl.card ≤ w)
    (noRefutation : ¬ PCRefutable (cnfSystem F) (T + flat S + w * S.sup cap))
    (R h : ℕ) (ratio : 1 ≤ R) (μ : (V → Bool) → ℝ) (nonnegative : ∀ x, 0 ≤ μ x)
    (positive : 0 < ∑ x, μ x) (smooth : ∀ x v, μ x ≤ (R : ℝ) * μ (Function.update x v (!(x v))))
    (bad : Finset (V → Bool))
    (includes : ∀ x, (∀ cl ∈ out (message H order pick x), ClauseSat (asBools x) cl) → asBools x ∈ bad)
    (accurate : (2 : ℝ)^h * (∑ x ∈ bad, μ x) ≤ ∑ x, μ x) :
    h ≤ Nat.clog 2 (R+1) * (T + flat S + S.sup cap) := by
  classical
  obtain ⟨cells, origin, U, M, codim, partition, agrees⟩ := circuitPartition H shape order pick
  let offset i := message H order pick (origin i)
  let word i (x : V → ZMod 2) := offset i + M i (x-origin i)
  have rank (i) (hi : i ∈ cells) :
      Module.finrank (ZMod 2) (LinearMap.range ((M i).comp (U i).subtype)) ≤ flat S := by
    apply codeRank S (U i) (M i) (offset i)
    intro u hu
    have identity : origin i + u - origin i = u := by abel
    have fromCircuit := agrees i hi (origin i + u) (by rwa [identity])
    rw [identity] at fromCircuit
    rw [← fromCircuit]
    exact allowed _
  have codeAllowed i (hi : i ∈ cells) x (hx : x-origin i ∈ U i) : word i x ∈ S := by
    have eq : message H order pick x = word i x := agrees i hi x hx
    exact eq ▸ allowed x
  have width i (hi : i ∈ cells) x (hx : x-origin i ∈ U i) :
      ∀ cl ∈ out (word i x), cl ∈ F ∧ cl.card ≤ w := (lists _ (codeAllowed i hi x hx)).2
  have capacity i (hi : i ∈ cells) x (hx : x-origin i ∈ U i) : (out (word i x)).card ≤ S.sup cap :=
    (lists _ (codeAllowed i hi x hx)).1.trans (Finset.le_sup (codeAllowed i hi x hx))
  have fails : ¬ (∀ i ∈ cells, ∀ x, x-origin i ∈ U i →
      ∃ cl ∈ out (word i x), ¬ ClauseSat (asBools x) cl) := fun exactSearch =>
    noRefutation (ClauseSearchPC.refuteFromPiecewiseMessages F cells origin U offset M out
      T (flat S) w (S.sup cap) (fun i hi => (codim i hi).trans nonlinear) rank partition
        width capacity exactSearch)
  push Not at fails
  obtain ⟨i, hi, x, hx, sat⟩ := fails
  obtain ⟨W, dimension, staysBad⟩ :=
    ClauseSearchPC.cosetAroundFailure (origin i) x (U i) (M i) (out (word i x)) hx sat
  have allBad (z : V → ZMod 2) (hz : z-x ∈ W) : asBools z ∈ bad := by
    obtain ⟨inCell, wordSame, sat⟩ := staysBad z hz
    apply includes z
    rw [agrees i hi z inCell, wordSame]
    exact sat
  have estimate := accuracyLeCodimension W x R h ratio μ nonnegative positive smooth bad allBad accurate
  refine estimate.trans (Nat.mul_le_mul_left _ (dimension.trans ?_))
  exact Nat.add_le_add (Nat.add_le_add ((codim i hi).trans nonlinear) (rank i hi)) (capacity i hi x hx)

omit [Fintype V] [DecidableEq V] in
private theorem satisfiableSmallList (F : Set (Clause V)) (clauses : Finset (Clause V)) (w : ℕ)
    (width : ∀ cl ∈ clauses, cl ∈ F ∧ cl.card ≤ w)
    (noRefutation : ¬ PCRefutable (cnfSystem F) (w * clauses.card)) :
    ∃ x : V → Bool, ∀ cl ∈ clauses, ClauseSat x cl := by
  classical
  by_contra no
  have refuted := ClauseSearchPC.refuteFromIndicators F ({()} : Finset Unit)
    (fun _ => (1 : ClauseSearchPC.Poly V)) (fun _ => clauses) 0 w clauses.card
    (by simp) (fun _ _ => width) (fun _ _ => le_rfl) (by simp) (by
      intro _ _ x _
      have noInput : ¬ ∀ cl ∈ clauses, ClauseSat (asBools x) cl := fun yes => no ⟨_, yes⟩
      push Not at noInput
      obtain ⟨cl, mem, failed⟩ := noInput
      exact ⟨cl, mem, (ClauseSearchPC.clauseFalse cl x).mpr failed⟩)
  exact noRefutation (by simpa using refuted)

/-- Both list budgets give the lower half of the search tradeoff whenever
the CNF is known to have sufficiently high PC degree at small budgets. -/
theorem accuracyLeMinimumBudget {n b : ℕ} (F : Set (Clause V)) (H : Circuit)
    (shape : ∀ g ∈ H.gates, Shape g) (order : Fin n → V) (pick : Fin b → ℕ) (T w C size : ℕ)
    (widthPositive : 1 ≤ w) (constantPositive : 1 ≤ C) (nonlinear : nl H.gates ≤ T)
    (S : Finset (Fin b → ZMod 2)) (out : (Fin b → ZMod 2) → Finset (Clause V))
    (cap : (Fin b → ZMod 2) → ℕ) (allowed : ∀ x, message H order pick x ∈ S)
    (lists : ∀ y ∈ S, (out y).card ≤ cap y ∧ ∀ cl ∈ out y, cl ∈ F ∧ cl.card ≤ w)
    (degree : ∀ B, C*B < size → ¬ PCRefutable (cnfSystem F) (w*B))
    (R h : ℕ) (ratio : 1 ≤ R) (μ : (V → Bool) → ℝ) (nonnegative : ∀ x, 0 ≤ μ x)
    (positive : 0 < ∑ x, μ x) (smooth : ∀ x v, μ x ≤ (R : ℝ) * μ (Function.update x v (!(x v))))
    (bad : Finset (V → Bool))
    (includes : ∀ x, (∀ cl ∈ out (message H order pick (asField x)), ClauseSat x cl) → x ∈ bad)
    (accurate : (2 : ℝ)^h * (∑ x ∈ bad, μ x) ≤ ∑ x, μ x) :
    min (size * Nat.clog 2 (R+1)) h ≤ C * Nat.clog 2 (R+1) *
      min (∑ y ∈ S, cap y) (T + S.sup cap + flat S) := by
  classical
  let raw := ∑ y ∈ S, cap y
  let controlled := T + S.sup cap + flat S
  let B := min raw controlled
  let L := Nat.clog 2 (R+1)
  change min (size * L) h ≤ C * L * B
  by_cases large : size ≤ C * B
  · calc
      _ ≤ size * L := min_le_left _ _
      _ ≤ (C*B)*L := Nat.mul_le_mul_right _ large
      _ = _ := by ring
  have limited := degree B (Nat.lt_of_not_ge large)
  have hBudget : h ≤ L * B := by
    by_cases rawSmaller : raw ≤ controlled
    · have swap : B = raw := min_eq_left rawSmaller
      rw [swap] at limited ⊢
      let clauses := S.biUnion out
      have clauseWidth cl (mem : cl ∈ clauses) : cl ∈ F ∧ cl.card ≤ w := by
        obtain ⟨y, hy, hit⟩ := Finset.mem_biUnion.mp mem
        exact (lists y hy).2 cl hit
      have count : clauses.card ≤ raw := Finset.card_biUnion_le.trans
        (Finset.sum_le_sum (fun y hy => (lists y hy).1))
      have noList : ¬ PCRefutable (cnfSystem F) (w*clauses.card) := fun ref =>
        limited (ClauseSearchPC.Toolkit.pcDerivable_mono ref (Nat.mul_le_mul_left w count) subset_rfl)
      obtain ⟨x, sat⟩ := satisfiableSmallList F clauses w clauseWidth noList
      have allBad y (holds : ∀ cl ∈ clauses, ClauseSat y cl) : y ∈ bad :=
        includes y (fun cl mem => holds cl (Finset.mem_biUnion.mpr ⟨_, allowed (asField y), mem⟩))
      have consistent : SmoothClauseSearch.Smooth μ R := ⟨nonnegative, positive, smooth⟩
      exact (SmoothClauseSearch.accuracyLeUnion μ R h consistent clauses x sat bad allBad accurate).trans
        (Nat.mul_le_mul_left _ count)
    · have swap : B = controlled := min_eq_right (le_of_not_ge rawSmaller)
      rw [swap] at limited ⊢
      have degreeBound : T + flat S + w * S.sup cap ≤ w * controlled := calc
        _ ≤ w*(T+flat S) + w*S.sup cap := Nat.add_le_add_right
          (by simpa using Nat.mul_le_mul_right (T+flat S) widthPositive) _
        _ = _ := by dsimp [controlled]; ring
      have noControlled : ¬ PCRefutable (cnfSystem F) (T + flat S + w*S.sup cap) := fun ref =>
        limited (ClauseSearchPC.Toolkit.pcDerivable_mono ref degreeBound subset_rfl)
      have allBad z (holds : ∀ cl ∈ out (message H order pick z), ClauseSat (asBools z) cl) :
          asBools z ∈ bad := by
        apply includes
        have roundTrip : asField (asBools z) = z := boolEquiv.left_inv z
        rwa [roundTrip]
      have bound := accuracyLeNonlinearBudget F H shape order pick T w nonlinear S out cap allowed lists
        noControlled R h ratio μ nonnegative positive smooth bad allBad accurate
      exact bound.trans (by dsimp [controlled, L]; rw [add_right_comm T (flat S)])
  calc
    _ ≤ h := min_le_right _ _
    _ ≤ L*B := hBudget
    _ ≤ C*(L*B) := by simpa using Nat.mul_le_mul_right (L*B) constantPositive
    _ = _ := by ring

end ClauseSearchLower

namespace ClauseSearchExpanderLower

open PEqualNP.Expanders PEqualNP.ProofComplexity PEqualNP.CircuitLowerBounds
open ClauseSearchCircuitCells ClauseSearchAffineMass

private theorem pigeonClauseWidth {m n : ℕ} (G : BipGraph m n) (i : Fin m) :
    ((Finset.univ : Finset (Literal (GEdge G))).filter
      (fun l => l.1.1.1 = i ∧ l.2 = true)).card = (G i).card := by
  classical
  let lit (j : G i) : Literal (GEdge G) := (⟨(i, j.val), j.property⟩, true)
  have injective : Function.Injective lit := by
    intro j k eq
    exact Subtype.ext (congrArg (fun l : Literal (GEdge G) => l.1.val.2) eq)
  have image : (Finset.univ : Finset (G i)).image lit =
      (Finset.univ : Finset (Literal (GEdge G))).filter (fun l => l.1.1.1 = i ∧ l.2 = true) := by
    ext l
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨rfl, rfl⟩
    · rcases l with ⟨⟨⟨p, j⟩, mem⟩, val⟩
      rintro ⟨(eq : p = i), (bit : val = true)⟩
      subst p
      subst val
      exact ⟨⟨j, mem⟩, rfl⟩
  rw [← image, Finset.card_image_of_injective _ injective, Finset.card_univ, Fintype.card_coe]

theorem clauseWidth {m n d : ℕ} (G : BipGraph m n) (degree : LeftDegLe G d)
    (cl : Clause (GEdge G)) (clause : cl ∈ funGraphPHP G) : cl.card ≤ max d 2 := by
  rcases clause with base | functional
  · rcases base with pigeon | hole
    · obtain ⟨i, rfl⟩ := pigeon
      rw [pigeonClauseWidth]
      exact (degree i).trans (le_max_left _ _)
    · obtain ⟨_, _, _, _, rfl⟩ := hole
      exact Finset.card_le_two.trans (le_max_right _ _)
  · obtain ⟨_, _, _, _, rfl⟩ := functional
    exact Finset.card_le_two.trans (le_max_right _ _)

private theorem nonlinearCount (H : Circuit) : nl H.gates = H.gates.countP
    (fun g => @decide (g.op = .and ∨ g.op = .or) (Classical.propDecidable _)) := by
  unfold nl
  congr 1
  funext g
  rcases g with ⟨op, args⟩
  cases op <;> simp [isNL]

private theorem messageAtBool {V : Type} {n b : ℕ} (H : Circuit) (order : Fin n → V)
    (pick : Fin b → ℕ) (x : V → Bool) (j : Fin b) :
    message H order pick (asField x) j =
      (((H.wires ([false,true] ++ List.ofFn (fun i : Fin n => x (order i)))).getD (pick j) false).toNat : ZMod 2) := by
  have points : (fun i : Fin n => decide (asField x (order i) = 1)) = fun i => x (order i) :=
    funext (fun i => congrFun (boolEquiv.right_inv x) (order i))
  have inputs : concreteInputs order (asField x) = [false,true] ++ List.ofFn (fun i : Fin n => x (order i)) := by
    unfold concreteInputs
    rw [points]
  unfold message
  rw [inputs]

theorem noRefutationOnSmallBudget {n d s₀ C : ℕ} (G : BipGraph (n+1) n)
    (small : 0 < s₀) (large : s₀ ≤ n)
    (expands : IsBdryExpander G (n/s₀) 2) (left : LeftDegLe G d)
    (scale : s₀*d*max d 2 ≤ C) (B : ℕ) (budget : C*B < n) :
    ¬ PCRefutable (cnfSystem (funGraphPHP G)) (max d 2 * B) := by
  have positive : 1 ≤ n/s₀ := (Nat.le_div_iff_mul_le small).mpr (by simpa using large)
  have cover : d * (max d 2 * B) ≤ n/s₀ := (Nat.le_div_iff_mul_le small).mpr (calc
    _ = (s₀*d*max d 2)*B := by ring
    _ ≤ C*B := Nat.mul_le_mul_right B scale
    _ ≤ n := budget.le)
  exact L049 _ _ G (n/s₀) d (max d 2*B) expands left positive cover

theorem deskLowerHalf : ∃ C n₀ : ℕ, 2 ≤ C ∧ ∀ n : ℕ, n₀ ≤ n →
  ∃ G : PEqualNP.Expanders.BipGraph (n+1) n,
    PEqualNP.Expanders.LeftDegLe G C ∧ PEqualNP.Expanders.RightDegLe G C ∧
    let V := PEqualNP.Expanders.GEdge G
    let X := V → Bool
    let e := Fintype.card V
    let F := PEqualNP.Expanders.funGraphPHP G
    ∀ (b T h R : ℕ) (S : Finset (Fin b → ZMod 2)) (cap : (Fin b → ZMod 2) → ℕ),
      1 ≤ R → S.Nonempty → (∀ y ∈ S, 1 ≤ cap y) →
      let Y := Fin b → ZMod 2
      let flat := sSup {k : ℕ | ∃ (U : Submodule (ZMod 2) Y) (y : Y),
        Module.finrank (ZMod 2) U = k ∧ ∀ u ∈ U, y + u ∈ S}
      let B := min (∑ y ∈ S, cap y) (T + S.sup cap + flat)
      let L := Nat.clog 2 (R+1)
      let smooth := fun μ : X → ℝ => (∀ x, 0 ≤ μ x) ∧ 0 < ∑ x, μ x ∧
        ∀ x v, μ x ≤ (R : ℝ) * μ (Function.update x v (!(x v)))
      let possible := fun (allSources : Bool) => ∃ (H : PEqualNP.CircuitLowerBounds.Circuit)
          (pick : Fin b → Fin (2+e+H.size)) (out : Y → Finset (PEqualNP.ProofComplexity.Clause V)),
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (2+e) H ∧
        (∀ g ∈ H.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
          g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)) ∧
        H.gates.countP (fun g => @decide (g.op = .and ∨ g.op = .or) (Classical.propDecidable _)) ≤ T ∧
        (∀ y ∈ S, (out y).card ≤ cap y ∧ ∀ cl ∈ out y, cl ∈ F) ∧
        let msg := fun (x : X) (j : Fin b) =>
          let ws := H.wires ([false,true] ++ List.ofFn (fun i : Fin e => x ((Fintype.equivFin V).symm i)))
          ((ws.getD (pick j).val false).toNat : ZMod 2)
        (∀ x : X, msg x ∈ S) ∧
        let bad := Finset.univ.filter (fun x : X =>
          @decide (∀ cl ∈ out (msg x), PEqualNP.ProofComplexity.ClauseSat x cl) (Classical.propDecidable _))
        let accurate := fun μ : X → ℝ => (2 : ℝ)^h * (∑ x ∈ bad, μ x) ≤ ∑ x, μ x
        if allSources then (∀ μ, smooth μ → accurate μ) else (∃ μ, smooth μ ∧ accurate μ)
      (possible false → min (n*L) h ≤ C*L*B) := by
  classical
  obtain ⟨d, s₀, n₀, positive, graphs⟩ := L043
  let w := max d 2
  let C := max w (s₀*d*w)
  have widthLe : w ≤ C := le_max_left _ _
  have dLe : d ≤ C := (le_max_left d 2).trans widthLe
  have cTwo : 2 ≤ C := (le_max_right d 2).trans widthLe
  refine ⟨C, max n₀ s₀, cTwo, ?_⟩
  intro n large
  have size := (le_max_right n₀ s₀).trans large
  obtain ⟨G, left, right, expands⟩ := graphs n ((le_max_left n₀ s₀).trans large)
  refine ⟨G, fun i => (left i).trans dLe, fun j => (right j).trans dLe, ?_⟩
  intro V X e F b T h R S cap ratio _ _ Y flat B L smooth possible
  rintro ⟨H, pick, out, _, shape, count, lists, valid, μ, props, accurate⟩
  let order : Fin e → V := (Fintype.equivFin V).symm
  let wires : Fin b → ℕ := fun j => (pick j).val
  let word (x : X) (j : Fin b) : ZMod 2 :=
    ((H.wires ([false,true] ++ List.ofFn (fun i : Fin e => x (order i)))).getD (wires j) false).toNat
  let bad : Finset X := Finset.univ.filter (fun x : X =>
    @decide (∀ cl ∈ out (word x), ClauseSat x cl) (Classical.propDecidable _))
  have sameWord (x : X) : message H order wires (asField x) = word x := by
    funext j
    exact messageAtBool H order wires x j
  have permitted (z : V → ZMod 2) : message H order wires z ∈ S := by
    have ok : word (asBools z) ∈ S := valid (asBools z)
    rw [← sameWord] at ok
    have roundTrip : asField (asBools z) = z := boolEquiv.left_inv z
    rwa [roundTrip] at ok
  have widths (y : Y) (hy : y ∈ S) :
      (out y).card ≤ cap y ∧ ∀ cl ∈ out y, cl ∈ F ∧ cl.card ≤ w := by
    refine ⟨(lists y hy).1, fun cl hit => ?_⟩
    exact ⟨(lists y hy).2 cl hit, clauseWidth G left cl ((lists y hy).2 cl hit)⟩
  have includeBad (x : X) (sat : ∀ cl ∈ out (message H order wires (asField x)), ClauseSat x cl) :
      x ∈ bad := by
    rw [sameWord] at sat
    simpa [bad] using sat
  have limited (B : ℕ) (budget : C*B < n) : ¬ PCRefutable (cnfSystem F) (w*B) :=
    noRefutationOnSmallBudget G positive size expands left (le_max_right _ _) B budget
  exact ClauseSearchLower.accuracyLeMinimumBudget F H shape order wires T w C n
    (by dsimp [w]; omega) (by omega) ((nonlinearCount H).trans_le count) S out cap permitted widths limited
    R h ratio μ props.1 props.2.1 props.2.2 bad includeBad accurate

end ClauseSearchExpanderLower

#print axioms ClauseSearchExpanderLower.deskLowerHalf
