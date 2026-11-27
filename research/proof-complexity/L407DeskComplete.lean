import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Data.Finsupp.Encodable
import PEqualNP.Defs
import Mathlib.FieldTheory.Finite.Polynomial

namespace PEqualNP.Outside.L_pcx_407

open PEqualNP.ProofComplexity

namespace PEqualNP.ProofComplexity.Helpers

open PEqualNP.Expanders

def permGraph {n b : ℕ} (σ : Fin b → Equiv.Perm (Fin (n + 1))) : BipGraph (n + 1) n :=
  fun i => Finset.univ.filter (fun j : Fin n => ∃ k, σ k i = j.castSucc)

def PermCountStmt : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (T Y : Finset α),
    (Finset.univ.filter (fun σ : Equiv.Perm α => ∀ x ∈ T, σ x ∈ Y)).card ≤
      Y.card.descFactorial T.card * (Fintype.card α - T.card).factorial

def ArithStmt : Prop :=
  ∃ s₀ n₀ : ℕ, 5 ≤ s₀ ∧ ∀ n : ℕ, n₀ ≤ n →
    ∑ t ∈ Finset.Icc 1 (n / s₀),
      ((n + 1).choose t : ℝ) * ((n + 1).choose (5 * t) : ℝ) *
        (((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ)) ^ 8 < 1

end PEqualNP.ProofComplexity.Helpers

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

  have ht : t.card ≤ Y.card.descFactorial T.card := by
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

  have hfib : ∀ g ∈ t, (S.filter fun σ => f σ = g).card ≤ (Fintype.card α - T.card).factorial := by
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
  calc S.card ≤ (Fintype.card α - T.card).factorial * t.card := this
    _ ≤ (Fintype.card α - T.card).factorial * Y.card.descFactorial T.card :=
        Nat.mul_le_mul_left _ ht
    _ = _ := Nat.mul_comm _ _

end PEqualNP.ProofComplexity.Helpers

namespace PEqualNP.ProofComplexity.Helpers

open Finset

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

namespace PEqualNP.ProofComplexity

theorem L043 : ∃ (b s₀ n₀ : ℕ), 0 < s₀ ∧ ∀ n : ℕ, n₀ ≤ n → ∃ G : PEqualNP.Expanders.BipGraph (n + 1) n, PEqualNP.Expanders.LeftDegLe G b ∧ PEqualNP.Expanders.RightDegLe G b ∧ PEqualNP.Expanders.IsBdryExpander G (n / s₀) 2 :=
  Helpers.expander_of_parts Helpers.permCount Helpers.arith
    (fun σ => Helpers.permGraph_leftDegLe σ) (fun σ => Helpers.permGraph_rightDegLe σ)
    (fun σ T hT hbad => Helpers.permGraph_trap σ T hT hbad)

end PEqualNP.ProofComplexity

namespace PEqualNP.ProofComplexity.Helpers

open MvPolynomial

variable {σ τ : Type}

theorem pcDerivable_mono {F F' : Set (MvPolynomial σ (ZMod 2))} {B B' : ℕ}
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F B p) (hB : B ≤ B') (hF : F ⊆ F') :
    PCDerivable F' B' p := by
  induction h with
  | ax hp hdeg => exact .ax (hF hp) (hdeg.trans hB)
  | zero => exact .zero
  | add _ _ ih1 ih2 => exact .add ih1 ih2
  | mulX j _ hdeg ih => exact .mulX j ih (hdeg.trans hB)

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
        rw [← mul_assoc, X, monomial_mul_monomial, one_mul, ← Finsupp.single_add, add_comm 1 n]
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

theorem pcDerivable_eval_eq_zero {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F B p) (a : σ → ZMod 2)
    (ha : ∀ f ∈ F, eval a f = 0) : eval a p = 0 := by
  induction h with
  | ax hp _ => exact ha _ hp
  | zero => simp
  | add _ _ ih1 ih2 => simp [ih1, ih2]
  | mulX j _ _ ih => simp [ih]

theorem pcRefutable_no_common_zero {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    (h : PCRefutable F B) : ¬ ∃ a : σ → ZMod 2, ∀ f ∈ F, eval a f = 0 := by
  rintro ⟨a, ha⟩
  have := pcDerivable_eval_eq_zero h a ha
  simp at this

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

theorem bitPHPSystem_no_common_zero {m l : ℕ} (hml : 2 ^ l < m) :
    ¬ ∃ a : Fin m × Fin l → ZMod 2, ∀ f ∈ bitPHPSystem m l, eval a f = 0 := by
  rintro ⟨a, ha⟩
  have := Fintype.card_le_of_injective _ (bitPHPSystem_injective a ha)
  simp at this
  omega

end PEqualNP.ProofComplexity.Helpers

namespace PEqualNP.ProofComplexity.Helpers

open MvPolynomial

theorem not_pcRefutable_of_pseudoReduction {σ : Type}
    {F : Set (MvPolynomial σ (ZMod 2))} {D : ℕ}
    (R : MvPolynomial σ (ZMod 2) →ₗ[ZMod 2] MvPolynomial σ (ZMod 2))
    (hax : ∀ f ∈ F, f.totalDegree ≤ D → R f = 0)
    (hmul : ∀ (v : σ) (a : σ →₀ ℕ), a.degree + 1 ≤ D →
      R (X v * monomial a 1) = R (X v * R (monomial a 1)))
    (hone : R 1 ≠ 0) :
    ¬ PCRefutable F D := by

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

namespace PEqualNP.ProofComplexity.Helpers

open MvPolynomial

section Static

variable {σ : Type}

noncomputable def staticSpan (F : Set (MvPolynomial σ (ZMod 2))) (k : ℕ) :
    Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) :=
  Submodule.span (ZMod 2)
    {q | ∃ (a : σ →₀ ℕ) (f : MvPolynomial σ (ZMod 2)),
      f ∈ F ∧ (monomial a 1 * f).totalDegree ≤ k ∧ q = monomial a 1 * f}

theorem monomial_one_mul_X (a : σ →₀ ℕ) (v : σ) :
    monomial a (1 : ZMod 2) * X v = monomial (a + Finsupp.single v 1) 1 := by
  rw [X, monomial_mul_monomial, mul_one]

theorem totalDegree_monomial_one (a : σ →₀ ℕ) :
    (monomial a (1 : ZMod 2)).totalDegree = a.degree := by
  rw [totalDegree_monomial _ one_ne_zero]
  rfl

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

theorem one_mem_staticSpan_zero {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    (hint : ∀ k < B, ∀ p, p ∈ staticSpan F (k + 1) → p.totalDegree ≤ k → p ∈ staticSpan F k)
    (h : (1 : MvPolynomial σ (ZMod 2)) ∈ staticSpan F B) :
    (1 : MvPolynomial σ (ZMod 2)) ∈ staticSpan F 0 := by
  induction B with
  | zero => exact h
  | succ k ih =>
    exact ih (fun k' hk' => hint k' (by omega)) (hint k (by omega) 1 h (by simp))

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

section Matching

variable {m N : ℕ}

def IsPartialMatching (T : Finset (Fin m × Fin N)) : Prop :=
  ∀ a ∈ T, ∀ b ∈ T, (a.1 = b.1 ∨ a.2 = b.2) → a = b

def MomentConsistent (m N k : ℕ) (z : Finset (Fin m × Fin N) → ZMod 2) : Prop :=
  ∀ T : Finset (Fin m × Fin N), IsPartialMatching T → T.card < k →
    ∀ i : Fin m, (∀ a ∈ T, a.1 ≠ i) →
      z T = ∑ j ∈ Finset.univ.filter (fun j : Fin N => ∀ a ∈ T, a.2 ≠ j), z (insert (i, j) T)

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

theorem not_isPartialMatching_insert {S : Finset (Fin m × Fin N)} {i : Fin m} {j j0 : Fin N}
    (h0 : (i, j0) ∈ S) (hj : j ≠ j0) : ¬ IsPartialMatching (insert (i, j) S) := by
  intro h
  have := h (i, j) (Finset.mem_insert_self _ _) (i, j0) (Finset.mem_insert_of_mem h0)
    (Or.inl rfl)
  exact hj (congrArg Prod.snd this)

open Classical in

noncomputable def momentWeight (z : Finset (Fin m × Fin N) → ZMod 2)
    (S : Finset (Fin m × Fin N)) : ZMod 2 :=
  if IsPartialMatching S then z S else 0

theorem momentWeight_of_not {z : Finset (Fin m × Fin N) → ZMod 2}
    {S : Finset (Fin m × Fin N)} (h : ¬ IsPartialMatching S) : momentWeight z S = 0 :=
  ite_eq_right h

theorem momentWeight_of_matching {z : Finset (Fin m × Fin N) → ZMod 2}
    {S : Finset (Fin m × Fin N)} (h : IsPartialMatching S) : momentWeight z S = z S :=
  ite_eq_left h

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

theorem not_momentExt_zero_of_no_holes (m : ℕ) (hm : 1 ≤ m) : ¬ MomentExt m 0 0 := by
  intro h
  obtain ⟨z', hz', hagree⟩ := h (fun _ => 1) (fun T _ hcard => by omega)
  have h1 := hz' ∅ isPartialMatching_empty (by simp) ⟨0, hm⟩ (by simp)
  rw [hagree ∅ isPartialMatching_empty (by simp)] at h1
  simp at h1

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

namespace PEqualNP.ProofComplexity.Helpers

open MvPolynomial

variable {σ : Type} [Countable σ]

noncomputable def monoKey (a : σ →₀ ℕ) : ℕ ×ₗ ℕ :=
  toLex (a.degree, Classical.choose (Countable.exists_injective_nat (σ →₀ ℕ)) a)

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

def IsStd (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (a : σ →₀ ℕ) : Prop :=
  monomial a (1 : ZMod 2) ∉ U ⊔ restrictSupport (ZMod 2) {b | MonoLt b a}

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

namespace PEqualNP.ProofComplexity.Helpers

open PEqualNP.Expanders

variable {m N : ℕ} (G : BipGraph m N)

def ContainedIn (s : ℕ) (H : Finset (Fin N)) (T : Finset (Fin m)) : Prop :=
  T.card ≤ s ∧ uniqueNbrs G T ⊆ H

open Classical in

noncomputable def supp (s : ℕ) (H : Finset (Fin N)) : Finset (Fin m) :=
  Finset.univ.filter (fun i => ∃ T, i ∈ T ∧ ContainedIn G s H T)

open Classical in
lemma mem_supp {s : ℕ} {H : Finset (Fin N)} {i : Fin m} :
    i ∈ supp G s H ↔ ∃ T, i ∈ T ∧ ContainedIn G s H T := by
  simp [supp]

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

namespace PEqualNP.ProofComplexity.Helpers

open MvPolynomial
open PEqualNP.Expanders

variable {m N : ℕ} (G : BipGraph m N)

def localSat (S : Finset (Fin m)) (α : GEdge G → ZMod 2) : Prop :=
  (∀ e e' : GEdge G, e.1.2 = e'.1.2 → e.1.1 ≠ e'.1.1 → α e * α e' = 0) ∧
  ∀ i ∈ S, ∃ e : GEdge G, e.1.1 = i ∧ α e = 1

noncomputable def locIdeal (S : Finset (Fin m)) :
    Submodule (ZMod 2) (MvPolynomial (GEdge G) (ZMod 2)) :=
  ⨅ (α : GEdge G → ZMod 2) (_ : localSat G S α),
    LinearMap.ker (MvPolynomial.aeval (R := ZMod 2) α).toLinearMap

theorem mem_locIdeal {S : Finset (Fin m)} {f : MvPolynomial (GEdge G) (ZMod 2)} :
    f ∈ locIdeal G S ↔ ∀ α, localSat G S α → eval α f = 0 := by
  simp only [locIdeal, Submodule.mem_iInf, LinearMap.mem_ker, AlgHom.toLinearMap_apply]
  rfl

def monoHoles (a : GEdge G →₀ ℕ) : Finset (Fin N) := a.support.image (fun e => e.1.2)

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

theorem localSat_clausePoly_pigeonClause (i : Fin m) :
    clausePoly (pigeonClause G i)
      = ∏ l ∈ pigeonClause G i, (1 + X l.1 : MvPolynomial (GEdge G) (ZMod 2)) := by
  rw [clausePoly]
  refine Finset.prod_congr rfl fun l hl => ?_
  have hl2 : l.2 = true := (Finset.mem_filter.mp hl).2.2
  simp only [hl2, ite_true]

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

namespace PEqualNP.ProofComplexity.Helpers

open MvPolynomial
open PEqualNP.Expanders

variable {m N : ℕ} (G : BipGraph m N)

theorem localNF_eval_bind₁ {σ : Type} (α : σ → ZMod 2) (φ : σ → MvPolynomial σ (ZMod 2))
    (f : MvPolynomial σ (ZMod 2)) :
    eval α (bind₁ φ f) = eval (fun e => eval α (φ e)) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p e hp => rw [map_mul, map_mul, map_mul, hp, bind₁_X_right, eval_X]

theorem localNF_map_eq_sum (L : MvPolynomial (GEdge G) (ZMod 2) →ₐ[ZMod 2]
    MvPolynomial (GEdge G) (ZMod 2)) (w : MvPolynomial (GEdge G) (ZMod 2)) :
    L w = ∑ c ∈ w.support, L (monomial c (w.coeff c)) := by
  conv_lhs => rw [← support_sum_monomial_coeff w]
  rw [map_sum]

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

noncomputable def localNF_override (p : Fin m) (j : Fin N) (e : GEdge G) :
    MvPolynomial (GEdge G) (ZMod 2) :=
  if e.1.2 = j then (if e.1.1 = p then 1 else 0) else X e

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

namespace PEqualNP.ProofComplexity.Helpers

open MvPolynomial
open PEqualNP.Expanders

variable {m N : ℕ} (G : BipGraph m N)

noncomputable def pseudoR (s : ℕ) :
    MvPolynomial (GEdge G) (ZMod 2) →ₗ[ZMod 2] MvPolynomial (GEdge G) (ZMod 2) :=
  (basisMonomials (GEdge G) (ZMod 2)).constr (ZMod 2)
    (fun a => nf (locIdeal G (supp G s (monoHoles G a))) (monomial a 1))

theorem pseudoR_monomial (s : ℕ) (a : GEdge G →₀ ℕ) :
    pseudoR G s (monomial a 1) = nf (locIdeal G (supp G s (monoHoles G a))) (monomial a 1) := by
  have h := Module.Basis.constr_basis (basisMonomials (GEdge G) (ZMod 2)) (ZMod 2)
    (fun a => nf (locIdeal G (supp G s (monoHoles G a))) (monomial a 1)) a
  simpa only [pseudoR, coe_basisMonomials] using h

theorem monoHoles_add_single (a : GEdge G →₀ ℕ) (v : GEdge G) :
    monoHoles G (a + Finsupp.single v 1) = insert v.1.2 (monoHoles G a) := by
  unfold monoHoles
  rw [support_add_single_one, Finset.image_insert]

theorem monoHoles_subset_of_vars {f : MvPolynomial (GEdge G) (ZMod 2)} {K : Finset (Fin N)}
    (h : ∀ e ∈ f.vars, e.1.2 ∈ K) : ∀ a ∈ f.support, monoHoles G a ⊆ K := by
  classical
  intro a ha j hj
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
  exact h e ((mem_vars_iff_mem_support e).mpr ⟨a, ha, he⟩)

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

namespace PEqualNP.ProofComplexity.Helpers

open MvPolynomial
open PEqualNP.Expanders

variable {m N : ℕ} (G : BipGraph m N)

def funLocalSat (S : Finset (Fin m)) (α : GEdge G → ZMod 2) : Prop :=
  localSat G S α ∧
  ∀ e e' : GEdge G, e.1.1 = e'.1.1 → e.1.2 ≠ e'.1.2 → α e * α e' = 0

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

def monoPigeons (a : GEdge G →₀ ℕ) : Finset (Fin m) := a.support.image (fun e => e.1.1)

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

namespace PEqualNP.ProofComplexity.Helpers

open MvPolynomial
open PEqualNP.Expanders

variable {m N : ℕ} (G : BipGraph m N)

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

namespace PEqualNP.ProofComplexity.Helpers

open MvPolynomial
open PEqualNP.Expanders

variable {m N : ℕ} (G : BipGraph m N)

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

theorem monoNbrs_subset_of_vars {f : MvPolynomial (GEdge G) (ZMod 2)} {K : Finset (Fin N)}
    (h : ∀ e ∈ f.vars, G e.1.1 ⊆ K) : ∀ a ∈ f.support, monoNbrs G a ⊆ K := by
  classical
  intro a ha j hj
  obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi
  exact h e ((mem_vars_iff_mem_support e).mpr ⟨a, ha, he⟩) hji

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

theorem funPseudoR_eq_zero_of_mem {s : ℕ} (hG : IsBdryExpander G s 2)
    {K : Finset (Fin N)} (hK : K.card ≤ s) {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hfK : ∀ a ∈ f.support, monoNbrs G a ⊆ K)
    (hmem : f ∈ funLocIdeal G (supp G s K)) : funPseudoR G s f = 0 := by
  rw [funPseudoR_eq_nf_of_monomials G (funLocIdeal G (supp G s K)) fun a ha =>
    funPseudoR_monomial_eq_nf G hG le_rfl hK ((Finset.card_le_card (hfK a ha)).trans hK)
      ((hfK a ha).trans Finset.subset_union_left)]
  exact (nf_eq_zero_iff _ _).mpr hmem

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

namespace PEqualNP.ProofComplexity

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

namespace ClauseSearchPC.Toolkit

open MvPolynomial PEqualNP.ProofComplexity

variable {σ : Type}

theorem pcDerivable_mono {F F' : Set (MvPolynomial σ (ZMod 2))} {B B' : ℕ}
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F B p) (hB : B ≤ B') (hF : F ⊆ F') :
    PCDerivable F' B' p := by
  induction h with
  | ax hp hdeg => exact .ax (hF hp) (hdeg.trans hB)
  | zero => exact .zero
  | add _ _ ih1 ih2 => exact .add ih1 ih2
  | mulX j _ hdeg ih => exact .mulX j ih (hdeg.trans hB)

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
        rw [← mul_assoc, X, monomial_mul_monomial, one_mul, ← Finsupp.single_add, add_comm 1 n]
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

noncomputable def boolAxioms (σ : Type) : Set (MvPolynomial σ (ZMod 2)) :=
  Set.range fun v : σ => X v * X v + X v

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

abbrev Af (V : Type) := (V → ZMod 2) × ZMod 2

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

theorem nonlinearCount (H : Circuit) : nl H.gates = H.gates.countP
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

namespace ClauseSearchUpper

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Expanders PEqualNP.ProofComplexity

theorem assignLists {A Y : Type} [DecidableEq A] [DecidableEq Y]
    (work : Finset A) (codes : Finset Y) (cap : Y → ℕ)
    (enough : work.card ≤ ∑ y ∈ codes, cap y) :
    ∃ (assign : work → Y) (out : Y → Finset A),
      (∀ a : work, assign a ∈ codes ∧ a.val ∈ out (assign a)) ∧
      (∀ y, out y ⊆ work) ∧ ∀ y ∈ codes, (out y).card ≤ cap y := by
  classical
  let Slots := Σ y : codes, Fin (cap y.val)
  have slotCount : Fintype.card Slots = ∑ y ∈ codes, cap y := by
    rw [Fintype.card_sigma]
    simp [Finset.sum_attach]
  obtain ⟨inject⟩ : Nonempty (work ↪ Slots) := Function.Embedding.nonempty_of_card_le (by
    rw [Fintype.card_coe, slotCount]
    exact enough)
  let assign (a : work) : Y := (inject a).1.val
  let selected (y : Y) := (Finset.univ : Finset work).filter (fun a => assign a = y)
  let out (y : Y) := (selected y).image Subtype.val
  refine ⟨assign, out, ?_, ?_, ?_⟩
  · intro a
    exact ⟨(inject a).1.property, Finset.mem_image.mpr
      ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩⟩
  · intro y a ha
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
    exact x.property
  · intro y hy
    let label : codes := ⟨y, hy⟩
    let Fiber := {s : Slots // s.1 = label}
    let equiv : Fiber ≃ Fin (cap y) :=
      { toFun := fun s => Fin.cast (congrArg (fun a : codes => cap a.val) s.property) s.val.2
        invFun := fun i => ⟨⟨label, i⟩, rfl⟩
        left_inv := by
          rintro ⟨⟨z, j⟩, eq⟩
          change z = label at eq
          subst z
          rfl
        right_inv := by intro j; rfl }
    let into (a : selected y) : Fiber :=
      ⟨inject a.val, Subtype.ext (Finset.mem_filter.mp a.property).2⟩
    have one : Function.Injective into := by
      intro a b eq
      exact Subtype.ext (inject.injective (congrArg Subtype.val eq))
    have count := Fintype.card_le_of_injective into one
    rw [Fintype.card_coe, Fintype.card_congr equiv, Fintype.card_fin] at count
    exact Finset.card_image_le.trans count

theorem constantMessage {n b : ℕ} (space : 2 ≤ n) (word : Fin b → ZMod 2) :
    ∃ (H : Circuit) (pick : Fin b → Fin (n + H.size)),
      H.gates = [] ∧ ReadsBack n H ∧
      ∀ (inputs : List Bool), inputs.getD 0 true = false → inputs.getD 1 false = true →
        ∀ j, (((H.wires inputs).getD (pick j).val false).toNat : ZMod 2) = word j := by
  let H : Circuit := ⟨[], 0⟩
  let pick (j : Fin b) : Fin (n + H.size) := ⟨if word j = 1 then 1 else 0, by
    change (if word j = 1 then 1 else 0) < n
    split_ifs <;> omega⟩
  refine ⟨H, pick, rfl, ?_, ?_⟩
  · intro j hj
    simp [H] at hj
  · intro inputs zero one j
    have zeroAt : inputs.getD 0 false = false := by
      cases inputs with
      | nil => simp
      | cons x xs => simpa using zero
    have bits : word j = 0 ∨ word j = 1 := by
      generalize word j = w
      revert w
      decide
    change ((inputs.getD (if word j = 1 then 1 else 0) false).toNat : ZMod 2) = word j
    rcases bits with h | h
    · rw [h, if_neg (by decide : (0 : ZMod 2) ≠ 1), zeroAt]
      rfl
    · rw [h, if_pos rfl, one]
      rfl

def pigeonClause {m n : ℕ} (G : BipGraph m n) (i : Fin m) : Clause (GEdge G) :=
  Finset.univ.filter (fun l => l.1.1.1 = i ∧ l.2 = true)

theorem graphViolation {m n : ℕ} (G : BipGraph m n) (deficit : n < m)
    (x : GEdge G → Bool) : ∃ cl ∈ funGraphPHP G, ¬ ClauseSat x cl := by
  classical
  by_contra no
  push Not at no
  have each (i : Fin m) : ∃ e : GEdge G, e.val.1 = i ∧ x e = true := by
    have sat := no (pigeonClause G i) (Or.inl (Or.inl ⟨i, rfl⟩))
    obtain ⟨l, mem, hit⟩ := sat
    obtain ⟨own, polarity⟩ := (Finset.mem_filter.mp mem).2
    exact ⟨l.1, own, hit.trans polarity⟩
  choose edge on assigned using each
  have injection : Function.Injective (fun i => (edge i).val.2) := by
    intro i j equal
    by_contra different
    have distinct : (edge i).val.1 ≠ (edge j).val.1 := by simpa [on] using different
    have sat := no ({(edge i, false), (edge j, false)} : Clause (GEdge G))
      (Or.inl (Or.inr ⟨edge i, edge j, equal, distinct, rfl⟩))
    obtain ⟨l, hit, value⟩ := sat
    rcases Finset.mem_insert.mp hit with rfl | hit
    · simp [assigned] at value
    · obtain rfl := Finset.mem_singleton.mp hit
      simp [assigned] at value
  have count := Fintype.card_le_of_injective _ injection
  simp only [Fintype.card_fin] at count
  omega

noncomputable def graphClauses {m n : ℕ} (G : BipGraph m n) : Finset (Clause (GEdge G)) := by
  classical
  exact Finset.univ.filter fun cl => cl ∈ funGraphPHP G

theorem memGraphClauses {m n : ℕ} (G : BipGraph m n) (cl : Clause (GEdge G)) :
    cl ∈ graphClauses G ↔ cl ∈ funGraphPHP G := by
  classical
  simp [graphClauses]

private def holeEdge {m n : ℕ} (G : BipGraph m n) (j : Fin n) (i : rightNbrs G j) : GEdge G :=
  ⟨(i.val, j), (Finset.mem_filter.mp i.property).2⟩

private def pigeonEdge {m n : ℕ} (G : BipGraph m n) (i : Fin m) (j : G i) : GEdge G :=
  ⟨(i, j.val), j.property⟩

theorem graphClauseCount {m n d : ℕ} (G : BipGraph m n) (left : LeftDegLe G d) (right : RightDegLe G d) :
    (graphClauses G).card ≤ m + n*(d*d) + m*(d*d) := by
  classical
  let H := Σ j : Fin n, rightNbrs G j × rightNbrs G j
  let P := Σ i : Fin m, G i × G i
  let pos := Finset.univ.image (pigeonClause G)
  let holes := (Finset.univ : Finset H).image fun a =>
    ({(holeEdge G a.1 a.2.1, false), (holeEdge G a.1 a.2.2, false)} : Clause (GEdge G))
  let functions := (Finset.univ : Finset P).image fun a =>
    ({(pigeonEdge G a.1 a.2.1, false), (pigeonEdge G a.1 a.2.2, false)} : Clause (GEdge G))
  have covered : graphClauses G ⊆ (pos ∪ holes) ∪ functions := by
    intro cl mem
    rcases (memGraphClauses G cl).mp mem with base | f
    · rcases base with p | h
      · obtain ⟨i, rfl⟩ := p
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
      · obtain ⟨⟨⟨p, j⟩, e⟩, ⟨⟨q, k⟩, e'⟩, (same : j = k), _, rfl⟩ := h
        subst k
        have e₁ : p ∈ rightNbrs G j := by simp [rightNbrs, e]
        have e₂ : q ∈ rightNbrs G j := by simp [rightNbrs, e']
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨⟨j, ⟨p, e₁⟩, ⟨q, e₂⟩⟩, Finset.mem_univ _, rfl⟩))
    · obtain ⟨⟨⟨p, j⟩, e⟩, ⟨⟨q, k⟩, e'⟩, (same : p = q), _, rfl⟩ := f
      subst q
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨⟨p, ⟨j, e⟩, ⟨k, e'⟩⟩, Finset.mem_univ _, rfl⟩)
  have posBound : pos.card ≤ m := Finset.card_image_le.trans_eq (by simp)
  have holeCount : Fintype.card H ≤ n*(d*d) := by
    dsimp [H]
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _j : Fin n, d*d := by
        apply Finset.sum_le_sum
        intro j _
        simpa using Nat.mul_le_mul (right j) (right j)
      _ = _ := by simp
  have functionCount : Fintype.card P ≤ m*(d*d) := by
    dsimp [P]
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _i : Fin m, d*d := by
        apply Finset.sum_le_sum
        intro i _
        simpa using Nat.mul_le_mul (left i) (left i)
      _ = _ := by simp
  have holeBound : holes.card ≤ n*(d*d) := Finset.card_image_le.trans (by simpa using holeCount)
  have functionBound : functions.card ≤ m*(d*d) := Finset.card_image_le.trans (by simpa using functionCount)
  calc
    _ ≤ ((pos ∪ holes) ∪ functions).card := Finset.card_le_card covered
    _ ≤ (pos ∪ holes).card + functions.card := Finset.card_union_le _ _
    _ ≤ (pos.card + holes.card) + functions.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ _ := Nat.add_le_add (Nat.add_le_add posBound holeBound) functionBound

end ClauseSearchUpper

namespace ClauseSearchProgram

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def wiresOf (gs : List Gate) (inputs : List Bool) : List Bool :=
  (⟨gs, 0⟩ : Circuit).wires inputs

lemma wiresOf_len (gs : List Gate) (x : List Bool) :
    (wiresOf gs x).length = x.length + gs.length := by
  unfold wiresOf Circuit.wires
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma wiresOf_append (gs1 gs2 : List Gate) (x : List Bool) :
    wiresOf (gs1 ++ gs2) x = wiresOf gs2 (wiresOf gs1 x) := by
  unfold wiresOf Circuit.wires
  exact List.foldl_append

lemma wiresOf_getD_lt (gs : List Gate) (x : List Bool) {i : ℕ} (hi : i < x.length) :
    (wiresOf gs x).getD i false = x.getD i false := by
  unfold wiresOf Circuit.wires
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (x ++ [g.op.eval (g.inputs.map fun idx => x.getD idx false)]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    rw [ih _ hi']
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wiresOf_append_getD_lt (gs1 gs2 : List Gate) (x : List Bool) {i : ℕ}
    (hi : i < x.length + gs1.length) :
    (wiresOf (gs1 ++ gs2) x).getD i false = (wiresOf gs1 x).getD i false := by
  rw [wiresOf_append, wiresOf_getD_lt gs2 (wiresOf gs1 x) (by rw [wiresOf_len]; exact hi)]

lemma wiresOf_snoc_last (gs : List Gate) (g : Gate) (x : List Bool) :
    (wiresOf (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (wiresOf gs x).getD i false) := by
  rw [wiresOf_append]
  set w := wiresOf gs x
  have hlen : w.length = x.length + gs.length := wiresOf_len gs x
  change (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD (x.length + gs.length) false = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
      show x.length + gs.length - w.length = 0 by omega]
  rfl

lemma wiresOf_snoc_last_eq {n : ℕ} (gs : List Gate) (g : Gate) (x : List Bool) (hx : x.length = n) :
    (wiresOf (gs ++ [g]) x).getD (n + gs.length) false =
      g.op.eval (g.inputs.map fun i => (wiresOf gs x).getD i false) := by
  have h := wiresOf_snoc_last gs g x
  rw [hx] at h
  exact h

lemma readsBack_append {n : ℕ} {gs1 gs2 : List Gate}
    (h1 : ReadsBack n ⟨gs1, 0⟩)
    (h2 : ∀ j < gs2.length, ∀ i ∈ (gs2.getD j ⟨.or, []⟩).inputs, i < n + gs1.length + j) :
    ReadsBack n ⟨gs1 ++ gs2, 0⟩ := by
  intro j hj i hi
  simp only [gateAt] at hi
  simp only [List.length_append] at hj
  by_cases hlt : j < gs1.length
  · have hget : (gs1 ++ gs2).getD j ⟨.or, []⟩ = gs1.getD j ⟨.or, []⟩ := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    rw [hget] at hi
    exact h1 j hlt i hi
  · have hge : gs1.length ≤ j := by omega
    have hget : (gs1 ++ gs2).getD j ⟨.or, []⟩ = gs2.getD (j - gs1.length) ⟨.or, []⟩ := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hge]
    rw [hget] at hi
    have := h2 (j - gs1.length) (by omega) i hi
    omega

def gateValue (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem readBeforeAppend (u v : List Bool) {i : ℕ} (earlier : i < u.length) :
    (u ++ v).getD i false = u.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left earlier]

private theorem independentSuffix (gs : List Gate) (w : List Bool)
    (back : ∀ g ∈ gs, ∀ i ∈ g.inputs, i < w.length) :
    wiresOf gs w = w ++ gs.map (gateValue w) := by
  induction gs generalizing w with
  | nil => simp [wiresOf, Circuit.wires]
  | cons g gs ih =>
    let new := w ++ [gateValue w g]
    have valueUnchanged : ∀ t ∈ gs, gateValue new t = gateValue w t := by
      intro t mem
      unfold gateValue
      congr 1
      exact List.map_congr_left (fun i hit => readBeforeAppend w _ (back t (List.mem_cons_of_mem _ mem) i hit))
    have staysEarlier : ∀ t ∈ gs, ∀ i ∈ t.inputs, i < new.length := by
      intro t mem i hit
      exact (back t (List.mem_cons_of_mem _ mem) i hit).trans_le (by simp [new])
    change wiresOf gs new = w ++ (g :: gs).map (gateValue w)
    rw [ih new staysEarlier, List.map_congr_left valueUnchanged]
    simp [new, List.append_assoc]

private theorem binaryField (z : ZMod 2) : z = 0 ∨ z = 1 := by
  revert z
  decide

private theorem modOfCount (l : List Bool) :
    (((GateOp.mod 2).eval l).toNat : ZMod 2) = 1 + (l.count true : ZMod 2) := by
  change ((decide (l.count true % 2 = 0)).toNat : ZMod 2) = 1 + (l.count true : ZMod 2)
  rw [← ZMod.natCast_mod (l.count true) 2]
  rcases Nat.mod_two_eq_zero_or_one (l.count true) with h | h <;> rw [h] <;> decide

def selectedWires {m : ℕ} (idx : List (Fin m)) (coeff : Fin m → ZMod 2) (wire : Fin m → ℕ) : List ℕ :=
  idx.filterMap (fun i => if coeff i = 1 then some (wire i) else none)

private theorem selectedCount {m : ℕ} (idx : List (Fin m)) (coeff : Fin m → ZMod 2)
    (wire : Fin m → ℕ) (w : List Bool) :
    ((((selectedWires idx coeff wire).map (fun i => w.getD i false)).count true : ℕ) : ZMod 2) =
      (idx.map (fun i => coeff i * ((w.getD (wire i) false).toNat : ZMod 2))).sum := by
  induction idx with
  | nil => simp [selectedWires]
  | cons i idx ih =>
    rcases binaryField (coeff i) with zero | one
    · simpa [selectedWires, zero] using ih
    · have selected : selectedWires (i::idx) coeff wire = wire i :: selectedWires idx coeff wire := by
        simp [selectedWires, one]
      rw [selected, List.map_cons, List.map_cons, List.sum_cons, one, one_mul]
      cases w.getD (wire i) false <;> simpa [Nat.cast_add, add_comm] using ih

theorem sumListOfFinset {ι A : Type} [AddCommMonoid A] (s : Finset ι) (f : ι → A) :
    (s.toList.map f).sum = ∑ i ∈ s, f i := by
  change ((s.toList.map f : List A) : Multiset A).sum = _
  rw [← Multiset.map_coe, Finset.coe_toList]
  rfl

noncomputable def affineGate {m : ℕ} (β : ZMod 2) (coeff : Fin m → ZMod 2) (wire : Fin m → ℕ) : Gate :=
  ⟨.mod 2, (if β = 1 then [] else [1]) ++ selectedWires (Finset.univ.toList) coeff wire⟩

private theorem affineGateCorrect {m : ℕ} (β : ZMod 2) (coeff : Fin m → ZMod 2)
    (wire : Fin m → ℕ) (w : List Bool) (one : w.getD 1 false = true) :
    ((gateValue w (affineGate β coeff wire)).toNat : ZMod 2) =
      β + ∑ i, coeff i * ((w.getD (wire i) false).toNat : ZMod 2) := by
  change (((GateOp.mod 2).eval (((if β = 1 then [] else [1]) ++
        selectedWires (Finset.univ.toList) coeff wire).map (fun i => w.getD i false))).toNat : ZMod 2) = _
  rw [modOfCount]
  have body := selectedCount (Finset.univ.toList : List (Fin m)) coeff wire w
  rw [sumListOfFinset] at body
  rcases binaryField β with zero | high
  · simp only [zero, show (0 : ZMod 2) ≠ 1 by decide, ite_false, List.singleton_append,
      List.map_cons, one, List.count_cons, beq_self_eq_true, ite_true, Nat.cast_add, Nat.cast_one, body, zero_add]
    have two : (1 : ZMod 2) + 1 = 0 := by decide
    calc
      _ = (1+1) + ∑ i, coeff i * ((w.getD (wire i) false).toNat : ZMod 2) := by ac_rfl
      _ = _ := by rw [two, zero_add]
  · simp only [high, ite_true, List.nil_append, body]

theorem appendAffineEncoder {n m b : ℕ} (space : 2 ≤ n) (gs : List Gate)
    (reads : ReadsBack n ⟨gs, 0⟩) (wire : Fin m → Fin (n + gs.length))
    (offset : Fin b → ZMod 2) (coeff : Fin b → Fin m → ZMod 2) :
    ∃ (tail : List Gate) (pick : Fin b → Fin (n + (gs ++ tail).length)),
      ReadsBack n ⟨gs ++ tail, 0⟩ ∧ (∀ g ∈ tail, g.op = .mod 2) ∧
      ∀ (inputs : List Bool), inputs.length = n → inputs.getD 1 false = true → ∀ j,
        (((wiresOf (gs ++ tail) inputs).getD (pick j).val false).toNat : ZMod 2) =
          offset j + ∑ i, coeff j i * (((wiresOf gs inputs).getD (wire i).val false).toNat : ZMod 2) := by
  let gate (j : Fin b) := affineGate (offset j) (coeff j) (fun i => (wire i).val)
  let tail := List.ofFn gate
  let pick (j : Fin b) : Fin (n + (gs ++ tail).length) := ⟨n + gs.length + j.val, by
    simp only [List.length_append, tail, List.length_ofFn]
    omega⟩
  have below : ∀ g ∈ tail, ∀ i ∈ g.inputs, i < n + gs.length := by
    intro g mem i arg
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp mem
    change i ∈ (if offset j = 1 then [] else [1]) ++
      selectedWires (Finset.univ.toList) (coeff j) (fun i => (wire i).val) at arg
    rcases List.mem_append.mp arg with constant | variableArg
    · split_ifs at constant <;> simp_all
      omega
    · obtain ⟨k, _, selected⟩ := List.mem_filterMap.mp variableArg
      by_cases h : coeff j k = 1
      · have eq : (wire k).val = i := by simpa only [h, ite_true, Option.some.injEq] using selected
        rw [← eq]
        exact (wire k).isLt
      · simp [h] at selected
  refine ⟨tail, pick, readsBack_append reads ?_, ?_, ?_⟩
  · intro j hj i mem
    have inTail : tail.getD j ⟨.or, []⟩ ∈ tail := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
      exact List.getElem_mem hj
    exact (below _ inTail _ mem).trans_le (Nat.le_add_right _ _)
  · intro g mem
    obtain ⟨_, rfl⟩ := List.mem_ofFn.mp mem
    rfl
  · intro inputs len one j
    let w := wiresOf gs inputs
    have wlen : w.length = n+gs.length := by simp [w, wiresOf_len, len]
    have wone : w.getD 1 false = true := (wiresOf_getD_lt gs inputs (by omega)).trans one
    have evaluate := independentSuffix tail w (by rw [wlen]; exact below)
    have atOutput : (wiresOf (gs ++ tail) inputs).getD (pick j).val false = gateValue w (gate j) := by
      rw [wiresOf_append, evaluate]
      change (w ++ tail.map (gateValue w)).getD (n+gs.length+j.val) false = _
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      simp only [wlen, Nat.add_sub_cancel_left, List.getElem?_map, tail, List.getElem?_ofFn, j.isLt, dite_true,
        Option.map_some, Option.getD_some]
    rw [atOutput]
    exact affineGateCorrect _ _ _ w wone

end ClauseSearchProgram

namespace ClauseSearchScanner

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover ClauseSearchProgram

def Shape (g : Gate) : Prop :=
  ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨ g.op = .mod 2 ∨
  (g.op = .not ∧ g.inputs.length = 1)

def Legal (n : ℕ) (gs : List Gate) : Prop := ReadsBack n ⟨gs, 0⟩ ∧ ∀ g ∈ gs, Shape g

def nonlinear (g : Gate) : Bool :=
  match g.op with
  | .and => true
  | .or => true
  | _ => false

def cost (gs : List Gate) : ℕ := gs.countP nonlinear

theorem emptyLegal (n : ℕ) : Legal n [] := by
  constructor <;> simp [ReadsBack]

theorem legalSnoc {n : ℕ} {gs : List Gate} {g : Gate} (ok : Legal n gs)
    (reads : ∀ i ∈ g.inputs, i < n+gs.length) (shape : Shape g) : Legal n (gs ++ [g]) := by
  refine ⟨readsBack_append ok.1 ?_, ?_⟩
  · intro j hj i hi
    have zero : j = 0 := by simp at hj; omega
    subst j
    exact (reads i (by simpa using hi)).trans_le (Nat.le_add_right _ _)
  · intro g' mem
    rcases List.mem_append.mp mem with old | new
    · exact ok.2 _ old
    · have eq : g' = g := List.mem_singleton.mp new
      rwa [eq]

theorem prefixValue {gs hs : List Gate} (extend : gs <+: hs)
    (inputs : List Bool) {i : ℕ} (before : i < inputs.length + gs.length) :
    (wiresOf hs inputs).getD i false = (wiresOf gs inputs).getD i false := by
  obtain ⟨tail, rfl⟩ := extend
  exact wiresOf_append_getD_lt _ _ _ before

private def literalFalseGate {n : ℕ} (lit : Fin n × Bool) : Gate :=
  ⟨.mod 2, lit.1.val :: (if lit.2 then [] else [1])⟩

private theorem literalFalseValue {n : ℕ} (lit : Fin n × Bool) (w : List Bool)
    (one : w.getD 1 false = true) :
    gateValue w (literalFalseGate lit) = !(w.getD lit.1.val false == lit.2) := by
  rcases lit with ⟨i, sign⟩
  cases sign with
  | false =>
    change decide (([w.getD i.val false, w.getD 1 false]).count true % 2 = 0) = !(w.getD i.val false == false)
    rw [one]
    cases w.getD i.val false <;> decide
  | true =>
    change decide (([w.getD i.val false]).count true % 2 = 0) = !(w.getD i.val false == true)
    cases w.getD i.val false <;> decide

def testLiterals {n : ℕ} (lits : List (Fin n × Bool)) (inputs : List Bool) : Bool :=
  lits.all (fun l => !(inputs.getD l.1.val false == l.2))

def conjoin (n : ℕ) : List (Fin n × Bool) → List Gate → ℕ → List Gate × ℕ
  | [], gs, a => (gs, a)
  | l :: ls, gs, a =>
    let k := n + gs.length
    let gates := (gs ++ [literalFalseGate l]) ++ [⟨.and, [a, k]⟩]
    conjoin n ls gates (k+1)

theorem conjoinCorrect {n : ℕ} (space : 2 ≤ n) (lits : List (Fin n × Bool))
    (gs : List Gate) (a : ℕ) (ok : Legal n gs) (earlier : a < n+gs.length) :
    let run := conjoin n lits gs a
    gs <+: run.1 ∧ Legal n run.1 ∧ run.2 < n+run.1.length ∧
      cost run.1 = cost gs + lits.length ∧
      ∀ (inputs : List Bool), inputs.length = n → inputs.getD 1 false = true →
        (wiresOf run.1 inputs).getD run.2 false =
          ((wiresOf gs inputs).getD a false && testLiterals lits inputs) := by
  induction lits generalizing gs a with
  | nil => simp [conjoin, ok, earlier, testLiterals]
  | cons l ls ih =>
    let k := n+gs.length
    let gate := literalFalseGate l
    let middle := gs ++ [gate]
    let out := middle ++ [⟨.and,[a,k]⟩]
    have middleLen : n+middle.length = k+1 := by simp [middle, k, Nat.add_assoc]
    have outLen : n+out.length = k+2 := by simp [out, middle, k, Nat.add_assoc]
    have canGate : ∀ i ∈ gate.inputs, i < n+gs.length := by
      intro i mem
      change i ∈ l.1.val :: (if l.2 then [] else [1]) at mem
      rcases List.mem_cons.mp mem with h | h
      · rw [h]
        exact l.1.isLt.trans_le (Nat.le_add_right _ _)
      · split_ifs at h <;> simp_all <;> omega
    have midOk : Legal n middle := legalSnoc ok canGate (Or.inr (Or.inl rfl))
    have andReads : ∀ i ∈ ([a,k] : List ℕ), i < n+middle.length := by
      intro i mem
      rw [List.mem_cons, List.mem_singleton] at mem
      rw [middleLen]
      rcases mem with rfl | rfl <;> omega
    have outOk : Legal n out := legalSnoc midOk andReads (Or.inl ⟨Or.inl rfl, rfl⟩)
    have outEarlier : k+1 < n+out.length := by omega
    have outPref : gs <+: out := (List.prefix_append gs [gate]).trans (List.prefix_append middle _)
    obtain ⟨extend, nextOk, field, budget, output⟩ := ih out (k+1) outOk outEarlier
    refine ⟨outPref.trans extend, nextOk, field, ?_, ?_⟩
    · change cost (conjoin n ls out (k+1)).1 = _
      rw [budget]
      simp [cost, out, middle, gate, literalFalseGate, nonlinear]
      omega
    · intro inputs len one
      have atOld : (wiresOf middle inputs).getD a false = (wiresOf gs inputs).getD a false :=
        wiresOf_append_getD_lt gs [gate] inputs (by omega)
      have atOne : (wiresOf gs inputs).getD 1 false = true :=
        (wiresOf_getD_lt gs inputs (by omega)).trans one
      have atVar : (wiresOf gs inputs).getD l.1.val false = inputs.getD l.1.val false :=
        wiresOf_getD_lt gs inputs (by rw [len]; exact l.1.isLt)
      have atK : (wiresOf middle inputs).getD k false = !(inputs.getD l.1.val false == l.2) := by
        rw [wiresOf_snoc_last_eq gs gate inputs len]
        change gateValue (wiresOf gs inputs) (literalFalseGate l) = _
        rw [literalFalseValue _ _ atOne, atVar]
      have atNew : (wiresOf out inputs).getD (k+1) false =
          ((wiresOf gs inputs).getD a false && !(inputs.getD l.1.val false == l.2)) := by
        rw [← middleLen, wiresOf_snoc_last_eq middle _ inputs len]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, id_eq, List.all_nil,
          Bool.and_true, atOld, atK]
      change (wiresOf (conjoin n ls out (k+1)).1 inputs).getD (conjoin n ls out (k+1)).2 false = _
      rw [output inputs len one, atNew]
      simp [testLiterals, Bool.and_assoc]

private theorem gateValueAnd (w : List Bool) (a b : ℕ) :
    gateValue w ⟨.and, [a,b]⟩ = (w.getD a false && w.getD b false) := by
  simp only [gateValue, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
    id_eq, Bool.and_true]

private theorem gateValueNot (w : List Bool) (a : ℕ) :
    gateValue w ⟨.not, [a]⟩ = !w.getD a false := rfl

def decision (n : ℕ) (lits : List (Fin n × Bool)) (gs : List Gate) (active : ℕ) : List Gate × ℕ × ℕ :=
  let tested := conjoin n lits gs 1
  let k := n+tested.1.length
  let selected := tested.1 ++ [⟨.and, [active, tested.2]⟩]
  let negate := selected ++ [⟨.not, [tested.2]⟩]
  let next := negate ++ [⟨.and, [active, k+1]⟩]
  (next, k+2, k)

private theorem decisionCorrect {n : ℕ} (space : 2 ≤ n) (lits : List (Fin n × Bool))
    (gs : List Gate) (active : ℕ) (ok : Legal n gs) (earlier : active < n+gs.length) :
    let run := decision n lits gs active
    gs <+: run.1 ∧ Legal n run.1 ∧ run.2.1 < n+run.1.length ∧ run.2.2 < n+run.1.length ∧
      cost run.1 = cost gs + (lits.length+2) ∧
      ∀ (inputs : List Bool), inputs.length = n → inputs.getD 1 false = true →
        (wiresOf run.1 inputs).getD run.2.1 false =
          ((wiresOf gs inputs).getD active false && !testLiterals lits inputs) ∧
        (wiresOf run.1 inputs).getD run.2.2 false =
          ((wiresOf gs inputs).getD active false && testLiterals lits inputs) := by
  let tested := conjoin n lits gs 1
  obtain ⟨p, testedOk, valid, testedCost, testValue⟩ := conjoinCorrect space lits gs 1 ok (by omega)
  change gs <+: tested.1 at p
  change Legal n tested.1 at testedOk
  let k := n+tested.1.length
  let selected := tested.1 ++ [⟨.and, [active, tested.2]⟩]
  let negate := selected ++ [⟨.not,[tested.2]⟩]
  let next := negate ++ [⟨.and,[active,k+1]⟩]
  have prefixLen := p.length_le
  have activeEarly : active < k := by dsimp [k]; omega
  have testedEarly : tested.2 < k := valid
  have selectedLen : n+selected.length = k+1 := by simp [selected, k, Nat.add_assoc]
  have negateLen : n+negate.length = k+2 := by
    simp only [negate, List.length_append, List.length_singleton]
    omega
  have nextLen : n+next.length = k+3 := by
    simp only [next, List.length_append, List.length_singleton]
    omega
  have selectedOk : Legal n selected := legalSnoc testedOk (by
      intro i hi; simp at hi
      rcases hi with rfl | rfl <;> assumption) (Or.inl ⟨Or.inl rfl, rfl⟩)
  have negateOk : Legal n negate := legalSnoc selectedOk (by
      intro i hi; obtain rfl := List.mem_singleton.mp hi
      rw [selectedLen]; omega) (Or.inr (Or.inr ⟨rfl, rfl⟩))
  have nextOk : Legal n next := legalSnoc negateOk (by
      intro i hi; simp at hi
      rw [negateLen]; rcases hi with rfl | rfl <;> omega) (Or.inl ⟨Or.inl rfl, rfl⟩)
  have p₁ : tested.1 <+: selected := List.prefix_append _ _
  have p₂ : selected <+: negate := List.prefix_append _ _
  have p₃ : negate <+: next := List.prefix_append _ _
  change gs <+: next ∧ Legal n next ∧ k+2 < n+next.length ∧ k < n+next.length ∧ _
  refine ⟨p.trans (p₁.trans (p₂.trans p₃)), nextOk, by omega, by omega, ?_, ?_⟩
  · change cost next = cost gs + (lits.length+2)
    change cost tested.1 = cost gs + lits.length at testedCost
    have more : cost next = cost tested.1 + 2 := by
      simp only [cost, next, negate, selected, List.countP_append]
      rfl
    rw [more, testedCost, Nat.add_assoc]
  · intro inputs len one
    have kept : (wiresOf tested.1 inputs).getD active false = (wiresOf gs inputs).getD active false :=
      prefixValue p inputs (by omega)
    have kValue : (wiresOf tested.1 inputs).getD tested.2 false = testLiterals lits inputs := by
      have actual := testValue inputs len one
      have start : (wiresOf gs inputs).getD 1 false = true :=
        (wiresOf_getD_lt gs inputs (by omega)).trans one
      change (wiresOf tested.1 inputs).getD tested.2 false = _ at actual
      simpa only [start, Bool.true_and] using actual
    have selectedValue : (wiresOf selected inputs).getD k false =
        ((wiresOf gs inputs).getD active false && testLiterals lits inputs) := by
      rw [wiresOf_snoc_last_eq tested.1 _ inputs len]
      change gateValue (wiresOf tested.1 inputs) ⟨.and, [active,tested.2]⟩ = _
      rw [gateValueAnd, kept, kValue]
    have negatedValue : (wiresOf negate inputs).getD (k+1) false = !testLiterals lits inputs := by
      rw [← selectedLen, wiresOf_snoc_last_eq selected _ inputs len]
      change gateValue (wiresOf selected inputs) ⟨.not,[tested.2]⟩ = _
      rw [gateValueNot, prefixValue p₁ inputs (by omega), kValue]
    have readyValue : (wiresOf next inputs).getD (k+2) false =
        ((wiresOf gs inputs).getD active false && !testLiterals lits inputs) := by
      rw [← negateLen, wiresOf_snoc_last_eq negate _ inputs len]
      change gateValue (wiresOf negate inputs) ⟨.and, [active,k+1]⟩ = _
      rw [gateValueAnd, prefixValue (p.trans (p₁.trans p₂)) inputs (by omega), negatedValue]
    change (wiresOf next inputs).getD (k+2) false = _ ∧ (wiresOf next inputs).getD k false = _
    exact ⟨readyValue, (prefixValue (p₂.trans p₃) inputs (by omega)).trans selectedValue⟩

def firstFlags : Bool → List Bool → List Bool
  | _, [] => []
  | active, v :: vs => (active && v) :: firstFlags (active && !v) vs

def scan (n : ℕ) : List (List (Fin n × Bool)) → List Gate → ℕ → List Gate × List ℕ
  | [], gs, _ => (gs, [])
  | t :: ts, gs, active =>
    let block := decision n t gs active
    let after := scan n ts block.1 block.2.1
    (after.1, block.2.2 :: after.2)

theorem scanCorrect {n : ℕ} (space : 2 ≤ n) (tests : List (List (Fin n × Bool)))
    (gs : List Gate) (active : ℕ) (ok : Legal n gs) (earlier : active < n+gs.length) :
    let run := scan n tests gs active
    gs <+: run.1 ∧ Legal n run.1 ∧ run.2.length = tests.length ∧
      (∀ a ∈ run.2, a < n+run.1.length) ∧
      cost run.1 = cost gs + (tests.map (fun t => t.length+2)).sum ∧
      ∀ (inputs : List Bool), inputs.length = n → inputs.getD 1 false = true →
        run.2.map (fun i => (wiresOf run.1 inputs).getD i false) =
          firstFlags ((wiresOf gs inputs).getD active false) (tests.map (fun t => testLiterals t inputs)) := by
  induction tests generalizing gs active with
  | nil => simp [scan, ok, firstFlags]
  | cons t ts ih =>
    let block := decision n t gs active
    let after := scan n ts block.1 block.2.1
    obtain ⟨old, blockOk, next, selected, blockCost, values⟩ := decisionCorrect space t gs active ok earlier
    obtain ⟨extend, tailOk, len, allEarlier, tailCost, evalTail⟩ := ih block.1 block.2.1 blockOk next
    have grows := extend.length_le
    have finalLen : (scan n (t::ts) gs active).2.length = (t::ts).length := by
      change after.2.length+1 = ts.length+1
      exact congrArg (·+1) len
    refine ⟨old.trans extend, tailOk, finalLen, ?_, ?_, ?_⟩
    · intro a ha
      change a ∈ block.2.2 :: after.2 at ha
      rcases List.mem_cons.mp ha with rfl | ha
      · change block.2.2 < n+block.1.length at selected
        change block.1.length ≤ after.1.length at grows
        change block.2.2 < n+after.1.length
        omega
      · exact allEarlier _ ha
    · change cost after.1 = _
      rw [tailCost, blockCost]
      simp [Nat.add_assoc]
    · intro inputs size one
      change (block.2.2 :: after.2).map (fun i => (wiresOf after.1 inputs).getD i false) = _
      have before : block.2.2 < inputs.length+block.1.length := by simpa only [size] using selected
      have kept := prefixValue extend inputs before
      obtain ⟨bActive, bFlag⟩ := values inputs size one
      rw [List.map_cons, kept, bFlag, evalTail inputs size one, bActive]
      rfl

private theorem flagsOff (values : List Bool) (i : ℕ) :
    (firstFlags false values).getD i false = false := by
  induction values generalizing i with
  | nil => cases i <;> rfl
  | cons v vs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem firstFlagsCases (values : List Bool) :
    (∀ i < values.length, values.getD i false = false ∧ (firstFlags true values).getD i false = false) ∨
    ∃ k < values.length, values.getD k false = true ∧
      ∀ i < values.length, (firstFlags true values).getD i false = decide (i = k) := by
  induction values with
  | nil => exact Or.inl (fun i h => (Nat.not_lt_zero _ h).elim)
  | cons v vs ih =>
    cases v with
    | true =>
      refine Or.inr ⟨0, by simp, rfl, ?_⟩
      intro i _
      cases i with
      | zero => rfl
      | succ i =>
        change (firstFlags false vs).getD i false = decide (i+1 = 0)
        exact (flagsOff _ _).trans (by simp)
    | false =>
      rcases ih with no | ⟨k, hk, fail, flags⟩
      · refine Or.inl (fun i h => ?_)
        cases i with
        | zero => exact ⟨rfl, rfl⟩
        | succ i => exact no i (by simpa using h)
      · refine Or.inr ⟨k+1, by simpa using hk, fail, ?_⟩
        intro i h
        cases i with
        | zero => simp [firstFlags]
        | succ i => simpa [firstFlags] using flags i (by simpa using h)

end ClauseSearchScanner

namespace ClauseSearchRealize

open PEqualNP.CircuitLowerBounds PEqualNP.ProofComplexity PEqualNP.MetaComplexity.NestedCover
open ClauseSearchProgram ClauseSearchScanner

variable {V : Type} [Fintype V] [DecidableEq V] {e b : ℕ}

def inputs (order : V ≃ Fin e) (x : V → Bool) : List Bool :=
  [false,true] ++ List.ofFn (fun i : Fin e => x (order.symm i))

omit [Fintype V] [DecidableEq V] in
theorem inputsLength (order : V ≃ Fin e) (x : V → Bool) : (inputs order x).length = 2+e := by
  rw [inputs, List.length_append, List.length_ofFn]
  rfl

omit [Fintype V] [DecidableEq V] in
theorem inputsOne (order : V ≃ Fin e) (x : V → Bool) : (inputs order x).getD 1 false = true := rfl

def inputWire (order : V ≃ Fin e) (v : V) : Fin (2+e) := ⟨2+(order v).val, by
  have := (order v).isLt
  omega⟩

theorem inputValue (order : V ≃ Fin e) (x : V → Bool) (v : V) :
    (inputs order x).getD (inputWire order v).val false = x v := by
  change ([false,true] ++ List.ofFn (fun i : Fin e => x (order.symm i))).getD (2+(order v).val) false = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  have sub : 2 + (order v).val - [false,true].length = (order v).val := by simp
  rw [sub]
  simp [(order v).isLt]

noncomputable def clauseTest (order : V ≃ Fin e) (cl : Clause V) : List (Fin (2+e) × Bool) :=
  cl.toList.map (fun l => (inputWire order l.1, l.2))

omit [Fintype V] [DecidableEq V] in
theorem clauseTestWidth (order : V ≃ Fin e) (cl : Clause V) : (clauseTest order cl).length = cl.card := by
  simp [clauseTest]

theorem clauseTestCorrect (order : V ≃ Fin e) (cl : Clause V) (x : V → Bool) :
    testLiterals (clauseTest order cl) (inputs order x) = true ↔ ¬ ClauseSat x cl := by
  have bit (l : Literal V) : (!( (inputs order x).getD (inputWire order l.1).val false == l.2)) = true ↔
      x l.1 ≠ l.2 := by
    rw [inputValue]
    cases x l.1 <;> cases l.2 <;> decide
  constructor
  · intro value sat
    obtain ⟨l, mem, eq⟩ := sat
    have hit : (inputWire order l.1, l.2) ∈ clauseTest order cl :=
      List.mem_map.mpr ⟨l, Finset.mem_toList.mpr mem, rfl⟩
    exact ((bit l).mp (List.all_eq_true.mp value _ hit)) eq
  · intro noSat
    apply List.all_eq_true.mpr
    intro p mem
    obtain ⟨l, member, rfl⟩ := List.mem_map.mp mem
    exact (bit l).mpr (fun eq => noSat ⟨l, Finset.mem_toList.mp member, eq⟩)

def code (order : V ≃ Fin e) (H : Circuit) (pick : Fin b → Fin (2+e+H.size)) (x : V → Bool) :
    Fin b → ZMod 2 := fun j => ((H.wires (inputs order x)).getD (pick j).val false).toNat

def Compiled (order : V ≃ Fin e) (F : Set (Clause V)) (work : Finset (Clause V))
    (S : Finset (Fin b → ZMod 2)) (cap : (Fin b → ZMod 2) → ℕ) (T : ℕ) : Prop :=
  ∃ (H : Circuit) (pick : Fin b → Fin (2+e+H.size)) (out : (Fin b → ZMod 2) → Finset (Clause V)),
    ReadsBack (2+e) H ∧ (∀ g ∈ H.gates, Shape g) ∧ cost H.gates ≤ T ∧
    (∀ y ∈ S, (out y).card ≤ cap y ∧ ∀ cl ∈ out y, cl ∈ F) ∧
    ∀ x, code order H pick x ∈ S ∧
      ((∀ cl ∈ out (code order H pick x), ClauseSat x cl) → ∀ cl ∈ work, ClauseSat x cl)

theorem compileConstant (order : V ≃ Fin e) (F : Set (Clause V)) (work : Finset (Clause V))
    (subset : ∀ cl ∈ work, cl ∈ F) (S : Finset (Fin b → ZMod 2)) (cap : (Fin b → ZMod 2) → ℕ)
    (nonempty : S.Nonempty) (room : work.card ≤ S.sup cap) (T : ℕ) : Compiled order F work S cap T := by
  classical
  obtain ⟨word, allowed, capacity⟩ := Finset.exists_mem_eq_sup S nonempty cap
  obtain ⟨H, pick, empty, reads, hw⟩ := ClauseSearchUpper.constantMessage (n := 2+e) (by omega) word
  let out (y : Fin b → ZMod 2) := if y = word then work else ∅
  have fixed (x : V → Bool) : code order H pick x = word :=
    funext (hw (inputs order x) (by simp [inputs]) (inputsOne order x))
  refine ⟨H, pick, out, reads, ?_, ?_, ?_, ?_⟩
  · simp [empty]
  · simp [empty, cost]
  · intro y hy
    by_cases eq : y = word
    · subst y
      simpa [out, ← capacity] using And.intro room subset
    · simp [out, eq]
  · intro x
    rw [fixed]
    exact ⟨allowed, by simp [out]⟩

private theorem parityFree (gs : List Gate) (only : ∀ g ∈ gs, g.op = .mod 2) : cost gs = 0 := by
  unfold cost
  rw [List.countP_eq_zero]
  intro g hg
  simp [nonlinear, only g hg]

def variablesUsed (work : Finset (Clause V)) : Finset V :=
  work.biUnion (fun cl => cl.image Prod.fst)

private theorem variablesBound (work : Finset (Clause V)) (w : ℕ)
    (width : ∀ cl ∈ work, cl.card ≤ w) : (variablesUsed work).card ≤ w*work.card := by
  unfold variablesUsed
  calc
    _ ≤ ∑ cl ∈ work, (cl.image Prod.fst).card := Finset.card_biUnion_le
    _ ≤ ∑ _cl ∈ work, w := Finset.sum_le_sum (fun cl hc => Finset.card_image_le.trans (width cl hc))
    _ = _ := by simp [Nat.mul_comm]

private theorem satReplays (work : Finset (Clause V)) {x z : V → Bool}
    (agree : ∀ v ∈ variablesUsed work, x v = z v) {cl : Clause V} (mem : cl ∈ work)
    (sat : ClauseSat x cl) : ClauseSat z cl := by
  obtain ⟨l, hl, val⟩ := sat
  have relevant : l.1 ∈ variablesUsed work := Finset.mem_biUnion.mpr ⟨cl, mem, Finset.mem_image_of_mem _ hl⟩
  exact ⟨l, hl, (agree l.1 relevant).symm.trans val⟩

theorem compileAffine (order : V ≃ Fin e) (F : Set (Clause V)) (work : Finset (Clause V))
    (subset : ∀ cl ∈ work, cl ∈ F) (w : ℕ) (width : ∀ cl ∈ work, cl.card ≤ w)
    (S : Finset (Fin b → ZMod 2)) (cap : (Fin b → ZMod 2) → ℕ)
    (positive : ∀ y ∈ S, 1 ≤ cap y) (U : Submodule (ZMod 2) (Fin b → ZMod 2))
    (origin : Fin b → ZMod 2) (allowed : ∀ u ∈ U, origin + u ∈ S)
    (room : w*work.card ≤ Module.finrank (ZMod 2) U) (T : ℕ) : Compiled order F work S cap T := by
  classical
  let vars := variablesUsed work
  let basis := Module.finBasis (ZMod 2) U
  obtain ⟨index⟩ : Nonempty (vars ↪ Fin (Module.finrank (ZMod 2) U)) :=
    Function.Embedding.nonempty_of_card_le (by
      simp only [Fintype.card_coe, Fintype.card_fin]
      exact (variablesBound work w width).trans room)
  let packed (x : V → Bool) : U := ∑ v : vars, ((x v.val).toNat : ZMod 2) • basis (index v)
  let word (x : V → Bool) := origin + (packed x).val
  have sameBits (x z : V → Bool) (same : word x = word z) (v : vars) : x v.val = z v.val := by
    have samePack : packed x = packed z := Subtype.ext (add_left_cancel same)
    have unpack (x : V → Bool) : basis.coord (index v) (packed x) = ((x v.val).toNat : ZMod 2) := by
      rw [show packed x = ∑ q : vars, ((x q.val).toNat : ZMod 2) • basis (index q) from rfl, map_sum]
      rw [Finset.sum_eq_single v]
      · simp [Module.Basis.coord_apply]
      · intro j _ diff
        have ne : index v ≠ index j := fun same => diff (index.injective same).symm
        simp [Module.Basis.coord_apply, Finsupp.single_apply, ne]
      · intro h
        exact (h (Finset.mem_univ v)).elim
    have bits := congrArg (basis.coord (index v)) samePack
    rw [unpack x, unpack z] at bits
    have injectiveBit : ∀ a z : Bool, (a.toNat : ZMod 2) = (z.toNat : ZMod 2) → a = z := by decide
    exact injectiveBit _ _ bits
  let idx := Fintype.equivFin vars
  let raw (i : Fin (Fintype.card vars)) : Fin (2+e+([ ] : List Gate).length) := inputWire order (idx.symm i).val
  let coeff (j : Fin b) (i : Fin (Fintype.card vars)) := (basis (index (idx.symm i))).val j
  obtain ⟨tail, pick, reads, only, eval⟩ := appendAffineEncoder (n := 2+e) (by omega) [] (emptyLegal _).1 raw origin coeff
  let H : Circuit := ⟨[]++tail,0⟩
  have encode (x : V → Bool) : code order H pick x = word x := by
    funext j
    have h := eval (inputs order x) (inputsLength order x) (inputsOne order x) j
    change code order H pick x j = origin j + ∑ i, coeff j i *
      (((inputs order x).getD (inputWire order (idx.symm i).val).val false).toNat : ZMod 2) at h
    rw [h]
    simp_rw [inputValue]
    change origin j + ∑ i, coeff j i * ((x (idx.symm i).val).toNat : ZMod 2) = origin j + (packed x).val j
    congr 1
    have right : (packed x).val j = ∑ v : vars, (basis (index v)).val j * ((x v.val).toNat : ZMod 2) := by
      simp [packed, Finset.sum_apply, mul_comm]
    rw [right]
    exact Equiv.sum_comp idx.symm (fun v : vars => (basis (index v)).val j * ((x v.val).toNat : ZMod 2))
  let bad (y : Fin b → ZMod 2) := ∃ cl ∈ work, ∃ x, word x = y ∧ ¬ ClauseSat x cl
  let out (y : Fin b → ZMod 2) : Finset (Clause V) := if h : bad y then {Classical.choose h} else ∅
  refine ⟨H, pick, out, reads, ?_, ?_, ?_, ?_⟩
  · intro g hg
    exact Or.inr (Or.inl (only g hg))
  · change cost tail ≤ T
    rw [parityFree tail only]
    exact Nat.zero_le _
  · intro y hy
    by_cases h : bad y
    · have one := positive y hy
      have inside := subset _ (Classical.choose_spec h).1
      simp [out, h, one, inside]
    · simp [out, h]
  · intro x
    rw [encode]
    refine ⟨allowed (packed x).val (packed x).property, ?_⟩
    intro sat cl member
    by_contra missing
    have someBad : bad (word x) := ⟨cl, member, x, rfl, missing⟩
    obtain ⟨inside, z, sameCode, falsified⟩ := Classical.choose_spec someBad
    have chosen : Classical.choose someBad ∈ out (word x) := by simp [out, someBad]
    exact falsified (satReplays work (fun v hv => sameBits x z sameCode.symm ⟨v,hv⟩) inside (sat _ chosen))

private theorem mappedEntry {A B : Type} (items : List A) (f : A → B) (i : Fin items.length) (d : B) :
    (items.map f).getD i.val d = f (items.get i) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem i.isLt]
  rfl

theorem compileNonlinear (order : V ≃ Fin e) (F : Set (Clause V)) (work : Finset (Clause V))
    (subset : ∀ cl ∈ work, cl ∈ F) (w : ℕ) (width : ∀ cl ∈ work, cl.card ≤ w)
    (S : Finset (Fin b → ZMod 2)) (cap : (Fin b → ZMod 2) → ℕ)
    (nonempty : S.Nonempty) (totalRoom : work.card ≤ ∑ y ∈ S, cap y)
    (T : ℕ) (gateRoom : (w+2)*work.card ≤ T) : Compiled order F work S cap T := by
  classical
  obtain ⟨startWord, startOK⟩ := nonempty
  obtain ⟨assign, out, assigns, inside, budgets⟩ := ClauseSearchUpper.assignLists work S cap totalRoom
  let items := work.toList
  let tests := items.map (clauseTest order)
  let run := scan (2+e) tests [] 1
  obtain ⟨_, legal, listLength, earlier, counted, eval⟩ :=
    scanCorrect (n := 2+e) (by omega) tests [] 1 (emptyLegal _) (by change 1 < 2+e; omega)
  have count : run.2.length = items.length := by simpa only [tests, List.length_map] using listLength
  let get (i : Fin items.length) : work := ⟨items.get i, Finset.mem_toList.mp (List.get_mem items i)⟩
  let atFlag (i : Fin items.length) : Fin run.2.length := Fin.cast count.symm i
  let wire (i : Fin items.length) : Fin (2+e+run.1.length) :=
    ⟨run.2.get (atFlag i), earlier _ (List.get_mem _ (atFlag i))⟩
  let target (i : Fin items.length) := assign (get i)
  let coeff (j : Fin b) (i : Fin items.length) := target i j - startWord j
  obtain ⟨tail, pick, reads, only, hCode⟩ :=
    appendAffineEncoder (n := 2+e) (by omega) run.1 legal.1 wire startWord coeff
  let H : Circuit := ⟨run.1++tail, 0⟩
  let bits (x : V → Bool) := tests.map (fun t => testLiterals t (inputs order x))
  have size (x : V → Bool) : (bits x).length = items.length := by simp [bits, tests]
  have fails (x : V → Bool) (i : Fin items.length) :
      (bits x).getD i.val false = true ↔ ¬ ClauseSat x (get i).val := by
    have h : (bits x).getD i.val false = testLiterals (clauseTest order (items.get i)) (inputs order x) := by
      dsimp [bits, tests]
      rw [List.map_map]
      exact mappedEntry items _ i false
    rw [h]
    exact clauseTestCorrect order _ x
  have flag (x : V → Bool) (i : Fin items.length) :
      (wiresOf run.1 (inputs order x)).getD (wire i).val false = (firstFlags true (bits x)).getD i.val false := by
    have h := eval (inputs order x) (inputsLength order x) (inputsOne order x)
    change run.2.map (fun a => (wiresOf run.1 (inputs order x)).getD a false) = firstFlags true (bits x) at h
    have value := congrArg (fun l : List Bool => l.getD (atFlag i).val false) h
    rw [mappedEntry run.2 _ (atFlag i) false] at value
    exact value
  have expands (x : V → Bool) (j : Fin b) : code order H pick x j = startWord j +
      ∑ i : Fin items.length, coeff j i * (((firstFlags true (bits x)).getD i.val false).toNat : ZMod 2) := by
    have h := hCode (inputs order x) (inputsLength order x) (inputsOne order x) j
    change code order H pick x j = _ at h
    simpa only [flag x] using h
  refine ⟨H, pick, out, reads, ?_, ?_, ?_, ?_⟩
  · intro g mem
    rcases List.mem_append.mp mem with mid | extra
    · exact legal.2 _ mid
    · exact Or.inr (Or.inl (only _ extra))
  · change cost (run.1++tail) ≤ T
    have firstCost : cost (run.1++tail) = cost run.1 := by
      have zero := parityFree tail only
      unfold cost at *
      rw [List.countP_append, zero, Nat.add_zero]
    rw [firstCost]
    have amount : (tests.map (fun t => t.length+2)).sum = ∑ cl ∈ work, ((clauseTest order cl).length+2) := by
      simpa only [tests, items, List.map_map, Function.comp_def] using
        sumListOfFinset work (fun cl => (clauseTest order cl).length+2)
    have bound : cost run.1 ≤ (w+2)*work.card := calc
      _ = ∑ cl ∈ work, ((clauseTest order cl).length+2) := by simpa [cost, amount] using counted
      _ ≤ ∑ _cl ∈ work, (w+2) := Finset.sum_le_sum (fun cl mem => by
        rw [clauseTestWidth]; exact Nat.add_le_add_right (width cl mem) _)
      _ = _ := by simp [Nat.mul_comm]
    exact bound.trans gateRoom
  · intro y mem
    exact ⟨budgets y mem, fun cl hit => subset _ (inside y hit)⟩
  · intro x
    rcases firstFlagsCases (bits x) with none | ⟨k, hk, selected, others⟩
    · have word : code order H pick x = startWord := by
        funext j
        rw [expands]
        have off (i : Fin items.length) : (firstFlags true (bits x)).getD i.val false = false :=
          (none i.val (by rw [size]; exact i.isLt)).2
        simp only [off, Bool.toNat_false, Nat.cast_zero, mul_zero, Finset.sum_const_zero, add_zero]
      refine ⟨word.symm ▸ startOK, fun _ cl hc => ?_⟩
      by_contra h
      obtain ⟨i, eq⟩ := List.mem_iff_get.mp (Finset.mem_toList.mpr hc : cl ∈ items)
      have no : ¬ ClauseSat x (get i).val := by
        change ¬ ClauseSat x (items.get i)
        rw [eq]
        exact h
      have hit := (fails x i).mpr no
      exact Bool.noConfusion ((none i.val (by rw [size]; exact i.isLt)).1.symm.trans hit)
    · let q : Fin items.length := ⟨k, by rwa [size] at hk⟩
      have word : code order H pick x = target q := by
        funext j
        rw [expands, Finset.sum_eq_single q]
        · rw [others k hk]
          simp only [decide_true, Bool.toNat_true, Nat.cast_one, mul_one, coeff]
          abel
        · intro i _ diff
          have ne : i.val ≠ k := fun equal => diff (Fin.ext equal)
          rw [others i.val (by rw [size]; exact i.isLt)]
          simp [ne]
        · intro miss
          exact (miss (Finset.mem_univ q)).elim
      have violated : ¬ ClauseSat x (get q).val := (fails x q).mp selected
      rw [word]
      exact ⟨(assigns (get q)).1, fun sat => (violated (sat _ (assigns (get q)).2)).elim⟩

end ClauseSearchRealize

namespace ClauseSearchBudget

open PEqualNP.ProofComplexity PEqualNP.Expanders PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover
open ClauseSearchUpper ClauseSearchScanner ClauseSearchRealize

noncomputable def flatSize {b : ℕ} (S : Finset (Fin b → ZMod 2)) : ℕ :=
  sSup {k : ℕ | ∃ (U : Submodule (ZMod 2) (Fin b → ZMod 2)) (y : Fin b → ZMod 2),
    Module.finrank (ZMod 2) U = k ∧ ∀ u ∈ U, y + u ∈ S}

theorem flatAttained {b : ℕ} (S : Finset (Fin b → ZMod 2)) (nonempty : S.Nonempty) :
    ∃ (U : Submodule (ZMod 2) (Fin b → ZMod 2)) (y : Fin b → ZMod 2),
      Module.finrank (ZMod 2) U = flatSize S ∧ ∀ u ∈ U, y + u ∈ S := by
  let D : Set ℕ := {k | ∃ (U : Submodule (ZMod 2) (Fin b → ZMod 2)) (y : Fin b → ZMod 2),
    Module.finrank (ZMod 2) U = k ∧ ∀ u ∈ U, y + u ∈ S}
  have bounded : BddAbove D := by
    refine ⟨b, ?_⟩
    rintro k ⟨U, _, rfl, _⟩
    simpa using Submodule.finrank_le U
  have inhabited : D.Nonempty := by
    obtain ⟨y, mem⟩ := nonempty
    refine ⟨0, ⊥, y, by simp, ?_⟩
    intro u zero
    have eq : u = 0 := zero
    simpa [eq] using mem
  exact Nat.sSup_mem inhabited bounded

theorem compileFromBudget {V : Type} [Fintype V] [DecidableEq V] {e b : ℕ}
    (order : V ≃ Fin e) (F : Set (Clause V)) (work : Finset (Clause V))
    (subset : ∀ cl ∈ work, cl ∈ F) (w : ℕ) (width : ∀ cl ∈ work, cl.card ≤ w)
    (S : Finset (Fin b → ZMod 2)) (cap : (Fin b → ZMod 2) → ℕ)
    (nonempty : S.Nonempty) (positive : ∀ y ∈ S, 1 ≤ cap y) (T : ℕ)
    (budget : 3*((w+2)*work.card) ≤ min (∑ y ∈ S, cap y) (T+S.sup cap+flatSize S)) :
    Compiled order F work S cap T := by
  let price := (w+2)*work.card
  have combined := (le_min_iff.mp budget).2
  have lePrice : work.card ≤ price := by
    simpa using (Nat.mul_le_mul_right work.card (by omega : 1 ≤ w+2))
  have affineLe : w*work.card ≤ price := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  by_cases listRoom : work.card ≤ S.sup cap
  · exact compileConstant order F work subset S cap nonempty listRoom T
  by_cases wordRoom : w*work.card ≤ flatSize S
  · obtain ⟨U, origin, dimension, allowed⟩ := flatAttained S nonempty
    exact compileAffine order F work subset w width S cap positive U origin allowed (by rwa [dimension]) T
  have enoughGates : price ≤ T := by
    change 3*price ≤ T+S.sup cap+flatSize S at combined
    omega
  have enoughLists : work.card ≤ ∑ y ∈ S, cap y := by
    have sumBound : 3*price ≤ ∑ y ∈ S, cap y := (le_min_iff.mp budget).1
    omega
  exact compileNonlinear order F work subset w width S cap nonempty enoughLists T enoughGates

noncomputable def satisfyingTests {V : Type} [Fintype V] [DecidableEq V]
    (work : Finset (Clause V)) : Finset (V → Bool) := by
  classical
  exact Finset.univ.filter fun x => ∀ cl ∈ work, ClauseSat x cl

theorem memSatisfyingTests {V : Type} [Fintype V] [DecidableEq V]
    (work : Finset (Clause V)) (x : V → Bool) :
    x ∈ satisfyingTests work ↔ ∀ cl ∈ work, ClauseSat x cl := by
  classical
  simp [satisfyingTests]

def rowVariables {m n : ℕ} (G : BipGraph m n) (i : Fin m) : Finset (GEdge G) :=
  Finset.univ.filter (fun e => e.val.1 = i)

private theorem rowWidth {m n d : ℕ} (G : BipGraph m n) (left : LeftDegLe G d) (i : Fin m) :
    (rowVariables G i).card ≤ d := by
  apply le_trans _ (left i)
  apply Finset.card_le_card_of_injOn (fun e : GEdge G => e.val.2)
  · intro e mem
    have own : e.val.1 = i := (Finset.mem_filter.mp mem).2
    exact own ▸ e.property
  · intro a ha b hb same
    have p : a.val.1 = i := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
    have q : b.val.1 = i := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
    exact Subtype.ext (Prod.ext (p.trans q.symm) same)

private theorem rowDisjoint {m n : ℕ} (G : BipGraph m n) {i j : Fin m} (distinct : i ≠ j) :
    Disjoint (rowVariables G i) (rowVariables G j) :=
  Finset.disjoint_left.mpr (fun _ a b => distinct
    ((Finset.mem_filter.mp a).2.symm.trans (Finset.mem_filter.mp b).2))

private theorem rowSat {m n : ℕ} (G : BipGraph m n) (i : Fin m) (x : GEdge G → Bool)
    (sat : ClauseSat x (pigeonClause G i)) : ∃ z ∈ rowVariables G i, x z = true := by
  obtain ⟨l, hit, value⟩ := sat
  obtain ⟨row, positive⟩ := (Finset.mem_filter.mp hit).2
  exact ⟨l.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, row⟩, value.trans positive⟩

theorem graphTestSet {n d C : ℕ} (G : BipGraph (n+1) n) (positive : 1 ≤ n)
    (left : LeftDegLe G d) (right : RightDegLe G d) (scale : d ≤ C) (R h : ℕ) (ratio : 1 ≤ R) :
    ∃ work : Finset (Clause (GEdge G)),
      (∀ cl ∈ work, cl ∈ funGraphPHP G) ∧
      work.card ≤ (2+3*(d*d)) * min n ((R+1)^C*h) ∧
      ∀ μ : (GEdge G → Bool) → ℝ, SmoothClauseSearch.Smooth μ R →
        (2:ℝ)^h * (∑ x ∈ satisfyingTests work, μ x) ≤ ∑ x, μ x := by
  classical
  let q := (R+1)^C*h
  by_cases exactSearch : n ≤ q
  · refine ⟨graphClauses G, fun cl mem => (memGraphClauses _ _).mp mem, ?_, ?_⟩
    · change (graphClauses G).card ≤ (2+3*(d*d)) * min n q
      rw [min_eq_left exactSearch]
      have small : n+1 ≤ 2*n := by omega
      calc
        _ ≤ n+1+n*(d*d)+(n+1)*(d*d) := graphClauseCount G left right
        _ ≤ 2*n+n*(d*d)+(2*n)*(d*d) :=
          Nat.add_le_add (Nat.add_le_add_right small _) (Nat.mul_le_mul_right _ small)
        _ = _ := by ring
    · intro μ smooth
      have empty : satisfyingTests (graphClauses G) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x mem
        obtain ⟨cl, hf, fail⟩ := graphViolation G (by omega) x
        exact fail ((memSatisfyingTests _ _).mp mem _ ((memGraphClauses _ _).mpr hf))
      rw [empty]
      simpa using smooth.2.1.le
  · have short : q ≤ n+1 := by omega
    let rowId : Fin q → Fin (n+1) := Fin.castLE short
    let work := Finset.univ.image (fun i : Fin q => pigeonClause G (rowId i))
    let rows := List.ofFn (fun i : Fin q => rowVariables G (rowId i))
    refine ⟨work, ?_, ?_, ?_⟩
    · intro cl mem
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp mem
      exact Or.inl (Or.inl ⟨rowId i, rfl⟩)
    · change work.card ≤ (2+3*(d*d)) * min n q
      rw [min_eq_right (by omega : q ≤ n)]
      have enough : work.card ≤ q := Finset.card_image_le.trans_eq (by simp)
      exact enough.trans (by simpa using Nat.mul_le_mul_right q (by omega : 1 ≤ 2+3*(d*d)))
    · intro μ smooth
      have disjoint : rows.Pairwise Disjoint := by
        apply List.pairwise_ofFn.mpr
        intro i j lt
        exact rowDisjoint G (fun same => (ne_of_lt lt) (Fin.ext (congrArg (fun j : Fin (n+1) => j.val) same)))
      have widths (row : Finset (GEdge G)) (mem : row ∈ rows) : row.card ≤ d := by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp mem
        exact rowWidth G left (rowId i)
      have enough : (R+1)^d*h ≤ rows.length := by
        rw [show rows.length = q from List.length_ofFn]
        exact Nat.mul_le_mul_right h (Nat.pow_le_pow_right (by omega) scale)
      have smaller : satisfyingTests work ⊆ SmoothClauseSearch.hitsEveryRow rows := by
        intro x mem
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        intro row inc
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp inc
        exact rowSat G (rowId i) x ((memSatisfyingTests _ _).mp mem _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
      have mass := Finset.sum_le_sum_of_subset_of_nonneg (f := μ) smaller (fun x _ _ => smooth.1 x)
      exact (mul_le_mul_of_nonneg_left mass (by positivity)).trans
        (SmoothClauseSearch.rowTestingAccuracy μ R d h smooth rows disjoint widths enough)

end ClauseSearchBudget

namespace ClauseSearchComplete

open PEqualNP.ProofComplexity

set_option maxHeartbeats 1000000 in
theorem complete : ∃ C n₀ : ℕ, 2 ≤ C ∧ ∀ n : ℕ, n₀ ≤ n →
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
      (possible false → min (n*L) h ≤ C*L*B) ∧
      (C * min n ((R+1)^C*h) ≤ B → possible true) := by
  classical
  obtain ⟨d, n₀, two, family⟩ := ClauseSearchExpanderLower.deskLowerHalf
  let w := max d 2
  let C := max d (3*(w+2)*(2+3*(d*d)))
  have degreeScale : d ≤ C := le_max_left _ _
  have sizeScale : 3*(w+2)*(2+3*(d*d)) ≤ C := le_max_right _ _
  refine ⟨C, max n₀ 1, two.trans degreeScale, ?_⟩
  intro n large
  have nPos : 1 ≤ n := (le_max_right _ _).trans large
  obtain ⟨G, left, right, lower⟩ := family n ((le_max_left _ _).trans large)
  refine ⟨G, fun i => (left i).trans degreeScale, fun j => (right j).trans degreeScale, ?_⟩
  intro V X e F b T h R S cap ratio nonempty positive Y flat B L smooth possible
  constructor
  · intro claimed
    have proved := lower b T h R S cap ratio nonempty positive claimed
    exact proved.trans (Nat.mul_le_mul_right B (Nat.mul_le_mul_right L degreeScale))
  · intro enough
    obtain ⟨work, subset, testSize, accuracy⟩ :=
      ClauseSearchBudget.graphTestSet G nPos left right degreeScale R h ratio
    have width (cl : Clause V) (mem : cl ∈ work) : cl.card ≤ w :=
      ClauseSearchExpanderLower.clauseWidth G left cl (subset cl mem)
    have testsFit : 3*((w+2)*work.card) ≤ B := calc
      _ = (3*(w+2))*work.card := by ring
      _ ≤ (3*(w+2))*((2+3*(d*d))*min n ((R+1)^C*h)) := Nat.mul_le_mul_left _ testSize
      _ = (3*(w+2)*(2+3*(d*d)))*min n ((R+1)^C*h) := by ring
      _ ≤ C*min n ((R+1)^C*h) := Nat.mul_le_mul_right _ sizeScale
      _ ≤ B := enough
    let order : V ≃ Fin e := Fintype.equivFin V
    obtain ⟨H, pick, out, reads, shape, cost, fits, selected⟩ :=
      ClauseSearchBudget.compileFromBudget order F work subset w width S cap nonempty positive T testsFit
    have nonlinear := (ClauseSearchExpanderLower.nonlinearCount H).symm.trans_le cost
    refine ⟨H, pick, out, reads, shape, nonlinear, fits, fun x => (selected x).1, ?_⟩
    let bad : Finset X := Finset.univ.filter (fun x : X =>
      @decide (∀ cl ∈ out (ClauseSearchRealize.code order H pick x), ClauseSat x cl) (Classical.propDecidable _))
    change ∀ μ : X → ℝ, smooth μ → (2 : ℝ)^h * (∑ x ∈ bad, μ x) ≤ ∑ x, μ x
    intro μ hm
    have reduced : bad ⊆ ClauseSearchBudget.satisfyingTests work := by
      intro x mem
      have sat : ∀ cl ∈ out (ClauseSearchRealize.code order H pick x), ClauseSat x cl :=
        @of_decide_eq_true _ (Classical.propDecidable _) (Finset.mem_filter.mp mem).2
      exact (ClauseSearchBudget.memSatisfyingTests _ _).mpr ((selected x).2 sat)
    have more := Finset.sum_le_sum_of_subset_of_nonneg (f := μ) reduced (fun x _ _ => hm.1 x)
    exact (mul_le_mul_of_nonneg_left more (by positivity : (0:ℝ) ≤ (2:ℝ)^h)).trans (accuracy μ hm)

end ClauseSearchComplete

end PEqualNP.Outside.L_pcx_407

theorem PEqualNP.Outside.L_pcx_407 : ∃ C n₀ : ℕ, 2 ≤ C ∧ ∀ n : ℕ, n₀ ≤ n →
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
      (possible false → min (n*L) h ≤ C*L*B) ∧
      (C * min n ((R+1)^C*h) ≤ B → possible true) :=
  PEqualNP.Outside.L_pcx_407.ClauseSearchComplete.complete
