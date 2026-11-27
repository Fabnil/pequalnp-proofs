import CrownRepeatedProfile
import CrownRepeatedDouble

namespace CrownProfileThree.Network

open CrownForks CrownProfiles PnpResearch Finset

variable {I : Type} [DecidableEq I] [Fintype I]

private abbrev Bits := Bool × Bool × Bool

private def group (N : Network I) (b : Bits) : Finset I :=
  univ.filter fun i => N.bits (singletonInput i) = b

def count (N : Network I) (b : Bits) : ℕ := (N.group b).card

private theorem inGroup {N : Network I} {b : Bits} {i : I} (h : i ∈ N.group b) :
    N.bits (singletonInput i) = b := (mem_filter.mp h).2

private theorem twiceInGroup (N : Network I) (b : Bits) (two : N.count b = 2) :
    ∃ i j, i ≠ j ∧ N.bits (singletonInput i) = b ∧ N.bits (singletonInput j) = b := by
  have many : 1 < (N.group b).card := by change 1 < N.count b; omega
  obtain ⟨i, hi, j, hj, ne⟩ := one_lt_card.mp many
  exact ⟨i, j, ne, inGroup hi, inGroup hj⟩

private theorem groupEmpty (N : Network I) (b : Bits) (none : ∀ a, N.bits (singletonInput a) ≠ b) :
    N.count b = 0 := by
  apply card_eq_zero.mpr
  exact eq_empty_iff_forall_notMem.mpr fun a ha => none a (inGroup ha)

private theorem countSum (N : Network I) (f : Bits → ℕ) :
    ∑ i, f (N.bits (singletonInput i)) = ∑ b, N.count b * f b := by
  calc
    _ = ∑ b, ∑ i ∈ N.group b, f (N.bits (singletonInput i)) :=
      (sum_fiberwise univ (fun i => N.bits (singletonInput i)) (fun i => f (N.bits (singletonInput i)))).symm
    _ = _ := sum_congr rfl fun b _ => sum_const_nat (fun i hi => congrArg f (inGroup hi))

private theorem singletonBlocks (N : Network I) (test : ThresholdOn N.forest.eval)
    (reads : ∀ i, N.forest.weight (ones i) ≤ 2)
    (a b : Bits) (single : load a = 1) (double : load b = 2)
    (contains : ∀ k, flag a k ≤ flag b k) (two : N.count a = 2) : N.count b = 0 := by
  obtain ⟨i, j, ne, ip, jp⟩ := N.twiceInGroup a two
  apply N.groupEmpty
  intro k kp
  exact N.repeatedSingletonNoDouble test ne (ip.trans jp.symm) (reads i) (reads j)
    (ip.symm ▸ single) (kp.symm ▸ double) (fun t => by rw [ip, kp]; exact contains t)

private theorem doubleBlocks (N : Network I) (test : ThresholdOn N.forest.eval)
    (reads : ∀ i, N.forest.weight (ones i) ≤ 2) (a b : Bits) (t : Fin 4) (double : load a = 2)
    (later : t ≠ firstStage a) (active : flag a t = true)
    (trigger : flag b (firstStage a) = true) (off : flag b t = false)
    (two : N.count a = 2) : N.count b = 0 := by
  obtain ⟨i, j, ne, ip, jp⟩ := N.twiceInGroup a two
  apply N.groupEmpty
  intro k kp
  have on := N.repeatedDoubleImplication test ne (ip.trans jp.symm) (reads i)
    (ip.symm ▸ double) (t := t) (by rwa [ip]) (by rwa [ip]) k (by rwa [ip, kp])
  rw [kp, off] at on
  contradiction

set_option maxHeartbeats 500000 in
private theorem boundsOfCounts (c p q r pq pr qr : ℕ)
    (pc : p ≤ 2) (qc : q ≤ 2) (rc : r ≤ 2)
    (pqc : pq ≤ 2) (prc : pr ≤ 2) (qrc : qr ≤ 2)
    (ps : p = 2 → pq = 0 ∧ pr = 0)
    (qs : q = 2 → pq = 0 ∧ qr = 0)
    (rs : r = 2 → pr = 0 ∧ qr = 0)
    (pqd : pq = 2 → p = 0 ∧ pr = 0)
    (prd : pr = 2 → p = 0 ∧ pq = 0)
    (qrd : qr = 2 → q = 0 ∧ pq = 0) :
    (c ≤ 3 → c + p + q + r + pq + pr + qr ≤ 9) ∧
      (8 * c + 4 * (p + q + r) + 2 * (pq + pr + qr) ≤ 32 →
        c + p + q + r + pq + pr + qr ≠ 8) := by
  constructor <;> intro h <;> omega

private theorem countBounds (N : Network I) (test : ThresholdOn N.forest.eval)
    (reads : ∀ i, N.forest.weight (ones i) ≤ 2) (full : N.count (true, true, true) = 0) :
    (N.count (false, false, false) ≤ 3 → Fintype.card I ≤ 9) ∧
      ((∑ i : I, 2 ^ (3 - load (N.bits (singletonInput i)))) ≤ 32 → Fintype.card I ≠ 8) := by
  let c := N.count (false, false, false)
  let p := N.count (true, false, false)
  let q := N.count (false, true, false)
  let r := N.count (false, false, true)
  let pq := N.count (true, true, false)
  let pr := N.count (true, false, true)
  let qr := N.count (false, true, true)
  have num : c + p + q + r + pq + pr + qr = Fintype.card I := by
    have h := N.countSum (fun _ => 1)
    simp only [sum_const, smul_eq_mul, Nat.mul_one, card_univ, Fintype.sum_prod_type,
      Fintype.sum_bool, full, Nat.zero_add] at h
    dsimp only [c, p, q, r, pq, pr, qr]
    omega
  have cap (b : Bits) (active : b ≠ (false, false, false)) : N.count b ≤ 2 :=
    N.groupCapacity test reads (N.group b) b (fun _ h => inGroup h) active
  have limits : (c ≤ 3 → c + p + q + r + pq + pr + qr ≤ 9) ∧
      (8 * c + 4 * (p + q + r) + 2 * (pq + pr + qr) ≤ 32 → c + p + q + r + pq + pr + qr ≠ 8) := by
    apply boundsOfCounts c p q r pq pr qr
      (cap _ (by decide)) (cap _ (by decide)) (cap _ (by decide))
      (cap _ (by decide)) (cap _ (by decide)) (cap _ (by decide))
    · intro two
      exact ⟨N.singletonBlocks test reads _ _ (by decide) (by decide) (by decide) two,
        N.singletonBlocks test reads _ _ (by decide) (by decide) (by decide) two⟩
    · intro two
      exact ⟨N.singletonBlocks test reads _ _ (by decide) (by decide) (by decide) two,
        N.singletonBlocks test reads _ _ (by decide) (by decide) (by decide) two⟩
    · intro two
      exact ⟨N.singletonBlocks test reads _ _ (by decide) (by decide) (by decide) two,
        N.singletonBlocks test reads _ _ (by decide) (by decide) (by decide) two⟩
    · intro two
      exact ⟨N.doubleBlocks test reads _ _ 1 (by decide) (by decide) (by decide) (by decide) (by decide) two,
        N.doubleBlocks test reads _ _ 1 (by decide) (by decide) (by decide) (by decide) (by decide) two⟩
    · intro two
      exact ⟨N.doubleBlocks test reads _ _ 2 (by decide) (by decide) (by decide) (by decide) (by decide) two,
        N.doubleBlocks test reads _ _ 2 (by decide) (by decide) (by decide) (by decide) (by decide) two⟩
    · intro two
      exact ⟨N.doubleBlocks test reads _ _ 2 (by decide) (by decide) (by decide) (by decide) (by decide) two,
        N.doubleBlocks test reads _ _ 2 (by decide) (by decide) (by decide) (by decide) (by decide) two⟩
  rw [← num]
  refine ⟨limits.1, ?_⟩
  intro h
  rw [N.countSum (fun b => 2 ^ (3 - load b))] at h
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, full, Nat.zero_mul, Nat.zero_add] at h
  simp [load] at h
  apply limits.2
  dsimp only [c, p, q, r, pq, pr, qr]
  omega

theorem noEight (N : Network I) (size : Fintype.card I = 8) (valid : N.forest.Valid)
    (test : ThresholdOn N.forest.eval) (reads : ∀ i, N.forest.weight (ones i) ≤ 2) : False := by
  have full := N.groupEmpty _ (N.noFullProfile size valid test reads)
  exact ((N.countBounds test reads full).2 (N.halfPacking valid test reads univ)) size

private theorem fullForcesSeven (N : Network I) (test : ThresholdOn N.forest.eval)
    (reads : ∀ i, N.forest.weight (ones i) ≤ 2)
    (cold : N.count (false, false, false) ≤ 3) {a : I}
    (full : N.bits (singletonInput a) = (true, true, true)) : Fintype.card I ≤ 7 := by
  apply N.cardLeSevenOfFull test reads _ full
  have coldStage : ∀ b : Bits, firstStage b = 3 ↔ b = (false, false, false) := by decide +kernel
  simpa [count, group, coldStage] using cold

theorem atMostNineOfFewEmpty (N : Network I) (test : ThresholdOn N.forest.eval)
    (reads : ∀ i, N.forest.weight (ones i) ≤ 2) (cold : N.count (false, false, false) ≤ 3) :
    Fintype.card I ≤ 9 := by
  by_contra! big
  have none : N.count (true, true, true) = 0 := N.groupEmpty _ fun a full => by
    have small := N.fullForcesSeven test reads cold full
    omega
  exact (not_le_of_gt big) ((N.countBounds test reads none).1 cold)

end CrownProfileThree.Network

namespace CrownExact

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem crownLower27 : ¬ RepSizeAtMost (fun u v : Fin 8 => decide (u ≠ v)) 26 := by
  intro small
  obtain ⟨p, q, r, h, valid, test, reads⟩ := CrownEight.crown26RequiresThree small
  let net : CrownProfileThree.Network (Fin 8) := ⟨p, q, r, h⟩
  exact net.noEight (by decide) valid test (fun i => (reads i).le)

theorem crownSize27 : RepSizeAtMost (fun u v : Fin 8 => decide (u ≠ v)) 27 ∧
    ¬ RepSizeAtMost (fun u v : Fin 8 => decide (u ≠ v)) 26 :=
  ⟨CrownEight.crownUpper27, crownLower27⟩

end CrownExact
