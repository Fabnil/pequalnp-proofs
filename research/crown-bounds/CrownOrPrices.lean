import CrownOrOrigins

namespace CrownOrPrices

open CrownFourNetwork CrownFourNormal CrownPairFormula CrownAllOrModel CrownOrSupport CrownOrGraph
open CrownOrOrigins CrownOrPacking Finset

def degree (g : Fin 64) (t : Fin 4) : ℕ := (CrownOrProfiles.successors g.val t.val).length

private theorem degree_bits : ∀ g : Fin 64,
    degree g 0 = (g.val.testBit 0).toNat + (g.val.testBit 1).toNat + (g.val.testBit 2).toNat ∧
    degree g 1 = (g.val.testBit 3).toNat + (g.val.testBit 4).toNat ∧
    degree g 2 = (g.val.testBit 5).toNat ∧ degree g 3 = 0 := by decide +kernel

private theorem use_le {I : Type} [DecidableEq I] (N : Network I) (s : Fin 3) (t : Fin 4) :
    (uses N s t).toNat ≤ N.readsFlag s t := by
  cases use : uses N s t
  · exact Nat.zero_le _
  · exact of_decide_eq_true use

variable {N : Network Ten}

theorem graph_read_budget (C : Case N) (k : Flag) :
    reads (output N) (.inl k) + degree (graph N) (stage k) ≤ 2 := by
  obtain ⟨d0, d1, d2, d3⟩ := degree_bits (graph N)
  have e0 : (graph N).val.testBit 0 = uses N 0 1 := (word6_bits _ _ _ _ _ _).1
  have e1 : (graph N).val.testBit 1 = uses N 0 2 := (word6_bits _ _ _ _ _ _).2.1
  have e2 : (graph N).val.testBit 2 = uses N 0 3 := (word6_bits _ _ _ _ _ _).2.2.1
  have e3 : (graph N).val.testBit 3 = uses N 1 2 := (word6_bits _ _ _ _ _ _).2.2.2.1
  have e4 : (graph N).val.testBit 4 = uses N 1 3 := (word6_bits _ _ _ _ _ _).2.2.2.2.1
  have e5 : (graph N).val.testBit 5 = uses N 2 3 := (word6_bits _ _ _ _ _ _).2.2.2.2.2
  cases k with
  | none =>
    change reads (output N) (.inl none) + degree (graph N) 3 ≤ 2
    rw [output_reads_last N C.valid, d3]
  | some s =>
    have used := earlier_read_budget N C.valid s
    rw [Fin.sum_univ_four] at used
    fin_cases s
    · change reads (output N) (.inl (some 0)) + degree (graph N) 0 ≤ 2
      change reads (output N) (.inl (some 0)) +
        (N.readsFlag 0 0 + N.readsFlag 0 1 + N.readsFlag 0 2 + N.readsFlag 0 3) = 2 at used
      rw [d0, e0, e1, e2]
      have a := use_le N 0 1
      have b := use_le N 0 2
      have c := use_le N 0 3
      omega
    · change reads (output N) (.inl (some 1)) + degree (graph N) 1 ≤ 2
      change reads (output N) (.inl (some 1)) +
        (N.readsFlag 1 0 + N.readsFlag 1 1 + N.readsFlag 1 2 + N.readsFlag 1 3) = 2 at used
      rw [d1, e3, e4]
      have a := use_le N 1 2
      have b := use_le N 1 3
      omega
    · change reads (output N) (.inl (some 2)) + degree (graph N) 2 ≤ 2
      change reads (output N) (.inl (some 2)) +
        (N.readsFlag 2 0 + N.readsFlag 2 1 + N.readsFlag 2 2 + N.readsFlag 2 3) = 2 at used
      rw [d2, e5]
      have a := use_le N 2 3
      omega

theorem degree_cap (C : Case N) (t : Fin 4) : degree (graph N) t ≤ 2 := by
  have eq : stage (stageEquiv.symm t) = t := stageEquiv.apply_symm_apply t
  have budget := graph_read_budget C (stageEquiv.symm t)
  rw [eq] at budget
  omega

set_option maxHeartbeats 1200000 in
private theorem outputReads_eq :
    ∀ (g : Fin 64) (b : Fin 16), CrownOrProfiles.outputReads g.val b.val =
      ∑ k ∈ maskSupport b, (2 - degree g (stage k)) := by decide +kernel

def bound (N : Network Ten) (i : Ten) : ℕ :=
  (2 - (origin N i).count) + CrownOrProfiles.outputReads (graph N).val (actual N i).val

private theorem bound_enough (C : Case N) (i : Ten) :
    reads (output N) (.inr i) + (∑ k ∈ support N i, reads (output N) (.inl k)) ≤ bound N i := by
  unfold bound
  rw [outputReads_eq, mask_support]
  have raw := CrownOrOrigins.read_bound C i
  apply Nat.add_le_add (by omega)
  apply sum_le_sum
  intro k _
  have used := graph_read_budget C k
  omega

private theorem bound_small (i : Ten) : bound N i ≤ 10 := by
  unfold bound
  rw [outputReads_eq, mask_support]
  have slots := card_le_card (subset_univ (support N i))
  rw [card_univ, show Fintype.card Flag = 4 by decide +kernel] at slots
  have sum : (∑ k ∈ support N i, (2 - degree (graph N) (stage k))) ≤ (support N i).card * 2 := by
    calc
      _ ≤ ∑ _k ∈ support N i, (2 : ℕ) := sum_le_sum fun _ _ => Nat.sub_le ..
      _ = _ := by simp
  omega

def cost (N : Network Ten) (i : Ten) : ℕ :=
  CrownOrProfiles.price (graph N).val (close (graph N) (origin N i)) (2 - (origin N i).count)

theorem cost_budget (C : Case N) : ∑ i : Ten, cost N i ≤ 1024 := by
  have mass := profilePacking (output N) (fun i => flagValues N (CrownForks.singletonInput i))
    C.tests univ (bound N) 10 (fun i _ => bound_enough C i) (fun i _ => bound_small i)
  have value (i : Ten) : cost N i = 2 ^ (10 - bound N i) := by
    unfold cost bound CrownOrProfiles.price
    rw [realized C i]
  simpa only [value, show (2 : ℕ) ^ 10 = 1024 by rfl] using mass

end CrownOrPrices
