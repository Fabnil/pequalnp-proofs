import CrownBlocks

namespace CrownQuotient

open CrownThreshold

/-- Rows retain their labels. A column moves to the other group under the
    straight cross-block matching. -/
def column (v : Fin 8) : Fin 8 := Fin.ofNat 8 (v.val + 4)

def adj (u v : Fin 8) : Bool :=
  decide (u.val / 4 ≠ v.val / 4 ∧ u.val % 4 ≠ v.val % 4)

theorem column_twice (v : Fin 8) : column (column v) = v := by
  fin_cases v <;> decide

theorem adj_column (u v : Fin 8) : adj u (column v) = CrownBlocks.adj (blocks := 2) u v := by
  fin_cases u <;> fin_cases v <;> decide

/-- The original promise after the eight ORs tests every quotient pair,
    including singleton inputs and two inputs on the same quotient side. -/
theorem pairedPromise_iff (f : (Fin 8 → Bool) → Bool) :
    (∀ u v : Fin 8, f (pairInput u (column v)) = CrownBlocks.adj (blocks := 2) u v) ↔
      ∀ u v : Fin 8, f (pairInput u v) = adj u v := by
  constructor
  · intro h u v
    have result := h u (column v)
    rw [column_twice] at result
    rw [← adj_column u (column v), column_twice] at result
    exact result
  · intro h u v
    exact (h u (column v)).trans (adj_column u v)

/-- Every pair of flags is tested, and exchanging the two flags leaves the
    input of the residual circuit unchanged. -/
theorem pairedTests_symmetric {blocks : ℕ} (f : (Fin (4 * blocks) → Bool) → Bool)
    (mate : Fin (4 * blocks) → Fin (4 * blocks))
    (tests : ∀ u v, f (pairInput u v) = CrownBlocks.adj u (mate v))
    (u v : Fin (4 * blocks)) : CrownBlocks.adj u (mate v) = CrownBlocks.adj v (mate u) := by
  rw [← tests u v, ← tests v u]
  congr 1
  funext i
  simp [pairInput, or_comm]

private theorem commonNeighbor {blocks : ℕ} (u v : Fin (4 * blocks))
    (same : u.val / 4 = v.val / 4) :
    ∃ c, CrownBlocks.adj u c = true ∧ CrownBlocks.adj v c = true := by
  have chooseLabel (i j : Fin 4) : ∃ l : Fin 4, l ≠ i ∧ l ≠ j := by
    fin_cases i <;> fin_cases j <;> decide
  obtain ⟨l, left, right⟩ :=
    chooseLabel ⟨u.val % 4, by omega⟩ ⟨v.val % 4, by omega⟩
  have ul : u.val % 4 ≠ l.val := by
    intro eq
    exact left (Fin.ext eq.symm)
  have vl : v.val % 4 ≠ l.val := by
    intro eq
    exact right (Fin.ext eq.symm)
  let c : Fin (4 * blocks) := ⟨4 * (u.val / 4) + l.val, by
    have := u.isLt
    have := l.isLt
    omega⟩
  have cb : c.val / 4 = u.val / 4 := by
    have := l.isLt
    dsimp [c]
    omega
  have cl : c.val % 4 = l.val := by
    have := l.isLt
    dsimp [c]
    omega
  exact ⟨c, by simp [CrownBlocks.adj, cb, cl, ul], by
    simp [CrownBlocks.adj, cb, cl, same, vl]⟩

/-- A complete row-column pairing makes adjacent and transposed tests
    agree. Two rows in one block must then have their mates in one block. -/
theorem pairedMates_sameBlock {blocks : ℕ}
    (mate : Fin (4 * blocks) ≃ Fin (4 * blocks))
    (symm : ∀ u v, CrownBlocks.adj u (mate v) = CrownBlocks.adj v (mate u))
    (u v : Fin (4 * blocks)) (same : u.val / 4 = v.val / 4) :
    (mate u).val / 4 = (mate v).val / 4 := by
  obtain ⟨c, left, right⟩ := commonNeighbor u v same
  let r := mate.symm c
  have swapped (x : Fin (4 * blocks)) (edge : CrownBlocks.adj x c = true) :
      r.val / 4 = (mate x).val / 4 := by
    have result := (symm x r).symm
    rw [show mate r = c by exact mate.apply_symm_apply c, edge] at result
    exact (of_decide_eq_true result).1
  exact (swapped u left).symm.trans (swapped v right)

theorem pairedMates_blockInvolution {blocks : ℕ}
    (mate : Fin (4 * blocks) ≃ Fin (4 * blocks))
    (symm : ∀ u v, CrownBlocks.adj u (mate v) = CrownBlocks.adj v (mate u))
    (u : Fin (4 * blocks)) :
    (mate (mate u)).val / 4 = u.val / 4 := by
  obtain ⟨c, edge, _⟩ := commonNeighbor u u rfl
  let r := mate.symm c
  have mate_r : mate r = c := mate.apply_symm_apply c
  have other : CrownBlocks.adj r (mate u) = true := by
    rw [← symm u r, mate_r, edge]
  have same := (of_decide_eq_true other).1
  have back := pairedMates_sameBlock mate symm r (mate u) same
  rw [mate_r] at back
  exact back.symm.trans (of_decide_eq_true edge).1.symm

/-- A paired label has both a row port and a column port. An unpaired label
    keeps one port when the other is set to zero. -/
def rowKept (missing rows : Finset (Fin 8)) (a : Fin 8) : Prop :=
  a ∉ missing ∨ a ∈ rows

def colKept (missing rows : Finset (Fin 8)) (a : Fin 8) : Prop :=
  a ∉ missing ∨ a ∉ rows

def visible (missing rows : Finset (Fin 8)) (a b : Fin 8) : Prop :=
  (rowKept missing rows a ∧ colKept missing rows b) ∨
    (rowKept missing rows b ∧ colKept missing rows a)

theorem hidden_iff (missing rows : Finset (Fin 8)) (a b : Fin 8) :
    ¬visible missing rows a b ↔ a ∈ missing ∧ b ∈ missing ∧
      ((a ∈ rows ∧ b ∈ rows) ∨ (a ∉ rows ∧ b ∉ rows)) := by
  unfold visible rowKept colKept
  tauto

theorem visible_of_missing_le_two (missing : Finset (Fin 8)) (bound : missing.card ≤ 2) :
    ∃ rows : Finset (Fin 8), ∀ a b, a ≠ b → visible missing rows a b := by
  by_cases nonempty : missing.Nonempty
  · obtain ⟨t, ht⟩ := nonempty
    refine ⟨{t}, fun a b ne => ?_⟩
    by_contra hidden
    obtain ⟨ha, hb, side⟩ := (hidden_iff missing {t} a b).mp hidden
    rcases side with both | neither
    · exact ne ((Finset.mem_singleton.mp both.1).trans (Finset.mem_singleton.mp both.2).symm)
    · have included : ({a, b} : Finset (Fin 8)) ⊆ missing.erase t := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_erase.mpr ⟨by simpa using neither.1, ha⟩
        · exact Finset.mem_erase.mpr ⟨by simpa using neither.2, hb⟩
      have count := Finset.card_le_card included
      simp [ne, Finset.card_erase_of_mem ht] at count
      omega
  · have empty := Finset.not_nonempty_iff_eq_empty.mp nonempty
    subst missing
    exact ⟨∅, fun _ _ _ => by simp [visible, rowKept, colKept]⟩

private theorem pairInput_comm (a b : Fin 8) : pairInput a b = pairInput b a := by
  funext i
  simp [pairInput, or_comm]

private theorem adj_comm (a b : Fin 8) : adj a b = adj b a := by
  unfold adj
  congr 1
  exact propext ⟨fun ⟨p, q⟩ => ⟨p.symm, q.symm⟩, fun ⟨p, q⟩ => ⟨p.symm, q.symm⟩⟩

private theorem negative_partner (a : Fin 8) : ∃ b : Fin 8, b ≠ a ∧ adj a b = false := by
  fin_cases a <;> decide

/-- Visible pairs keep their prescribed value. Each singleton also keeps its
    value when it has a visible negative superset. -/
theorem quotient_on_visible {f : (Fin 8 → Bool) → Bool} {missing rows : Finset (Fin 8)}
    (mono : ∀ x y, (∀ i, x i ≤ y i) → f x ≤ f y)
    (negatives : ∀ a, ∃ b, visible missing rows a b ∧ adj a b = false)
    (values : ∀ a b, rowKept missing rows a → colKept missing rows b →
      f (pairInput a b) = adj a b) :
    (∀ a b, visible missing rows a b → f (pairInput a b) = adj a b) ∧
      ∀ a, f (pairInput a a) = false := by
  have pair (a b : Fin 8) (visiblePair : visible missing rows a b) : f (pairInput a b) = adj a b := by
    rcases visiblePair with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · exact values a b ha hb
    · rw [pairInput_comm a b, adj_comm a b]
      exact values b a hb ha
  refine ⟨pair, fun a => ?_⟩
  obtain ⟨b, seen, neg⟩ := negatives a
  have pointwise (i : Fin 8) : pairInput a a i ≤ pairInput a b i := by
    by_cases h : i = a <;> simp [pairInput, h]
  have lower := mono (pairInput a a) (pairInput a b) pointwise
  rw [pair a b seen, neg] at lower
  exact Bool.eq_false_of_le_false lower

/-- Keeping opposite ports for at most two missing pairs gives the full
    quotient promise. Monotonicity supplies the singleton tests. -/
theorem quotient_of_visible {f : (Fin 8 → Bool) → Bool} {missing rows : Finset (Fin 8)}
    (mono : ∀ x y, (∀ i, x i ≤ y i) → f x ≤ f y)
    (covers : ∀ a b, a ≠ b → visible missing rows a b)
    (values : ∀ a b, rowKept missing rows a → colKept missing rows b →
      f (pairInput a b) = adj a b) :
    ∀ a b, f (pairInput a b) = adj a b := by
  obtain ⟨pair, singleton⟩ := quotient_on_visible mono (fun a => by
    obtain ⟨b, ne, neg⟩ := negative_partner a
    exact ⟨b, covers a b ne.symm, neg⟩) values
  intro a b
  by_cases eq : a = b
  · subst b
    simpa [adj] using singleton a
  · exact pair a b (covers a b eq)

end CrownQuotient
