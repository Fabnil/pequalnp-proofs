import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17798.Forest

variable {α : Type*} [DecidableEq α]

private theorem charge_succ (charge : Finset ℕ) (n : ℕ) :
    ((Finset.range (n + 1)).filter (fun i => i ∈ charge)).card =
      ((Finset.range n).filter (fun i => i ∈ charge)).card + (if n ∈ charge then 1 else 0) := by
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases mem : n ∈ charge <;> simp [mem]

/-- Expand the frontier backwards. A wire carrying more than one element is covered by
one earlier wire, or by two earlier wires when it can be charged. The set of frontier indices
identifies repeated uses of the same wire, so each charge is spent at most once. -/
theorem cover_card_le (support : ℕ → Finset α) (charge : Finset ℕ) (good : ℕ → Prop)
    (n : ℕ) (F : Finset ℕ)
    (expand : ∀ i < n, good i → 1 < (support i).card →
      ∃ P : Finset ℕ, (∀ j ∈ P, j < i ∧ good j) ∧ support i ⊆ P.biUnion support ∧
        P.card ≤ 1 + (if i ∈ charge then 1 else 0))
    (bounded : ∀ i ∈ F, i < n ∧ good i) :
    (F.biUnion support).card ≤ F.card + ((Finset.range n).filter (fun i => i ∈ charge)).card := by
  induction n generalizing F with
  | zero =>
    have empty : F = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
      (fun i hi => Nat.not_lt_zero i (bounded i hi).1)
    simp [empty]
  | succ n ih =>
    have before := fun i (hi : i < n) => expand i (Nat.lt_succ_of_lt hi)
    have cost := charge_succ charge n
    by_cases last : n ∈ F
    · have lower : ∀ i ∈ F.erase n, i < n ∧ good i := by
        intro i hi
        obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hi
        obtain ⟨hb,hg⟩ := bounded i hm
        exact ⟨by omega,hg⟩
      have count := Finset.card_erase_add_one last
      by_cases small : (support n).card ≤ 1
      · have eq : F.biUnion support = support n ∪ (F.erase n).biUnion support := by
          calc
            _ = (insert n (F.erase n)).biUnion support := by rw [Finset.insert_erase last]
            _ = _ := Finset.biUnion_insert
        have combine := Finset.card_union_le (support n) ((F.erase n).biUnion support)
        have tail := ih (F.erase n) before lower
        rw [eq]
        omega
      · obtain ⟨P, prev, subs, costP⟩ :=
          expand n (Nat.lt_succ_self _) (bounded n last).2 (by omega)
        have allEarlier : ∀ i ∈ F.erase n ∪ P, i < n ∧ good i := by
          intro i hi
          rcases Finset.mem_union.mp hi with hi | hi
          · exact lower i hi
          · exact prev i hi
        have sub : F.biUnion support ⊆ (F.erase n ∪ P).biUnion support := by
          intro x hx
          obtain ⟨i, hi, hx⟩ := Finset.mem_biUnion.mp hx
          by_cases eq : i = n
          · subst i
            obtain ⟨j,hj,hx⟩ := Finset.mem_biUnion.mp (subs hx)
            exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_union_right _ hj,hx⟩
          · exact Finset.mem_biUnion.mpr
              ⟨i,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hi⟩),hx⟩
        have hc := Finset.card_le_card sub
        have front := Finset.card_union_le (F.erase n) P
        have tail := ih (F.erase n ∪ P) before allEarlier
        omega
    · have lower : ∀ i ∈ F, i < n ∧ good i := by
        intro i hi
        obtain ⟨hb,hg⟩ := bounded i hi
        have hne : i ≠ n := by rintro rfl; exact last hi
        exact ⟨by omega,hg⟩
      have tail := ih F before lower
      omega

def chargedFor (support : ℕ → Finset α) (unions : Finset ℕ) (N : Finset α) : Finset ℕ :=
  unions.filter (fun i => 1 < (support i).card ∧ support i ⊆ N)

/-- Specialization for a singleton-support circuit with one-wire and union steps. Empty
wires and singleton wires need not be unfolded. -/
theorem neighborhood_cover (support : ℕ → Finset α) (unions : Finset ℕ)
    (n : ℕ) (N : Finset α) (F : Finset ℕ)
    (step : ∀ i < n, 1 < (support i).card →
      (∃ a < i, support i = support a) ∨
      (i ∈ unions ∧ ∃ a < i, ∃ b < i, support i = support a ∪ support b))
    (outputs : ∀ i ∈ F, i < n ∧ support i ⊆ N) :
    (F.biUnion support).card ≤ F.card + (chargedFor support unions N).card := by
  let charge := chargedFor support unions N
  have expand : ∀ i < n, support i ⊆ N → 1 < (support i).card →
      ∃ P : Finset ℕ, (∀ j ∈ P, j < i ∧ support j ⊆ N) ∧ support i ⊆ P.biUnion support ∧
        P.card ≤ 1 + (if i ∈ charge then 1 else 0) := by
    intro i hi inside large
    rcases step i hi large with ⟨a, ha, eq⟩ | ⟨mem, a, ha, b, hb, eq⟩
    · refine ⟨{a}, ?_, ?_, ?_⟩
      · intro j hj
        have : j = a := Finset.mem_singleton.mp hj
        subst j
        exact ⟨ha, eq ▸ inside⟩
      · simp [eq]
      · simp
    · refine ⟨{a,b}, ?_, ?_, ?_⟩
      · have covered : support a ∪ support b ⊆ N := eq ▸ inside
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl
        · exact ⟨ha, Finset.subset_union_left.trans covered⟩
        · exact ⟨hb, Finset.subset_union_right.trans covered⟩
      · simp [eq]
      · have h : i ∈ charge := Finset.mem_filter.mpr ⟨mem,large,inside⟩
        rw [ite_eq_left h]
        exact Finset.card_le_two
  have h := cover_card_le support charge (fun i => support i ⊆ N) n F expand outputs
  have cost : ((Finset.range n).filter (fun i => i ∈ charge)).card ≤ charge.card :=
    Finset.card_le_card (fun _ hi => (Finset.mem_filter.mp hi).2)
  exact h.trans (Nat.add_le_add_left cost _)

open scoped BigOperators

/-- A union gate with at least two supported neighbors can be charged to only one center. -/
theorem charges_sum_le {κ : Type*} (support : ℕ → Finset α) (unions : Finset ℕ)
    (centers : Finset κ) (N : κ → Finset α)
    (overlap : ∀ c ∈ centers, ∀ d ∈ centers, c ≠ d → (N c ∩ N d).card ≤ 1) :
    ∑ c ∈ centers, (chargedFor support unions (N c)).card ≤ unions.card := by
  let charge := fun c => chargedFor support unions (N c)
  have separate : (centers : Set κ).PairwiseDisjoint charge := by
    intro c hc d hd apart
    apply Finset.disjoint_left.mpr
    intro i ic id
    obtain ⟨_,big,covC⟩ := Finset.mem_filter.mp ic
    obtain ⟨_,_,covD⟩ := Finset.mem_filter.mp id
    have small := overlap c (Finset.mem_coe.mp hc) d (Finset.mem_coe.mp hd) apart
    have sub : support i ⊆ N c ∩ N d := fun _ hx => Finset.mem_inter.mpr ⟨covC hx,covD hx⟩
    have compare := Finset.card_le_card sub
    omega
  change ∑ c ∈ centers, (charge c).card ≤ unions.card
  rw [← Finset.card_biUnion separate]
  apply Finset.card_le_card
  intro i hi
  obtain ⟨c,_,hc⟩ := Finset.mem_biUnion.mp hi
  exact (Finset.mem_filter.mp hc).1

theorem neighborhoods_total {κ : Type*} (support : ℕ → Finset α) (unions : Finset ℕ)
    (n : ℕ) (centers : Finset κ) (N : κ → Finset α) (F : κ → Finset ℕ)
    (step : ∀ i < n, 1 < (support i).card →
      (∃ a < i, support i = support a) ∨
      (i ∈ unions ∧ ∃ a < i, ∃ b < i, support i = support a ∪ support b))
    (outputs : ∀ c ∈ centers, ∀ i ∈ F c, i < n ∧ support i ⊆ N c)
    (overlap : ∀ c ∈ centers, ∀ d ∈ centers, c ≠ d → (N c ∩ N d).card ≤ 1) :
    (∑ c ∈ centers, ((F c).biUnion support).card) ≤
      (∑ c ∈ centers, (F c).card) + unions.card := by
  calc
    _ ≤ ∑ c ∈ centers, ((F c).card + (chargedFor support unions (N c)).card) :=
      Finset.sum_le_sum (fun c hc => neighborhood_cover support unions n (N c) (F c) step (outputs c hc))
    _ = (∑ c ∈ centers, (F c).card) + ∑ c ∈ centers, (chargedFor support unions (N c)).card := by
      rw [Finset.sum_add_distrib]
    _ ≤ _ := Nat.add_le_add_left (charges_sum_le support unions centers N overlap) _

end PEqualNP.Outside.L_meta_17798.Forest

namespace PEqualNP.Outside.L_meta_17798.WeightedForest

open scoped BigOperators

variable {α : Type*} [DecidableEq α]

/-- Expand the frontier backwards. A terminal wire can contribute its full support, with
one element paid for by its frontier position and the rest by its weight. At a retaining
step the weight pays for any extra predecessor positions. A frontier is a set of wire
indices, so repeated uses of a wire incur its weight at most once. -/
theorem weighted_cover_card_le (support : ℕ → Finset α) (weight : ℕ → ℕ)
    (good : ℕ → Prop) (n : ℕ) (F : Finset ℕ)
    (expand : ∀ i < n, good i →
      (support i).card ≤ 1 + weight i ∨
      ∃ P : Finset ℕ, (∀ j ∈ P, j < i ∧ good j) ∧ support i ⊆ P.biUnion support ∧
        P.card ≤ 1 + weight i)
    (bounded : ∀ i ∈ F, i < n ∧ good i) :
    (F.biUnion support).card ≤ F.card + ∑ i ∈ Finset.range n, weight i := by
  induction n generalizing F with
  | zero =>
    have empty : F = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
      (fun i hi => Nat.not_lt_zero i (bounded i hi).1)
    simp [empty]
  | succ n ih =>
    have before := fun i (hi : i < n) => expand i (Nat.lt_succ_of_lt hi)
    rw [Finset.sum_range_succ]
    by_cases last : n ∈ F
    · have lower : ∀ i ∈ F.erase n, i < n ∧ good i := by
        intro i hi
        obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hi
        obtain ⟨hb,hg⟩ := bounded i hm
        exact ⟨by omega,hg⟩
      have count := Finset.card_erase_add_one last
      rcases expand n (Nat.lt_succ_self _) (bounded n last).2 with small | ⟨P, prev, subs, costP⟩
      · have eq : F.biUnion support = support n ∪ (F.erase n).biUnion support := by
          calc
            _ = (insert n (F.erase n)).biUnion support := by rw [Finset.insert_erase last]
            _ = _ := Finset.biUnion_insert
        have combine := Finset.card_union_le (support n) ((F.erase n).biUnion support)
        have tail := ih (F.erase n) before lower
        rw [eq]
        omega
      · have allEarlier : ∀ i ∈ F.erase n ∪ P, i < n ∧ good i := by
          intro i hi
          rcases Finset.mem_union.mp hi with hi | hi
          · exact lower i hi
          · exact prev i hi
        have sub : F.biUnion support ⊆ (F.erase n ∪ P).biUnion support := by
          intro x hx
          obtain ⟨i, hi, hx⟩ := Finset.mem_biUnion.mp hx
          by_cases eq : i = n
          · subst i
            obtain ⟨j,hj,hx⟩ := Finset.mem_biUnion.mp (subs hx)
            exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_union_right _ hj,hx⟩
          · exact Finset.mem_biUnion.mpr
              ⟨i,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hi⟩),hx⟩
        have hc := Finset.card_le_card sub
        have front := Finset.card_union_le (F.erase n) P
        have tail := ih (F.erase n ∪ P) before allEarlier
        omega
    · have lower : ∀ i ∈ F, i < n ∧ good i := by
        intro i hi
        obtain ⟨hb,hg⟩ := bounded i hi
        have hne : i ≠ n := by rintro rfl; exact last hi
        exact ⟨by omega,hg⟩
      have tail := ih F before lower
      omega

def chargedFor (support : ℕ → Finset α) (wires : Finset ℕ) (N : Finset α) : Finset ℕ :=
  wires.filter (fun i => 1 < (support i).card ∧ support i ⊆ N)

/-- A large marked wire can be used as a terminal at an extra cost of its support
cardinality minus one. A projection has one predecessor and a union at most two. -/
theorem weighted_neighborhood_cover (support : ℕ → Finset α) (unions exceptions : Finset ℕ)
    (n : ℕ) (N : Finset α) (F : Finset ℕ)
    (step : ∀ i < n, 1 < (support i).card →
      i ∈ exceptions ∨ (∃ a < i, support i = support a) ∨
      (i ∈ unions ∧ ∃ a < i, ∃ b < i, support i = support a ∪ support b))
    (outputs : ∀ i ∈ F, i < n ∧ support i ⊆ N) :
    (F.biUnion support).card ≤ F.card + (chargedFor support unions N).card +
      ∑ i ∈ chargedFor support exceptions N, ((support i).card - 1) := by
  let U := chargedFor support unions N
  let E := chargedFor support exceptions N
  let weight : ℕ → ℕ := fun i =>
    (if i ∈ U then 1 else 0) + (if i ∈ E then (support i).card - 1 else 0)
  have expand : ∀ i < n, support i ⊆ N →
      (support i).card ≤ 1 + weight i ∨
      ∃ P : Finset ℕ, (∀ j ∈ P, j < i ∧ support j ⊆ N) ∧ support i ⊆ P.biUnion support ∧
        P.card ≤ 1 + weight i := by
    intro i hi inside
    by_cases large : 1 < (support i).card
    · rcases step i hi large with mem | ⟨a, ha, eq⟩ | ⟨mem, a, ha, b, hb, eq⟩
      · left
        have member : i ∈ E := Finset.mem_filter.mpr ⟨mem, large, inside⟩
        simp only [weight, ite_eq_left member]
        omega
      · exact Or.inr ⟨{a}, by simpa using And.intro ha (eq ▸ inside), by simp [eq], by simp⟩
      · refine Or.inr ⟨{a, b}, ?_, by simp [eq], ?_⟩
        · have covered : support a ∪ support b ⊆ N := eq ▸ inside
          intro j hj
          simp only [Finset.mem_insert, Finset.mem_singleton] at hj
          rcases hj with rfl | rfl
          · exact ⟨ha, Finset.subset_union_left.trans covered⟩
          · exact ⟨hb, Finset.subset_union_right.trans covered⟩
        · have member : i ∈ U := Finset.mem_filter.mpr ⟨mem, large, inside⟩
          have count : ({a, b} : Finset ℕ).card ≤ 2 := Finset.card_le_two
          simp only [weight, ite_eq_left member]
          omega
    · exact Or.inl (by omega)
  have h := weighted_cover_card_le support weight (fun i => support i ⊆ N) n F expand outputs
  have unionBound : ((Finset.range n).filter (fun i => i ∈ U)).card ≤ U.card :=
    Finset.card_le_card (fun _ hi => (Finset.mem_filter.mp hi).2)
  have exceptionBound : (∑ i ∈ (Finset.range n).filter (fun i => i ∈ E), ((support i).card - 1)) ≤
      ∑ i ∈ E, ((support i).card - 1) :=
    Finset.sum_le_sum_of_subset (fun _ hi => (Finset.mem_filter.mp hi).2)
  simp only [weight, Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const,
    Nat.nsmul_eq_mul, Nat.mul_one] at h
  change _ ≤ F.card + U.card + ∑ i ∈ E, ((support i).card - 1)
  omega

/-- A wire with at least two supported neighbors belongs to at most one of the
charged sets when distinct neighborhoods meet in at most one neighbor. -/
private theorem chargedFor_pairwise_disjoint {κ : Type*} (support : ℕ → Finset α)
    (wires : Finset ℕ) (centers : Finset κ) (N : κ → Finset α)
    (overlap : ∀ c ∈ centers, ∀ d ∈ centers, c ≠ d → (N c ∩ N d).card ≤ 1) :
    (centers : Set κ).PairwiseDisjoint (fun c => chargedFor support wires (N c)) := by
  intro c hc d hd apart
  apply Finset.disjoint_left.mpr
  intro i ic id
  obtain ⟨_, big, covC⟩ := Finset.mem_filter.mp ic
  obtain ⟨_, _, covD⟩ := Finset.mem_filter.mp id
  have small := overlap c (Finset.mem_coe.mp hc) d (Finset.mem_coe.mp hd) apart
  have sub : support i ⊆ N c ∩ N d := fun _ hx => Finset.mem_inter.mpr ⟨covC hx, covD hx⟩
  have compare := Finset.card_le_card sub
  omega

/-- Summing any natural-valued wire costs across the charged sets spends each cost at most once. -/
theorem chargedFor_sum_le {κ : Type*} (support : ℕ → Finset α) (wires : Finset ℕ)
    (centers : Finset κ) (N : κ → Finset α) (cost : ℕ → ℕ)
    (overlap : ∀ c ∈ centers, ∀ d ∈ centers, c ≠ d → (N c ∩ N d).card ≤ 1) :
    (∑ c ∈ centers, ∑ i ∈ chargedFor support wires (N c), cost i) ≤ ∑ i ∈ wires, cost i := by
  rw [← Finset.sum_biUnion (chargedFor_pairwise_disjoint support wires centers N overlap)]
  apply Finset.sum_le_sum_of_subset
  intro i hi
  obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hi
  exact (Finset.mem_filter.mp hc).1

theorem weighted_neighborhoods_total {κ : Type*} (support : ℕ → Finset α)
    (unions exceptions : Finset ℕ) (n : ℕ) (centers : Finset κ)
    (N : κ → Finset α) (F : κ → Finset ℕ) (coverage : κ → Finset α)
    (step : ∀ i < n, 1 < (support i).card →
      i ∈ exceptions ∨ (∃ a < i, support i = support a) ∨
      (i ∈ unions ∧ ∃ a < i, ∃ b < i, support i = support a ∪ support b))
    (outputs : ∀ c ∈ centers, ∀ i ∈ F c, i < n ∧ support i ⊆ N c)
    (covered : ∀ c ∈ centers, coverage c ⊆ (F c).biUnion support)
    (overlap : ∀ c ∈ centers, ∀ d ∈ centers, c ≠ d → (N c ∩ N d).card ≤ 1) :
    (∑ c ∈ centers, (coverage c).card) ≤
      (∑ c ∈ centers, (F c).card) + unions.card + ∑ i ∈ exceptions, ((support i).card - 1) := by
  have unionBound : (∑ c ∈ centers, (chargedFor support unions (N c)).card) ≤ unions.card := by
    simpa using chargedFor_sum_le support unions centers N (fun _ => 1) overlap
  have exceptionBound :=
    chargedFor_sum_le support exceptions centers N (fun i => (support i).card - 1) overlap
  have localBound : (∑ c ∈ centers, (coverage c).card) ≤
      ∑ c ∈ centers, ((F c).card + (chargedFor support unions (N c)).card +
        ∑ i ∈ chargedFor support exceptions (N c), ((support i).card - 1)) :=
    Finset.sum_le_sum fun c hc => (Finset.card_le_card (covered c hc)).trans
      (weighted_neighborhood_cover support unions exceptions n (N c) (F c) step (outputs c hc))
  simp only [Finset.sum_add_distrib] at localBound
  omega

end PEqualNP.Outside.L_meta_17798.WeightedForest

namespace PEqualNP.Outside.L_meta_17798.Trace

abbrev Side (n : ℕ) := Fin n → Bool
abbrev Signal (n : ℕ) := Side n × Side n

def oneHot {n : ℕ} (p : Fin n) : Side n := fun i => decide (i = p)
def off (n : ℕ) : Side n := fun _ => false
def zeroSignal (n : ℕ) : Signal n := (off n, off n)

def Upward {n : ℕ} (X : Set (Signal n)) : Prop :=
  ∀ ⦃u v : Signal n⦄, u ≤ v → u ∈ X → v ∈ X

def Initial {n : ℕ} (W : ℕ → Set (Signal n)) : Prop :=
  ∀ p : Fin n, W p.val = {x | x.1 p = true} ∧ W (n + p.val) = {x | x.2 p = true}

def Pure {n : ℕ} (X Y : Set (Signal n)) : Prop :=
  ∃ A B : Set (Side n), X = A ×ˢ Set.univ ∧ Y = Set.univ ×ˢ B

def Steps {n : ℕ} (s : ℕ) (bad : Finset ℕ) (W : ℕ → Set (Signal n)) : Prop :=
  ∀ j < s, ∃ a b : ℕ, max a b < n + n + j ∧
    (W (n + n + j) ∈ [W a ∪ W b, W a, ∅] ∨
      W (n + n + j) = W a ∩ W b ∧ (j ∈ bad ∨ Pure (W a) (W b)))

theorem wire_mono_zero {n s i : ℕ} {bad : Finset ℕ} {W : ℕ → Set (Signal n)}
    (initial : Initial W) (steps : Steps s bad W) (hi : i < n + n + s) :
    Upward (W i) ∧ zeroSignal n ∉ W i := by
  induction i using Nat.strong_induction_on with
  | ind i earlier =>
    by_cases hp : i < n
    · have h := (initial ⟨i, hp⟩).1
      change W i = {u | u.1 ⟨i, hp⟩ = true} at h
      rw [h]
      refine ⟨?_, by simp [zeroSignal, off]⟩
      intro u v hle hu
      exact Bool.eq_true_of_true_le (hu ▸ hle.1 ⟨i, hp⟩)
    by_cases hl : i < n + n
    · let l : Fin n := ⟨i - n, by omega⟩
      have eq : n + l.val = i := by dsimp [l]; omega
      rw [← eq, (initial l).2]
      refine ⟨?_, by simp [zeroSignal, off]⟩
      intro u v hle hu
      exact Bool.eq_true_of_true_le (hu ▸ hle.2 l)
    · let j := i - (n + n)
      have eq : n + n + j = i := by dsimp [j]; omega
      have hj : j < s := by dsimp [j]; omega
      obtain ⟨a, b, before, form⟩ := steps j hj
      rw [eq] at before form
      have ha : a < i := (le_max_left _ _).trans_lt before
      have hb : b < i := (le_max_right _ _).trans_lt before
      obtain ⟨upA, zeroA⟩ := earlier a ha (ha.trans hi)
      obtain ⟨upB, zeroB⟩ := earlier b hb (hb.trans hi)
      rcases form with choices | ⟨inter, _⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at choices
        rcases choices with disj | copy | empty
        · rw [disj]
          refine ⟨?_, ?_⟩
          · intro u v hle hu
            exact hu.elim (fun ha => Or.inl (upA hle ha)) (fun hb => Or.inr (upB hle hb))
          · exact fun h => h.elim zeroA zeroB
        · rw [copy]
          exact ⟨upA, zeroA⟩
        · rw [empty]
          refine ⟨?_, Set.notMem_empty _⟩
          intro _ _ _ h
          exact False.elim h
      · rw [inter]
        refine ⟨?_, fun h => zeroA h.1⟩
        intro _ _ hle h
        exact ⟨upA hle h.1, upB hle h.2⟩

theorem pure_intersection_vanishes {n : ℕ} {X Y : Set (Signal n)}
    (pure : Pure X Y) (zeroX : zeroSignal n ∉ X) (zeroY : zeroSignal n ∉ Y) :
    (∀ p : Side n, (p, off n) ∉ X ∩ Y) ∧
      (∀ l : Side n, (off n, l) ∉ X ∩ Y) := by
  obtain ⟨A, B, hx, hy⟩ := pure
  have noA : off n ∉ A := by
    intro h
    apply zeroX
    rw [hx]
    exact ⟨h, Set.mem_univ _⟩
  have noB : off n ∉ B := by
    intro h
    apply zeroY
    rw [hy]
    exact ⟨Set.mem_univ _, h⟩
  rw [hx, hy]
  exact ⟨fun _ h => noB h.2.2, fun _ h => noA h.1.1⟩

def lineMass {n : ℕ} (y : Side n) : ℕ := Fintype.card {l : Fin n // y l = true}

def missing {n : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I] (y : Side n) : Side n :=
  fun p => decide (¬ ∃ l, I p l ∧ y l = true)

def Sound {n : ℕ} (q : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I]
    (X : Set (Signal n)) : Prop :=
  ∀ y : Side n, lineMass y ≤ q → (missing I y, y) ∉ X

theorem sound_of_subset {n q : ℕ} {I : Fin n → Fin n → Prop} [DecidableRel I]
    {X Y : Set (Signal n)} (sub : X ⊆ Y) (sound : Sound q I Y) : Sound q I X :=
  fun y hy hx => sound y hy (sub hx)

private theorem lineMass_off (n : ℕ) : lineMass (off n) = 0 := by
  let : IsEmpty {l : Fin n // off n l = true} :=
    ⟨fun l => by simpa only [off, Bool.false_eq_true] using l.property⟩
  exact Fintype.card_of_isEmpty

private theorem lineMass_oneHot {n : ℕ} (j : Fin n) : lineMass (oneHot j) ≤ 1 := by
  let f : {l : Fin n // oneHot j l = true} → Fin 1 := fun _ => 0
  have inj : Function.Injective f := by
    intro a b _
    apply Subtype.ext
    have ha : a.val = j := by simpa [oneHot] using a.property
    have hb : b.val = j := by simpa [oneHot] using b.property
    exact ha.trans hb.symm
  simpa [lineMass] using Fintype.card_le_of_injective f inj

private theorem inputs_not_sound {n q i : ℕ} {I : Fin n → Fin n → Prop} [DecidableRel I]
    {W : ℕ → Set (Signal n)} (initial : Initial W) (hq : 1 ≤ q) (hi : i < n + n) :
    ¬ Sound q I (W i) := by
  intro sound
  by_cases hp : i < n
  · have h := (initial ⟨i, hp⟩).1
    change W i = {u | u.1 ⟨i, hp⟩ = true} at h
    apply sound (off n) (by rw [lineMass_off]; exact Nat.zero_le _)
    rw [h]
    simp [missing, off]
  · let l : Fin n := ⟨i - n, by omega⟩
    have e : n + l.val = i := by dsimp [l]; omega
    apply sound (oneHot l) ((lineMass_oneHot l).trans hq)
    rw [← e, (initial l).2]
    simp [oneHot]

theorem accepting_sound_intersection
    {n q s i : ℕ} {I : Fin n → Fin n → Prop} [DecidableRel I]
    {bad : Finset ℕ} {W : ℕ → Set (Signal n)}
    (initial : Initial W) (steps : Steps s bad W) (hq : 1 ≤ q)
    (hi : i < n + n + s) {u : Signal n} (accepted : u ∈ W i) (sound : Sound q I (W i)) :
    ∃ j < s, ∃ a b : ℕ, max a b < n + n + j ∧
      W (n + n + j) = W a ∩ W b ∧ (j ∈ bad ∨ Pure (W a) (W b)) ∧
      W (n + n + j) ⊆ W i ∧ u ∈ W (n + n + j) ∧ Sound q I (W (n + n + j)) := by
  induction i using Nat.strong_induction_on with
  | ind i earlier =>
    by_cases isInput : i < n + n
    · exact (inputs_not_sound initial hq isInput sound).elim
    let j := i - (n + n)
    have eq : n + n + j = i := by dsimp [j]; omega
    have hj : j < s := by dsimp [j]; omega
    obtain ⟨a, b, before, form⟩ := steps j hj
    rcases form with choices | ⟨inter, tagged⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at choices
      rw [eq] at before choices
      have ha : a < i := (le_max_left _ _).trans_lt before
      have hb : b < i := (le_max_right _ _).trans_lt before
      have useChild (c : ℕ) (hc : c < i) (sub : W c ⊆ W i) (hacc : u ∈ W c) :
          ∃ j < s, ∃ a b : ℕ, max a b < n + n + j ∧
            W (n + n + j) = W a ∩ W b ∧ (j ∈ bad ∨ Pure (W a) (W b)) ∧
              W (n + n + j) ⊆ W i ∧ u ∈ W (n + n + j) ∧ Sound q I (W (n + n + j)) := by
        obtain ⟨j, hj, a, b, earlier, form, tagged, path, mem, leafSound⟩ :=
          earlier c hc (hc.trans hi) hacc (sound_of_subset sub sound)
        exact ⟨j, hj, a, b, earlier, form, tagged, path.trans sub, mem, leafSound⟩
      rcases choices with disj | copy | empty
      · have member : u ∈ W a ∪ W b := disj ▸ accepted
        rcases member with left | right
        · apply useChild a ha _ left
          rw [disj]
          exact Set.subset_union_left
        · apply useChild b hb _ right
          rw [disj]
          exact Set.subset_union_right
      · exact useChild a ha (by rw [copy]) (copy ▸ accepted)
      · exact (Set.notMem_empty u (empty ▸ accepted)).elim
    · refine ⟨j, hj, a, b, before, inter, tagged, ?_, ?_, ?_⟩
      · rw [eq]
      · exact eq.symm ▸ accepted
      · exact eq.symm ▸ sound

theorem sound_singleton_incidence
    {n q : ℕ} {I : Fin n → Fin n → Prop} [DecidableRel I]
    {X : Set (Signal n)} (hq : 1 ≤ q) (up : Upward X) (sound : Sound q I X)
    {p l : Fin n} (mem : (oneHot p, oneHot l) ∈ X) : I p l := by
  by_contra non
  have leMissing : oneHot p ≤ missing I (oneHot l) := by
    intro p'
    by_cases h : p' = p
    · subst p'
      simp [missing, oneHot, non]
    · simp [oneHot, h]
  have pair_le : (oneHot p, oneHot l) ≤ (missing I (oneHot l), oneHot l) :=
    ⟨leMissing, le_rfl⟩
  exact sound (oneHot l) ((lineMass_oneHot l).trans hq) (up pair_le mem)

noncomputable def singletonSupport {n : ℕ} (X : Set (Side n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun p => oneHot p ∈ X)

theorem mem_singletonSupport {n : ℕ} {X : Set (Side n)} {p : Fin n} :
    p ∈ singletonSupport X ↔ oneHot p ∈ X := by
  classical
  simp [singletonSupport]

theorem centered_sound_rectangle
    {n q : ℕ} {I : Fin n → Fin n → Prop} [DecidableRel I]
    (unique : ∀ p p' : Fin n, p ≠ p' → ∃! l : Fin n, I p l ∧ I p' l)
    {X : Set (Signal n)} {A B : Set (Side n)}
    (hq : 1 ≤ q) (up : Upward X) (sound : Sound q I X) (rect : X = A ×ˢ B) :
    (∀ p ∈ singletonSupport A, ∀ l ∈ singletonSupport B, I p l) ∧
      ((singletonSupport A).card ≤ 1 ∨ (singletonSupport B).card ≤ 1) := by
  classical
  have contained : ∀ p ∈ singletonSupport A, ∀ l ∈ singletonSupport B, I p l := by
    intro p hp l hl
    apply sound_singleton_incidence hq up sound
    rw [rect]
    exact ⟨mem_singletonSupport.mp hp, mem_singletonSupport.mp hl⟩
  refine ⟨contained, ?_⟩
  by_cases single : (singletonSupport A).card ≤ 1
  · exact Or.inl single
  · apply Or.inr
    apply Finset.card_le_one.mpr
    intro l hl l' hl'
    obtain ⟨p, hp, p', hp', distinct⟩ := Finset.one_lt_card.mp (lt_of_not_ge single)
    obtain ⟨common, _, un⟩ := unique p p' distinct
    exact (un l ⟨contained p hp l hl, contained p' hp' l hl⟩).trans
      (un l' ⟨contained p hp l' hl', contained p' hp' l' hl'⟩).symm

theorem incident_leaf
    {n q s out : ℕ} {I : Fin n → Fin n → Prop} [DecidableRel I]
    {bad : Finset ℕ} {W : ℕ → Set (Signal n)}
    (initial : Initial W) (steps : Steps s bad W) (hq : 1 ≤ q)
    (unique : ∀ p p' : Fin n, p ≠ p' → ∃! l : Fin n, I p l ∧ I p' l)
    (hout : out < n + n + s) {p l : Fin n}
    (accepted : (oneHot p, oneHot l) ∈ W out) (sound : Sound q I (W out)) :
    ∃ j < s, W (n + n + j) ⊆ W out ∧ (oneHot p, oneHot l) ∈ W (n + n + j) ∧
      (j ∈ bad ∨
        ∃ a b : ℕ, max a b < n + n + j ∧
          ∃ A B : Set (Side n), W a = A ×ˢ Set.univ ∧ W b = Set.univ ×ˢ B ∧
            W (n + n + j) = A ×ˢ B ∧ p ∈ singletonSupport A ∧ l ∈ singletonSupport B ∧
            (∀ p' ∈ singletonSupport A, ∀ l' ∈ singletonSupport B, I p' l') ∧
            ((singletonSupport A).card ≤ 1 ∨ (singletonSupport B).card ≤ 1)) := by
  obtain ⟨j, hj, a, b, earlier, inter, tag, sub, pair, safe⟩ :=
    accepting_sound_intersection initial steps hq hout accepted sound
  refine ⟨j, hj, sub, pair, ?_⟩
  rcases tag with exceptional | ⟨A, B, left, right⟩
  · exact Or.inl exceptional
  · apply Or.inr
    have rect : W (n + n + j) = A ×ˢ B := by
      rw [inter, left, right]
      ext x
      simp
    rw [rect] at pair
    have up := (wire_mono_zero initial steps (show n + n + j < n + n + s by omega)).1
    obtain ⟨contained, centered⟩ := centered_sound_rectangle unique hq up safe rect
    exact ⟨a, b, earlier, A, B, left, right, rect,
      mem_singletonSupport.mpr pair.1, mem_singletonSupport.mpr pair.2, contained, centered⟩

private noncomputable def supportOn {n : ℕ}
    (sample : Fin n → Signal n) (X : Set (Signal n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun p => sample p ∈ X)

@[simp] private theorem mem_supportOn {n : ℕ}
    {sample : Fin n → Signal n} {X : Set (Signal n)} {p : Fin n} :
    p ∈ supportOn sample X ↔ sample p ∈ X := by
  classical
  simp [supportOn]

noncomputable def pointSupport {n : ℕ}
    (W : ℕ → Set (Signal n)) (i : ℕ) : Finset (Fin n) :=
  supportOn (fun p => (oneHot p, off n)) (W i)

noncomputable def lineSupport {n : ℕ}
    (W : ℕ → Set (Signal n)) (i : ℕ) : Finset (Fin n) :=
  supportOn (fun l => (off n, oneHot l)) (W i)

@[simp] theorem mem_pointSupport {n i : ℕ}
    {W : ℕ → Set (Signal n)} {p : Fin n} :
    p ∈ pointSupport W i ↔ (oneHot p, off n) ∈ W i :=
  mem_supportOn

@[simp] theorem mem_lineSupport {n i : ℕ}
    {W : ℕ → Set (Signal n)} {l : Fin n} :
    l ∈ lineSupport W i ↔ (off n, oneHot l) ∈ W i :=
  mem_supportOn

theorem pointSupport_strip {n i : ℕ} {W : ℕ → Set (Signal n)}
    {A : Set (Side n)} (strip : W i = A ×ˢ Set.univ) :
    pointSupport W i = singletonSupport A := by
  ext p
  simp [strip, mem_singletonSupport]

theorem lineSupport_strip {n i : ℕ} {W : ℕ → Set (Signal n)}
    {B : Set (Side n)} (strip : W i = Set.univ ×ˢ B) :
    lineSupport W i = singletonSupport B := by
  ext l
  simp [strip, mem_singletonSupport]

theorem supports_input_point {n : ℕ} {W : ℕ → Set (Signal n)}
    (initial : Initial W) (p : Fin n) :
    pointSupport W p.val = {p} ∧ lineSupport W p.val = ∅ := by
  constructor
  · ext a
    simpa [(initial p).1, oneHot] using (eq_comm : p = a ↔ a = p)
  · ext a
    simp [(initial p).1, off]

theorem supports_input_line {n : ℕ} {W : ℕ → Set (Signal n)}
    (initial : Initial W) (l : Fin n) :
    pointSupport W (n + l.val) = ∅ ∧ lineSupport W (n + l.val) = {l} := by
  constructor
  · ext a
    simp [(initial l).2, off]
  · ext a
    simpa [(initial l).2, oneHot] using (eq_comm : l = a ↔ a = l)

def gateWires (n s : ℕ) : Finset ℕ := Finset.Ico (n + n) (n + n + s)

theorem card_gateWires (n s : ℕ) : (gateWires n s).card = s := by
  simp [gateWires]

def badWires (n s : ℕ) (bad : Finset ℕ) : Finset ℕ :=
  ((Finset.range s ∩ bad).image fun j => n + n + j)

@[simp] theorem badWires_empty (n s : ℕ) : badWires n s ∅ = ∅ := by
  simp [badWires]

theorem mem_badWires {n s i : ℕ} {bad : Finset ℕ} :
    i ∈ badWires n s bad ↔ ∃ j < s, j ∈ bad ∧ n + n + j = i := by
  simp [badWires, and_assoc]

theorem card_badWires_le (n s : ℕ) (bad : Finset ℕ) :
    (badWires n s bad).card ≤ bad.card :=
  Finset.card_image_le.trans (Finset.card_le_card Finset.inter_subset_right)

private theorem supportOn_step_with_bad {n s : ℕ} {bad : Finset ℕ} {W : ℕ → Set (Signal n)}
    {sample : Fin n → Signal n} (initial : Initial W) (steps : Steps s bad W)
    (smallInput : ∀ i < n + n, (supportOn sample (W i)).card ≤ 1)
    (vanishes : ∀ ⦃X Y : Set (Signal n)⦄, Pure X Y → zeroSignal n ∉ X →
      zeroSignal n ∉ Y → ∀ p, sample p ∉ X ∩ Y) :
    ∀ i < n + n + s, 1 < (supportOn sample (W i)).card →
      (∃ a < i, supportOn sample (W i) = supportOn sample (W a)) ∨
      (i ∈ gateWires n s ∧ ∃ a < i, ∃ b < i,
        supportOn sample (W i) = supportOn sample (W a) ∪ supportOn sample (W b)) ∨
      i ∈ badWires n s bad := by
  intro i hi large
  have inputEnd : n + n ≤ i := Nat.le_of_not_gt fun h => (Nat.not_lt_of_ge (smallInput i h)) large
  let j := i - (n + n)
  have eq : n + n + j = i := by dsimp [j]; omega
  have hj : j < s := by dsimp [j]; omega
  obtain ⟨a, b, earlier, form⟩ := steps j hj
  rw [eq] at earlier form
  have ha : a < i := (le_max_left _ _).trans_lt earlier
  have hb : b < i := (le_max_right _ _).trans_lt earlier
  rcases form with choices | ⟨inter, marked | pure⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at choices
    rcases choices with disj | copy | empty
    · refine Or.inr (Or.inl ⟨Finset.mem_Ico.mpr ⟨inputEnd, hi⟩, a, ha, b, hb, ?_⟩)
      ext p
      simp [disj]
    · exact Or.inl ⟨a, ha, congrArg (supportOn sample) copy⟩
    · have none : supportOn sample (W i) = ∅ := by
        ext p
        simp [empty]
      simp [none] at large
  · exact Or.inr (Or.inr (mem_badWires.mpr ⟨j, hj, marked, eq⟩))
  · have zeroA := (wire_mono_zero initial steps (ha.trans hi)).2
    have zeroB := (wire_mono_zero initial steps (hb.trans hi)).2
    have none : supportOn sample (W i) = ∅ := by
      ext p
      simp [inter, vanishes pure zeroA zeroB p]
    simp [none] at large

theorem pointSupport_step_with_bad {n s : ℕ} {bad : Finset ℕ} {W : ℕ → Set (Signal n)}
    (initial : Initial W) (steps : Steps s bad W) :
    ∀ i < n + n + s, 1 < (pointSupport W i).card →
      (∃ a < i, pointSupport W i = pointSupport W a) ∨
      (i ∈ gateWires n s ∧ ∃ a < i, ∃ b < i,
        pointSupport W i = pointSupport W a ∪ pointSupport W b) ∨
      i ∈ badWires n s bad := by
  apply supportOn_step_with_bad initial steps
  · intro i hi
    change (pointSupport W i).card ≤ 1
    by_cases hp : i < n
    · rw [(supports_input_point initial ⟨i, hp⟩).1]
      simp
    · let l : Fin n := ⟨i - n, by omega⟩
      have eq : n + l.val = i := by dsimp [l]; omega
      rw [← eq, (supports_input_line initial l).1]
      simp
  · exact fun _ _ pure zeroA zeroB p => (pure_intersection_vanishes pure zeroA zeroB).1 (oneHot p)

theorem lineSupport_step_with_bad {n s : ℕ} {bad : Finset ℕ} {W : ℕ → Set (Signal n)}
    (initial : Initial W) (steps : Steps s bad W) :
    ∀ i < n + n + s, 1 < (lineSupport W i).card →
      (∃ a < i, lineSupport W i = lineSupport W a) ∨
      (i ∈ gateWires n s ∧ ∃ a < i, ∃ b < i,
        lineSupport W i = lineSupport W a ∪ lineSupport W b) ∨
      i ∈ badWires n s bad := by
  apply supportOn_step_with_bad initial steps
  · intro i hi
    change (lineSupport W i).card ≤ 1
    by_cases hp : i < n
    · rw [(supports_input_point initial ⟨i, hp⟩).2]
      simp
    · let l : Fin n := ⟨i - n, by omega⟩
      have eq : n + l.val = i := by dsimp [l]; omega
      rw [← eq, (supports_input_line initial l).2]
      simp
  · exact fun _ _ pure zeroA zeroB l => (pure_intersection_vanishes pure zeroA zeroB).2 (oneHot l)

theorem pointSupport_step {n s : ℕ} {W : ℕ → Set (Signal n)}
    (initial : Initial W) (steps : Steps s ∅ W) :
    ∀ i < n + n + s, 1 < (pointSupport W i).card →
      (∃ a < i, pointSupport W i = pointSupport W a) ∨
      (i ∈ gateWires n s ∧ ∃ a < i, ∃ b < i,
        pointSupport W i = pointSupport W a ∪ pointSupport W b) := by
  simpa only [badWires_empty, Finset.notMem_empty, or_false]
    using pointSupport_step_with_bad initial steps

theorem lineSupport_step {n s : ℕ} {W : ℕ → Set (Signal n)}
    (initial : Initial W) (steps : Steps s ∅ W) :
    ∀ i < n + n + s, 1 < (lineSupport W i).card →
      (∃ a < i, lineSupport W i = lineSupport W a) ∨
      (i ∈ gateWires n s ∧ ∃ a < i, ∃ b < i,
        lineSupport W i = lineSupport W a ∪ lineSupport W b) := by
  simpa only [badWires_empty, Finset.notMem_empty, or_false]
    using lineSupport_step_with_bad initial steps

end PEqualNP.Outside.L_meta_17798.Trace

namespace PEqualNP.Outside.L_meta_17798.Count

open scoped BigOperators

variable {n : ℕ}

theorem singleton_of_small {α : Type*} [DecidableEq α] {S : Finset α} {a : α}
    (ha : a ∈ S) (hcard : S.card ≤ 1) : S = {a} := by
  ext b
  constructor
  · intro hb
    exact Finset.mem_singleton.mpr (Finset.card_le_one.mp hcard b hb a ha)
  · intro hb
    rcases Finset.mem_singleton.mp hb with rfl
    exact ha

theorem disjoint_card_sum {κ α : Type*} [DecidableEq α] (indices : Finset κ)
    (groups : κ → Finset α) (pool : Finset α)
    (subset : ∀ i ∈ indices, groups i ⊆ pool) (disjoint : (↑indices : Set κ).PairwiseDisjoint groups) :
    (∑ i ∈ indices, (groups i).card) ≤ pool.card := by
  rw [← Finset.card_biUnion disjoint]
  apply Finset.card_le_card
  intro j hj
  obtain ⟨i, hi, hj⟩ := Finset.mem_biUnion.mp hj
  exact subset i hi hj

theorem image_of_centered_sum {κ α : Type*} [DecidableEq κ] [DecidableEq α] [Fintype α]
    (leaves : Finset κ) (side : κ → Finset α) (operand : κ → ℕ) :
    (∑ a : α, ((leaves.filter (fun j => side j = {a})).image operand).card) ≤ leaves.card := by
  apply le_trans (Finset.sum_le_sum (fun a _ => Finset.card_image_le))
  apply disjoint_card_sum _ _ leaves
  · intro a _ j hj
    exact (Finset.mem_filter.mp hj).1
  · intro a _ b _ hne
    apply Finset.disjoint_left.mpr
    intro j ja jb
    have eq := (Finset.mem_filter.mp ja).2.symm.trans (Finset.mem_filter.mp jb).2
    exact hne (by simpa using eq)

def lineNeighbors (I : Fin n → Fin n → Prop) [DecidableRel I] (p : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (I p)

def pointNeighbors (I : Fin n → Fin n → Prop) [DecidableRel I] (l : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun p => I p l)

theorem lineNeighbors_overlap {I : Fin n → Fin n → Prop} [DecidableRel I]
    (unique : ∀ p p' : Fin n, p ≠ p' → ∃! l : Fin n, I p l ∧ I p' l)
    {p p' : Fin n} (hne : p ≠ p') : (lineNeighbors I p ∩ lineNeighbors I p').card ≤ 1 := by
  obtain ⟨l₀, _, hu⟩ := unique p p' hne
  apply Finset.card_le_one.mpr
  intro l hl l' hl'
  simp only [Finset.mem_inter, lineNeighbors, Finset.mem_filter, Finset.mem_univ, true_and] at hl hl'
  exact (hu l hl).trans (hu l' hl').symm

theorem pointNeighbors_overlap {I : Fin n → Fin n → Prop} [DecidableRel I]
    (unique : ∀ p p' : Fin n, p ≠ p' → ∃! l : Fin n, I p l ∧ I p' l)
    {l l' : Fin n} (hne : l ≠ l') : (pointNeighbors I l ∩ pointNeighbors I l').card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp p' hp'
  simp only [Finset.mem_inter, pointNeighbors, Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
  by_contra hh
  obtain ⟨l₀, _, hu⟩ := unique p p' hh
  exact hne ((hu l ⟨hp.1, hp'.1⟩).trans (hu l' ⟨hp.2, hp'.2⟩).symm)

theorem incidence_card_filter (I : Fin n → Fin n → Prop) [DecidableRel I] :
    Fintype.card (Σ l : Fin n, {p : Fin n // I p l}) =
      ((Finset.univ : Finset (Fin n × Fin n)).filter (fun e => I e.1 e.2)).card := by
  let equiv : (Σ l : Fin n, {p : Fin n // I p l}) ≃ {e : Fin n × Fin n // I e.1 e.2} :=
    { toFun := fun e => ⟨(e.2.val,e.1), e.2.property⟩
      invFun := fun e => ⟨e.val.2, ⟨e.val.1, e.property⟩⟩
      left_inv := by rintro ⟨l,p,hp⟩; rfl
      right_inv := by rintro ⟨⟨p,l⟩,he⟩; rfl }
  rw [Fintype.card_congr equiv]
  exact Fintype.card_subtype _

theorem incidence_card_le {I : Fin n → Fin n → Prop} [DecidableRel I]
    (L R : Fin n → Finset (Fin n))
    (cover : ∀ p l, I p l → l ∈ L p ∨ p ∈ R l) :
    Fintype.card (Σ l : Fin n, {p : Fin n // I p l}) ≤
      (∑ p : Fin n, (L p).card) + ∑ l : Fin n, (R l).card := by
  classical
  let E : Finset (Fin n × Fin n) := Finset.univ.filter (fun e => I e.1 e.2)
  let PL := (Finset.univ : Finset (Fin n)).biUnion (fun p => (L p).image (Prod.mk p))
  let PR := (Finset.univ : Finset (Fin n)).biUnion (fun l => (R l).image (fun p => (p,l)))
  have eq : Fintype.card (Σ l : Fin n, {p : Fin n // I p l}) = E.card := incidence_card_filter I
  have sub : E ⊆ PL ∪ PR := by
    intro e he
    rcases e with ⟨p,l⟩
    have hi := (Finset.mem_filter.mp he).2
    apply Finset.mem_union.mpr
    rcases cover p l hi with hl | hr
    · exact Or.inl (Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ _, Finset.mem_image.mpr ⟨l,hl,rfl⟩⟩)
    · exact Or.inr (Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, Finset.mem_image.mpr ⟨p,hr,rfl⟩⟩)
  rw [eq]
  calc
    E.card ≤ (PL ∪ PR).card := Finset.card_le_card sub
    _ ≤ PL.card + PR.card := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add
      (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_image_le))
      (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_image_le))

theorem centered_rectangles_cover {κ : Type*} [DecidableEq κ] {I H : Fin n → Fin n → Prop}
    [DecidableRel I] [DecidableRel H]
    (leaves : Finset κ) (P L : κ → Finset (Fin n)) (a b : κ → ℕ)
    (centered : ∀ j ∈ leaves, (P j).card ≤ 1 ∨ (L j).card ≤ 1)
    (contained : ∀ j ∈ leaves, ∀ p ∈ P j, ∀ l ∈ L j, I p l)
    (cover : ∀ p l, H p l → ∃ j ∈ leaves, p ∈ P j ∧ l ∈ L j)
    (pSupport lSupport : ℕ → Finset (Fin n))
    (limit pCost lCost : ℕ)
    (shape : ∀ j ∈ leaves, a j < limit ∧ b j < limit ∧ pSupport (a j) = P j ∧ lSupport (b j) = L j)
    (pBudget : ∀ F : Fin n → Finset ℕ,
      (∀ l : Fin n, ∀ i ∈ F l, i < limit ∧ pSupport i ⊆ pointNeighbors I l) →
      (∑ l : Fin n, ((F l).biUnion pSupport).card) ≤ (∑ l : Fin n, (F l).card) + pCost)
    (lBudget : ∀ F : Fin n → Finset ℕ,
      (∀ p : Fin n, ∀ i ∈ F p, i < limit ∧ lSupport i ⊆ lineNeighbors I p) →
      (∑ p : Fin n, ((F p).biUnion lSupport).card) ≤ (∑ p : Fin n, (F p).card) + lCost) :
    Fintype.card (Σ l : Fin n, {p : Fin n // H p l}) ≤ 2 * leaves.card + pCost + lCost := by
  classical
  let left (p : Fin n) := (leaves.filter (fun j => P j = {p})).image b
  let right (l : Fin n) := (leaves.filter (fun j => L j = {l})).image a
  let supplyL p := (left p).biUnion lSupport
  let supplyP l := (right l).biUnion pSupport
  have leftOK : ∀ p : Fin n, ∀ i ∈ left p, i < limit ∧ lSupport i ⊆ lineNeighbors I p := by
    intro p i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨hj,single⟩ := Finset.mem_filter.mp hj
    refine ⟨(shape j hj).2.1, ?_⟩
    intro l hl
    rw [(shape j hj).2.2.2] at hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, contained j hj p (by simp [single]) l hl⟩
  have rightOK : ∀ l : Fin n, ∀ i ∈ right l, i < limit ∧ pSupport i ⊆ pointNeighbors I l := by
    intro l i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨hj,single⟩ := Finset.mem_filter.mp hj
    refine ⟨(shape j hj).1, ?_⟩
    intro p hp
    rw [(shape j hj).2.2.1] at hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, contained j hj p hp l (by simp [single])⟩
  have hL := lBudget left leftOK
  have hP := pBudget right rightOK
  have hc := incidence_card_le (I := H) supplyL supplyP (by
    intro p l he
    obtain ⟨j,hj,hp,hl⟩ := cover p l he
    rcases centered j hj with hpSmall | hlSmall
    · apply Or.inl
      apply Finset.mem_biUnion.mpr
      exact ⟨b j, Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, singleton_of_small hp hpSmall⟩, rfl⟩,
        (shape j hj).2.2.2.symm ▸ hl⟩
    · apply Or.inr
      apply Finset.mem_biUnion.mpr
      exact ⟨a j, Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, singleton_of_small hl hlSmall⟩, rfl⟩,
        (shape j hj).2.2.1.symm ▸ hp⟩)
  have rootL : (∑ p : Fin n, (left p).card) ≤ leaves.card := image_of_centered_sum leaves P b
  have rootR : (∑ l : Fin n, (right l).card) ≤ leaves.card := image_of_centered_sum leaves L a
  change (∑ p : Fin n, (supplyL p).card) ≤ (∑ p : Fin n, (left p).card) + lCost at hL
  change (∑ l : Fin n, (supplyP l).card) ≤ (∑ l : Fin n, (right l).card) + pCost at hP
  omega

end PEqualNP.Outside.L_meta_17798.Count

namespace PEqualNP.Outside.L_meta_17798.Clean

open Trace
open scoped BigOperators

structure Rectangle {n : ℕ} (I : Fin n → Fin n → Prop)
    (W : ℕ → Set (Signal n)) (j : ℕ) where
  a : ℕ
  b : ℕ
  earlier : max a b < n + n + j
  A : Set (Side n)
  B : Set (Side n)
  leftStrip : W a = A ×ˢ Set.univ
  rightStrip : W b = Set.univ ×ˢ B
  gateProduct : W (n + n + j) = A ×ˢ B
  contained : ∀ p ∈ singletonSupport A, ∀ l ∈ singletonSupport B, I p l
  centered : (singletonSupport A).card ≤ 1 ∨ (singletonSupport B).card ≤ 1

theorem incidence_count_without_bad {n q s out pCost lCost : ℕ} {bad : Finset ℕ}
    (I H : Fin n → Fin n → Prop) [DecidableRel I] [DecidableRel H]
    (W : ℕ → Set (Signal n)) (initial : Initial W) (steps : Steps s bad W) (hq : 1 ≤ q)
    (unique : ∀ p p' : Fin n, p ≠ p' → ∃! l : Fin n, I p l ∧ I p' l)
    (outValid : out < n + n + s) (safe : Sound q I (W out))
    (accepts : ∀ p l, H p l → (oneHot p, oneHot l) ∈ W out)
    (avoids : ∀ p l, H p l → ∀ j < s, j ∈ bad → W (n+n+j) ⊆ W out →
      (oneHot p, oneHot l) ∉ W (n+n+j))
    (pBudget : ∀ F : Fin n → Finset ℕ,
      (∀ l : Fin n, ∀ i ∈ F l, i < n+n+s ∧ pointSupport W i ⊆ Count.pointNeighbors I l) →
      (∑ l : Fin n, ((F l).biUnion (pointSupport W)).card) ≤ (∑ l : Fin n, (F l).card) + pCost)
    (lBudget : ∀ F : Fin n → Finset ℕ,
      (∀ p : Fin n, ∀ i ∈ F p, i < n+n+s ∧ lineSupport W i ⊆ Count.lineNeighbors I p) →
      (∑ p : Fin n, ((F p).biUnion (lineSupport W)).card) ≤ (∑ p : Fin n, (F p).card) + lCost) :
    Fintype.card (Σ l : Fin n, {p : Fin n // H p l}) ≤ 2 * s + pCost + lCost := by
  classical
  let present := (Finset.range s).filter (fun j => Nonempty (Rectangle I W j))
  let roots := present.attach
  let rect (j : {j : ℕ // j ∈ present}) : Rectangle I W j.val :=
    Classical.choice (Finset.mem_filter.mp j.property).2
  let pts (j : {j : ℕ // j ∈ present}) := singletonSupport (rect j).A
  let lines (j : {j : ℕ // j ∈ present}) := singletonSupport (rect j).B
  have covers : ∀ p l, H p l → ∃ j ∈ roots, p ∈ pts j ∧ l ∈ lines j := by
    intro p l edge
    obtain ⟨j, hj, sub, pair, tag⟩ := incident_leaf initial steps hq unique outValid (accepts p l edge) safe
    rcases tag with excluded | ⟨a,b,early,A,B,left,right,prod,_,_,contained,centered⟩
    · exact (avoids p l edge j hj excluded sub pair).elim
    let certificate : Rectangle I W j := ⟨a,b,early,A,B,left,right,prod,contained,centered⟩
    let i : {j : ℕ // j ∈ present} :=
      ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, ⟨certificate⟩⟩⟩
    refine ⟨i, Finset.mem_attach _ _, ?_⟩
    have hit : (oneHot p, oneHot l) ∈ W (n+n+i.val) := pair
    rw [(rect i).gateProduct] at hit
    exact ⟨mem_singletonSupport.mpr hit.1, mem_singletonSupport.mpr hit.2⟩
  have form : ∀ j ∈ roots, (rect j).a < n+n+s ∧ (rect j).b < n+n+s ∧
      pointSupport W (rect j).a = pts j ∧ lineSupport W (rect j).b = lines j := by
    intro j _
    have hj := Finset.mem_range.mp (Finset.mem_filter.mp j.property).1
    have ha := (le_max_left (rect j).a (rect j).b).trans_lt (rect j).earlier
    have hb := (le_max_right (rect j).a (rect j).b).trans_lt (rect j).earlier
    exact ⟨by omega, by omega, pointSupport_strip (rect j).leftStrip, lineSupport_strip (rect j).rightStrip⟩
  have hCount : roots.card ≤ s := by
    dsimp only [roots]
    rw [Finset.card_attach]
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range s)
  have h := Count.centered_rectangles_cover (I := I) (H := H) roots pts lines (fun j => (rect j).a) (fun j => (rect j).b)
    (fun j _ => (rect j).centered) (fun j _ => (rect j).contained) covers (pointSupport W) (lineSupport W)
    (n+n+s) pCost lCost form pBudget lBudget
  omega

noncomputable def exceptionalIncidences {n : ℕ} (I : Fin n → Fin n → Prop)
    (W : ℕ → Set (Signal n)) (s out : ℕ) (bad : Finset ℕ) : Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter fun e => I e.1 e.2 ∧
    ∃ j < s, j ∈ bad ∧ W (n+n+j) ⊆ W out ∧ (oneHot e.1, oneHot e.2) ∈ W (n+n+j)

theorem mem_exceptionalIncidences {n : ℕ} (I : Fin n → Fin n → Prop)
    (W : ℕ → Set (Signal n)) (s out : ℕ) (bad : Finset ℕ) (p l : Fin n) :
    (p,l) ∈ exceptionalIncidences I W s out bad ↔ I p l ∧
      ∃ j < s, j ∈ bad ∧ W (n+n+j) ⊆ W out ∧ (oneHot p, oneHot l) ∈ W (n+n+j) := by
  classical
  simp [exceptionalIncidences]

theorem incidence_bound_with_bad {n q s out pCost lCost : ℕ} {bad : Finset ℕ}
    (I : Fin n → Fin n → Prop) [DecidableRel I]
    (W : ℕ → Set (Signal n)) (initial : Initial W) (steps : Steps s bad W) (hq : 1 ≤ q)
    (degree : ∀ l : Fin n, Fintype.card {p : Fin n // I p l} = q + 1)
    (unique : ∀ p p' : Fin n, p ≠ p' → ∃! l : Fin n, I p l ∧ I p' l)
    (outValid : out < n + n + s) (safe : Sound q I (W out))
    (accepts : ∀ p l, I p l → (oneHot p, oneHot l) ∈ W out)
    (pBudget : ∀ F : Fin n → Finset ℕ,
      (∀ l : Fin n, ∀ i ∈ F l, i < n+n+s ∧ pointSupport W i ⊆ Count.pointNeighbors I l) →
      (∑ l : Fin n, ((F l).biUnion (pointSupport W)).card) ≤ (∑ l : Fin n, (F l).card) + pCost)
    (lBudget : ∀ F : Fin n → Finset ℕ,
      (∀ p : Fin n, ∀ i ∈ F p, i < n+n+s ∧ lineSupport W i ⊆ Count.lineNeighbors I p) →
      (∑ p : Fin n, ((F p).biUnion (lineSupport W)).card) ≤ (∑ p : Fin n, (F p).card) + lCost) :
    n * (q + 1) ≤ 2 * s + pCost + lCost + (exceptionalIncidences I W s out bad).card := by
  classical
  let badEdges := exceptionalIncidences I W s out bad
  let H (p l : Fin n) := I p l ∧ (p,l) ∉ badEdges
  have h := incidence_count_without_bad I H W initial steps hq unique outValid safe
    (fun p l hp => accepts p l hp.1)
    (fun p l hp j hj hbad sub hit => hp.2 ((mem_exceptionalIncidences I W s out bad p l).mpr
      ⟨hp.1, j,hj,hbad,sub,hit⟩)) pBudget lBudget
  let E := (Finset.univ : Finset (Fin n × Fin n)).filter (fun e => I e.1 e.2)
  let C := (Finset.univ : Finset (Fin n × Fin n)).filter (fun e => H e.1 e.2)
  have countE : E.card = n * (q + 1) := by
    rw [← Count.incidence_card_filter I, Fintype.card_sigma]
    simp [degree]
  have countC : C.card ≤ 2 * s + pCost + lCost := by
    rw [← Count.incidence_card_filter H]
    exact h
  have sub : E ⊆ C ∪ badEdges := by
    rintro ⟨p,l⟩ he
    have hin := (Finset.mem_filter.mp he).2
    apply Finset.mem_union.mpr
    by_cases hh : (p,l) ∈ badEdges
    · exact Or.inr hh
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hin, hh⟩)
  have count := (Finset.card_le_card sub).trans (Finset.card_union_le C badEdges)
  change n * (q + 1) ≤ 2 * s + pCost + lCost + badEdges.card
  omega

theorem clean_circuit_lower_bound {n q s out : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (W : ℕ → Set (Signal n)) (initial : Initial W) (steps : Steps s ∅ W)
    (hq : 1 ≤ q) (degree : ∀ l : Fin n, Fintype.card {p : Fin n // I p l} = q + 1)
    (unique : ∀ p p' : Fin n, p ≠ p' → ∃! l : Fin n, I p l ∧ I p' l)
    (outValid : out < n + n + s) (safe : Sound q I (W out))
    (accepts : ∀ p l, I p l → (oneHot p, oneHot l) ∈ W out) : n * (q + 1) ≤ 4 * s := by
  have h := incidence_count_without_bad (pCost := s) (lCost := s)
    I I W initial steps hq unique outValid safe accepts (by simp)
    (fun F good => by
      simpa only [card_gateWires] using Forest.neighborhoods_total (pointSupport W) (gateWires n s)
        (n+n+s) Finset.univ (Count.pointNeighbors I) F (pointSupport_step initial steps)
        (fun l _ => good l) (fun _ _ _ _ hn => Count.pointNeighbors_overlap unique hn))
    (fun F good => by
      simpa only [card_gateWires] using Forest.neighborhoods_total (lineSupport W) (gateWires n s)
        (n+n+s) Finset.univ (Count.lineNeighbors I) F (lineSupport_step initial steps)
        (fun p _ => good p) (fun _ _ _ _ hn => Count.lineNeighbors_overlap unique hn))
  have hEdges : Fintype.card (Σ l : Fin n, {p : Fin n // I p l}) = n * (q + 1) := by
    rw [Fintype.card_sigma]
    simp [degree]
  rw [hEdges] at h
  omega

end PEqualNP.Outside.L_meta_17798.Clean

namespace PEqualNP.Outside.L_meta_17798.Clean

open Trace
open scoped BigOperators

theorem circuit_lower_bound_with_exceptions {n q s out : ℕ} {bad : Finset ℕ}
    (I : Fin n → Fin n → Prop) [DecidableRel I]
    (W : ℕ → Set (Signal n)) (initial : Initial W) (steps : Steps s bad W) (hq : 1 ≤ q)
    (degree : ∀ l : Fin n, Fintype.card {p : Fin n // I p l} = q + 1)
    (unique : ∀ p p' : Fin n, p ≠ p' → ∃! l : Fin n, I p l ∧ I p' l)
    (outValid : out < n+n+s) (safe : Sound q I (W out))
    (accepts : ∀ p l, I p l → (oneHot p, oneHot l) ∈ W out) :
    n * (q + 1) ≤ 4 * s +
      (∑ i ∈ badWires n s bad, ((pointSupport W i).card - 1)) +
      (∑ i ∈ badWires n s bad, ((lineSupport W i).card - 1)) +
      (exceptionalIncidences I W s out bad).card := by
  let pc := ∑ i ∈ badWires n s bad, ((pointSupport W i).card - 1)
  let lc := ∑ i ∈ badWires n s bad, ((lineSupport W i).card - 1)
  have pointBudget : ∀ F : Fin n → Finset ℕ,
      (∀ c : Fin n, ∀ i ∈ F c, i < n+n+s ∧ pointSupport W i ⊆ Count.pointNeighbors I c) →
      (∑ c : Fin n, ((F c).biUnion (pointSupport W)).card) ≤ (∑ c : Fin n, (F c).card) + (s + pc) := by
    intro F good
    have h := WeightedForest.weighted_neighborhoods_total (pointSupport W) (gateWires n s)
      (badWires n s bad) (n+n+s) Finset.univ (Count.pointNeighbors I) F
      (fun c => (F c).biUnion (pointSupport W)) (by
        intro i hi hbig
        rcases pointSupport_step_with_bad initial steps i hi hbig with hcopy | hunion | hbad
        · exact Or.inr (Or.inl hcopy)
        · exact Or.inr (Or.inr hunion)
        · exact Or.inl hbad)
      (fun c _ => good c) (fun _ _ => Finset.Subset.rfl)
      (fun _ _ _ _ hn => Count.pointNeighbors_overlap unique hn)
    simpa only [card_gateWires, Nat.add_assoc, pc] using h
  have lineBudget : ∀ F : Fin n → Finset ℕ,
      (∀ c : Fin n, ∀ i ∈ F c, i < n+n+s ∧ lineSupport W i ⊆ Count.lineNeighbors I c) →
      (∑ c : Fin n, ((F c).biUnion (lineSupport W)).card) ≤ (∑ c : Fin n, (F c).card) + (s + lc) := by
    intro F good
    have h := WeightedForest.weighted_neighborhoods_total (lineSupport W) (gateWires n s)
      (badWires n s bad) (n+n+s) Finset.univ (Count.lineNeighbors I) F
      (fun c => (F c).biUnion (lineSupport W)) (by
        intro i hi hbig
        rcases lineSupport_step_with_bad initial steps i hi hbig with hcopy | hunion | hbad
        · exact Or.inr (Or.inl hcopy)
        · exact Or.inr (Or.inr hunion)
        · exact Or.inl hbad)
      (fun c _ => good c) (fun _ _ => Finset.Subset.rfl)
      (fun _ _ _ _ hn => Count.lineNeighbors_overlap unique hn)
    simpa only [card_gateWires, Nat.add_assoc, lc] using h
  have bound := incidence_bound_with_bad I W initial steps hq degree unique outValid safe accepts
    pointBudget lineBudget
  change n * (q + 1) ≤ 4*s + pc + lc + (exceptionalIncidences I W s out bad).card
  omega

end PEqualNP.Outside.L_meta_17798.Clean
