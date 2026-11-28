import Mathlib.Data.Fintype.Card
import PEqualNP.Defs.SearchRUP

namespace PnpResearch.RupFrames

open PEqualNP.ProofComplexity PEqualNP.Search

variable {V : Type}

def Consistent (frame : Literal V → Prop) : Prop :=
  ∀ l, frame l → ¬ frame (negLit l)

def Stable (frame : Literal V → Prop) (clause : Clause V) : Prop :=
  (∃ l ∈ clause, frame l) ∨
  ∃ l ∈ clause, ∃ k ∈ clause, l ≠ k ∧ ¬ frame (negLit l) ∧ ¬ frame (negLit k)

def Dead (frame : Literal V → Prop) (clause : Clause V) : Prop :=
  ∀ l ∈ clause, frame (negLit l)

private theorem neg_neg (l : Literal V) : negLit (negLit l) = l := by
  rcases l with ⟨v, b⟩
  cases b <;> rfl

private theorem stable_not_dead {S : Literal V → Prop} (ok : Consistent S)
    {d : Clause V} (h : Stable S d) : ¬ Dead S d := by
  intro dead
  rcases h with ⟨l, hl, holds⟩ | ⟨l, hl, _, _, _, openLit, _⟩
  · exact ok l holds (dead l hl)
  · exact openLit (dead l hl)

private theorem frame_contains_propagation {S : Literal V → Prop} {Γ : Set (Clause V)}
    {A : Set (Literal V)} (ok : Consistent S) (stable : ∀ d ∈ Γ, Stable S d)
    (extendsA : ∀ l ∈ A, S l) {l : Literal V} (forced : UPForces Γ A l) : S l := by
  induction forced with
  | hyp premise => exact extendsA _ premise
  | @unit d l hd hl step ih =>
    rcases stable d hd with ⟨k, hk, holds⟩ | ⟨k, hk, q, hq, neq, unk, unq⟩
    · by_cases e : k = l
      · exact e ▸ holds
      · exact (ok k holds (ih k hk e)).elim
    · by_cases e : k = l
      · exact (unq (ih q hq (fun h => neq (e.trans h.symm)))).elim
      · exact (unk (ih k hk e)).elim

private theorem assumption_of_both {Γ : Set (Clause V)} {A : Set (Literal V)}
    (noDead : ∀ d ∈ Γ, ¬ Dead (UPForces Γ A) d) {l : Literal V}
    (positive : UPForces Γ A l) (negative : UPForces Γ A (negLit l)) : l ∈ A := by
  cases positive with
  | hyp h => exact h
  | @unit d l hd hl step =>
    exfalso
    apply noDead d hd
    intro k hk
    by_cases eq : k = l
    · simpa only [eq] using negative
    · exact step k hk eq

private theorem stable_closure {Γ : Set (Clause V)} {A : Set (Literal V)}
    (noDead : ∀ d ∈ Γ, ¬ Dead (UPForces Γ A) d) : ∀ d ∈ Γ, Stable (UPForces Γ A) d := by
  classical
  intro d hd
  by_cases holds : ∃ l ∈ d, UPForces Γ A l
  · exact Or.inl holds
  · have live : ∃ l ∈ d, ¬ UPForces Γ A (negLit l) := by
      by_contra h
      exact noDead d hd (fun l hl => by
        by_contra no
        exact h ⟨l, hl, no⟩)
    obtain ⟨l, hl, openLit⟩ := live
    by_cases pair : ∃ k ∈ d, k ≠ l ∧ ¬ UPForces Γ A (negLit k)
    · obtain ⟨k, hk, neq, openK⟩ := pair
      exact Or.inr ⟨l, hl, k, hk, Ne.symm neq, openLit, openK⟩
    · have last : UPForces Γ A l := UPForces.unit hd hl (fun k hk neq => by
        by_contra no
        exact pair ⟨k, hk, neq, no⟩)
      exact (holds ⟨l, hl, last⟩).elim

/-- For consistent assumptions, failure of unit propagation is equivalent to the
existence of a consistent partial assignment that is closed under all known clauses. -/
theorem no_conflict_iff_frame (Γ : Set (Clause V)) (A : Set (Literal V))
    (consistentAssumptions : Consistent (fun l => l ∈ A)) :
    (¬ ∃ d ∈ Γ, Dead (UPForces Γ A) d) ↔
      ∃ S : Literal V → Prop, Consistent S ∧
        (∀ l ∈ A, S l) ∧ ∀ d ∈ Γ, Stable S d := by
  constructor
  · intro noConflict
    have noDead : ∀ d ∈ Γ, ¬ Dead (UPForces Γ A) d :=
      fun d hd dead => noConflict ⟨d, hd, dead⟩
    refine ⟨UPForces Γ A, ?_, fun _ h => UPForces.hyp h, stable_closure noDead⟩
    intro l positive negative
    exact consistentAssumptions l (assumption_of_both noDead positive negative)
      (assumption_of_both noDead negative (by simpa only [neg_neg] using positive))
  · rintro ⟨S, ok, extendsA, stable⟩ ⟨d, hd, conflict⟩
    exact stable_not_dead ok (stable d hd)
      (fun l hl => frame_contains_propagation ok stable extendsA (conflict l hl))

/-- A nontautological clause is RUP exactly when no stable frame falsifies it. -/
theorem rup_iff_no_frame (Γ : Set (Clause V)) (C : Clause V)
    (ok : Consistent (fun l => l ∈ negLit '' (↑C : Set (Literal V)))) :
    IsRUP Γ C ↔ ¬ ∃ S : Literal V → Prop, Consistent S ∧
      Dead S C ∧ ∀ d ∈ Γ, Stable S d := by
  classical
  have ext (S : Literal V → Prop) :
      (∀ l ∈ negLit '' (↑C : Set (Literal V)), S l) ↔ Dead S C := by
    constructor
    · intro all l hl
      exact all (negLit l) ⟨l, hl, rfl⟩
    · rintro dead _ ⟨l, hl, rfl⟩
      exact dead l hl
  have h := no_conflict_iff_frame Γ (negLit '' (↑C : Set (Literal V))) ok
  change (¬ IsRUP Γ C) ↔ _ at h
  simp only [ext] at h
  constructor
  · intro rup frame
    exact (h.mpr frame) rup
  · intro noFrame
    by_contra noRup
    exact noFrame (h.mp noRup)

def Admissible (S : Literal V → Prop) : List (Clause V) → Prop
  | [] => True
  | c :: previous =>
      Admissible S previous ∧ ((∀ d ∈ previous, Stable S d) → ¬ Dead S c)

def Unit (S : Literal V → Prop) (C : Clause V) : Prop :=
  ¬ Stable S C ∧ ¬ Dead S C

/-- A frame is blocked if a unit clause precedes any clause falsified by the frame.
The recursive list is in the project's newest-first order. -/
def Blocks (S : Literal V → Prop) : List (Clause V) → Prop
  | [] => False
  | c :: previous =>
      Blocks S previous ∨ ((∀ d ∈ previous, ¬ Dead S d) ∧ Unit S c)

private theorem admissible_of_no_dead (S : Literal V → Prop) :
    ∀ ρ : List (Clause V), (∀ d ∈ ρ, ¬ Dead S d) → Admissible S ρ := by
  intro ρ
  induction ρ with
  | nil => exact fun _ => trivial
  | cons c tail ih =>
    intro h
    exact ⟨ih (fun d hd => h d (List.mem_cons_of_mem _ hd)),
      fun _ => h c List.mem_cons_self⟩

theorem blocks_iff (S : Literal V → Prop) (ok : Consistent S) (ρ : List (Clause V)) :
    Blocks S ρ ↔ Admissible S ρ ∧ (∃ d ∈ ρ, ¬ Stable S d) := by
  classical
  induction ρ with
  | nil => simp [Blocks, Admissible]
  | cons c tail ih =>
    constructor
    · rintro (previous | ⟨noDead, unit⟩)
      · obtain ⟨ad, d, hd, unstable⟩ := ih.mp previous
        exact ⟨⟨ad, fun all => (unstable (all d hd)).elim⟩,
          d, List.mem_cons_of_mem c hd, unstable⟩
      · exact ⟨⟨admissible_of_no_dead S tail noDead, fun _ => unit.2⟩,
          c, List.mem_cons_self, unit.1⟩
    · rintro ⟨⟨ad, neDead⟩, witness⟩
      by_cases earlier : ∃ d ∈ tail, ¬ Stable S d
      · exact Or.inl (ih.mpr ⟨ad, earlier⟩)
      · have st : ∀ d ∈ tail, Stable S d := fun d hd => by
          by_contra no
          exact earlier ⟨d, hd, no⟩
        obtain ⟨d, hd, h⟩ := witness
        rw [List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact Or.inr ⟨fun d hd => stable_not_dead ok (st d hd), h, neDead st⟩
        · exact (h (st d hd)).elim

/-- Checking every base-stable frame characterizes a nontautological RUP trace. -/
theorem run_iff_admissible (F : Set (Clause V)) (ρ : List (Clause V))
    (nonTaut : ∀ c ∈ ρ, Consistent (fun l => l ∈ negLit '' (↑c : Set (Literal V)))) :
    IsRUPRun F ρ ↔
      ∀ S : Literal V → Prop, Consistent S → (∀ d ∈ F, Stable S d) → Admissible S ρ := by
  induction ρ with
  | nil => exact ⟨fun _ _ _ _ => trivial, fun _ => IsRUPRun.nil⟩
  | cons c tail ih =>
    have tailNonTaut : ∀ d ∈ tail, Consistent (fun l => l ∈ negLit '' (↑d : Set (Literal V))) :=
      fun d hd => nonTaut d (List.mem_cons_of_mem _ hd)
    constructor
    · intro run S ok base
      cases run with
      | learn past rup =>
        refine ⟨(ih tailNonTaut).mp past S ok base, fun old dead => ?_⟩
        have impossible := (rup_iff_no_frame _ c (nonTaut c List.mem_cons_self)).mp rup
        exact impossible ⟨S, ok, dead, fun d hd => hd.elim (base d) (old d)⟩
    · intro frames
      apply IsRUPRun.learn ((ih tailNonTaut).mpr (fun S ok base => (frames S ok base).1))
      apply (rup_iff_no_frame _ c (nonTaut c List.mem_cons_self)).mpr
      rintro ⟨S, ok, dead, stable⟩
      exact (frames S ok (fun d hd => stable d (Or.inl hd))).2
        (fun d hd => stable d (Or.inr hd)) dead

/-- In a refutation ending with the empty clause, every base-stable frame must
have been blocked before that last clause. -/
theorem refutation_iff_blocks (F : Set (Clause V)) (ρ : List (Clause V))
    (nonTaut : ∀ c ∈ (∅ :: ρ), Consistent (fun l => l ∈ negLit '' (↑c : Set (Literal V)))) :
    IsRUPRun F (∅ :: ρ) ↔
      ∀ S : Literal V → Prop, Consistent S → (∀ d ∈ F, Stable S d) → Blocks S ρ := by
  classical
  rw [run_iff_admissible F _ nonTaut]
  constructor
  · intro adm S ok base
    have h := adm S ok base
    apply (blocks_iff S ok ρ).mpr
    refine ⟨h.1, ?_⟩
    by_contra none
    have allStable : ∀ d ∈ ρ, Stable S d := fun d hd => by
      by_contra no
      exact none ⟨d, hd, no⟩
    exact h.2 allStable (by simp [Dead])
  · intro blocks S ok base
    obtain ⟨ad, d, hd, unstable⟩ := (blocks_iff S ok ρ).mp (blocks S ok base)
    exact ⟨ad, fun all => (unstable (all d hd)).elim⟩

end PnpResearch.RupFrames

namespace PnpResearch.RupFrames

open PEqualNP.ProofComplexity PEqualNP.Search

variable {V : Type}

theorem not_rup_of_frame {F : Set (Clause V)} {C : Clause V} {S : Literal V → Prop}
    (ok : Consistent S) (base : ∀ D ∈ F, Stable S D) (dead : Dead S C) : ¬ IsRUP F C := by
  rintro ⟨D, hD, forced⟩
  have assumptions : ∀ l ∈ negLit '' (↑C : Set (Literal V)), S l := by
    rintro _ ⟨l, hl, rfl⟩
    exact dead l hl
  exact stable_not_dead ok (base D hD)
    (fun l hl => frame_contains_propagation ok base assumptions (forced l hl))

theorem admissible_of_run {F : Set (Clause V)} {ρ : List (Clause V)}
    (run : IsRUPRun F ρ) {S : Literal V → Prop} (ok : Consistent S)
    (base : ∀ D ∈ F, Stable S D) : Admissible S ρ := by
  induction run with
  | nil => trivial
  | @learn past C prior rup ih =>
    refine ⟨ih, fun older dead => not_rup_of_frame (F := F ∪ {D | D ∈ past}) ok ?_ dead rup⟩
    intro D hD
    exact hD.elim (base D) (older D)

theorem blocks_of_run_dead {F : Set (Clause V)} {ρ : List (Clause V)} {C : Clause V}
    (run : IsRUPRun F (C :: ρ)) {S : Literal V → Prop} (ok : Consistent S)
    (base : ∀ D ∈ F, Stable S D) (dead : Dead S C) : Blocks S ρ := by
  classical
  have adm := admissible_of_run run ok base
  apply (blocks_iff S ok ρ).mpr
  refine ⟨adm.1, ?_⟩
  by_contra noBlock
  exact adm.2 (fun D hD => by
    by_contra h
    exact noBlock ⟨D, hD, h⟩) dead

theorem blocks_of_run_empty {F : Set (Clause V)} {ρ : List (Clause V)}
    (run : IsRUPRun F (∅ :: ρ)) {S : Literal V → Prop} (ok : Consistent S)
    (base : ∀ D ∈ F, Stable S D) : Blocks S ρ :=
  blocks_of_run_dead run ok base (by simp [Dead])

theorem run_suffix {F : Set (Clause V)} (newer : List (Clause V)) {ρ : List (Clause V)}
    (run : IsRUPRun F (newer ++ ρ)) : IsRUPRun F ρ := by
  induction newer with
  | nil => exact run
  | cons _ _ ih =>
    cases run with
    | learn previous _ => exact ih previous

theorem dead_requires_older_block {F : Set (Clause V)} {newer older : List (Clause V)}
    {C : Clause V} (run : IsRUPRun F (newer ++ C :: older)) {S : Literal V → Prop}
    (ok : Consistent S) (base : ∀ D ∈ F, Stable S D) (dead : Dead S C) : Blocks S older :=
  blocks_of_run_dead (run_suffix newer run) ok base dead

/-- Write a run containing the empty clause as later steps followed by the first empty step
and its nonempty history. -/
theorem first_empty_of_run {F : Set (Clause V)} {ρ : List (Clause V)}
    (run : IsRUPRun F ρ) (empty : (∅ : Clause V) ∈ ρ) :
    ∃ later past, ρ = later ++ ∅ :: past ∧ IsRUPRun F (∅ :: past) ∧
      (∅ : Clause V) ∉ past ∧ past.length < ρ.length := by
  classical
  induction run with
  | nil => simp at empty
  | @learn past C prior rup ih =>
    by_cases before : (∅ : Clause V) ∈ past
    · obtain ⟨later, earlier, eq, firstRun, noEmpty, shorter⟩ := ih before
      exact ⟨C :: later, earlier, congrArg (List.cons C) eq, firstRun, noEmpty,
        shorter.trans (Nat.lt_succ_self _)⟩
    · have eq : (∅ : Clause V) = C := (List.mem_cons.mp empty).resolve_right before
      subst C
      exact ⟨[], past, rfl, .learn prior rup, before, Nat.lt_succ_self _⟩

theorem blocks_iff_split {S : Literal V → Prop} {ρ : List (Clause V)} :
    Blocks S ρ ↔ ∃ newer older C, ρ = newer ++ C :: older ∧ Unit S C ∧
      ∀ D ∈ older, ¬ Dead S D := by
  induction ρ with
  | nil => simp [Blocks]
  | cons head tail ih =>
    constructor
    · rintro (blocked | ⟨noDead, unit⟩)
      · obtain ⟨newer, older, C, eq, unit, noDead⟩ := ih.mp blocked
        exact ⟨head :: newer, older, C, congrArg (List.cons head) eq, unit, noDead⟩
      · exact ⟨[], tail, head, rfl, unit, noDead⟩
    · rintro ⟨newer, older, C, eq, unit, noDead⟩
      cases newer with
      | nil =>
        rcases List.cons.inj eq with ⟨rfl, rfl⟩
        exact Or.inr ⟨noDead, unit⟩
      | cons first rest =>
        exact Or.inl (ih.mpr ⟨rest, older, C, (List.cons.inj eq).2, unit, noDead⟩)

theorem unit_iff_unique_open {S : Literal V → Prop} (ok : Consistent S) {C : Clause V} :
    Unit S C ↔ ∃ l ∈ C, ¬ S l ∧ ¬ S (negLit l) ∧
      ∀ k ∈ C, k ≠ l → S (negLit k) := by
  classical
  constructor
  · rintro ⟨unstable, notDead⟩
    have existsOpen : ∃ l ∈ C, ¬ S (negLit l) := by
      by_contra noOpen
      exact notDead (fun l hl => by
        by_contra opens
        exact noOpen ⟨l, hl, opens⟩)
    obtain ⟨l, hl, openL⟩ := existsOpen
    refine ⟨l, hl, fun h => unstable (Or.inl ⟨l, hl, h⟩), openL, ?_⟩
    intro k hk neq
    by_contra openK
    exact unstable (Or.inr ⟨k, hk, l, hl, neq, openK, openL⟩)
  · rintro ⟨l, hl, notTrue, openL, falseOthers⟩
    refine ⟨?_, fun dead => openL (dead l hl)⟩
    rintro (⟨k, hk, trueK⟩ | ⟨k, hk, q, hq, neq, openK, openQ⟩)
    · by_cases h : k = l
      · exact notTrue (h ▸ trueK)
      · exact ok k trueK (falseOthers k hk h)
    · by_cases h : k = l
      · exact openQ (falseOthers q hq (fun e => neq (h.trans e.symm)))
      · exact openK (falseOthers k hk h)

def Matched {k m n : Nat} (p : Fin k → Fin m) (h : Fin k → Fin n)
    (i : Fin m) (j : Fin n) : Prop := ∃ a, p a = i ∧ h a = j

/-- The matched edges are true. Every other edge incident to a matched row or column is
false. All remaining edges are unset. -/
def MatchingFrame {k m n : Nat} (p : Fin k → Fin m) (h : Fin k → Fin n) :
    Literal (Fin m × Fin n) → Prop
  | ((i, j), true) => Matched p h i j
  | ((i, j), false) => ¬ Matched p h i j ∧ ((∃ a, p a = i) ∨ ∃ a, h a = j)

theorem matchingFrame_consistent {k m n : Nat} (p : Fin k → Fin m) (h : Fin k → Fin n) :
    Consistent (MatchingFrame p h) := by
  rintro ⟨⟨i, j⟩, b⟩
  cases b
  · exact fun h hn => h.1 hn
  · exact fun h hn => hn.1 h

private theorem two_free_holes {k n : Nat} (h : Fin k → Fin n) (room : k + 2 ≤ n) :
    ∃ j j' : Fin n, j ≠ j' ∧ (∀ a, h a ≠ j) ∧ ∀ a, h a ≠ j' := by
  let used := Finset.univ.image h
  have cardUsed : used.card ≤ k := by
    simpa only [Finset.card_fin] using
      (Finset.card_image_le (s := Finset.univ) (f := h))
  have two : 1 < usedᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨j, hj, j', hj', neq⟩ := Finset.one_lt_card.mp two
  have outside (z : Fin n) (hz : z ∈ usedᶜ) (a : Fin k) : h a ≠ z :=
    fun eq => (Finset.mem_compl.mp hz) (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, eq⟩)
  exact ⟨j, j', neq, outside j hj, outside j' hj'⟩

theorem matchingFrame_stable {k m n : Nat} (p : Fin k → Fin m) (h : Fin k → Fin n)
    (inj : Function.Injective h) (room : k + 2 ≤ n) :
    ∀ C ∈ PHP m n, Stable (MatchingFrame p h) C := by
  classical
  intro C Cmem
  rcases Cmem with ⟨i, rfl⟩ | ⟨i, i', j, neq, rfl⟩
  · by_cases known : ∃ a, p a = i
    · obtain ⟨a, ha⟩ := known
      exact Or.inl ⟨((i, h a), true), Finset.mem_image.mpr ⟨h a, Finset.mem_univ _, rfl⟩,
        ⟨a, ha, rfl⟩⟩
    · obtain ⟨j, j', neq, free, free'⟩ := two_free_holes h room
      have openEdge (z : Fin n) (hz : ∀ a, h a ≠ z) :
          ¬ MatchingFrame p h (negLit ((i, z), true)) := by
        rintro ⟨_, used | ⟨a, ha⟩⟩
        · exact known used
        · exact hz a ha
      exact Or.inr ⟨((i, j), true), Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩,
        ((i, j'), true), Finset.mem_image.mpr ⟨j', Finset.mem_univ _, rfl⟩,
        fun e => neq (congrArg (fun l : Literal (Fin m × Fin n) => l.1.2) e),
        openEdge j free, openEdge j' free'⟩
  · by_cases a : Matched p h i j
    · have b : ¬ Matched p h i' j := by
        obtain ⟨u, hu, uh⟩ := a
        rintro ⟨v, hv, vh⟩
        have uv := inj (uh.trans vh.symm)
        exact neq (hu.symm.trans (uv ▸ hv))
      obtain ⟨u, _, uh⟩ := a
      exact Or.inl ⟨((i', j), false), by simp, b, Or.inr ⟨u, uh⟩⟩
    · by_cases b : Matched p h i' j
      · obtain ⟨u, _, uh⟩ := b
        exact Or.inl ⟨((i, j), false), by simp, a, Or.inr ⟨u, uh⟩⟩
      · exact Or.inr ⟨((i, j), false), by simp, ((i', j), false), by simp,
          fun e => neq (congrArg (fun l : Literal (Fin m × Fin n) => l.1.1) e), a, b⟩

theorem blocks_append_newer {S : Literal V → Prop} {ρ : List (Clause V)}
    (newer : List (Clause V)) (blocked : Blocks S ρ) : Blocks S (newer ++ ρ) := by
  induction newer with
  | nil => exact blocked
  | cons _ _ ih => exact Or.inl ih

abbrev Php65Clause := Clause (Fin 6 × Fin 5)

private def paddingClause : Php65Clause := {((0, 0), true), ((0, 0), false)}

/-- Any counterexample to L-meta-9471 induces a fixed-length ordering satisfying the
matching-frame constraints. The learned history is newest first. -/
theorem php65_matching_order {ρ : List Php65Clause} (run : IsRUPRun (PHP 6 5) ρ)
    (empty : (∅ : Php65Clause) ∈ ρ) (budget : ρ.length ≤ 20) :
    ∃ past : List Php65Clause, past.length = 19 ∧ (∅ : Php65Clause) ∉ past ∧
      ∀ (k : Nat), k ≤ 3 → ∀ (p : Fin k → Fin 6) (h : Fin k → Fin 5),
        Function.Injective h → Blocks (MatchingFrame p h) past := by
  obtain ⟨_, past, _, firstRun, noEmpty, shorter⟩ := first_empty_of_run run empty
  have lengthBound : past.length ≤ 19 := by omega
  let padding := List.replicate (19 - past.length) paddingClause
  have padNonempty : (∅ : Php65Clause) ∉ padding := by
    have ne : (∅ : Php65Clause) ≠ paddingClause := by decide
    intro mem
    exact ne (List.eq_of_mem_replicate mem)
  refine ⟨padding ++ past, ?_, ?_, ?_⟩
  · simp only [List.length_append, padding, List.length_replicate]
    omega
  · simpa only [List.mem_append, not_or] using And.intro padNonempty noEmpty
  · intro k hk p h inj
    exact blocks_append_newer padding (blocks_of_run_empty firstRun (matchingFrame_consistent p h)
      (matchingFrame_stable p h inj (by omega)))

theorem php65_previous_unit {ρ : List Php65Clause} (run : IsRUPRun (PHP 6 5) (∅ :: ρ)) :
    ∃ C ∈ ρ, C.card = 1 := by
  let p : Fin 0 → Fin 6 := Fin.elim0
  let h : Fin 0 → Fin 5 := Fin.elim0
  have emptyFrame (l : Literal (Fin 6 × Fin 5)) : ¬ MatchingFrame p h l := by
    rcases l with ⟨⟨i, j⟩, b⟩
    cases b
    · rintro ⟨_, ⟨a, _⟩ | ⟨a, _⟩⟩ <;> exact a.elim0
    · rintro ⟨a, _⟩
      exact a.elim0
  have ok := matchingFrame_consistent p h
  have blocked := blocks_of_run_empty run ok
    (matchingFrame_stable p h (fun a _ _ => a.elim0) (by decide))
  obtain ⟨newer, older, C, rfl, unit, _⟩ := blocks_iff_split.mp blocked
  obtain ⟨l, hl, _, _, other⟩ := (unit_iff_unique_open ok).mp unit
  have eq : C = {l} := by
    ext k
    simp only [Finset.mem_singleton]
    exact ⟨fun hk => by_contra fun ne => emptyFrame _ (other k hk ne), fun h => h ▸ hl⟩
  exact ⟨C, List.mem_append_right newer List.mem_cons_self, by rw [eq, Finset.card_singleton]⟩

end PnpResearch.RupFrames


namespace PnpResearch.RupFrames

open PEqualNP.ProofComplexity PEqualNP.Search

variable {V : Type}

/-- Replacing every old clause by a subclause preserves RUP. A unit derivation whose
conclusion was removed from its reason already forces a conflict in the new database. -/
theorem rup_of_subsumption {Γ Δ : Set (Clause V)} {C : Clause V}
    (subs : ∀ D ∈ Γ, ∃ E ∈ Δ, E ⊆ D) (rup : IsRUP Γ C) : IsRUP Δ C := by
  classical
  by_contra noConflict
  have transfer {l : Literal V}
      (forces : UPForces Γ (negLit '' (↑C : Set (Literal V))) l) :
      UPForces Δ (negLit '' (↑C : Set (Literal V))) l := by
    induction forces with
    | hyp assumed => exact .hyp assumed
    | @unit D l hD _ _ ih =>
      obtain ⟨E, hE, sub⟩ := subs D hD
      by_cases retained : l ∈ E
      · exact .unit hE retained (fun k hk neq => ih k (sub hk) neq)
      · exact (noConflict ⟨E, hE, fun k hk =>
          ih k (sub hk) (fun e => retained (e ▸ hk))⟩).elim
  obtain ⟨D, hD, force⟩ := rup
  obtain ⟨E, hE, sub⟩ := subs D hD
  exact noConflict ⟨E, hE, fun l hl => transfer (force l (sub hl))⟩

theorem replace_learned_by_subclause {F : Set (Clause V)} {older : List (Clause V)}
    {C D : Clause V} (newer : List (Clause V)) (run : IsRUPRun F (newer ++ C :: older))
    (learnD : IsRUP (F ∪ {E | E ∈ older}) D) (sub : D ⊆ C) :
    IsRUPRun F (newer ++ D :: older) := by
  induction newer with
  | nil =>
    cases run with
    | learn prior _ => exact .learn prior learnD
  | cons head tail ih =>
    cases run with
    | learn prior rup =>
      apply IsRUPRun.learn (ih prior)
      apply rup_of_subsumption _ rup
      intro E belongs
      rcases belongs with base | old
      · exact ⟨E, Or.inl base, Finset.Subset.refl E⟩
      · rcases List.mem_append.mp old with hTail | hOld
        · exact ⟨E, Or.inr (List.mem_append_left _ hTail), Finset.Subset.refl E⟩
        · rcases List.mem_cons.mp hOld with rfl | hOlder
          · exact ⟨D, Or.inr (List.mem_append_right _ List.mem_cons_self), sub⟩
          · exact ⟨E, Or.inr (List.mem_append_right _ (List.mem_cons_of_mem _ hOlder)),
              Finset.Subset.refl E⟩

theorem replace_first_learned_by_subclause {F : Set (Clause V)} {C D : Clause V}
    (newer : List (Clause V)) (run : IsRUPRun F (newer ++ [C]))
    (learnD : IsRUP F D) (sub : D ⊆ C) : IsRUPRun F (newer ++ [D]) := by
  apply replace_learned_by_subclause newer run _ sub
  simpa using learnD

def AssumptionsConsistent (C : Clause V) : Prop :=
  Consistent (fun l => l ∈ negLit '' (↑C : Set (Literal V)))

private theorem taut_pair_of_not_assumptionsConsistent {C : Clause V}
    (inconsistent : ¬ AssumptionsConsistent C) : ∃ l ∈ C, negLit l ∈ C := by
  classical
  by_contra noPair
  apply inconsistent
  rintro _ ⟨l, hl, rfl⟩ ⟨k, hk, eq⟩
  have e := congrArg negLit eq
  simp only [neg_neg] at e
  exact noPair ⟨l, hl, e ▸ hk⟩

private theorem negLit_ne_self (l : Literal V) : negLit l ≠ l := by
  rcases l with ⟨v, b⟩
  cases b <;> simp [negLit]

private theorem stable_of_taut_pair (S : Literal V → Prop) {C : Clause V}
    (taut : ∃ l ∈ C, negLit l ∈ C) : Stable S C := by
  classical
  obtain ⟨l, hl, hn⟩ := taut
  by_cases positive : S l
  · exact Or.inl ⟨l, hl, positive⟩
  · by_cases negative : S (negLit l)
    · exact Or.inl ⟨negLit l, hn, negative⟩
    · exact Or.inr ⟨l, hl, negLit l, hn, (negLit_ne_self l).symm, negative,
        by simpa only [neg_neg] using positive⟩

/-- RUP of a clause with consistent assumptions survives dropping tautological clauses. -/
theorem rup_of_drop_tautologies {Γ Δ : Set (Clause V)} {C : Clause V}
    (retained : ∀ D ∈ Γ, D ∈ Δ ∨ ¬ AssumptionsConsistent D)
    (ok : AssumptionsConsistent C) (rup : IsRUP Γ C) : IsRUP Δ C := by
  apply (rup_iff_no_frame Δ C ok).mpr
  rintro ⟨S, consistent, dead, stable⟩
  apply (rup_iff_no_frame Γ C ok).mp rup
  refine ⟨S, consistent, dead, ?_⟩
  intro D hD
  rcases retained D hD with kept | taut
  · exact stable D kept
  · exact stable_of_taut_pair S (taut_pair_of_not_assumptionsConsistent taut)

/-- Delete all learned clauses whose negated assumptions are inconsistent. -/
theorem remove_tautological_steps {F : Set (Clause V)} {ρ : List (Clause V)}
    (run : IsRUPRun F ρ) :
    ∃ σ, IsRUPRun F σ ∧ List.Sublist σ ρ ∧
      ∀ C, C ∈ σ ↔ C ∈ ρ ∧ AssumptionsConsistent C := by
  classical
  induction run with
  | nil => exact ⟨[], .nil, .slnil, by simp⟩
  | @learn older learned prior rup ih =>
    obtain ⟨σ, runσ, sub, memσ⟩ := ih
    by_cases ok : AssumptionsConsistent learned
    · have rupσ : IsRUP (F ∪ {D | D ∈ σ}) learned := by
        apply rup_of_drop_tautologies _ ok rup
        intro D old
        rcases old with base | mem
        · exact Or.inl (Or.inl base)
        · by_cases good : AssumptionsConsistent D
          · exact Or.inl (Or.inr ((memσ D).mpr ⟨mem, good⟩))
          · exact Or.inr good
      refine ⟨learned :: σ, .learn runσ rupσ, .cons_cons learned sub, ?_⟩
      intro C
      simp only [List.mem_cons, memσ, or_and_right]
      constructor
      · rintro (rfl | h)
        · exact Or.inl ⟨rfl, ok⟩
        · exact Or.inr h
      · exact fun h => h.imp And.left id
    · refine ⟨σ, runσ, .cons learned sub, ?_⟩
      intro C
      simp only [List.mem_cons, memσ, or_and_right]
      constructor
      · exact Or.inr
      · rintro (⟨rfl, bad⟩ | h)
        · exact (ok bad).elim
        · exact h

theorem remove_tautologies_from_refutation {F : Set (Clause V)} {ρ : List (Clause V)}
    (run : IsRUPRun F ρ) (empty : (∅ : Clause V) ∈ ρ) :
    ∃ σ, IsRUPRun F σ ∧ (∅ : Clause V) ∈ σ ∧ σ.length ≤ ρ.length ∧
      ∀ C ∈ σ, AssumptionsConsistent C := by
  obtain ⟨σ, clean, sub, memσ⟩ := remove_tautological_steps run
  have emptyOk : AssumptionsConsistent (∅ : Clause V) := by
    simp [AssumptionsConsistent, Consistent]
  exact ⟨σ, clean, (memσ _).mpr ⟨empty, emptyOk⟩, sub.length_le,
    fun C hC => ((memσ C).mp hC).2⟩

end PnpResearch.RupFrames
