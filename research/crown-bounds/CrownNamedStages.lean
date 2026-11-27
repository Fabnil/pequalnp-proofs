import CrownOrFrontier
import CrownRedundantReads

namespace CrownNamedStages

open CrownForks CrownForest CrownForestCost CrownProfiles CrownVisibility CrownFourProfiles CrownOrFrontier
open CrownPairFormula CrownOrStages CrownReadSupport PnpResearch
open CrownProfileThree.Network (ones)

variable {I A B : Type}

private def formulasFor {A B : Type} :
    SharedFormula A → (A → B) → (ℕ → B) → List (Formula B)
  | .tree f, raw, _ => [rename f raw]
  | .share f _ rest, raw, shared =>
    rename f raw :: formulasFor rest (withHead (shared 0) raw) (fun i => shared (i + 1))

/-- All shared formulas followed by the output formula. Every argument has
    one name throughout the list, so direct reads can be counted by stage. -/
def formulas (E : SharedFormula I) : List (Formula (I ⊕ ℕ)) := formulasFor E Sum.inl Sum.inr

private theorem lengthFor (E : SharedFormula A) (raw : A → B) (shared : ℕ → B) :
    (formulasFor E raw shared).length = numShared E + 1 := by
  induction E generalizing shared <;> simp only [formulasFor, List.length_cons, List.length_nil, numShared, *]

theorem length_formulas (E : SharedFormula I) : (formulas E).length = numShared E + 1 :=
  lengthFor E Sum.inl Sum.inr

private theorem evalFor (E : SharedFormula A) (raw : A → B) (shared : ℕ → B) (value : B → Bool)
    (known : ∀ k, value (shared k) = bitAt (profile E (value ∘ raw)) k) :
    (formulasFor E raw shared).map (fun f => f.evalWith value) =
      profile E (value ∘ raw) ++ [E.eval (value ∘ raw)] := by
  induction E generalizing shared with
  | tree f => simp [formulasFor, profile, SharedFormula.eval, eval_rename]
  | share f extra rest ih =>
    have head : value (shared 0) = f.evalWith (value ∘ raw) := known 0
    have next : value ∘ withHead (shared 0) raw =
        withHead (f.evalWith (value ∘ raw)) (value ∘ raw) := by
      funext a
      cases a with
      | none => exact head
      | some a => rfl
    have tail := ih (withHead (shared 0) raw) (fun k => shared (k + 1)) (fun k => by
      rw [next]
      exact known (k + 1))
    simp only [formulasFor, List.map_cons, eval_rename, tail, next, profile, List.cons_append,
      SharedFormula.eval]

theorem eval_formulas (E : SharedFormula I) (x : I → Bool) :
    (formulas E).map (fun f => f.evalWith (supply (profile E x) x)) =
      profile E x ++ [E.eval x] :=
  evalFor E Sum.inl Sum.inr (supply (profile E x) x) fun _ => rfl

private theorem stock_no_flags (E : SharedFormula A) (raw : A → B) (shared : ℕ → B)
    (w : B → ℕ) (zero : ∀ k, w (shared k) = 0) :
    stock (formulasFor E raw shared) w = E.weight (w ∘ raw) := by
  induction E generalizing shared with
  | tree f => simpa only [formulasFor, stock, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, SharedFormula.weight] using weight_rename f raw w
  | share f extra rest ih =>
    have inherited : w ∘ withHead (shared 0) raw = withHead 0 (w ∘ raw) := by
      funext a
      cases a with
      | none => exact zero 0
      | some a => rfl
    change leafWeight (rename f raw) w +
      stock (formulasFor rest (withHead (shared 0) raw) (fun k => shared (k + 1))) w = _
    rw [weight_rename, ih (withHead (shared 0) raw) (fun k => shared (k + 1)) (fun k => zero _)]
    rw [inherited]
    rfl

theorem raw_reads [DecidableEq I] (E : SharedFormula I) (i : I) :
    stock (formulas E) (ones (Sum.inl i)) = E.weight (ones i) := by
  have mass : ones (Sum.inl i : I ⊕ ℕ) ∘ Sum.inl = ones i := by
    funext x
    simp [ones, singletonInput]
  rw [formulas, stock_no_flags E Sum.inl Sum.inr _ (by intro k; simp [ones, singletonInput]), mass]

private theorem leaf_zero (f : Formula A) : leafWeight f (fun _ => 0) = 0 := by
  simpa [stock] using stock_zero [f]

private theorem stock_flag (E : SharedFormula A) (valid : E.Valid) (raw : A → B)
    (shared : ℕ → B) (w : B → ℕ) (k m : ℕ)
    (zero : ∀ a, w (raw a) = 0) (selected : ∀ j, w (shared j) = (decide (j = k)).toNat)
    (use : (copies E)[k]? = some m) :
    stock (formulasFor E raw shared) w = m + 1 := by
  induction E generalizing k shared with
  | tree f => simp [copies] at use
  | share f extra rest ih =>
    have raw0 : w ∘ raw = fun _ => 0 := funext zero
    change leafWeight (rename f raw) w +
      stock (formulasFor rest (withHead (shared 0) raw) (fun j => shared (j + 1))) w = _
    rw [weight_rename, raw0, leaf_zero, Nat.zero_add]
    cases k with
    | zero =>
      have same : extra = m := by simpa [copies] using use
      have tail : ∀ j : ℕ, w (shared (j + 1)) = 0 := by intro j; simp [selected]
      have mass : w ∘ withHead (shared 0) raw = withHead 1 (fun _ => 0) := by
        funext a
        cases a <;> simp [zero, selected]
      rw [stock_no_flags rest _ _ _ tail, mass, valid.2.2, same]
    | succ k =>
      have zero' (a : Option _) : w (withHead (shared 0) raw a) = 0 := by
        cases a <;> simp [selected, zero]
      have selected' (j : ℕ) : w (shared (j + 1)) = (decide (j = k)).toNat := by
        rw [selected]
        simp
      exact ih valid.2.1 (withHead (shared 0) raw) (fun j => shared (j + 1)) k zero' selected'
        (by simpa [copies] using use)

theorem shared_reads [DecidableEq I] (E : SharedFormula I) (valid : E.Valid) {k m : ℕ}
    (use : (copies E)[k]? = some m) :
    stock (formulas E) (ones (Sum.inr k)) = m + 1 := by
  exact stock_flag E valid Sum.inl Sum.inr (ones (Sum.inr k)) k m
    (by intro i; simp [ones, singletonInput])
    (by intro j; simp [ones, singletonInput]) use

private theorem stage_zero (E : SharedFormula A) (raw : A → B) (shared : ℕ → B)
    (w : B → ℕ) (t : ℕ) {F : Formula B} (atStage : (formulasFor E raw shared)[t]? = some F)
    (zero : ∀ a, w (raw a) = 0) (prior : ∀ j < t, w (shared j) = 0) :
    leafWeight F w = 0 := by
  induction E generalizing t F shared with
  | tree f =>
    cases t with
    | zero =>
      have eq : rename f raw = F := by simpa [formulasFor] using atStage
      have raw0 : w ∘ raw = fun _ => 0 := funext zero
      rw [← eq, weight_rename, raw0, leaf_zero]
    | succ t => simp [formulasFor] at atStage
  | share f extra rest ih =>
    cases t with
    | zero =>
      have eq : rename f raw = F := by simpa [formulasFor] using atStage
      have raw0 : w ∘ raw = fun _ => 0 := funext zero
      rw [← eq, weight_rename, raw0, leaf_zero]
    | succ t =>
      apply ih (withHead (shared 0) raw) (fun j => shared (j + 1)) t
        (by simpa only [formulasFor, List.getElem?_cons_succ] using atStage)
      · intro a
        cases a with
        | none => exact prior 0 (by omega)
        | some a => exact zero a
      · intro j hj
        exact prior (j + 1) (by omega)

theorem reads_forward [DecidableEq I] (E : SharedFormula I) {t k : ℕ} {F : Formula (I ⊕ ℕ)}
    (atStage : (formulas E)[t]? = some F) (later : t ≤ k) : reads F (Sum.inr k) = 0 := by
  apply stage_zero E Sum.inl Sum.inr (ones (Sum.inr k)) t atStage
  · intro a
    simp [ones, singletonInput]
  · intro j before
    have ne : j ≠ k := by omega
    simp [ones, singletonInput, ne]

theorem eval_at (E : SharedFormula I) (x : I → Bool) {t : ℕ} {F : Formula (I ⊕ ℕ)}
    (atStage : (formulas E)[t]? = some F) :
    F.evalWith (supply (profile E x) x) = bitAt (profile E x ++ [E.eval x]) t := by
  have table := congrArg (fun row : List Bool => row[t]?) (eval_formulas E x)
  rw [List.getElem?_map, atStage] at table
  exact congrArg (fun result : Option Bool => result.getD false) table

private theorem rename_or (f : Formula A) (key : A → B) (pure : orOnly f) :
    orOnly (rename f key) := by
  induction f <;> simp_all [orOnly, rename]

def orOfLeaves : Formula A → Formula A
  | .var a => .var a
  | .conj l r | .disj l r => .disj (orOfLeaves l) (orOfLeaves r)

private theorem orOfLeaves_shape (f : Formula A) : orOnly (orOfLeaves f) := by
  induction f <;> simp_all [orOfLeaves, orOnly]

private theorem orOfLeaves_ge (f : Formula A) (x : A → Bool) :
    f.evalWith x ≤ (orOfLeaves f).evalWith x := by
  induction f with
  | var a => exact le_rfl
  | conj l r il ir =>
    exact le_trans (Bool.and_le_left _ _) (le_trans il (Bool.left_le_or _ _))
  | disj l r il ir =>
    exact Bool.or_le (le_trans il (Bool.left_le_or _ _)) (le_trans ir (Bool.right_le_or _ _))

/-- With disjunctions of raw inputs as arguments, keeping all singleton
    activations permits replacing every AND in a formula by OR. -/
theorem replace_by_or [DecidableEq I] (f : Formula A) (val : (I → Bool) → A → Bool)
    (atoms : ∀ a, singletonDisjunction (fun x => val x a))
    (single : ∀ i, (orOfLeaves f).evalWith (val (singletonInput i)) = true →
      f.evalWith (val (singletonInput i)) = true) :
    ∃ g, orOnly g ∧ formulaGates g = formulaGates f ∧ (∀ w, leafWeight g w = leafWeight f w) ∧
      ∀ x, g.evalWith (val x) = f.evalWith (val x) := by
  have pure := orOfLeaves_shape f
  have count : formulaGates (orOfLeaves f) = formulaGates f := by
    clear single atoms pure
    induction f <;> simp_all [orOfLeaves, formulaGates]
  have weight (w : A → ℕ) : leafWeight (orOfLeaves f) w = leafWeight f w := by
    clear single atoms pure count
    induction f <;> simp_all [orOfLeaves, leafWeight]
  have supports := eval_orOnly (orOfLeaves f) val pure atoms
  refine ⟨orOfLeaves f, pure, count, weight, fun x => le_antisymm ?_ (orOfLeaves_ge f (val x))⟩
  apply Bool.le_iff_imp.mpr
  intro on
  obtain ⟨i, present, early⟩ := (supports x).mp on
  have order (a : A) : val (singletonInput i) a ≤ val x a := by
    exact Bool.le_iff_imp.mpr (fun accepts => (atoms a x).mpr ⟨i, present, accepts⟩)
  exact Bool.le_iff_imp.mp (evalMono f order) (single i early)

private theorem or_at_for (E : SharedFormula A) (raw : A → B) (shared : ℕ → B)
    {n t : ℕ} {F : Formula B} (pure : orPrefix E n) (inside : t < n)
    (atStage : (formulasFor E raw shared)[t]? = some F) : orOnly F := by
  induction E generalizing n t F shared with
  | tree f =>
    cases n with
    | zero => omega
    | succ n => exact pure.elim
  | share f extra rest ih =>
    cases n with
    | zero => omega
    | succ n =>
      cases t with
      | zero =>
        have eq : rename f raw = F := by simpa [formulasFor] using atStage
        rw [← eq]
        exact rename_or f raw pure.1
      | succ t =>
        exact ih (withHead (shared 0) raw) (fun j => shared (j + 1)) pure.2 (Nat.lt_of_succ_lt_succ inside)
          (by simpa only [formulasFor, List.getElem?_cons_succ] using atStage)

theorem or_at (E : SharedFormula I) {n t : ℕ} {F : Formula (I ⊕ ℕ)}
    (pure : orPrefix E n) (inside : t < n) (atStage : (formulas E)[t]? = some F) :
    orOnly F :=
  or_at_for E Sum.inl Sum.inr pure inside atStage

private theorem two_shared_for [DecidableEq I] (E : SharedFormula A)
    (val : (I → Bool) → A → Bool) (key : A → I ⊕ ℕ) (start : ℕ)
    (injective : Function.Injective key)
    (earlierName : ∀ a k, key a = Sum.inr k → k < start)
    (rawValue : ∀ a i, key a = Sum.inl i → ∀ x, val x a = x i)
    (mono : ∀ {x y}, (∀ i, x i ≤ y i) → ∀ a, val x a ≤ val y a)
    (value : (I → Bool) → I ⊕ ℕ → Bool)
    (agrees : ∀ x a, value x (key a) = val x a)
    (known : ∀ x k, value x (Sum.inr (start + k)) = bitAt (profile E (val x)) k)
    (prepared : AllPrepared val E) {t : ℕ} {F : Formula (I ⊕ ℕ)}
    (inside : t < numShared E)
    (atStage : (formulasFor E key (fun k => Sum.inr (start + k)))[t]? = some F)
    (nonOr : ¬ orOnly F) :
    ∃ i a b, a ≠ b ∧ 0 < reads F (Sum.inr a) ∧ 0 < reads F (Sum.inr b) ∧
      value (singletonInput i) (Sum.inr a) = true ∧ value (singletonInput i) (Sum.inr b) = true ∧
      value (singletonInput i) (Sum.inr (start + t)) = true ∧
      (¬ ∀ x, value x (Sum.inr a) ≤ value x (Sum.inr b)) ∧
      (¬ ∀ x, value x (Sum.inr b) ≤ value x (Sum.inr a)) := by
  induction E generalizing t F start with
  | tree f => simp [numShared] at inside
  | @share B f extra rest ih =>
    cases t with
    | zero =>
      have same : rename f key = F := by simpa [formulasFor] using atStage
      subst F
      rcases prepared.1 with pure | ⟨_, i, ⟨a, b, useA, useB, onA, onB, ab, ba⟩, onF⟩
      · exact (nonOr (rename_or f key pure)).elim
      have isShared (u v : B) (onU : val (singletonInput i) u = true)
          (onV : val (singletonInput i) v = true) (notImplies : ¬ ∀ x, val x u ≤ val x v) :
          ∃ k, key u = Sum.inr k := by
        cases name : key u with
        | inr k => exact ⟨k, rfl⟩
        | inl raw =>
          have line := rawValue u raw name
          have same : raw = i := by simpa only [line, singletonInput, decide_eq_true_eq] using onU
          subst raw
          refine (notImplies fun x => ?_).elim
          rw [line]
          cases hx : x i with
          | false => exact Bool.false_le _
          | true =>
            have below (j : I) : singletonInput i j ≤ x j := by
              by_cases eq : j = i
              · simp [singletonInput, eq, hx]
              · simp [singletonInput, eq]
            simpa only [onV, hx] using mono below v
      obtain ⟨p, hp⟩ := isShared a b onA onB ab
      obtain ⟨q, hq⟩ := isShared b a onB onA ba
      have different : p ≠ q := by
        intro eq
        subst q
        have same := injective (hp.trans hq.symm)
        subst b
        exact ab fun _ => le_rfl
      have use (u : B) (k : ℕ) (name : key u = Sum.inr k) (used : Uses f u) :
          0 < reads (rename f key) (Sum.inr k) := by
        change 0 < leafWeight (rename f key) (ones (Sum.inr k))
        rw [weight_rename]
        have occurs := used (ones (Sum.inr k) ∘ key)
        have mass : (ones (Sum.inr k) ∘ key) u = 1 := by simp [name, ones, singletonInput]
        rw [mass] at occurs
        exact occurs
      refine ⟨i, p, q, different, use a p hp useA, use b q hq useB, ?_, ?_, ?_, ?_, ?_⟩
      · rwa [← hp, agrees]
      · rwa [← hq, agrees]
      · simpa only [known, profile, bitAt, List.getElem?_cons_zero, Option.getD_some] using onF
      · intro comparison
        exact ab (fun x => by simpa only [← hp, ← hq, agrees] using comparison x)
      · intro comparison
        exact ba (fun x => by simpa only [← hp, ← hq, agrees] using comparison x)
    | succ t =>
      let nextKey := withHead (Sum.inr start) key
      have nextInjective : Function.Injective nextKey := by
        intro a b same
        cases a with
        | none =>
          cases b with
          | none => rfl
          | some b => exact (Nat.lt_irrefl start (earlierName b start same.symm)).elim
        | some a =>
          cases b with
          | none => exact (Nat.lt_irrefl start (earlierName a start same)).elim
          | some b => exact congrArg some (injective same)
      have tail : ∃ i a b, a ≠ b ∧ 0 < reads F (Sum.inr a) ∧ 0 < reads F (Sum.inr b) ∧
          value (singletonInput i) (Sum.inr a) = true ∧ value (singletonInput i) (Sum.inr b) = true ∧
          value (singletonInput i) (Sum.inr (start + 1 + t)) = true ∧
          (¬ ∀ x, value x (Sum.inr a) ≤ value x (Sum.inr b)) ∧
          (¬ ∀ x, value x (Sum.inr b) ≤ value x (Sum.inr a)) := by
        apply ih (fun x => withHead (f.evalWith (val x)) (val x)) nextKey (start + 1)
          nextInjective ?_ ?_ ?_ ?_ ?_ prepared.2 (by simpa [numShared] using inside) ?_ nonOr
        · intro a k name
          cases a with
          | none =>
            have eq : start = k := Sum.inr.inj name
            omega
          | some a => exact Nat.lt_succ_of_lt (earlierName a k name)
        · intro a i name x
          cases a with
          | none => cases name
          | some a => exact rawValue a i name x
        · intro x y order a
          cases a with
          | none => exact evalMono f (mono order)
          | some a => exact mono order a
        · intro x a
          cases a with
          | none =>
            change value x (Sum.inr start) = f.evalWith (val x)
            simpa only [Nat.add_zero, profile, bitAt,
              List.getElem?_cons_zero, Option.getD_some] using known x 0
          | some a => exact agrees x a
        · intro x k
          simpa only [Nat.add_assoc, Nat.add_comm 1, profile, bitAt,
            List.getElem?_cons_succ] using known x (k + 1)
        · simpa only [formulasFor, List.getElem?_cons_succ, nextKey, Nat.add_zero,
            Nat.add_assoc, Nat.add_comm 1] using atStage
      simpa only [Nat.add_assoc, Nat.add_comm 1] using tail

/-- At some singleton the shared formula and two incomparable shared
    arguments are active together. -/
theorem incomparable_arguments [DecidableEq I] (E : SharedFormula I)
    (prepared : AllPrepared (fun x => x) E) {t : ℕ} {F : Formula (I ⊕ ℕ)}
    (inside : t < numShared E) (atStage : (formulas E)[t]? = some F) (nonOr : ¬ orOnly F) :
    ∃ i a b, a < t ∧ b < t ∧ a ≠ b ∧ 0 < reads F (Sum.inr a) ∧ 0 < reads F (Sum.inr b) ∧
      bitAt (profile E (singletonInput i)) a = true ∧ bitAt (profile E (singletonInput i)) b = true ∧
      bitAt (profile E (singletonInput i)) t = true ∧
      (¬ ∀ x, bitAt (profile E x) a ≤ bitAt (profile E x) b) ∧
      (¬ ∀ x, bitAt (profile E x) b ≤ bitAt (profile E x) a) := by
  obtain ⟨i, a, b, ne, useA, useB, onA, onB, onF, ab, ba⟩ := two_shared_for E (fun x => x) Sum.inl 0
    Sum.inl_injective (by intro _ _ eq; cases eq)
    (by intro j i eq x; cases eq; rfl) (fun order => order) (fun x => supply (profile E x) x)
    (fun _ _ => rfl) (by simp [supply]) prepared inside
    (by simpa only [formulas, Nat.zero_add] using atStage) nonOr
  have before (k : ℕ) (used : 0 < reads F (Sum.inr k)) : k < t := by
    by_contra! late
    rw [reads_forward E atStage late] at used
    omega
  change bitAt (profile E (singletonInput i)) (0 + t) = true at onF
  exact ⟨i, a, b, before a useA, before b useB, ne, useA, useB, onA, onB,
    by simpa only [Nat.zero_add] using onF, ab, ba⟩

theorem two_shared_arguments [DecidableEq I] (E : SharedFormula I)
    (prepared : AllPrepared (fun x => x) E) {t : ℕ} {F : Formula (I ⊕ ℕ)}
    (inside : t < numShared E) (atStage : (formulas E)[t]? = some F) (nonOr : ¬ orOnly F) :
    ∃ i a b, a < t ∧ b < t ∧ a ≠ b ∧ 0 < reads F (Sum.inr a) ∧ 0 < reads F (Sum.inr b) ∧
      bitAt (profile E (singletonInput i)) a = true ∧ bitAt (profile E (singletonInput i)) b = true ∧
      bitAt (profile E (singletonInput i)) t = true := by
  obtain ⟨i, a, b, ha, hb, ne, useA, useB, onA, onB, onF, _, _⟩ :=
    incomparable_arguments E prepared inside atStage nonOr
  exact ⟨i, a, b, ha, hb, ne, useA, useB, onA, onB, onF⟩

/-- The first AND has an overlap singleton and an exclusive singleton for
    each of its two incomparable OR arguments. -/
theorem first_and_singletons [DecidableEq I] (E : SharedFormula I)
    (prepared : AllPrepared (fun x => x) E) {t : ℕ} {F : Formula (I ⊕ ℕ)}
    (pure : orPrefix E t) (inside : t < numShared E)
    (atStage : (formulas E)[t]? = some F) (nonOr : ¬ orOnly F) :
    ∃ i j k a b, a < t ∧ b < t ∧ a ≠ b ∧ 0 < reads F (Sum.inr a) ∧ 0 < reads F (Sum.inr b) ∧
      bitAt (profile E (singletonInput i)) a = true ∧ bitAt (profile E (singletonInput i)) b = true ∧
      bitAt (profile E (singletonInput i)) t = true ∧
      bitAt (profile E (singletonInput j)) a = true ∧ bitAt (profile E (singletonInput j)) b = false ∧
      bitAt (profile E (singletonInput k)) b = true ∧ bitAt (profile E (singletonInput k)) a = false := by
  classical
  obtain ⟨i, a, b, ha, hb, ne, useA, useB, onA, onB, onF, ab, ba⟩ :=
    incomparable_arguments E prepared inside atStage nonOr
  have exclusive (s u : ℕ) (hs : s < t) (hu : u < t)
      (notImp : ¬ ∀ x, bitAt (profile E x) s ≤ bitAt (profile E x) u) :
      ∃ j, bitAt (profile E (singletonInput j)) s = true ∧
        bitAt (profile E (singletonInput j)) u = false := by
    by_contra none
    have disj (r : ℕ) (early : r < t) : singletonDisjunction (fun x => bitAt (profile E x) r) :=
      orStage E t pure (fun x a => x a) projection r early
    apply notImp
    apply implies_of_singletons (disj s hs) (disj u hu)
    intro j
    apply Bool.le_iff_imp.mpr
    intro on
    by_contra off
    exact none ⟨j, on, Bool.eq_false_of_not_eq_true off⟩
  obtain ⟨j, onJA, offJB⟩ := exclusive a b ha hb ab
  obtain ⟨k, onKB, offKA⟩ := exclusive b a hb ha ba
  exact ⟨i, j, k, a, b, ha, hb, ne, useA, useB, onA, onB, onF, onJA, offJB, onKB, offKA⟩

private theorem flag_mono (E : SharedFormula A) {x y : A → Bool} (order : ∀ a, x a ≤ y a)
    (k : ℕ) : bitAt (profile E x) k ≤ bitAt (profile E y) k := by
  induction E generalizing k with
  | tree f => exact le_rfl
  | share f extra rest ih =>
    have head := evalMono f order
    cases k with
    | zero => exact head
    | succ k => exact ih (withHeadMono head order) k

private theorem leaf_with_positive_weight [DecidableEq A] (f : Formula A) (w : A → ℕ)
    (positive : 0 < leafWeight f w) : ∃ a, 0 < w a ∧ 0 < reads f a := by
  induction f with
  | var a => exact ⟨a, positive, by simp [reads, leafWeight, singletonInput]⟩
  | conj l r il ir | disj l r il ir =>
    change 0 < leafWeight l w + leafWeight r w at positive
    by_cases onL : 0 < leafWeight l w
    · obtain ⟨a, ha, use⟩ := il onL
      refine ⟨a, ha, ?_⟩
      simp only [reads, leafWeight] at use ⊢
      omega
    · obtain ⟨a, ha, use⟩ := ir (by omega)
      refine ⟨a, ha, ?_⟩
      simp only [reads, leafWeight] at use ⊢
      omega

/-- If adjoining an input turns a stage on, that stage reads the new input
    or a newly active earlier signal. This includes the final formula. -/
theorem must_read_change [DecidableEq I] (E : SharedFormula I) {i j : I}
    {t : ℕ} {F : Formula (I ⊕ ℕ)} (atStage : (formulas E)[t]? = some F)
    (before : bitAt (profile E (singletonInput j) ++ [E.eval (singletonInput j)]) t = false)
    (after : bitAt (profile E (pairInput i j) ++ [E.eval (pairInput i j)]) t = true) :
    0 < reads F (Sum.inl i) ∨ ∃ k < t, 0 < reads F (Sum.inr k) ∧
      bitAt (profile E (singletonInput j)) k = false ∧ bitAt (profile E (pairInput i j)) k = true := by
  let x := supply (profile E (singletonInput j)) (singletonInput j)
  let y := supply (profile E (pairInput i j)) (pairInput i j)
  have order (a : I ⊕ ℕ) : x a ≤ y a := by
    cases a with
    | inl a => exact TwoShared.otherSingleton_pair i j a
    | inr k => exact flag_mono E (TwoShared.otherSingleton_pair i j) k
  have off : F.evalWith x = false := (eval_at E (singletonInput j) atStage).trans before
  have on : F.evalWith y = true := (eval_at E (pairInput i j) atStage).trans after
  have change : 0 < leafWeight F (fun a => rise (x a) (y a)) := by
    by_contra! no
    have equal := eqOfNoRise F order (Nat.eq_zero_of_le_zero no)
    rw [off, on] at equal
    contradiction
  obtain ⟨a, changing, read⟩ := leaf_with_positive_weight F _ change
  have truth (p q : Bool) : 0 < rise p q → p = false ∧ q = true := by
    revert p q
    decide
  obtain ⟨offA, onA⟩ := truth _ _ changing
  cases a with
  | inl a =>
    change singletonInput j a = false at offA
    change (singletonInput i a || singletonInput j a) = true at onA
    rw [offA, Bool.or_false] at onA
    have eq : a = i := by simpa [singletonInput] using onA
    exact Or.inl (eq ▸ read)
  | inr k =>
    have earlier : k < t := by
      by_contra! late
      exact (Nat.ne_of_gt read) (reads_forward E atStage late)
    exact Or.inr ⟨k, earlier, read, offA, onA⟩

/-- The sequence includes the shared signals and ends with the output. -/
def stageValue (E : SharedFormula I) (x : I → Bool) (t : ℕ) : Bool :=
  bitAt (profile E x ++ [E.eval x]) t

private theorem stageValue_of_shared (E : SharedFormula I) (x : I → Bool) {t : ℕ}
    (inside : t < numShared E) : stageValue E x t = bitAt (profile E x) t := by
  unfold stageValue bitAt
  rw [List.getElem?_append_left (by simpa only [profile_length] using inside)]

/-- Stages that read the same raw arguments on two inputs and depend only on
    each other or on fixed stages also agree on those inputs. -/
theorem closed_stages_agree [DecidableEq I] (E : SharedFormula I) (x y : I → Bool)
    (fixed closed : ℕ → Prop) (known : ∀ t, fixed t → stageValue E x t = stageValue E y t)
    (inputsAgree : ∀ t, ∀ {F}, (formulas E)[t]? = some F → closed t →
      ∀ i, 0 < reads F (Sum.inl i) → x i = y i)
    (parents : ∀ t, ∀ {F}, (formulas E)[t]? = some F → closed t →
      ∀ k, 0 < reads F (Sum.inr k) → fixed k ∨ closed k) :
    ∀ t, ∀ {F}, (formulas E)[t]? = some F → closed t → stageValue E x t = stageValue E y t := by
  intro t
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    intro F atStage h
    let u := supply (profile E x) x
    let v := supply (profile E y) y
    have agree (a : I ⊕ ℕ) (used : 0 < reads F a) : u a = v a := by
      cases a with
      | inl i => exact inputsAgree t atStage h i used
      | inr k =>
        have earlier : k < t := by
          by_contra! late
          rw [reads_forward E atStage late] at used
          omega
        have tPresent := (List.getElem?_eq_some_iff.mp atStage).choose
        have kPresent : k < (formulas E).length := earlier.trans tPresent
        have inside : k < numShared E := by
          rw [length_formulas] at tPresent
          omega
        have before : stageValue E x k = stageValue E y k := by
          rcases parents t atStage h k used with held | done
          · exact known k held
          · exact ih k earlier (List.getElem?_eq_getElem kPresent) done
        exact (stageValue_of_shared E x inside).symm.trans
          (before.trans (stageValue_of_shared E y inside))
    have equal : F.evalWith u = F.evalWith v := le_antisymm
      (CrownRedundantReads.evalMonoOnReads F (fun a ha => (agree a ha).le))
      (CrownRedundantReads.evalMonoOnReads F (fun a ha => (agree a ha).symm.le))
    rw [eval_at E x atStage, eval_at E y atStage] at equal
    exact equal

/-- A singleton that dominates the arguments of a pair at a given stage
    transmits its negative evaluation to the pair. -/
theorem pair_off_of_dominated [DecidableEq I] (E : SharedFormula I) (i j w : I)
    {t : ℕ} {F : Formula (I ⊕ ℕ)} (atStage : (formulas E)[t]? = some F)
    (off : stageValue E (singletonInput w) t = false)
    (noI : reads F (Sum.inl i) = 0) (noJ : reads F (Sum.inl j) = 0)
    (dominated : ∀ k < t, 0 < reads F (Sum.inr k) →
      bitAt (profile E (pairInput i j)) k ≤ bitAt (profile E (singletonInput w)) k) :
    stageValue E (pairInput i j) t = false := by
  let u := supply (profile E (pairInput i j)) (pairInput i j)
  let v := supply (profile E (singletonInput w)) (singletonInput w)
  have le (a : I ⊕ ℕ) (used : 0 < reads F a) : u a ≤ v a := by
    cases a with
    | inl a =>
      have neI : a ≠ i := fun eq => by subst a; omega
      have neJ : a ≠ j := fun eq => by subst a; omega
      simp [u, supply, pairInput, singletonInput, neI, neJ]
    | inr a =>
      have earlier : a < t := by
        by_contra! late
        rw [reads_forward E atStage late] at used
        omega
      exact dominated a earlier used
  have step := CrownRedundantReads.evalMonoOnReads F le
  rw [eval_at E _ atStage, eval_at E _ atStage] at step
  change stageValue E (pairInput i j) t ≤ stageValue E (singletonInput w) t at step
  rw [off] at step
  exact Bool.le_antisymm step (Bool.false_le _)

/-- A pair inherits an accepting singleton's value when all of that
    singleton's active arguments persist at the stage. -/
theorem pair_on_of_dominates [DecidableEq I] (E : SharedFormula I) (i j w : I)
    {t : ℕ} {F : Formula (I ⊕ ℕ)} (atStage : (formulas E)[t]? = some F)
    (on : stageValue E (singletonInput w) t = true) (noW : reads F (Sum.inl w) = 0)
    (dominates : ∀ k < t, 0 < reads F (Sum.inr k) →
      bitAt (profile E (singletonInput w)) k ≤ bitAt (profile E (pairInput i j)) k) :
    stageValue E (pairInput i j) t = true := by
  let u := supply (profile E (singletonInput w)) (singletonInput w)
  let v := supply (profile E (pairInput i j)) (pairInput i j)
  have le (a : I ⊕ ℕ) (used : 0 < reads F a) : u a ≤ v a := by
    cases a with
    | inl a =>
      have ne : a ≠ w := fun eq => by subst a; omega
      simp [u, supply, singletonInput, ne]
    | inr a =>
      have earlier : a < t := by
        by_contra! late
        rw [reads_forward E atStage late] at used
        omega
      exact dominates a earlier used
  have step := CrownRedundantReads.evalMonoOnReads F le
  rw [eval_at E _ atStage, eval_at E _ atStage] at step
  change stageValue E (singletonInput w) t ≤ stageValue E (pairInput i j) t at step
  rw [on] at step
  exact Bool.le_antisymm (Bool.le_true _) step

/-- A set of possible pair activations is sound if it contains the singleton
    activations and closes under a possible change from each singleton. -/
theorem pair_activation_covered [DecidableEq I] (E : SharedFormula I) (i j : I) (first : ℕ)
    (pure : orPrefix E first) (bounded : first ≤ numShared E) (possible : ℕ → Prop)
    (singles : ∀ t, stageValue E (singletonInput i) t = true ∨
      stageValue E (singletonInput j) t = true → possible t)
    (mixed : ∀ t ≥ first, ∀ {F}, (formulas E)[t]? = some F →
      (0 < reads F (Sum.inl j) ∨ ∃ k < t,
        0 < reads F (Sum.inr k) ∧ stageValue E (singletonInput i) k = false ∧ possible k) →
      (0 < reads F (Sum.inl i) ∨ ∃ k < t,
        0 < reads F (Sum.inr k) ∧ stageValue E (singletonInput j) k = false ∧ possible k) → possible t) :
    ∀ t, ∀ {F}, (formulas E)[t]? = some F → stageValue E (pairInput i j) t = true → possible t := by
  intro t
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    intro F atStage on
    by_cases hasSingle : stageValue E (singletonInput i) t = true ∨
        stageValue E (singletonInput j) t = true
    · exact singles t hasSingle
    have offI := Bool.eq_false_of_not_eq_true (fun h => hasSingle (Or.inl h))
    have offJ := Bool.eq_false_of_not_eq_true (fun h => hasSingle (Or.inr h))
    by_cases early : t < first
    · have inside := lt_of_lt_of_le early bounded
      rw [stageValue_of_shared E _ inside, orStage_pair E _ pure t early,
        ← stageValue_of_shared E _ inside, ← stageValue_of_shared E _ inside, offI, offJ] at on
      contradiction
    have position := (List.getElem?_eq_some_iff.mp atStage).choose
    rw [length_formulas] at position
    have extend {source current : I} (same : pairInput source current = pairInput i j)
        (off : stageValue E (singletonInput current) t = false) :
        0 < reads F (Sum.inl source) ∨ ∃ k < t, 0 < reads F (Sum.inr k) ∧
          stageValue E (singletonInput current) k = false ∧ possible k := by
      have after : stageValue E (pairInput source current) t = true := same.symm ▸ on
      rcases must_read_change E atStage off after with raw | ⟨k, earlier, use, zero, one⟩
      · exact Or.inl raw
      have inside : k < numShared E := by omega
      have present : k < (formulas E).length := by simpa only [length_formulas] using earlier.trans position
      refine Or.inr ⟨k, earlier, use, (stageValue_of_shared E _ inside).trans zero, ?_⟩
      apply ih k earlier (List.getElem?_eq_getElem present)
      exact (stageValue_of_shared E _ inside).trans (by simpa only [same] using one)
    exact mixed t (Nat.le_of_not_gt early) atStage
      (extend (by funext a; simp only [pairInput, Bool.or_comm]) offI) (extend rfl offJ)

end CrownNamedStages
