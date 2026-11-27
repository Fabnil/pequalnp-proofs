import CrownThreshold
import ReadOnce

/-!
Cut accounting for positive formulas with shared results. The separation
argument adapts the AND cuts in the project's L_meta_18242. A baseline
assignment lets us freeze inputs and discard cuts that cannot separate
the remaining singletons.
-/

namespace CrownForks

open Finset PnpResearch

def leafWeight {A : Type} (f : Formula A) (w : A → ℕ) : ℕ :=
  match f with
  | .var a => w a
  | .conj l r | .disj l r => leafWeight l w + leafWeight r w

theorem leafWeight_add {A : Type} (f : Formula A) (u v : A → ℕ) :
    leafWeight f (fun a => u a + v a) = leafWeight f u + leafWeight f v := by
  induction f <;> simp_all [leafWeight] <;> omega

theorem leafWeight_mul {A : Type} (f : Formula A) (u : A → ℕ) (k : ℕ) :
    leafWeight f (fun a => k * u a) = k * leafWeight f u := by
  induction f <;> simp_all [leafWeight, Nat.mul_add]

theorem evalMono {A : Type} (f : Formula A) {u v : A → Bool}
    (le : ∀ a, u a ≤ v a) : f.evalWith u ≤ f.evalWith v := by
  induction f with
  | var a => exact le a
  | conj l r hl hr =>
    exact Bool.le_and (le_trans (Bool.and_le_left _ _) hl) (le_trans (Bool.and_le_right _ _) hr)
  | disj l r hl hr =>
    exact Bool.or_le (le_trans hl (Bool.left_le_or _ _)) (le_trans hr (Bool.right_le_or _ _))

theorem evalZero {A : Type} (f : Formula A) :
    f.evalWith (fun _ => false) = false := by
  induction f <;> simp_all [Formula.evalWith]

def rise (before now : Bool) : ℕ := ((!before) && now).toNat

theorem eqOfNoRise {A : Type} (f : Formula A) {base value : A → Bool}
    (le : ∀ a, base a ≤ value a)
    (zero : leafWeight f (fun a => rise (base a) (value a)) = 0) :
    f.evalWith base = f.evalWith value := by
  induction f with
  | var a =>
    have h := le a
    cases ha : base a <;> cases hb : value a <;>
      simp_all [rise, leafWeight, Formula.evalWith, Bool.le_iff_imp]
  | conj l r hl hr | disj l r hl hr =>
    simp only [leafWeight, Nat.add_eq_zero_iff] at zero
    simp only [Formula.evalWith, hl zero.1, hr zero.2]

abbrev Cut (I : Type) := I → Option Bool

def opposing (l r : Bool) : Option Bool :=
  if l = r then none else some r

def cutAt (lb rb l r : Bool) : Option Bool :=
  if lb || rb then none else opposing l r

def cuts {A I : Type} (f : Formula A) (base : A → Bool) (single : I → A → Bool) :
    List (Cut I) :=
  match f with
  | .var _ => []
  | .conj l r =>
    (fun i => cutAt (l.evalWith base) (r.evalWith base) (l.evalWith (single i))
      (r.evalWith (single i))) :: (cuts l base single ++ cuts r base single)
  | .disj l r => cuts l base single ++ cuts r base single

def degree {I : Type} (rows : List (Cut I)) (i : I) : ℕ :=
  rows.countP fun row => (row i).isSome

theorem degree_append {I : Type} (u v : List (Cut I)) (i : I) :
    degree (u ++ v) i = degree u i + degree v i := by
  simp [degree, List.countP_append]

def splits {I : Type} (row : Cut I) (i j : I) : Prop :=
  (row i = some false ∧ row j = some true) ∨ (row i = some true ∧ row j = some false)

def separated {I : Type} (rows : List (Cut I)) (i j : I) : Prop :=
  ∃ row ∈ rows, splits row i j

theorem separated_append {I : Type} (u v : List (Cut I)) (i j : I) :
    separated (u ++ v) i j ↔ separated u i j ∨ separated v i j := by
  simp only [separated, List.mem_append, or_and_right, exists_or]

private theorem andRise : ∀ lb rb l r : Bool, lb ≤ l → rb ≤ r →
    (cutAt lb rb l r).isSome.toNat + rise (lb && rb) (l && r) ≤
      rise lb l + rise rb r := by decide

private theorem orRise : ∀ lb rb l r : Bool, lb ≤ l → rb ≤ r →
    rise (lb || rb) (l || r) ≤ rise lb l + rise rb r := by decide

theorem cutCharge {A I : Type} (f : Formula A) (base : A → Bool) (single : I → A → Bool)
    (i : I) (le : ∀ a, base a ≤ single i a) :
    degree (cuts f base single) i + rise (f.evalWith base) (f.evalWith (single i)) ≤
      leafWeight f (fun a => rise (base a) (single i a)) := by
  induction f with
  | var a => simp [cuts, degree, leafWeight, Formula.evalWith]
  | conj l r hl hr =>
    have cost := andRise _ _ _ _ (evalMono l le) (evalMono r le)
    simp only [cuts, Formula.evalWith, leafWeight]
    have count : ∀ (c : Cut I) (rs : List (Cut I)),
        degree (c :: rs) i = degree rs i + (c i).isSome.toNat := by
      intro c rs
      cases h : (c i).isSome <;> simp [degree, h, Nat.add_comm]
    rw [count, degree_append]
    omega
  | disj l r hl hr =>
    have cost := orRise _ _ _ _ (evalMono l le) (evalMono r le)
    simp only [cuts, Formula.evalWith, leafWeight, degree_append]
    omega

theorem cutSeparate {A I : Type} (f : Formula A) (base : A → Bool)
    (single : I → A → Bool) (pair : A → Bool) (i j : I) (escape : Prop)
    (li : ∀ a, base a ≤ single i a) (lj : ∀ a, base a ≤ single j a)
    (leaf : ∀ a, pair a = true → single i a = false → single j a = false → escape)
    (on : f.evalWith pair = true) (offi : f.evalWith (single i) = false)
    (offj : f.evalWith (single j) = false) :
    escape ∨ separated (cuts f base single) i j := by
  induction f with
  | var a => exact Or.inl (leaf a on offi offj)
  | disj l r hl hr =>
    simp only [Formula.evalWith, Bool.or_eq_true, Bool.or_eq_false_iff] at on offi offj
    rcases on with on | on
    · exact (hl on offi.1 offj.1).imp_right fun h =>
        (separated_append ..).2 (Or.inl h)
    · exact (hr on offi.2 offj.2).imp_right fun h =>
        (separated_append ..).2 (Or.inr h)
  | conj l r hl hr =>
    simp only [Formula.evalWith, Bool.and_eq_true] at on
    have push (c : Cut I) :
        separated (cuts l base single ++ cuts r base single) i j →
        separated (c :: (cuts l base single ++ cuts r base single)) i j := by
      rintro ⟨row, hm, h⟩
      exact ⟨row, List.mem_cons_of_mem _ hm, h⟩
    by_cases bothLeft : l.evalWith (single i) = false ∧ l.evalWith (single j) = false
    · exact (hl on.1 bothLeft.1 bothLeft.2).imp_right fun h =>
        push _ ((separated_append ..).2 (Or.inl h))
    by_cases bothRight : r.evalWith (single i) = false ∧ r.evalWith (single j) = false
    · exact (hr on.2 bothRight.1 bothRight.2).imp_right fun h =>
        push _ ((separated_append ..).2 (Or.inr h))
    have childL_i := evalMono l li
    have childL_j := evalMono l lj
    have childR_i := evalMono r li
    have childR_j := evalMono r lj
    let row : Cut I := fun a => cutAt (l.evalWith base) (r.evalWith base)
      (l.evalWith (single a)) (r.evalWith (single a))
    refine Or.inr ⟨row, List.mem_cons_self, ?_⟩
    cases hli : l.evalWith (single i) <;> cases hlj : l.evalWith (single j) <;>
      cases hri : r.evalWith (single i) <;> cases hrj : r.evalWith (single j) <;>
      simp_all [Formula.evalWith, row, splits, cutAt, opposing, Bool.le_iff_imp]

def rowCode {I : Type} (rows : List (Cut I)) (i : I) (k : Fin rows.length) : Option Bool :=
  rows.get k i

theorem fixedRowCode {I : Type} (rows : List (Cut I)) (i : I) :
    (CrownThreshold.fixedCoordinates (rowCode rows i)).card = degree rows i := by
  calc
    _ = (List.ofFn rows.get).countP (fun row => (row i).isSome) := by
      rw [List.countP_ofFn]
      apply congrArg Finset.card
      ext k
      constructor <;> intro h <;>
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2⟩
    _ = _ := by rw [List.ofFn_get]; rfl

theorem rowCodeSeparates {I : Type} {rows : List (Cut I)} {i j : I}
    (h : separated rows i j) :
    ∃ k, (rowCode rows i k = some false ∧ rowCode rows j k = some true) ∨
      (rowCode rows i k = some true ∧ rowCode rows j k = some false) := by
  obtain ⟨row, hm, hp⟩ := h
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hm
  refine ⟨k, ?_⟩
  change splits (rows.get k) i j
  rw [hk]
  exact hp

theorem boundedByCuts {I : Type} (S : Finset I) (rows : List (Cut I)) (b : ℕ)
    (sep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → separated rows i j)
    (count : ∀ i ∈ S, degree rows i ≤ b) : S.card ≤ 2 ^ b := by
  have h := CrownThreshold.weightedPacking S (rowCode rows) (fun _ => b) b
    (fun i hi j hj ne => rowCodeSeparates (sep i hi j hj ne))
    (fun i hi => by simpa [fixedRowCode] using count i hi) (fun _ _ => le_rfl)
  simpa using h

def withHead {A B : Type} (head : B) (rest : A → B) (key : Option A) : B :=
  key.elim head rest

@[simp] theorem withHead_none {A B : Type} (head : B) (rest : A → B) :
    withHead head rest none = head := rfl

@[simp] theorem withHead_some {A B : Type} (head : B) (rest : A → B) (a : A) :
    withHead head rest (some a) = rest a := rfl

@[simp] theorem withHead_const {A B : Type} (b : B) :
    withHead b (fun _ : A => b) = fun _ => b := by
  funext a
  cases a <;> rfl

theorem withHeadMono {A : Type} {u v : A → Bool} {a b : Bool}
    (h : a ≤ b) (e : ∀ x, u x ≤ v x) :
    ∀ x, withHead a u x ≤ withHead b v x := by
  intro x
  cases x with
  | none => exact h
  | some x => exact e x

def singletonInput {I : Type} [DecidableEq I] (i k : I) : Bool := decide (k = i)

def pairInput {I : Type} [DecidableEq I] (i j k : I) : Bool :=
  singletonInput i k || singletonInput j k

def ThresholdOn {I : Type} [DecidableEq I] (f : (I → Bool) → Bool) : Prop :=
  (∀ i, f (singletonInput i) = false) ∧ ∀ i j, i ≠ j → f (pairInput i j) = true

structure Samples (I A : Type) where
  base : A → Bool
  one : I → A → Bool
  two : I → I → A → Bool

namespace Samples

variable {I A : Type}

def raw (I : Type) [DecidableEq I] : Samples I I :=
  ⟨fun _ => false, singletonInput, pairInput⟩

def onBase (s : Samples I A) : Prop :=
  ∀ i a, s.base a ≤ s.one i a

def freeze (s : Samples I A) (bit : Bool) : Samples I (Option A) :=
  ⟨withHead bit s.base, fun i => withHead bit (s.one i),
    fun i j => withHead bit (s.two i j)⟩

def add (s : Samples I A) (f : Formula A) : Samples I (Option A) :=
  ⟨withHead (f.evalWith s.base) s.base,
    fun i => withHead (f.evalWith (s.one i)) (s.one i),
    fun i j => withHead (f.evalWith (s.two i j)) (s.two i j)⟩

def riseAt (s : Samples I A) (i : I) (a : A) : ℕ :=
  rise (s.base a) (s.one i a)

def rows (s : Samples I A) (f : Formula A) : List (Cut I) :=
  cuts f s.base s.one

def leafWitness (s : Samples I A) (prior : List (Cut I)) (i j : I) : Prop :=
  ∀ a, s.two i j a = true → s.one i a = false → s.one j a = false → separated prior i j

theorem raw_onBase [DecidableEq I] : (raw I).onBase := fun _ _ => Bool.false_le _

theorem freeze_onBase (s : Samples I A) (mono : s.onBase) (bit : Bool) :
    (s.freeze bit).onBase :=
  fun i => withHeadMono le_rfl (mono i)

theorem add_onBase (s : Samples I A) (mono : s.onBase) (f : Formula A) :
    (s.add f).onBase :=
  fun i => withHeadMono (evalMono f (mono i)) (mono i)

theorem raw_leafWitness [DecidableEq I] (i j : I) : (raw I).leafWitness [] i j := by
  intro a h hi hj
  change singletonInput i a = false at hi
  change singletonInput j a = false at hj
  simp [raw, pairInput, hi, hj] at h

theorem freeze_leafWitness {s : Samples I A} {prior : List (Cut I)} {i j : I}
    (known : s.leafWitness prior i j) (bit : Bool) : (s.freeze bit).leafWitness prior i j := by
  intro a h hi hj
  cases a with
  | none => exact Bool.noConfusion (h.symm.trans hi)
  | some a => exact known a h hi hj

theorem add_leafWitness {s : Samples I A} {prior : List (Cut I)} {i j : I}
    (mono : s.onBase) (known : s.leafWitness prior i j) (f : Formula A) :
    (s.add f).leafWitness (prior ++ s.rows f) i j := by
  intro a h hi hj
  cases a with
  | none =>
    apply (separated_append ..).2
    exact cutSeparate f s.base s.one (s.two i j) i j (separated prior i j)
      (mono i) (mono j) known h hi hj
  | some a =>
    exact (separated_append ..).2 (Or.inl (known a h hi hj))

theorem outputSeparates {s : Samples I A} {prior : List (Cut I)} {i j : I}
    (mono : s.onBase) (known : s.leafWitness prior i j) (f : Formula A)
    (on : f.evalWith (s.two i j) = true)
    (no_i : f.evalWith (s.one i) = false) (no_j : f.evalWith (s.one j) = false) :
    separated (prior ++ s.rows f) i j :=
  (separated_append ..).2 (cutSeparate f s.base s.one (s.two i j) i j (separated prior i j)
    (mono i) (mono j) known on no_i no_j)

theorem charge (s : Samples I A) (mono : s.onBase) (f : Formula A) (i : I) :
    degree (s.rows f) i + rise (f.evalWith s.base) (f.evalWith (s.one i)) ≤
      leafWeight f (s.riseAt i) :=
  cutCharge f s.base s.one i (mono i)

theorem freeze_riseAt (s : Samples I A) (bit : Bool) (i : I) :
    (s.freeze bit).riseAt i = withHead 0 (s.riseAt i) := by
  funext a
  cases a with
  | none => cases bit <;> rfl
  | some a => rfl

def headUses (f : Formula (Option A)) : ℕ :=
  leafWeight f (withHead 1 fun _ => 0)

theorem head_weight (f : Formula (Option A)) (k : ℕ) (w : A → ℕ) :
    leafWeight f (withHead k w) =
      leafWeight f (withHead 0 w) + k * headUses f := by
  have formula : withHead k w = fun a =>
      withHead 0 w a + k * withHead 1 (fun _ => 0) a := by
    funext a
    cases a <;> simp
  rw [formula, leafWeight_add, leafWeight_mul, headUses]

theorem add_riseAt (s : Samples I A) (f : Formula A) (i : I) :
    (s.add f).riseAt i =
      withHead (rise (f.evalWith s.base) (f.evalWith (s.one i))) (s.riseAt i) := by
  funext a
  cases a <;> rfl

theorem add_weight (s : Samples I A) (f : Formula A) (g : Formula (Option A)) (i : I) :
    leafWeight g ((s.add f).riseAt i) =
      leafWeight g (withHead 0 (s.riseAt i)) +
        rise (f.evalWith s.base) (f.evalWith (s.one i)) * headUses g := by
  rw [add_riseAt, head_weight]

theorem formulaCapacity (S : Finset I) (s : Samples I A) (f : Formula A)
    (mono : s.onBase) (initial : ∀ i j, s.leafWitness [] i j)
    (off : ∀ i ∈ S, f.evalWith (s.one i) = false)
    (on : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → f.evalWith (s.two i j) = true)
    (limit : ∀ i ∈ S, leafWeight f (s.riseAt i) ≤ 1) : S.card ≤ 2 := by
  apply boundedByCuts S (s.rows f) 1
  · intro i hi j hj ne
    simpa using outputSeparates mono (initial i j) f (on i hi j hj ne) (off i hi) (off j hj)
  · intro i hi
    have c := charge s mono f i
    have l := limit i hi
    omega

theorem composedCapacity (S : Finset I) (s : Samples I A) (f : Formula A) (g : Formula (Option A))
    (mono : s.onBase) (initial : ∀ i j, s.leafWitness [] i j)
    (off : ∀ i ∈ S, g.evalWith ((s.add f).one i) = false)
    (on : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → g.evalWith ((s.add f).two i j) = true)
    (limit : ∀ i ∈ S, leafWeight f (s.riseAt i) + leafWeight g ((s.add f).riseAt i) ≤ 1) :
    S.card ≤ 2 := by
  apply boundedByCuts S (s.rows f ++ (s.add f).rows g) 1
  · intro i hi j hj ne
    have found := add_leafWitness mono (initial i j) f
    simpa using outputSeparates (add_onBase s mono f) found g
      (on i hi j hj ne) (off i hi) (off j hj)
  · intro i hi
    rw [degree_append]
    have a := charge s mono f i
    have b := charge (s.add f) (add_onBase s mono f) g i
    have l := limit i hi
    omega

end Samples

def rename {A B : Type} (f : Formula A) (map : A → B) : Formula B :=
  match f with
  | .var a => .var (map a)
  | .conj l r => .conj (rename l map) (rename r map)
  | .disj l r => .disj (rename l map) (rename r map)

theorem eval_rename {A B : Type} (f : Formula A) (map : A → B) (x : B → Bool) :
    (rename f map).evalWith x = f.evalWith (x ∘ map) := by
  induction f <;> simp_all [rename, Formula.evalWith]

theorem weight_rename {A B : Type} (f : Formula A) (map : A → B) (w : B → ℕ) :
    leafWeight (rename f map) w = leafWeight f (w ∘ map) := by
  induction f <;> simp_all [rename, leafWeight]

def swapSignals {I : Type} : Option (Option I) → Option (Option I)
  | none => some none
  | some none => none
  | some (some a) => some (some a)

theorem swap_assignment {I B : Type} (p q : B) (x : I → B) :
    (withHead p (withHead q x)) ∘ swapSignals = withHead q (withHead p x) := by
  funext a
  rcases a with _ | _ | a <;> rfl

theorem head_twice_weight {A : Type} (f : Formula (Option (Option A))) (p q : ℕ)
    (w : A → ℕ) :
    leafWeight f (withHead q (withHead p w)) =
      leafWeight f (withHead 0 (withHead 0 w)) +
        p * leafWeight f (withHead 0 (withHead 1 (fun _ => 0))) +
        q * Samples.headUses f := by
  rw [Samples.head_weight]
  have same : withHead 0 (withHead p w) = fun a =>
      withHead 0 (withHead 0 w) a + p * withHead 0 (withHead 1 (fun _ => 0)) a := by
    funext a
    rcases a with _ | _ | a <;> simp
  rw [same, leafWeight_add, leafWeight_mul]

structure TwoShared (I : Type) where
  first : Formula I
  second : Formula (Option I)
  output : Formula (Option (Option I))

namespace TwoShared

variable {I : Type} [DecidableEq I]

def p (N : TwoShared I) (x : I → Bool) : Bool := N.first.evalWith x

def q (N : TwoShared I) (x : I → Bool) : Bool :=
  N.second.evalWith (withHead (N.p x) x)

def value (N : TwoShared I) (x : I → Bool) : Bool :=
  N.output.evalWith (withHead (N.q x) (withHead (N.p x) x))

def pOn (N : TwoShared I) (i : I) : Bool := N.p (singletonInput i)
def qOn (N : TwoShared I) (i : I) : Bool := N.q (singletonInput i)

def firstRaw (N : TwoShared I) (i : I) : ℕ :=
  leafWeight N.first (fun k => (singletonInput i k).toNat)

def secondRaw (N : TwoShared I) (i : I) : ℕ :=
  leafWeight N.second (withHead 0 fun k => (singletonInput i k).toNat)

def outputRaw (N : TwoShared I) (i : I) : ℕ :=
  leafWeight N.output (withHead 0 (withHead 0 fun k => (singletonInput i k).toNat))

def pUses (N : TwoShared I) : ℕ :=
  Samples.headUses N.second + leafWeight N.output (withHead 0 (withHead 1 fun _ => 0))

def qUses (N : TwoShared I) : ℕ := Samples.headUses N.output

def ThresholdTests (N : TwoShared I) : Prop := ThresholdOn N.value

omit [DecidableEq I] in
theorem pMono (N : TwoShared I) {x y : I → Bool} (le : ∀ i, x i ≤ y i) : N.p x ≤ N.p y :=
  evalMono N.first le

omit [DecidableEq I] in
theorem qMono (N : TwoShared I) {x y : I → Bool} (le : ∀ i, x i ≤ y i) : N.q x ≤ N.q y :=
  evalMono N.second (withHeadMono (pMono N le) le)

theorem singleton_pair (i j : I) : ∀ k, singletonInput i k ≤ pairInput i j k :=
  fun _ => Bool.left_le_or _ _

theorem otherSingleton_pair (i j : I) : ∀ k, singletonInput j k ≤ pairInput i j k :=
  fun _ => Bool.right_le_or _ _

theorem pOnPair (N : TwoShared I) {i j : I} (h : N.pOn i = true) :
    N.p (pairInput i j) = true :=
  (Bool.le_iff_imp.mp (N.pMono (singleton_pair i j))) h

theorem qOnPair (N : TwoShared I) {i j : I} (h : N.qOn i = true) :
    N.q (pairInput i j) = true :=
  (Bool.le_iff_imp.mp (N.qMono (singleton_pair i j))) h

theorem raw_rises (i : I) :
    (Samples.raw I).riseAt i = fun k => (singletonInput i k).toNat := by
  funext k
  simp [Samples.riseAt, Samples.raw, rise]

theorem firstNeeded (N : TwoShared I) {i : I} (on : N.pOn i = true) :
    1 ≤ N.firstRaw i := by
  by_contra! h
  have eq := eqOfNoRise N.first ((Samples.raw_onBase (I := I)) i)
    (show leafWeight N.first ((Samples.raw I).riseAt i) = 0 from by
      rw [raw_rises]
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h))
  change N.first.evalWith (fun _ => false) = N.pOn i at eq
  simp [evalZero, on] at eq

theorem secondNeeded (N : TwoShared I) {i : I}
    (poff : N.pOn i = false) (qon : N.qOn i = true) : 1 ≤ N.secondRaw i := by
  let s := (Samples.raw I).freeze false
  by_contra! h
  have eq := eqOfNoRise N.second ((Samples.freeze_onBase _ Samples.raw_onBase false) i)
    (show leafWeight N.second (s.riseAt i) = 0 from by
      change leafWeight N.second (((Samples.raw I).freeze false).riseAt i) = 0
      rw [Samples.freeze_riseAt, raw_rises]
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h))
  have atOne : N.second.evalWith (s.one i) = true := by
    have pFalse : N.p (singletonInput i) = false := poff
    change N.second.evalWith (withHead false (singletonInput i)) = true
    simpa only [qOn, q, pFalse] using qon
  have atZero : N.second.evalWith s.base = false := by
    simp [s, Samples.freeze, Samples.raw, evalZero]
  exact Bool.noConfusion (atZero.symm.trans (eq.trans atOne))

variable [Fintype I]

def group (N : TwoShared I) (p q : Bool) : Finset I :=
  univ.filter fun i => N.pOn i = p ∧ N.qOn i = q

theorem group_bits (N : TwoShared I) {p q : Bool} {i : I} :
    i ∈ N.group p q ↔ N.pOn i = p ∧ N.qOn i = q := by
  simp [group]

theorem leftCapacity (N : TwoShared I) (test : N.ThresholdTests)
    (raw : ∀ i, N.firstRaw i + N.secondRaw i + N.outputRaw i ≤ 2) :
    (N.group true false).card ≤ 2 := by
  let data := (Samples.raw I).freeze true
  refine Samples.composedCapacity (N.group true false) data N.second N.output
    (Samples.freeze_onBase _ Samples.raw_onBase _) (fun i j =>
      Samples.freeze_leafWitness (Samples.raw_leafWitness i j) _) ?_ ?_ ?_
  · intro i hi
    have pe : N.p (singletonInput i) = true := (N.group_bits.mp hi).1
    change N.output.evalWith (withHead (N.second.evalWith (withHead true (singletonInput i)))
      (withHead true (singletonInput i))) = false
    simpa only [value, q, pe] using test.1 i
  · intro i hi j _ ne
    have pe := N.pOnPair (j := j) (N.group_bits.mp hi).1
    change N.output.evalWith (withHead (N.second.evalWith (withHead true (pairInput i j)))
      (withHead true (pairInput i j))) = true
    simpa only [value, q, pe] using test.2 i j ne
  · intro i hi
    have bits := N.group_bits.mp hi
    have pe : N.p (singletonInput i) = true := bits.1
    have qoff : N.second.evalWith (data.one i) = false := by
      change N.second.evalWith (withHead true (singletonInput i)) = false
      simpa only [qOn, q, pe] using bits.2
    rw [Samples.add_weight]
    have inactive : rise (N.second.evalWith data.base) (N.second.evalWith (data.one i)) = 0 := by
      simp [qoff, rise]
    rw [inactive, Nat.zero_mul, Nat.add_zero]
    change leafWeight N.second (((Samples.raw I).freeze true).riseAt i) +
      leafWeight N.output (withHead 0 (((Samples.raw I).freeze true).riseAt i)) ≤ 1
    rw [Samples.freeze_riseAt, raw_rises]
    change N.secondRaw i + N.outputRaw i ≤ 1
    have need := N.firstNeeded bits.1
    have count := raw i
    omega

theorem rightCapacity (N : TwoShared I) (test : N.ThresholdTests)
    (raw : ∀ i, N.firstRaw i + N.secondRaw i + N.outputRaw i ≤ 2) :
    (N.group false true).card ≤ 2 := by
  let data := (Samples.raw I).freeze true
  let first := rename N.first some
  let out := rename N.output swapSignals
  have firstEval (x : I → Bool) : first.evalWith (withHead true x) = N.p x :=
    (eval_rename N.first some (withHead true x)).trans rfl
  have same (x : I → Bool) (h : N.q x = true) :
      out.evalWith (withHead (first.evalWith (withHead true x)) (withHead true x)) =
        N.value x := by
    rw [firstEval]
    change (rename N.output swapSignals).evalWith (withHead (N.p x) (withHead true x)) = _
    rw [eval_rename, swap_assignment, value, h]
  refine Samples.composedCapacity (N.group false true) data first out
    (Samples.freeze_onBase _ Samples.raw_onBase _) (fun i j =>
      Samples.freeze_leafWitness (Samples.raw_leafWitness i j) _) ?_ ?_ ?_
  · intro i hi
    change out.evalWith
      (withHead (first.evalWith (withHead true (singletonInput i))) (withHead true (singletonInput i))) =
        false
    rw [same _ (N.group_bits.mp hi).2]
    exact test.1 i
  · intro i hi j _ ne
    change out.evalWith
      (withHead (first.evalWith (withHead true (pairInput i j))) (withHead true (pairInput i j))) =
        true
    rw [same _ (N.qOnPair (N.group_bits.mp hi).2)]
    exact test.2 i j ne
  · intro i hi
    have bits := N.group_bits.mp hi
    have poff : first.evalWith (data.one i) = false := by
      change first.evalWith (withHead true (singletonInput i)) = false
      exact (firstEval _).trans bits.1
    rw [Samples.add_weight]
    have inactive : rise (first.evalWith data.base) (first.evalWith (data.one i)) = 0 := by
      simp [poff, rise]
    rw [inactive, Nat.zero_mul, Nat.add_zero]
    change leafWeight (rename N.first some) (((Samples.raw I).freeze true).riseAt i) +
      leafWeight (rename N.output swapSignals) (withHead 0 (((Samples.raw I).freeze true).riseAt i)) ≤ 1
    rw [Samples.freeze_riseAt, raw_rises, weight_rename, weight_rename, swap_assignment]
    change N.firstRaw i + N.outputRaw i ≤ 1
    have need := N.secondNeeded bits.1 bits.2
    have count := raw i
    omega

theorem bothCapacity (N : TwoShared I) (test : N.ThresholdTests)
    (raw : ∀ i, N.firstRaw i + N.secondRaw i + N.outputRaw i ≤ 2) :
    (N.group true true).card ≤ 2 := by
  let data := ((Samples.raw I).freeze true).freeze true
  refine Samples.formulaCapacity (N.group true true) data N.output
    (Samples.freeze_onBase _ (Samples.freeze_onBase _ Samples.raw_onBase _) _) (fun i j =>
      Samples.freeze_leafWitness (Samples.freeze_leafWitness (Samples.raw_leafWitness i j) _) _)
    ?_ ?_ ?_
  · intro i hi
    have bits := N.group_bits.mp hi
    have pe : N.p (singletonInput i) = true := bits.1
    have qe : N.q (singletonInput i) = true := bits.2
    change N.output.evalWith (withHead true (withHead true (singletonInput i))) = false
    simpa only [value, pe, qe] using test.1 i
  · intro i hi j _ ne
    have bits := N.group_bits.mp hi
    have pe := N.pOnPair (j := j) bits.1
    have qe := N.qOnPair (j := j) bits.2
    change N.output.evalWith (withHead true (withHead true (pairInput i j))) = true
    simpa only [value, pe, qe] using test.2 i j ne
  · intro i hi
    change leafWeight N.output ((((Samples.raw I).freeze true).freeze true).riseAt i) ≤ 1
    rw [Samples.freeze_riseAt, Samples.freeze_riseAt, raw_rises]
    change N.outputRaw i ≤ 1
    have need := N.firstNeeded (N.group_bits.mp hi).1
    have count := raw i
    omega

omit [Fintype I] in
theorem addedInputRise (i j : I) (ne : i ≠ j) :
    (fun k => rise (singletonInput j k) (pairInput i j k)) =
      fun k => (singletonInput i k).toNat := by
  funext k
  by_cases h : k = i
  · subst k
    simp [singletonInput, pairInput, rise, ne]
  · by_cases h' : k = j <;> simp [singletonInput, pairInput, rise, h, h', ne.symm]

theorem outputNeeded (N : TwoShared I) (test : N.ThresholdTests) {i j : I}
    (hi : i ∈ N.group true true) (hj : j ∈ N.group true true) (ne : i ≠ j) :
    1 ≤ N.outputRaw i := by
  let x := withHead true (withHead true (singletonInput j))
  let y := withHead true (withHead true (pairInput i j))
  have le : ∀ a, x a ≤ y a :=
    withHeadMono le_rfl (withHeadMono le_rfl (otherSingleton_pair i j))
  have no : N.output.evalWith x = false := by
    have pj : N.p (singletonInput j) = true := (N.group_bits.mp hj).1
    have qj : N.q (singletonInput j) = true := (N.group_bits.mp hj).2
    change N.output.evalWith (withHead true (withHead true (singletonInput j))) = false
    simpa only [value, pj, qj] using test.1 j
  have yes : N.output.evalWith y = true := by
    have pe := N.pOnPair (j := j) (N.group_bits.mp hi).1
    have qe := N.qOnPair (j := j) (N.group_bits.mp hi).2
    change N.output.evalWith (withHead true (withHead true (pairInput i j))) = true
    simpa only [value, pe, qe] using test.2 i j ne
  have mass : (fun a => rise (x a) (y a)) =
      withHead 0 (withHead 0 fun k => (singletonInput i k).toNat) := by
    funext a
    rcases a with _ | _ | a
    · rfl
    · rfl
    · exact congrFun (addedInputRise i j ne) a
  by_contra! small
  have noMass : leafWeight N.output (fun a => rise (x a) (y a)) = 0 := by
    rw [mass]
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ small)
  rw [eqOfNoRise N.output le noMass, yes] at no
  contradiction

theorem linked (N : TwoShared I) (test : N.ThresholdTests)
    (raw : ∀ i, N.firstRaw i + N.secondRaw i + N.outputRaw i ≤ 2)
    (both : (N.group true true).card = 2) : (N.group true false).card = 0 := by
  obtain ⟨i, hi, j, hj, ne⟩ := Finset.one_lt_card.mp (show 1 < (N.group true true).card by omega)
  have first := N.firstNeeded (N.group_bits.mp hi).1
  have last := N.outputNeeded test hi hj ne
  have budget := raw i
  have absent : N.secondRaw i = 0 := by omega
  let data := (Samples.raw I).freeze true
  have mass : leafWeight N.second (data.riseAt i) = 0 := by
    change leafWeight N.second (((Samples.raw I).freeze true).riseAt i) = 0
    rw [Samples.freeze_riseAt, raw_rises]
    exact absent
  have atOne : N.second.evalWith (data.one i) = true := by
    have pe : N.p (singletonInput i) = true := (N.group_bits.mp hi).1
    change N.second.evalWith (withHead true (singletonInput i)) = true
    simpa only [qOn, q, pe] using (N.group_bits.mp hi).2
  have forced : N.second.evalWith (withHead true (fun _ => false)) = true :=
    (eqOfNoRise N.second ((Samples.freeze_onBase _ Samples.raw_onBase true) i) mass).trans atOne
  apply Finset.card_eq_zero.mpr
  ext k
  simp only [Finset.notMem_empty, iff_false]
  intro hk
  have bits := N.group_bits.mp hk
  have hp : N.p (singletonInput k) = true := bits.1
  have m : N.second.evalWith (withHead true (fun _ => false)) ≤ N.qOn k :=
    evalMono N.second (withHeadMono (show true ≤ N.p (singletonInput k) by rw [hp])
      (fun a => Bool.false_le (singletonInput k a)))
  have hq : N.qOn k = true := (Bool.le_iff_imp.mp m) forced
  exact Bool.noConfusion (hq.symm.trans bits.2)

theorem capacity (N : TwoShared I) (test : N.ThresholdTests)
    (raw : ∀ i, N.firstRaw i + N.secondRaw i + N.outputRaw i ≤ 2)
    (firstUses : N.pUses ≤ 2) (secondUses : N.qUses ≤ 2) : Fintype.card I ≤ 6 := by
  let a := Samples.raw I
  let b := a.add N.first
  let c := b.add N.second
  let rows := (a.rows N.first ++ b.rows N.second) ++ c.rows N.output
  have monoA : a.onBase := Samples.raw_onBase
  have monoB : b.onBase := Samples.add_onBase a monoA N.first
  have monoC : c.onBase := Samples.add_onBase b monoB N.second
  have sep : ∀ i j : I, i ≠ j → separated rows i j := by
    intro i j ne
    have w1 := Samples.add_leafWitness monoA (Samples.raw_leafWitness i j) N.first
    have w2 := Samples.add_leafWitness monoB w1 N.second
    simpa only [rows, List.nil_append] using
      Samples.outputSeparates monoC w2 N.output (test.2 i j ne) (test.1 i) (test.1 j)
  have baseB : b.base = fun _ => false := by
    simp [b, a, Samples.add, Samples.raw, evalZero]
  have pRise (i : I) :
      rise (N.first.evalWith a.base) (N.first.evalWith (a.one i)) = (N.pOn i).toNat := by
    simp [a, Samples.raw, evalZero, rise, pOn, p]
  have qRise (i : I) :
      rise (N.second.evalWith b.base) (N.second.evalWith (b.one i)) = (N.qOn i).toNat := by
    rw [baseB, evalZero]
    simp [b, a, Samples.add, Samples.raw, rise, qOn, q, p]
  have firstRises (i : I) : b.riseAt i =
      withHead (N.pOn i).toNat (fun k => (singletonInput i k).toNat) := by
    change (a.add N.first).riseAt i = _
    rw [Samples.add_riseAt, pRise]
    exact congrArg (withHead (N.pOn i).toNat) (raw_rises i)
  have secondRises (i : I) : c.riseAt i =
      withHead (N.qOn i).toNat (withHead (N.pOn i).toNat (fun k => (singletonInput i k).toNat)) := by
    change (b.add N.second).riseAt i = _
    rw [Samples.add_riseAt, qRise, firstRises]
  have count (i : I) : degree rows i ≤ 2 + (N.pOn i).toNat + (N.qOn i).toNat := by
    have h1 := Samples.charge a monoA N.first i
    have h2 := Samples.charge b monoB N.second i
    have h3 := Samples.charge c monoC N.output i
    rw [pRise] at h1
    change _ ≤ N.firstRaw i at h1
    rw [qRise, firstRises, Samples.head_weight] at h2
    change _ ≤ N.secondRaw i + (N.pOn i).toNat * Samples.headUses N.second at h2
    rw [secondRises, head_twice_weight] at h3
    change _ ≤ N.outputRaw i + (N.pOn i).toNat *
      leafWeight N.output (withHead 0 (withHead 1 fun _ => 0)) +
        (N.qOn i).toNat * Samples.headUses N.output at h3
    have lp := Nat.mul_le_mul_left (N.pOn i).toNat firstUses
    rw [pUses, Nat.mul_add] at lp
    have lq : (N.qOn i).toNat * Samples.headUses N.output ≤ (N.qOn i).toNat * 2 :=
      Nat.mul_le_mul_left _ secondUses
    have budget := raw i
    simp only [rows, degree_append]
    omega
  simpa using CrownThreshold.twoForkCodeCapacity (univ : Finset I) N.pOn N.qOn (rowCode rows)
    (fun i _ j _ ne => rowCodeSeparates (sep i j ne))
    (fun i _ => by simpa only [fixedRowCode] using count i)
    (N.leftCapacity test raw) (N.rightCapacity test raw) (N.bothCapacity test raw)
    (N.linked test raw)

end TwoShared

section FewerShared

variable {I : Type} [DecidableEq I] [Fintype I]

theorem formulaThresholdCapacity (f : Formula I) (test : ThresholdOn f.evalWith)
    (raw : ∀ i, leafWeight f (fun k => (singletonInput i k).toNat) ≤ 2) :
    Fintype.card I ≤ 4 := by
  let a := Samples.raw I
  have cap := boundedByCuts (univ : Finset I) (a.rows f) 2
    (fun i _ j _ ne => by
      simpa only [List.nil_append] using
        Samples.outputSeparates Samples.raw_onBase (Samples.raw_leafWitness i j) f
          (test.2 i j ne) (test.1 i) (test.1 j))
    (fun i _ => by
      change degree ((Samples.raw I).rows f) i ≤ 2
      have charge := Samples.charge (Samples.raw I) Samples.raw_onBase f i
      rw [TwoShared.raw_rises] at charge
      have r := raw i
      omega)
  simpa using cap

theorem oneSharedThresholdCapacity (first : Formula I) (output : Formula (Option I))
    (test : ThresholdOn (fun x => output.evalWith (withHead (first.evalWith x) x)))
    (raw : ∀ i, leafWeight first (fun k => (singletonInput i k).toNat) +
      leafWeight output (withHead 0 fun k => (singletonInput i k).toNat) ≤ 2)
    (reuse : Samples.headUses output ≤ 3) : Fintype.card I ≤ 5 := by
  let a := Samples.raw I
  let b := a.add first
  let hot (i : I) := first.evalWith (singletonInput i)
  let H := (univ : Finset I).filter fun i => hot i = true
  let C := (univ : Finset I).filter fun i => hot i = false
  let rows := a.rows first ++ b.rows output
  let s := a.freeze true
  have h : H.card ≤ 2 := by
    refine Samples.formulaCapacity H s output
      (Samples.freeze_onBase _ Samples.raw_onBase _)
      (fun i j => Samples.freeze_leafWitness (Samples.raw_leafWitness i j) _) ?_ ?_ ?_
    · intro i hi
      have atOne := (Finset.mem_filter.mp hi).2
      change first.evalWith (singletonInput i) = true at atOne
      change output.evalWith (withHead true (singletonInput i)) = false
      simpa only [atOne] using test.1 i
    · intro i hi j _ ne
      have atOne := (Finset.mem_filter.mp hi).2
      have atPair := (Bool.le_iff_imp.mp (evalMono first (TwoShared.singleton_pair i j))) atOne
      change output.evalWith (withHead true (pairInput i j)) = true
      simpa only [atPair] using test.2 i j ne
    · intro i hi
      change leafWeight output (((Samples.raw I).freeze true).riseAt i) ≤ 1
      rw [Samples.freeze_riseAt, TwoShared.raw_rises]
      have atOne : first.evalWith (singletonInput i) = true := (Finset.mem_filter.mp hi).2
      have needed : 1 ≤ leafWeight first (fun k => (singletonInput i k).toNat) := by
        by_contra! small
        have mass : leafWeight first ((Samples.raw I).riseAt i) = 0 := by
          rw [TwoShared.raw_rises]
          exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ small)
        have e := eqOfNoRise first (Samples.raw_onBase i) mass
        change first.evalWith (fun _ => false) = first.evalWith (singletonInput i) at e
        simp [evalZero, atOne] at e
      have r := raw i
      omega
  have sep : ∀ i j, i ≠ j → separated rows i j := by
    intro i j ne
    have w := Samples.add_leafWitness Samples.raw_onBase (Samples.raw_leafWitness i j) first
    simpa only [rows, List.nil_append] using
      Samples.outputSeparates (Samples.add_onBase a Samples.raw_onBase first) w output
        (test.2 i j ne) (test.1 i) (test.1 j)
  have d (i : I) : degree rows i ≤ 2 + 2 * (hot i).toNat := by
    have c1 := Samples.charge (Samples.raw I) Samples.raw_onBase first i
    have c2 := Samples.charge b (Samples.add_onBase a Samples.raw_onBase first) output i
    have r1 : rise (first.evalWith a.base) (first.evalWith (a.one i)) = (hot i).toNat := by
      simp [a, Samples.raw, hot, rise, evalZero]
    change degree (a.rows first) i + rise (first.evalWith a.base) (first.evalWith (a.one i)) ≤
      leafWeight first ((Samples.raw I).riseAt i) at c1
    rw [r1, TwoShared.raw_rises] at c1
    change degree (b.rows output) i + _ ≤ leafWeight output ((a.add first).riseAt i) at c2
    rw [Samples.add_weight, r1] at c2
    change _ ≤ leafWeight output (withHead 0 ((Samples.raw I).riseAt i)) +
      (hot i).toNat * Samples.headUses output at c2
    rw [TwoShared.raw_rises] at c2
    have u := Nat.mul_le_mul_left (hot i).toNat reuse
    have r := raw i
    simp only [rows, degree_append]
    omega
  have packing := CrownThreshold.weightedPacking (univ : Finset I) (rowCode rows)
    (fun i => 2 + 2 * (hot i).toNat) 4
    (fun i _ j _ ne => rowCodeSeparates (sep i j ne))
    (fun i _ => by simpa only [fixedRowCode] using d i)
    (fun i _ => by cases hot i <;> decide)
  have weight (i : I) :
      2 ^ (4 - (2 + 2 * (hot i).toNat)) =
        (if hot i = false then 4 else 0) + (if hot i = true then 1 else 0) := by
    cases hot i <;> decide
  simp only [weight] at packing
  have cap : 4 * C.card + H.card ≤ 16 := by
    simpa [Finset.sum_add_distrib, Finset.sum_ite, H, C, Nat.mul_comm] using packing
  have notHot : (univ.filter fun i => ¬ hot i = true) = C := by
    ext i
    cases e : hot i <;> simp [C, e]
  have parts : H.card + C.card = Fintype.card I := by
    have part := Finset.card_filter_add_card_filter_not (s := (univ : Finset I))
      (fun i => hot i = true)
    rw [notHot] at part
    simpa [H] using part
  by_cases z : H.card = 0 <;> omega

end FewerShared

end CrownForks
