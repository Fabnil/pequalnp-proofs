import CrownForks

namespace CrownPairFormula

open CrownForks PnpResearch

variable {A : Type} [DecidableEq A]

def setTwo (u : A → Bool) (i j : A) (a b : Bool) (k : A) : Bool :=
  if k = i then a else if k = j then b else u k

def reads (f : Formula A) (i : A) : ℕ :=
  leafWeight f (fun k => (singletonInput i k).toNat)

private abbrev Square := Bool × Bool × Bool × Bool

private def square (f : Formula A) (u : A → Bool) (i j : A) : Square :=
  (f.evalWith (setTwo u i j false false), f.evalWith (setTwo u i j true false),
    f.evalWith (setTwo u i j false true), f.evalWith (setTwo u i j true true))

private def ignoresFirst (s : Square) : Prop := s.1 = s.2.1 ∧ s.2.2.1 = s.2.2.2
private def ignoresSecond (s : Square) : Prop := s.1 = s.2.2.1 ∧ s.2.1 = s.2.2.2
private def meet (s : Square) : Prop := s.1 = (s.2.1 && s.2.2.1)
private def join (s : Square) : Prop := s.2.2.2 = (s.2.1 || s.2.2.1)
private def increasing (s : Square) : Prop :=
  s.1 ≤ s.2.1 ∧ s.1 ≤ s.2.2.1 ∧ s.2.1 ≤ s.2.2.2 ∧ s.2.2.1 ≤ s.2.2.2

private instance (s : Square) : Decidable (ignoresFirst s) := inferInstanceAs (Decidable (_ ∧ _))
private instance (s : Square) : Decidable (ignoresSecond s) := inferInstanceAs (Decidable (_ ∧ _))
private instance (s : Square) : Decidable (meet s) := inferInstanceAs (Decidable (_ = _))
private instance (s : Square) : Decidable (join s) := inferInstanceAs (Decidable (_ = _))
private instance (s : Square) : Decidable (increasing s) := inferInstanceAs (Decidable (_ ∧ _))

private def mix (useAnd : Bool) (s t : Square) : Square :=
  let op := if useAnd then (· && ·) else (· || ·)
  (op s.1 t.1, op s.2.1 t.2.1, op s.2.2.1 t.2.2.1, op s.2.2.2 t.2.2.2)

private theorem preserveMeet : ∀ (b : Bool) (s t : Square),
    ((ignoresFirst s ∧ ignoresSecond s ∧ meet t) ∨ (ignoresFirst t ∧ ignoresSecond t ∧ meet s)) →
    meet (mix b s t) := by decide +kernel

private theorem preserveJoin : ∀ (b : Bool) (s t : Square),
    ((ignoresFirst s ∧ ignoresSecond s ∧ join t) ∨ (ignoresFirst t ∧ ignoresSecond t ∧ join s)) →
    join (mix b s t) := by decide +kernel

private theorem splitPreserves : ∀ s t : Square,
    increasing s → increasing t →
    ((ignoresFirst s ∧ ignoresSecond t) ∨ (ignoresSecond s ∧ ignoresFirst t)) →
    meet (mix true s t) ∧ join (mix false s t) := by decide +kernel

private theorem missingPreserves : ∀ s : Square,
    increasing s → (ignoresFirst s ∨ ignoresSecond s) → meet s := by decide +kernel

private theorem mono (f : Formula A) (u : A → Bool) (i j : A) :
    increasing (square f u i j) := by
  have h {a b c d : Bool} (ha : a ≤ c) (hb : b ≤ d) :
      f.evalWith (setTwo u i j a b) ≤ f.evalWith (setTwo u i j c d) := by
    apply evalMono
    intro k
    unfold setTwo
    split
    · exact ha
    · split
      · exact hb
      · exact le_rfl
  exact ⟨h (Bool.false_le _) le_rfl, h le_rfl (Bool.false_le _),
    h le_rfl (Bool.false_le _), h (Bool.false_le _) le_rfl⟩

private theorem skipFirst (f : Formula A) (u : A → Bool) (i j : A) (h : reads f i = 0) :
    ignoresFirst (square f u i j) := by
  have stable (b : Bool) : f.evalWith (setTwo u i j false b) = f.evalWith (setTwo u i j true b) := by
    apply eqOfNoRise
    · intro k
      by_cases k = i <;> simp [setTwo, *]
    · have mass : (fun k => rise (setTwo u i j false b k) (setTwo u i j true b k)) =
          fun k => (singletonInput i k).toNat := by
        funext k
        by_cases ki : k = i <;> simp [setTwo, singletonInput, ki, rise]
      rwa [mass]
  exact ⟨stable false, stable true⟩

private theorem skipSecond (f : Formula A) (u : A → Bool) {i j : A} (ne : i ≠ j)
    (h : reads f j = 0) : ignoresSecond (square f u i j) := by
  have stable (a : Bool) : f.evalWith (setTwo u i j a false) = f.evalWith (setTwo u i j a true) := by
    apply eqOfNoRise
    · intro k
      by_cases ki : k = i <;> by_cases kj : k = j <;> simp [setTwo, ki, kj, ne.symm]
    · have mass : (fun k => rise (setTwo u i j a false k) (setTwo u i j a true k)) =
          fun k => (singletonInput j k).toNat := by
        funext k
        by_cases ki : k = i
        · subst k
          simp [setTwo, singletonInput, ne, rise]
        · by_cases kj : k = j <;> simp [setTwo, singletonInput, ki, kj, ne.symm, rise]
      rwa [mass]
  exact ⟨stable false, stable true⟩

private theorem meetOrJoin (f : Formula A) {i j : A} (ne : i ≠ j)
    (hi : reads f i ≤ 1) (hj : reads f j ≤ 1) :
    (∀ u, meet (square f u i j)) ∨ (∀ u, join (square f u i j)) := by
  induction f with
  | var a =>
    apply Or.inl
    intro u
    refine missingPreserves _ (mono _ _ _ _) ?_
    by_cases e : a = i
    · exact Or.inr (skipSecond _ _ ne (by simp [reads, leafWeight, singletonInput, e, ne]))
    · exact Or.inl (skipFirst _ _ _ _ (by simp [reads, leafWeight, singletonInput, e]))
  | conj l r ihl ihr | disj l r ihl ihr =>
    change reads l i + reads r i ≤ 1 at hi
    change reads l j + reads r j ≤ 1 at hj
    suffices step : ∀ k : Bool, (∀ u, meet (mix k (square l u i j) (square r u i j))) ∨
        (∀ u, join (mix k (square l u i j) (square r u i j))) by
      first | exact step true | exact step false
    intro k
    have passLeft (ri : reads r i = 0) (rj : reads r j = 0) :
        (∀ u, meet (mix k (square l u i j) (square r u i j))) ∨
        (∀ u, join (mix k (square l u i j) (square r u i j))) := by
      rcases ihl (by omega) (by omega) with h | h
      · exact Or.inl (fun u => preserveMeet k _ _ (Or.inr
          ⟨skipFirst r u i j ri, skipSecond r u ne rj, h u⟩))
      · exact Or.inr (fun u => preserveJoin k _ _ (Or.inr
          ⟨skipFirst r u i j ri, skipSecond r u ne rj, h u⟩))
    have passRight (li : reads l i = 0) (lj : reads l j = 0) :
        (∀ u, meet (mix k (square l u i j) (square r u i j))) ∨
        (∀ u, join (mix k (square l u i j) (square r u i j))) := by
      rcases ihr (by omega) (by omega) with h | h
      · exact Or.inl (fun u => preserveMeet k _ _ (Or.inl
          ⟨skipFirst l u i j li, skipSecond l u ne lj, h u⟩))
      · exact Or.inr (fun u => preserveJoin k _ _ (Or.inl
          ⟨skipFirst l u i j li, skipSecond l u ne lj, h u⟩))
    by_cases li : reads l i = 0 <;> by_cases lj : reads l j = 0
    · exact passRight li lj
    ·
      have sides (u : A → Bool) := splitPreserves (square l u i j) (square r u i j)
        (mono l u i j) (mono r u i j)
        (Or.inl ⟨skipFirst l u i j li, skipSecond r u ne (by omega)⟩)
      cases k
      · exact Or.inr (fun u => (sides u).2)
      · exact Or.inl (fun u => (sides u).1)
    ·
      have sides (u : A → Bool) := splitPreserves (square l u i j) (square r u i j)
        (mono l u i j) (mono r u i j)
        (Or.inr ⟨skipSecond l u ne lj, skipFirst r u i j (by omega)⟩)
      cases k
      · exact Or.inr (fun u => (sides u).2)
      · exact Or.inl (fun u => (sides u).1)
    · exact passLeft (by omega) (by omega)

theorem noAndToOr (f : Formula A) {i j : A} (ne : i ≠ j) (hi : reads f i ≤ 1)
    (hj : reads f j ≤ 1) (u v : A → Bool)
    (u10 : f.evalWith (setTwo u i j true false) = false)
    (u01 : f.evalWith (setTwo u i j false true) = false)
    (u11 : f.evalWith (setTwo u i j true true) = true)
    (v00 : f.evalWith (setTwo v i j false false) = false)
    (v10 : f.evalWith (setTwo v i j true false) = true)
    (v01 : f.evalWith (setTwo v i j false true) = true) : False := by
  rcases meetOrJoin f ne hi hj with h | h
  · have m := h v
    simp [meet, square, v00, v10, v01] at m
  · have o := h u
    simp [join, square, u10, u01, u11] at o

end CrownPairFormula
