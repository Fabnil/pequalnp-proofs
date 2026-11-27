import CrownForestCost

namespace CrownFactorAnd

open CrownForks CrownForestCost PnpResearch

variable {A J : Type}

/-- Sum, over the leaves, of the number of AND gates above each leaf. -/
def andDepthSum : Formula A → ℕ
  | .var _ => 0
  | .disj l r => andDepthSum l + andDepthSum r
  | .conj l r => andDepthSum l + andDepthSum r + formulaGates l + formulaGates r + 2

def andsOff (f : Formula A) (x : A → Bool) : Prop :=
  match f with
  | .var _ => True
  | .disj l r => andsOff l x ∧ andsOff r x
  | .conj l r => f.evalWith x = false ∧ andsOff l x ∧ andsOff r x

private def orLeaf (a : A) : Option (Formula A) → Formula A
  | none => .var a
  | some f => .disj (.var a) f

private def appendOr (r : Formula A) : Option (Formula A) → Formula A
  | none => r
  | some l => .disj l r

private structure Reassociated (f g : Formula A) : Prop where
  eval : ∀ x, g.evalWith x = f.evalWith x
  weight : ∀ w, leafWeight g w = leafWeight f w
  gates : formulaGates g = formulaGates f
  depth : andDepthSum g = andDepthSum f

private theorem Reassociated.trans {f g h : Formula A} (fg : Reassociated f g)
    (gh : Reassociated g h) : Reassociated f h :=
  ⟨fun _ => (gh.eval _).trans (fg.eval _), fun _ => (gh.weight _).trans (fg.weight _),
    gh.gates.trans fg.gates, gh.depth.trans fg.depth⟩

private theorem swapOr (l r : Formula A) : Reassociated (.disj l r) (.disj r l) := by
  constructor
  · intro x
    exact Bool.or_comm _ _
  · intro w
    exact Nat.add_comm _ _
  · simp only [formulaGates, Nat.add_comm (formulaGates l) (formulaGates r)]
  · exact Nat.add_comm _ _

private theorem reassociate (l r : Formula A) (a : A) (tail : Option (Formula A))
    (split : Reassociated l (orLeaf a tail)) :
    Reassociated (.disj l r) (orLeaf a (some (appendOr r tail))) := by
  constructor
  · intro x
    change (orLeaf a (some (appendOr r tail))).evalWith x = (l.evalWith x || r.evalWith x)
    rw [← split.eval x]
    cases tail <;> simp [orLeaf, appendOr, Formula.evalWith, Bool.or_assoc]
  · intro w
    change leafWeight (orLeaf a (some (appendOr r tail))) w = leafWeight l w + leafWeight r w
    rw [← split.weight w]
    cases tail <;> simp [orLeaf, appendOr, leafWeight, Nat.add_assoc]
  · change formulaGates (orLeaf a (some (appendOr r tail))) = formulaGates l + formulaGates r + 1
    rw [← split.gates]
    cases tail <;> simp [orLeaf, appendOr, formulaGates, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  · change andDepthSum (orLeaf a (some (appendOr r tail))) = andDepthSum l + andDepthSum r
    rw [← split.depth]
    cases tail <;> simp [orLeaf, appendOr, andDepthSum]

private theorem exposedLeaf (f : Formula A) (x : A → Bool) (clear : andsOff f x)
    (on : f.evalWith x = true) :
    ∃ a tail, x a = true ∧ Reassociated f (orLeaf a tail) := by
  induction f with
  | var a => exact ⟨a, none, on, ⟨fun _ => rfl, fun _ => rfl, rfl, rfl⟩⟩
  | conj l r il ir =>
    have off : (Formula.conj l r).evalWith x = false := clear.1
    rw [on] at off
    contradiction
  | disj l r il ir =>
    change (l.evalWith x || r.evalWith x) = true at on
    rw [Bool.or_eq_true] at on
    rcases on with hl | hr
    · obtain ⟨a, tail, ha, split⟩ := il clear.1 hl
      exact ⟨a, some (appendOr r tail), ha, reassociate l r a tail split⟩
    · obtain ⟨a, tail, ha, split⟩ := ir clear.2 hr
      exact ⟨a, some (appendOr l tail), ha, (swapOr l r).trans (reassociate r l a tail split)⟩

private theorem exposedLeaf_le (f : Formula A) (a : A) (tail : Option (Formula A))
    (split : Reassociated f (orLeaf a tail)) (x : A → Bool) : x a ≤ f.evalWith x := by
  rw [← split.eval x]
  cases tail with
  | none => exact le_rfl
  | some tail => exact Bool.left_le_or _ _

private def reduces (f g : Formula A) : Prop :=
  formulaGates g < formulaGates f ∨
    (formulaGates g = formulaGates f ∧ (∀ w, leafWeight g w = leafWeight f w) ∧
      andDepthSum g < andDepthSum f)

private theorem reduceLeft (l l' r : Formula A) (better : reduces l l') :
    reduces (.conj l r) (.conj l' r) ∧ reduces (.disj l r) (.disj l' r) := by
  rcases better with fewer | ⟨same, mass, less⟩
  · constructor <;> left <;> simp only [formulaGates] <;> omega
  · constructor <;> right <;> simp [formulaGates, leafWeight, andDepthSum, same, mass] <;> omega

private theorem reduceRight (l r r' : Formula A) (better : reduces r r') :
    reduces (.conj l r) (.conj l r') ∧ reduces (.disj l r) (.disj l r') := by
  rcases better with fewer | ⟨same, mass, less⟩
  · constructor <;> left <;> simp only [formulaGates] <;> omega
  · constructor <;> right <;> simp [formulaGates, leafWeight, andDepthSum, same, mass] <;> omega

private theorem takeOut (val : J → A → Bool) (l r : Formula A) (a : A)
    (tail : Option (Formula A)) (split : Reassociated l (orLeaf a tail))
    (lower : ∀ t, val t a ≤ r.evalWith (val t)) :
    ∃ g : Formula A, (∀ t, g.evalWith (val t) = (Formula.conj l r).evalWith (val t)) ∧
      reduces (.conj l r) g := by
  cases tail with
  | none =>
    refine ⟨.var a, ?_, Or.inl (by simp [formulaGates])⟩
    intro t
    change val t a = (l.evalWith (val t) && r.evalWith (val t))
    rw [← split.eval (val t)]
    have absorb : ∀ x y : Bool, x ≤ y → x = (x && y) := by decide
    exact absorb _ _ (lower t)
  | some tail =>
    refine ⟨.disj (.var a) (.conj tail r), ?_, Or.inr ⟨?_, ?_, ?_⟩⟩
    · intro t
      change (val t a || (tail.evalWith (val t) && r.evalWith (val t))) =
        (l.evalWith (val t) && r.evalWith (val t))
      rw [← split.eval (val t)]
      have factor : ∀ x y z : Bool, x ≤ z → (x || (y && z)) = ((x || y) && z) := by decide
      exact factor _ _ _ (lower t)
    · have size := split.gates
      simp only [orLeaf, formulaGates] at size ⊢
      omega
    · intro w
      have weight := split.weight w
      simp only [orLeaf, leafWeight] at weight ⊢
      omega
    · have size := split.gates
      have depth := split.depth
      simp only [orLeaf, formulaGates, andDepthSum] at size depth ⊢
      omega

private theorem improveAt (val : J → A → Bool) (t : J)
    (compare : ∀ a b, val t a = true → val t b = true →
      (∀ q, val q a ≤ val q b) ∨ (∀ q, val q b ≤ val q a))
    (f : Formula A) (bad : ¬ andsOff f (val t)) :
    ∃ g : Formula A, (∀ q, g.evalWith (val q) = f.evalWith (val q)) ∧ reduces f g := by
  induction f with
  | var a => exact (bad trivial).elim
  | disj l r il ir =>
    by_cases hl : andsOff l (val t)
    · obtain ⟨r', eq, advance⟩ := ir (fun hr => bad ⟨hl, hr⟩)
      exact ⟨.disj l r', fun q => by simp only [Formula.evalWith, eq q],
        (reduceRight l r r' advance).2⟩
    · obtain ⟨l', eq, advance⟩ := il hl
      exact ⟨.disj l' r, fun q => by simp only [Formula.evalWith, eq q],
        (reduceLeft l l' r advance).2⟩
  | conj l r il ir =>
    by_cases hl : andsOff l (val t)
    · by_cases hr : andsOff r (val t)
      · have on : (l.evalWith (val t) && r.evalWith (val t)) = true := by
          exact Bool.eq_true_of_not_eq_false fun off => bad ⟨off, hl, hr⟩
        rw [Bool.and_eq_true] at on
        obtain ⟨u, restL, hu, left⟩ := exposedLeaf l _ hl on.1
        obtain ⟨v, restR, hv, right⟩ := exposedLeaf r _ hr on.2
        rcases compare u v hu hv with uv | vu
        · exact takeOut val l r u restL left (fun q => (uv q).trans (exposedLeaf_le r v restR right _))
        · obtain ⟨g, eq, advance⟩ := takeOut val r l v restR right
            (fun q => (vu q).trans (exposedLeaf_le l u restL left _))
          refine ⟨g, fun q => (eq q).trans (Bool.and_comm _ _), ?_⟩
          simpa [reduces, formulaGates, leafWeight, andDepthSum, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc] using advance
      · obtain ⟨r', eq, advance⟩ := ir hr
        exact ⟨.conj l r', fun q => by simp only [Formula.evalWith, eq q],
          (reduceRight l r r' advance).1⟩
    · obtain ⟨l', eq, advance⟩ := il hl
      exact ⟨.conj l' r, fun q => by simp only [Formula.evalWith, eq q],
        (reduceLeft l l' r advance).1⟩

/-- At samples where every two active leaves are comparable, every AND can be
    made inactive while retaining all leaf counts, or the formula can shrink. -/
theorem normalize (val : J → A → Bool) (sample : J → Prop)
    (compare : ∀ t, sample t → ∀ a b, val t a = true → val t b = true →
      (∀ q, val q a ≤ val q b) ∨ (∀ q, val q b ≤ val q a))
    (f : Formula A) :
    ∃ g : Formula A, (∀ q, g.evalWith (val q) = f.evalWith (val q)) ∧
      (formulaGates g < formulaGates f ∨
        (formulaGates g = formulaGates f ∧ (∀ w, leafWeight g w = leafWeight f w) ∧
          ∀ t, sample t → andsOff g (val t))) := by
  classical
  let candidates (n : ℕ) := ∃ g : Formula A,
    (∀ q, g.evalWith (val q) = f.evalWith (val q)) ∧ formulaGates g = formulaGates f ∧
      (∀ w, leafWeight g w = leafWeight f w) ∧ andDepthSum g = n
  have existsCandidate : ∃ n, candidates n :=
    ⟨andDepthSum f, f, fun _ => rfl, rfl, fun _ => rfl, rfl⟩
  obtain ⟨g, equal, same, reads, minimal⟩ := Nat.find_spec existsCandidate
  by_cases all : ∀ t, sample t → andsOff g (val t)
  · exact ⟨g, equal, Or.inr ⟨same, reads, all⟩⟩
  · push Not at all
    obtain ⟨t, inside, bad⟩ := all
    obtain ⟨h, eq, progress⟩ := improveAt val t (compare t inside) g bad
    have eval (q : J) := (eq q).trans (equal q)
    rcases progress with fewer | ⟨size, mass, less⟩
    · exact ⟨h, eval, Or.inl (fewer.trans_le same.le)⟩
    · have new : candidates (andDepthSum h) :=
        ⟨h, eval, size.trans same, fun w => (mass w).trans (reads w), rfl⟩
      exact (not_lt_of_ge (Nat.find_min' existsCandidate new) (minimal ▸ less)).elim

end CrownFactorAnd
