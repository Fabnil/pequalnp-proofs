import CrownForks
import CrownRun

/-!
A resource run factors into a sequence of shared formulas. Every repeated
result becomes a new variable in the formulas that follow it. The factorization
preserves the use count of each original variable and charges each extra copy.
-/

namespace CrownForest

open PnpResearch CrownForks CrownRun

inductive SharedFormula : Type → Type 1 where
  | tree {A : Type} (f : Formula A) : SharedFormula A
  | share {A : Type} (f : Formula A) (extra : ℕ)
      (rest : SharedFormula (Option A)) : SharedFormula A

namespace SharedFormula

def eval {A : Type} : SharedFormula A → (A → Bool) → Bool
  | .tree f, x => f.evalWith x
  | .share f _ rest, x => eval rest (withHead (f.evalWith x) x)

def weight {A : Type} : SharedFormula A → (A → ℕ) → ℕ
  | .tree f, w => leafWeight f w
  | .share f _ rest, w => leafWeight f w + weight rest (withHead 0 w)

def extraUses {A : Type} : SharedFormula A → ℕ
  | .tree _ => 0
  | .share _ extra rest => extra + extraUses rest

def Valid {A : Type} : SharedFormula A → Prop
  | .tree _ => True
  | .share _ extra rest =>
    0 < extra ∧ Valid rest ∧ weight rest (withHead 1 fun _ => 0) = extra + 1

def evalFn {A : Type} {n : ℕ} (f : SharedFormula A) (value : A → BF n) : BF n :=
  fun x => f.eval (fun a => value a x)

end SharedFormula

def wire {A : Type} {n : ℕ} (value : A → BF n) (f : Formula A) : BF n :=
  fun x => f.evalWith (fun a => value a x)

def stock {A : Type} (fs : List (Formula A)) (w : A → ℕ) : ℕ :=
  (fs.map fun f => leafWeight f w).sum

theorem stock_append {A : Type} (fs gs : List (Formula A)) (w : A → ℕ) :
    stock (fs ++ gs) w = stock fs w + stock gs w := by simp [stock]

theorem stock_replicate {A : Type} (count : ℕ) (a : A) (w : A → ℕ) :
    stock (List.replicate count (.var a)) w = count * w a := by
  simp [stock, leafWeight, List.sum_replicate]

theorem stock_rename {A B : Type} (fs : List (Formula A)) (f : A → B) (w : B → ℕ) :
    stock (fs.map (fun t => rename t f)) w = stock fs (w ∘ f) := by
  simp [stock, List.map_map, Function.comp_def, weight_rename]

theorem stock_zero {A : Type} (fs : List (Formula A)) : stock fs (fun _ => 0) = 0 := by
  have f0 (f : Formula A) : leafWeight f (fun _ => 0) = 0 := by
    induction f <;> simp_all [leafWeight]
  induction fs <;> simp_all [stock]

theorem wire_rename {A B : Type} {n : ℕ} (f : Formula A) (map : A → B) (value : B → BF n) :
    wire value (rename f map) = wire (value ∘ map) f := by
  funext x
  exact eval_rename f map (fun b => value b x)

-- Selection from a multiset of stored values, as in L_meta_18242.
private theorem map_perm_cons {A B : Type} (f : A → B) {xs : List A} {b : B} {ys : List B}
    (h : (xs.map f).Perm (b :: ys)) :
    ∃ a zs, xs.Perm (a :: zs) ∧ f a = b ∧ (zs.map f).Perm ys := by
  have hb : b ∈ xs.map f := h.mem_iff.2 (by simp)
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb
  obtain ⟨l, r, rfl⟩ := List.append_of_mem ha
  refine ⟨a, l ++ r, List.perm_middle, rfl, ?_⟩
  exact (((List.perm_middle (a := a) (l₁ := l) (l₂ := r)).map f).symm.trans h).cons_inv

theorem fromTrace {n t : ℕ} {F : BF n} {ws : List (BF n)} (run : MR [F] t ws) :
    ∀ (A : Type) (value : A → BF n) (fs : List (Formula A)), (fs.map (wire value)).Perm ws →
      ∃ E : SharedFormula A, E.Valid ∧ E.evalFn value = F ∧
        (∀ w, E.weight w = stock fs w) ∧ fs.length + E.extraUses = t + 1 := by
  refine TR.ind (P := fun t ws => ∀ (A : Type) (value : A → BF n) (fs : List (Formula A)),
    (fs.map (wire value)).Perm ws →
      ∃ E : SharedFormula A, E.Valid ∧ E.evalFn value = F ∧
        (∀ w, E.weight w = stock fs w) ∧ fs.length + E.extraUses = t + 1)
    run ?_ ?_ ?_
  · intro A value fs actual
    have length : fs.length = 1 := by simpa using actual.length_eq
    obtain ⟨f, rfl⟩ := List.length_eq_one_iff.mp length
    refine ⟨.tree f, trivial, ?_, fun w => by simp [stock, SharedFormula.weight], rfl⟩
    change wire value f = F
    simpa using actual
  · intro _ xs ys p _ ih A value fs actual
    exact ih A value fs (actual.trans p.symm)
  · intro s a b rest k extra op _ ih A value fs actual
    obtain ⟨l, tail, permL, valL, afterL⟩ := map_perm_cons (wire value) actual
    obtain ⟨r, restFs, permR, valR, afterR⟩ := map_perm_cons (wire value) afterL
    have perm := permL.trans (permR.cons l)
    let f : Formula A := if k = 0 then .conj l r else .disj l r
    have val : wire value f = gF k a b := by
      rcases mono_cases k op with rfl | rfl
      · simp only [f, ite_eq_left (rfl : (0 : Fin 4) = 0), gF_and]
        funext x
        change (wire value l x && wire value r x) = (a x && b x)
        rw [valL, valR]
      · have ne : (1 : Fin 4) ≠ 0 := by decide
        simp only [f, ite_eq_right ne, gF_or]
        funext x
        change (wire value l x || wire value r x) = (a x || b x)
        rw [valL, valR]
    have count : fs.length = restFs.length + 2 := by
      simpa [Nat.add_assoc] using perm.length_eq
    have mass (w : A → ℕ) : leafWeight f w + stock restFs w = stock fs w := by
      have eq := (perm.map (fun u => leafWeight u w)).sum_eq
      by_cases op : k = 0 <;>
        simpa [f, op, stock, leafWeight, Nat.add_assoc] using eq.symm
    by_cases e : extra = 0
    · subst extra
      have fits : ((f :: restFs).map (wire value)).Perm
          (List.replicate (0 + 1) (gF k a b) ++ rest) := by
        simpa [val] using afterR.cons (gF k a b)
      obtain ⟨E, ok, ev, use, cost⟩ := ih A value (f :: restFs) fits
      refine ⟨E, ok, ev, fun w => ?_, ?_⟩
      · rw [use]
        simpa [stock] using mass w
      · simp only [List.length_cons] at cost
        omega
    · let moved : Option A → BF n := withHead (wire value f) value
      let follow : List (Formula (Option A)) :=
        List.replicate (extra + 1) (.var none) ++ restFs.map (fun t => rename t some)
      have newTail : ((restFs.map fun t => rename t some).map (wire moved)).Perm rest := by
        have ren (f : Formula A) : wire moved (rename f some) = wire value f :=
          (wire_rename f some moved).trans rfl
        simpa [List.map_map, Function.comp_def, ren] using afterR
      have first : wire moved (.var none) = gF k a b := val
      have fits : (follow.map (wire moved)).Perm
          (List.replicate (extra + 1) (gF k a b) ++ rest) := by
        simp only [follow, List.map_append, List.map_replicate, first]
        exact (List.Perm.refl _).append newTail
      obtain ⟨E, ok, ev, use, cost⟩ := ih (Option A) moved follow fits
      have headCount : E.weight (withHead 1 fun _ => 0) = extra + 1 := by
        rw [use]
        simp only [follow]
        rw [stock_append, stock_replicate, stock_rename, withHead_none, Nat.mul_one]
        change extra + 1 + stock restFs (fun _ => 0) = extra + 1
        rw [stock_zero, Nat.add_zero]
      refine ⟨.share f extra E, ⟨by omega, ok, headCount⟩, ?_, ?_, ?_⟩
      · suffices eval : (SharedFormula.share f extra E).evalFn value = E.evalFn moved from
          eval.trans ev
        funext x
        apply congrArg E.eval
        funext z
        cases z <;> rfl
      · intro w
        change leafWeight f w + E.weight (withHead 0 w) = _
        rw [use]
        simp only [follow]
        rw [stock_append, stock_replicate, stock_rename, withHead_none, Nat.mul_zero,
          Nat.zero_add]
        exact mass w
      · simp only [follow, List.length_append, List.length_replicate, List.length_map] at cost
        change fs.length + (extra + E.extraUses) = _
        omega

theorem stock_vars {I : Type} [DecidableEq I] (idx : List I) (i : I) :
    stock (idx.map Formula.var) (fun k => (singletonInput i k).toNat) = idx.count i := by
  induction idx with
  | nil => simp [stock]
  | cons k ks ih =>
    change (singletonInput i k).toNat + stock (ks.map Formula.var) _ = (k :: ks).count i
    rw [ih]
    by_cases eq : k = i <;> simp [singletonInput, eq, Nat.add_comm]

theorem fromCircuit {n : ℕ} {C : PEqualNP.CircuitLowerBounds.Circuit}
    (mono : PEqualNP.MetaComplexity.Monotone2 C) (F : BF n)
    (acts : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = F x)
    (nonzero : F ≠ zF) (nonone : F ≠ oneF) :
    ∃ idx : List (Fin n), ∃ E : SharedFormula (Fin n),
      E.Valid ∧ E.eval = F ∧ (∀ i, E.weight (fun k => (singletonInput i k).toNat) = idx.count i) ∧
        idx.length + E.extraUses ≤ C.size + 1 := by
  obtain ⟨t, ht, idx, run⟩ := CrownRun.fromCircuit mono F acts nonzero nonone
  have start : ((idx.map Formula.var).map (wire var)).Perm (idx.map var) := by
    rw [List.map_map]
    exact List.Perm.refl _
  obtain ⟨E, ok, ev, mass, time⟩ := fromTrace run (Fin n) var (idx.map Formula.var) start
  refine ⟨idx, E, ok, ev, ?_, ?_⟩
  · intro i
    rw [mass]
    exact stock_vars idx i
  · simp only [List.length_map] at time
    omega

theorem readTwiceByExtraUses {I : Type} [Fintype I] [DecidableEq I] (E : SharedFormula I)
    (ok : E.Valid) (test : ThresholdOn E.eval)
    (raw : ∀ i, E.weight (fun k => (singletonInput i k).toNat) ≤ 2)
    (extra : E.extraUses ≤ 2) : Fintype.card I ≤ 4 + E.extraUses := by
  cases E with
  | tree f =>
    exact formulaThresholdCapacity f test raw
  | share p u tail =>
    cases tail with
    | tree h =>
      have head : Samples.headUses h = u + 1 := ok.2.2
      have cost : u ≤ 2 := by simpa [SharedFormula.extraUses] using extra
      have positive : 0 < u := ok.1
      have bound := oneSharedThresholdCapacity p h test raw (by omega)
      simp only [SharedFormula.extraUses]
      omega
    | share q v last =>
      cases last with
      | tree h =>
        let N : TwoShared I := ⟨p, q, h⟩
        have first : N.pUses = u + 1 := ok.2.2
        have second : N.qUses = v + 1 := ok.2.1.2.2
        have up : 0 < u := ok.1
        have vp : 0 < v := ok.2.1.1
        have uv : u + v ≤ 2 := by simpa [SharedFormula.extraUses] using extra
        have r : ∀ i, N.firstRaw i + N.secondRaw i + N.outputRaw i ≤ 2 := by
          intro i
          simpa [N, TwoShared.firstRaw, TwoShared.secondRaw, TwoShared.outputRaw,
            SharedFormula.weight, Nat.add_assoc] using raw i
        have bound := N.capacity test r (by omega) (by omega)
        simp only [SharedFormula.extraUses]
        omega
      | share r w more =>
        have up : 0 < u := ok.1
        have vp : 0 < v := ok.2.1.1
        have wp : 0 < w := ok.2.1.2.1.1
        simp only [SharedFormula.extraUses] at extra
        omega

theorem readTwiceCapacity {I : Type} [Fintype I] [DecidableEq I] (E : SharedFormula I)
    (ok : E.Valid) (test : ThresholdOn E.eval)
    (raw : ∀ i, E.weight (fun k => (singletonInput i k).toNat) ≤ 2)
    (extra : E.extraUses ≤ 2) : Fintype.card I ≤ 6 := by
  have limit := readTwiceByExtraUses E ok test raw extra
  omega

theorem noReadTwiceBefore {n : ℕ} {F : BF n} {idx : List (Fin n)} {s : ℕ}
    (run : MR [F] s (idx.map var)) (test : ThresholdOn F) (upper : n ≤ 7) (small : s + 6 ≤ 3 * n)
    (raw : ∀ i, idx.count i = 2) : False := by
  have start : ((idx.map Formula.var).map (wire var)).Perm (idx.map var) := by
    rw [List.map_map]
    exact List.Perm.refl _
  obtain ⟨E, ok, ev, mass, time⟩ := fromTrace run (Fin n) var (idx.map Formula.var) start
  have all : idx.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    apply List.mem_toFinset.mpr
    exact List.count_pos_iff.mp (by rw [raw]; decide)
  have length : idx.length = 2 * n := by
    rw [← List.sum_toFinset_count_eq_length idx, all]
    simp [raw, Nat.mul_comm]
  simp only [List.length_map, length] at time
  have size : E.extraUses ≤ 2 := by
    omega
  have counts (i : Fin n) : E.weight (fun k => (singletonInput i k).toNat) ≤ 2 := by
    rw [mass, stock_vars, raw]
  have correct : ThresholdOn E.eval := by
    change E.eval = F at ev
    rwa [ev]
  have contradiction : n ≤ 4 + E.extraUses := by
    simpa using readTwiceByExtraUses E ok correct counts size
  omega

theorem noFifteenReadTwice {F : BF 7} {idx : List (Fin 7)} {s : ℕ}
    (run : MR [F] s (idx.map var)) (test : ThresholdOn F) (small : s ≤ 15)
    (raw : ∀ i, idx.count i = 2) : False :=
  noReadTwiceBefore run test (by decide) (by omega) raw

end CrownForest
