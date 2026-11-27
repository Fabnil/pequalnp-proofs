import PEqualNP.Defs
import PEqualNP.Outside.L_meta_10788
import PEqualNP.Outside.L_meta_10890

namespace LeafWheel29220

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_10788.L11022RestrictSupport
open CircuitHelpers CircuitHelpers.PermInputs CircuitHelpers.Readers

def target (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) ||
  (x 1 && x 6) || (x 3 && x 6) || (x 5 && x 6) || (x 0 && x 7) ||
  (x 1 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)

def restricted (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 1 && x 5) ||
  (x 2 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) ||
  (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)

def insertFalse (x : Fin 7 → Bool) : Fin 8 → Bool :=
  ![x 0, x 1, false, x 2, x 4, x 3, x 5, x 6]

/-- Clearing leaf 2 and permuting inputs yields the graph of L-meta-10890. -/
theorem restriction : ∀ x : Fin 7 → Bool, target (insertFalse x) = restricted x := by
  decide +kernel

def circuit : Circuit := ⟨
  [⟨.or, [0, 2]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [5, 10]⟩,
   ⟨.or, [1, 3]⟩, ⟨.or, [12, 7]⟩, ⟨.and, [6, 13]⟩, ⟨.or, [0, 1]⟩,
   ⟨.or, [4, 7]⟩, ⟨.and, [15, 16]⟩, ⟨.and, [4, 7]⟩, ⟨.or, [11, 14]⟩,
   ⟨.or, [17, 18]⟩, ⟨.or, [19, 20]⟩], 21⟩

theorem upper : Monotone2 circuit ∧ circuit.size = 14 ∧
    ∀ x : Fin 8 → Bool, circuit.eval (List.ofFn x) = target x := by
  refine ⟨?_, rfl, ?_⟩
  · simp [circuit, Monotone2]
  · decide +kernel

private def mark (i j : Fin 8) : Fin 8 → Bool :=
  fun k => decide (k = i ∨ k = j)

private theorem nonconstant : ∃ x y : Fin 8 → Bool, target x ≠ target y := by
  refine ⟨mark 0 4, fun _ => false, ?_⟩
  decide +kernel

private theorem essential (p : Fin 8) (h : p = 2 ∨ p = 3) : Dep target p := by
  rcases h with rfl | rfl
  · refine ⟨mark 5 5, ?_⟩
    decide +kernel
  · refine ⟨mark 6 6, ?_⟩
    decide +kernel

private theorem nonconstantPinned (p : Fin 8) (h : p = 2 ∨ p = 3) (b : Bool) :
    ∃ x y : Fin 8 → Bool, target (Function.update x p b) ≠ target (Function.update y p b) := by
  refine ⟨mark 0 4, fun _ => false, ?_⟩
  rcases h with rfl | rfl <;> cases b <;> decide +kernel

private def labels2 (i : Fin 8) : Fin 7 := ![0, 1, 0, 2, 4, 3, 5, 6] i
private def labels3 (i : Fin 8) : Fin 7 := ![1, 0, 2, 0, 4, 5, 3, 6] i

private theorem relabel2 : ∀ x : Fin 7 → Bool,
    target (Function.update (x ∘ labels2) 2 false) = restricted x := by decide +kernel

private theorem relabel3 : ∀ x : Fin 7 → Bool,
    target (Function.update (x ∘ labels3) 3 false) = restricted x := by decide +kernel

theorem pinnedLower (p : Fin 8) (leaf : p = 2 ∨ p = 3) {s : ℕ}
    (fit : HasCircuitSize 8 (fun x => target (Function.update x p false)) s) : 12 ≤ s := by
  have h : HasCircuitSize 7 restricted s := by
    rcases leaf with rfl | rfl
    · have h := relabel_size labels2 _ s fit
      change HasCircuitSize 7 (fun x => target (Function.update (x ∘ labels2) 2 false)) s at h
      rwa [funext relabel2] at h
    · have h := relabel_size labels3 _ s fit
      change HasCircuitSize 7 (fun x => target (Function.update (x ∘ labels3) 3 false)) s at h
      rwa [funext relabel3] at h
  exact PEqualNP.Outside.L_meta_10890_aux.final s h

/-- The lower bound counts AND, OR, and NOT gates with no limit on the number of NOTs. -/
theorem lower {s : ℕ} (fit : HasCircuitSize 8 target s) : 13 ≤ s := by
  obtain ⟨gs, o, least, bound⟩ := exists_least 8 target s nonconstant fit
  let p : Fin 8 := 2
  have hp : p = 2 ∨ p = 3 := Or.inl rfl
  obtain ⟨r, hr⟩ := least.dep_read p (essential p hp) (nonconstantPinned p hp)
  have drop := least.save p false (nonconstantPinned p hp false) {r} (by
    intro q hq
    have e : q = r := Finset.mem_singleton.mp hq
    subst q
    exact rc_input false hr)
  obtain ⟨t, saved, residual⟩ := drop
  have bound' := pinnedLower p hp residual
  simp only [Finset.card_singleton] at saved
  omega

/-- Each pendant input of a normalized circuit at the lower budget has a single OR reader. -/
theorem soleReader {gs : List Gate} {o : ℕ} (clean : CleanL 8 gs)
    (correct : ∀ x, vl gs x o = target x) (size : gs.length ≤ 13)
    (p : Fin 8) (leaf : p = 2 ∨ p = 3) : ∃ r g w,
      gs[r]? = some g ∧ g.op = .or ∧ w ≠ p.val ∧
      (g.inputs = [p.val, w] ∨ g.inputs = [w, p.val]) ∧
      ∀ q, Reads gs q p → q = r := by
  have least : Least 8 target gs o := by
    refine ⟨clean, correct, ?_⟩
    intro ds out dc de
    have fits : HasCircuitSize 8 target ds.length := by
      simpa only [de] using has_of_clean 8 ds out dc
    exact size.trans (lower fits)
  have fixedNC := nonconstantPinned p leaf false
  have noTwo : ¬ Drop target p false 2 gs.length := by
    rintro ⟨s, budget, fits⟩
    have bound := pinnedLower p leaf fits
    omega
  obtain ⟨r, reader⟩ := least.dep_read p (essential p leaf) (nonconstantPinned p leaf)
  have sole : ∀ q, Reads gs q p → q = r := by
    intro q hq
    by_contra diff
    exact noTwo (least.save2 p false fixedNC r q (fun eq => diff eq.symm)
      (rc_input false reader) (rc_input false hq))
  obtain ⟨g, rg, rp⟩ := reader
  have op : g.op = .or := by
    by_contra notOr
    have annihilator : g.op = .not ∨ false = fixBit g := by
      rcases clean r g rg with ⟨neg, _⟩ | ⟨ops, _⟩
      · exact Or.inl neg
      · rcases ops with andGate | orGate
        · exact Or.inr (by simp [fixBit, andGate])
        · exact (notOr orGate).elim
    have affected := isC_reader clean p r g rg rp false annihilator
    obtain ⟨q, after, _, charged⟩ := least.next p false fixedNC r
      (reads_len (show Reads gs r p from ⟨g, rg, rp⟩)) affected
    exact noTwo (least.save2 p false fixedNC r q (ne_of_lt after)
      (rc_input false ⟨g, rg, rp⟩) charged)
  rcases gate_cases gs clean r g rg p.val rp with neg | ⟨w, args, formula⟩
  · rw [op] at neg
    cases neg.1
  · have same : ∀ x : Fin 8 → Bool,
        vl gs x (8 + r) = (vl gs x p.val || vl gs x w) := by
      rcases formula with andGate | orGate
      · rw [op] at andGate
        cases andGate.1
      · exact orGate.2
    have apart : w ≠ p.val := by
      intro eq
      apply least.no_alias nonconstant r (reads_len (show Reads gs r p from ⟨g, rg, rp⟩))
        p.val (by have := p.isLt; omega)
      intro x
      simpa [eq] using same x
    exact ⟨r, g, w, rg, op, apart, args, sole⟩

private theorem singletonRejects : ∀ i : Fin 8, target (mark i i) = false := by decide +kernel

private theorem differentLeaves : ∀ i : Fin 8,
    mark 2 5 i ≠ mark 3 5 i → i = 2 ∨ i = 3 := by decide +kernel

/-- The two unique OR readers have different gate indices. -/
theorem distinctReaders {gs : List Gate} {o : ℕ} (clean : CleanL 8 gs)
    (correct : ∀ x, vl gs x o = target x) (size : gs.length ≤ 13) :
    ∃ r s, r ≠ s ∧ Reads gs r (2 : ℕ) ∧ Reads gs s (3 : ℕ) := by
  obtain ⟨r, g, w, rg, op, _, args, uOnly⟩ := soleReader clean correct size 2 (Or.inl rfl)
  obtain ⟨s, g', _, sg, _, _, args', vOnly⟩ := soleReader clean correct size 3 (Or.inr rfl)
  have reads2 : Reads gs r (2 : ℕ) := by
    refine ⟨g, rg, ?_⟩
    rcases args with e | e <;> simp [e]
  have reads3 : Reads gs s (3 : ℕ) := by
    refine ⟨g', sg, ?_⟩
    rcases args' with e | e <;> simp [e]
  refine ⟨r, s, ?_, reads2, reads3⟩
  intro shared
  subst s
  have gateEq : g' = g := Option.some.inj (sg.symm.trans rg)
  subst g'
  have input3 : (3 : ℕ) ∈ g.inputs := by
    rcases args' with e | e <;> simp [e]
  have peer : w = 3 := by
    rcases args with e | e <;> simp [e] at input3 <;> omega
  have readout (x : Fin 8 → Bool) : vl gs x (8 + r) = (x 2 || x 3) := by
    rw [vl_gate gs clean x r g rg, op]
    rcases args with e | e
    · simp [e, peer, GateOp.eval, vl_input gs x 2 (by decide), vl_input gs x 3 (by decide)]
    · simp [e, peer, GateOp.eval, vl_input gs x 2 (by decide), vl_input gs x 3 (by decide),
        Bool.or_comm]
  have yes : target (mark 2 5) = true := by decide +kernel
  have no : target (mark 3 5) = false := by decide +kernel
  have validOut : o < 8 + gs.length := by
    by_contra! past
    have claim := correct (mark 2 5)
    rw [vl_beyond gs _ _ past, yes] at claim
    cases claim
  have nonInput (i : Fin 8) : o ≠ i.val := by
    intro e
    have claim := correct (mark i i)
    rw [e, vl_input gs _ _ i.isLt, singletonRejects] at claim
    simp [mark] at claim
  let cut : Fin (8 + gs.length) := ⟨8 + r, by have := reads_len reads2; omega⟩
  let out : Fin (8 + gs.length) := ⟨o, validOut⟩
  have sameAtCut : vl gs (mark 2 5) cut.val = vl gs (mark 3 5) cut.val := by
    change vl gs (mark 2 5) (8 + r) = vl gs (mark 3 5) (8 + r)
    rw [readout, readout]
    decide +kernel
  have blocks : ∀ i : Fin 8, mark 2 5 i ≠ mark 3 5 i →
      ¬ Relation.ReflTransGen (PetersenCutTrace.avoid (PetersenCutTrace.readEdge gs) cut)
        (PetersenCutTrace.inputWire gs i) out := by
    intro i different path
    rcases Relation.ReflTransGen.cases_head path with same | ⟨v, first, _⟩
    · exact nonInput i (congrArg Fin.val same).symm
    · obtain ⟨⟨j, t, atJ, dst, uses⟩, _, misses⟩ := first
      have hits : Reads gs j i := ⟨t, atJ, uses⟩
      have jr : j = r := by
        rcases differentLeaves i different with rfl | rfl
        · exact uOnly j hits
        · exact vOnly j hits
      exact misses (Fin.ext (by simpa [cut, jr] using dst))
  have eq := PetersenCutTrace.circuit_cut_agreement clean cut out (mark 2 5) (mark 3 5) sameAtCut blocks
  change vl gs (mark 2 5) o = vl gs (mark 3 5) o at eq
  rw [correct, correct, yes, no] at eq
  cases eq

end LeafWheel29220
