import PEqualNP.Defs
import PEqualNP.Outside.L_meta_10788

namespace SingleOrRestriction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_10788
open PEqualNP.Outside.L_meta_10788.L11022RestrictSupport
open CircuitHelpers CircuitHelpers.Readers L10586WeightedRestriction

/-- If setting an essential input to false can save at most one gate, its sole
reader in a least circuit is a binary OR with another wire as its operand. -/
theorem tightSoleOr {n s : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {out : ℕ}
    (least : Least (n + 1) f gs out) (p : Fin (n + 1)) (essential : Dep f p)
    (nonconstant : ∀ b : Bool, ∃ x y, f (Function.update x p b) ≠ f (Function.update y p b))
    (lower : ∀ k, HasCircuitSize (n + 1) (fun x => f (Function.update x p false)) k → s ≤ k)
    (budget : gs.length ≤ s + 1) : ∃ r g w,
      gs[r]? = some g ∧ g.op = .or ∧ w ≠ p.val ∧
      (g.inputs = [p.val, w] ∨ g.inputs = [w, p.val]) ∧ ∀ q, Reads gs q p → q = r := by
  have noTwo : ¬ Drop f p false 2 gs.length := by
    rintro ⟨k, saved, fit⟩
    have := lower k fit
    omega
  obtain ⟨r, reader⟩ := least.dep_read p essential nonconstant
  have sole : ∀ q, Reads gs q p → q = r := by
    intro q hq
    by_contra different
    exact noTwo (least.save2 p false (nonconstant false) r q (Ne.symm different)
      (rc_input false reader) (rc_input false hq))
  obtain ⟨g, hit, used⟩ := reader
  have op : g.op = .or := by
    by_contra notOr
    have annihilator : g.op = .not ∨ false = fixBit g := by
      rcases least.hcl r g hit with ⟨neg, _⟩ | ⟨ops, _⟩
      · exact Or.inl neg
      · rcases ops with andGate | orGate
        · exact Or.inr (by simp [fixBit, andGate])
        · exact (notOr orGate).elim
    have constant := isC_reader least.hcl p r g hit used false annihilator
    obtain ⟨q, later, _, charged⟩ := least.next p false (nonconstant false) r
      (reads_len (show Reads gs r p from ⟨g, hit, used⟩)) constant
    exact noTwo (least.save2 p false (nonconstant false) r q (ne_of_lt later)
      (rc_input false ⟨g, hit, used⟩) charged)
  rcases gate_cases gs least.hcl r g hit p.val used with neg | ⟨w, ports, formula⟩
  · rw [op] at neg
    cases neg.1
  · have computes (x : Fin (n + 1) → Bool) :
        vl gs x (n + 1 + r) = (vl gs x p.val || vl gs x w) := by
      rcases formula with andGate | orGate
      · rw [op] at andGate
        cases andGate.1
      · exact orGate.2 x
    refine ⟨r, g, w, hit, op, ?_, ports, sole⟩
    intro equal
    apply least.no_alias (dep_nc essential) r (reads_len (show Reads gs r p from ⟨g, hit, used⟩))
      p.val (by have := p.isLt; omega)
    intro x
    simpa [equal] using computes x

/-- The pinned positions keep the false constant. Every other old wire is
represented by a wire in the simplified circuit, possibly as an alias. -/
structure FixedWires (pin : ℕ → Prop) (xs : List Stat) : Prop where
  early : ∀ i, pin i → i < xs.length
  fixed : ∀ i, pin i → xs.getD i (.const false) = .const false
  wire : ∀ i < xs.length, ¬ pin i → ∃ j, xs.getD i (.const false) = .wire j

private theorem appendWire {pin : ℕ → Prop} {xs : List Stat} (h : FixedWires pin xs) (j : ℕ) :
    FixedWires pin (xs ++ [.wire j]) := by
  refine ⟨fun i hi => by have := h.early i hi; simp; omega, ?_, ?_⟩
  · intro i hit
    rw [List.getD_append _ _ _ _ (h.early i hit)]
    exact h.fixed i hit
  · intro i hi misses
    by_cases before : i < xs.length
    · obtain ⟨w, eq⟩ := h.wire i before misses
      exact ⟨w, (List.getD_append _ _ _ _ before).trans eq⟩
    · have eq : i = xs.length := by simp at hi; omega
      subst i
      exact ⟨j, by simp⟩

/-- A legal gate that reads a pinned input is a binary OR whose other operand
is unpinned. The two orders of the argument list are allowed. -/
def ClearReader (pin : ℕ → Prop) (g : Gate) : Prop :=
  ∃ a b, pin a ∧ ¬ pin b ∧ g.op = .or ∧ (g.inputs = [a, b] ∨ g.inputs = [b, a])

def keepGate (pin : ℕ → Prop) [DecidablePred pin] (g : Gate) : Bool :=
  !(g.inputs.any fun i => decide (pin i))

private theorem keepStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate)
    {pin : ℕ → Prop} (status : FixedWires pin acc.1) (clean : CleanGate acc.1.length g)
    (misses : ∀ a ∈ g.inputs, ¬ pin a) :
    ∃ g', g'.op = g.op ∧ elimStep n acc g =
      (acc.1 ++ [.wire (n + acc.2.length)], acc.2 ++ [g']) := by
  have wires (a : ℕ) (mem : a ∈ g.inputs) := status.wire a (clean.lt a mem) (misses a mem)
  rcases clean with ⟨tag, a, _, ports⟩ | ⟨tag, a, b, _, _, ports⟩
  · obtain ⟨u, hu⟩ := wires a (by simp [ports])
    refine ⟨⟨.not, [u]⟩, tag.symm, ?_⟩
    simp only [elimStep, tag, ports, List.map_cons, List.map_nil, hu, simplify, simpNot]
    rfl
  · obtain ⟨u, hu⟩ := wires a (by simp [ports])
    obtain ⟨v, hv⟩ := wires b (by simp [ports])
    rcases tag with tag | tag
    · refine ⟨⟨.and, [u, v]⟩, tag.symm, ?_⟩
      simp only [elimStep, tag, ports, List.map_cons, List.map_nil, hu, hv, simplify, simpAnd]
      rfl
    · refine ⟨⟨.or, [u, v]⟩, tag.symm, ?_⟩
      simp only [elimStep, tag, ports, List.map_cons, List.map_nil, hu, hv, simplify, simpOr]
      rfl

private theorem clearStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate)
    {pin : ℕ → Prop} (status : FixedWires pin acc.1) (clean : CleanGate acc.1.length g)
    (reader : ClearReader pin g) : ∃ j, elimStep n acc g = (acc.1 ++ [.wire j], acc.2) := by
  obtain ⟨a, b, pa, pb, op, ports⟩ := reader
  have mem : b ∈ g.inputs := by rcases ports with ports | ports <;> simp [ports]
  obtain ⟨w, hw⟩ := status.wire b (clean.lt b mem) pb
  refine ⟨w, ?_⟩
  rcases ports with ports | ports <;>
    simp only [elimStep, op, ports, List.map_cons, List.map_nil, status.fixed a pa, hw, simplify, simpOr] <;>
    simp

/-- Clearing any number of pinned inputs deletes exactly the ORs that read
them, provided each of those ORs has an unpinned operand. The other operations
stay in their original order. -/
theorem restrictOperations (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (pin : ℕ → Prop) [DecidablePred pin] (status : FixedWires pin acc.1)
    (clean : ∀ i g, gs[i]? = some g → CleanGate (acc.1.length + i) g)
    (readers : ∀ g ∈ gs, (∃ a ∈ g.inputs, pin a) → ClearReader pin g) :
    FixedWires pin (elim n gs acc).1 ∧
    (elim n gs acc).2.map Gate.op = acc.2.map Gate.op ++ (gs.filter (keepGate pin)).map Gate.op := by
  induction gs generalizing acc with
  | nil => exact ⟨status, by simp [elim]⟩
  | cons g gs ih =>
    have headClean : CleanGate acc.1.length g := by simpa using clean 0 g rfl
    have tailClean (j : ℕ) (i : ℕ) (t : Gate) (hit : gs[i]? = some t) :
        CleanGate ((acc.1 ++ [Stat.wire j]).length + i) t := by
      have ht : (g :: gs)[i + 1]? = some t := hit
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using clean (i + 1) t ht
    have tailReaders (t : Gate) (mem : t ∈ gs) := readers t (List.mem_cons_of_mem _ mem)
    rw [elim_cons]
    by_cases hit : ∃ a ∈ g.inputs, pin a
    · have absent : keepGate pin g = false := by simp [keepGate, List.any_eq_true, hit]
      obtain ⟨j, hs⟩ := clearStep n acc g status headClean (readers g (by simp) hit)
      rw [hs]
      obtain ⟨h, ops⟩ := ih (acc.1 ++ [.wire j], acc.2) (appendWire status j) (tailClean j) tailReaders
      exact ⟨h, by simpa [absent] using ops⟩
    · have misses (a : ℕ) (mem : a ∈ g.inputs) : ¬ pin a := fun pinned => hit ⟨a, mem, pinned⟩
      have present : keepGate pin g = true := by simpa [keepGate] using misses
      obtain ⟨g', op, hs⟩ := keepStep n acc g status headClean
        misses
      rw [hs]
      obtain ⟨h, ops⟩ := ih (acc.1 ++ [.wire (n + acc.2.length)], acc.2 ++ [g'])
        (appendWire status _) (tailClean _) tailReaders
      exact ⟨h, by simpa [present, op, List.append_assoc] using ops⟩

private theorem initialStatus (n : ℕ) (p : Fin (n + 1)) :
    FixedWires (· = p.val) (statAt n p false) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i e
    simpa only [statAt_length, e] using p.isLt
  · intro i hi
    subst i
    exact statAt_at n p false
  · intro i hi misses
    rw [statAt_length] at hi
    rcases Fin.eq_self_or_eq_succAbove p ⟨i, hi⟩ with e | ⟨k, e⟩
    · exact (misses (congrArg Fin.val e)).elim
    · exact ⟨k, by simpa only [← e] using statAt_above n p false k⟩

/-- For a single pinned input and a unique OR reader, the restriction removes
that OR alone. The equality records the exact sequence of surviving operations. -/
theorem singleOrOperations {n r w : ℕ} {gs : List Gate} {g : Gate} (p : Fin (n + 1))
    (clean : CleanL (n + 1) gs) (hit : gs[r]? = some g) (op : g.op = .or) (peer : w ≠ p.val)
    (ports : g.inputs = [p.val, w] ∨ g.inputs = [w, p.val])
    (sole : ∀ q, Reads gs q p → q = r) :
    (passG n gs p false).map Gate.op = (gs.eraseIdx r).map Gate.op := by
  have covers : ∀ t ∈ gs, (∃ a ∈ t.inputs, a = p.val) → ClearReader (· = p.val) t := by
    intro t mem h
    obtain ⟨a, read, rfl⟩ := h
    obtain ⟨q, atQ⟩ := List.mem_iff_getElem?.mp mem
    have eq := sole q ⟨t, atQ, read⟩
    subst q
    have same := Option.some.inj (atQ.symm.trans hit)
    subst t
    exact ⟨p.val, w, rfl, peer, op, ports⟩
  have ops := (restrictOperations n gs (statAt n p false, []) (· = p.val) (initialStatus n p)
    (by simpa [statAt_length, CleanL] using clean) covers).2
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs r g hit
  have absent : keepGate (· = p.val) g = false := by
    rcases ports with ports | ports <;> simp [keepGate, ports]
  have keepPre : pre.filter (keepGate (· = p.val)) = pre := by
    apply List.filter_eq_self.mpr
    intro t mem
    obtain ⟨i, atI⟩ := List.mem_iff_getElem?.mp mem
    have early := (List.getElem?_eq_some_iff.mp atI).1
    have read : ¬ (p.val ∈ t.inputs) := by
      intro used
      have same := sole i ⟨t, by rwa [List.getElem?_append_left early], used⟩
      omega
    simpa [keepGate] using (fun a (mem : a ∈ t.inputs) (e : a = p.val) => read (e ▸ mem))
  have keepPost : post.filter (keepGate (· = p.val)) = post := by
    apply List.filter_eq_self.mpr
    intro t mem
    obtain ⟨i, atI⟩ := List.mem_iff_getElem?.mp mem
    have read : ¬ (p.val ∈ t.inputs) := by
      intro used
      have atI' : (pre ++ g :: post)[pre.length + 1 + i]? = some t := by
        rw [List.getElem?_append_right (by omega)]
        simpa [show pre.length + 1 + i - pre.length = i + 1 by omega] using atI
      have same := sole _ ⟨t, atI', used⟩
      omega
    simpa [keepGate] using (fun a (mem : a ∈ t.inputs) (e : a = p.val) => read (e ▸ mem))
  simpa [passG, keepPre, keepPost, absent, List.eraseIdx_append] using ops

/-- At the one-gate gap, the false cofactor has exactly one fewer gate and the
same number of NOTs as the original least circuit. -/
theorem tightCofactor {n s : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {out : ℕ}
    (least : Least (n + 1) f gs out) (p : Fin (n + 1)) (essential : Dep f p)
    (nonconstant : ∀ b : Bool, ∃ x y, f (Function.update x p b) ≠ f (Function.update y p b))
    (lower : ∀ k, HasCircuitSize (n + 1) (fun x => f (Function.update x p false)) k → s ≤ k)
    (budget : gs.length ≤ s + 1) :
    ∃ o, CleanL n (passG n gs p false) ∧
      (∀ x, vl (passG n gs p false) x o = f (ins p false x)) ∧
      (passG n gs p false).length + 1 = gs.length ∧
      notGateCount (passG n gs p false) = notGateCount gs := by
  obtain ⟨r, g, w, hit, op, peer, ports, sole⟩ := tightSoleOr least p essential nonconstant lower budget
  have ops := singleOrOperations p least.hcl hit op peer ports sole
  have nc : ∃ x y, f (ins p false x) ≠ f (ins p false y) := by
    obtain ⟨x, y, different⟩ := nonconstant false
    exact ⟨Fin.removeNth p x, Fin.removeNth p y, by simpa only [upd_ins] using different⟩
  obtain ⟨o, clean, computes⟩ := restrict_eval least.hcl least.hev p false nc
  refine ⟨o, clean, computes, ?_, ?_⟩
  · have len := congrArg List.length ops
    obtain ⟨pre, post, rfl, rfl⟩ := split_at gs r g hit
    simp [List.eraseIdx_append] at len ⊢
    omega
  · have count := congrArg (List.countP isNotGate) ops
    simp only [List.countP_map, Function.comp_def] at count
    obtain ⟨pre, post, rfl, rfl⟩ := split_at gs r g hit
    simp only [notGateCount, ← List.countP_eq_length_filter]
    rw [count]
    simp [List.eraseIdx_append, List.countP_append, op, isNotGate]

/-- A lower bound excluding NOTs in the tight cofactor also excludes them in
the original circuit, even when the cofactor's unrestricted minimum is one less. -/
theorem noNotOfTightCofactor {n s : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {out : ℕ}
    (least : Least (n + 1) f gs out) (p : Fin (n + 1)) (essential : Dep f p)
    (nonconstant : ∀ b : Bool, ∃ x y, f (Function.update x p b) ≠ f (Function.update y p b))
    (lower : ∀ k, HasCircuitSize (n + 1) (fun x => f (Function.update x p false)) k → s ≤ k)
    (budget : gs.length ≤ s + 1)
    (signedLower : ∀ ds o, CleanL n ds → (∀ x, vl ds x o = f (ins p false x)) →
      0 < notGateCount ds → s + 1 ≤ ds.length) : notGateCount gs = 0 := by
  obtain ⟨o, clean, computes, len, count⟩ := tightCofactor least p essential nonconstant lower budget
  by_contra! someNot
  have := signedLower _ o clean computes (by omega)
  omega

/-- If there is also a monotone witness at the next size, every circuit can be
replaced by a monotone circuit within the original budget. -/
theorem monotoneReplacement {n s k : ℕ} {f : (Fin (n + 1) → Bool) → Bool}
    (p : Fin (n + 1)) (essential : Dep f p)
    (nonconstant : ∀ b : Bool, ∃ x y, f (Function.update x p b) ≠ f (Function.update y p b))
    (lower : ∀ t, HasCircuitSize (n + 1) (fun x => f (Function.update x p false)) t → s ≤ t)
    (signedLower : ∀ ds o, CleanL n ds → (∀ x, vl ds x o = f (ins p false x)) →
      0 < notGateCount ds → s + 1 ≤ ds.length)
    (witness : ∃ ds o, (∀ g ∈ ds, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      ds.length ≤ s + 2 ∧ ∀ x, Circuit.eval ⟨ds, o⟩ (List.ofFn x) = f x)
    (fit : HasCircuitSize (n + 1) f k) :
    ∃ ds o, (∀ g ∈ ds, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      ds.length ≤ k ∧ ∀ x, Circuit.eval ⟨ds, o⟩ (List.ofFn x) = f x := by
  by_cases enough : s + 2 ≤ k
  · obtain ⟨ds, o, basis, len, computes⟩ := witness
    exact ⟨ds, o, basis, len.trans enough, computes⟩
  · obtain ⟨gs, out, least, len⟩ := exists_least (n + 1) f k (dep_nc essential) fit
    have noNot := noNotOfTightCofactor least p essential nonconstant lower (by omega) signedLower
    have empty : gs.filter (fun g => isNotGate g.op) = [] := List.length_eq_zero_iff.mp noNot
    refine ⟨gs, out, ?_, len, least.hev⟩
    intro g mem
    have noNotOp : g.op ≠ .not := by
      intro neg
      have found : g ∈ gs.filter (fun g => isNotGate g.op) :=
        List.mem_filter.mpr ⟨mem, by simp [neg, isNotGate]⟩
      simp only [empty, List.not_mem_nil] at found
    have good := (clean_nok _ gs least.hcl g mem).1
    exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, noNotOp, or_false]
      using good.1, good.2⟩

/-- An edge from an operand to a binary OR's output. -/
def orEdge (m : ℕ) (gs : List Gate) (a b : ℕ) : Prop :=
  ∃ r g, gs[r]? = some g ∧ b = m + r ∧ g.op = .or ∧ a ∈ g.inputs

theorem orPathTrue {m a b : ℕ} {gs : List Gate} (clean : CleanL m gs) (x : Fin m → Bool)
    (path : Relation.ReflTransGen (orEdge m gs) a b) (on : vl gs x a = true) :
    vl gs x b = true := by
  induction path with
  | refl => exact on
  | tail _ edge ih =>
    obtain ⟨r, g, hit, rfl, op, used⟩ := edge
    rcases gate_cases gs clean r g hit _ used with neg | ⟨_, _, branch⟩
    · rw [op] at neg
      cases neg.1
    · rcases branch with andGate | orGate
      · rw [op] at andGate
        cases andGate.1
      · simp [orGate.2, ih]

/-- When an input changes the output through a sole reader, no wire that is
true on both assignments can reach that reader using only OR gates. -/
theorem trueOrPathBlocksInfluence {m r out start : ℕ} {gs : List Gate} (clean : CleanL m gs)
    (p : Fin m) (reader : Reads gs r p) (sole : ∀ q, Reads gs q p → q = r)
    (outValid : out < m + gs.length) (outApart : out ≠ p.val) (x y : Fin m → Bool)
    (agree : ∀ i ≠ p, x i = y i) (differs : vl gs x out ≠ vl gs y out)
    (xOn : vl gs x start = true) (yOn : vl gs y start = true) :
    ¬ Relation.ReflTransGen (orEdge m gs) start (m + r) := by
  intro path
  let cut : Fin (m + gs.length) := ⟨m + r, by have := reads_len reader; omega⟩
  let output : Fin (m + gs.length) := ⟨out, outValid⟩
  have same : vl gs x cut.val = vl gs y cut.val :=
    (orPathTrue clean x path xOn).trans (orPathTrue clean y path yOn).symm
  have blocked : ∀ i : Fin m, x i ≠ y i →
      ¬ Relation.ReflTransGen (PetersenCutTrace.avoid (PetersenCutTrace.readEdge gs) cut)
        (PetersenCutTrace.inputWire gs i) output := by
    intro i different route
    have ip : i = p := by by_contra apart; exact different (agree i apart)
    subst i
    rcases Relation.ReflTransGen.cases_head route with equal | ⟨_, first, _⟩
    · exact outApart (congrArg Fin.val equal).symm
    · obtain ⟨⟨j, g, hit, dst, uses⟩, _, misses⟩ := first
      have jr := sole j ⟨g, hit, uses⟩
      exact misses (Fin.ext (by simpa [cut, jr] using dst))
  exact differs (PetersenCutTrace.circuit_cut_agreement clean cut output x y same blocked)

end SingleOrRestriction
