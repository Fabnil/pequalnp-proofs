import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Induction
import PEqualNP.Defs.MetaComplexityLgpMono
import PEqualNP.Defs.Represents

namespace PnpResearch

inductive Formula (α : Type) where
  | var (x : α)
  | conj (f g : Formula α)
  | disj (f g : Formula α)

namespace Formula

variable {α : Type} [DecidableEq α]

def vars : Formula α → Finset α
  | var x => {x}
  | conj f g | disj f g => f.vars ∪ g.vars

def eval : Formula α → Finset α → Bool
  | var x, s => decide (x ∈ s)
  | conj f g, s => f.eval s && g.eval s
  | disj f g, s => f.eval s || g.eval s

def ReadOnce : Formula α → Prop
  | var _ => True
  | conj f g | disj f g => Disjoint f.vars g.vars ∧ f.ReadOnce ∧ g.ReadOnce

private theorem empty (f : Formula α) : f.eval ∅ = false := by
  induction f <;> simp_all [eval]

private theorem eval_congr (f : Formula α) {s t : Finset α}
    (h : ∀ x ∈ f.vars, x ∈ s ↔ x ∈ t) : f.eval s = f.eval t := by
  induction f with
  | var x =>
    have hx := h x (by simp [vars])
    change decide (x ∈ s) = decide (x ∈ t)
    by_cases hs : x ∈ s
    · have ht := hx.mp hs
      simp [hs, ht]
    · have ht : x ∉ t := fun h => hs (hx.mpr h)
      simp [hs, ht]
  | conj f g ihf ihg | disj f g ihf ihg =>
    have hf := ihf (fun x hx => h x (Finset.mem_union_left _ hx))
    have hg := ihg (fun x hx => h x (Finset.mem_union_right _ hx))
    simp only [eval, hf, hg]

private theorem drop_right (f : Formula α) {a b : α} (hb : b ∉ f.vars) :
    f.eval {a, b} = f.eval {a} := by
  apply eval_congr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · rfl
    · exact (hb hx).elim
  · exact Or.inl

private theorem drop_left (f : Formula α) {a b : α} (ha : a ∉ f.vars) :
    f.eval {a, b} = f.eval {b} := by
  have swap : ({a, b} : Finset α) = {b, a} := by
    ext x
    simp [or_comm]
  rw [swap]
  exact drop_right f ha

private theorem mem_of_singleton (f : Formula α) {a : α} (h : f.eval {a} = true) :
    a ∈ f.vars := by
  by_contra ha
  have e : f.eval {a} = f.eval ∅ := eval_congr f (by
    intro x hx
    simp only [Finset.mem_singleton, Finset.notMem_empty, iff_false]
    rintro rfl
    exact ha hx)
  rw [e, empty] at h
  contradiction

private theorem pair_mem (f : Formula α) {a b : α} (ha : f.eval {a} = false)
    (hb : f.eval {b} = false) (hab : f.eval {a, b} = true) : a ∈ f.vars ∧ b ∈ f.vars := by
  constructor
  · by_contra h
    rw [drop_left f h, hb] at hab
    contradiction
  · by_contra h
    rw [drop_right f h, ha] at hab
    contradiction

private theorem cross (f g : Formula α) {a b : α} (hd : Disjoint f.vars g.vars)
    (h : (conj f g).eval {a, b} = true) :
    (a ∈ f.vars ∧ b ∈ g.vars ∧ f.eval {a} = true ∧ g.eval {b} = true)
      ∨ (b ∈ f.vars ∧ a ∈ g.vars ∧ f.eval {b} = true ∧ g.eval {a} = true) := by
  rw [eval, Bool.and_eq_true] at h
  have D := Finset.disjoint_left.mp hd
  by_cases haf : a ∈ f.vars
  · have hvg : g.eval {b} = true := (drop_left g (D haf)).symm.trans h.2
    have hbg := mem_of_singleton g hvg
    have hvf : f.eval {a} = true := (drop_right f (fun hbf => D hbf hbg)).symm.trans h.1
    exact Or.inl ⟨haf, hbg, hvf, hvg⟩
  · have hvf : f.eval {b} = true := (drop_left f haf).symm.trans h.1
    have hbf := mem_of_singleton f hvf
    have hvg : g.eval {a} = true := (drop_right g (D hbf)).symm.trans h.2
    exact Or.inr ⟨hbf, mem_of_singleton g hvg, hvf, hvg⟩

/-- Among pairs whose singletons are false, a read-once monotone formula completes every
three-edge path on four vertices. This applies in particular to one-hot bipartite inputs. -/
theorem complete_three_edges (f : Formula α) (hr : f.ReadOnce) {a b c d : α}
    (ha : f.eval {a} = false) (hb : f.eval {b} = false)
    (hc : f.eval {c} = false) (hd : f.eval {d} = false)
    (hac : f.eval {a, c} = true) (had : f.eval {a, d} = true)
    (hbc : f.eval {b, c} = true) : f.eval {b, d} = true := by
  induction f with
  | var x =>
    simp only [eval, Finset.mem_singleton, decide_eq_false_iff_not] at ha hc
    simp [eval, ha, hc] at hac
  | conj f g =>
    obtain ⟨disj, -, -⟩ := hr
    have D := Finset.disjoint_left.mp disj
    rcases cross f g disj hac with left | right
    · have cd := (cross f g disj had).resolve_right (fun h => D left.1 h.2.1)
      have ab := (cross f g disj hbc).resolve_right (fun h => D h.1 left.2.1)
      have eb : f.eval {b, d} = f.eval {b} := drop_right f (fun h => D h cd.2.1)
      have ed : g.eval {b, d} = g.eval {d} := drop_left g (D ab.1)
      simp [eval, eb, ed, ab.2.2.1, cd.2.2.2]
    · have cd := (cross f g disj had).resolve_left (fun h => D h.1 right.2.1)
      have ab := (cross f g disj hbc).resolve_left (fun h => D right.1 h.2.1)
      have ed : f.eval {b, d} = f.eval {d} := drop_left f (fun h => D h ab.2.1)
      have eb : g.eval {b, d} = g.eval {b} := drop_right g (D cd.1)
      simp [eval, ed, eb, cd.2.2.1, ab.2.2.2]
  | disj f g ihf ihg =>
    obtain ⟨disj, hf, hg⟩ := hr
    simp only [eval, Bool.or_eq_false_iff] at ha hb hc hd
    simp only [eval, Bool.or_eq_true] at hac had hbc ⊢
    have D := Finset.disjoint_left.mp disj
    rcases hac with hac | hac
    · obtain ⟨af, cf⟩ := pair_mem f ha.1 hc.1 hac
      have had := had.resolve_right (fun h => D af (pair_mem g ha.2 hd.2 h).1)
      have hbc := hbc.resolve_right (fun h => D cf (pair_mem g hb.2 hc.2 h).2)
      exact Or.inl (ihf hf ha.1 hb.1 hc.1 hd.1 hac had hbc)
    · obtain ⟨ag, cg⟩ := pair_mem g ha.2 hc.2 hac
      have had := had.resolve_left (fun h => D (pair_mem f ha.1 hd.1 h).1 ag)
      have hbc := hbc.resolve_left (fun h => D (pair_mem f hb.1 hc.1 h).2 cg)
      exact Or.inr (ihg hg ha.2 hb.2 hc.2 hd.2 hac had hbc)

end Formula

namespace Formula

variable {α : Type} [DecidableEq α]

def evalWith : Formula α → (α → Bool) → Bool
  | var x, value => value x
  | conj f g, value => f.evalWith value && g.evalWith value
  | disj f g, value => f.evalWith value || g.evalWith value

theorem eval_eq_evalWith (f : Formula α) (s : Finset α) :
    f.eval s = f.evalWith (fun x => decide (x ∈ s)) := by
  induction f <;> simp_all [eval, evalWith]

private theorem evalWith_mono (f : Formula α) {value other : α → Bool}
    (h : ∀ x ∈ f.vars, value x ≤ other x) : f.evalWith value ≤ f.evalWith other := by
  induction f with
  | var x => exact h x (by simp [vars])
  | conj f g ihf ihg | disj f g ihf ihg =>
    have hf := ihf (fun x hx => h x (Finset.mem_union_left _ hx))
    have hg := ihg (fun x hx => h x (Finset.mem_union_right _ hx))
    dsimp only [evalWith]
    first
    | exact Bool.le_and (le_trans (Bool.and_le_left _ _) hf) (le_trans (Bool.and_le_right _ _) hg)
    | exact Bool.or_le (le_trans hf (Bool.left_le_or _ _)) (le_trans hg (Bool.right_le_or _ _))

def substitute (u : α) (replacement : Formula α) : Formula α → Formula α
  | var x => if x = u then replacement else var x
  | conj f g => conj (substitute u replacement f) (substitute u replacement g)
  | disj f g => disj (substitute u replacement f) (substitute u replacement g)

theorem evalWith_substitute (f replacement : Formula α) (u : α) (value : α → Bool) :
    (substitute u replacement f).evalWith value =
      f.evalWith (fun x => if x = u then replacement.evalWith value else value x) := by
  induction f with
  | var x => by_cases h : x = u <;> simp [substitute, evalWith, h]
  | conj f g ihf ihg | disj f g ihf ihg => simp [substitute, evalWith, ihf, ihg]

private theorem evalWith_congr (f : Formula α) {value other : α → Bool}
    (h : ∀ x ∈ f.vars, value x = other x) : f.evalWith value = f.evalWith other := by
  exact le_antisymm (f.evalWith_mono (fun x hx => (h x hx).le))
    (f.evalWith_mono (fun x hx => (h x hx).symm.le))

private theorem mem_vars_substitute (f replacement : Formula α) (u x : α) :
    x ∈ (substitute u replacement f).vars ↔
      (x ∈ f.vars ∧ x ≠ u) ∨ (u ∈ f.vars ∧ x ∈ replacement.vars) := by
  induction f with
  | var y =>
    by_cases h : y = u
    · subst y
      simp [substitute, vars]
    · simp [substitute, vars, h, Ne.symm h]
      exact fun e => e ▸ h
  | conj f g ihf ihg | disj f g ihf ihg =>
    simp only [substitute, vars, Finset.mem_union, ihf, ihg]
    constructor
    · rintro ((⟨h, hn⟩ | ⟨h, hr⟩) | (⟨h, hn⟩ | ⟨h, hr⟩))
      · exact Or.inl ⟨Or.inl h, hn⟩
      · exact Or.inr ⟨Or.inl h, hr⟩
      · exact Or.inl ⟨Or.inr h, hn⟩
      · exact Or.inr ⟨Or.inr h, hr⟩
    · rintro (⟨h | h, hn⟩ | ⟨h | h, hr⟩)
      · exact Or.inl (Or.inl ⟨h, hn⟩)
      · exact Or.inr (Or.inl ⟨h, hn⟩)
      · exact Or.inl (Or.inr ⟨h, hr⟩)
      · exact Or.inr (Or.inr ⟨h, hr⟩)

private theorem readOnce_substitute (f replacement : Formula α) (u : α)
    (hf : f.ReadOnce) (hg : replacement.ReadOnce)
    (fresh : Disjoint (f.vars.erase u) replacement.vars) :
    (substitute u replacement f).ReadOnce := by
  induction f with
  | var x => by_cases h : x = u <;> simp [substitute, ReadOnce, h, hg]
  | conj f g ihf ihg | disj f g ihf ihg =>
    obtain ⟨separate, hf, hrg⟩ := hf
    have sep := Finset.disjoint_left.mp separate
    have fresh' : ∀ z ∈ f.vars ∪ g.vars, z ≠ u → z ∉ replacement.vars :=
      fun _ hz hne => Finset.disjoint_left.mp fresh (Finset.mem_erase.mpr ⟨hne, hz⟩)
    refine ⟨Finset.disjoint_left.mpr ?_, ihf hf ?_, ihg hrg ?_⟩
    · intro z hz₁ hz₂
      rcases (mem_vars_substitute f replacement u z).mp hz₁ with ⟨h₁, hn₁⟩ | ⟨h₁, hr₁⟩ <;>
        rcases (mem_vars_substitute g replacement u z).mp hz₂ with ⟨h₂, hn₂⟩ | ⟨h₂, hr₂⟩
      · exact sep h₁ h₂
      · exact fresh' z (Finset.mem_union_left _ h₁) hn₁ hr₂
      · exact fresh' z (Finset.mem_union_right _ h₂) hn₂ hr₁
      · exact sep h₁ h₂
    · exact Finset.disjoint_left.mpr fun z hz =>
        fresh' z (Finset.mem_union_left _ (Finset.mem_erase.mp hz).2) (Finset.mem_erase.mp hz).1
    · exact Finset.disjoint_left.mpr fun z hz =>
        fresh' z (Finset.mem_union_right _ (Finset.mem_erase.mp hz).2) (Finset.mem_erase.mp hz).1

end Formula

namespace CircuitFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The right summand supplies constants while the gates are being expanded.
abbrev Wire := Nat ⊕ Bool
abbrev Expr := Formula Wire

def values (ws : List Bool) : Wire → Bool
  | .inl i => ws.getD i false
  | .inr b => b

def active (f : Expr) : Finset Wire :=
  f.vars.filter (fun x => x.isLeft)

private def Scoped (bound : Nat) (f : Expr) : Prop :=
  ∀ i, Sum.inl i ∈ f.vars → i < bound

private def operand (bound i : Nat) : Expr :=
  .var (if i < bound then .inl i else .inr false)

private def gateExpr (bound : Nat) (opAnd : Bool) (inputs : List Nat) : Expr :=
  match inputs with
  | [] => .var (.inr opAnd)
  | [i] => operand bound i
  | i :: j :: _ =>
    if opAnd then .conj (operand bound i) (operand bound j)
    else .disj (operand bound i) (operand bound j)

private theorem scoped_operand (bound i : Nat) : Scoped bound (operand bound i) := by
  by_cases h : i < bound <;> simp [Scoped, operand, h, Formula.vars]

private theorem scoped_gateExpr (bound : Nat) (opAnd : Bool) (inputs : List Nat) :
    Scoped bound (gateExpr bound opAnd inputs) := by
  cases inputs with
  | nil => simp [Scoped, gateExpr, Formula.vars]
  | cons i rest =>
    cases rest with
    | nil => exact scoped_operand bound i
    | cons j more =>
      have hi := scoped_operand bound i
      have hj := scoped_operand bound j
      cases opAnd <;> intro k hk <;>
        rcases Finset.mem_union.mp hk with h | h
      all_goals first | exact hi k h | exact hj k h

private theorem gateExpr_active (bound : Nat) (opAnd : Bool) (inputs : List Nat) :
    (active (gateExpr bound opAnd inputs)).card ≤ 2 ∧
    ((active (gateExpr bound opAnd inputs)).card = 2 →
      (gateExpr bound opAnd inputs).ReadOnce ∧
      active (gateExpr bound opAnd inputs) = (gateExpr bound opAnd inputs).vars) := by
  cases inputs with
  | nil => simp [gateExpr, active, Formula.vars, Finset.filter_singleton]
  | cons i rest =>
    cases rest with
    | nil =>
      by_cases hi : i < bound <;>
        simp [gateExpr, operand, active, Formula.vars, Finset.filter_singleton, hi]
    | cons j more =>
      cases opAnd <;> by_cases hi : i < bound <;> by_cases hj : j < bound <;>
        by_cases hij : i = j <;>
        simp [gateExpr, operand, active, Formula.vars, Formula.ReadOnce, hi, hj, hij,
          Finset.filter_singleton, Finset.filter_insert]

private theorem evalWith_operand (ws : List Bool) (i : Nat) :
    (operand ws.length i).evalWith (values ws) = ws.getD i false := by
  by_cases hi : i < ws.length
  · simp [operand, hi, Formula.evalWith, values]
  · simp [operand, hi, Formula.evalWith, values, List.getD_eq_getElem?_getD]

private def IsBinaryMonotone (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

private def isAnd (op : GateOp) : Bool :=
  match op with
  | .and => true
  | _ => false

private theorem evalWith_gateExpr (ws : List Bool) (g : Gate) (h : IsBinaryMonotone g) :
    (gateExpr ws.length (isAnd g.op) g.inputs).evalWith (values ws)
      = g.op.eval (g.inputs.map fun i => ws.getD i false) := by
  rcases g with ⟨op, ins⟩
  obtain ⟨hop, hin⟩ := h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl <;> cases ins with
  | nil => rfl
  | cons i rest =>
    cases rest with
    | nil => simpa [gateExpr, GateOp.eval] using evalWith_operand ws i
    | cons j more =>
      cases more with
      | nil => simp [gateExpr, isAnd, Formula.evalWith, evalWith_operand, GateOp.eval]
      | cons j more => simp at hin

private theorem substitute_gate_scoped (f : Expr) (j : Nat) (g : Gate)
    (h : Scoped (j + 1) f) :
    Scoped j (Formula.substitute (.inl j) (gateExpr j (isAnd g.op) g.inputs) f) := by
  intro i hi
  rcases (Formula.mem_vars_substitute _ _ _ _).mp hi with ⟨hm, hn⟩ | ⟨_, hm⟩
  · have ine : i ≠ j := fun e => hn (congrArg Sum.inl e)
    have ib := h i hm
    omega
  · exact scoped_gateExpr j (isAnd g.op) g.inputs i hm

private theorem substitute_gate_size (f : Expr) (j : Nat) (g : Gate) :
    let G := gateExpr j (isAnd g.op) g.inputs
    let next := Formula.substitute (.inl j) G f
    (active next).card ≤ (active f).card + 1 ∧
      ((active next).card = (active f).card + 1 → f.ReadOnce → active f = f.vars →
        next.ReadOnce ∧ active next = next.vars) := by
  dsimp only
  let w : Wire := .inl j
  let G := gateExpr j (isAnd g.op) g.inputs
  let next := Formula.substitute w G f
  change (active next).card ≤ (active f).card + 1 ∧
    ((active next).card = (active f).card + 1 → f.ReadOnce → active f = f.vars →
      next.ReadOnce ∧ active next = next.vars)
  by_cases h : w ∈ f.vars
  · have hReal : w ∈ active f := Finset.mem_filter.mpr ⟨h, rfl⟩
    have hVars : next.vars = f.vars.erase w ∪ G.vars := by
      ext z
      simp [next, Formula.mem_vars_substitute, h, and_comm]
    have hActive : active next = (active f).erase w ∪ active G := by
      ext z
      simp only [active, hVars, Finset.mem_filter, Finset.mem_union, Finset.mem_erase, or_and_right,
        and_assoc]
    have hErase := Finset.card_erase_of_mem hReal
    have hPositive := Finset.card_pos.mpr ⟨w, hReal⟩
    have hCard := Finset.card_union_add_card_inter ((active f).erase w) (active G)
    have hGate := gateExpr_active j (isAnd g.op) g.inputs
    change (active G).card ≤ 2 ∧
      ((active G).card = 2 → G.ReadOnce ∧ active G = G.vars) at hGate
    constructor
    · rw [hActive]
      omega
    · intro eq hRead hPure
      rw [hActive] at eq
      have hTwo : (active G).card = 2 := by omega
      have disjoint : Disjoint ((active f).erase w) (active G) := by
        apply Finset.disjoint_iff_inter_eq_empty.mpr
        apply Finset.card_eq_zero.mp
        omega
      obtain ⟨hReadG, hPureG⟩ := hGate.2 hTwo
      rw [hPure, hPureG] at disjoint
      refine ⟨Formula.readOnce_substitute f G w hRead hReadG disjoint, ?_⟩
      rw [hActive, hPure, hPureG, hVars]
  · have hActive : active next = active f := by
      ext z
      simp only [active, Finset.mem_filter, next, Formula.mem_vars_substitute, h,
        false_and, or_false]
      exact ⟨fun hz => ⟨hz.1.1, hz.2⟩, fun hz =>
        ⟨⟨hz.1, fun he => h (he ▸ hz.1)⟩, hz.2⟩⟩
    rw [hActive]
    omega

private def gateValue (ws : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => ws.getD i false)

private def run (gs : List Gate) (ws : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [gateValue w g]) ws

private theorem run_length (gs : List Gate) (ws : List Bool) :
    (run gs ws).length = ws.length + gs.length := by
  induction gs generalizing ws with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (ws ++ [gateValue ws g])).length = _
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

private theorem substitute_gate_eval (f : Expr) (ws : List Bool) (g : Gate)
    (h : IsBinaryMonotone g) (valid : Scoped (ws.length + 1) f) :
    (Formula.substitute (.inl ws.length) (gateExpr ws.length (isAnd g.op) g.inputs) f).evalWith
        (values ws) =
      f.evalWith (values (ws ++ [gateValue ws g])) := by
  rw [Formula.evalWith_substitute]
  apply Formula.evalWith_congr
  intro wire hw
  cases wire with
  | inr b => simp [values]
  | inl i =>
    have bound := valid i hw
    by_cases e : i = ws.length
    · subst i
      simp only [ite_true, values]
      rw [evalWith_gateExpr ws g h]
      simp [gateValue, List.getD_eq_getElem?_getD]
    · have ilt : i < ws.length := by omega
      simp [e, values, List.getD_eq_getElem?_getD, List.getElem?_append_left ilt]

private theorem expand (gs : List Gate) (n : Nat)
    (hmono : ∀ g ∈ gs, IsBinaryMonotone g) (seed : Expr) (valid : Scoped (n + gs.length) seed) :
    ∃ f : Expr, Scoped n f ∧
      (∀ xs : List Bool, xs.length = n → f.evalWith (values xs) = seed.evalWith (values (run gs xs))) ∧
      (active f).card ≤ (active seed).card + gs.length ∧
      ((active f).card = (active seed).card + gs.length → seed.ReadOnce → active seed = seed.vars →
        f.ReadOnce ∧ active f = f.vars) := by
  induction gs using List.reverseRecOn generalizing seed with
  | nil => exact ⟨seed, by simpa using valid, by simp [run], by simp, fun _ hR hV => ⟨hR, hV⟩⟩
  | append_singleton prior g ih =>
    let j := n + prior.length
    let next := Formula.substitute (.inl j) (gateExpr j (isAnd g.op) g.inputs) seed
    have validSeed : Scoped (j + 1) seed := by
      simpa [j, Nat.add_assoc] using valid
    have validNext : Scoped (n + prior.length) next := substitute_gate_scoped seed j g validSeed
    have hg : IsBinaryMonotone g := hmono g (by simp)
    have hprior : ∀ g' ∈ prior, IsBinaryMonotone g' := fun g' hm =>
      hmono g' (List.mem_append_left _ hm)
    obtain ⟨f, hscope, heval, hsmall, htight⟩ := ih hprior next validNext
    obtain ⟨spent, tight⟩ := substitute_gate_size seed j g
    change (active next).card ≤ (active seed).card + 1 at spent
    refine ⟨f, hscope, ?_, ?_, ?_⟩
    · intro xs hlen
      rw [heval xs hlen]
      have hlen' : (run prior xs).length = j := by rw [run_length, hlen]
      have h := substitute_gate_eval seed (run prior xs) g hg (by rwa [hlen'])
      rw [hlen'] at h
      exact h.trans (by simp [run, List.foldl_append])
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · intro eq hOnce hPure
      simp only [List.length_append, List.length_cons, List.length_nil] at eq
      have atStep : (active next).card = (active seed).card + 1 := by omega
      have atTail : (active f).card = (active next).card + prior.length := by omega
      obtain ⟨hOnce', hPure'⟩ := tight atStep hOnce hPure
      exact htight atTail hOnce' hPure'

/-- A binary monotone circuit's output agrees with a formula on at most one more distinct
input wire than its gate count. At equality that formula is read-once and constant-free. -/
theorem exists_formula (C : Circuit) (n : Nat) (hmono : Monotone2 C) :
    ∃ f : Expr, (∀ i, Sum.inl i ∈ f.vars → i < n) ∧
      (∀ xs : List Bool, xs.length = n → f.evalWith (values xs) = C.eval xs) ∧
      (active f).card ≤ C.size + 1 ∧
      ((active f).card = C.size + 1 → f.ReadOnce ∧ active f = f.vars) := by
  let bound := n + C.gates.length
  let seed := operand bound C.output
  obtain ⟨f, scope, heval, hsize, htight⟩ :=
    expand C.gates n hmono seed (scoped_operand bound C.output)
  have seedSmall : (active seed).card ≤ 1 := by
    by_cases h : C.output < bound <;>
      simp [seed, operand, active, Formula.vars, Finset.filter_singleton, h]
  refine ⟨f, scope, ?_, ?_, ?_⟩
  · intro xs hlen
    rw [heval xs hlen]
    change seed.evalWith (values (run C.gates xs)) = (run C.gates xs).getD C.output false
    simpa [seed, bound, run_length, hlen] using evalWith_operand (run C.gates xs) C.output
  · unfold Circuit.size
    omega
  · intro eq
    unfold Circuit.size at eq
    have seedOne : (active seed).card = 1 := by omega
    have seedOnce : seed.ReadOnce := by simp [seed, operand, Formula.ReadOnce]
    have pureSeed : active seed = seed.vars := by
      by_cases h : C.output < bound
      · simp [seed, operand, active, Formula.vars, Finset.filter_singleton, h]
      · simp [seed, operand, active, Formula.vars, Finset.filter_singleton, h] at seedOne
    exact htight (by omega) seedOnce pureSeed

/-- An accepted input is componentwise below a rejected input outside wire `i`. A monotone
representation must inspect that wire. The two entries can lie in any promised domain. -/
def ForcesInput (C : Circuit) (n i : Nat) : Prop :=
  ∃ xs ys : List Bool, xs.length = n ∧ ys.length = n ∧ C.eval xs = true ∧ C.eval ys = false ∧
    ∀ j, j ≠ i → xs.getD j false ≤ ys.getD j false

private theorem forced_mem_active (C : Circuit) (n : Nat) (f : Expr)
    (heval : ∀ xs : List Bool, xs.length = n → f.evalWith (values xs) = C.eval xs)
    {i : Nat} (hforce : ForcesInput C n i) : Sum.inl i ∈ active f := by
  obtain ⟨xs, ys, hx, hy, htrue, hfalse, hle⟩ := hforce
  have hm : Sum.inl i ∈ f.vars := by
    by_contra notMem
    have hmono := Formula.evalWith_mono f (value := values xs) (other := values ys) (by
      intro j hj
      cases j with
      | inr b => exact le_rfl
      | inl j =>
        exact hle j (fun eq => notMem (eq ▸ hj)))
    rw [heval xs hx, heval ys hy, htrue, hfalse] at hmono
    simp [Bool.le_iff_imp] at hmono
  exact Finset.mem_filter.mpr ⟨hm, rfl⟩

/-- The support-aware gate lower bound, with extraction of a read-once formula when tight. -/
theorem forced_inputs (C : Circuit) (n : Nat) (hmono : Monotone2 C) (X : Finset Nat)
    (hforce : ∀ i ∈ X, ForcesInput C n i) :
    X.card ≤ C.size + 1 ∧
      (C.size + 1 ≤ X.card →
        ∃ f : Expr, f.ReadOnce ∧ active f = f.vars ∧
          (∀ xs : List Bool, xs.length = n → f.evalWith (values xs) = C.eval xs)) := by
  obtain ⟨f, _, heval, hsize, htight⟩ := exists_formula C n hmono
  let embed : Nat ↪ Wire := ⟨Sum.inl, fun _ _ h => Sum.inl.inj h⟩
  have sub : X.map embed ⊆ active f := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hw
    exact forced_mem_active C n f heval (hforce i hi)
  have leSize : X.card ≤ (active f).card := by
    simpa using Finset.card_le_card sub
  refine ⟨leSize.trans hsize, fun h => ?_⟩
  obtain ⟨readOnce, onlyInputs⟩ := htight (le_antisymm hsize (h.trans leSize))
  exact ⟨f, readOnce, onlyInputs, heval⟩

/-- A constant-free extracted formula can be evaluated just on the set of live input wires. -/
theorem eval_on_support (f : Expr) (onlyInputs : active f = f.vars)
    (xs : List Bool) (s : Finset Wire)
    (h : ∀ i, xs.getD i false = decide (Sum.inl i ∈ s)) :
    f.eval s = f.evalWith (values xs) := by
  rw [Formula.eval_eq_evalWith]
  apply Formula.evalWith_congr
  intro w hw
  cases w with
  | inl i => exact (h i).symm
  | inr b =>
    rw [← onlyInputs] at hw
    simp [active] at hw

end CircuitFrontier

namespace Bipartite

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open CircuitFrontier

variable {n m : Nat}

private def support (u : Fin n) (v : Fin m) : Finset Wire :=
  {Sum.inl u.val, Sum.inl (n + v.val)}

private theorem supported_getD (u : Fin n) (v : Fin m) (i : Nat) :
    (oneEach u v).getD i false = decide (Sum.inl i ∈ support u v) := by
  rw [List.getD_eq_getElem?_getD, oneEach]
  by_cases hi : i < n
  · have hcol : i ≠ n + v.val := by omega
    rw [List.getElem?_append_left (by simpa using hi)]
    simp [hi, support, hcol, Fin.ext_iff]
  · have hrow : i ≠ u.val := by have := u.isLt; omega
    have hle : n ≤ i := Nat.le_of_not_gt hi
    rw [List.getElem?_append_right (by simpa using hle), List.length_ofFn, List.getElem?_ofFn]
    by_cases hj : i - n < m
    · have hshift : i - n = v.val ↔ i = n + v.val := by omega
      simp [hj, support, hrow, Fin.ext_iff, hshift]
    · have hcol : i ≠ n + v.val := by have := v.isLt; omega
      simp [hj, support, hrow, hcol]

/-- A row or column wire is required if changing away from its vertex can
turn an edge into a nonedge while the vertex on the other side stays fixed. -/
def Needed (A : Fin n → Fin m → Bool) (i : Nat) : Prop :=
  (∃ r s c, i = r.val ∧ A r c = true ∧ A s c = false) ∨
  (∃ r c d, i = n + c.val ∧ A r c = true ∧ A r d = false)

private theorem forced {A : Fin n → Fin m → Bool} {C : Circuit} (hC : Represents A C)
    {i : Nat} (hi : Needed A i) : ForcesInput C (n + m) i := by
  rcases hi with ⟨r, s, c, rfl, hp, hn⟩ | ⟨r, c, d, rfl, hp, hn⟩
  · refine ⟨oneEach r c, oneEach s c, by simp [oneEach], by simp [oneEach],
      (hC _ _).trans hp, (hC _ _).trans hn, ?_⟩
    intro j hj
    rw [supported_getD, supported_getD, Bool.le_iff_imp]
    simp only [decide_eq_true_eq, support, Finset.mem_insert, Finset.mem_singleton, Sum.inl.injEq]
    exact fun h => Or.inr (h.resolve_left hj)
  · refine ⟨oneEach r c, oneEach r d, by simp [oneEach], by simp [oneEach],
      (hC _ _).trans hp, (hC _ _).trans hn, ?_⟩
    intro j hj
    rw [supported_getD, supported_getD, Bool.le_iff_imp]
    simp only [decide_eq_true_eq, support, Finset.mem_insert, Finset.mem_singleton, Sum.inl.injEq]
    exact fun h => Or.inl (h.resolve_right hj)

private theorem rejected_singleton (f : Expr) {u : Fin n} {v : Fin m} {w : Wire}
    (hw : w ∈ support u v) (h : f.eval (support u v) = false) : f.eval {w} = false := by
  have le : f.eval {w} ≤ f.eval (support u v) := by
    simp only [Formula.eval_eq_evalWith]
    apply Formula.evalWith_mono
    intro x _
    by_cases hx : x = w
    · subst x
      simp [hw]
    · simp [hx]
  rw [h] at le
  exact Bool.eq_false_of_le_false le

/-- A three-edge path with its fourth edge absent obstructs the gate budget at
which all required wires would have to occur in a read-once formula. -/
theorem not_rep_size_of_path {A : Fin n → Fin m → Bool} {s : Nat} (X : Finset Nat)
    (hX : ∀ i ∈ X, Needed A i) (budget : s + 1 ≤ X.card)
    {a b : Fin n} {c d : Fin m} (hac : A a c = true) (had : A a d = true)
    (hbc : A b c = true) (hbd : A b d = false)
    (rowRejects : ∃ v, A a v = false) (colRejects : ∃ u, A u c = false) :
    ¬ RepSizeAtMost A s := by
  rintro ⟨C, mono, size, rep⟩
  obtain ⟨_, tight⟩ := forced_inputs C (n + m) mono X (fun i hi => forced rep (hX i hi))
  obtain ⟨f, readOnce, pure, evalCircuit⟩ := tight ((Nat.succ_le_succ size).trans budget)
  have evalAt (u : Fin n) (v : Fin m) : f.eval (support u v) = A u v :=
    (eval_on_support f pure _ _ (supported_getD u v)).trans
      ((evalCircuit (oneEach u v) (by simp [oneEach])).trans (rep u v))
  obtain ⟨v, hv⟩ := rowRejects
  obtain ⟨u, hu⟩ := colRejects
  have fa : f.eval {Sum.inl a.val} = false :=
    rejected_singleton f (u := a) (v := v) (by simp [support]) ((evalAt a v).trans hv)
  have fb : f.eval {Sum.inl b.val} = false :=
    rejected_singleton f (u := b) (v := d) (by simp [support]) ((evalAt b d).trans hbd)
  have fc : f.eval {Sum.inl (n + c.val)} = false :=
    rejected_singleton f (u := u) (v := c) (by simp [support]) ((evalAt u c).trans hu)
  have fd : f.eval {Sum.inl (n + d.val)} = false :=
    rejected_singleton f (u := b) (v := d) (by simp [support]) ((evalAt b d).trans hbd)
  have good := Formula.complete_three_edges f readOnce fa fb fc fd
    ((evalAt a c).trans hac) ((evalAt a d).trans had) ((evalAt b c).trans hbc)
  have bad : f.eval {Sum.inl b.val, Sum.inl (n + d.val)} = false := (evalAt b d).trans hbd
  rw [bad] at good
  contradiction

end Bipartite

namespace Mask29683

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open CircuitFrontier

private def adj (u : Fin 3) (v : Fin 6) : Bool :=
  (29683 : ℕ).testBit (6 * u.val + v.val)

private theorem required : ∀ i ∈ Finset.range 9, Bipartite.Needed adj i := by
  have check : ∀ i : Fin 9, Bipartite.Needed adj i.val := by
    simp only [Bipartite.Needed]
    decide +kernel
  intro i hi
  exact check ⟨i, Finset.mem_range.mp hi⟩

/-- The eight-gate upper bound asked for by L-meta-23092 is false. -/
theorem not_rep_size_at_most_eight : ¬ RepSizeAtMost adj 8 :=
  Bipartite.not_rep_size_of_path (Finset.range 9) required (by simp)
    (a := 1) (b := 2) (c := 2) (d := 3)
    (by decide) (by decide) (by decide) (by decide)
    ⟨4, by decide⟩ ⟨0, by decide⟩

private def witness : Circuit :=
  ⟨[⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.and, [0, 10]⟩,
    ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [12, 5]⟩, ⟨GateOp.and, [1, 6]⟩,
    ⟨GateOp.or, [13, 14]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [15, 16]⟩], 17⟩

/-- Nine gates suffice for the same relation in the project's circuit model. -/
theorem rep_size_at_most_nine : RepSizeAtMost adj 9 := by
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end Mask29683

namespace Mask3178496

open PEqualNP.Represents

private def adj (u v : Fin 5) : Bool :=
  (3178496 : ℕ).testBit (5 * u.val + v.val)

private theorem required : ∀ i ∈ ({3, 4, 5, 6} : Finset Nat), Bipartite.Needed adj i := by
  have h : ∀ i : Fin 10, i.val ∈ ({3, 4, 5, 6} : Finset Nat) → Bipartite.Needed adj i.val := by
    simp only [Bipartite.Needed]
    decide +kernel
  intro i hi
  have lt : i < 10 := by simp at hi; omega
  exact h ⟨i, lt⟩ hi

/-- The bound in L-meta-20710 contradicts the path obstruction. -/
theorem not_rep_size_at_most_three : ¬ RepSizeAtMost adj 3 :=
  Bipartite.not_rep_size_of_path {3, 4, 5, 6} required (by decide)
    (a := 4) (b := 3) (c := 0) (d := 1)
    (by decide) (by decide) (by decide) (by decide)
    ⟨2, by decide⟩ ⟨0, by decide⟩

end Mask3178496

namespace Mask391151

open PEqualNP.Represents

private def adj (u : Fin 4) (v : Fin 6) : Bool :=
  (391151 : ℕ).testBit (6 * u.val + v.val)

private def inputs : Finset Nat := (Finset.range 10).erase 3

private theorem required : ∀ i ∈ inputs, Bipartite.Needed adj i := by
  have h : ∀ i : Fin 10, i.val ∈ inputs → Bipartite.Needed adj i.val := by
    simp only [Bipartite.Needed]
    decide +kernel
  intro i hi
  exact h ⟨i, Finset.mem_range.mp (Finset.mem_erase.mp hi).2⟩ hi

/-- Even with one optional row wire, the bound in L-meta-23282 is too small. -/
theorem not_rep_size_at_most_eight : ¬ RepSizeAtMost adj 8 :=
  Bipartite.not_rep_size_of_path inputs required (by decide)
    (a := 0) (b := 1) (c := 1) (d := 5)
    (by decide) (by decide) (by decide) (by decide)
    ⟨4, by decide⟩ ⟨3, by decide⟩

end Mask391151

end PnpResearch
