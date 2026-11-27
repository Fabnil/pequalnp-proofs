import PEqualNP.Defs.Represents

namespace PnpResearch.DropColumn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) w

private theorem run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).length = _
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

private theorem read_append (w : List α) (a d : α) (i : Nat) :
    (w ++ [a]).getD i d = if i = w.length then a else w.getD i d := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ne_of_lt h]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    by_cases eq : i = w.length
    · simp [eq]
    · have n : w.length < i := by omega
      have nz : i - w.length ≠ 0 := by omega
      cases diff : i - w.length with
      | zero => exact (nz diff).elim
      | succ k =>
        have od : w.getD i d = d := List.getD_eq_default _ _ (by omega)
        simpa [eq, List.getD_eq_getElem?_getD] using od.symm

private def allowed (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

private abbrev Alias := Option Nat

private def value (ws : List Bool) : Alias → Bool
  | none => false
  | some i => ws.getD i false

private def bound (k : Nat) : Alias → Prop
  | none => True
  | some i => i < k

private def simplify (g : Gate) (wire : Nat) (args : List Alias) : Option Gate × Alias :=
  if none ∈ args then
    match g.op with
    | .or => (none, (args.filterMap id).head?)
    | _ => (none, none)
  else
    (some ⟨g.op, args.filterMap id⟩, some wire)

private theorem simplify_skip (g : Gate) (k : Nat) (args : List Alias)
    (hn : none ∈ args) : (simplify g k args).1 = none := by
  cases hop : g.op <;> simp [simplify, hn, hop]

private theorem simplify_allowed (g : Gate) (k : Nat) (args : List Alias)
    (h : allowed g) (len : args.length = g.inputs.length) :
    ∀ q ∈ (simplify g k args).1.toList, allowed q := by
  by_cases hn : none ∈ args
  · simp [simplify_skip g k args hn]
  · intro q hq
    have eq : q = ⟨g.op, args.filterMap id⟩ := by simpa [simplify, hn] using hq
    subst q
    exact ⟨h.1, (List.length_filterMap_le id args).trans (len ▸ h.2)⟩

private theorem simplify_value (g : Gate) (ws : List Bool) (args : List Alias)
    (hg : allowed g) (len : args.length = g.inputs.length)
    (valid : ∀ a ∈ args, bound ws.length a) :
    let out := simplify g ws.length args
    bound (ws.length + out.1.toList.length) out.2 ∧
      value (run out.1.toList ws) out.2 = g.op.eval (args.map (value ws)) := by
  obtain ⟨hop, hlen⟩ := hg
  have hargs : args.length ≤ 2 := len ▸ hlen
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rcases g with ⟨op, inputs⟩
    rcases hop with rfl | rfl <;>
      simp [simplify, run, value, bound, GateOp.eval]
  · rcases g with ⟨op, inputs⟩
    rcases hop with rfl | rfl <;> cases a <;>
      simp [simplify, run, value, bound, GateOp.eval]
  · have ha : bound ws.length a := valid a (by simp)
    have hb : bound ws.length b := valid b (by simp)
    rcases g with ⟨op, inputs⟩
    rcases hop with rfl | rfl <;> cases a <;> cases b <;>
      simp_all [simplify, run, value, bound, GateOp.eval]
  · simp at hargs

private abbrev Build := List Alias × List Gate

private def init (n : Nat) : Build :=
  ((List.range n).map some ++ [none], [])

private def step (n : Nat) (acc : Build) (g : Gate) : Build :=
  let out := simplify g (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i none)
  (acc.1 ++ [out.2], acc.2 ++ out.1.toList)

private def translate (n : Nat) (gs : List Gate) (acc : Build) : Build :=
  gs.foldl (step n) acc

private theorem option_toList_size (q : Option Gate) : q.toList.length ≤ 1 := by
  cases q <;> simp

private theorem step_size (n : Nat) (acc : Build) (g : Gate) :
    (step n acc g).2.length ≤ acc.2.length + 1 := by
  simp only [step, List.length_append]
  exact Nat.add_le_add_left (option_toList_size _) _

private theorem translate_size (n : Nat) (gs : List Gate) (acc : Build) :
    (translate n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [translate]
  | cons g gs ih =>
    change (translate n gs (step n acc g)).2.length ≤ _
    have h := ih (step n acc g)
    have s := step_size n acc g
    simp only [List.length_cons]
    omega

private theorem translate_strict (n : Nat) (gs : List Gate) (acc : Build) (i : Nat)
    (hbound : i < acc.1.length) (hz : acc.1.getD i none = none)
    (hread : ∃ g ∈ gs, i ∈ g.inputs) :
    (translate n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp at hread
  | cons g gs ih =>
    change (translate n gs (step n acc g)).2.length + 1 ≤ _
    simp only [List.length_cons]
    by_cases here : i ∈ g.inputs
    · have hm : none ∈ g.inputs.map (fun i => acc.1.getD i none) :=
        List.mem_map.mpr ⟨i, here, hz⟩
      have skip := simplify_skip g (n + acc.2.length) _ hm
      have sz : (step n acc g).2.length = acc.2.length := by
        simp only [step, skip, Option.toList_none, List.append_nil]
      have tail := translate_size n gs (step n acc g)
      omega
    · have tail : ∃ q ∈ gs, i ∈ q.inputs := by
        obtain ⟨q, hq, hi⟩ := hread
        rcases List.mem_cons.mp hq with rfl | hq
        · exact (here hi).elim
        · exact ⟨q, hq, hi⟩
      have bound' : i < (step n acc g).1.length := by
        simp [step]
        omega
      have hz' : (step n acc g).1.getD i none = none := by
        simp only [step, read_append, ite_eq_right (ne_of_lt hbound), hz]
      have sizeTail := ih (step n acc g) bound' hz' tail
      have sizeHead := step_size n acc g
      omega

private theorem translate_allowed (n : Nat) (gs : List Gate) (acc : Build)
    (old : ∀ g ∈ acc.2, allowed g) (new : ∀ g ∈ gs, allowed g) :
    ∀ g ∈ (translate n gs acc).2, allowed g := by
  induction gs generalizing acc with
  | nil => exact old
  | cons g gs ih =>
    change ∀ q ∈ (translate n gs (step n acc g)).2, allowed q
    apply ih (step n acc g) ?_ (fun q hq => new q (by simp [hq]))
    intro q hq
    simp only [step, List.mem_append] at hq
    rcases hq with hq | hq
    · exact old q hq
    · exact simplify_allowed g _ _ (new g (by simp)) (by simp) q hq

private def Inv (n : Nat) (xs ws : List Bool) (acc : Build) : Prop :=
  acc.1.length = ws.length ∧ ∀ i,
    bound (n + acc.2.length) (acc.1.getD i none) ∧
      value (run acc.2 xs) (acc.1.getD i none) = ws.getD i false

private theorem init_inv (n : Nat) (xs : List Bool) (h : xs.length = n) :
    Inv n xs (xs ++ [false]) (init n) := by
  refine ⟨by simp [init, h], ?_⟩
  intro i
  simp only [init, read_append, List.length_map, List.length_range, List.length_nil,
    Nat.add_zero, h, run, List.foldl_nil]
  by_cases ilt : i < n
  · have notLast : i ≠ n := ne_of_lt ilt
    simp [notLast, List.getD_eq_getElem?_getD, ilt, bound, value]
  · have none : ((List.range n).map some).getD i (none : Alias) = none :=
      List.getD_eq_default _ _ (by simp; omega)
    have z : xs.getD i false = false := List.getD_eq_default _ _ (by omega)
    rw [none, z]
    by_cases e : i = n <;> simp [e, bound, value]

private theorem value_append_tail (w t : List Bool) (a : Alias) (h : bound w.length a) :
    value (w ++ t) a = value w a := by
  cases a with
  | none => rfl
  | some i => simp [value, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem bound_mono {k l : Nat} (h : k ≤ l) (a : Alias) :
    bound k a → bound l a := by
  cases a <;> simp only [bound]
  · exact id
  · exact fun ha => lt_of_lt_of_le ha h

private theorem step_inv (n : Nat) (xs ws : List Bool) (acc : Build) (g : Gate)
    (hx : xs.length = n) (hg : allowed g) (hi : Inv n xs ws acc) :
    Inv n xs (ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) (step n acc g) := by
  obtain ⟨lengths, old⟩ := hi
  let newW := run acc.2 xs
  let args := g.inputs.map fun i => acc.1.getD i none
  let result := simplify g (n + acc.2.length) args
  have lengthW : newW.length = n + acc.2.length := by rw [run_length, hx]
  have valid : ∀ a ∈ args, bound newW.length a := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
    rw [lengthW]
    exact (old i).1
  have same := simplify_value g newW args hg (by simp [args]) valid
  change bound (newW.length + (simplify g newW.length args).1.toList.length)
    (simplify g newW.length args).2 ∧ _ at same
  rw [lengthW] at same
  have vals : args.map (value newW) = g.inputs.map (fun i => ws.getD i false) := by
    simp only [args, List.map_map]
    exact List.map_congr_left (fun i _ => (old i).2)
  have hunfold : step n acc g = (acc.1 ++ [result.2], acc.2 ++ result.1.toList) := rfl
  have extension : ∃ t, run result.1.toList newW = newW ++ t := by
    cases result.1 with
    | none => exact ⟨[], by simp [run]⟩
    | some q => exact ⟨[_], rfl⟩
  obtain ⟨tail, ht⟩ := extension
  rw [hunfold]
  refine ⟨by simp [lengths], ?_⟩
  intro i
  have compose : run (acc.2 ++ result.1.toList) xs = run result.1.toList newW := by
    simp [run, newW, List.foldl_append]
  simp only [List.length_append, read_append, lengths]
  by_cases eq : i = ws.length
  · simp only [eq, ite_true]
    refine ⟨by simpa [result, Nat.add_assoc] using same.1, ?_⟩
    rw [compose]
    exact same.2.trans (congrArg (GateOp.eval g.op) vals)
  · simp only [eq, ite_false]
    refine ⟨bound_mono (by omega) _ (old i).1, ?_⟩
    rw [compose, ht, value_append_tail _ _ _ (by rw [lengthW]; exact (old i).1)]
    exact (old i).2

private theorem translate_inv (n : Nat) (xs ws : List Bool) (gs : List Gate) (acc : Build)
    (hx : xs.length = n) (hg : ∀ g ∈ gs, allowed g) (h : Inv n xs ws acc) :
    Inv n xs (run gs ws) (translate n gs acc) := by
  induction gs generalizing acc ws with
  | nil => exact h
  | cons g gs ih =>
    apply ih _ (step n acc g) (fun q hq => hg q (by simp [hq]))
    exact step_inv n xs ws acc g hx (hg g (by simp)) h

/-- Fix the last input to false. If a gate reads that input, the resulting
function has a monotone circuit with at least one fewer gate. -/
theorem remove_last (n : Nat) (C : Circuit) (hg : Monotone2 C)
    (read : ∃ g ∈ C.gates, n ∈ g.inputs) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + 1 ≤ C.size ∧
      ∀ xs : List Bool, xs.length = n → D.eval xs = C.eval (xs ++ [false]) := by
  let acc := translate n C.gates (init n)
  let output := (acc.1.getD C.output none).getD (n + acc.2.length)
  refine ⟨⟨acc.2, output⟩, ?_, ?_, ?_⟩
  · exact translate_allowed n C.gates (init n) (by simp [init]) hg
  · simpa only [acc, Circuit.size, init, List.length_nil, Nat.zero_add] using
      translate_strict n C.gates (init n) n (by simp [init])
        (by simp only [init, read_append, List.length_map, List.length_range, ite_true]) read
  · intro xs hx
    have out := (translate_inv n xs (xs ++ [false]) C.gates (init n) hx hg
      (init_inv n xs hx)).2 C.output
    change (run acc.2 xs).getD output false = (run C.gates (xs ++ [false])).getD C.output false
    rw [← out.2]
    change (run acc.2 xs).getD ((acc.1.getD C.output none).getD (n + acc.2.length)) false =
      value (run acc.2 xs) (acc.1.getD C.output none)
    cases acc.1.getD C.output none with
    | none =>
      exact List.getD_eq_default _ _ (by simp [run_length, hx])
    | some i => rfl

private theorem gate_le (g : Gate) (hg : allowed g) {x y : Nat → Bool}
    (less : ∀ j ∈ g.inputs, x j ≤ y j) :
    g.op.eval (g.inputs.map x) ≤ g.op.eval (g.inputs.map y) := by
  obtain ⟨op, inputs⟩ := g
  have hop : op = .and ∨ op = .or := by simpa using hg.1
  apply Bool.le_iff_imp.mpr
  intro ht
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq] at ht ⊢
    intro b hb
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
    exact Bool.le_iff_imp.mp (less j hj) (ht _ (List.mem_map.mpr ⟨j, hj, rfl⟩))
  · simp only [GateOp.eval, List.any_eq_true, id_eq] at ht ⊢
    obtain ⟨b, hb, hbt⟩ := ht
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
    exact ⟨y j, List.mem_map.mpr ⟨j, hj, rfl⟩, Bool.le_iff_imp.mp (less j hj) hbt⟩

private theorem run_le_except (i : Nat) (gs : List Gate)
    (hmono : ∀ g ∈ gs, allowed g) (hno : ∀ g ∈ gs, i ∉ g.inputs)
    (x y : List Bool) (hlen : x.length = y.length)
    (less : ∀ j, j ≠ i → x.getD j false ≤ y.getD j false) :
    ∀ j, j ≠ i → (run gs x).getD j false ≤ (run gs y).getD j false := by
  induction gs generalizing x y with
  | nil => exact less
  | cons g gs ih =>
    let a := g.op.eval (g.inputs.map fun j => x.getD j false)
    let b := g.op.eval (g.inputs.map fun j => y.getD j false)
    have hnew : a ≤ b := by
      apply gate_le g (hmono g (by simp))
      intro j hj
      exact less j (fun e => hno g (by simp) (e ▸ hj))
    change ∀ j, j ≠ i → (run gs (x ++ [a])).getD j false ≤ (run gs (y ++ [b])).getD j false
    apply ih (fun q hq => hmono q (by simp [hq])) (fun q hq => hno q (by simp [hq]))
      _ _ (by simp [hlen])
    intro j hj
    rw [read_append, read_append, hlen]
    by_cases eq : j = y.length <;> simp only [eq, ite_true, ite_false]
    · exact hnew
    · exact less j hj

private theorem run_at_input (gs : List Gate) (xs : List Bool) (i : Nat) (bound : i < xs.length) :
    (run gs xs).getD i false = xs.getD i false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    let a := g.op.eval (g.inputs.map fun j => xs.getD j false)
    change (run gs (xs ++ [a])).getD i false = _
    rw [ih (xs ++ [a]) (by simp; omega), read_append, ite_eq_right (ne_of_lt bound)]

/-- If an accepting input is below a rejected input away from coordinate `i`,
then a monotone circuit with a different output wire must read `i` in a gate. -/
theorem gate_reads_of_comparison (C : Circuit) (i : Nat) (hmono : Monotone2 C)
    (out : C.output ≠ i) {x y : List Bool} (hlen : x.length = y.length)
    (hx : C.eval x = true) (hy : C.eval y = false)
    (less : ∀ j, j ≠ i → x.getD j false ≤ y.getD j false) :
    ∃ g ∈ C.gates, i ∈ g.inputs := by
  by_contra h
  have hno : ∀ g ∈ C.gates, i ∉ g.inputs := fun g hg rd => h ⟨g, hg, rd⟩
  have cmp := run_le_except i C.gates hmono hno x y hlen less C.output out
  change C.eval x ≤ C.eval y at cmp
  simp [hx, hy, Bool.le_iff_imp] at cmp

open PEqualNP.Represents

private def table5 (u : Fin 4) (v : Fin 5) : Bool := (104284 : Nat).testBit (5 * u.val + v.val)

private def table4 (u v : Fin 4) : Bool := (13740 : Nat).testBit (4 * u.val + v.val)

private theorem oneEach_restriction :
    ∀ u v : Fin 4, oneEach u (Fin.castSucc v) = oneEach u v ++ [false] ∧
      table5 u (Fin.castSucc v) = table4 u v := by
  decide

private theorem reaches_last (C : Circuit) (hmono : Monotone2 C) (hrep : Represents table5 C) :
    ∃ g ∈ C.gates, 8 ∈ g.inputs := by
  have hout : C.output ≠ 8 := by
    intro eq
    let x := oneEach (0 : Fin 4) (2 : Fin 5)
    have hx : C.eval x = true := (hrep 0 2).trans (by decide)
    change (run C.gates x).getD C.output false = true at hx
    rw [eq, run_at_input C.gates x 8 (by decide)] at hx
    exact (by decide : x.getD 8 false ≠ true) hx
  apply gate_reads_of_comparison C 8 hmono hout
    (x := oneEach (0 : Fin 4) (4 : Fin 5)) (y := oneEach (0 : Fin 4) (0 : Fin 5))
    (by decide) ((hrep 0 4).trans (by decide)) ((hrep 0 0).trans (by decide))
  intro j hne
  by_cases hj : j < 9
  · have cmp : ∀ k : Fin 9, k.val ≠ 8 →
        (oneEach (0 : Fin 4) (4 : Fin 5)).getD k.val false ≤
          (oneEach (0 : Fin 4) (0 : Fin 5)).getD k.val false := by decide
    exact cmp ⟨j, hj⟩ hne
  · have hx : (oneEach (0 : Fin 4) (4 : Fin 5)).length = 9 := by decide
    have hy : (oneEach (0 : Fin 4) (0 : Fin 5)).length = 9 := by decide
    rw [List.getD_eq_default _ _ (by rw [hx]; omega), List.getD_eq_default _ _ (by rw [hy]; omega)]

/-- The four-column restriction of mask 104284 has mask 13740 and saves one gate.
The lower bound for mask 13740 is checked separately by L-meta-8971. -/
theorem not_mask104284
    (hcore : ¬ RepSizeAtMost (fun u v : Fin 4 => (13740 : Nat).testBit (4 * u.val + v.val)) 10) :
    ¬ RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (104284 : Nat).testBit (5 * u.val + v.val)) 11 := by
  rintro ⟨C, hm, hs, hc⟩
  obtain ⟨D, monoD, small, eq⟩ := remove_last 8 C hm (reaches_last C hm hc)
  apply hcore
  refine ⟨D, monoD, by omega, ?_⟩
  intro u v
  obtain ⟨inputs, labels⟩ := oneEach_restriction u v
  have len : (oneEach u v).length = 8 := by simp [oneEach]
  rw [eq (oneEach u v) len, ← inputs]
  exact (hc u (Fin.castSucc v)).trans labels

end PnpResearch.DropColumn
