import PEqualNP.Defs
import PEqualNP.Outside.L_meta_6158

namespace PEqualNP.Outside.L_meta_27804

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/- The circuit transformations below are from the row-duplication proof in PR #41743. -/

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

private theorem gate_reads_of_comparison (C : Circuit) (i : Nat) (hmono : Monotone2 C)
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

private theorem read_ofFn (f : Fin n → α) (i : ℕ) (d : α) :
    (List.ofFn f).getD i d = if h : i < n then f ⟨i, h⟩ else d := by
  by_cases h : i < n <;> simp [List.getD_eq_getElem?_getD, h]

private def bits (n : ℕ) (indices : Finset ℕ) : List Bool :=
  List.ofFn fun i : Fin n => decide (i.val ∈ indices)

private theorem bits_read (n : ℕ) (indices : Finset ℕ) (i : ℕ) :
    (bits n indices).getD i false = decide (i < n ∧ i ∈ indices) := by
  rw [bits, read_ofFn]
  by_cases h : i < n <;> simp [h]

private theorem decideSame {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    decide p = decide q :=
  Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using h)

private theorem oneEach_bits (i : Fin n) (j : Fin m) :
    oneEach i j = bits (n + m) {i.val, n + j.val} := by
  rw [bits, List.ofFn_add]
  unfold oneEach
  congr 1
  · apply congrArg List.ofFn
    funext k
    have h : k.val ≠ n + j.val := by omega
    simp [Fin.ext_iff, h]
  · apply congrArg List.ofFn
    funext k
    have h : n + k.val ≠ i.val := by omega
    simp [Fin.ext_iff, h]

private theorem run_mono (gs : List Gate) (hmono : ∀ g ∈ gs, allowed g)
    (x y : List Bool) (hlen : x.length = y.length)
    (hxy : ∀ i, x.getD i false ≤ y.getD i false) :
    ∀ i, (run gs x).getD i false ≤ (run gs y).getD i false := by
  induction gs generalizing x y with
  | nil => exact hxy
  | cons g gs ih =>
    let a := g.op.eval (g.inputs.map fun j => x.getD j false)
    let b := g.op.eval (g.inputs.map fun j => y.getD j false)
    have hab : a ≤ b := gate_le g (hmono g (by simp)) (fun i _ => hxy i)
    change ∀ i, (run gs (x ++ [a])).getD i false ≤ (run gs (y ++ [b])).getD i false
    apply ih (fun q hq => hmono q (by simp [hq])) _ _ (by simp [hlen])
    intro i
    rw [read_append, read_append, hlen]
    by_cases hi : i = y.length
    · simpa only [hi, ite_true] using hab
    · simpa only [hi, ite_false] using hxy i

private theorem eval_mono_bits (C : Circuit) (hC : Monotone2 C) (n : ℕ)
    {x y : Finset ℕ} (hxy : x ⊆ y) : C.eval (bits n x) ≤ C.eval (bits n y) := by
  apply run_mono C.gates hC _ _ (by simp [bits]) _ C.output
  intro i
  rw [bits_read, bits_read]
  exact Bool.le_iff_imp.mpr (by simpa only [decide_eq_true_eq] using
    (fun h : i < n ∧ i ∈ x => ⟨h.1, hxy h.2⟩ : (i < n ∧ i ∈ x) → i < n ∧ i ∈ y))

private def beginBuild (k : ℕ) (ports : ℕ → Alias) (pre : List Gate) : Build :=
  (List.ofFn fun i : Fin k => ports i.val, pre)

private def rebuild (n k : ℕ) (C : Circuit) (ports : ℕ → Alias) (pre : List Gate) : Circuit :=
  let result := translate n C.gates (beginBuild k ports pre)
  ⟨result.2, (result.1.getD C.output none).getD (n + result.2.length)⟩

private theorem rebuild_mono (n k : ℕ) (C : Circuit) (hC : Monotone2 C)
    (ports : ℕ → Alias) (pre : List Gate) (hp : ∀ g ∈ pre, allowed g) :
    Monotone2 (rebuild n k C ports pre) :=
  translate_allowed n C.gates _ hp hC

private theorem rebuild_size (n k : ℕ) (C : Circuit) (ports : ℕ → Alias) (pre : List Gate) :
    (rebuild n k C ports pre).size ≤ pre.length + C.size :=
  translate_size n C.gates _

private theorem rebuild_saves (n k : ℕ) (C : Circuit) (ports : ℕ → Alias) (pre : List Gate)
    {i : ℕ} (hi : i < k) (hz : ports i = none) (read : ∃ g ∈ C.gates, i ∈ g.inputs) :
    (rebuild n k C ports pre).size + 1 ≤ pre.length + C.size := by
  apply translate_strict n C.gates (beginBuild k ports pre) i _ _ read
  · simpa [beginBuild] using hi
  · simp [beginBuild, hi, hz]

private theorem rebuild_eval (n k : ℕ) (C : Circuit) (hC : Monotone2 C)
    (ports : ℕ → Alias) (pre : List Gate) (xs ys : List Bool)
    (hx : xs.length = n) (hy : ys.length = k)
    (matchPorts : ∀ i < k, bound (n + pre.length) (ports i) ∧
      value (run pre xs) (ports i) = ys.getD i false) :
    (rebuild n k C ports pre).eval xs = C.eval ys := by
  let start := beginBuild k ports pre
  have initial : Inv n xs ys start := by
    refine ⟨by simp [start, beginBuild, hy], ?_⟩
    intro i
    by_cases hi : i < k
    · simpa [start, beginBuild, read_ofFn, hi] using matchPorts i hi
    · have zero : ys.getD i false = false := List.getD_eq_default _ _ (by omega)
      simpa [start, beginBuild, read_ofFn, hi, bound, value] using zero.symm
  let result := translate n C.gates start
  have h := (translate_inv n xs ys C.gates start hx hC initial).2 C.output
  change (run result.2 xs).getD ((result.1.getD C.output none).getD (n + result.2.length)) false =
    (run C.gates ys).getD C.output false
  rw [← h.2]
  cases result.1.getD C.output none with
  | none => exact List.getD_eq_default _ _ (by simp [run_length, hx])
  | some i => rfl

private theorem reads_of_bits (C : Circuit) (hC : Monotone2 C) (n i : ℕ) (hi : i < n)
    {yes no other : Finset ℕ}
    (hy : C.eval (bits n yes) = true) (hn : C.eval (bits n no) = false)
    (ho : C.eval (bits n other) = true) (hout : i ∉ other)
    (hsub : yes.erase i ⊆ no) :
    ∃ g ∈ C.gates, i ∈ g.inputs := by
  have notOutput : C.output ≠ i := by
    intro e
    change (run C.gates (bits n other)).getD C.output false = true at ho
    rw [e, run_at_input C.gates _ i (by simpa [bits] using hi), bits_read] at ho
    simp [hout] at ho
  apply gate_reads_of_comparison C i hC notOutput (by simp [bits]) hy hn
  intro j hj
  rw [bits_read, bits_read]
  apply Bool.le_iff_imp.mpr
  simp only [decide_eq_true_eq]
  exact fun h => ⟨h.1, hsub (Finset.mem_erase.mpr ⟨hj, h.2⟩)⟩
private def clearPorts (j i : ℕ) : Alias := if i = j then none else some i

private def clearWire (n j : ℕ) (C : Circuit) : Circuit :=
  rebuild n n C (clearPorts j) []

private theorem clearWire_eval (n j : ℕ) (C : Circuit) (hC : Monotone2 C)
    (S : Finset ℕ) (hj : j ∉ S) :
    (clearWire n j C).eval (bits n S) = C.eval (bits n S) := by
  apply rebuild_eval n n C hC (clearPorts j) [] _ _ (by simp [bits]) (by simp [bits])
  intro i hi
  by_cases h : i = j
  · subst i
    simp only [clearPorts, ite_true, bound, value, true_and, bits_read]
    simp [hj]
  · simp only [clearPorts, h, ite_false, List.length_nil, Nat.add_zero, bound, value,
      run, List.foldl_nil]
    exact ⟨hi, True.intro⟩

private def disjoin (n seed : ℕ) : List ℕ → Circuit
  | [] => ⟨[], seed⟩
  | i :: rest =>
    let later := disjoin (n + 1) n rest
    ⟨⟨.or, [seed, i]⟩ :: later.gates, later.output⟩

private theorem disjoin_spec (rest : List ℕ) (n seed : ℕ) (xs : List Bool)
    (len : xs.length = n) (hs : seed < n) (hr : ∀ i ∈ rest, i < n) :
    let D := disjoin n seed rest
    Monotone2 D ∧ D.size = rest.length ∧ D.output < n + D.size ∧
      D.eval xs = (xs.getD seed false || rest.any (fun i => xs.getD i false)) := by
  induction rest generalizing n seed xs with
  | nil => exact ⟨by simp [disjoin, Monotone2], rfl, by simpa [disjoin, Circuit.size] using hs,
      by simp [disjoin, Circuit.eval, Circuit.wires]⟩
  | cons i rest ih =>
    let x := xs.getD seed false || xs.getD i false
    let next := disjoin (n + 1) n rest
    have hi : i < n := hr i (by simp)
    have tail : ∀ j ∈ rest, j < n := fun j hj => hr j (by simp [hj])
    obtain ⟨hmono, hsize, hout, he⟩ := ih (n + 1) n (xs ++ [x])
      (by simp [len]) (by omega) (fun j hj => by have := tail j hj; omega)
    change next.output < n + 1 + next.size at hout
    change (∀ g ∈ ⟨GateOp.or, [seed, i]⟩ :: next.gates, allowed g) ∧
      next.size + 1 = rest.length + 1 ∧ next.output < n + (next.size + 1) ∧ _
    refine ⟨?_, congrArg (· + 1) hsize, by omega, ?_⟩
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | h
      · simp [allowed]
      · exact hmono g h
    · have stepEq : (disjoin n seed (i :: rest)).eval xs = next.eval (xs ++ [x]) := by
        simp [Circuit.eval, Circuit.wires, disjoin, next, GateOp.eval, x]
      rw [stepEq]
      rw [he, read_append, len, ite_eq_left rfl]
      have anys : rest.any (fun j => (xs ++ [x]).getD j false) =
          rest.any (fun j => xs.getD j false) := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_eq_true]
        have get (j : ℕ) (hj : j ∈ rest) :
            (xs ++ [x]).getD j false = xs.getD j false := by
          rw [read_append, len, ite_eq_right (ne_of_lt (tail j hj))]
        constructor
        · rintro ⟨j, hj, hv⟩
          exact ⟨j, hj, (get j hj).symm.trans hv⟩
        · rintro ⟨j, hj, hv⟩
          exact ⟨j, hj, (get j hj).trans hv⟩
      rw [anys]
      simp [x, Bool.or_assoc]

private def table (n m : ℕ) (u : Fin n) (v : Fin m) : Bool :=
  (64478 : ℕ).testBit (4 * min u.val 3 + min v.val 3)

private def zeroPadded (u v : Fin 4) : Bool :=
  (854 : ℕ).testBit (4 * u.val + v.val)

private theorem maskCheck : ∀ i j : Fin 4,
    (64478 : ℕ).testBit (4 * i.val + j.val) =
      decide (i.val = 3 ∨ j.val = 3 ∨ i.val ≠ j.val) := by decide +kernel

private theorem table_spec (u : Fin n) (v : Fin m) :
    table n m u v = decide (3 ≤ u.val ∨ 3 ≤ v.val ∨ u.val ≠ v.val) := by
  let i : Fin 4 := ⟨min u.val 3, by omega⟩
  let j : Fin 4 := ⟨min v.val 3, by omega⟩
  change (64478 : ℕ).testBit (4 * i.val + j.val) = _
  rw [maskCheck]
  apply decideSame
  dsimp [i, j]
  omega

private theorem padded_spec : ∀ i j : Fin 4,
    zeroPadded i j = decide (i.val < 3 ∧ j.val < 3 ∧ i.val ≠ j.val) := by decide +kernel

private def extraWires (n m : ℕ) : Finset ℕ :=
  Finset.Ico 3 n ∪ Finset.Ico (n + 3) (n + m)

private theorem extra_mem : i ∈ extraWires n m ↔
    (3 ≤ i ∧ i < n) ∨ (n + 3 ≤ i ∧ i < n + m) := by simp [extraWires]

private theorem extra_count (n m : ℕ) (hn : 3 ≤ n) (hm : 3 ≤ m) :
    (extraWires n m).card + 6 = n + m := by
  have apart : Disjoint (Finset.Ico 3 n) (Finset.Ico (n + 3) (n + m)) := by
    rw [Finset.disjoint_left]
    intro i hl hr
    simp only [Finset.mem_Ico] at hl hr
    omega
  rw [extraWires, Finset.card_union_of_disjoint apart, Nat.card_Ico, Nat.card_Ico]
  omega

private def Agrees (n m : ℕ) (removed : Finset ℕ) (C : Circuit) : Prop :=
  ∀ (u : Fin n) (v : Fin m), u.val ∉ removed → n + v.val ∉ removed →
    C.eval (bits (n + m) {u.val, n + v.val}) = table n m u v

private theorem core_untouched (hn : 4 ≤ n) {removed : Finset ℕ}
    (sub : removed ⊆ extraWires n m) {i : ℕ} (hi : i < 3) :
    i ∉ removed ∧ n + i ∉ removed := by
  constructor <;> intro h <;> have := extra_mem.mp (sub h) <;> omega

private theorem reads_extra (hn : 4 ≤ n) (hm : 4 ≤ m)
    {removed : Finset ℕ} (sub : removed ⊆ extraWires n m)
    (C : Circuit) (mono : Monotone2 C) (ag : Agrees n m removed C)
    {i : ℕ} (hi : i ∈ extraWires n m) (unused : i ∉ removed) :
    ∃ g ∈ C.gates, i ∈ g.inputs := by
  let r0 : Fin n := ⟨0, by omega⟩
  let c0 : Fin m := ⟨0, by omega⟩
  let c1 : Fin m := ⟨1, by omega⟩
  have row0 := (core_untouched hn sub (i := 0) (by decide)).1
  have col0 := (core_untouched hn sub (i := 0) (by decide)).2
  have col1 := (core_untouched hn sub (i := 1) (by decide)).2
  have falseTest : C.eval (bits (n + m) {0, n}) = false := by
    simpa [r0, c0, table_spec] using ag r0 c0 row0 col0
  have trueTest : C.eval (bits (n + m) {0, n + 1}) = true := by
    simpa [r0, c1, table_spec] using ag r0 c1 row0 col1
  have hregion := extra_mem.mp hi
  have bounded : i < n + m := by omega
  have unrelated : i ∉ ({0, n + 1} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  rcases hregion with row | col
  · let u : Fin n := ⟨i, row.2⟩
    have accepted : C.eval (bits (n + m) {i, n}) = true := by
      simpa [u, c0, table_spec, row.1] using ag u c0 unused col0
    refine reads_of_bits C mono _ _ bounded accepted falseTest trueTest unrelated ?_
    intro j hj
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hj ⊢
    omega
  · let v : Fin m := ⟨i - n, by omega⟩
    have renamed : n + v.val = i := by dsimp [v]; omega
    have ge : 3 ≤ v.val := by dsimp [v]; omega
    have accepted : C.eval (bits (n + m) {0, i}) = true := by
      have used := ag r0 v row0 (by rw [renamed]; exact unused)
      rw [renamed, table_spec] at used
      simpa [r0, ge] using used
    refine reads_of_bits C mono _ _ bounded accepted falseTest trueTest unrelated ?_
    intro j hj
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hj ⊢
    omega

private theorem clear_extras (hn : 4 ≤ n) (hm : 4 ≤ m) (C : Circuit)
    (mono : Monotone2 C) (ag : Agrees n m ∅ C) :
    ∀ U ⊆ extraWires n m, ∃ D : Circuit,
      Monotone2 D ∧ D.size + U.card ≤ C.size ∧ Agrees n m U D := by
  intro U
  induction U using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨C, mono, by simp, ag⟩
  | @insert i U absent ih =>
    intro sub
    have hi : i ∈ extraWires n m := sub (Finset.mem_insert_self i U)
    have smaller : U ⊆ extraWires n m := fun _ ha => sub (Finset.mem_insert_of_mem ha)
    obtain ⟨D, dm, budget, agrees⟩ := ih smaller
    have read := reads_extra hn hm smaller D dm agrees hi absent
    have bound : i < n + m := by have := extra_mem.mp hi; omega
    let E := clearWire (n + m) i D
    have save : E.size + 1 ≤ D.size := by
      simpa [E, clearWire] using rebuild_saves (n + m) (n + m) D (clearPorts i) []
        bound (by simp [clearPorts]) read
    refine ⟨E, rebuild_mono _ _ D dm _ [] (by simp), ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem absent]
      omega
    · intro u v hu hv
      have safe : i ∉ ({u.val, n + v.val} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv ⊢
        aesop
      rw [show E = clearWire (n + m) i D from rfl, clearWire_eval _ _ _ dm _ safe]
      exact agrees u v (fun h => hu (Finset.mem_insert_of_mem h))
        (fun h => hv (Finset.mem_insert_of_mem h))

private def cropPorts (n i : ℕ) : Alias :=
  if i < 3 then some i else if n ≤ i ∧ i < n + 3 then some (4 + (i - n)) else none

private def projected (n : ℕ) (u v : Fin 4) : Finset ℕ :=
  (if u.val < 3 then {u.val} else ∅) ∪ (if v.val < 3 then {n + v.val} else ∅)

private theorem projected_mem : i ∈ projected n u v ↔
    (u.val < 3 ∧ i = u.val) ∨ (v.val < 3 ∧ i = n + v.val) := by
  by_cases hu : u.val < 3 <;> by_cases hv : v.val < 3 <;> simp [projected, hu, hv]

private theorem crop_eval (hn : 4 ≤ n) (C : Circuit) (mono : Monotone2 C)
    (u v : Fin 4) :
    (rebuild 8 (n + m) C (cropPorts n) []).eval (oneEach u v) =
      C.eval (bits (n + m) (projected n u v)) := by
  rw [oneEach_bits]
  apply rebuild_eval 8 (n + m) C mono _ [] _ _ (by simp [bits]) (by simp [bits])
  intro i hi
  by_cases row : i < 3
  · simp only [cropPorts, row, ite_true, List.length_nil, Nat.add_zero, bound, value,
      run, List.foldl_nil]
    refine ⟨by omega, ?_⟩
    rw [bits_read, bits_read]
    apply decideSame
    simp only [Finset.mem_insert, Finset.mem_singleton, projected_mem]
    omega
  · by_cases col : n ≤ i ∧ i < n + 3
    · simp only [cropPorts, row, col, true_and, ite_false, ite_true, List.length_nil, Nat.add_zero,
        bound, value, run, List.foldl_nil]
      refine ⟨by omega, ?_⟩
      rw [bits_read, bits_read]
      apply decideSame
      simp only [Finset.mem_insert, Finset.mem_singleton, projected_mem]
      omega
    · simp only [cropPorts, row, col, ite_false, bound, value, true_and]
      rw [bits_read]
      symm
      apply decide_eq_false
      simp only [projected_mem]
      omega

private theorem crop_correct (hn : 4 ≤ n) (hm : 4 ≤ m) (C : Circuit) (mono : Monotone2 C)
    (ag : Agrees n m (extraWires n m) C) :
    Represents zeroPadded (rebuild 8 (n + m) C (cropPorts n) []) := by
  intro u v
  rw [crop_eval hn _ mono, padded_spec]
  by_cases both : u.val < 3 ∧ v.val < 3
  · let u' : Fin n := ⟨u.val, by omega⟩
    let v' : Fin m := ⟨v.val, by omega⟩
    have left := (core_untouched hn (Finset.Subset.refl (extraWires n m)) both.1).1
    have right := (core_untouched hn (Finset.Subset.refl (extraWires n m)) both.2).2
    simpa [projected, both.1, both.2, u', v', table_spec, not_le.mpr both.1, not_le.mpr both.2]
      using ag u' v' left right
  · have pad : ¬(u.val < 3 ∧ v.val < 3 ∧ u.val ≠ v.val) := fun h => both ⟨h.1, h.2.1⟩
    rw [decide_eq_false pad]
    let d := if u.val < 3 then u.val else if v.val < 3 then v.val else 0
    have small : d < 3 := by dsimp [d]; split_ifs <;> omega
    let a : Fin n := ⟨d, by omega⟩
    let b : Fin m := ⟨d, by omega⟩
    have keep := core_untouched hn (Finset.Subset.refl (extraWires n m)) small
    have hf : C.eval (bits (n + m) {d, n + d}) = false := by
      simpa [a, b, table_spec, not_le.mpr small] using ag a b keep.1 keep.2
    have covered : projected n u v ⊆ {d, n + d} := by
      intro i hi
      rw [projected_mem] at hi
      rcases hi with ⟨hu, rfl⟩ | ⟨hv, rfl⟩
      · simp [d, hu]
      · have hu : ¬ u.val < 3 := fun h => both ⟨h, hv⟩
        simp [d, hu, hv]
    cases e : C.eval (bits (n + m) (projected n u v)) with
    | false => rfl
    | true =>
      have wrong := (Bool.le_iff_imp.mp (eval_mono_bits C mono (n + m) covered)) e
      rw [hf] at wrong
      exact Bool.noConfusion wrong

theorem lower (n m : ℕ) (hn : 4 ≤ n) (hm : 4 ≤ m) : ¬ RepSizeAtMost (table n m) (n + m) := by
  rintro ⟨C, mono, size, good⟩
  have agrees : Agrees n m ∅ C := by
    intro u v _ _
    simpa only [oneEach_bits] using good u v
  obtain ⟨D, dm, budget, correct⟩ := clear_extras hn hm C mono agrees
    (extraWires n m) (Finset.Subset.refl _)
  let E := rebuild 8 (n + m) D (cropPorts n) []
  have small := rebuild_size 8 (n + m) D (cropPorts n) []
  have hc := extra_count n m (by omega) (by omega)
  apply PEqualNP.Outside.L_meta_6158.2
  refine ⟨E, rebuild_mono _ _ D dm _ [] (by simp), ?_, crop_correct hn hm D dm correct⟩
  have smaller : E.size ≤ D.size := by simpa [E] using small
  omega

private def liftPorts (n i : ℕ) : Alias :=
  if i < 3 then some i else if 4 ≤ i ∧ i < 7 then some (n + (i - 4)) else none

private def coreCircuit (n m : ℕ) : Circuit :=
  rebuild (n + m) 8 PEqualNP.Outside.L_meta_6158.upperC (liftPorts n) []

private theorem core_rep (hn : 4 ≤ n) (hm : 4 ≤ m) (u : Fin n) (v : Fin m)
    (hu : u.val < 3) (hv : v.val < 3) :
    (coreCircuit n m).eval (bits (n + m) {u.val, n + v.val}) = decide (u.val ≠ v.val) := by
  let i : Fin 4 := ⟨u.val, by omega⟩
  let j : Fin 4 := ⟨v.val, by omega⟩
  have simulates : (coreCircuit n m).eval (bits (n + m) {u.val, n + v.val}) =
      PEqualNP.Outside.L_meta_6158.upperC.eval (oneEach i j) := by
    rw [oneEach_bits]
    apply rebuild_eval (n + m) 8 PEqualNP.Outside.L_meta_6158.upperC
      PEqualNP.Outside.L_meta_6158.upper_mono _ [] _ _ (by simp [bits]) (by simp [bits])
    intro p hp
    by_cases row : p < 3
    · simp only [liftPorts, row, ite_true, List.length_nil, Nat.add_zero, bound, value,
        run, List.foldl_nil]
      refine ⟨by omega, ?_⟩
      rw [bits_read, bits_read]
      apply decideSame
      simp only [Finset.mem_insert, Finset.mem_singleton, i, j]
      omega
    · by_cases col : 4 ≤ p ∧ p < 7
      · simp only [liftPorts, row, col, true_and, ite_false, ite_true, List.length_nil, Nat.add_zero,
          bound, value, run, List.foldl_nil]
        refine ⟨by omega, ?_⟩
        rw [bits_read, bits_read]
        apply decideSame
        simp only [Finset.mem_insert, Finset.mem_singleton, i, j]
        omega
      · simp only [liftPorts, row, col, ite_false, bound, value, true_and]
        rw [bits_read]
        symm
        apply decide_eq_false
        simp only [Finset.mem_insert, Finset.mem_singleton, i, j]
        omega
  have known := PEqualNP.Outside.L_meta_6158.upper_rep i j
  change PEqualNP.Outside.L_meta_6158.upperC.eval (oneEach i j) = zeroPadded i j at known
  rw [simulates, known, padded_spec]
  simp [i, j, hu, hv]

private theorem extra_active (u : Fin n) (v : Fin m) :
    (extraWires n m).toList.any ((bits (n + m) {u.val, n + v.val}).getD · false) =
      decide (3 ≤ u.val ∨ 3 ≤ v.val) := by
  have uBound := u.isLt
  have vBound := v.isLt
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Finset.mem_toList, bits_read, decide_eq_true_eq,
    Finset.mem_insert, Finset.mem_singleton, extra_mem]
  constructor
  · rintro ⟨i, eligible, _, rfl | rfl⟩ <;> omega
  · rintro (hu | hv)
    · exact ⟨u.val, Or.inl ⟨hu, uBound⟩, by omega, Or.inl rfl⟩
    · exact ⟨n + v.val, Or.inr ⟨by omega, by omega⟩, by omega, Or.inr rfl⟩

theorem upper (n m : ℕ) (hn : 4 ≤ n) (hm : 4 ≤ m) : RepSizeAtMost (table n m) (n + m + 1) := by
  let B := coreCircuit n m
  let R := (extraWires n m).toList
  let K := disjoin (n + m + B.size) B.output R
  let C : Circuit := ⟨B.gates ++ K.gates, K.output⟩
  have bm : Monotone2 B := rebuild_mono _ _ _ PEqualNP.Outside.L_meta_6158.upper_mono _ [] (by simp)
  have bs : B.size ≤ 7 := by
    have cost := rebuild_size (n + m) 8 PEqualNP.Outside.L_meta_6158.upperC (liftPorts n) []
    simpa [B, coreCircuit, PEqualNP.Outside.L_meta_6158.upperC, Circuit.size] using cost
  have outputValid : B.output < n + m + B.size := by
    let a : Fin n := ⟨0, by omega⟩
    let b : Fin m := ⟨1, by omega⟩
    have active := core_rep hn hm a b (by change 0 < 3; decide) (by change 1 < 3; decide)
    have truth : B.eval (bits (n + m) {0, n + 1}) = true := by
      simpa [a, b, B] using active
    by_contra! outside
    change (run B.gates (bits (n + m) {0, n + 1})).getD B.output false = true at truth
    rw [List.getD_eq_default _ _ (by simpa [run_length, bits, Circuit.size] using outside)] at truth
    cases truth
  have readRaw : ∀ i ∈ R, i < n + m := by
    intro i h
    have := extra_mem.mp (Finset.mem_toList.mp h)
    omega
  have extend (xs : List Bool) (len : xs.length = n + m) :
      Monotone2 K ∧ K.size = R.length ∧
        C.eval xs = (B.eval xs || R.any (xs.getD · false)) := by
    let w := run B.gates xs
    obtain ⟨km, ks, _, ke⟩ := disjoin_spec R (n + m + B.size) B.output w
      (by simp [run_length, w, len, Circuit.size]) outputValid
      (fun i hi => (readRaw i hi).trans_le (Nat.le_add_right _ _))
    refine ⟨km, ks, ?_⟩
    have rfirst : ∀ i ∈ R, w.getD i false = xs.getD i false :=
      fun i hi => run_at_input B.gates xs i (by rw [len]; exact readRaw i hi)
    have anyeq : R.any (w.getD · false) = R.any (xs.getD · false) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true]
      constructor
      · rintro ⟨i, hi, h⟩
        exact ⟨i, hi, (rfirst i hi).symm.trans h⟩
      · rintro ⟨i, hi, h⟩
        exact ⟨i, hi, (rfirst i hi).trans h⟩
    have fold : C.eval xs = K.eval w := by
      simp only [C, w, Circuit.eval, Circuit.wires, run, List.foldl_append]
    rw [fold, ke, anyeq]
    rfl
  have ⟨km, ks, _⟩ := extend (bits (n + m) ∅) (by simp [bits])
  have card : R.length + 6 = n + m := by
    simpa [R] using extra_count n m (by omega) (by omega)
  refine ⟨C, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with mem | mem
    · exact bm g mem
    · exact km g mem
  · change (B.gates ++ K.gates).length ≤ n + m + 1
    rw [List.length_append]
    change B.size + K.size ≤ n + m + 1
    omega
  · intro u v
    rw [oneEach_bits, (extend _ (by simp [bits])).2.2, table_spec]
    change (B.eval (bits (n + m) {u.val, n + v.val}) ||
      (extraWires n m).toList.any ((bits (n + m) {u.val, n + v.val}).getD · false)) = _
    rw [extra_active]
    by_cases hu : 3 ≤ u.val
    · simp [hu]
    · by_cases hv : 3 ≤ v.val
      · simp [hv]
      · rw [show B = coreCircuit n m from rfl, core_rep hn hm u v (by omega) (by omega)]
        simp [hu, hv]

end PEqualNP.Outside.L_meta_27804

theorem PEqualNP.Outside.L_meta_27804 :
    ∀ (n m : Nat), 4 ≤ n → 4 ≤ m →
    let A := fun (u : Fin n) (v : Fin m) =>
      (64478 : Nat).testBit (4 * min u.val 3 + min v.val 3)
    PEqualNP.Represents.RepSizeAtMost A (n + m + 1) ∧
      ¬ PEqualNP.Represents.RepSizeAtMost A (n + m) := by
  intro n m hn hm
  exact ⟨PEqualNP.Outside.L_meta_27804.upper n m hn hm,
    PEqualNP.Outside.L_meta_27804.lower n m hn hm⟩
