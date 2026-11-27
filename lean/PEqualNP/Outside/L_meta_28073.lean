import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_28073

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

private def dropPorts (r i : ℕ) : Alias :=
  if i < r then some i else if i = r then none else some (i - 1)

private def dropRow (r m : ℕ) (C : Circuit) : Circuit :=
  rebuild (r + m) (r + 1 + m) C (dropPorts r) []

private theorem dropRow_eval (C : Circuit) (hC : Monotone2 C) (i : Fin r) (j : Fin m) :
    (dropRow r m C).eval (oneEach i j) = C.eval (oneEach i.castSucc j) := by
  rw [oneEach_bits, oneEach_bits]
  apply rebuild_eval (r + m) (r + 1 + m) C hC (dropPorts r) []
  · simp [bits]
  · simp [bits]
  intro a ha
  by_cases left : a < r
  · simp only [dropPorts, left, ite_true, List.length_nil, Nat.add_zero, bound, value,
      run, List.foldl_nil, bits_read, Finset.mem_insert, Finset.mem_singleton, Fin.val_castSucc]
    refine ⟨by omega, decideSame (by omega)⟩
  · by_cases here : a = r
    · subst a
      simp only [dropPorts, Nat.lt_irrefl, ite_false, ite_true, bound, value,
        bits_read, Finset.mem_insert, Finset.mem_singleton, Fin.val_castSucc, true_and]
      have h : ¬ (r < r + 1 + m ∧ (r = i.val ∨ r = r + 1 + j.val)) := by omega
      simp [h]
    · simp only [dropPorts, left, here, ite_false, List.length_nil, Nat.add_zero, bound, value,
        run, List.foldl_nil, bits_read, Finset.mem_insert, Finset.mem_singleton, Fin.val_castSucc]
      refine ⟨by omega, decideSame (by omega)⟩

private def collapseRow (u : Fin r) (i : Fin (r + 1)) : Fin r :=
  if h : i.val < r then ⟨i.val, h⟩ else u

private def growPorts (r m u i : ℕ) : Alias :=
  if i = u then some (r + 1 + m) else if i < r then some i else some (i + 1)

private def growRow (r m : ℕ) (u : Fin r) (C : Circuit) : Circuit :=
  rebuild (r + 1 + m) (r + m) C (growPorts r m u.val) [⟨.or, [u.val, r]⟩]

private theorem growRow_eval (C : Circuit) (hC : Monotone2 C)
    (u : Fin r) (i : Fin (r + 1)) (j : Fin m) :
    (growRow r m u C).eval (oneEach i j) = C.eval (oneEach (collapseRow u i) j) := by
  rw [oneEach_bits, oneEach_bits]
  apply rebuild_eval (r + 1 + m) (r + m) C hC (growPorts r m u.val) [⟨.or, [u.val, r]⟩]
  · simp [bits]
  · simp [bits]
  intro a ha
  have rowCases : (collapseRow u i).val = a ↔
      (i.val = a ∧ i.val < r) ∨ (i.val = r ∧ u.val = a) := by
    by_cases h : i.val < r <;> simp [collapseRow, h] <;> omega
  by_cases hu : a = u.val
  · subst a
    simp only [growPorts, ite_true, List.length_cons, List.length_nil, bound, value]
    refine ⟨by omega, ?_⟩
    change (bits (r + 1 + m) {i.val, r + 1 + j.val} ++
      [GateOp.or.eval [_, _]]).getD (r + 1 + m) false = _
    rw [read_append]
    have lengthBits : (bits (r + 1 + m) {i.val, r + 1 + j.val}).length = r + 1 + m := by
      simp [bits]
    rw [lengthBits, ite_eq_left rfl]
    simp only [GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq,
      bits_read, Finset.mem_insert, Finset.mem_singleton]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    rw [eq_comm (a := u.val) (b := (collapseRow u i).val), rowCases]
    omega
  · by_cases left : a < r
    · simp only [growPorts, hu, left, ite_false, ite_true, List.length_cons, List.length_nil,
        bound, value]
      refine ⟨by omega, ?_⟩
      change (bits (r + 1 + m) {i.val, r + 1 + j.val} ++ [_]).getD a false = _
      rw [read_append]
      have neq : a ≠ (bits (r + 1 + m) {i.val, r + 1 + j.val}).length := by
        simp [bits]; omega
      rw [ite_eq_right neq, bits_read, bits_read]
      apply decideSame
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rw [eq_comm (a := a) (b := (collapseRow u i).val), rowCases]
      omega
    · simp only [growPorts, hu, left, ite_false, List.length_cons, List.length_nil, bound, value]
      refine ⟨by omega, ?_⟩
      change (bits (r + 1 + m) {i.val, r + 1 + j.val} ++ [_]).getD (a + 1) false = _
      rw [read_append]
      have neq : a + 1 ≠ (bits (r + 1 + m) {i.val, r + 1 + j.val}).length := by
        simp [bits]; omega
      rw [ite_eq_right neq, bits_read, bits_read]
      apply decideSame
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega

private def expanded (A : Fin n → Fin m → Bool) (u : Fin n) (t : ℕ)
    (i : Fin (n + t)) (j : Fin m) : Bool :=
  if h : i.val < n then A ⟨i.val, h⟩ j else A u j

private theorem expanded_original (A : Fin n → Fin m → Bool) (u i : Fin n)
    (t : ℕ) (j : Fin m) :
    expanded A u t (i.castLE (Nat.le_add_right n t)) j = A i j := by
  simp [expanded, i.isLt]

private theorem expanded_step (A : Fin n → Fin m → Bool) (u : Fin n)
    (i : Fin (n + t)) (j : Fin m) :
    expanded A u (t + 1) i.castSucc j = expanded A u t i j := rfl

private theorem expanded_end (A : Fin n → Fin m → Bool) (u : Fin n) (t : ℕ)
    (j : Fin m) : expanded A u (t + 1) (Fin.last (n + t)) j = A u j := by
  simp [expanded, show ¬ n + t < n by omega]

private theorem readDup (A : Fin n → Fin m → Bool) (u : Fin n) (t : ℕ)
    (C : Circuit) (hC : Monotone2 C) (hrep : Represents (expanded A u (t + 1)) C)
    (j : Fin m) (i : Fin n) (hu : A u j = true) (hf : A i j = false) :
    ∃ g ∈ C.gates, n + t ∈ g.inputs := by
  let r := n + t
  let col := r + 1 + j.val
  have hyes : C.eval (bits (r + 1 + m) {r, col}) = true := by
    simpa only [oneEach_bits, Fin.val_last, r, col, ← Nat.add_assoc] using
      (hrep (Fin.last r) j).trans ((expanded_end A u t j).trans hu)
  have hno : C.eval (bits (r + 1 + m) {i.val, col}) = false := by
    simpa only [oneEach_bits, Fin.val_castLE, r, col, ← Nat.add_assoc] using
      (hrep (i.castLE (Nat.le_add_right n (t + 1))) j).trans
        ((expanded_original A u i (t + 1) j).trans hf)
  have hother : C.eval (bits (r + 1 + m) {u.val, col}) = true := by
    simpa only [oneEach_bits, Fin.val_castLE, r, col, ← Nat.add_assoc] using
      (hrep (u.castLE (Nat.le_add_right n (t + 1))) j).trans
        ((expanded_original A u u (t + 1) j).trans hu)
  apply reads_of_bits C hC (r + 1 + m) r (by omega) hyes hno hother
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨by dsimp [r]; omega, by dsimp [col]; omega⟩
  · intro x hx
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    exact Or.inr (hx.2.resolve_left hx.1)

private theorem lowerCopies (A : Fin n → Fin m → Bool) (u : Fin n) (t : ℕ) (C : Circuit)
    (hC : Monotone2 C) (hrep : Represents (expanded A u t) C) :
    ∃ D : Circuit, Monotone2 D ∧ Represents A D ∧
      D.size + (if ∃ (j : Fin m) (i : Fin n), A u j = true ∧ A i j = false then t else 0)
        ≤ C.size := by
  induction t generalizing C with
  | zero =>
    refine ⟨C, hC, ?_, by simp⟩
    intro i j
    simpa [expanded, i.isLt] using hrep i j
  | succ t ih =>
    let D := dropRow (n + t) m C
    have hd : Monotone2 D := rebuild_mono _ _ C hC _ [] (by simp)
    have hre : Represents (expanded A u t) D := by
      intro i j
      exact (dropRow_eval C hC i j).trans ((hrep i.castSucc j).trans (expanded_step A u i j))
    obtain ⟨F, hf, hfre, hsize⟩ := ih D hd hre
    refine ⟨F, hf, hfre, ?_⟩
    by_cases paid : ∃ (j : Fin m) (i : Fin n), A u j = true ∧ A i j = false
    · obtain ⟨j, i, ht, hn⟩ := paid
      have read := readDup A u t C hC hrep j i ht hn
      have saved : D.size + 1 ≤ C.size := by
        simpa only [D, dropRow, List.length_nil, Nat.zero_add] using
          (rebuild_saves (n + t + m) (n + t + 1 + m) C (dropPorts (n + t)) []
            (by omega) (by simp [dropPorts]) read)
      have has : ∃ (j : Fin m) (i : Fin n), A u j = true ∧ A i j = false := ⟨j, i, ht, hn⟩
      simp only [has, ite_true] at hsize ⊢
      omega
    · have le : D.size ≤ C.size := by simpa only [D, dropRow, List.length_nil, Nat.zero_add] using
        (rebuild_size (n + t + m) (n + t + 1 + m) C (dropPorts (n + t)) [])
      simp only [paid, ite_false] at hsize ⊢
      exact hsize.trans le

private theorem upperPaid (A : Fin n → Fin m → Bool) (u : Fin n) (t : ℕ) (C : Circuit)
    (hC : Monotone2 C) (hrep : Represents A C) :
    ∃ D : Circuit, Monotone2 D ∧ Represents (expanded A u t) D ∧ D.size ≤ C.size + t := by
  induction t with
  | zero =>
    refine ⟨C, hC, ?_, by simp⟩
    intro i j
    simpa [expanded, i.isLt] using hrep i j
  | succ t ih =>
    obtain ⟨D, hd, hre, hs⟩ := ih
    let r := n + t
    let u' : Fin r := u.castLE (Nat.le_add_right n t)
    let E := growRow r m u' D
    refine ⟨E, ?_, ?_, ?_⟩
    · apply rebuild_mono _ _ D hd
      simp [allowed]
    · intro i j
      rw [growRow_eval D hd]
      by_cases hi : i.val < r
      · let x : Fin r := ⟨i.val, hi⟩
        have eq : i = x.castSucc := Fin.ext rfl
        rw [eq, expanded_step A u x j]
        simpa [collapseRow, x.isLt] using hre x j
      · have eq : i = Fin.last r := Fin.ext (by simp; omega)
        rw [eq, expanded_end A u t j]
        simpa only [collapseRow, Fin.val_last, Nat.lt_irrefl, dite_false, u',
          expanded_original] using hre u' j
    · have le : E.size ≤ [(⟨GateOp.or, [u'.val, r]⟩ : Gate)].length + D.size :=
        rebuild_size _ _ _ _ _
      simp only [List.length_cons, List.length_nil] at le
      omega

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

private theorem clearColumns (A : Fin n → Fin m → Bool) (row : Fin n) (bad rep : Fin m)
    (hbad : A row bad = false) (hrep : ∀ i, A i rep = true)
    (cut : Finset (Fin m)) (good : ∀ j ∈ cut, ∀ i, A i j = true) (hkeep : rep ∉ cut)
    (C : Circuit) (hC : Monotone2 C) (h : Represents A C) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + cut.card ≤ C.size ∧
      ∀ i j, j ∉ cut → D.eval (oneEach i j) = A i j := by
  induction cut using Finset.induction_on with
  | empty => exact ⟨C, hC, by simp, fun i j _ => h i j⟩
  | @insert j cut hj ih =>
    have hrep' : rep ∉ cut := fun hm => hkeep (Finset.mem_insert_of_mem hm)
    obtain ⟨D, hd, hsz, htest⟩ := ih
      (fun l hl => good l (Finset.mem_insert_of_mem hl)) hrep'
    have hb : bad ∉ cut := by
      intro hm
      exact Bool.false_ne_true (hbad.symm.trans (good bad (Finset.mem_insert_of_mem hm) row))
    let x := n + j.val
    have noRep : j ≠ rep := by
      intro e
      subst j
      exact hkeep (Finset.mem_insert_self _ _)
    have hyes := (htest row j hj).trans (good j (Finset.mem_insert_self _ _) row)
    have hno := (htest row bad hb).trans hbad
    have hother := (htest row rep hrep').trans (hrep row)
    rw [oneEach_bits] at hyes hno hother
    have read : ∃ g ∈ D.gates, x ∈ g.inputs := by
      apply reads_of_bits D hd (n + m) x (by dsimp [x]; omega) hyes hno hother
      · have ne : j.val ≠ rep.val := fun e => noRep (Fin.ext e)
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or, x]
        exact ⟨by omega, by omega⟩
      · intro k hk
        simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, x] at hk ⊢
        exact Or.inl (hk.2.resolve_right hk.1)
    let E := clearWire (n + m) x D
    have save : E.size + 1 ≤ D.size := by
      simpa only [E, clearWire, List.length_nil, Nat.zero_add] using
        (rebuild_saves (n + m) (n + m) D (clearPorts x) [] (by dsimp [x]; omega)
          (by simp [clearPorts]) read)
    refine ⟨E, rebuild_mono _ _ D hd _ [] (by simp), ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hj]
      omega
    · intro i l hl
      have ne : j ≠ l := fun eq => hl (eq ▸ Finset.mem_insert_self j cut)
      have valNe : j.val ≠ l.val := fun eq => ne (Fin.ext eq)
      have cutOff : x ∉ ({i.val, n + l.val} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or, x]
        exact ⟨by omega, by omega⟩
      rw [oneEach_bits, clearWire_eval (n + m) x D hd _ cutOff, ← oneEach_bits]
      exact htest i l (fun h => hl (Finset.mem_insert_of_mem h))

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

private def virtual (n u i q j : ℕ) (present : Bool) : Finset ℕ :=
  (if i < n ∧ i ≠ u then {i} else ∅) ∪
    (if present then {u, n + q} else {n + j})

private theorem memVirtual (n u i q j a : ℕ) (present : Bool) :
    a ∈ virtual n u i q j present ↔
      (i < n ∧ i ≠ u ∧ a = i) ∨
      (present = true ∧ (a = u ∨ a = n + q)) ∨
      (present = false ∧ a = n + j) := by
  cases present <;> by_cases h : i < n ∧ i ≠ u <;> simp [virtual, h] <;> tauto

private def freePorts (n u t pivot : ℕ) (universal : Finset ℕ) (bus : Alias) (a : ℕ) : Alias :=
  if a = u then bus else if a < n then some a else
    if a ∈ universal then (if a = pivot then bus else none) else some (a + t)

private theorem freeRebuild (A : Fin n → Fin m → Bool) (u : Fin n) (q : Fin m) (t : ℕ)
    (hmin : ∀ i j, A u j = true → A i j = true)
    (hq : (∃ j, A u j = true) → A u q = true)
    (U : Finset ℕ) (hU : ∀ j : Fin m, n + j.val ∈ U ↔ A u j = true)
    (C : Circuit) (hC : Monotone2 C)
    (hkeep : ∀ i j, A u j = false ∨ j = q → C.eval (oneEach i j) = A i j)
    (pre : List Gate) (hpre : ∀ g ∈ pre, allowed g) (bus : Alias)
    (hbus : bound (n + t + m + pre.length) bus)
    (evalBus : ∀ (i : Fin (n + t)) (j : Fin m), value (run pre (oneEach i j)) bus = A u j) :
    ∃ D : Circuit, Monotone2 D ∧ Represents (expanded A u t) D ∧
      D.size ≤ pre.length + C.size := by
  let V := freePorts n u.val t (n + q.val) U bus
  let D := rebuild (n + t + m) (n + m) C V pre
  refine ⟨D, rebuild_mono _ _ C hC _ _ hpre, ?_, rebuild_size _ _ _ _ _⟩
  intro i j
  let S := virtual n u.val i.val q.val j.val (A u j)
  have rawRead (a : ℕ) (la : a < n + t + m) :
      (run pre (oneEach i j)).getD a false = decide (a = i.val ∨ a = n + t + j.val) := by
    rw [oneEach_bits, run_at_input pre _ a (by simpa [bits] using la), bits_read]
    simp [la]
  have evaluate : D.eval (oneEach i j) = C.eval (bits (n + m) S) := by
    apply rebuild_eval _ _ C hC V pre _ _
    · simp [oneEach]
    · simp [bits]
    intro a la
    have lookup : (bits (n + m) S).getD a false = decide (a ∈ S) := by
      rw [bits_read]
      simp only [la, true_and]
    rw [lookup]
    by_cases isU : a = u.val
    · subst a
      simp only [V, freePorts, ite_true]
      refine ⟨hbus, ?_⟩
      rw [evalBus]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, S, memVirtual]
      cases h : A u j <;> simp [h] <;> omega
    · by_cases left : a < n
      · simp only [V, freePorts, isU, ite_false, left, ite_true, bound, value]
        refine ⟨by omega, ?_⟩
        rw [rawRead a (by omega)]
        apply decideSame
        simp only [S, memVirtual]
        omega
      · let c : Fin m := ⟨a - n, by omega⟩
        have isC : a = n + c.val := by dsimp [c]; omega
        have belongs : a ∈ U ↔ A u c = true := by rw [isC, hU]
        by_cases hc : A u c = true
        · have mem : a ∈ U := belongs.mpr hc
          by_cases isQ : a = n + q.val
          · have port : V a = bus := by
              change freePorts n u.val t (n + q.val) U bus a = bus
              rw [freePorts, ite_eq_right isU, ite_eq_right left, ite_eq_left mem, ite_eq_left isQ]
            rw [port]
            refine ⟨hbus, ?_⟩
            rw [evalBus]
            apply Bool.eq_iff_iff.mpr
            simp only [decide_eq_true_eq, S, memVirtual]
            have noBad : A u j = false → a ≠ n + j.val := by
              intro hf e
              have h : c = j := Fin.ext (by omega)
              have ht : A u j = true := h ▸ hc
              simp [hf] at ht
            constructor
            · intro h
              exact Or.inr (Or.inl ⟨h, Or.inr isQ⟩)
            · rintro (⟨hi, _, e⟩ | ⟨h, _⟩ | ⟨h, e⟩)
              · omega
              · exact h
              · exact (noBad h e).elim
          · simp only [V, freePorts, isU, left, ite_false, mem, ite_true, isQ, bound, value,
              true_and, false_eq_decide_iff]
            simp only [S, memVirtual]
            have noBad : A u j = false → a ≠ n + j.val := by
              intro hf e
              have h : c = j := Fin.ext (by omega)
              have ht : A u j = true := h ▸ hc
              simp [hf] at ht
            cases h : A u j <;> simp [h, noBad] <;> omega
        · have notMem : a ∉ U := fun h => hc (belongs.mp h)
          simp only [V, freePorts, isU, left, ite_false, notMem, bound, value]
          refine ⟨by omega, ?_⟩
          rw [rawRead (a + t) (by omega)]
          apply decideSame
          simp only [S, memVirtual]
          cases h : A u j
          · simp [h]
            omega
          · have nJ : a ≠ n + j.val := by
              intro e
              exact hc ((Fin.ext (show j.val = c.val by omega) : j = c) ▸ h)
            have nQ : a ≠ n + q.val := by
              intro e
              exact hc ((Fin.ext (show q.val = c.val by omega) : q = c) ▸ hq ⟨j, h⟩)
            simp [h, nJ, nQ]
            omega
  rw [evaluate]
  by_cases hj : A u j = true
  · have qTrue := hq ⟨j, hj⟩
    have accepts : C.eval (bits (n + m) {u.val, n + q.val}) = true := by
      rw [← oneEach_bits, hkeep u q (Or.inr rfl), qTrue]
    have le := eval_mono_bits C hC (n + m) (x := {u.val, n + q.val}) (y := S)
      (by
        intro a ha
        apply Finset.mem_union_right
        simpa only [hj, ite_true] using ha)
    have target : expanded A u t i j = true := by
      by_cases hi : i.val < n <;> simp [expanded, hi, hj, hmin _ _ hj]
    rw [target]
    exact (Bool.le_iff_imp.mp le) accepts
  · have jFalse : A u j = false := Bool.eq_false_iff.mpr hj
    by_cases row : i.val < n ∧ i.val ≠ u.val
    · let i' : Fin n := ⟨i.val, row.1⟩
      have setEq : S = {i.val, n + j.val} := by simp [S, virtual, row, jFalse]
      rw [setEq, ← oneEach_bits i' j, hkeep i' j (Or.inl jFalse)]
      simp [expanded, row.1, i']
    · have setEq : S = {n + j.val} := by simp [S, virtual, row, jFalse]
      have rejects : C.eval (bits (n + m) {u.val, n + j.val}) = false := by
        rw [← oneEach_bits, hkeep u j (Or.inl jFalse), jFalse]
      have le := eval_mono_bits C hC (n + m) (x := S) (y := {u.val, n + j.val})
        (by intro a ha; rw [setEq] at ha; exact Finset.mem_insert_of_mem ha)
      have target : expanded A u t i j = false := by
        by_cases hi : i.val < n
        · have eq : (⟨i.val, hi⟩ : Fin n) = u :=
            Fin.ext (by by_contra ne; exact row ⟨hi, ne⟩)
          simp [expanded, hi, eq, jFalse]
        · simp [expanded, hi, jFalse]
      rw [target]
      apply Bool.eq_false_iff.mpr
      intro ht
      exact Bool.false_ne_true (rejects.symm.trans ((Bool.le_iff_imp.mp le) ht))

private theorem readColumn (i : Fin n) (j c : Fin m) :
    (oneEach i j).getD (n + c.val) false = decide (c = j) := by
  rw [oneEach_bits, bits_read]
  apply decideSame
  simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  omega

private theorem upperFree (A : Fin n → Fin m → Bool) (u : Fin n) (t : ℕ)
    (hmin : ∀ i j, A u j = true → A i j = true)
    (neg : ∃ i j, A i j = false) (C : Circuit) (hC : Monotone2 C) (hrep : Represents A C) :
    ∃ D : Circuit, Monotone2 D ∧ Represents (expanded A u t) D ∧ D.size ≤ C.size := by
  obtain ⟨badRow, badCol, hf⟩ := neg
  by_cases nonempty : ∃ q, A u q = true
  · obtain ⟨q, hq⟩ := nonempty
    let universal : Finset (Fin m) := Finset.univ.filter (fun j => A u j = true)
    let cut := universal.erase q
    have memUniversal (j : Fin m) : j ∈ universal ↔ A u j = true := by simp [universal]
    have memCut (j : Fin m) : j ∈ cut ↔ j ≠ q ∧ A u j = true := by simp [cut, memUniversal]
    obtain ⟨F, hF, hsaved, hfits⟩ := clearColumns A badRow badCol q hf
      (fun i => hmin i q hq) cut
      (fun j hj i => hmin i j ((memCut j).mp hj).2)
      (by simp [memCut]) C hC hrep
    let mapWire (j : Fin m) : ℕ := n + t + j.val
    let rest := cut.toList.map mapWire
    let seed := mapWire q
    let G := disjoin (n + t + m) seed rest
    have boundSeed : seed < n + t + m := by dsimp [seed, mapWire]; omega
    have boundRest : ∀ j ∈ rest, j < n + t + m := by
      intro j hj
      obtain ⟨c, _, e⟩ := List.mem_map.mp hj
      subst j
      dsimp [mapWire]
      omega
    have spec (i : Fin (n + t)) (j : Fin m) :=
      disjoin_spec rest (n + t + m) seed (oneEach i j) (by simp [oneEach]) boundSeed boundRest
    have gatesLen : G.gates.length = cut.card := by
      simpa [G, Circuit.size, rest] using (spec (u.castLE (Nat.le_add_right n t)) q).2.1
    have preMono : ∀ g ∈ G.gates, allowed g := (spec (u.castLE (Nat.le_add_right n t)) q).1
    have busBound : bound (n + t + m + G.gates.length) (some G.output) :=
      (spec (u.castLE (Nat.le_add_right n t)) q).2.2.1
    have busEval (i : Fin (n + t)) (j : Fin m) :
        value (run G.gates (oneEach i j)) (some G.output) = A u j := by
      change G.eval (oneEach i j) = A u j
      rw [(spec i j).2.2.2]
      unfold seed
      change ((oneEach i j).getD (n + t + q.val) false ||
        (cut.toList.map mapWire).any (fun k => (oneEach i j).getD k false)) = A u j
      rw [readColumn i j q, List.any_map]
      have hTail : (cut.toList.any fun k => (oneEach i j).getD (mapWire k) false) =
          decide (j ∈ cut) := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_eq_true, Finset.mem_toList, mapWire, readColumn, decide_eq_true_eq]
        constructor
        · rintro ⟨k, hk, rfl⟩
          exact hk
        · exact fun hj => ⟨j, hj, rfl⟩
      change (decide (q = j) ||
        (cut.toList.any fun k => (oneEach i j).getD (mapWire k) false)) = A u j
      rw [hTail]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, decide_eq_true_eq, memCut]
      by_cases isQ : j = q
      · subst j
        simp [hq]
      · have notEq := Ne.symm isQ
        simp [isQ, notEq]
    let ports := universal.image (fun j : Fin m => n + j.val)
    have mports (j : Fin m) : n + j.val ∈ ports ↔ A u j = true := by
      simp only [ports, Finset.mem_image, Nat.add_left_cancel_iff, memUniversal]
      constructor
      · rintro ⟨k, hk, eq⟩
        exact (Fin.ext eq : k = j) ▸ hk
      · exact fun h => ⟨j, h, rfl⟩
    obtain ⟨D, hD, hcorrect, hsize⟩ := freeRebuild A u q t hmin (fun _ => hq) ports mports
      F hF (fun i j hj => hfits i j (by
        intro hm
        obtain ⟨hne, htrue⟩ := (memCut j).mp hm
        rcases hj with hfalse | eq
        · exact Bool.false_ne_true (hfalse.symm.trans htrue)
        · exact hne eq))
      G.gates preMono (some G.output) busBound busEval
    exact ⟨D, hD, hcorrect, hsize.trans (by rw [gatesLen]; omega)⟩
  · have allFalse (j : Fin m) : A u j = false := Bool.eq_false_iff.mpr (fun h => nonempty ⟨j, h⟩)
    obtain ⟨D, hD, hcorrect, hsize⟩ := freeRebuild A u badCol t hmin
      (fun h => (nonempty h).elim) ∅ (fun j => by simp [allFalse]) C hC (fun i j _ => hrep i j)
      [] (by simp) none (by simp [bound]) (fun i j => (allFalse j).symm)
    exact ⟨D, hD, hcorrect, by simpa using hsize⟩

end PEqualNP.Outside.L_meta_28073

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Outside.L_meta_28073

theorem PEqualNP.Outside.L_meta_28073 :
    ∀ (n m : Nat) (A : Fin n → Fin m → Bool) (u : Fin n),
      (∃ i j, A i j = false) →
      ∀ (t s : Nat),
        let expanded := fun (i : Fin (n + t)) (j : Fin m) =>
          if h : i.val < n then A ⟨i.val, h⟩ j else A u j
        let extra := if ∃ (j : Fin m) (i : Fin n), A u j = true ∧ A i j = false
          then t else 0
        PEqualNP.Represents.RepSizeAtMost expanded s ↔
          ∃ b : Nat, PEqualNP.Represents.RepSizeAtMost A b ∧ b + extra ≤ s := by
  intro n m A u neg t s
  change RepSizeAtMost (expanded A u t) s ↔
    ∃ b, RepSizeAtMost A b ∧
      b + (if ∃ (j : Fin m) (i : Fin n), A u j = true ∧ A i j = false then t else 0) ≤ s
  constructor
  · rintro ⟨C, hC, hsize, hrep⟩
    obtain ⟨D, hD, hre, hs⟩ := lowerCopies A u t C hC hrep
    exact ⟨D.size, ⟨D, hD, le_rfl, hre⟩, hs.trans hsize⟩
  · rintro ⟨b, ⟨C, hC, hsize, hrep⟩, bound⟩
    by_cases paid : ∃ (j : Fin m) (i : Fin n), A u j = true ∧ A i j = false
    · obtain ⟨D, hD, hre, hs⟩ := upperPaid A u t C hC hrep
      simp only [paid, ite_true] at bound
      exact ⟨D, hD, by omega, hre⟩
    · have hmin (i : Fin n) (j : Fin m) (h : A u j = true) : A i j = true := by
        cases eq : A i j
        · exact (paid ⟨j, i, h, eq⟩).elim
        · rfl
      obtain ⟨D, hD, hre, hs⟩ := upperFree A u t hmin neg C hC hrep
      simp only [paid, ite_false, Nat.add_zero] at bound
      exact ⟨D, hD, by omega, hre⟩

