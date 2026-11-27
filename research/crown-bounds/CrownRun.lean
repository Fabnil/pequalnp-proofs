import PEqualNP.Defs
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic.FinCases

/-!
The resource-run construction adapts the mathematical declarations in
PEqualNP/Outside/L_meta_18242.lean at 661aa6ad1563cdaa2ecce4b9124db0eeaaa33885
in open-goat/pequalnp-proofs (Apache-2.0). The Boolean input dimension is a parameter.
The whole file uses the project's gate semantics and the surrounding proof
works with the branch-specific number of uses of every wire.
-/

namespace CrownRun

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def zeroGate (k : Fin 4) (a b : Bool) : Bool :=
  match k.val with
  | 0 => a && b
  | 1 => a || b
  | 2 => a && !b
  | _ => !a && b

section Generic
variable {α : Type} {β : Type}

def UC (G : Fin 4 → α → α → α) (A : Fin 4 → Prop) : ℕ → (α → Prop) → α → Prop
  | 0, S, f => S f
  | t + 1, S, f => UC G A t S f ∨
      ∃ k a b, A k ∧ S a ∧ S b ∧ UC G A t (fun w => w = G k a b ∨ S w) f

theorem UC_monoS (G : Fin 4 → α → α → α) (A : Fin 4 → Prop) :
    ∀ (t : ℕ) (S S' : α → Prop) (f : α), (∀ w, S w → S' w) → UC G A t S f → UC G A t S' f
  | 0, _, _, f, h, hu => h f hu
  | t + 1, S, S', f, h, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (UC_monoS G A t S S' f h hu)
    · exact Or.inr ⟨k, a, b, hk, h a ha, h b hb,
        UC_monoS G A t _ _ f (fun w hw => hw.imp id (h w)) hu⟩

theorem UC_le {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} {t t' : ℕ} {S : α → Prop} {f : α}
    (h : t ≤ t') (hu : UC G A t S f) : UC G A t' S f := by
  induction h with
  | refl => exact hu
  | step _ ih => exact Or.inl ih

theorem UC_gate {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} {t : ℕ} {S : α → Prop} {f : α}
    (k : Fin 4) (a b : α) (hk : A k) (ha : S a) (hb : S b)
    (hu : UC G A t (fun w => w = G k a b ∨ S w) f) : UC G A (t + 1) S f :=
  Or.inr ⟨k, a, b, hk, ha, hb, hu⟩

theorem UC_map {G : Fin 4 → α → α → α} {G' : Fin 4 → β → β → β} {A : Fin 4 → Prop} (e : α → β)
    (he : ∀ k a b, e (G k a b) = G' k (e a) (e b)) :
    ∀ (t : ℕ) (S : α → Prop) (S' : β → Prop) (f : α), (∀ w, S w → S' (e w)) →
      UC G A t S f → UC G' A t S' (e f)
  | 0, _, _, f, h, hu => h f hu
  | t + 1, S, S', f, h, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (UC_map e he t S S' f h hu)
    · refine Or.inr ⟨k, e a, e b, hk, h a ha, h b hb, UC_map e he t _ _ f ?_ hu⟩
      intro w hw
      rcases hw with rfl | hw
      · exact Or.inl (he k a b)
      · exact Or.inr (h w hw)

def TR (G : Fin 4 → α → α → α) (C : Fin 4 → α → α → Prop) (ys : List α) (t : ℕ)
    (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 ys →
    (∀ s xs zs, List.Perm xs zs → P s xs → P s zs) →
    (∀ s a b r (k : Fin 4) (u : ℕ), C k a b →
      P s (List.replicate (u + 1) (G k a b) ++ r) → P (s + 1) (a :: b :: r)) →
    P t ws

section Run
variable {G : Fin 4 → α → α → α} {C : Fin 4 → α → α → Prop} {ys : List α}

theorem TR.done : TR G C ys 0 ys := fun _ d _ _ => d

theorem TR.perm {s : ℕ} {xs zs : List α} (p : List.Perm xs zs) (h : TR G C ys s xs) :
    TR G C ys s zs := fun P d q st => q s xs zs p (h P d q st)

theorem TR.step {s : ℕ} {a b : α} {r : List α} (k : Fin 4) (u : ℕ) (hc : C k a b)
    (h : TR G C ys s (List.replicate (u + 1) (G k a b) ++ r)) :
    TR G C ys (s + 1) (a :: b :: r) := fun P d q st => st s a b r k u hc (h P d q st)

theorem TR.ind {P : ℕ → List α → Prop} {t : ℕ} {ws : List α} (h : TR G C ys t ws)
    (d : P 0 ys)
    (p : ∀ s xs zs, List.Perm xs zs → TR G C ys s xs → P s xs → P s zs)
    (st : ∀ s a b r (k : Fin 4) (u : ℕ), C k a b →
      TR G C ys s (List.replicate (u + 1) (G k a b) ++ r) →
      P s (List.replicate (u + 1) (G k a b) ++ r) → P (s + 1) (a :: b :: r)) : P t ws :=
  (h (fun s xs => TR G C ys s xs ∧ P s xs) ⟨TR.done, d⟩
    (fun s xs zs hp hx => ⟨TR.perm hp hx.1, p s xs zs hp hx.1 hx.2⟩)
    (fun s a b r k u hc hx => ⟨TR.step k u hc hx.1, st s a b r k u hc hx.1 hx.2⟩)).2

theorem TR.inv {t : ℕ} {ws : List α} (h : TR G C ys t ws) :
    (t = 0 → List.Perm ws ys) ∧
    (∀ s, t = s + 1 → ∃ (k : Fin 4) (u : ℕ) (a b : α) (r : List α), C k a b ∧
      List.Perm ws (a :: b :: r) ∧ TR G C ys s (List.replicate (u + 1) (G k a b) ++ r)) := by
  refine TR.ind (P := fun t ws => (t = 0 → List.Perm ws ys) ∧
    (∀ s, t = s + 1 → ∃ (k : Fin 4) (u : ℕ) (a b : α) (r : List α), C k a b ∧
      List.Perm ws (a :: b :: r) ∧ TR G C ys s (List.replicate (u + 1) (G k a b) ++ r))) h
    ⟨fun _ => List.Perm.refl _, fun s hs => by omega⟩ ?_ ?_
  · intro s xs zs hp _ ih
    refine ⟨fun h0 => hp.symm.trans (ih.1 h0), fun s' hs => ?_⟩
    obtain ⟨k, u, a, b, r, hc, hq, hr⟩ := ih.2 s' hs
    exact ⟨k, u, a, b, r, hc, hp.symm.trans hq, hr⟩
  · intro s a b r k u hc hr _
    refine ⟨fun h0 => by omega, fun s' hs => ?_⟩
    have : s = s' := by omega
    subst this
    exact ⟨k, u, a, b, r, hc, List.Perm.refl _, hr⟩

theorem TR.len {t : ℕ} {ws : List α} (h : TR G C ys t ws) : ws.length ≤ t + ys.length := by
  refine TR.ind (P := fun t ws => ws.length ≤ t + ys.length) h (by simp) ?_ ?_
  · intro s xs zs hp _ ih
    rw [← hp.length_eq]; exact ih
  · intro s a b r k u _ _ ih
    simp only [List.length_append, List.length_replicate, List.length_cons] at ih ⊢
    omega

theorem TR.monoC {C' : Fin 4 → α → α → Prop} (hC : ∀ k a b, C k a b → C' k a b) {t : ℕ}
    {ws : List α} (h : TR G C ys t ws) : TR G C' ys t ws :=
  TR.ind (P := fun t ws => TR G C' ys t ws) h TR.done (fun _ _ _ hp _ ih => TR.perm hp ih)
    (fun _ _ _ _ k u hc _ ih => TR.step k u (hC _ _ _ hc) ih)

end Run

def strictC (G : Fin 4 → α → α → α) (z : α) (A : Fin 4 → Prop) (I : α → Prop) :
    Fin 4 → α → α → Prop :=
  fun k a b => A k ∧ I a ∧ I b ∧ a ≠ b ∧ G k a b ≠ a ∧ G k a b ≠ b ∧ G k a b ≠ z

theorem normalize [DecidableEq α] (G : Fin 4 → α → α → α) (z : α) (A : Fin 4 → Prop)
    (I : α → Prop) (hI : ∀ k a b, I a → I b → I (G k a b))
    (hz1 : ∀ k b, G k z b = z ∨ G k z b = b) (hz2 : ∀ k a, G k a z = z ∨ G k a z = a)
    (hd : ∀ k a, G k a a = z ∨ G k a a = a) :
    ∀ (t : ℕ) (S : α → Prop) (f : α), (∀ w, S w → I w) → f ≠ z → UC G A t S f →
      ∃ t', t' ≤ t ∧ ∃ ws : List α, (∀ w ∈ ws, S w ∧ w ≠ z) ∧
        TR G (strictC G z A I) [f] t' ws
  | 0, S, f, _, hf, hu => ⟨0, le_rfl, [f], by simpa using ⟨hu, hf⟩, TR.done⟩
  | t + 1, S, f, hS, hf, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · obtain ⟨t', ht, ws, hws, hr⟩ := normalize G z A I hI hz1 hz2 hd t S f hS hf hu
      exact ⟨t', by omega, ws, hws, hr⟩
    · obtain ⟨t', ht, ws, hws, hr⟩ := normalize G z A I hI hz1 hz2 hd t _ f (by
        rintro w (rfl | hw)
        · exact hI k a b (hS a ha) (hS b hb)
        · exact hS w hw) hf hu
      by_cases hg : S (G k a b)
      · refine ⟨t', by omega, ws, fun w hw => ⟨?_, (hws w hw).2⟩, hr⟩
        rcases (hws w hw).1 with rfl | h
        · exact hg
        · exact h
      by_cases hc : G k a b ∈ ws
      · have hgz : G k a b ≠ z := (hws _ hc).2
        have hga : G k a b ≠ a := fun h => hg (by rw [h]; exact ha)
        have hgb : G k a b ≠ b := fun h => hg (by rw [h]; exact hb)
        have hab : a ≠ b := by
          rintro rfl
          rcases hd k a with h | h
          · exact hgz h
          · exact hga h
        have haz : a ≠ z := by
          rintro rfl
          rcases hz1 k b with h | h
          · exact hgz h
          · exact hgb h
        have hbz : b ≠ z := by
          rintro rfl
          rcases hz2 k a with h | h
          · exact hgz h
          · exact hga h
        obtain ⟨u, hu1⟩ : ∃ u, List.count (G k a b) ws = u + 1 :=
          ⟨List.count (G k a b) ws - 1, by have := List.count_pos_iff.2 hc; omega⟩
        have hperm : ws.Perm (List.replicate (u + 1) (G k a b) ++ ws.filter (· ≠ G k a b)) := by
          rw [← hu1, ← List.filter_eq]
          have := List.filter_append_perm (fun x => decide (x = G k a b)) ws
          refine this.symm.trans ?_
          simp
        refine ⟨t' + 1, by omega, a :: b :: ws.filter (· ≠ G k a b), ?_,
          TR.step k u ⟨hk, hS a ha, hS b hb, hab, hga, hgb, hgz⟩ (TR.perm hperm hr)⟩
        intro w hw
        simp only [List.mem_cons, List.mem_filter, decide_eq_true_eq] at hw
        rcases hw with rfl | rfl | ⟨hw, hne⟩
        · exact ⟨ha, haz⟩
        · exact ⟨hb, hbz⟩
        · rcases (hws w hw).1 with h | h
          · exact absurd h hne
          · exact ⟨h, (hws w hw).2⟩
      · refine ⟨t', by omega, ws, fun w hw => ⟨?_, (hws w hw).2⟩, hr⟩
        rcases (hws w hw).1 with rfl | h
        · exact absurd hw hc
        · exact h

theorem TR.map {G : Fin 4 → α → α → α} {G' : Fin 4 → β → β → β} {C : Fin 4 → α → α → Prop}
    {C' : Fin 4 → β → β → Prop} (e : α → β) (he : ∀ k a b, e (G k a b) = G' k (e a) (e b))
    (hC : ∀ k a b, C k a b → C' k (e a) (e b)) {ys : List α} {t : ℕ} {ws : List α}
    (h : TR G C ys t ws) : TR G' C' (ys.map e) t (ws.map e) := by
  refine TR.ind (P := fun t ws => TR G' C' (ys.map e) t (ws.map e)) h TR.done
    (fun _ _ _ hp _ ih => TR.perm (hp.map e) ih) ?_
  intro s a b r k u hc _ ih
  rw [List.map_append, List.map_replicate, he] at ih
  exact TR.step k u (hC _ _ _ hc) ih

theorem TR.rel {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} (R : α → α → Prop)
    (hR : ∀ k a a' b b', R a a' → R b b' → R (G k a b) (G k a' b')) {ys : List α} {t : ℕ}
    {ws : List α} (h : TR G (fun k _ _ => A k) ys t ws) :
    ∀ ws', List.Forall₂ R ws ws' →
      ∃ ys', List.Forall₂ R ys ys' ∧ TR G (fun k _ _ => A k) ys' t ws' := by
  refine TR.ind (P := fun t ws => ∀ ws', List.Forall₂ R ws ws' →
      ∃ ys', List.Forall₂ R ys ys' ∧ TR G (fun k _ _ => A k) ys' t ws') h
    (fun ws' hw => ⟨ws', hw, TR.done⟩) ?_ ?_
  · intro s xs zs hp _ ih zs' hz
    obtain ⟨xs', hx, hp'⟩ := List.perm_comp_forall₂ hp hz
    obtain ⟨ys', hy, hr⟩ := ih xs' hx
    exact ⟨ys', hy, TR.perm hp' hr⟩
  · intro s a b r k u hc _ ih ws' hw
    obtain ⟨a', t1, ha, ht1, rfl⟩ := List.forall₂_cons_left_iff.1 hw
    obtain ⟨b', r', hb, hr', rfl⟩ := List.forall₂_cons_left_iff.1 ht1
    have h1 : List.Forall₂ R (List.replicate (u + 1) (G k a b) ++ r)
        (List.replicate (u + 1) (G k a' b') ++ r') := by
      refine List.rel_append ?_ hr'
      generalize u + 1 = n
      induction n with
      | zero => exact List.Forall₂.nil
      | succ n ih => exact List.Forall₂.cons (hR k a a' b b' ha hb) ih
    obtain ⟨ys', hy, hrun⟩ := ih _ h1
    exact ⟨ys', hy, TR.step k u hc hrun⟩

end Generic

abbrev BF (n : ℕ) := (Fin n → Bool) → Bool

variable {n : ℕ}

def gF (k : Fin 4) (a b : (BF n)) : (BF n) := fun x => zeroGate k (a x) (b x)

def var (i : Fin n) : (BF n) := fun x => x i

def zF : (BF n) := fun _ => false

def rst (p : Fin n) (a : (BF n)) : (BF n) := fun x => a (Function.update x p false)

theorem gF_zero_left (k : Fin 4) (b : (BF n)) : gF k zF b = zF ∨ gF k zF b = b := by
  fin_cases k
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_zero_right (k : Fin 4) (a : (BF n)) : gF k a zF = zF ∨ gF k a zF = a := by
  fin_cases k
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_self (k : Fin 4) (a : (BF n)) : gF k a a = zF ∨ gF k a a = a := by
  fin_cases k
  · exact Or.inr (funext fun x => by simp [gF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_zero_zero (k : Fin 4) : gF (n := n) k zF zF = zF := by
  fin_cases k <;> exact funext fun x => by simp [gF, zF, zeroGate]

def MonoA : Fin 4 → Prop := fun k => k.val < 2

abbrev MR (ys : List (BF n)) (s : ℕ) (ws : List (BF n)) : Prop := TR gF (fun k _ _ => MonoA k) ys s ws

def outF (ys : List (BF n)) : (BF n) := fun x => ys.any fun y => y x

def otop (x : Fin n) : (BF n) := fun p => decide (∃ i, i ≠ x ∧ p i = true)

theorem mono_cases (k : Fin 4) (hk : MonoA k) : k = 0 ∨ k = 1 := by
  fin_cases k <;> simp_all [MonoA]

theorem gF_and (a b : (BF n)) : gF 0 a b = fun p => a p && b p := rfl

theorem gF_or (a b : (BF n)) : gF 1 a b = fun p => a p || b p := rfl

theorem UC_monoA {α : Type} {G : Fin 4 → α → α → α} {A A' : Fin 4 → Prop}
    (hA : ∀ k, A k → A' k) :
    ∀ (t : ℕ) (S : α → Prop) (f : α), UC G A t S f → UC G A' t S f
  | 0, _, _, hu => hu
  | t + 1, S, f, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (UC_monoA hA t S f hu)
    · exact Or.inr ⟨k, a, b, hA k hk, ha, hb, UC_monoA hA t _ f hu⟩

theorem vars_list : ∀ (ws : List (BF n)), (∀ w ∈ ws, ∃ i, w = var i) →
    ∃ idx : List (Fin n), ws = idx.map var
  | [], _ => ⟨[], rfl⟩
  | w :: ws, h => by
    obtain ⟨i, rfl⟩ := h w (by simp)
    obtain ⟨idx, rfl⟩ := vars_list ws fun w hw => h w (by simp [hw])
    exact ⟨i :: idx, rfl⟩

def gv (g : Gate) (W : List (BF n)) : (BF n) :=
  fun x => g.op.eval (g.inputs.map fun i => (W.getD i zF) x)

def wiresF : List Gate → List (BF n) → List (BF n)
  | [], W => W
  | g :: gs, W => wiresF gs (W ++ [gv g W])

theorem getD_map_x (W : List (BF n)) (i : ℕ) (x : Fin n → Bool) :
    (W.map fun w => w x).getD i false = (W.getD i zF) x := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases W[i]? <;> rfl

theorem wires_eq (x : Fin n → Bool) : ∀ (gs : List Gate) (W : List (BF n)),
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (W.map fun w => w x) = (wiresF gs W).map fun w => w x
  | [], W => rfl
  | g :: gs, W => by
    simp only [List.foldl_cons, wiresF]
    rw [← wires_eq x gs (W ++ [gv g W])]
    congr 1
    simp only [List.map_append, List.map_cons, List.map_nil, gv, getD_map_x]

theorem getD_mem (W : List (BF n)) (i : ℕ) : W.getD i zF ∈ W ∨ W.getD i zF = zF := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : W[i]? with _ | a
  · exact Or.inr rfl
  · exact Or.inl (List.mem_of_getElem? h)

def oneF : (BF n) := fun _ => true
def Ready (S : (BF n) → Prop) (w : (BF n)) := w=zF ∨ w=oneF ∨ S w

theorem monoForm (g : Gate) (W : List (BF n)) (op : g.op = GateOp.and ∨ g.op = GateOp.or)
    (arity : g.inputs.length≤2) (S : (BF n) → Prop) (available : ∀ w∈W, Ready S w) :
    Ready S (gv g W) ∨ ∃ k a b, MonoA k ∧ S a ∧ S b ∧ gv g W=gF k a b := by
  have get (i : ℕ) : Ready S (W.getD i zF) :=
    (getD_mem W i).elim (available _) Or.inl
  have binary (k : Fin 4) (hk : MonoA k) (a b : (BF n)) (h : gv g W=gF k a b)
      (ha : Ready S a) (hb : Ready S b) :
      Ready S (gv g W) ∨ ∃ k a b, MonoA k ∧ S a ∧ S b ∧ gv g W=gF k a b := by
    rcases mono_cases k hk with rfl|rfl <;> rw [h]
    · rcases ha with rfl|rfl|aS
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl hb
      · rcases hb with rfl|rfl|bS
        · exact Or.inl (Or.inl (funext fun x => Bool.and_false _))
        · exact Or.inl (Or.inr (Or.inr (by simpa [gF_and,oneF] using aS)))
        · exact Or.inr ⟨0,a,b,hk,aS,bS,rfl⟩
    · rcases ha with rfl|rfl|aS
      · exact Or.inl hb
      · exact Or.inl (Or.inr (Or.inl rfl))
      · rcases hb with rfl|rfl|bS
        · exact Or.inl (Or.inr (Or.inr (by simpa [gF_or,zF] using aS)))
        · exact Or.inl (Or.inr (Or.inl (funext fun x => Bool.or_true _)))
        · exact Or.inr ⟨1,a,b,hk,aS,bS,rfl⟩
  rcases g with ⟨operation,ins⟩
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨l, rest⟩⟩⟩
  · rcases op with rfl|rfl
    · exact Or.inl (Or.inr (Or.inl rfl))
    · exact Or.inl (Or.inl rfl)
  · rcases op with rfl|rfl <;> apply Or.inl <;> convert get i using 1 <;> funext x <;> simp [gv,GateOp.eval]
  · rcases op with rfl|rfl
    · exact binary 0 (by simp [MonoA] : MonoA 0) _ _ (by funext x; simp [gv,GateOp.eval,gF_and]) (get i) (get j)
    · exact binary 1 (by simp [MonoA] : MonoA 1) _ _ (by funext x; simp [gv,GateOp.eval,gF_or]) (get i) (get j)
  · simp at arity

theorem circuitRun (gs : List Gate) (o : ℕ) (mono : ∀ g∈gs,
    (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) (S : (BF n) → Prop)
    (W : List (BF n)) (stored : ∀ w∈W, Ready S w) :
    Ready (UC gF MonoA gs.length S) ((wiresF gs W).getD o zF) := by
  induction gs generalizing S W with
  | nil => exact (getD_mem W o).elim (stored _) Or.inl
  | cons g gs ih =>
    have tail := fun f (hf : f∈gs) => mono f (List.mem_cons_of_mem _ hf)
    obtain ⟨op,arity⟩ := mono g (by simp)
    rcases monoForm g W op arity S stored with free|⟨k,a,b,hk,ha,hb,eq⟩
    · have prev := ih tail S (W++[gv g W]) (by
        intro w hw
        rcases List.mem_append.mp hw with left|right
        · exact stored _ left
        · simpa using (List.mem_singleton.mp right ▸ free : Ready S w))
      rcases prev with h|h|h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (UC_le (by simp) h))
    · let A (w : (BF n)) := w=gF k a b ∨ S w
      have prev := ih tail A (W++[gv g W]) (by
        intro w hw
        rcases List.mem_append.mp hw with left|right
        · exact (stored w left).imp id (fun q => q.imp id Or.inr)
        · obtain rfl := List.mem_singleton.mp right
          exact Or.inr (Or.inr (Or.inl eq)))
      rcases prev with h|h|h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (UC_gate k a b hk ha hb h))

/-- Extract a run with explicit wire multiplicities from a monotone circuit. -/
theorem fromCircuit {C : Circuit} (mono : Monotone2 C) (F : BF n)
    (acts : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = F x)
    (nonzero : F ≠ zF) (nonone : F ≠ oneF) :
    ∃ t, t ≤ C.size ∧ ∃ idx : List (Fin n), MR [F] t (idx.map var) := by
  classical
  have same : (wiresF C.gates (List.ofFn var)).getD C.output zF = F := by
    funext x
    rw [← acts x, ← getD_map_x, ← wires_eq]
    simp only [Circuit.eval, Circuit.wires, List.map_ofFn]
    rfl
  have h := circuitRun (n := n) C.gates C.output mono (fun w => ∃ i, w = var i) (List.ofFn var) (by
    intro w hw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
    exact Or.inr (Or.inr ⟨i, rfl⟩))
  rw [same] at h
  rcases h with z | u | real
  · exact False.elim (nonzero z)
  · exact False.elim (nonone u)
  · obtain ⟨t, ht, ws, avail, run⟩ :=
      normalize gF zF MonoA (fun _ => True) (fun _ _ _ _ _ => trivial)
        gF_zero_left gF_zero_right gF_self C.size _ F (fun _ _ => trivial) nonzero real
    obtain ⟨idx, rfl⟩ := vars_list ws fun w hw => (avail w hw).1
    exact ⟨t, ht, idx, TR.monoC (fun _ _ _ h => h.1) run⟩

end CrownRun
