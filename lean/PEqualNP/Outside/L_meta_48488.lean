import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48488

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def fullMask : Nat := 0xffffffffffffffff

abbrev Masked (mask w : Nat) : Prop := w &&& mask = w

def bsel {α : Type} (c : Bool) (t f : α) : α := Bool.rec f t c

theorem bsel_true {α : Type} (t f : α) : bsel true t f = t := rfl
theorem bsel_false {α : Type} (t f : α) : bsel false t f = f := rfl

theorem beq_false_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem ne_of_beq_false {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := by
  intro e; subst e; rw [Nat.beq_refl] at h; exact Bool.noConfusion h

theorem masked_self (mask : Nat) : Masked mask mask := by
  unfold Masked; simp

theorem masked_land_right (mask w : Nat) : Masked mask (w &&& mask) := by
  unfold Masked; apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and]

theorem xor_cancel_left (mask v : Nat) : mask ^^^ (mask ^^^ v) = v := by
  apply Nat.eq_of_testBit_eq; intro i; simp

theorem masked_sub_and {mask cut w : Nat} (sub : mask &&& cut = cut) :
    (w &&& mask) &&& cut = w &&& cut := by
  apply Nat.eq_of_testBit_eq; intro i
  have es := congrArg (fun x => x.testBit i) sub
  simp only [Nat.testBit_and] at es ⊢
  cases hc : cut.testBit i <;> simp_all

theorem masked_sub_xor {mask cut w : Nat} (sub : mask &&& cut = cut) :
    (mask ^^^ w) &&& cut = cut ^^^ (w &&& cut) := by
  apply Nat.eq_of_testBit_eq; intro i
  have es := congrArg (fun x => x.testBit i) sub
  simp only [Nat.testBit_and, Nat.testBit_xor] at es ⊢
  cases hc : cut.testBit i <;> simp_all

def canon (mask w : Nat) : Nat :=
  let v := w &&& mask
  bsel (Nat.beq v 0 || Nat.beq v mask) 0
    (let iv := mask ^^^ v; bsel (Nat.blt v iv) v iv)

theorem canon_zero (mask : Nat) : canon mask 0 = 0 := by
  unfold canon; simp [bsel]

theorem canon_self (mask : Nat) : canon mask mask = 0 := by
  unfold canon; simp [bsel]

theorem canon_land (mask w : Nat) : canon mask (w &&& mask) = canon mask w := by
  unfold canon; dsimp only; rw [masked_land_right mask w]

theorem canon_cases (mask w : Nat) :
    (canon mask w = 0 ∧ (w &&& mask = 0 ∨ w &&& mask = mask)) ∨
    (canon mask w ≠ 0 ∧ (canon mask w = w &&& mask ∨ canon mask w = mask ^^^ (w &&& mask))) := by
  unfold canon; dsimp only
  set v := w &&& mask
  by_cases hv0 : v = 0
  · left; rw [hv0]; simp [bsel]
  · by_cases hvm : v = mask
    · left; rw [hvm]; simp [bsel]
    · right
      rw [beq_false_ne hv0, beq_false_ne hvm]
      simp only [Bool.or_false, bsel_false]
      cases hlt : Nat.blt v (mask ^^^ v)
      · rw [bsel_false]
        refine ⟨?_, Or.inr rfl⟩
        intro hz
        have e := congrArg (fun x => mask ^^^ x) hz
        rw [xor_cancel_left] at e
        exact hvm (by simpa using e)
      · rw [bsel_true]; exact ⟨hv0, Or.inl rfl⟩

theorem canon_xor_mask (mask w : Nat) : canon mask (mask ^^^ w) = canon mask w := by
  have hsub : (mask ^^^ w) &&& mask = mask ^^^ (w &&& mask) := masked_sub_xor (masked_self mask)
  unfold canon; dsimp only
  rw [hsub]
  generalize hv : w &&& mask = v
  set iv := mask ^^^ v
  have hiv : mask ^^^ iv = v := xor_cancel_left mask v
  rw [hiv]
  by_cases hv0 : v = 0
  · have hivm : iv = mask := by simp [iv, hv0]
    rw [hv0, hivm]; simp [bsel]
  · by_cases hvm : v = mask
    · have hiv0 : iv = 0 := by simp [iv, hvm]
      rw [hvm, hiv0]; simp [bsel]
    · have hiv0 : iv ≠ 0 := by
        intro h; apply hvm
        have e := congrArg (fun x => mask ^^^ x) h
        rw [hiv] at e; simpa using e
      have hivm : iv ≠ mask := by
        intro h; apply hv0
        have e := congrArg (fun x => mask ^^^ x) h
        rw [hiv] at e; simpa using e
      rw [beq_false_ne hv0, beq_false_ne hvm, beq_false_ne hiv0, beq_false_ne hivm]
      simp only [Bool.or_false, bsel_false]
      have hne : v ≠ iv := by
        intro h
        have hm0 : mask = 0 := by
          apply Nat.eq_of_testBit_eq; intro i
          have ei := congrArg (fun x => x.testBit i) h
          simp only [iv, Nat.testBit_xor] at ei
          cases hv' : v.testBit i <;> cases hm' : mask.testBit i <;> simp_all
        have : v = 0 := by rw [← hv, hm0]; simp
        exact hv0 this
      by_cases hlt : v < iv
      · have h1 : Nat.blt v iv = true := Nat.blt_eq.mpr hlt
        have h2 : Nat.blt iv v = false := by cases h : Nat.blt iv v; rfl; have := Nat.blt_eq.mp h; omega
        rw [h1, h2, bsel_true, bsel_false]
      · have hgt : iv < v := by omega
        have h1 : Nat.blt v iv = false := by cases h : Nat.blt v iv; rfl; have := Nat.blt_eq.mp h; omega
        have h2 : Nat.blt iv v = true := Nat.blt_eq.mpr hgt
        rw [h1, h2, bsel_false, bsel_true]

theorem canon_idem (mask w : Nat) : canon mask (canon mask w) = canon mask w := by
  rcases canon_cases mask w with ⟨h0, _⟩ | ⟨_, h1 | h2⟩
  · rw [h0, canon_zero]
  · calc canon mask (canon mask w) = canon mask (w &&& mask) := by rw [h1]
      _ = canon mask w := canon_land mask w
  · calc canon mask (canon mask w) = canon mask (mask ^^^ (w &&& mask)) := by rw [h2]
      _ = canon mask (w &&& mask) := canon_xor_mask mask (w &&& mask)
      _ = canon mask w := canon_land mask w

theorem canon_submask {mask cut w : Nat} (sub : mask &&& cut = cut) (hc : canon mask w ≠ 0) :
    canon cut (canon mask w) = canon cut w := by
  rcases canon_cases mask w with ⟨h0, _⟩ | ⟨_, h1 | h2⟩
  · exact absurd h0 hc
  · rw [h1, ← canon_land cut (w &&& mask), masked_sub_and sub, canon_land]
  · rw [h2, ← canon_land cut (mask ^^^ (w &&& mask)), masked_sub_xor sub, masked_sub_and sub]
    rw [← masked_sub_xor (masked_self cut), canon_land, canon_xor_mask]

theorem canon_submask_zero {mask cut w : Nat} (sub : mask &&& cut = cut) (hc : canon mask w = 0) :
    canon cut w = 0 := by
  rcases canon_cases mask w with ⟨_, h0 | hm⟩ | ⟨hne, _⟩
  · rw [← canon_land cut w, ← masked_sub_and sub, h0]; simp [canon_zero]
  · rw [← canon_land cut w, ← masked_sub_and sub, hm, sub, canon_self]
  · exact absurd hc hne

theorem canon_testBit_eq {mask w p n : Nat} (hp : mask.testBit p = true) (hn : mask.testBit n = true) :
    ((canon mask w).testBit p = (canon mask w).testBit n) ↔ (w.testBit p = w.testBit n) := by
  rcases canon_cases mask w with ⟨h0, h1 | h2⟩ | ⟨_, h1 | h2⟩
  · rw [h0]
    have e1 := congrArg (fun x => x.testBit p) h1
    have e2 := congrArg (fun x => x.testBit n) h1
    simp [Nat.testBit_and, hp, hn] at e1 e2 ⊢; simp [e1, e2]
  · rw [h0]
    have e1 := congrArg (fun x => x.testBit p) h2
    have e2 := congrArg (fun x => x.testBit n) h2
    simp [Nat.testBit_and, hp, hn] at e1 e2 ⊢; simp [e1, e2]
  · rw [h1]; simp [Nat.testBit_and, hp, hn]
  · rw [h2]; simp [Nat.testBit_xor, Nat.testBit_and, hp, hn]

def binOp (mask op a b : Nat) : Nat :=
  bsel (Nat.beq op 0) (canon mask (a &&& b))
    (bsel (Nat.beq op 1) (canon mask (a ||| b))
      (bsel (Nat.beq op 2) (canon mask (a &&& (mask ^^^ b)))
        (canon mask ((mask ^^^ a) &&& b))))

theorem binOp_canon (mask op a b : Nat) : canon mask (binOp mask op a b) = binOp mask op a b := by
  unfold binOp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false] <;> exact canon_idem mask _

theorem binOp_comm (mask op a b : Nat) (hop : op < 4) :
    ∃ op' < 4, binOp mask op a b = binOp mask op' b a := by
  have hland : a &&& b = b &&& a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  have hlor : a ||| b = b ||| a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_or, Bool.or_comm]
  have h23 : a &&& (mask ^^^ b) = (mask ^^^ b) &&& a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  have h32 : (mask ^^^ a) &&& b = b &&& (mask ^^^ a) := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  rcases (show op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 by omega) with rfl | rfl | rfl | rfl
  · exact ⟨0, by omega, by change canon mask (a &&& b) = canon mask (b &&& a); rw [hland]⟩
  · exact ⟨1, by omega, by change canon mask (a ||| b) = canon mask (b ||| a); rw [hlor]⟩
  · exact ⟨3, by omega, by change canon mask (a &&& (mask ^^^ b)) = canon mask ((mask ^^^ b) &&& a); rw [h23]⟩
  · exact ⟨2, by omega, by change canon mask ((mask ^^^ a) &&& b) = canon mask (b &&& (mask ^^^ a)); rw [h32]⟩

theorem binOp_zero_left (mask op b : Nat) : binOp mask op 0 b = 0 ∨ binOp mask op 0 b = canon mask b := by
  unfold binOp
  have hmb : (mask ^^^ 0) &&& b = b &&& mask := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · right; rw [hmb, canon_land]
  · left; simp [canon_zero]
  · right; simp
  · right; simp
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]

theorem binOp_zero_right (mask op a : Nat) : binOp mask op a 0 = 0 ∨ binOp mask op a 0 = canon mask a := by
  unfold binOp
  have hma : a &&& (mask ^^^ 0) = a &&& mask := by simp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · left; simp [canon_zero]
  · right; rw [hma, canon_land]
  · right; simp
  · right; simp
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]

theorem binOp_self (mask op a : Nat) : binOp mask op a a = 0 ∨ binOp mask op a a = canon mask a := by
  have h2 : canon mask (a &&& (mask ^^^ a)) = 0 := by
    rw [← canon_land]
    have : (a &&& (mask ^^^ a)) &&& mask = 0 := by
      apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
      cases a.testBit i <;> cases mask.testBit i <;> rfl
    rw [this, canon_zero]
  have h3 : canon mask ((mask ^^^ a) &&& a) = 0 := by
    rw [← canon_land]
    have : ((mask ^^^ a) &&& a) &&& mask = 0 := by
      apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
      cases a.testBit i <;> cases mask.testBit i <;> rfl
    rw [this, canon_zero]
  unfold binOp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · left; exact h3
  · left; exact h2
  · right; simp
  · right; simp
  · right; simp
  · right; simp
  · right; simp
  · right; simp

theorem deMorgan_or_mask {mask a b : Nat} (ha : Masked mask a) (hb : Masked mask b) :
    mask ^^^ (a &&& b) = (mask ^^^ a) ||| (mask ^^^ b) := by
  unfold Masked at ha hb
  apply Nat.eq_of_testBit_eq; intro i
  have ea := congrArg (fun x => x.testBit i) ha
  have eb := congrArg (fun x => x.testBit i) hb
  simp only [Nat.testBit_and] at ea eb
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor]
  cases hm : mask.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all

theorem canon_and_in_binOp (mask x y : Nat) :
    canon mask (x &&& y) = 0 ∨
    canon mask (x &&& y) = canon mask x ∨
    canon mask (x &&& y) = canon mask y ∨
    ∃ op < 4, canon mask (x &&& y) = binOp mask op (canon mask x) (canon mask y) := by
  have hxy : canon mask (x &&& y) = canon mask ((x &&& mask) &&& (y &&& mask)) := by
    rw [← canon_land mask (x &&& y), ← canon_land mask ((x &&& mask) &&& (y &&& mask))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and]
    cases x.testBit i <;> cases y.testBit i <;> cases mask.testBit i <;> rfl
  rw [hxy]
  have hvxm : Masked mask (x &&& mask) := masked_land_right mask x
  have hvym : Masked mask (y &&& mask) := masked_land_right mask y
  rcases canon_cases mask x with ⟨hx0, hx1 | hx2⟩ | ⟨_, hx1 | hx2⟩
  · left; rw [hx1]; simp [canon_zero]
  · right; right; left; rw [hx2]
    have : mask &&& (y &&& mask) = y &&& mask := by
      apply Nat.eq_of_testBit_eq; intro i
      have e := congrArg (fun t => t.testBit i) hvym
      simp only [Nat.testBit_and] at e ⊢; rw [Bool.and_comm]; exact e
    rw [this, canon_land]
  · rcases canon_cases mask y with ⟨hy0, hy1 | hy2⟩ | ⟨_, hy1 | hy2⟩
    · left; rw [hy1]; simp [canon_zero]
    · right; left; rw [hy2, hvxm, canon_land]
    · right; right; right; refine ⟨0, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x &&& canon mask y)
      rw [hx1, hy1]
    · right; right; right; refine ⟨2, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x &&& (mask ^^^ canon mask y))
      rw [hx1, hy2, xor_cancel_left]
  · rcases canon_cases mask y with ⟨hy0, hy1 | hy2⟩ | ⟨_, hy1 | hy2⟩
    · left; rw [hy1]; simp [canon_zero]
    · right; left; rw [hy2, hvxm, canon_land]
    · right; right; right; refine ⟨3, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask ((mask ^^^ canon mask x) &&& canon mask y)
      rw [hx2, hy1, xor_cancel_left]
    · right; right; right; refine ⟨1, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x ||| canon mask y)
      rw [hx2, hy2, ← deMorgan_or_mask hvxm hvym, canon_xor_mask]

theorem canon_or_in_binOp (mask x y : Nat) :
    canon mask (x ||| y) = 0 ∨
    canon mask (x ||| y) = canon mask x ∨
    canon mask (x ||| y) = canon mask y ∨
    ∃ op < 4, canon mask (x ||| y) = binOp mask op (canon mask x) (canon mask y) := by
  have hxy : canon mask (x ||| y) = canon mask ((mask ^^^ x) &&& (mask ^^^ y)) := by
    rw [← canon_xor_mask mask (x ||| y), ← canon_land mask (mask ^^^ (x ||| y))]
    rw [← canon_land mask ((mask ^^^ x) &&& (mask ^^^ y))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor]
    cases mask.testBit i <;> cases x.testBit i <;> cases y.testBit i <;> rfl
  rw [hxy]
  have h := canon_and_in_binOp mask (mask ^^^ x) (mask ^^^ y)
  rwa [canon_xor_mask, canon_xor_mask] at h

theorem canon_sub_binOp {mask cut op a b : Nat} (sub : mask &&& cut = cut) :
    canon cut (binOp mask op a b) = 0 ∨
    canon cut (binOp mask op a b) = canon cut a ∨
    canon cut (binOp mask op a b) = canon cut b ∨
    ∃ op' < 4, canon cut (binOp mask op a b) = binOp cut op' (canon cut a) (canon cut b) := by
  have go (u : Nat) : canon cut (canon mask u) = canon cut u := by
    by_cases h : canon mask u = 0
    · rw [h, canon_zero, (canon_submask_zero sub h).symm]
    · exact canon_submask sub h
  have hmx1 : canon cut ((mask ^^^ a) &&& b) = canon cut ((cut ^^^ a) &&& b) := by
    rw [← canon_land cut ((mask ^^^ a) &&& b), ← canon_land cut ((cut ^^^ a) &&& b)]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    have es := congrArg (fun t => t.testBit i) sub
    simp only [Nat.testBit_and] at es
    simp only [Nat.testBit_and, Nat.testBit_xor]
    cases hc : cut.testBit i
    · simp
    · simp only [hc, Bool.and_true] at es ⊢; rw [es]
  have hmx2 : canon cut (a &&& (mask ^^^ b)) = canon cut (a &&& (cut ^^^ b)) := by
    rw [← canon_land cut (a &&& (mask ^^^ b)), ← canon_land cut (a &&& (cut ^^^ b))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    have es := congrArg (fun t => t.testBit i) sub
    simp only [Nat.testBit_and] at es
    simp only [Nat.testBit_and, Nat.testBit_xor]
    cases hc : cut.testBit i
    · simp
    · simp only [hc, Bool.and_true] at es ⊢; rw [es]
  have hsub_case1 : canon cut ((cut ^^^ a) &&& b) = 0 ∨ canon cut ((cut ^^^ a) &&& b) = canon cut a ∨
      canon cut ((cut ^^^ a) &&& b) = canon cut b ∨
      ∃ op' < 4, canon cut ((cut ^^^ a) &&& b) = binOp cut op' (canon cut a) (canon cut b) := by
    have h := canon_and_in_binOp cut (cut ^^^ a) b
    rwa [canon_xor_mask] at h
  have hsub_case2 : canon cut (a &&& (cut ^^^ b)) = 0 ∨ canon cut (a &&& (cut ^^^ b)) = canon cut a ∨
      canon cut (a &&& (cut ^^^ b)) = canon cut b ∨
      ∃ op' < 4, canon cut (a &&& (cut ^^^ b)) = binOp cut op' (canon cut a) (canon cut b) := by
    have h := canon_and_in_binOp cut a (cut ^^^ b)
    rwa [canon_xor_mask] at h
  have hbin_eq : binOp mask op a b = canon mask (a &&& b) ∨ binOp mask op a b = canon mask (a ||| b) ∨
      binOp mask op a b = canon mask (a &&& (mask ^^^ b)) ∨ binOp mask op a b = canon mask ((mask ^^^ a) &&& b) := by
    unfold binOp
    cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp [bsel]
  rcases hbin_eq with h | h | h | h <;> rw [h, go]
  · exact canon_and_in_binOp cut a b
  · exact canon_or_in_binOp cut a b
  · rw [hmx2]; exact hsub_case2
  · rw [hmx1]; exact hsub_case1

def Avail (bank : List Nat) (w : Nat) : Prop := w = 0 ∨ w ∈ bank

def GateBin (mask : Nat) (bank : List Nat) (v : Nat) : Prop :=
  ∃ a b op, op < 4 ∧ Avail bank a ∧ Avail bank b ∧ v = binOp mask op a b

def BuildsBin (mask : Nat) (bank : List Nat) : List Nat → Prop
  | [] => True
  | v :: vs => GateBin mask bank v ∧ BuildsBin mask (v :: bank) vs

def LowerBin (mask : Nat) (stock : List Nat) (goal m : Nat) : Prop :=
  ∀ vs, BuildsBin mask stock vs → Avail (vs ++ stock) goal → m ≤ vs.length

theorem avail_weaken {b1 b2 : List Nat} (sub : ∀ w ∈ b1, w ∈ b2) {w : Nat} (h : Avail b1 w) :
    Avail b2 w := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (sub w h)

theorem gate_weaken {mask : Nat} {b1 b2 : List Nat} (sub : ∀ w ∈ b1, w ∈ b2) {v : Nat}
    (h : GateBin mask b1 v) : GateBin mask b2 v := by
  obtain ⟨a, b, op, hop, ha, hb, hv⟩ := h
  exact ⟨a, b, op, hop, avail_weaken sub ha, avail_weaken sub hb, hv⟩

theorem builds_weaken {mask : Nat} {b1 b2 vs : List Nat} (sub : ∀ w ∈ b1, w ∈ b2)
    (h : BuildsBin mask b1 vs) : BuildsBin mask b2 vs := by
  induction vs generalizing b1 b2 with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨gate_weaken sub h.1, ih ?_ h.2⟩
    intro w hw; rcases List.mem_cons.mp hw with rfl | hw
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (sub w hw)

theorem builds_append {mask : Nat} {roots first second : List Nat}
    (h1 : BuildsBin mask roots first) (h2 : BuildsBin mask (first ++ roots) second) :
    BuildsBin mask roots (first ++ second) := by
  induction first generalizing roots with
  | nil => exact h2
  | cons v vs ih =>
    refine ⟨h1.1, ih h1.2 ?_⟩
    exact builds_weaken (fun w hw => by simp only [List.mem_append, List.mem_cons] at hw ⊢; tauto) h2

def dropIf (drop : Bool) (x : Nat) (S : Finset Nat) : Finset Nat :=
  if drop then S.erase x else S

theorem dropIf_subset (drop : Bool) (x : Nat) (S : Finset Nat) : dropIf drop x S ⊆ S := by
  unfold dropIf; split; exact Finset.erase_subset _ _; exact Finset.Subset.refl _

theorem dropIf_card_le (drop : Bool) (x : Nat) (S : Finset Nat) :
    S.card ≤ (dropIf drop x S).card + 1 := by
  unfold dropIf; split
  · by_cases hx : x ∈ S
    · have := Finset.card_erase_add_one hx; omega
    · rw [Finset.erase_eq_of_notMem hx]; omega
  · omega

inductive LiveBin (mask goal : Nat) : Nat → Finset Nat → Prop
  | done : LiveBin mask goal 0 {goal}
  | step {k : Nat} {S : Finset Nat} {a b op : Nat}
      (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hop : op < 4)
      (hz : binOp mask op a b ≠ 0) (hf : binOp mask op a b ∉ S)
      (keepA keepB : Bool) :
      LiveBin mask goal k (insert (binOp mask op a b) (dropIf (!keepA) a (dropIf (!keepB) b S))) →
      LiveBin mask goal (k + 1) S

theorem liveBin_zero_not_mem {mask goal k : Nat} {S : Finset Nat} (hg : goal ≠ 0)
    (h : LiveBin mask goal k S) : 0 ∉ S := by
  induction h with
  | done => simp [hg.symm]
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    intro h0; apply ih
    apply Finset.mem_insert_of_mem
    unfold dropIf
    split
    · apply Finset.mem_erase.mpr; refine ⟨ha0.symm, ?_⟩
      split
      · exact Finset.mem_erase.mpr ⟨hb0.symm, h0⟩
      · exact h0
    · split
      · exact Finset.mem_erase.mpr ⟨hb0.symm, h0⟩
      · exact h0

theorem liveBin_card_le {mask goal k : Nat} {S : Finset Nat} (h : LiveBin mask goal k S) :
    S.card ≤ k + 1 := by
  induction h with
  | done => simp
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    set z := binOp mask op a b
    have h1 := dropIf_card_le (!keepB) b S
    have h2 := dropIf_card_le (!keepA) a (dropIf (!keepB) b S)
    have hz' : z ∉ dropIf (!keepA) a (dropIf (!keepB) b S) := fun hm =>
      hf (dropIf_subset _ _ _ (dropIf_subset _ _ _ hm))
    have h3 : (insert z (dropIf (!keepA) a (dropIf (!keepB) b S))).card =
        (dropIf (!keepA) a (dropIf (!keepB) b S)).card + 1 := Finset.card_insert_of_notMem hz'
    omega

theorem extractLiveBin_aux {mask goal : Nat} (hg : goal ≠ 0) :
    ∀ (vs bank : List Nat) (k : Nat) (L : Finset Nat),
      BuildsBin mask bank vs → (∀ w ∈ bank, canon mask w = w) →
      L ⊆ (vs ++ bank).toFinset → LiveBin mask goal k L →
      ∃ k' S, k' ≤ k + vs.length ∧ S ⊆ bank.toFinset ∧ LiveBin mask goal k' S
  | [], bank, k, L, _, _, hsub, hlive => ⟨k, L, by simp, hsub, hlive⟩
  | v :: vs, bank, k, L, hbuild, hcb, hsub, hlive => by
    have hcv : canon mask v = v := by
      obtain ⟨a, b, op, _, _, _, rfl⟩ := hbuild.1; exact binOp_canon mask op a b
    have hcb' : ∀ w ∈ v :: bank, canon mask w = w := by
      intro w hw; rcases List.mem_cons.mp hw with rfl | hw; exact hcv; exact hcb w hw
    have hsub' : L ⊆ (vs ++ (v :: bank)).toFinset := by
      intro w hw
      have := hsub hw
      simp only [List.toFinset_append, List.toFinset_cons, Finset.mem_union, Finset.mem_insert] at this ⊢
      tauto
    obtain ⟨k1, L1, hk1, hL1sub, hlive1⟩ := extractLiveBin_aux hg vs (v :: bank) k L hbuild.2 hcb' hsub' hlive
    by_cases hv : v ∈ L1 ∧ v ∉ bank
    · obtain ⟨hvL, hvb⟩ := hv
      have hv0 : v ≠ 0 := fun h0 => liveBin_zero_not_mem hg hlive1 (h0 ▸ hvL)
      obtain ⟨a, b, op, hop, haA, hbA, hvEq⟩ := hbuild.1
      have ha0 : a ≠ 0 := by
        intro h0; subst h0
        rcases binOp_zero_left mask op b with h | h
        · exact hv0 (hvEq.trans h)
        · rcases hbA with rfl | hbM
          · rw [canon_zero] at h; exact hv0 (hvEq.trans h)
          · rw [hcb b hbM] at h; exact hvb ((hvEq.trans h) ▸ hbM)
      have hb0 : b ≠ 0 := by
        intro h0; subst h0
        rcases binOp_zero_right mask op a with h | h
        · exact hv0 (hvEq.trans h)
        · rcases haA with rfl | haM
          · rw [canon_zero] at h; exact hv0 (hvEq.trans h)
          · rw [hcb a haM] at h; exact hvb ((hvEq.trans h) ▸ haM)
      have haM : a ∈ bank := haA.resolve_left ha0
      have hbM : b ∈ bank := hbA.resolve_left hb0
      have hab : a ≠ b := by
        intro h; subst h
        rcases binOp_self mask op a with h0 | ha'
        · exact hv0 (hvEq.trans h0)
        · rw [hcb a haM] at ha'; exact hvb ((hvEq.trans ha') ▸ haM)
      set R := L1.erase v
      set S := insert a (insert b R)
      have hSsub : S ⊆ bank.toFinset := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact List.mem_toFinset.mpr haM
        · rcases Finset.mem_insert.mp hw with rfl | hw
          · exact List.mem_toFinset.mpr hbM
          · have h1 := hL1sub (Finset.mem_of_mem_erase hw)
            simp only [List.toFinset_cons, Finset.mem_insert] at h1
            exact h1.resolve_left (Finset.ne_of_mem_erase hw)
      have hvNotS : v ∉ S := by
        intro hm
        rcases Finset.mem_insert.mp hm with rfl | hm
        · exact hvb haM
        · rcases Finset.mem_insert.mp hm with rfl | hm
          · exact hvb hbM
          · exact (Finset.notMem_erase v L1) hm
      have hL1eq : insert v (dropIf (!(decide (a ∈ R))) a (dropIf (!(decide (b ∈ R))) b S)) = L1 := by
        ext w
        by_cases haR : a ∈ R <;> by_cases hbR : b ∈ R
        · simp only [haR, hbR, decide_true, Bool.not_true, Bool.false_eq_true, dropIf, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | rfl | rfl | ⟨_, hw⟩); exact hvL; exact (Finset.mem_erase.mp haR).2; exact (Finset.mem_erase.mp hbR).2; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h; exact Or.inr (Or.inr (Or.inr ⟨h, hw⟩))
        · simp only [haR, hbR, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, dropIf, ite_true, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwb, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact (Finset.mem_erase.mp haR).2; exact absurd rfl hwb; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            intro hwb; subst hwb; exact hbR (Finset.mem_erase.mpr ⟨h, hw⟩)
        · simp only [haR, hbR, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, dropIf, ite_true, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwa, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact absurd rfl hwa; exact (Finset.mem_erase.mp hbR).2; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            intro hwa; subst hwa; exact haR (Finset.mem_erase.mpr ⟨h, hw⟩)
        · simp only [haR, hbR, decide_false, Bool.not_false, dropIf, ite_true, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwa, hwb, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact absurd rfl hwa; exact absurd rfl hwb; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, ?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            · intro hwa; subst hwa; exact haR (Finset.mem_erase.mpr ⟨h, hw⟩)
            · intro hwb; subst hwb; exact hbR (Finset.mem_erase.mpr ⟨h, hw⟩)
      refine ⟨k1 + 1, S, by simp only [List.length_cons]; omega, hSsub, ?_⟩
      apply LiveBin.step (a := a) (b := b) (op := op)
        (Finset.mem_insert_self a _) (Finset.mem_insert_of_mem (Finset.mem_insert_self b _))
        hab ha0 hb0 hop (hvEq ▸ hv0) (hvEq ▸ hvNotS) (decide (a ∈ R)) (decide (b ∈ R))
      rw [← hvEq, hL1eq]; exact hlive1
    · refine ⟨k1, L1, by simp only [List.length_cons]; omega, ?_, hlive1⟩
      intro w hw
      have h1 := hL1sub hw
      simp only [List.toFinset_cons, Finset.mem_insert] at h1
      rcases h1 with rfl | h1
      · have hvb : w ∈ bank := by by_contra hnb; exact hv ⟨hw, hnb⟩
        exact List.mem_toFinset.mpr hvb
      · exact h1

theorem extractLiveBin {mask goal : Nat} {stock vs : List Nat}
    (hg : goal ≠ 0) (hcs : ∀ w ∈ stock, canon mask w = w)
    (hbuild : BuildsBin mask stock vs) (hhit : Avail (vs ++ stock) goal) :
    ∃ k S, k ≤ vs.length ∧ S ⊆ stock.toFinset ∧ LiveBin mask goal k S := by
  have hmem : goal ∈ vs ++ stock := hhit.resolve_left hg
  have hsub : ({goal} : Finset Nat) ⊆ (vs ++ stock).toFinset := by
    intro w hw; rw [Finset.mem_singleton.mp hw]; exact List.mem_toFinset.mpr hmem
  obtain ⟨k, S, hk, hS, hL⟩ := extractLiveBin_aux hg vs stock 0 {goal} hbuild hcs hsub LiveBin.done
  exact ⟨k, S, by omega, hS, hL⟩

theorem liveBin_agrees {mask goal k p n : Nat} {S : Finset Nat}
    (hp : mask.testBit p = true) (hn : mask.testBit n = true)
    (h : LiveBin mask goal k S) (hag : ∀ w ∈ S, w.testBit p = w.testBit n) :
    goal.testBit p = goal.testBit n := by
  induction h with
  | done => exact hag goal (Finset.mem_singleton_self goal)
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    apply ih; intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · have ea := hag a ha
      have eb := hag b hb
      unfold binOp
      cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
      all_goals rw [canon_testBit_eq hp hn]
      all_goals simp [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, hp, hn, ea, eb]
    · exact hag w (dropIf_subset _ _ _ (dropIf_subset _ _ _ hw))

def forceW {α : Type} (w : Nat) (k : Nat → α) : α :=
  Nat.rec (k 0) (fun m _ => k (m + 1)) w

theorem forceW_eq {α : Type} (w : Nat) (k : Nat → α) : forceW w k = k w := by
  cases w <;> rfl

def forceWs (ws : List Nat) (k : List Nat → Bool) : Bool :=
  (List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun w _ next k => forceW w (fun v => next (fun rest => k (v :: rest)))) ws) k

theorem forceWs_eq (ws : List Nat) (k : List Nat → Bool) : forceWs ws k = k ws := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih =>
    change forceW w (fun v => forceWs ws (fun rest => k (v :: rest))) = _
    rw [forceW_eq, ih]

def dagPart (ws : List Nat) : Nat → Nat → Bool :=
  List.rec
    (fun p n => Nat.beq p 0 || Nat.beq n 0)
    (fun w _ rest p n =>
      (Nat.beq p 0 || Nat.beq n 0) ||
        forceW (p &&& w) (fun up =>
          forceW (n &&& w) (fun down =>
            rest up down &&
              forceW (p ^^^ up) (fun offP =>
                forceW (n ^^^ down) (rest offP))))) ws

theorem offBits {v w i : Nat} (h : (v ^^^ (v &&& w)).testBit i = true) :
    v.testBit i = true ∧ w.testBit i = false := by
  rw [Nat.testBit_xor, Nat.testBit_and] at h
  cases hv : v.testBit i <;> cases hw : w.testBit i <;> simp [hv, hw] at h ⊢

theorem dagPart_sound {ws : List Nat} {pos neg : Nat} (fail : dagPart ws pos neg = false) :
    ∃ p n, pos.testBit p = true ∧ neg.testBit n = true ∧ ∀ w ∈ ws, w.testBit p = w.testBit n := by
  have nonempty {w : Nat} (hn : w ≠ 0) : ∃ j, w.testBit j = true := by
    by_contra! all; apply hn; apply Nat.eq_of_testBit_eq; intro i; simp [all i]
  induction ws generalizing pos neg with
  | nil =>
    change (Nat.beq pos 0 || Nat.beq neg 0) = false at fail
    simp only [Bool.or_eq_false_iff] at fail
    obtain ⟨p, hp⟩ := nonempty (ne_of_beq_false fail.1)
    obtain ⟨n, hn⟩ := nonempty (ne_of_beq_false fail.2)
    exact ⟨p, n, hp, hn, by simp⟩
  | cons w ws ih =>
    change ((Nat.beq pos 0 || Nat.beq neg 0) ||
      forceW (pos &&& w) (fun up =>
        forceW (neg &&& w) (fun down =>
          dagPart ws up down &&
            forceW (pos ^^^ up) (fun offP =>
              forceW (neg ^^^ down) (dagPart ws offP))))) = false at fail
    simp only [forceW_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at fail
    rcases fail.2 with on | off
    · obtain ⟨p, n, hp, hn, ag⟩ := ih on
      rw [Nat.testBit_and, Bool.and_eq_true] at hp hn
      refine ⟨p, n, hp.1, hn.1, fun a ha => ?_⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · rw [hp.2, hn.2]
      · exact ag a ha
    · obtain ⟨p, n, hp, hn, ag⟩ := ih off
      have hp' := offBits hp
      have hn' := offBits hn
      refine ⟨p, n, hp'.1, hn'.1, fun a ha => ?_⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · rw [hp'.2, hn'.2]
      · exact ag a ha

theorem dagPart_live {mask goal k : Nat} {ws : List Nat}
    (hgm : Masked mask goal) (hlive : LiveBin mask goal k ws.toFinset) :
    dagPart ws goal (mask ^^^ goal) = true := by
  by_contra hf
  have hfalse : dagPart ws goal (mask ^^^ goal) = false := by
    cases h : dagPart ws goal (mask ^^^ goal) <;> simp_all
  obtain ⟨p, n, hp, hn, ag⟩ := dagPart_sound hfalse
  have hpm : mask.testBit p = true := by
    have e := congrArg (fun x => x.testBit p) hgm
    simp only [Nat.testBit_and, hp, Bool.true_and] at e; exact e
  have hnm : mask.testBit n = true ∧ goal.testBit n = false := by
    rw [Nat.testBit_xor] at hn
    have imp : goal.testBit n = true → mask.testBit n = true := by
      intro hg
      have e := congrArg (fun x => x.testBit n) hgm
      simp only [Nat.testBit_and, hg, Bool.true_and] at e; exact e
    cases hm : mask.testBit n <;> cases hg : goal.testBit n <;> simp_all
  have eq := liveBin_agrees hpm hnm.1 hlive (fun w hw => ag w (List.mem_toFinset.mp hw))
  rw [hp, hnm.2] at eq; exact Bool.noConfusion eq

def flatSet (cut : Nat) (S : Finset Nat) : Finset Nat :=
  S.filter (fun w => Nat.beq (canon cut w) 0)

theorem flatSet_insert_notMem {cut w : Nat} {S : Finset Nat} (hw : w ∉ S) :
    (flatSet cut (insert w S)).card =
      if canon cut w = 0 then (flatSet cut S).card + 1 else (flatSet cut S).card := by
  unfold flatSet
  rw [Finset.filter_insert]
  by_cases hc : canon cut w = 0
  · simp only [hc, Nat.beq_refl, ite_true]
    exact Finset.card_insert_of_notMem (fun h => hw (Finset.mem_filter.mp h).1)
  · simp only [beq_false_ne hc, Bool.false_eq_true, ite_false, hc]

theorem flatSet_erase {cut w : Nat} {S : Finset Nat} :
    (flatSet cut S).card ≤ (flatSet cut (S.erase w)).card + (if canon cut w = 0 then 1 else 0) := by
  unfold flatSet
  rw [Finset.filter_erase]
  by_cases hm : w ∈ S.filter (fun x => Nat.beq (canon cut x) 0)
  · have hcw : canon cut w = 0 := Nat.eq_of_beq_eq_true (Finset.mem_filter.mp hm).2
    have hcard := Finset.card_erase_add_one hm
    simp only [hcw, ite_true]; omega
  · rw [Finset.erase_eq_of_notMem hm]; omega

theorem maskedBuildBin {mask cut goal k : Nat} {S : Finset Nat}
    (sub : mask &&& cut = cut) (hgnf : canon cut goal ≠ 0)
    (h : LiveBin mask goal k S) :
    ∀ (bank : List Nat), (∀ w ∈ S, Avail bank (canon cut w)) →
      ∃ vs, vs.length + (flatSet cut S).card ≤ k ∧ BuildsBin cut bank vs ∧
        Avail (vs ++ bank) (canon cut goal) := by
  induction h with
  | done =>
    intro bank hsup
    have hfl : (flatSet cut {goal}).card = 0 := by
      unfold flatSet
      simp [hgnf]
    exact ⟨[], by simp [hfl], trivial, hsup goal (Finset.mem_singleton_self goal)⟩
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB tail ih =>
    intro bank hsup
    set z := binOp mask op a b
    set S1 := dropIf (!keepB) b S
    set S2 := dropIf (!keepA) a S1
    set S' := insert z S2
    have hS2sub : S2 ⊆ S := Finset.Subset.trans (dropIf_subset _ _ _) (dropIf_subset _ _ _)
    have hzNotS2 : z ∉ S2 := fun hm => hf (hS2sub hm)
    have hfl1 : (flatSet cut S).card ≤ (flatSet cut S1).card + (if canon cut b = 0 then 1 else 0) := by
      unfold S1 dropIf; split; exact flatSet_erase; omega
    have hfl2 : (flatSet cut S1).card ≤ (flatSet cut S2).card + (if canon cut a = 0 then 1 else 0) := by
      unfold S2 dropIf; split; exact flatSet_erase; omega
    have hfl3 : (flatSet cut S').card =
        if canon cut z = 0 then (flatSet cut S2).card + 1 else (flatSet cut S2).card :=
      flatSet_insert_notMem hzNotS2
    have hcz : canon cut z = 0 ∨ canon cut z = canon cut a ∨ canon cut z = canon cut b ∨
        ∃ op' < 4, canon cut z = binOp cut op' (canon cut a) (canon cut b) :=
      canon_sub_binOp sub
    by_cases hfa : canon cut a = 0
    · by_cases hfb : canon cut b = 0
      · have hfz : canon cut z = 0 := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact h
          · exact h.trans hfa
          · exact h.trans hfb
          · rw [hfa, hfb] at h
            rcases binOp_zero_left cut op' 0 with h0 | h0
            · exact h.trans h0
            · exact h.trans (h0.trans (canon_zero cut))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact Or.inl hfz
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, hfz, ite_true] at hfl1 hfl2 hfl3
        exact ⟨vs, by omega, hbd, hhit⟩
      · have hfz : canon cut z = 0 ∨ canon cut z = canon cut b := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact Or.inl h
          · exact Or.inl (h.trans hfa)
          · exact Or.inr h
          · rw [hfa] at h
            rcases binOp_zero_left cut op' (canon cut b) with h0 | h0
            · exact Or.inl (h.trans h0)
            · exact Or.inr (h.trans (h0.trans (canon_idem cut b)))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · rcases hfz with h0 | hb'
            · exact Or.inl h0
            · rw [hb']; exact hsup b hb
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, ite_true, ite_false] at hfl1 hfl2
        have : (flatSet cut S2).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        exact ⟨vs, by omega, hbd, hhit⟩
    · by_cases hfb : canon cut b = 0
      · have hfz : canon cut z = 0 ∨ canon cut z = canon cut a := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact Or.inl h
          · exact Or.inr h
          · exact Or.inl (h.trans hfb)
          · rw [hfb] at h
            rcases binOp_zero_right cut op' (canon cut a) with h0 | h0
            · exact Or.inl (h.trans h0)
            · exact Or.inr (h.trans (h0.trans (canon_idem cut a)))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · rcases hfz with h0 | ha'
            · exact Or.inl h0
            · rw [ha']; exact hsup a ha
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, ite_true, ite_false] at hfl1 hfl2
        have : (flatSet cut S2).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        exact ⟨vs, by omega, hbd, hhit⟩
      · simp only [hfa, hfb, ite_false] at hfl1 hfl2
        have hfl_le : (flatSet cut S).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        rcases hcz with h0 | ha' | hb' | ⟨op', hop', hbin⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · exact Or.inl h0
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · rw [ha']; exact hsup a ha
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · rw [hb']; exact hsup b hb
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · set cz := canon cut z
          have hgate : GateBin cut bank cz := ⟨canon cut a, canon cut b, op', hop', hsup a ha, hsup b hb, hbin⟩
          have hsup' : ∀ w ∈ S', Avail (cz :: bank) (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · exact Or.inr List.mem_cons_self
            · exact avail_weaken (fun u hu => List.mem_cons_of_mem _ hu) (hsup w (hS2sub hw))
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih (cz :: bank) hsup'
          refine ⟨cz :: vs, by simp only [List.length_cons]; omega, ⟨hgate, hbd⟩, ?_⟩
          exact avail_weaken (fun u hu => by simp only [List.mem_append, List.mem_cons] at hu ⊢; tauto) hhit

def flatCount (cut : Nat) (ws : List Nat) : Nat :=
  List.rec 0 (fun w _ cnt => bsel (Nat.beq (canon cut w) 0) (cnt + 1) cnt) ws

theorem flatCount_card (cut : Nat) {ws : List Nat} (nd : ws.Nodup) :
    flatCount cut ws = (flatSet cut ws.toFinset).card := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hnd := List.nodup_cons.mp nd
    have fresh : w ∉ ws.toFinset := by simpa using hnd.1
    change bsel (Nat.beq (canon cut w) 0) (flatCount cut ws + 1) (flatCount cut ws) = _
    rw [List.toFinset_cons, flatSet_insert_notMem fresh, ih hnd.2]
    by_cases hc : canon cut w = 0
    · simp [hc, bsel]
    · rw [beq_false_ne hc, bsel_false]; simp [hc]

def availB (bank : List Nat) (w : Nat) : Bool :=
  Nat.beq w 0 || bank.contains w

theorem availB_spec {bank : List Nat} {w : Nat} : availB bank w = true ↔ Avail bank w := by
  unfold availB Avail; simp [Nat.beq_eq]

def recipeGateBin (cut : Nat) (bank : List Nat) (vc ac bc : Nat) : Bool :=
  availB bank ac && availB bank bc &&
    (Nat.beq vc (binOp cut 0 ac bc) || Nat.beq vc (binOp cut 1 ac bc) ||
     Nat.beq vc (binOp cut 2 ac bc) || Nat.beq vc (binOp cut 3 ac bc))

theorem recipeGateBin_spec {cut : Nat} {bank : List Nat} {vc ac bc : Nat}
    (h : recipeGateBin cut bank vc ac bc = true) : GateBin cut bank vc := by
  unfold recipeGateBin at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, availB_spec] at h
  obtain ⟨⟨ha, hb⟩, ((h0 | h1) | h2) | h3⟩ := h
  · exact ⟨ac, bc, 0, by omega, ha, hb, h0⟩
  · exact ⟨ac, bc, 1, by omega, ha, hb, h1⟩
  · exact ⟨ac, bc, 2, by omega, ha, hb, h2⟩
  · exact ⟨ac, bc, 3, by omega, ha, hb, h3⟩

def addUniq (w : Nat) (l : List Nat) : List Nat :=
  if l.contains w then l else w :: l

def recipeStart (cut : Nat) (stock ws : List Nat) : List Nat :=
  List.rec [] (fun w _ acc =>
    let v := canon cut w
    if availB stock v then acc else addUniq v acc) ws

def recipeClose (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun (w, a, b) _ next acc =>
      let v := canon cut w
      if acc.contains v then
        let va := canon cut a
        let vb := canon cut b
        let acc1 := if availB stock va then acc else addUniq va acc
        let acc2 := if availB stock vb then acc1 else addUniq vb acc1
        next acc2
      else next acc) hist needed

def replayRec (cut : Nat) (needed : List Nat) (hist : List (Nat × Nat × Nat)) (bank : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun _ => [])
    (fun (w, a, b) _ next bank =>
      let v := canon cut w
      if needed.contains v && !(availB bank v) && recipeGateBin cut bank v (canon cut a) (canon cut b) then
        v :: next (v :: bank)
      else next bank) hist bank

theorem replayRec_builds (cut : Nat) (needed : List Nat) (hist : List (Nat × Nat × Nat)) (bank : List Nat) :
    BuildsBin cut bank (replayRec cut needed hist bank) := by
  induction hist generalizing bank with
  | nil => trivial
  | cons rec hist ih =>
    obtain ⟨w, a, b⟩ := rec
    change BuildsBin cut bank
      (if needed.contains (canon cut w) && !(availB bank (canon cut w)) &&
          recipeGateBin cut bank (canon cut w) (canon cut a) (canon cut b) then
        canon cut w :: replayRec cut needed hist (canon cut w :: bank)
      else replayRec cut needed hist bank)
    split
    · rename_i hyes
      exact ⟨recipeGateBin_spec (Bool.and_eq_true_iff.mp hyes).2, ih _⟩
    · exact ih _

def boundCloses (target : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat))
    (bound : Nat × List Nat × Nat × Nat) : Bool :=
  let (cut, stock, lower, goal) := bound
  let (fuel, ws, hist) := state
  Nat.beq (canon cut target) goal && !(Nat.beq goal 0) &&
    forceW (fuel - flatCount cut ws) (fun rem =>
      if Nat.blt rem lower then
        forceWs (recipeStart cut stock ws) (fun start =>
          if Nat.blt (start.length + rem) lower then
            forceWs (recipeClose cut stock hist start) (fun needed =>
              if Nat.blt (needed.length + rem) lower then
                forceWs (replayRec cut needed hist.reverse stock) (fun replay =>
                  Nat.blt (replay.length + rem) lower &&
                    ws.all (fun w => availB (replay ++ stock) (canon cut w)))
              else false)
          else false)
      else false)

def knownCloses (target : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  List.rec false (fun b _ rest => boundCloses target state b || rest) bounds

def KnownBin (bounds : List (Nat × List Nat × Nat × Nat)) : Prop :=
  ∀ b ∈ bounds, LowerBin b.1 b.2.1 b.2.2.2 b.2.2.1

theorem boundCloses_sound {mask goal : Nat} {state : Nat × List Nat × List (Nat × Nat × Nat)}
    {bound : Nat × List Nat × Nat × Nat}
    (hlow : LowerBin bound.1 bound.2.1 bound.2.2.2 bound.2.2.1)
    (sub : mask &&& bound.1 = bound.1)
    (nd : state.2.1.Nodup) {k : Nat} (hk : k ≤ state.1)
    (hlive : LiveBin mask goal k state.2.1.toFinset) :
    boundCloses goal state bound = false := by
  obtain ⟨fuel, ws, hist⟩ := state
  obtain ⟨cut, stock, lower, bgoal⟩ := bound
  dsimp only at hlow sub nd hk hlive
  apply Bool.eq_false_iff.mpr
  intro hc
  unfold boundCloses at hc
  simp only [forceW_eq, forceWs_eq, Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hc
  obtain ⟨⟨hgeq, hgnz⟩, scan⟩ := hc
  have hgnz' : bgoal ≠ 0 := ne_of_beq_false hgnz
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  simp only [Bool.and_eq_true, Nat.blt_eq] at scan
  obtain ⟨hlen, hsrc⟩ := scan
  set replay := replayRec cut (recipeClose cut stock hist (recipeStart cut stock ws)) hist.reverse stock
  have hgnf : canon cut goal ≠ 0 := hgeq.symm ▸ hgnz'
  have hsup : ∀ w ∈ ws.toFinset, Avail (replay ++ stock) (canon cut w) := by
    intro w hw
    exact availB_spec.mp (List.all_eq_true.mp hsrc w (List.mem_toFinset.mp hw))
  obtain ⟨ys, hylen, hybd, hyhit⟩ := maskedBuildBin sub hgnf hlive (replay ++ stock) hsup
  rw [← flatCount_card cut nd] at hylen
  have hboth := builds_append (replayRec_builds cut _ hist.reverse stock) hybd
  have hfinal : Avail ((replay ++ ys) ++ stock) bgoal := by
    rw [← hgeq]
    exact avail_weaken (fun u hu => by simp only [List.mem_append] at hu ⊢; tauto) hyhit
  have heno := hlow (replay ++ ys) hboth hfinal
  simp only [List.length_append] at heno
  omega

theorem knownCloses_sound {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    {state : Nat × List Nat × List (Nat × Nat × Nat)}
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (nd : state.2.1.Nodup) {k : Nat} (hk : k ≤ state.1)
    (hlive : LiveBin mask goal k state.2.1.toFinset) :
    knownCloses goal bounds state = false := by
  induction bounds with
  | nil => rfl
  | cons b bs ih =>
    change (boundCloses goal state b || knownCloses goal bs state) = false
    rw [boundCloses_sound (hknown b List.mem_cons_self) (hsub b List.mem_cons_self) nd hk hlive]
    exact ih (fun x hx => hknown x (List.mem_cons_of_mem _ hx)) (fun x hx => hsub x (List.mem_cons_of_mem _ hx))

def insertSorted (x : Nat) (l : List Nat) : List Nat :=
  List.rec [x] (fun y ys ih => bsel (Nat.ble x y) (x :: y :: ys) (y :: ih)) l

theorem insertSorted_mem {x w : Nat} {l : List Nat} :
    w ∈ insertSorted x l ↔ w = x ∨ w ∈ l := by
  induction l with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    change w ∈ bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys) ↔ _
    cases Nat.ble x y
    · rw [bsel_false]; simp only [List.mem_cons, ih]; tauto
    · rw [bsel_true]; simp only [List.mem_cons]

theorem insertSorted_nodup {x : Nat} {l : List Nat} (hx : x ∉ l) (nd : l.Nodup) :
    (insertSorted x l).Nodup := by
  induction l with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    have hnd := List.nodup_cons.mp nd
    have hxy : x ≠ y := fun h => hx (h ▸ List.mem_cons_self)
    have hxs : x ∉ ys := fun h => hx (List.mem_cons_of_mem _ h)
    change (bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys)).Nodup
    cases Nat.ble x y
    · rw [bsel_false]
      apply List.nodup_cons.mpr
      refine ⟨fun hm => ?_, ih hxs hnd.2⟩
      rcases insertSorted_mem.mp hm with h | h
      · exact hxy h.symm
      · exact hnd.1 h
    · rw [bsel_true]; exact List.nodup_cons.mpr ⟨hx, nd⟩

def dropVal (drop : Bool) (x : Nat) (l : List Nat) : List Nat :=
  bsel drop (List.rec [] (fun y _ ih => bsel (Nat.beq y x) ih (y :: ih)) l) l

theorem dropVal_mem {drop : Bool} {x w : Nat} {l : List Nat} :
    w ∈ dropVal drop x l ↔ w ∈ l ∧ (drop = true → w ≠ x) := by
  cases drop
  · simp [dropVal, bsel]
  · induction l with
    | nil => simp [dropVal, bsel]
    | cons y ys ih =>
      change w ∈ bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys) ↔ _
      cases hb : Nat.beq y x
      · rw [bsel_false]
        have hne : y ≠ x := ne_of_beq_false hb
        simp only [List.mem_cons, ih, true_implies]
        constructor
        · rintro (rfl | ⟨hw, hwx⟩); exact ⟨Or.inl rfl, hne⟩; exact ⟨Or.inr hw, hwx⟩
        · rintro ⟨rfl | hw, hwx⟩; exact Or.inl rfl; exact Or.inr ⟨hw, hwx⟩
      · rw [bsel_true]
        have heq : y = x := Nat.eq_of_beq_eq_true hb
        subst heq
        simp only [List.mem_cons, ih, true_implies]
        constructor
        · rintro ⟨hw, hwx⟩; exact ⟨Or.inr hw, hwx⟩
        · rintro ⟨rfl | hw, hwx⟩; exact absurd rfl hwx; exact ⟨hw, hwx⟩

theorem dropVal_nodup {drop : Bool} {x : Nat} {l : List Nat} (nd : l.Nodup) :
    (dropVal drop x l).Nodup := by
  cases drop
  · exact nd
  · induction l with
    | nil => simp [dropVal, bsel]
    | cons y ys ih =>
      have hnd := List.nodup_cons.mp nd
      change (bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys)).Nodup
      cases Nat.beq y x
      · rw [bsel_false]
        exact List.nodup_cons.mpr ⟨fun hm => hnd.1 (dropVal_mem.mp hm).1, ih hnd.2⟩
      · rw [bsel_true]; exact ih hnd.2

theorem dropVal_toFinset (drop : Bool) (x : Nat) (l : List Nat) :
    (dropVal drop x l).toFinset = dropIf drop x l.toFinset := by
  ext w; simp only [List.mem_toFinset, dropVal_mem, dropIf]
  cases drop <;> simp [Finset.mem_erase, and_comm]

def subsetWords (stock : List Nat) (bits : Nat) : List Nat :=
  (List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun w _ ih b =>
      let rest := ih (b >>> 1)
      bsel (Nat.beq (b &&& 1) 1) (insertSorted w rest) rest) stock) bits

theorem subsetWords_subset (stock : List Nat) (bits : Nat) :
    ∀ w ∈ subsetWords stock bits, w ∈ stock := by
  induction stock generalizing bits with
  | nil => intro w hw; simp [subsetWords] at hw
  | cons x xs ih =>
    intro w hw
    change w ∈ bsel (Nat.beq (bits &&& 1) 1)
      (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1)) at hw
    cases hb : Nat.beq (bits &&& 1) 1
    · rw [hb, bsel_false] at hw; exact List.mem_cons_of_mem _ (ih _ w hw)
    · rw [hb, bsel_true] at hw
      rcases insertSorted_mem.mp hw with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih _ w hm)

theorem subsetWords_nodup {stock : List Nat} (nd : stock.Nodup) (bits : Nat) :
    (subsetWords stock bits).Nodup := by
  induction stock generalizing bits with
  | nil => simp [subsetWords]
  | cons x xs ih =>
    have hnd := List.nodup_cons.mp nd
    change (bsel (Nat.beq (bits &&& 1) 1)
      (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1))).Nodup
    cases Nat.beq (bits &&& 1) 1
    · rw [bsel_false]; exact ih hnd.2 _
    · rw [bsel_true]; exact insertSorted_nodup (fun hm => hnd.1 (subsetWords_subset xs _ x hm)) (ih hnd.2 _)

theorem exists_subsetToken (stock : List Nat) (S : Finset Nat) :
    ∃ bits < 2 ^ stock.length, (subsetWords stock bits).toFinset = S ∩ stock.toFinset := by
  induction stock with
  | nil => exact ⟨0, by simp, by simp [subsetWords]⟩
  | cons x xs ih =>
    obtain ⟨b, hb, heq⟩ := ih
    by_cases hx : x ∈ S
    · refine ⟨2 * b + 1, by simp only [List.length_cons, Nat.pow_succ]; omega, ?_⟩
      have hdiv : (2 * b + 1) >>> 1 = b := by change (2 * b + 1) / 2 = b; omega
      have hmod : ((2 * b + 1) &&& 1) = 1 := by rw [Nat.and_one_is_mod]; omega
      change (bsel (Nat.beq ((2 * b + 1) &&& 1) 1)
        (insertSorted x (subsetWords xs ((2 * b + 1) >>> 1)))
        (subsetWords xs ((2 * b + 1) >>> 1))).toFinset = _
      rw [hdiv, hmod, Nat.beq_refl, bsel_true]
      ext w; simp only [List.mem_toFinset, insertSorted_mem, Finset.mem_inter, List.toFinset_cons, Finset.mem_insert]
      have hw : w ∈ subsetWords xs b ↔ w ∈ S ∧ w ∈ xs := by
        have e := congrArg (fun t => w ∈ t) heq; simpa [List.mem_toFinset] using e
      rw [hw]; constructor
      · rintro (rfl | ⟨hs, hxs⟩); exact ⟨hx, Or.inl rfl⟩; exact ⟨hs, Or.inr hxs⟩
      · rintro ⟨hs, rfl | hxs⟩; exact Or.inl rfl; exact Or.inr ⟨hs, hxs⟩
    · refine ⟨2 * b, by simp only [List.length_cons, Nat.pow_succ]; omega, ?_⟩
      have hdiv : (2 * b) >>> 1 = b := by change (2 * b) / 2 = b; omega
      have hmod : ((2 * b) &&& 1) = 0 := by rw [Nat.and_one_is_mod]; omega
      change (bsel (Nat.beq ((2 * b) &&& 1) 1)
        (insertSorted x (subsetWords xs ((2 * b) >>> 1)))
        (subsetWords xs ((2 * b) >>> 1))).toFinset = _
      rw [hdiv, hmod]
      change (subsetWords xs b).toFinset = _
      ext w; simp only [List.mem_toFinset, Finset.mem_inter, List.toFinset_cons, Finset.mem_insert]
      have hw : w ∈ subsetWords xs b ↔ w ∈ S ∧ w ∈ xs := by
        have e := congrArg (fun t => w ∈ t) heq; simpa [List.mem_toFinset] using e
      rw [hw]; constructor
      · rintro ⟨hs, hxs⟩; exact ⟨hs, Or.inr hxs⟩
      · rintro ⟨hs, rfl | hxs⟩; exact absurd hs hx; exact ⟨hs, hxs⟩

def rootState (stock : List Nat) (fuel token : Nat) : Nat × List Nat × List (Nat × Nat × Nat) :=
  (fuel, subsetWords stock token, [])

def makeToken (a b op keep : Nat) : Nat := ((a * 16 + b) * 4 + op) * 4 + keep

def childState (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  let (fuel, ws, hist) := state
  let keep := token &&& 3
  let op := (token >>> 2) &&& 3
  let b := (token >>> 4) &&& 15
  let a := token >>> 8
  if Nat.beq fuel 0 || !(Nat.blt a b) || !(Nat.blt b ws.length) then none
  else
    let x := ws.getD a 0
    let y := ws.getD b 0
    let z := binOp mask op x y
    if Nat.beq z 0 || ws.contains z then none
    else
      let keepA := Nat.beq (keep &&& 1) 1
      let keepB := Nat.beq ((keep >>> 1) &&& 1) 1
      let rest := dropVal (!keepA) x (dropVal (!keepB) y ws)
      some (fuel - 1, insertSorted z rest, (z, x, y) :: hist)

theorem childState_wf {mask token : Nat} {st ch : Nat × List Nat × List (Nat × Nat × Nat)}
    (nd : st.2.1.Nodup) (h : childState mask token st = some ch) :
    ch.1 < st.1 ∧ ch.2.1.Nodup := by
  obtain ⟨fuel, ws, hist⟩ := st
  dsimp only at nd
  unfold childState at h; dsimp only at h
  split at h
  · contradiction
  · rename_i hok
    split at h
    · contradiction
    · rename_i hfresh
      have heq := Option.some.inj h
      subst ch
      simp only [Bool.or_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hok hfresh
      have hfpos : fuel ≠ 0 := fun hf => hok (Or.inl (Or.inl hf))
      have hznot : ¬(ws.contains (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0)
          (ws.getD ((token >>> 4) &&& 15) 0)) = true) := fun hm => hfresh (Or.inr hm)
      refine ⟨by dsimp; omega, ?_⟩
      apply insertSorted_nodup
      · intro hm
        have hmem := (dropVal_mem.mp (dropVal_mem.mp hm).1).1
        exact hznot (List.contains_iff_mem.mpr hmem)
      · exact dropVal_nodup (dropVal_nodup nd)

def dagTrace (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
    (fun _ prev j =>
      let (parent, token) := forest j
      if Nat.beq parent 0 then
        if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
      else (prev (parent - 1)).bind (childState mask token)) (fuel + 1)) i

theorem dagTrace_nodup {mask fuel : Nat} {stock : List Nat} {forest : Nat → Nat × Nat}
    (nd : stock.Nodup) {i : Nat} {st : Nat × List Nat × List (Nat × Nat × Nat)}
    (h : dagTrace mask stock fuel forest i = some st) : st.2.1.Nodup := by
  unfold dagTrace at h
  suffices ∀ steps j s,
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) steps) j = some s → s.2.1.Nodup from
    this (fuel + 1) i st h
  intro steps
  induction steps with
  | zero => intro j s h; contradiction
  | succ n ih =>
    intro j s h; dsimp only at h
    split at h
    · split at h
      · have e := Option.some.inj h; subst s; exact subsetWords_nodup nd _
      · contradiction
    · cases hp : (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) n) ((forest j).1 - 1) with
      | none => rw [hp] at h; contradiction
      | some p => rw [hp] at h; exact (childState_wf (ih _ _ hp) h).2

def dagLocal (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  let (fuel, ws, _) := state
  Nat.blt (fuel + 1) ws.length ||
    !(dagPart ws goal (mask ^^^ goal)) ||
    knownCloses goal bounds state

theorem dagLocal_open {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    {state : Nat × List Nat × List (Nat × Nat × Nat)}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (nd : state.2.1.Nodup) {k : Nat} (hk : k ≤ state.1)
    (hlive : LiveBin mask goal k state.2.1.toFinset) :
    dagLocal mask goal bounds state = false := by
  obtain ⟨fuel, ws, hist⟩ := state
  dsimp only at nd hk hlive
  unfold dagLocal
  have hcard : ws.length ≤ fuel + 1 := by
    have := liveBin_card_le hlive
    rw [List.toFinset_card_of_nodup nd] at this; omega
  have h1 : Nat.blt (fuel + 1) ws.length = false := by
    cases h : Nat.blt (fuel + 1) ws.length; rfl; have := Nat.blt_eq.mp h; omega
  have h2 : dagPart ws goal (mask ^^^ goal) = true := dagPart_live hgm hlive
  have h3 : knownCloses goal bounds (fuel, ws, hist) = false :=
    knownCloses_sound hknown hsub nd hk hlive
  simp [h1, h2, h3]

def treeBlock (lo hi : Nat) (f : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ next a b =>
      if Nat.blt a b then
        let m := (a + b) / 2
        if Nat.beq a m then f a else next a m && next m b
      else true) (hi - lo + 1)) lo hi

theorem treeBlock_at {lo hi : Nat} {f : Nat → Bool} (h : treeBlock lo hi f = true) :
    ∀ {i : Nat}, lo ≤ i → i < hi → f i = true := by
  unfold treeBlock at h
  suffices ∀ steps a b, b - a ≤ steps →
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          if Nat.blt x y then
            let m := (x + y) / 2
            if Nat.beq x m then f x else next x m && next m y
          else true) steps) a b = true →
      ∀ i, a ≤ i → i < b → f i = true by
    intro i h1 h2; exact this (hi - lo + 1) lo hi (by omega) h i h1 h2
  intro steps
  induction steps with
  | zero => intro a b hba _ i h1 h2; omega
  | succ s ih =>
    intro a b hba h i h1 h2
    dsimp only at h
    have hab : Nat.blt a b = true := Nat.blt_eq.mpr (by omega)
    simp only [hab, ite_true] at h
    set m := (a + b) / 2
    by_cases ham : a = m
    · have hbm : Nat.beq a m = true := Nat.beq_eq.mpr ham
      simp only [hbm, ite_true] at h
      have hia : i = a := by omega
      subst hia; exact h
    · have hbm : Nat.beq a m = false := beq_false_ne ham
      simp only [hbm, Bool.false_eq_true, ite_false] at h
      rcases Bool.and_eq_true_iff.mp h with ⟨hl, hr⟩
      by_cases him : i < m
      · exact ih a m (by omega) hl i h1 him
      · exact ih m b (by omega) hr i (by omega) h2

def dagRef (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (parent token : Nat)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  match links parent token with
  | none => false
  | some dest =>
    Nat.blt dest count &&
      match states dest with
      | none => false
      | some saved => Nat.beq saved.1 state.1 && (saved.2.1 == state.2.1)

def dagCheckChildren (mask goal : Nat) (bounds : Nat → List (Nat × List Nat × Nat × Nat))
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  let (fuel, ws, hist) := state
  let n := ws.length
  !(ws.contains goal) &&
    (Nat.beq fuel 0 ||
      (Nat.blt n 17 &&
        treeBlock 0 n (fun a =>
          let x := ws.getD a 0
          treeBlock (a + 1) n (fun b =>
            let y := ws.getD b 0
            treeBlock 0 4 (fun op =>
              forceW (binOp mask op x y) (fun z =>
                Nat.beq z 0 || ws.contains z ||
                  treeBlock 0 4 (fun keep =>
                    let keepA := Nat.beq (keep &&& 1) 1
                    let keepB := Nat.beq ((keep >>> 1) &&& 1) 1
                    let newLen := n - 1 + (if keepA then 1 else 0) + (if keepB then 1 else 0)
                    Nat.blt fuel newLen ||
                      forceWs (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))) (fun ws' =>
                        let ch := (fuel - 1, ws', (z, x, y) :: hist)
                        dagLocal mask goal (bounds (makeToken a b op keep)) ch || ref (makeToken a b op keep) ch))))))))

def dagCheckNode (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some st => dagCheckChildren mask goal (fun _ => bounds) (dagRef count states links (i + 1)) st

def dagCheckRoots (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (stock : List Nat) (fuel : Nat) : Bool :=
  treeBlock 0 (2 ^ stock.length) (fun token =>
    forceWs (subsetWords stock token) (fun ws =>
      let st := (fuel, ws, [])
      dagLocal mask goal bounds st || ref token st))

theorem getElem_index_lt {l : List Nat} {x : Nat} (hx : x ∈ l) :
    ∃ i < l.length, l.getD i 0 = x := by
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hx
  refine ⟨i, hi, ?_⟩
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, heq]

theorem list_len_child {x y z : Nat} {ws : List Nat} {keepA keepB : Bool}
    (nd : ws.Nodup) (hx : x ∈ ws) (hy : y ∈ ws) (hxy : x ≠ y) (hz : z ∉ ws) :
    (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).length =
      ws.length - 1 + (if keepA then 1 else 0) + (if keepB then 1 else 0) := by
  have nd' : (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).Nodup :=
    insertSorted_nodup (fun hm => hz (dropVal_mem.mp (dropVal_mem.mp hm).1).1) (dropVal_nodup (dropVal_nodup nd))
  have h1 := List.toFinset_card_of_nodup nd'
  have h2 := List.toFinset_card_of_nodup nd
  have hset : (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).toFinset =
      insert z (dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset)) := by
    ext w
    simp only [List.mem_toFinset, insertSorted_mem, Finset.mem_insert, ← dropVal_toFinset]
  rw [hset] at h1
  have hz' : z ∉ dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset) :=
    fun hm => hz (List.mem_toFinset.mp (dropIf_subset _ _ _ (dropIf_subset _ _ _ hm)))
  rw [Finset.card_insert_of_notMem hz'] at h1
  set T := dropIf (!keepB) y ws.toFinset
  have hxb : x ∈ T := by
    unfold T dropIf; split
    · exact Finset.mem_erase.mpr ⟨hxy, List.mem_toFinset.mpr hx⟩
    · exact List.mem_toFinset.mpr hx
  have hcb : T.card = ws.toFinset.card - (if keepB then 0 else 1) := by
    unfold T dropIf; cases keepB
    · have := Finset.card_erase_add_one (List.mem_toFinset.mpr hy); simp; omega
    · simp
  have hca : (dropIf (!keepA) x T).card = T.card - (if keepA then 0 else 1) := by
    unfold dropIf; cases keepA
    · have := Finset.card_erase_add_one hxb; simp only [Bool.not_false, Bool.false_eq_true, ite_true, ite_false]; omega
    · simp
  have hlen2 : 2 ≤ ws.toFinset.card := by
    have hsub : ({x, y} : Finset Nat) ⊆ ws.toFinset := by
      intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
      · exact List.mem_toFinset.mpr hx
      · rw [Finset.mem_singleton.mp hw]; exact List.mem_toFinset.mpr hy
    have hpair : ({x, y} : Finset Nat).card = 2 := Finset.card_pair hxy
    have := Finset.card_le_card hsub; omega
  rw [← h1, hca, hcb, h2]
  cases keepA <;> cases keepB <;> simp <;> omega

theorem dagAllNodes {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {links : Nat → Nat → Option Nat}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1) (snd : stock.Nodup)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNode mask goal bounds count
      (dagTrace mask stock fuel forest) links i = true) :
    ∀ cap i st, i < count → dagTrace mask stock fuel forest i = some st →
      st.1 = cap → ∀ k, k ≤ cap → ¬LiveBin mask goal k st.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i st hi htr hcap k hk hlive
    obtain ⟨rem, ws, hist⟩ := st
    dsimp only at hcap hlive
    have nd : ws.Nodup := dagTrace_nodup snd htr
    have hchk := hnodes i (Nat.zero_le i) hi
    unfold dagCheckNode at hchk
    rw [htr] at hchk
    unfold dagCheckChildren at hchk
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, Nat.beq_eq, Nat.blt_eq] at hchk
    obtain ⟨hnohit, hstep⟩ := hchk
    generalize hS : ws.toFinset = S at hlive
    cases hlive with
    | done =>
      have hgm' : goal ∈ ws := List.mem_toFinset.mp (hS.symm ▸ Finset.mem_singleton_self goal)
      have hc : ws.contains goal = true := List.contains_iff_mem.mpr hgm'
      rw [hc] at hnohit; exact Bool.noConfusion hnohit
    | @step k' _ a0 b0 op0 ha0 hb0 hab0 _ _ hop0 hz0 hf0 keepA0 keepB0 tail0 =>
      rw [← hS] at ha0 hb0 hf0 tail0
      have hrem_pos : rem ≠ 0 := by omega
      rcases hstep with hrem0 | ⟨hn17, hblock⟩
      · exact hrem_pos hrem0
      · have haM : a0 ∈ ws := List.mem_toFinset.mp ha0
        have hbM : b0 ∈ ws := List.mem_toFinset.mp hb0
        obtain ⟨ia0, hia0, hea0⟩ := getElem_index_lt haM
        obtain ⟨ib0, hib0, heb0⟩ := getElem_index_lt hbM
        have hiab_ne : ia0 ≠ ib0 := fun heq => hab0 (hea0.symm.trans (heq ▸ heb0))
        have ⟨a, b, op, keepA, keepB, ha_lt, hab_lt, hb_lt, hop_lt, hax, hby, hzeq, htail⟩ :
            ∃ a b op keepA keepB, a < ws.length ∧ a < b ∧ b < ws.length ∧ op < 4 ∧
              ws.getD a 0 = (if ia0 < ib0 then a0 else b0) ∧
              ws.getD b 0 = (if ia0 < ib0 then b0 else a0) ∧
              binOp mask op (ws.getD a 0) (ws.getD b 0) = binOp mask op0 a0 b0 ∧
              LiveBin mask goal k' (insert (binOp mask op (ws.getD a 0) (ws.getD b 0))
                (dropIf (!keepA) (ws.getD a 0) (dropIf (!keepB) (ws.getD b 0) ws.toFinset))) := by
          by_cases hlt : ia0 < ib0
          · exact ⟨ia0, ib0, op0, keepA0, keepB0, hia0, hlt, hib0, hop0,
              by simp only [hlt, ite_true]; exact hea0,
              by simp only [hlt, ite_true]; exact heb0,
              by rw [hea0, heb0], by rw [hea0, heb0]; exact tail0⟩
          · obtain ⟨op1, hop1, hopEq⟩ := binOp_comm mask op0 a0 b0 hop0
            have hswap : dropIf (!keepB0) b0 (dropIf (!keepA0) a0 ws.toFinset) =
                dropIf (!keepA0) a0 (dropIf (!keepB0) b0 ws.toFinset) := by
              ext w; simp only [dropIf]; cases keepA0 <;> cases keepB0 <;> simp [Finset.mem_erase, and_left_comm]
            exact ⟨ib0, ia0, op1, keepB0, keepA0, hib0, by omega, hia0, hop1,
              by simp only [hlt, ite_false]; exact heb0,
              by simp only [hlt, ite_false]; exact hea0,
              by rw [hea0, heb0, hopEq],
              by rw [hea0, heb0, ← hopEq, hswap]; exact tail0⟩
        set x := ws.getD a 0
        set y := ws.getD b 0
        set z := binOp mask op x y
        set keep := (if keepA then 1 else 0) + (if keepB then 2 else 0)
        have hkeep_lt : keep < 4 := by cases keepA <;> cases keepB <;> simp [keep]
        have hkA : Nat.beq (keep &&& 1) 1 = keepA := by cases keepA <;> cases keepB <;> decide
        have hkB : Nat.beq ((keep >>> 1) &&& 1) 1 = keepB := by cases keepA <;> cases keepB <;> decide
        have hkA' : (keep &&& 1 = 1) ↔ keepA = true := by cases keepA <;> cases keepB <;> decide
        have hkB' : ((keep >>> 1) &&& 1 = 1) ↔ keepB = true := by cases keepA <;> cases keepB <;> decide
        have hA := treeBlock_at hblock (Nat.zero_le a) ha_lt
        have hB := treeBlock_at hA (by omega : a + 1 ≤ b) hb_lt
        have hO := treeBlock_at hB (Nat.zero_le op) hop_lt
        simp only [forceW_eq, Bool.or_eq_true, Nat.beq_eq] at hO
        have hznz : z ≠ 0 := hzeq.symm ▸ hz0
        have hznm : ws.contains z = false := by
          cases h : ws.contains z
          · rfl
          · exact absurd (List.mem_toFinset.mpr (List.contains_iff_mem.mp h)) (hzeq.symm ▸ hf0)
        rcases hO with (hz' | hcm) | hK
        · exact hznz hz'
        · rw [hznm] at hcm; exact Bool.noConfusion hcm
        · have hKe := treeBlock_at hK (Nat.zero_le keep) hkeep_lt
          simp only [hkA, hkB, hkA', hkB', forceWs_eq, Bool.or_eq_true, Nat.blt_eq] at hKe
          set ws' := insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))
          have hxM : x ∈ ws := by simp only [x, hax]; split; exact haM; exact hbM
          have hyM : y ∈ ws := by simp only [y, hby]; split; exact hbM; exact haM
          have hxy : x ≠ y := by simp only [x, y, hax, hby]; split; exact hab0; exact hab0.symm
          have hzNotW : z ∉ ws := fun hm => by
            have := List.contains_iff_mem.mpr hm; rw [hznm] at this; exact Bool.noConfusion this
          have hnd' : ws'.Nodup :=
            insertSorted_nodup (fun hm => hzNotW (dropVal_mem.mp (dropVal_mem.mp hm).1).1) (dropVal_nodup (dropVal_nodup nd))
          have hset' : ws'.toFinset = insert z (dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset)) := by
            ext w; simp only [ws', List.mem_toFinset, insertSorted_mem, Finset.mem_insert, ← dropVal_toFinset]
          have hlive' : LiveBin mask goal k' ws'.toFinset := by rwa [hset']
          have hlen' := list_len_child (z := z) (keepA := keepA) (keepB := keepB) nd hxM hyM hxy hzNotW
          have hcard' : ws'.length ≤ rem := by
            have := liveBin_card_le hlive'
            rw [List.toFinset_card_of_nodup hnd'] at this; omega
          rcases hKe with hwide | hloc | href
          · change ws'.length = _ at hlen'; rw [← hlen'] at hwide; omega
          · have hopen := dagLocal_open (state := (rem - 1, ws', (z, x, y) :: hist)) hgm hknown hsub hnd' (k := k') (by omega) hlive'
            rw [hopen] at hloc; exact Bool.noConfusion hloc
          · unfold dagRef at href
            split at href
            · contradiction
            · rename_i dest _
              simp only [Bool.and_eq_true, Nat.blt_eq] at href
              obtain ⟨hdest, hst⟩ := href
              cases htr2 : dagTrace mask stock fuel forest dest with
              | none => rw [htr2] at hst; contradiction
              | some saved =>
                rw [htr2] at hst
                simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at hst
                obtain ⟨hfEq, hwEq⟩ := hst
                have hbelow : rem - 1 < cap := by omega
                exact ih (rem - 1) hbelow dest saved hdest htr2 hfEq k' (by omega) (hwEq ▸ hlive')

theorem lowerDag {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {links : Nat → Nat → Option Nat}
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hroots : dagCheckRoots mask goal bounds
      (dagRef count (dagTrace mask stock fuel forest) links 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNode mask goal bounds count
      (dagTrace mask stock fuel forest) links i = true) :
    LowerBin mask stock goal (fuel + 1) := by
  intro vs hbuild hhit
  by_contra! hlt
  have hcs' : ∀ w ∈ stock, canon mask w = w := fun w hw =>
    Nat.beq_eq.mp (List.all_eq_true.mp hcs w hw)
  obtain ⟨k, S, hk, hSsub, hlive⟩ := extractLiveBin hgnz hcs' hbuild hhit
  obtain ⟨tok, htok, hteq⟩ := exists_subsetToken stock S
  rw [Finset.inter_eq_left.mpr hSsub] at hteq
  have hchk := treeBlock_at hroots (Nat.zero_le tok) htok
  simp only [forceWs_eq, Bool.or_eq_true] at hchk
  have hnd : (subsetWords stock tok).Nodup := subsetWords_nodup snd tok
  have hlive' : LiveBin mask goal k (subsetWords stock tok).toFinset := by rwa [hteq]
  rcases hchk with hloc | href
  · have hopen := dagLocal_open (state := (fuel, subsetWords stock tok, [])) hgm hknown hsub hnd (k := k) (by omega) hlive'
    rw [hopen] at hloc; exact Bool.noConfusion hloc
  · unfold dagRef at href
    split at href
    · contradiction
    · rename_i dest _
      simp only [Bool.and_eq_true, Nat.blt_eq] at href
      obtain ⟨hdest, hst⟩ := href
      cases htr : dagTrace mask stock fuel forest dest with
      | none => rw [htr] at hst; contradiction
      | some saved =>
        rw [htr] at hst
        simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at hst
        obtain ⟨hfEq, hwEq⟩ := hst
        exact dagAllNodes hgm hknown hsub snd hnodes fuel dest saved hdest htr hfEq k (by omega) (hwEq ▸ hlive')

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true

def binaryCost (gs : List Gate) : Nat := (gs.filter isBinary).length

def legal (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def evalBit (k : Nat) (w : Nat) : Bool := w.testBit k

def stepBool (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def actionWord (w : List Nat) (g : Gate) : Nat := match g.op with
  | .not => fullMask ^^^ ((g.inputs.head?.map (fun i => w.getD i 0)).getD 0)
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) fullMask
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

theorem fullMask_eq : fullMask = 2 ^ 64 - 1 := by decide

theorem fullMask_bit {k : Nat} (hk : k < 64) : fullMask.testBit k = true := by
  rw [fullMask_eq, Nat.testBit_two_pow_sub_one]; simp [hk]

theorem readBit (w : List Nat) (i k : Nat) :
    (w.map (evalBit k)).getD i false = evalBit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), evalBit]

theorem actionWord_spec (w : List Nat) (g : Gate) (hg : legal g) {k : Nat} (hk : k < 64) :
    stepBool (w.map (evalBit k)) g = (w ++ [actionWord w g]).map (evalBit k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hcap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hcap
  have hfm := fullMask_bit hk
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at hcap
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [stepBool, List.map_cons, List.map_nil, readBit, List.map_append, actionWord,
      GateOp.eval, List.foldr_cons, List.foldr_nil, List.head?_cons, List.head?_nil,
      List.headD_cons, List.headD_nil, Option.map_some, Option.map_none, Option.getD_some,
      Option.getD_none, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq,
      Bool.and_true, Bool.or_false, evalBit, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor,
      Nat.zero_testBit, hfm, Bool.true_xor]

def rawVars : List Nat :=
  [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

def rootStock : List Nat :=
  [0x5555555555555555, 0x3333333333333333, 0x0f0f0f0f0f0f0f0f,
   0x00ff00ff00ff00ff, 0x0000ffff0000ffff, 0x00000000ffffffff]

theorem rawVars_avail : ∀ u ∈ rawVars, Avail rootStock (canon fullMask u) := by
  intro u hu
  simp only [rawVars, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Or.inr (by decide)

theorem compileBin_aux (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (w bank : List Nat)
    (hw : ∀ u ∈ w, Avail bank (canon fullMask u)) :
    ∃ vs, vs.length ≤ binaryCost gs ∧ BuildsBin fullMask bank vs ∧
      ∀ u ∈ gs.foldl (fun acc g => acc ++ [actionWord acc g]) w, Avail (vs ++ bank) (canon fullMask u) := by
  induction gs generalizing w bank with
  | nil => exact ⟨[], Nat.le_refl _, trivial, by simpa using hw⟩
  | cons g gs ih =>
    have hg0 := hg g List.mem_cons_self
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    set z := actionWord w g
    have hread (i : Nat) : Avail bank (canon fullMask (w.getD i 0)) := by
      by_cases hi : i < w.length
      · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi])
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi), canon_zero]; exact Or.inl rfl
    have hstep : Avail bank (canon fullMask z) ∨ (isBinary g = true ∧ GateBin fullMask bank (canon fullMask z)) := by
      obtain ⟨op, args⟩ := g
      obtain ⟨hop, hcap⟩ := hg0
      change op = .and ∨ op = .or ∨ op = .not at hop
      change args.length ≤ 2 at hcap
      rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at hcap
      · rcases hop with rfl | rfl | rfl
        · left; simp [z, actionWord, canon_self]; exact Or.inl rfl
        · left; simp [z, actionWord, canon_zero]; exact Or.inl rfl
        · left; simp [z, actionWord, canon_self]; exact Or.inl rfl
      · rcases hop with rfl | rfl | rfl
        · left; simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
          rw [canon_land]; exact hread i
        · left; simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.or_zero]
          exact hread i
        · left; simp only [z, actionWord, List.head?_cons, Option.map_some, Option.getD_some]
          rw [canon_xor_mask]; exact hread i
      · rcases hop with rfl | rfl | rfl
        · simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
          have h1 : canon fullMask (w.getD i 0 &&& (w.getD j 0 &&& fullMask)) =
              canon fullMask (w.getD i 0 &&& w.getD j 0) := by
            rw [← canon_land fullMask (w.getD i 0 &&& (w.getD j 0 &&& fullMask))]
            rw [← canon_land fullMask (w.getD i 0 &&& w.getD j 0)]
            congr 1; apply Nat.eq_of_testBit_eq; intro k; simp only [Nat.testBit_and]
            cases (w.getD i 0).testBit k <;> cases (w.getD j 0).testBit k <;> cases fullMask.testBit k <;> rfl
          rw [h1]
          rcases canon_and_in_binOp fullMask (w.getD i 0) (w.getD j 0) with h0 | hi' | hj' | ⟨op', hop', hbin⟩
          · left; exact Or.inl h0
          · left; rw [hi']; exact hread i
          · left; rw [hj']; exact hread j
          · right; exact ⟨rfl, canon fullMask (w.getD i 0), canon fullMask (w.getD j 0), op', hop', hread i, hread j, hbin⟩
        · simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.or_zero]
          rcases canon_or_in_binOp fullMask (w.getD i 0) (w.getD j 0) with h0 | hi' | hj' | ⟨op', hop', hbin⟩
          · left; exact Or.inl h0
          · left; rw [hi']; exact hread i
          · left; rw [hj']; exact hread j
          · right; exact ⟨rfl, canon fullMask (w.getD i 0), canon fullMask (w.getD j 0), op', hop', hread i, hread j, hbin⟩
        · left; simp only [z, actionWord, List.head?_cons, Option.map_some, Option.getD_some]
          rw [canon_xor_mask]; exact hread i
    rcases hstep with hav | ⟨hbin, hgate⟩
    · have hw' : ∀ u ∈ w ++ [z], Avail bank (canon fullMask u) := by
        intro u hu; rcases List.mem_append.mp hu with hu | hu
        · exact hw u hu
        · rw [List.mem_singleton.mp hu]; exact hav
      obtain ⟨vs, hlen, hbd, hall⟩ := ih hgs (w ++ [z]) bank hw'
      have hbc : binaryCost gs ≤ binaryCost (g :: gs) := by
        unfold binaryCost; simp only [List.filter]; cases isBinary g <;> simp
      exact ⟨vs, Nat.le_trans hlen hbc, hbd, hall⟩
    · set cz := canon fullMask z
      have hw' : ∀ u ∈ w ++ [z], Avail (cz :: bank) (canon fullMask u) := by
        intro u hu; rcases List.mem_append.mp hu with hu | hu
        · exact avail_weaken (fun a ha => List.mem_cons_of_mem _ ha) (hw u hu)
        · rw [List.mem_singleton.mp hu]; exact Or.inr List.mem_cons_self
      obtain ⟨vs, hlen, hbd, hall⟩ := ih hgs (w ++ [z]) (cz :: bank) hw'
      have hbc : binaryCost (g :: gs) = binaryCost gs + 1 := by
        unfold binaryCost; simp [hbin]
      refine ⟨cz :: vs, by simp only [List.length_cons, hbc]; omega, ⟨hgate, hbd⟩, ?_⟩
      intro u hu
      exact avail_weaken (fun a ha => by simp only [List.mem_append, List.mem_cons] at ha ⊢; tauto) (hall u hu)

theorem foldl_evalBit (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (w : List Nat) {k : Nat} (hk : k < 64) :
    gs.foldl stepBool (w.map (evalBit k)) =
      (gs.foldl (fun acc g => acc ++ [actionWord acc g]) w).map (evalBit k) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [actionWord_spec w g (hg g List.mem_cons_self) hk]
    exact ih (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (w ++ [actionWord w g])

theorem rawVars_ofFn (x : Fin 6 → Bool) :
    List.ofFn x = rawVars.map (evalBit (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) := by
  have hx : ∀ (b0 b1 b2 b3 b4 b5 : Bool),
      [b0, b1, b2, b3, b4, b5] =
      rawVars.map (evalBit ((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
        (if b3 then 8 else 0) + (if b4 then 16 else 0) + (if b5 then 32 else 0))) := by
    decide +kernel
  have hsum : (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) =
      (if x 0 then 1 else 0) + (if x 1 then 2 else 0) + (if x 2 then 4 else 0) +
      (if x 3 then 8 else 0) + (if x 4 then 16 else 0) + (if x 5 then 32 else 0) := by
    simp [Fin.sum_univ_six]
  rw [hsum, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  exact hx (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

theorem sum_bits_6 (n : Nat) (hn : n < 64) :
    (∑ i : Fin 6, if n.testBit i.val then 2 ^ (i : Nat) else 0) = n := by
  simp only [Fin.sum_univ_six, Fin.val_zero, Fin.val_one, Fin.val_two]
  change (if n.testBit 0 then 1 else 0) + (if n.testBit 1 then 2 else 0) +
    (if n.testBit 2 then 4 else 0) + (if n.testBit 3 then 8 else 0) +
    (if n.testBit 4 then 16 else 0) + (if n.testBit 5 then 32 else 0) = n
  revert n; decide +kernel

theorem table2_from_lowerBin (target m : Nat)
    (hlow : LowerBin fullMask rootStock (canon fullMask target) (m - 1))
    (wg : List Gate) (wout : Nat) (hsz : wg.length = m)
    (hmono : Monotone2 ⟨wg, wout⟩)
    (heval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, wout⟩ (List.ofFn x) =
      Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) :
    ∀ s : Nat, HasCircuitSize 6 (fun x : Fin 6 → Bool =>
      Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) s →
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool,
      C.eval (List.ofFn x) = Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) := by
  intro s ⟨C, hfan, hsize, hC⟩
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, hgm, hgop⟩ := hasNot
    have hshort : binaryCost C.gates < C.gates.length :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr ⟨g, hgm, by simp [isBinary, hgop]⟩
    have hleg : ∀ g ∈ C.gates, legal g := by
      intro g hg
      obtain ⟨hop, hlen⟩ := hfan g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      exact ⟨hop, hlen⟩
    obtain ⟨vs, hvlen, hvbd, hvhit⟩ := compileBin_aux C.gates hleg rawVars rootStock rawVars_avail
    set finalW := C.gates.foldl (fun acc g => acc ++ [actionWord acc g]) rawVars
    have hout_eq : finalW.getD C.output 0 &&& fullMask = target &&& fullMask := by
      apply Nat.eq_of_testBit_eq; intro k
      by_cases hk : k < 64
      · have hfm := fullMask_bit hk
        simp only [Nat.testBit_and, hfm, Bool.and_true]
        let x : Fin 6 → Bool := fun i => k.testBit i.val
        have hxidx : (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) = k := sum_bits_6 k hk
        have h1 := hC x
        dsimp only at h1
        rw [hxidx, rawVars_ofFn x, hxidx] at h1
        change (C.gates.foldl stepBool (rawVars.map (evalBit k))).getD C.output false = target.testBit k at h1
        rw [foldl_evalBit C.gates hleg rawVars hk, readBit] at h1
        exact h1
      · have hfm0 : fullMask.testBit k = false := by
          rw [fullMask_eq, Nat.testBit_two_pow_sub_one]; simp [hk]
        simp [Nat.testBit_and, hfm0]
    have hout_avail : Avail (vs ++ rootStock) (canon fullMask target) := by
      rw [← canon_land fullMask target, ← hout_eq, canon_land]
      by_cases hi : C.output < finalW.length
      · exact hvhit _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi])
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi), canon_zero]; exact Or.inl rfl
    have hge := hlow vs hvbd hout_avail
    have hcsz : C.size = C.gates.length := rfl
    have hwsz : (⟨wg, wout⟩ : Circuit).size = m := hsz
    exact ⟨⟨wg, wout⟩, hmono, by omega, heval⟩
  · refine ⟨C, ?_, hsize, hC⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim

def memN (z : Nat) (l : List Nat) : Bool :=
  List.rec false (fun w _ ih => Bool.rec ih true (Nat.beq z w)) l

theorem memN_eq (z : Nat) (l : List Nat) : memN z l = l.contains z := by
  apply Bool.eq_iff_iff.mpr
  rw [List.contains_iff_mem]
  induction l with
  | nil => simp [memN]
  | cons w ws ih =>
    change Bool.rec (memN z ws) true (Nat.beq z w) = true ↔ z ∈ w :: ws
    cases h : Nat.beq z w
    · have hne : z ≠ w := ne_of_beq_false h
      simp [ih, hne]
    · have heq : z = w := Nat.eq_of_beq_eq_true h
      simp [heq]

def allN (p : Nat → Bool) (l : List Nat) : Bool :=
  List.rec true (fun w _ ih => Bool.rec false ih (p w)) l

theorem allN_eq (p : Nat → Bool) (l : List Nat) : allN p l = l.all p := by
  induction l with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec false (allN p ws) (p w) = (p w && ws.all p)
    rw [ih]; cases p w <;> rfl

def lenN (l : List Nat) : Nat :=
  List.rec 0 (fun _ _ ih => Nat.add ih 1) l

theorem lenN_eq (l : List Nat) : lenN l = l.length := by
  induction l with
  | nil => rfl
  | cons _ ws ih => change Nat.add (lenN ws) 1 = ws.length + 1; rw [ih]

def appN (l r : List Nat) : List Nat :=
  List.rec r (fun w _ ih => w :: ih) l

theorem appN_eq (l r : List Nat) : appN l r = l ++ r := by
  induction l with
  | nil => rfl
  | cons w ws ih => change w :: appN ws r = w :: (ws ++ r); rw [ih]

def revAccN {α : Type} (l acc : List α) : List α :=
  (List.rec (motive := fun _ => List α → List α) (fun a => a) (fun w _ ih a => ih (w :: a)) l) acc

theorem revAccN_eq {α : Type} (l acc : List α) : revAccN l acc = l.reverse ++ acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons w ws ih =>
    change revAccN ws (w :: acc) = (w :: ws).reverse ++ acc
    rw [ih, List.reverse_cons, List.append_assoc]; rfl

def getDN (l : List Nat) (i : Nat) : Nat :=
  (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun w _ ih k => Nat.rec w (fun m _ => ih m) k) l) i

theorem getDN_eq (l : List Nat) (i : Nat) : getDN l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons w ws ih =>
    cases i with
    | zero => rfl
    | succ m => change getDN ws m = (w :: ws).getD (m + 1) 0; rw [ih]; rfl

def eqListN (l1 : List Nat) : List Nat → Bool :=
  List.rec
    (fun l2 => List.rec true (fun _ _ _ => false) l2)
    (fun x _ ih l2 => List.rec false (fun y ys _ => Bool.rec false (ih ys) (Nat.beq x y)) l2) l1

theorem eqListN_eq (l1 l2 : List Nat) : eqListN l1 l2 = (l1 == l2) := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> rfl
  | cons x xs ih =>
    cases l2 with
    | nil => rfl
    | cons y ys =>
      change Bool.rec false (eqListN xs ys) (Nat.beq x y) = ((x :: xs) == (y :: ys))
      rw [ih]
      by_cases h : x = y
      · subst h; simp [Nat.beq_refl]
      · have h1 : Nat.beq x y = false := beq_false_ne h
        have h2 : (x == y) = false := beq_false_of_ne h
        simp [h1, h2]

def canonF (mask w : Nat) : Nat :=
  let v := Nat.land w mask
  Bool.rec
    (Bool.rec
      (let iv := Nat.xor mask v
       Bool.rec iv v (Nat.blt v iv))
      0 (Nat.beq v mask))
    0 (Nat.beq v 0)

theorem canonF_eq (mask w : Nat) : canonF mask w = canon mask w := by
  unfold canonF canon bsel; dsimp only
  change (Bool.rec (Bool.rec (Bool.rec (mask ^^^ (w &&& mask)) (w &&& mask) ((w &&& mask).blt (mask ^^^ (w &&& mask)))) 0 ((w &&& mask).beq mask)) 0 ((w &&& mask).beq 0) : Nat) = _
  cases Nat.beq (w &&& mask) 0 <;> cases Nat.beq (w &&& mask) mask <;> rfl

def binOpF (mask op a b : Nat) : Nat :=
  Bool.rec
    (Bool.rec
      (Bool.rec (canonF mask (Nat.land (Nat.xor mask a) b))
        (canonF mask (Nat.land a (Nat.xor mask b))) (Nat.beq op 2))
      (canonF mask (Nat.lor a b)) (Nat.beq op 1))
    (canonF mask (Nat.land a b)) (Nat.beq op 0)

theorem binOpF_eq (mask op a b : Nat) : binOpF mask op a b = binOp mask op a b := by
  unfold binOpF binOp bsel
  simp only [canonF_eq]
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> rfl

def dagPartF (ws : List Nat) : Nat → Nat → Bool :=
  List.rec
    (fun p n => Bool.rec (Nat.beq n 0) true (Nat.beq p 0))
    (fun w _ rest p n =>
      Bool.rec
        (Bool.rec
          (forceW (Nat.land p w) (fun up =>
            forceW (Nat.land n w) (fun down =>
              Bool.rec false
                (forceW (Nat.xor p up) (fun offP =>
                  forceW (Nat.xor n down) (rest offP)))
                (rest up down))))
          true (Nat.beq n 0))
        true (Nat.beq p 0)) ws

theorem dagPartF_eq (ws : List Nat) (p n : Nat) : dagPartF ws p n = dagPart ws p n := by
  induction ws generalizing p n with
  | nil =>
    change Bool.rec (Nat.beq n 0) true (Nat.beq p 0) = (Nat.beq p 0 || Nat.beq n 0)
    cases Nat.beq p 0 <;> rfl
  | cons w ws ih =>
    change Bool.rec (Bool.rec (forceW (Nat.land p w) (fun up =>
      forceW (Nat.land n w) (fun down =>
        Bool.rec false (forceW (Nat.xor p up) (fun offP => forceW (Nat.xor n down) (dagPartF ws offP)))
          (dagPartF ws up down)))) true (Nat.beq n 0)) true (Nat.beq p 0) =
      ((Nat.beq p 0 || Nat.beq n 0) || forceW (p &&& w) (fun up =>
        forceW (n &&& w) (fun down => dagPart ws up down &&
          forceW (p ^^^ up) (fun offP => forceW (n ^^^ down) (dagPart ws offP)))))
    simp only [forceW_eq]
    cases Nat.beq p 0
    · cases Nat.beq n 0
      · change Bool.rec false (dagPartF ws _ _) (dagPartF ws _ _) = (dagPart ws _ _ && dagPart ws _ _)
        rw [ih, ih]; cases dagPart ws (p &&& w) (n &&& w) <;> rfl
      · rfl
    · rfl

def flatCountF (cut : Nat) (ws : List Nat) : Nat :=
  List.rec 0 (fun w _ cnt =>
    let v := Nat.land w cut
    Bool.rec (Bool.rec cnt (Nat.add cnt 1) (Nat.beq v cut)) (Nat.add cnt 1) (Nat.beq v 0)) ws

theorem flatCountF_eq (cut : Nat) (ws : List Nat) : flatCountF cut ws = flatCount cut ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (Bool.rec (flatCountF cut ws) (Nat.add (flatCountF cut ws) 1) (Nat.beq (Nat.land w cut) cut))
      (Nat.add (flatCountF cut ws) 1) (Nat.beq (Nat.land w cut) 0) =
      bsel (Nat.beq (canon cut w) 0) (flatCount cut ws + 1) (flatCount cut ws)
    rw [ih]
    rcases canon_cases cut w with ⟨h0, h1 | h2⟩ | ⟨hne, _⟩
    · have hb : Nat.beq (Nat.land w cut) 0 = true := Nat.beq_eq.mpr h1
      rw [h0, hb, Nat.beq_refl]; rfl
    · have hb : Nat.beq (Nat.land w cut) cut = true := Nat.beq_eq.mpr h2
      rw [h0, hb, Nat.beq_refl]; cases Nat.beq (Nat.land w cut) 0 <;> rfl
    · have h1 : Nat.beq (Nat.land w cut) 0 = false := beq_false_ne (fun e => by
        change w &&& cut = 0 at e; exact hne (by unfold canon; dsimp only; rw [e]; simp [bsel]))
      have h2 : Nat.beq (Nat.land w cut) cut = false := beq_false_ne (fun e => by
        change w &&& cut = cut at e; exact hne (by unfold canon; dsimp only; rw [e]; simp [bsel]))
      rw [h1, h2, beq_false_ne hne]; rfl

def availBF (bank : List Nat) (w : Nat) : Bool :=
  Bool.rec (memN w bank) true (Nat.beq w 0)

theorem availBF_eq (bank : List Nat) (w : Nat) : availBF bank w = availB bank w := by
  unfold availBF availB; rw [memN_eq]; cases Nat.beq w 0 <;> rfl

def recipeGateBinF (cut : Nat) (bank : List Nat) (vc ac bc : Nat) : Bool :=
  Bool.rec false
    (Bool.rec false
      (Bool.rec
        (Bool.rec
          (Bool.rec (Nat.beq vc (binOpF cut 3 ac bc)) true (Nat.beq vc (binOpF cut 2 ac bc)))
          true (Nat.beq vc (binOpF cut 1 ac bc)))
        true (Nat.beq vc (binOpF cut 0 ac bc)))
      (availBF bank bc))
    (availBF bank ac)

theorem recipeGateBinF_eq (cut : Nat) (bank : List Nat) (vc ac bc : Nat) :
    recipeGateBinF cut bank vc ac bc = recipeGateBin cut bank vc ac bc := by
  unfold recipeGateBinF recipeGateBin
  simp only [availBF_eq, binOpF_eq]
  cases availB bank ac <;> cases availB bank bc <;>
    cases Nat.beq vc (binOp cut 0 ac bc) <;> cases Nat.beq vc (binOp cut 1 ac bc) <;>
    cases Nat.beq vc (binOp cut 2 ac bc) <;> cases Nat.beq vc (binOp cut 3 ac bc) <;> rfl

def addUniqF (w : Nat) (l : List Nat) : List Nat :=
  Bool.rec (w :: l) l (memN w l)

theorem addUniqF_eq (w : Nat) (l : List Nat) : addUniqF w l = addUniq w l := by
  unfold addUniqF addUniq; rw [memN_eq]; cases l.contains w <;> rfl

def recipeStartF (cut : Nat) (stock ws : List Nat) : List Nat :=
  List.rec [] (fun w _ acc =>
    let v := canonF cut w
    Bool.rec (addUniqF v acc) acc (availBF stock v)) ws

theorem recipeStartF_eq (cut : Nat) (stock ws : List Nat) : recipeStartF cut stock ws = recipeStart cut stock ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (addUniqF (canonF cut w) (recipeStartF cut stock ws)) (recipeStartF cut stock ws) (availBF stock (canonF cut w)) =
      (if availB stock (canon cut w) then recipeStart cut stock ws else addUniq (canon cut w) (recipeStart cut stock ws))
    rw [ih, canonF_eq, availBF_eq, addUniqF_eq]; cases availB stock (canon cut w) <;> rfl

def recipeCloseF (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun (w, a, b) _ next acc =>
      let v := canonF cut w
      Bool.rec (next acc)
        (let va := canonF cut a
         let vb := canonF cut b
         let acc1 := Bool.rec (addUniqF va acc) acc (availBF stock va)
         let acc2 := Bool.rec (addUniqF vb acc1) acc1 (availBF stock vb)
         next acc2)
        (memN v acc)) hist needed

theorem recipeCloseF_eq (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) :
    recipeCloseF cut stock hist needed = recipeClose cut stock hist needed := by
  induction hist generalizing needed with
  | nil => rfl
  | cons rec hist ih =>
    obtain ⟨w, a, b⟩ := rec
    have hL : recipeCloseF cut stock ((w, a, b) :: hist) needed =
        Bool.rec (recipeCloseF cut stock hist needed)
          (let va := canonF cut a; let vb := canonF cut b
           let acc1 := Bool.rec (addUniqF va needed) needed (availBF stock va)
           let acc2 := Bool.rec (addUniqF vb acc1) acc1 (availBF stock vb)
           recipeCloseF cut stock hist acc2)
          (memN (canonF cut w) needed) := rfl
    have hR : recipeClose cut stock ((w, a, b) :: hist) needed =
        (if needed.contains (canon cut w) then
          let va := canon cut a; let vb := canon cut b
          let acc1 := if availB stock va then needed else addUniq va needed
          let acc2 := if availB stock vb then acc1 else addUniq vb acc1
          recipeClose cut stock hist acc2
        else recipeClose cut stock hist needed) := rfl
    rw [hL, hR]; dsimp only
    simp only [canonF_eq, memN_eq, availBF_eq, addUniqF_eq]
    cases needed.contains (canon cut w)
    · exact ih needed
    · dsimp only; rw [ih]
      cases availB stock (canon cut a) <;> cases availB stock (canon cut b) <;> rfl

def replayRecF (cut : Nat) (needed : List Nat) (hist : List (Nat × Nat × Nat)) (bank : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun _ => [])
    (fun (w, a, b) _ next bank =>
      let v := canonF cut w
      Bool.rec (next bank)
        (Bool.rec
          (Bool.rec (next bank) (v :: next (v :: bank))
            (recipeGateBinF cut bank v (canonF cut a) (canonF cut b)))
          (next bank) (availBF bank v))
        (memN v needed)) hist bank

theorem replayRecF_eq (cut : Nat) (needed : List Nat) (hist : List (Nat × Nat × Nat)) (bank : List Nat) :
    replayRecF cut needed hist bank = replayRec cut needed hist bank := by
  induction hist generalizing bank with
  | nil => rfl
  | cons rec hist ih =>
    obtain ⟨w, a, b⟩ := rec
    have hL : replayRecF cut needed ((w, a, b) :: hist) bank =
        let v := canonF cut w
        Bool.rec (replayRecF cut needed hist bank)
          (Bool.rec
            (Bool.rec (replayRecF cut needed hist bank) (v :: replayRecF cut needed hist (v :: bank))
              (recipeGateBinF cut bank v (canonF cut a) (canonF cut b)))
            (replayRecF cut needed hist bank) (availBF bank v))
          (memN v needed) := rfl
    have hR : replayRec cut needed ((w, a, b) :: hist) bank =
        (let v := canon cut w
         if needed.contains v && !(availB bank v) && recipeGateBin cut bank v (canon cut a) (canon cut b) then
           v :: replayRec cut needed hist (v :: bank)
         else replayRec cut needed hist bank) := rfl
    rw [hL, hR]; dsimp only
    simp only [canonF_eq, memN_eq, availBF_eq, recipeGateBinF_eq]
    rw [ih bank, ih (canon cut w :: bank)]
    cases needed.contains (canon cut w) <;> cases availB bank (canon cut w) <;>
      cases recipeGateBin cut bank (canon cut w) (canon cut a) (canon cut b) <;> rfl

def boundClosesF (state : Nat × List Nat × List (Nat × Nat × Nat))
    (bound : Nat × List Nat × Nat × Nat) : Bool :=
  let (cut, stock, lower, _) := bound
  let (fuel, ws, hist) := state
  forceW (Nat.sub fuel (flatCountF cut ws)) (fun rem =>
    Bool.rec false
      (forceWs (recipeStartF cut stock ws) (fun start =>
        Bool.rec false
          (forceWs (recipeCloseF cut stock hist start) (fun needed =>
            Bool.rec false
              (forceWs (replayRecF cut needed (revAccN hist []) stock) (fun replay =>
                Bool.rec false
                  (allN (fun w => availBF (appN replay stock) (canonF cut w)) ws)
                  (Nat.blt (Nat.add (lenN replay) rem) lower)))
              (Nat.blt (Nat.add (lenN needed) rem) lower)))
          (Nat.blt (Nat.add (lenN start) rem) lower)))
      (Nat.blt rem lower))

theorem boundClosesF_eq {target : Nat} {state : Nat × List Nat × List (Nat × Nat × Nat)}
    {bound : Nat × List Nat × Nat × Nat}
    (hg : canon bound.1 target = bound.2.2.2) (hnz : bound.2.2.2 ≠ 0) :
    boundClosesF state bound = boundCloses target state bound := by
  obtain ⟨fuel, ws, hist⟩ := state
  obtain ⟨cut, stock, lower, bgoal⟩ := bound
  dsimp only at hg hnz
  unfold boundClosesF boundCloses
  simp only [forceW_eq, forceWs_eq, flatCountF_eq, recipeStartF_eq, recipeCloseF_eq,
    replayRecF_eq, revAccN_eq, List.append_nil, lenN_eq, allN_eq, appN_eq, availBF_eq, canonF_eq,
    hg, Nat.beq_refl, beq_false_ne hnz, Bool.not_false, Bool.and_true, Bool.true_and]
  cases Nat.blt (fuel - flatCount cut ws) lower
  · rfl
  · cases Nat.blt ((recipeStart cut stock ws).length + (fuel - flatCount cut ws)) lower
    · rfl
    · cases Nat.blt ((recipeClose cut stock hist (recipeStart cut stock ws)).length + (fuel - flatCount cut ws)) lower
      · rfl
      · cases Nat.blt ((replayRec cut (recipeClose cut stock hist (recipeStart cut stock ws)) hist.reverse stock).length + (fuel - flatCount cut ws)) lower <;> rfl

def knownClosesF (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  List.rec false (fun b _ rest => Bool.rec rest true (boundClosesF state b)) bounds

theorem knownClosesF_eq {target : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 target = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    knownClosesF bounds state = knownCloses target bounds state := by
  induction bounds with
  | nil => rfl
  | cons b bs ih =>
    change Bool.rec (knownClosesF bs state) true (boundClosesF state b) =
      (boundCloses target state b || knownCloses target bs state)
    have h0 := hgoals b List.mem_cons_self
    rw [boundClosesF_eq h0.1 h0.2, ih (fun x hx => hgoals x (List.mem_cons_of_mem _ hx))]
    cases boundCloses target state b <;> rfl

def insertSortedF (x : Nat) (l : List Nat) : List Nat :=
  List.rec [x] (fun y ys ih => Bool.rec (y :: ih) (x :: y :: ys) (Nat.ble x y)) l

theorem insertSortedF_eq (x : Nat) (l : List Nat) : insertSortedF x l = insertSorted x l := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    change Bool.rec (y :: insertSortedF x ys) (x :: y :: ys) (Nat.ble x y) =
      bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys)
    rw [ih]; cases Nat.ble x y <;> rfl

def dropValF (drop : Bool) (x : Nat) (l : List Nat) : List Nat :=
  Bool.rec l (List.rec [] (fun y _ ih => Bool.rec (y :: ih) ih (Nat.beq y x)) l) drop

theorem dropValF_eq (drop : Bool) (x : Nat) (l : List Nat) : dropValF drop x l = dropVal drop x l := by
  cases drop
  · rfl
  · induction l with
    | nil => rfl
    | cons y ys ih =>
      change Bool.rec (y :: dropValF true x ys) (dropValF true x ys) (Nat.beq y x) =
        bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys)
      rw [ih]; cases Nat.beq y x <;> rfl

def subsetWordsF (stock : List Nat) (bits : Nat) : List Nat :=
  (List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun w _ ih b =>
      let rest := ih (Nat.shiftRight b 1)
      Bool.rec rest (insertSortedF w rest) (Nat.beq (Nat.land b 1) 1)) stock) bits

theorem subsetWordsF_eq (stock : List Nat) (bits : Nat) : subsetWordsF stock bits = subsetWords stock bits := by
  induction stock generalizing bits with
  | nil => rfl
  | cons x xs ih =>
    change Bool.rec (subsetWordsF xs (Nat.shiftRight bits 1))
      (insertSortedF x (subsetWordsF xs (Nat.shiftRight bits 1))) (Nat.beq (Nat.land bits 1) 1) =
      bsel (Nat.beq (bits &&& 1) 1) (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1))
    rw [ih, insertSortedF_eq]; cases Nat.beq (bits &&& 1) 1 <;> rfl

def childStateF (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  let (fuel, ws, hist) := state
  let keep := Nat.land token 3
  let op := Nat.land (Nat.shiftRight token 2) 3
  let b := Nat.land (Nat.shiftRight token 4) 15
  let a := Nat.shiftRight token 8
  Bool.rec
    (Bool.rec none
      (Bool.rec none
        (let x := getDN ws a
         let y := getDN ws b
         let z := binOpF mask op x y
         Bool.rec
           (Bool.rec
             (let keepA := Nat.beq (Nat.land keep 1) 1
              let keepB := Nat.beq (Nat.land (Nat.shiftRight keep 1) 1) 1
              let rest := dropValF (Bool.rec true false keepA) x (dropValF (Bool.rec true false keepB) y ws)
              some (Nat.sub fuel 1, insertSortedF z rest, (z, x, y) :: hist))
             none (memN z ws))
           none (Nat.beq z 0))
        (Nat.blt b (lenN ws)))
      (Nat.blt a b))
    none (Nat.beq fuel 0)

theorem childStateF_eq (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    childStateF mask token state = childState mask token state := by
  obtain ⟨fuel, ws, hist⟩ := state
  unfold childStateF childState
  simp only [lenN_eq, getDN_eq, binOpF_eq, memN_eq, dropValF_eq, insertSortedF_eq]
  cases Nat.beq fuel 0
  · cases Nat.blt (token >>> 8) ((token >>> 4) &&& 15)
    · rfl
    · cases Nat.blt ((token >>> 4) &&& 15) ws.length
      · rfl
      · cases Nat.beq (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0) (ws.getD ((token >>> 4) &&& 15) 0)) 0
        · cases ws.contains (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0) (ws.getD ((token >>> 4) &&& 15) 0))
          · cases Nat.beq ((token &&& 3) &&& 1) 1 <;> cases Nat.beq (((token &&& 3) >>> 1) &&& 1) 1 <;> rfl
          · rfl
        · rfl
  · rfl

def dagTraceF (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
    (fun _ prev j =>
      let (parent, token) := forest j
      Bool.rec
        (match prev (Nat.sub parent 1) with
         | none => none
         | some st => childStateF mask token st)
        (Bool.rec none (some (fuel, subsetWordsF stock token, []))
          (Nat.blt token (Nat.shiftLeft 1 (lenN stock))))
        (Nat.beq parent 0)) (Nat.add fuel 1)) i

theorem dagTraceF_eq (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    dagTraceF mask stock fuel forest i = dagTrace mask stock fuel forest i := by
  unfold dagTraceF dagTrace
  suffices ∀ steps j,
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          Bool.rec
            (match prev (Nat.sub parent 1) with
             | none => none
             | some st => childStateF mask token st)
            (Bool.rec none (some (fuel, subsetWordsF stock token, []))
              (Nat.blt token (Nat.shiftLeft 1 (lenN stock))))
            (Nat.beq parent 0)) steps) j =
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) steps) j from
    this (fuel + 1) i
  intro steps
  induction steps with
  | zero => intro j; rfl
  | succ n ih =>
    intro j
    dsimp only
    have hpow : Nat.shiftLeft 1 (lenN stock) = 2 ^ stock.length := by
      rw [lenN_eq]; change 1 <<< stock.length = _; rw [Nat.shiftLeft_eq, Nat.one_mul]
    cases Nat.beq (forest j).1 0
    · dsimp only
      rw [ih]
      cases (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          if Nat.beq (forest k).1 0 then
            if Nat.blt (forest k).2 (2 ^ stock.length) then some (rootState stock fuel (forest k).2) else none
          else (prev ((forest k).1 - 1)).bind (childState mask (forest k).2)) n) ((forest j).1 - 1)
      · rfl
      · exact childStateF_eq mask (forest j).2 _
    · dsimp only
      rw [hpow, subsetWordsF_eq]
      cases Nat.blt (forest j).2 (2 ^ stock.length) <;> rfl

def dagLocalF (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  let (fuel, ws, _) := state
  Bool.rec
    (Bool.rec true
      (knownClosesF bounds state)
      (dagPartF ws goal (Nat.xor mask goal)))
    true (Nat.blt (Nat.add fuel 1) (lenN ws))

theorem dagLocalF_eq {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    dagLocalF mask goal bounds state = dagLocal mask goal bounds state := by
  obtain ⟨fuel, ws, hist⟩ := state
  unfold dagLocalF dagLocal; dsimp only
  rw [lenN_eq, dagPartF_eq, knownClosesF_eq hgoals]
  cases Nat.blt (fuel + 1) ws.length <;> cases dagPart ws goal (mask ^^^ goal) <;> rfl

def dagRefF (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (parent token : Nat)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  match links parent token with
  | none => false
  | some dest =>
    Bool.rec false
      (match states dest with
       | none => false
       | some saved => Bool.rec false (eqListN saved.2.1 state.2.1) (Nat.beq saved.1 state.1))
      (Nat.blt dest count)

theorem dagRefF_eq (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (parent token : Nat)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    dagRefF count states links parent token state = dagRef count states links parent token state := by
  unfold dagRefF dagRef
  cases links parent token with
  | none => rfl
  | some dest =>
    dsimp only
    cases Nat.blt dest count
    · rfl
    · dsimp only
      cases states dest with
      | none => rfl
      | some saved =>
        dsimp only
        rw [eqListN_eq]; cases Nat.beq saved.1 state.1 <;> rfl

def treeBlockF (lo hi : Nat) (f : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ next a b =>
      Bool.rec true
        (let m := Nat.shiftRight (Nat.add a b) 1
         Bool.rec (Bool.rec false (next m b) (next a m)) (f a) (Nat.beq a m))
        (Nat.blt a b)) (Nat.add (Nat.sub hi lo) 1)) lo hi

theorem treeBlockF_eq (lo hi : Nat) (f : Nat → Bool) : treeBlockF lo hi f = treeBlock lo hi f := by
  unfold treeBlockF treeBlock
  suffices ∀ steps a b,
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          Bool.rec true
            (let m := Nat.shiftRight (Nat.add x y) 1
             Bool.rec (Bool.rec false (next m y) (next x m)) (f x) (Nat.beq x m))
            (Nat.blt x y)) steps) a b =
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          if Nat.blt x y then
            let m := (x + y) / 2
            if Nat.beq x m then f x else next x m && next m y
          else true) steps) a b from
    this (hi - lo + 1) lo hi
  intro steps
  induction steps with
  | zero => intro a b; rfl
  | succ s ih =>
    intro a b
    dsimp only
    have hdiv : Nat.shiftRight (Nat.add a b) 1 = (a + b) / 2 := by
      change (a + b) >>> 1 = (a + b) / 2; rw [Nat.shiftRight_eq_div_pow]
    rw [hdiv]
    cases Nat.blt a b
    · rfl
    · cases Nat.beq a ((a + b) / 2)
      · rw [ih, ih]
        change Bool.rec false _ _ = (_ && _)
        cases (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true) _ s) a ((a + b) / 2) <;> rfl
      · rfl

def dagCheckChildrenF (mask goal : Nat) (bounds : Nat → List (Nat × List Nat × Nat × Nat))
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  let (fuel, ws, hist) := state
  let n := lenN ws
  Bool.rec
    (Bool.rec
      (Bool.rec false
        (treeBlockF 0 n (fun a =>
          let x := getDN ws a
          treeBlockF (Nat.add a 1) n (fun b =>
            let y := getDN ws b
            treeBlockF 0 4 (fun op =>
              forceW (binOpF mask op x y) (fun z =>
                Bool.rec
                  (Bool.rec
                    (treeBlockF 0 4 (fun keep =>
                      let keepA := Nat.beq (Nat.land keep 1) 1
                      let keepB := Nat.beq (Nat.land (Nat.shiftRight keep 1) 1) 1
                      let newLen := Nat.add (Nat.add (Nat.sub n 1) (Bool.rec 0 1 keepA)) (Bool.rec 0 1 keepB)
                      Bool.rec
                        (forceWs (insertSortedF z (dropValF (Bool.rec true false keepA) x (dropValF (Bool.rec true false keepB) y ws))) (fun ws' =>
                          let ch := (Nat.sub fuel 1, ws', (z, x, y) :: hist)
                          let tok := Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) op) 2) keep
                          Bool.rec (ref tok ch) true (dagLocalF mask goal (bounds tok) ch)))
                        true (Nat.blt fuel newLen)))
                    true (memN z ws))
                  true (Nat.beq z 0))))))
        (Nat.blt n 17))
      true (Nat.beq fuel 0))
    false (memN goal ws)

theorem makeTokenF_eq (a b op keep : Nat) :
    Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) op) 2) keep =
    makeToken a b op keep := by
  unfold makeToken
  change ((((a <<< 4) + b) <<< 2) + op) <<< 2 + keep = _
  simp only [Nat.shiftLeft_eq]

theorem localOr (a b : Bool) : Bool.rec b true a = (a || b) := by
  cases a <;> rfl

set_option maxHeartbeats 1000000 in
theorem dagCheckChildrenF_eq {mask goal : Nat} {bounds : Nat → List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ tok, ∀ b ∈ bounds tok, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    dagCheckChildrenF mask goal bounds ref state = dagCheckChildren mask goal bounds ref state := by
  obtain ⟨fuel, ws, hist⟩ := state
  unfold dagCheckChildrenF dagCheckChildren; dsimp only
  simp only [lenN_eq, memN_eq, treeBlockF_eq]
  cases ws.contains goal
  · cases Nat.beq fuel 0
    · cases Nat.blt ws.length 17
      · rfl
      · dsimp only
        simp only [Bool.not_false, Bool.true_and, Bool.false_or]
        apply congrArg (treeBlock 0 ws.length); funext a
        simp only [getDN_eq]
        apply congrArg (treeBlock (a + 1) ws.length); funext b
        apply congrArg (treeBlock 0 4); funext op
        simp only [binOpF_eq, forceW_eq]
        cases Nat.beq (binOp mask op (ws.getD a 0) (ws.getD b 0)) 0
        · cases ws.contains (binOp mask op (ws.getD a 0) (ws.getD b 0))
          · dsimp only; simp only [Bool.false_or]
            apply congrArg (treeBlock 0 4); funext keep
            simp only [insertSortedF_eq, dropValF_eq, forceWs_eq, makeTokenF_eq,
              dagLocalF_eq (hgoals (makeToken a b op keep)), localOr]
            cases Nat.beq (keep &&& 1) 1 <;> cases Nat.beq ((keep >>> 1) &&& 1) 1
            all_goals dsimp only
            all_goals simp only [Bool.false_eq_true, ite_true, ite_false, Bool.not_true, Bool.not_false]
            all_goals cases Nat.blt fuel _
            all_goals rfl
          · rfl
        · rfl
    · rfl
  · rfl

def dagCheckNodeF (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some st => dagCheckChildrenF mask goal (fun _ => bounds) (dagRefF count states links (Nat.add i 1)) st

theorem dagCheckNodeF_eq {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (i : Nat) :
    dagCheckNodeF mask goal bounds count states links i = dagCheckNode mask goal bounds count states links i := by
  unfold dagCheckNodeF dagCheckNode
  cases states i with
  | none => rfl
  | some st =>
    have href : dagRefF count states links (Nat.add i 1) = dagRef count states links (i + 1) := by
      funext tok s; exact dagRefF_eq count states links (i + 1) tok s
    rw [href]; exact dagCheckChildrenF_eq (fun _ => hgoals) _ st

def dagCheckRootsF (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (stock : List Nat) (fuel : Nat) : Bool :=
  treeBlockF 0 (Nat.shiftLeft 1 (lenN stock)) (fun token =>
    forceWs (subsetWordsF stock token) (fun ws =>
      let st := (fuel, ws, [])
      Bool.rec (dagLocalF mask goal bounds st) true (ref token st)))

theorem dagCheckRootsF_eq {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (stock : List Nat) (fuel : Nat) :
    dagCheckRootsF mask goal bounds ref stock fuel = dagCheckRoots mask goal bounds ref stock fuel := by
  unfold dagCheckRootsF dagCheckRoots
  have hpow : Nat.shiftLeft 1 (lenN stock) = 2 ^ stock.length := by
    rw [lenN_eq]; change 1 <<< stock.length = _; rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [hpow, treeBlockF_eq]
  congr 1; funext tok
  simp only [subsetWordsF_eq, forceWs_eq, dagLocalF_eq hgoals]
  cases ref tok (fuel, subsetWords stock tok, []) <;> cases dagLocal mask goal bounds (fuel, subsetWords stock tok, []) <;> rfl

def unpackF (data width idx : Nat) : Nat :=
  Nat.land (Nat.shiftRight data (Nat.mul idx width)) (Nat.sub (Nat.shiftLeft 1 width) 1)

def unpackForestF (data pBits tBits : Nat) : Nat → Nat × Nat := fun i =>
  let w := Nat.add pBits tBits
  let code := unpackF data w i
  (Nat.shiftRight code tBits, Nat.land code (Nat.sub (Nat.shiftLeft 1 tBits) 1))

def unpackLinksF (index data idxW sizeBits tokBits destBits steps : Nat) : Nat → Nat → Option Nat :=
  fun parent tok =>
    let entry := unpackF index idxW parent
    let sz := Nat.land entry (Nat.sub (Nat.shiftLeft 1 sizeBits) 1)
    let off := Nat.shiftRight entry sizeBits
    let w := Nat.add tokBits destBits
    (Nat.rec (motive := fun _ => Nat → Nat → Option Nat) (fun _ _ => none)
      (fun _ next lo hi =>
        Bool.rec none
          (let mid := Nat.shiftRight (Nat.add lo hi) 1
           let code := unpackF data w mid
           let key := Nat.land code (Nat.sub (Nat.shiftLeft 1 tokBits) 1)
           Bool.rec
             (Bool.rec (next (Nat.add mid 1) hi) (next lo mid) (Nat.blt tok key))
             (some (Nat.shiftRight code tokBits)) (Nat.beq tok key))
          (Nat.blt lo hi)) steps) off (Nat.add off sz)

theorem lowerDagF {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {links : Nat → Nat → Option Nat}
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hroots : dagCheckRootsF mask goal bounds
      (dagRefF count (dagTraceF mask stock fuel forest) links 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeF mask goal bounds count
      (dagTraceF mask stock fuel forest) links i = true) :
    LowerBin mask stock goal (fuel + 1) := by
  have htr : dagTraceF mask stock fuel forest = dagTrace mask stock fuel forest := by
    funext i; exact dagTraceF_eq mask stock fuel forest i
  rw [htr] at hroots hnodes
  have hr : dagCheckRoots mask goal bounds (dagRef count (dagTrace mask stock fuel forest) links 0) stock fuel = true := by
    have href : dagRefF count (dagTrace mask stock fuel forest) links 0 = dagRef count (dagTrace mask stock fuel forest) links 0 := by
      funext t s; exact dagRefF_eq count _ links 0 t s
    rw [href, dagCheckRootsF_eq hgoals] at hroots; exact hroots
  have hn : ∀ i, 0 ≤ i → i < count → dagCheckNode mask goal bounds count (dagTrace mask stock fuel forest) links i = true := by
    intro i h1 h2
    have h := hnodes i h1 h2
    rwa [dagCheckNodeF_eq hgoals] at h
  exact lowerDag hgm hgnz hcs snd hknown hsub hr hn

theorem treeBlockF_at {lo hi : Nat} {f : Nat → Bool} (h : treeBlockF lo hi f = true) :
    ∀ {i : Nat}, lo ≤ i → i < hi → f i = true := by
  rw [treeBlockF_eq] at h; exact treeBlock_at h

def hintWordAt (pages : List (Nat × Nat × Nat)) (i : Nat) : Nat :=
  let page := pages.getD (Nat.shiftRight i 5) (0, 1, 0)
  let j := Nat.land i 31
  let first := unpackF page.1 page.2.1 j
  let last := unpackF page.1 page.2.1 (Nat.add j 1)
  Nat.land (Nat.shiftRight page.2.2 first) (Nat.sub (Nat.shiftLeft 1 (Nat.sub last first)) 1)

def hintCut (word token : Nat) : Nat :=
  (Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 63)
    (fun _ next at' =>
      forceW (Nat.shiftRight word at') (fun info =>
        Bool.rec
          (let bit := Nat.land (Nat.shiftRight info 1) 15
           let leftLeaves := Nat.land (Nat.shiftRight info 5) 63
           next (Bool.rec (Nat.add at' 11) (Nat.add at' (Nat.mul leftLeaves 18)) (Nat.testBit token bit)))
          (Nat.land (Nat.shiftRight info 1) 63) (Nat.beq (Nat.land info 1) 0))) 13) 0

def hintedBounds (chunks : List (List (Nat × List Nat × Nat × Nat))) (word token : Nat) :
    List (Nat × List Nat × Nat × Nat) :=
  forceW (hintCut word token) fun i =>
    match chunks[Nat.shiftRight i 3]? with
    | none => []
    | some chunk =>
      match chunk[Nat.land i 7]? with
      | none => []
      | some b => [b]

theorem hintedBounds_mem {chunks : List (List (Nat × List Nat × Nat × Nat))}
    {word token : Nat} {b : Nat × List Nat × Nat × Nat}
    (hb : b ∈ hintedBounds chunks word token) : b ∈ chunks.flatten := by
  simp only [hintedBounds, forceW_eq] at hb
  split at hb
  · simp at hb
  · rename_i chunk hchunk
    split at hb
    · simp at hb
    · rename_i a ha
      have eq : b = a := List.mem_singleton.mp hb
      subst b
      exact List.mem_flatten.mpr ⟨chunk, List.mem_of_getElem? hchunk, List.mem_of_getElem? ha⟩

-- The general checker is from barelyanything's pull request 54457.

theorem blockSpec {f : Nat → Bool} {lo hi : Nat} (h : treeBlockF lo hi f = true) :
    ∀ i, lo ≤ i → i < hi → f i = true := fun _ hlo hhi => treeBlockF_at h hlo hhi

theorem joinBlockSpecs {f : Nat → Bool} {lo mid hi : Nat}
    (first : ∀ i, lo ≤ i → i < mid → f i = true)
    (last : ∀ i, mid ≤ i → i < hi → f i = true) :
    ∀ i, lo ≤ i → i < hi → f i = true := by
  intro i hlo hhi
  by_cases h : i < mid
  · exact first i hlo h
  · exact last i (by omega) hhi


section Relabel

variable {n r : Nat}


def rowPull (p : Fin r → Fin n) (w : Nat) : Nat :=
  (BitVec.ofBoolListLE (List.ofFn fun i : Fin r => w.testBit (p i).val)).toNat

theorem rowPull_testBit (p : Fin r → Fin n) (w i : Nat) :
    (rowPull p w).testBit i = if h : i < r then w.testBit (p ⟨i, h⟩).val else false := by
  simp only [rowPull, BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : i < r <;> simp [h]

theorem rowPull_bit (p : Fin r → Fin n) (w : Nat) (i : Fin r) :
    (rowPull p w).testBit i.val = w.testBit (p i).val := by
  simp only [rowPull_testBit, i.isLt, dite_true]

theorem rowPull_zero (p : Fin r → Fin n) : rowPull p 0 = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : i < r <;> simp [rowPull_testBit, h]

theorem rowPull_and (p : Fin r → Fin n) (a b : Nat) :
    rowPull p (a &&& b) = rowPull p a &&& rowPull p b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : i < r <;> simp [rowPull_testBit, h]

theorem rowPull_or (p : Fin r → Fin n) (a b : Nat) :
    rowPull p (a ||| b) = rowPull p a ||| rowPull p b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : i < r <;> simp [rowPull_testBit, h]

theorem rowPull_xor (p : Fin r → Fin n) (a b : Nat) :
    rowPull p (a ^^^ b) = rowPull p a ^^^ rowPull p b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : i < r <;> simp [rowPull_testBit, h]

def rowCanon (p : Fin r → Fin n) (mask w : Nat) : Nat :=
  canon (rowPull p mask) (rowPull p w)

theorem rowCanon_zero (p : Fin r → Fin n) (mask : Nat) : rowCanon p mask 0 = 0 := by
  rw [rowCanon, rowPull_zero, canon_zero]

theorem rowCanon_canon (p : Fin r → Fin n) (mask w : Nat) :
    rowCanon p mask (canon mask w) = rowCanon p mask w := by
  have cut : rowCanon p mask (w &&& mask) = rowCanon p mask w := by
    rw [rowCanon, rowPull_and, canon_land]
    rfl
  rcases canon_cases mask w with ⟨h0, hz | hm⟩ | ⟨_, h | h⟩
  · rw [h0, rowCanon_zero, ← cut, hz, rowCanon_zero]
  · rw [h0, rowCanon_zero, ← cut, hm, rowCanon, canon_self]
  · rw [h, cut]
  · rw [h, rowCanon, rowPull_xor, canon_xor_mask]
    exact cut

private theorem rowCanon_binOp (p : Fin r → Fin n) (mask op a b : Nat) (hop : op < 4) :
    rowCanon p mask (binOp mask op a b) = 0 ∨
    rowCanon p mask (binOp mask op a b) = rowCanon p mask a ∨
    rowCanon p mask (binOp mask op a b) = rowCanon p mask b ∨
    ∃ k < 4, rowCanon p mask (binOp mask op a b) =
      binOp (rowPull p mask) k (rowCanon p mask a) (rowCanon p mask b) := by
  rcases (show op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 by omega) with rfl | rfl | rfl | rfl
  · rw [show binOp mask 0 a b = canon mask (a &&& b) from rfl, rowCanon_canon]
    simp only [rowCanon, rowPull_and]
    exact canon_and_in_binOp _ _ _
  · rw [show binOp mask 1 a b = canon mask (a ||| b) from rfl, rowCanon_canon]
    simp only [rowCanon, rowPull_or]
    exact canon_or_in_binOp _ _ _
  · rw [show binOp mask 2 a b = canon mask (a &&& (mask ^^^ b)) from rfl, rowCanon_canon]
    simp only [rowCanon, rowPull_and, rowPull_xor]
    simpa only [canon_xor_mask] using
      canon_and_in_binOp (rowPull p mask) (rowPull p a) (rowPull p mask ^^^ rowPull p b)
  · rw [show binOp mask 3 a b = canon mask ((mask ^^^ a) &&& b) from rfl, rowCanon_canon]
    simp only [rowCanon, rowPull_and, rowPull_xor]
    simpa only [canon_xor_mask] using
      canon_and_in_binOp (rowPull p mask) (rowPull p mask ^^^ rowPull p a) (rowPull p b)

theorem avail_rowPull (p : Fin r → Fin n) {mask w : Nat} {bank bank' : List Nat}
    (stocked : ∀ u ∈ bank, Avail bank' (rowCanon p mask u)) (h : Avail bank w) :
    Avail bank' (rowCanon p mask w) := by
  rcases h with rfl | h
  · exact .inl (rowCanon_zero p mask)
  · exact stocked _ h

private theorem gateBin_copy {mask w : Nat} {bank : List Nat} (h : Avail bank w)
    (hc : canon mask w = w) : GateBin mask bank w := by
  refine ⟨w, w, 0, by omega, h, h, ?_⟩
  change w = canon mask (w &&& w)
  rw [Nat.and_self, hc]

theorem gateBin_rowPull (p : Fin r → Fin n) {mask w : Nat} {bank bank' : List Nat}
    (stocked : ∀ u ∈ bank, Avail bank' (rowCanon p mask u)) (h : GateBin mask bank w) :
    GateBin (rowPull p mask) bank' (rowCanon p mask w) := by
  obtain ⟨a, b, op, hop, ha, hb, rfl⟩ := h
  have ha' := avail_rowPull p stocked ha
  have hb' := avail_rowPull p stocked hb
  have hcanon := canon_idem (rowPull p mask) (rowPull p (binOp mask op a b))
  rcases rowCanon_binOp p mask op a b hop with h0 | h1 | h2 | ⟨k, hk, hv⟩
  · exact gateBin_copy (.inl h0) hcanon
  · exact gateBin_copy (h1.symm ▸ ha') hcanon
  · exact gateBin_copy (h2.symm ▸ hb') hcanon
  · exact ⟨_, _, k, hk, ha', hb', hv⟩

theorem buildsBin_rowPull (p : Fin r → Fin n) {mask : Nat} {bank bank' vs : List Nat}
    (stocked : ∀ u ∈ bank, Avail bank' (rowCanon p mask u)) (h : BuildsBin mask bank vs) :
    BuildsBin (rowPull p mask) bank' (vs.map (rowCanon p mask)) := by
  induction vs generalizing bank bank' with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨gateBin_rowPull p stocked h.1, ih ?_ h.2⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact .inr List.mem_cons_self
    · rcases stocked w hw with h0 | hmem
      · exact .inl h0
      · exact .inr (List.mem_cons_of_mem _ hmem)

theorem lowerBin_of_rowPull (p : Fin r → Fin n) {mask goal k : Nat} {stock stock' : List Nat}
    (stocked : ∀ w ∈ stock, Avail stock' (rowCanon p mask w))
    (known : LowerBin (rowPull p mask) stock' (rowCanon p mask goal) k) :
    LowerBin mask stock goal k := by
  intro vs circuit hit
  have projected := buildsBin_rowPull p stocked circuit
  have output : Avail (vs.map (rowCanon p mask) ++ stock') (rowCanon p mask goal) := by
    apply avail_rowPull p _ hit
    intro w hw
    rcases List.mem_append.mp hw with hvs | hs
    · exact .inr (List.mem_append_left _ (List.mem_map_of_mem hvs))
    · rcases stocked w hs with h0 | hmem
      · exact .inl h0
      · exact .inr (List.mem_append_right _ hmem)
  simpa only [List.length_map] using known _ projected output

theorem rowPull_inverse (p : Equiv.Perm (Fin n)) (w : Nat) :
    rowPull p.symm (rowPull p w) = w % 2 ^ n := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : i < n
  · let j : Fin n := ⟨i, h⟩
    simp only [Nat.testBit_mod_two_pow, h, decide_true, Bool.true_and]
    change (rowPull p.symm (rowPull p w)).testBit j.val = w.testBit j.val
    rw [rowPull_bit p.symm, rowPull_bit p, Equiv.apply_symm_apply]
  · simp [rowPull_testBit, Nat.testBit_mod_two_pow, h]

private theorem canon_before_width {mask : Nat} (h : mask < 2 ^ n) (w : Nat) :
    canon mask (w % 2 ^ n) = canon mask w := by
  rw [← canon_land mask (w % 2 ^ n), ← canon_land mask w]
  congr 1
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · simp [Nat.testBit_and, Nat.testBit_mod_two_pow, hi]
  · have hz : mask.testBit i = false := Nat.testBit_lt_two_pow
      (h.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_of_not_lt hi)))
    simp [Nat.testBit_and, hz]

theorem rowCanon_inverse (p : Equiv.Perm (Fin n)) {mask : Nat} (h : mask < 2 ^ n) (w : Nat) :
    rowCanon p.symm (rowPull p mask) (rowCanon p mask w) = canon mask w := by
  change rowCanon p.symm (rowPull p mask) (canon (rowPull p mask) (rowPull p w)) = canon mask w
  rw [rowCanon_canon, rowCanon, rowPull_inverse p mask, rowPull_inverse p w,
    Nat.mod_eq_of_lt h, canon_before_width h]

theorem rowCanon_injective_on_canon (p : Equiv.Perm (Fin n)) {mask a b : Nat}
    (hm : mask < 2 ^ n) (ha : canon mask a = a) (hb : canon mask b = b)
    (h : rowCanon p mask a = rowCanon p mask b) : a = b := by
  have e := congrArg (rowCanon p.symm (rowPull p mask)) h
  simpa only [rowCanon_inverse p hm, ha, hb] using e

end Relabel


def decodeRows (code : Nat) (i : Fin 64) : Fin 64 :=
  ⟨Nat.mod (Nat.shiftRight code (Nat.mul i.val 6)) 64, Nat.mod_lt _ (by decide)⟩

abbrev DagState := Nat × List Nat × List (Nat × Nat × Nat)

def RefSound (mask goal count : Nat) (states : Nat → Option DagState)
    (ref : Nat → Nat → DagState → Bool) : Prop :=
  ∀ parent tok st, ref parent tok st = true →
    ∃ dest saved, dest < count ∧ states dest = some saved ∧ saved.1 = st.1 ∧
      ∀ k, LiveBin mask goal k st.2.1.toFinset → LiveBin mask goal k saved.2.1.toFinset

def checkNodeVia (mask goal : Nat) (bounds : Nat → List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option DagState) (ref : Nat → Nat → DagState → Bool) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some st => dagCheckChildren mask goal bounds (ref (i + 1)) st

theorem dagAllNodesRef {mask goal fuel count : Nat} {stock : List Nat}
    {boundsFor : Nat → Nat → List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {ref : Nat → Nat → DagState → Bool}
    (hgm : Masked mask goal) (hknown : ∀ i tok, KnownBin (boundsFor i tok))
    (hsub : ∀ i tok, ∀ b ∈ boundsFor i tok, mask &&& b.1 = b.1) (snd : stock.Nodup)
    (good : RefSound mask goal count (dagTrace mask stock fuel forest) ref)
    (hnodes : ∀ i, 0 ≤ i → i < count → checkNodeVia mask goal (boundsFor i)
      (dagTrace mask stock fuel forest) ref i = true) :
    ∀ cap i st, i < count → dagTrace mask stock fuel forest i = some st →
      st.1 = cap → ∀ k, k ≤ cap → ¬LiveBin mask goal k st.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i st hi htr hcap k hk hlive
    obtain ⟨rem, ws, hist⟩ := st
    dsimp only at hcap hlive
    have nd : ws.Nodup := dagTrace_nodup snd htr
    have hchk := hnodes i (Nat.zero_le i) hi
    unfold checkNodeVia at hchk
    rw [htr] at hchk
    unfold dagCheckChildren at hchk
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, Nat.beq_eq, Nat.blt_eq] at hchk
    obtain ⟨hnohit, hstep⟩ := hchk
    generalize hS : ws.toFinset = S at hlive
    cases hlive with
    | done =>
      have hgm' : goal ∈ ws := List.mem_toFinset.mp (hS.symm ▸ Finset.mem_singleton_self goal)
      have hc : ws.contains goal = true := List.contains_iff_mem.mpr hgm'
      rw [hc] at hnohit; exact Bool.noConfusion hnohit
    | @step k' _ a0 b0 op0 ha0 hb0 hab0 _ _ hop0 hz0 hf0 keepA0 keepB0 tail0 =>
      rw [← hS] at ha0 hb0 hf0 tail0
      have hrem_pos : rem ≠ 0 := by omega
      rcases hstep with hrem0 | ⟨hn17, hblock⟩
      · exact hrem_pos hrem0
      · have haM : a0 ∈ ws := List.mem_toFinset.mp ha0
        have hbM : b0 ∈ ws := List.mem_toFinset.mp hb0
        obtain ⟨ia0, hia0, hea0⟩ := getElem_index_lt haM
        obtain ⟨ib0, hib0, heb0⟩ := getElem_index_lt hbM
        have hiab_ne : ia0 ≠ ib0 := fun heq => hab0 (hea0.symm.trans (heq ▸ heb0))
        have ⟨a, b, op, keepA, keepB, ha_lt, hab_lt, hb_lt, hop_lt, hax, hby, hzeq, htail⟩ :
            ∃ a b op keepA keepB, a < ws.length ∧ a < b ∧ b < ws.length ∧ op < 4 ∧
              ws.getD a 0 = (if ia0 < ib0 then a0 else b0) ∧
              ws.getD b 0 = (if ia0 < ib0 then b0 else a0) ∧
              binOp mask op (ws.getD a 0) (ws.getD b 0) = binOp mask op0 a0 b0 ∧
              LiveBin mask goal k' (insert (binOp mask op (ws.getD a 0) (ws.getD b 0))
                (dropIf (!keepA) (ws.getD a 0) (dropIf (!keepB) (ws.getD b 0) ws.toFinset))) := by
          by_cases hlt : ia0 < ib0
          · exact ⟨ia0, ib0, op0, keepA0, keepB0, hia0, hlt, hib0, hop0,
              by simp only [hlt, ite_true]; exact hea0,
              by simp only [hlt, ite_true]; exact heb0,
              by rw [hea0, heb0], by rw [hea0, heb0]; exact tail0⟩
          · obtain ⟨op1, hop1, hopEq⟩ := binOp_comm mask op0 a0 b0 hop0
            have hswap : dropIf (!keepB0) b0 (dropIf (!keepA0) a0 ws.toFinset) =
                dropIf (!keepA0) a0 (dropIf (!keepB0) b0 ws.toFinset) := by
              ext w; simp only [dropIf]; cases keepA0 <;> cases keepB0 <;> simp [Finset.mem_erase, and_left_comm]
            exact ⟨ib0, ia0, op1, keepB0, keepA0, hib0, by omega, hia0, hop1,
              by simp only [hlt, ite_false]; exact heb0,
              by simp only [hlt, ite_false]; exact hea0,
              by rw [hea0, heb0, hopEq],
              by rw [hea0, heb0, ← hopEq, hswap]; exact tail0⟩
        set x := ws.getD a 0
        set y := ws.getD b 0
        set z := binOp mask op x y
        set keep := (if keepA then 1 else 0) + (if keepB then 2 else 0)
        have hkeep_lt : keep < 4 := by cases keepA <;> cases keepB <;> simp [keep]
        have hkA : Nat.beq (keep &&& 1) 1 = keepA := by cases keepA <;> cases keepB <;> decide
        have hkB : Nat.beq ((keep >>> 1) &&& 1) 1 = keepB := by cases keepA <;> cases keepB <;> decide
        have hkA' : (keep &&& 1 = 1) ↔ keepA = true := by cases keepA <;> cases keepB <;> decide
        have hkB' : ((keep >>> 1) &&& 1 = 1) ↔ keepB = true := by cases keepA <;> cases keepB <;> decide
        have hA := treeBlock_at hblock (Nat.zero_le a) ha_lt
        have hB := treeBlock_at hA (by omega : a + 1 ≤ b) hb_lt
        have hO := treeBlock_at hB (Nat.zero_le op) hop_lt
        simp only [forceW_eq, Bool.or_eq_true, Nat.beq_eq] at hO
        have hznz : z ≠ 0 := hzeq.symm ▸ hz0
        have hznm : ws.contains z = false := by
          cases h : ws.contains z
          · rfl
          · exact absurd (List.mem_toFinset.mpr (List.contains_iff_mem.mp h)) (hzeq.symm ▸ hf0)
        rcases hO with (hz' | hcm) | hK
        · exact hznz hz'
        · rw [hznm] at hcm; exact Bool.noConfusion hcm
        · have hKe := treeBlock_at hK (Nat.zero_le keep) hkeep_lt
          simp only [hkA, hkB, hkA', hkB', forceWs_eq, Bool.or_eq_true, Nat.blt_eq] at hKe
          set ws' := insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))
          have hxM : x ∈ ws := by simp only [x, hax]; split; exact haM; exact hbM
          have hyM : y ∈ ws := by simp only [y, hby]; split; exact hbM; exact haM
          have hxy : x ≠ y := by simp only [x, y, hax, hby]; split; exact hab0; exact hab0.symm
          have hzNotW : z ∉ ws := fun hm => by
            have := List.contains_iff_mem.mpr hm; rw [hznm] at this; exact Bool.noConfusion this
          have hnd' : ws'.Nodup :=
            insertSorted_nodup (fun hm => hzNotW (dropVal_mem.mp (dropVal_mem.mp hm).1).1) (dropVal_nodup (dropVal_nodup nd))
          have hset' : ws'.toFinset = insert z (dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset)) := by
            ext w; simp only [ws', List.mem_toFinset, insertSorted_mem, Finset.mem_insert, ← dropVal_toFinset]
          have hlive' : LiveBin mask goal k' ws'.toFinset := by rwa [hset']
          have hlen' := list_len_child (z := z) (keepA := keepA) (keepB := keepB) nd hxM hyM hxy hzNotW
          have hcard' : ws'.length ≤ rem := by
            have := liveBin_card_le hlive'
            rw [List.toFinset_card_of_nodup hnd'] at this; omega
          rcases hKe with hwide | hloc | href
          · change ws'.length = _ at hlen'; rw [← hlen'] at hwide; omega
          · have hopen := dagLocal_open (state := (rem - 1, ws', (z, x, y) :: hist)) hgm (hknown i (makeToken a b op keep)) (hsub i (makeToken a b op keep)) hnd' (k := k') (by omega) hlive'
            rw [hopen] at hloc; exact Bool.noConfusion hloc
          · obtain ⟨dest, saved, hdest, htr', heq, moved⟩ :=
              good (i + 1) (makeToken a b op keep) _ href
            exact ih (rem - 1) (by omega) dest saved hdest htr' heq k' (by omega) (moved k' hlive')

theorem lowerDagRef {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {boundsFor : Nat → Nat → List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {ref : Nat → Nat → DagState → Bool}
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hroots : dagCheckRoots mask goal bounds
      (ref 0) stock fuel = true)
    (hknownFor : ∀ i tok, KnownBin (boundsFor i tok))
    (hsubFor : ∀ i tok, ∀ b ∈ boundsFor i tok, mask &&& b.1 = b.1)
    (good : RefSound mask goal count (dagTrace mask stock fuel forest) ref)
    (hnodes : ∀ i, 0 ≤ i → i < count → checkNodeVia mask goal (boundsFor i)
      (dagTrace mask stock fuel forest) ref i = true) :
    LowerBin mask stock goal (fuel + 1) := by
  intro vs hbuild hhit
  by_contra! hlt
  have hcs' : ∀ w ∈ stock, canon mask w = w := fun w hw =>
    Nat.beq_eq.mp (List.all_eq_true.mp hcs w hw)
  obtain ⟨k, S, hk, hSsub, hlive⟩ := extractLiveBin hgnz hcs' hbuild hhit
  obtain ⟨tok, htok, hteq⟩ := exists_subsetToken stock S
  rw [Finset.inter_eq_left.mpr hSsub] at hteq
  have hchk := treeBlock_at hroots (Nat.zero_le tok) htok
  simp only [forceWs_eq, Bool.or_eq_true] at hchk
  have hnd : (subsetWords stock tok).Nodup := subsetWords_nodup snd tok
  have hlive' : LiveBin mask goal k (subsetWords stock tok).toFinset := by rwa [hteq]
  rcases hchk with hloc | href
  · have hopen := dagLocal_open (state := (fuel, subsetWords stock tok, [])) hgm hknown hsub hnd (k := k) (by omega) hlive'
    rw [hopen] at hloc; exact Bool.noConfusion hloc
  · obtain ⟨dest, saved, hdest, htr, heq, moved⟩ := good 0 tok _ href
    exact dagAllNodesRef hgm hknownFor hsubFor snd good hnodes fuel dest saved hdest htr heq k
      (by omega) (moved k hlive')

def chooseBounds : List (Nat × List Nat × Nat × Nat) → Nat → List (Nat × List Nat × Nat × Nat)
  | [], _ => []
  | b :: bs, bits =>
    let rest := chooseBounds bs (Nat.shiftRight bits 1)
    Bool.rec rest (b :: rest) (Nat.testBit bits 0)

theorem chooseBounds_mem {bs : List (Nat × List Nat × Nat × Nat)} (bits : Nat)
    {b : Nat × List Nat × Nat × Nat} (h : b ∈ chooseBounds bs bits) : b ∈ bs := by
  induction bs generalizing bits with
  | nil => simp [chooseBounds] at h
  | cons a tail ih =>
    cases e : Nat.testBit bits 0
    · simp only [chooseBounds, e] at h
      exact List.mem_cons_of_mem _ (ih _ h)
    · simp only [chooseBounds, e] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih _ h)

def checkNodeViaF (mask goal : Nat) (bounds : Nat → List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option DagState) (ref : Nat → Nat → DagState → Bool) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some st => dagCheckChildrenF mask goal bounds (ref (Nat.add i 1)) st

theorem checkNodeViaF_eq {mask goal : Nat} {bounds : Nat → List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ tok, ∀ b ∈ bounds tok, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (states : Nat → Option DagState) (ref : Nat → Nat → DagState → Bool) (i : Nat) :
    checkNodeViaF mask goal bounds states ref i = checkNodeVia mask goal bounds states ref i := by
  unfold checkNodeViaF checkNodeVia
  cases states i with
  | none => rfl
  | some st => exact dagCheckChildrenF_eq hgoals _ st

theorem lowerDagRefF {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)} {boundsFor : Nat → Nat → List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {ref : Nat → Nat → DagState → Bool}
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true) (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hmem : ∀ i tok b, b ∈ boundsFor i tok → b ∈ bounds)
    (good : RefSound mask goal count (dagTraceF mask stock fuel forest) ref)
    (hroots : dagCheckRootsF mask goal bounds (ref 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → checkNodeViaF mask goal (boundsFor i)
      (dagTraceF mask stock fuel forest) ref i = true) :
    LowerBin mask stock goal (fuel + 1) := by
  have htr : dagTraceF mask stock fuel forest = dagTrace mask stock fuel forest := by
    funext i; exact dagTraceF_eq mask stock fuel forest i
  rw [htr] at good hnodes
  rw [dagCheckRootsF_eq hgoals] at hroots
  refine lowerDagRef hgm hgnz hcs snd hknown hsub hroots
    (boundsFor := boundsFor) (fun i tok b hb => hknown b (hmem i tok b hb))
    (fun i tok b hb => hsub b (hmem i tok b hb)) good ?_
  intro i hlo hhi
  have h := hnodes i hlo hhi
  rwa [checkNodeViaF_eq (fun tok b hb => hgoals b (hmem i tok b hb))] at h



theorem image_dropIf (f : Nat → Nat) (drop : Bool) (x : Nat) (S : Finset Nat)
    (hinj : ∀ w ∈ S, f w = f x → w = x) :
    (dropIf drop x S).image f = dropIf drop (f x) (S.image f) := by
  cases drop with
  | false => rfl
  | true =>
    change (S.erase x).image f = (S.image f).erase (f x)
    ext y
    constructor
    · intro hy
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
      exact Finset.mem_erase.mpr ⟨fun eq => hne (hinj w hmem eq), Finset.mem_image_of_mem _ hmem⟩
    · intro hy
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hy
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hmem
      exact Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨fun eq => hne (congrArg f eq), hw⟩)

theorem liveBin_rowPerm {n : Nat} (p : Equiv.Perm (Fin n)) {mask goal k : Nat} {S : Finset Nat}
    (hm : mask < 2 ^ n) (h : LiveBin mask goal k S) (canonical : ∀ w ∈ S, canon mask w = w) :
    LiveBin (rowPull p mask) (rowCanon p mask goal) k (S.image (rowCanon p mask)) := by
  induction h with
  | done =>
    simpa only [Finset.image_singleton] using
      (LiveBin.done (mask := rowPull p mask) (goal := rowCanon p mask goal))
  | @step k S a b op ha hb hab ha0 hb0 hop hz fresh keepA keepB _ ih =>
    let f := rowCanon p mask
    let z := binOp mask op a b
    let after := dropIf (!keepA) a (dropIf (!keepB) b S)
    have cz : canon mask z = z := binOp_canon mask op a b
    have ca := canonical a ha
    have cb := canonical b hb
    have ha' : f a ∈ S.image f := Finset.mem_image_of_mem _ ha
    have hb' : f b ∈ S.image f := Finset.mem_image_of_mem _ hb
    have distinct : f a ≠ f b := fun he => hab (rowCanon_injective_on_canon p hm ca cb he)
    have nonzero {w : Nat} (hw : canon mask w = w) (hn : w ≠ 0) : f w ≠ 0 := by
      intro he
      exact hn (rowCanon_injective_on_canon p hm hw (canon_zero mask)
        (he.trans (rowCanon_zero p mask).symm))
    have new : f z ∉ S.image f := by
      intro hit
      obtain ⟨w, hw, eq⟩ := Finset.mem_image.mp hit
      have he := rowCanon_injective_on_canon p hm (canonical w hw) cz eq
      apply fresh
      change z ∈ S
      rwa [← he]
    have moved : ∃ op' < 4, f z = binOp (rowPull p mask) op' (f a) (f b) := by
      rcases rowCanon_binOp p mask op a b hop with eq | eq | eq | ok
      · exact (nonzero cz hz eq).elim
      · exfalso
        apply new
        change f z = f a at eq
        rwa [eq]
      · exfalso
        apply new
        change f z = f b at eq
        rwa [eq]
      · exact ok
    obtain ⟨op', hop', produced⟩ := moved
    have nextCanonical : ∀ w ∈ insert z after, canon mask w = w := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact cz
      · exact canonical w (dropIf_subset (!keepB) b S
          (dropIf_subset (!keepA) a (dropIf (!keepB) b S) hw))
    have firstDrop : (dropIf (!keepB) b S).image f = dropIf (!keepB) (f b) (S.image f) :=
      image_dropIf f (!keepB) b S (fun w hw => rowCanon_injective_on_canon p hm (canonical w hw) cb)
    have movedAfter : after.image f = dropIf (!keepA) (f a) (dropIf (!keepB) (f b) (S.image f)) := by
      unfold after
      rw [image_dropIf f (!keepA) a (dropIf (!keepB) b S), firstDrop]
      intro w hw
      exact rowCanon_injective_on_canon p hm (canonical w (dropIf_subset (!keepB) b S hw)) ca
    have rest := ih nextCanonical
    change LiveBin (rowPull p mask) (rowCanon p mask goal) k ((insert z after).image f) at rest
    rw [Finset.image_insert, movedAfter, produced] at rest
    exact LiveBin.step ha' hb' distinct (nonzero ca ha0) (nonzero cb hb0) hop'
      (by rw [← produced]; exact nonzero cz hz) (by rwa [← produced]) keepA keepB rest

theorem liveBin_rowSymmetry {n : Nat} (p : Equiv.Perm (Fin n)) {mask goal k : Nat} {S : Finset Nat}
    (hm : mask < 2 ^ n) (hmask : rowPull p mask = mask) (hgoal : rowCanon p mask goal = goal)
    (h : LiveBin mask goal k S) (canonical : ∀ w ∈ S, canon mask w = w) :
    LiveBin mask goal k (S.image (rowCanon p mask)) := by
  simpa only [hmask, hgoal] using liveBin_rowPerm p hm h canonical

structure RowAction64 where
  source : Fin 64 → Fin 64
  apply : Nat → Nat
  testBit_eq : ∀ w (i : Fin 64), (apply w).testBit i.val = w.testBit (source i).val

def RowAction64.id : RowAction64 := ⟨fun i => i, fun w => w, fun _ _ => rfl⟩

def RowAction64.comp (a b : RowAction64) : RowAction64 :=
  ⟨fun i => b.source (a.source i), fun w => a.apply (b.apply w), by
    intro w i
    rw [a.testBit_eq, b.testBit_eq]⟩

private def lowerLane (lo d : Nat) (i : Fin 64) : Bool :=
  decide (d ≤ i.val) && lo.testBit (i.val - d)

private def maskSource (lo hi d : Nat) (i : Fin 64) : Fin 64 :=
  ⟨(if lowerLane lo d i then i.val - d
    else if hi.testBit (d + i.val) then d + i.val else i.val) % 64, Nat.mod_lt _ (by decide)⟩

def goodMaskLanes (lo hi keep d : Nat) (i : Fin 64) : Prop :=
  let a := lowerLane lo d i
  let b := hi.testBit (d + i.val)
  let c := keep.testBit i.val
  (a = true ∧ b = false ∧ c = false) ∨
    (a = false ∧ b = true ∧ c = false ∧ d + i.val < 64) ∨
    (a = false ∧ b = false ∧ c = true)

def maskedRow64 (lo hi keep d : Nat) (cert : ∀ i : Fin 64, goodMaskLanes lo hi keep d i) : RowAction64 :=
  ⟨maskSource lo hi d, fun w => ((lo &&& w) <<< d) ||| ((hi &&& w) >>> d) ||| (keep &&& w), by
    intro w i
    have bits : (((lo &&& w) <<< d) ||| ((hi &&& w) >>> d) ||| (keep &&& w)).testBit i.val =
        ((lowerLane lo d i && w.testBit (i.val-d)) ||
          (hi.testBit (d+i.val) && w.testBit (d+i.val)) ||
          (keep.testBit i.val && w.testBit i.val)) := by
      simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
        lowerLane, Bool.and_assoc]
    rw [bits]
    have h := cert i
    unfold goodMaskLanes at h
    rcases h with ⟨a,b,c⟩ | ⟨a,b,c,h⟩ | ⟨a,b,c⟩
    · have h : i.val-d < 64 := (Nat.sub_le ..).trans_lt i.isLt
      simp [maskSource, a, b, c, Nat.mod_eq_of_lt h]
    · simp [maskSource, a, b, c, Nat.mod_eq_of_lt h]
    · simp [maskSource, a, b, c, Nat.mod_eq_of_lt i.isLt]⟩

theorem fullMask_testBit (i : Nat) : fullMask.testBit i = decide (i < 64) := by
  change (2 ^ 64 - 1).testBit i = _
  exact Nat.testBit_two_pow_sub_one _ _

theorem rowPull_fullMask (p : Fin 64 → Fin 64) : rowPull p fullMask = fullMask := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 64
  · simp [rowPull_testBit, hi, fullMask_testBit, (p ⟨i, hi⟩).isLt]
  · simp [rowPull_testBit, hi, fullMask_testBit]

theorem RowAction64.pull_eq (a : RowAction64) {p : Fin 64 → Fin 64} (h : ∀ i, a.source i = p i)
    (w : Nat) : a.apply w &&& fullMask = rowPull p w := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, fullMask_testBit]
  by_cases hi : i < 64
  · let j : Fin 64 := ⟨i, hi⟩
    simp only [hi, decide_true, Bool.and_true]
    change (a.apply w).testBit j.val = (rowPull p w).testBit j.val
    rw [a.testBit_eq, rowPull_bit, h]
  · simp [hi, rowPull_testBit]

theorem RowAction64.canon_eq (a : RowAction64) {p : Fin 64 → Fin 64} (h : ∀ i, a.source i = p i)
    (w : Nat) : canonF fullMask (a.apply w) = rowCanon p fullMask w := by
  rw [canonF_eq, ← canon_land fullMask (a.apply w), a.pull_eq h, rowCanon, rowPull_fullMask]


def unpackPaged (pages : List Nat) (width pageBits i : Nat) : Nat :=
  unpackF (getDN pages (Nat.shiftRight i pageBits)) width
    (Nat.land i (Nat.sub (Nat.shiftLeft 1 pageBits) 1))

def unpackPagedWidths (pages : List (Nat × Nat)) (pageBits i : Nat) : Nat :=
  let page := pages.getD (Nat.shiftRight i pageBits) (0, 0)
  unpackF page.2 page.1 (Nat.land i (Nat.sub (Nat.shiftLeft 1 pageBits) 1))

def unpackForestRelative (row : Nat → Nat) (tBits : Nat) : Nat → Nat × Nat := fun i =>
  let code := row i
  let distance := Nat.shiftRight code tBits
  (Bool.rec (Nat.sub (Nat.add i 1) distance) 0 (Nat.beq distance 0),
    Nat.land code (Nat.sub (Nat.shiftLeft 1 tBits) 1))

def unpackLinksPaged (index entry : Nat → Nat) (sizeBits tokBits steps : Nat) : Nat → Nat → Option Nat :=
  fun parent tok =>
    let start := index parent
    let sz := Nat.land start (Nat.sub (Nat.shiftLeft 1 sizeBits) 1)
    let off := Nat.shiftRight start sizeBits
    (Nat.rec (motive := fun _ => Nat → Nat → Option Nat) (fun _ _ => none)
      (fun _ next lo hi =>
        Bool.rec none
          (let mid := Nat.shiftRight (Nat.add lo hi) 1
           let code := entry mid
           let key := Nat.land code (Nat.sub (Nat.shiftLeft 1 tokBits) 1)
           Bool.rec
             (Bool.rec (next (Nat.add mid 1) hi) (next lo mid) (Nat.blt tok key))
             (some (Nat.shiftRight code tokBits)) (Nat.beq tok key))
          (Nat.blt lo hi)) steps) off (Nat.add off sz)

abbrev TableSymmetry (mask goal : Nat) :=
  {s : ({p : Equiv.Perm (Fin 64) // rowPull p mask = mask ∧
      rowCanon p mask goal = goal}) × (Nat → Nat) //
    ∀ w, s.2 w = rowCanon s.1.val mask w}

def rowSort (f : Nat → Nat) : List Nat → List Nat
  | [] => []
  | w :: ws => insertSortedF (f w) (rowSort f ws)

theorem rowSort_mem (f : Nat → Nat) (ws : List Nat) (w : Nat) :
    w ∈ rowSort f ws ↔ w ∈ ws.map f := by
  induction ws with
  | nil => rfl
  | cons a as ih => simp only [rowSort, List.map_cons, insertSortedF_eq, insertSorted_mem, List.mem_cons, ih]

theorem rowSort_finset (f : Nat → Nat) (ws : List Nat) :
    (rowSort f ws).toFinset = ws.toFinset.image f := by
  ext w
  simp only [List.mem_toFinset, rowSort_mem, List.mem_map, Finset.mem_image]

def refMatches (mask goal : Nat) (syms : List (TableSymmetry mask goal))
    (sym : Nat) (saved st : DagState) : Bool :=
  if Nat.beq sym 0 then eqListN st.2.1 saved.2.1
  else match syms[sym]? with
  | none => false
  | some p => st.2.1.all (fun w => Nat.beq (canonF mask w) w) &&
      eqListN (rowSort p.val.2 st.2.1) saved.2.1

theorem refMatches_sound {mask goal : Nat} (hm : mask < 2 ^ 64)
    (syms : List (TableSymmetry mask goal)) (sym : Nat) (saved st : DagState)
    (hc : refMatches mask goal syms sym saved st = true) (k : Nat)
    (live : LiveBin mask goal k st.2.1.toFinset) : LiveBin mask goal k saved.2.1.toFinset := by
  unfold refMatches at hc
  split at hc
  · simp only [eqListN_eq, beq_iff_eq] at hc
    exact hc ▸ live
  · split at hc
    · contradiction
    · rename_i p hp
      simp only [Bool.and_eq_true, eqListN_eq, beq_iff_eq] at hc
      have hcanonical : ∀ w ∈ st.2.1.toFinset, canon mask w = w := by
        intro w hw
        have h := Nat.beq_eq.mp (List.all_eq_true.mp hc.1 w (List.mem_toFinset.mp hw))
        rwa [canonF_eq] at h
      have moved := liveBin_rowSymmetry p.val.1.val hm p.val.1.property.1 p.val.1.property.2 live hcanonical
      have haction : p.val.2 = rowCanon p.val.1.val mask := funext p.property
      rw [← haction, ← rowSort_finset, hc.2] at moved
      exact moved

def symDagRef (mask goal count bits : Nat) (syms : List (TableSymmetry mask goal))
    (states : Nat → Option DagState) (links : Nat → Nat → Option Nat)
    (parent tok : Nat) (st : DagState) : Bool :=
  match links parent tok with
  | none => false
  | some code =>
    let dest := Nat.shiftRight code bits
    let sym := Nat.land code (Nat.sub (Nat.shiftLeft 1 bits) 1)
    Nat.blt dest count &&
      (match states dest with
      | none => false
      | some saved => Nat.beq saved.1 st.1 && refMatches mask goal syms sym saved st)

theorem symDagRef_sound {mask goal count bits : Nat} (hm : mask < 2 ^ 64)
    (syms : List (TableSymmetry mask goal)) (states : Nat → Option DagState)
    (links : Nat → Nat → Option Nat) : RefSound mask goal count states
      (symDagRef mask goal count bits syms states links) := by
  intro parent tok st h
  unfold symDagRef at h
  split at h
  · contradiction
  · rename_i code heq
    simp only [Bool.and_eq_true] at h
    obtain ⟨hd, hmoves⟩ := h
    split at hmoves
    · contradiction
    · rename_i saved hstate
      simp only [Bool.and_eq_true] at hmoves
      obtain ⟨hf, hmatch⟩ := hmoves
      exact ⟨_, saved, Nat.blt_eq.mp hd, hstate, Nat.beq_eq.mp hf,
        refMatches_sound hm syms _ saved st hmatch⟩

def cert_mask : Nat := 0xffffffffffffffff
def cert_stock : List Nat := [0xffffffff, 0xffff0000ffff, 0xff00ff00ff00ff, 0xf0f0f0f0f0f0f0f, 0x3333333333333333, 0x5555555555555555]
def cert_goal : Nat := 0x11717570157577f
def cert_bound_chunks : List (List (Nat × List Nat × Nat × Nat)) := [
  [(0xf0f0f0f0f0f0f0f0, [0xf0f0f0f0, 0xf0f00000f0f0, 0xf000f000f000f0, 0x3030303030303030, 0x5050505050505050], 9, 0x10105000505070), (0xcccccccccccccccc, [0xcccccccc, 0xcccc0000cccc, 0xcc00cc00cc00cc, 0xc0c0c0c0c0c0c0c, 0x4444444444444444], 9, 0x404440044444c), (0xff00ff00ff00ff, [0xff00ff, 0xff000000ff, 0xf000f000f000f, 0x33003300330033, 0x55005500550055], 9, 0x1700570057007f), (0xffff0000ffff, [0xffff, 0xff000000ff, 0xf0f00000f0f, 0x333300003333, 0x555500005555], 9, 0x17570000577f), (0x5555555555555555, [0x55555555, 0x555500005555, 0x55005500550055, 0x505050505050505, 0x1111111111111111], 8, 0x115155501555555), (0xaaaaaaaaaaaaaaaa, [0xaaaaaaaa, 0xaaaa0000aaaa, 0xaa00aa00aa00aa, 0xa0a0a0a0a0a0a0a, 0x2222222222222222], 8, 0x202020002022a), (0xf0f0f0f0f0f0f0f, [0xf0f0f0f, 0xf0f00000f0f, 0xf000f000f000f, 0x303030303030303, 0x505050505050505], 8, 0x10707070107070f), (0xffff00000000ffff, [0xffff, 0xff0000000000ff, 0xf0f000000000f0f, 0x3333000000003333, 0x5555000000005555], 10, 0x11700000000577f)],
  [(0xff00ff00ff00ff00, [0xff00ff00, 0xff000000ff00, 0xf000f000f000f00, 0x3300330033003300, 0x5500550055005500], 8, 0x100170001005700), (0x3333333333333333, [0x33333333, 0x333300003333, 0x33003300330033, 0x303030303030303, 0x1111111111111111], 8, 0x113131301131333), (0xffff0000ffff0000, [0xffff0000, 0xff000000ff0000, 0xf0f00000f0f0000, 0x3333000033330000, 0x5555000055550000], 8, 0x117000001570000), (0xffffffff00000000, [0xffff00000000, 0xff00ff00000000, 0xf0f0f0f00000000, 0x3333333300000000, 0x5555555500000000], 9, 0x117175700000000), (0xffffffff, [0xffff, 0xff00ff, 0xf0f0f0f, 0x33333333, 0x55555555], 9, 0x157577f), (0x55555555aaaaaaaa, [0xaaaaaaaa, 0x55550000aaaa, 0x55005500aa00aa, 0x50505050a0a0a0a, 0x1111111122222222], 10, 0x11515550002022a), (0x5555555500000000, [0x555500000000, 0x55005500000000, 0x505050500000000, 0x1111111100000000], 7, 0x115155500000000), (0x5500550055005500, [0x55005500, 0x550000005500, 0x500050005000500, 0x1100110011001100], 5, 0x100150001005500)],
  [(0xff000000ff, [0xff, 0xf0000000f, 0x3300000033, 0x5500000055], 5, 0x570000007f), (0xf0f0f0f00f0f0f0f, [0xf0f0f0f, 0xf0f000000f0f, 0xf000f0000f000f, 0x3030303003030303, 0x5050505005050505], 10, 0x1010500107070f), (0xaaaaaaaa, [0xaaaa, 0xaa00aa, 0xa0a0a0a, 0x22222222], 7, 0x2022a), (0x5050505050505050, [0x50505050, 0x505000005050, 0x50005000500050, 0x1010101010101010], 5, 0x10105000505050), (0xf0f00000f0f0, [0xf0f0, 0xf0000000f0, 0x303000003030, 0x505000005050], 6, 0x105000005070), (0x33333333, [0x3333, 0x330033, 0x3030303, 0x11111111], 7, 0x1131333), (0xa0a0a0a0a0a0a0a, [0xa0a0a0a, 0xa0a00000a0a, 0xa000a000a000a, 0x202020202020202], 5, 0x202020002020a), (0xff00ff0000000000, [0xff0000000000, 0xf000f0000000000, 0x3300330000000000, 0x5500550000000000], 7, 0x100170000000000)],
  [(0xf0f0f0f, [0xf0f, 0xf000f, 0x3030303, 0x5050505], 7, 0x107070f), (0xffff000000000000, [0xff000000000000, 0xf0f000000000000, 0x3333000000000000, 0x5555000000000000], 7, 0x117000000000000), (0x4444444444444444, [0x44444444, 0x444400004444, 0x44004400440044, 0x404040404040404], 5, 0x4044400444444), (0xcc00cc00cc00cc, [0xcc00cc, 0xcc000000cc, 0xc000c000c000c, 0x44004400440044], 6, 0x400440044004c), (0x5555000055550000, [0x55550000, 0x55000000550000, 0x505000005050000, 0x1111000011110000], 5, 0x115000001550000), (0x2222222222222222, [0x22222222, 0x222200002222, 0x22002200220022, 0x202020202020202], 5, 0x2020200020222), (0xaa00aa00aa00aa, [0xaa00aa, 0xaa000000aa, 0xa000a000a000a, 0x22002200220022], 5, 0x200020002002a), (0xc0c0c0c0c0c0c0c, [0xc0c0c0c, 0xc0c00000c0c, 0xc000c000c000c, 0x404040404040404], 5, 0x404040004040c)],
  [(0xaaaa0000aaaa, [0xaaaa, 0xaa000000aa, 0xa0a00000a0a, 0x222200002222], 5, 0x2020000022a), (0xff00ff0000ff00ff, [0xff00ff, 0xff00000000ff, 0xf000f00000f000f, 0x3300330000330033, 0x5500550000550055], 10, 0x10017000057007f), (0xcccccccc33333333, [0x33333333, 0xcccc00003333, 0xcc00cc00330033, 0xc0c0c0c03030303, 0x4444444411111111], 10, 0x4044401131333), (0xc0c0c0c0c0c0c0c0, [0xc0c0c0c0, 0xc0c00000c0c0, 0xc000c000c000c0, 0x4040404040404040], 5, 0x4000404040), (0xcccc0000cccc, [0xcccc, 0xcc000000cc, 0xc0c00000c0c, 0x444400004444], 6, 0x4440000444c), (0x3300330033003300, [0x33003300, 0x330000003300, 0x300030003000300, 0x1100110011001100], 4, 0x100130001001300), (0xf000f000f000f0, [0xf000f0, 0xf0000000f0, 0x30003000300030, 0x50005000500050], 6, 0x10005000500070), (0xff000000ff0000, [0xff0000, 0xf0000000f0000, 0x33000000330000, 0x55000000550000], 5, 0x17000000570000)],
  [(0xf0f0f0f000000000, [0xf0f000000000, 0xf000f000000000, 0x3030303000000000, 0x5050505000000000], 5, 0x10105000000000), (0xffff, [0xff, 0xf0f, 0x3333, 0x5555], 5, 0x577f), (0xffff00000000, [0xff00000000, 0xf0f00000000, 0x333300000000, 0x555500000000], 5, 0x175700000000), (0x3030303030303030, [0x30303030, 0x303000003030, 0x30003000300030, 0x1010101010101010], 5, 0x10101000101030), (0x3333333300000000, [0x333300000000, 0x33003300000000, 0x303030300000000, 0x1111111100000000], 5, 0x113131300000000), (0xf000f000f000f00, [0xf000f00, 0xf0000000f00, 0x300030003000300, 0x500050005000500], 4, 0x100070001000700), (0xcccccccc00000000, [0xcccc00000000, 0xcc00cc00000000, 0xc0c0c0c00000000, 0x4444444400000000], 5, 0x4044400000000), (0xf0f0f0f00000000, [0xf0f00000000, 0xf000f00000000, 0x303030300000000, 0x505050500000000], 5, 0x107070700000000)],
  [(0xff000000ff00, [0xff00, 0xf0000000f00, 0x330000003300, 0x550000005500], 5, 0x170000005700), (0xff00ff, [0xff, 0xf000f, 0x330033, 0x550055], 5, 0x57007f), (0xcccccccc, [0xcccc, 0xcc00cc, 0xc0c0c0c, 0x44444444], 5, 0x44444c), (0xf0f0f0f0, [0xf0f0, 0xf000f0, 0x30303030, 0x50505050], 5, 0x505070), (0xffff0000, [0xff0000, 0xf0f0000, 0x33330000, 0x55550000], 5, 0x1570000), (0x3333000033330000, [0x33330000, 0x33000000330000, 0x303000003030000, 0x1111000011110000], 4, 0x113000001130000), (0xf0f00000f0f0000, [0xf0f0000, 0xf0000000f0000, 0x303000003030000, 0x505000005050000], 4, 0x107000001070000), (0xff00ff00000000, [0xff00000000, 0xf000f00000000, 0x33003300000000, 0x55005500000000], 5, 0x17005700000000)],
  [(0xff00ff00, [0xff00, 0xf000f00, 0x33003300, 0x55005500], 5, 0x1005700)]]
def cert_bounds := cert_bound_chunks.flatten
theorem cert_sub : ∀ b ∈ cert_bounds, cert_mask &&& b.1 = b.1 := by
  have hall : cert_bounds.all (fun b => Nat.beq (Nat.land cert_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem cert_goals : ∀ b ∈ cert_bounds, canon b.1 cert_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : cert_bounds.all (fun b => Nat.beq (canonF b.1 cert_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def cert_forest : Nat → Nat × Nat := unpackForestRelative (unpackPagedWidths [
    (17, 0x19a58ad1c18a81b43091f828df80dc0b7c61a5835c1668e0c600a2a02df126860b7c411f8ed7c18d82b5b11ab82d7018c80b5306380e8dc56c01c7c09b802d20129e08367833031a09ade0c581eb1831a054de0c580d2f8318014ae98460532211bc1488746305221916c14d854570ab20291078a6093405a1881b828c40c5a0423020f81026003f),
    (18, 0x2193ec6f02113dc6302113cc5b021b3bc57055900844e914c1474021106c5b059e0086c1515c1d64051d008440d14c234b06d1c0c5402d0c0864c8dbc1474021d03e7f051900864099cc156f0358c0844b4d3c1578021d03e7f055a00864099cc156f0358c085ca0d1c083406d0c0834028fe596e021500a5f90518124402110345304d90083402d0c126e02919f93e),
    (19, 0x16a4069bc092f80a570d08c029902a3780a44088c6029101a2d80a6c048ae05590052200c530107d5c06cb63596453016a80358ca5b580c8c018a64cd9c063200e7b2369e02d90073d90343038a604d3c05a18e26a0747e02d30151d822370147802d10051980944078a60251015a78125f014a6024d005a18626205ad608dac0db38135f016a60c92804a201c6b012880314c051940017),
    (18, 0xa315c085c0559008449b14c147402110745b059e0086c1715c085c07590147402110345308d2c1b47031500b4302191e36f051d008740f9fc1464021902673055bc0d6302111934f055e008740f9fc1568021902673055bc0d630217143470cd2c2b47031501b43048fc0a37421b80b7c14d2c0d7010d1c145402df02b4302df01a3f031c00a372a1983d6f0d58c2b52),
    (20, 0x9441bb4f013640096401e7b00d6b0093418b4300b6402b4300b6401a3f00a6400a331516e01b430123f00a331316600c5804d6b00a5c03a6b00c7002a6700c5801a5f00a5c00a530d94600a4401c6b00a4400c530b13e031440084c01a3700925008360084404c530194400b5f0084402b4f012440084400c530083e030620085401b5f008560083e0084a8381f008642bc6f008442ac630084429c5b0086c),
    (20, 0x134900b4804453025620156000a3400c6a01b4b00d6e00b430084c102370635200c580515f00c600415701a5f00b6c00a570213d0146200b500092709846009440845b0096c07457015640094405c530094404b4f0095c03b4702c5b024570156400b4800c5300a360082eaa0530094425c6b0094424c53013540095401d6300c530093421b6b0148c0094401c5300b430097c1eb67014640096401e7b00d6b),
    (20, 0x1b4f0095c00b470082edd85b0084432c5b0086c31c570085c01d6400937008442f45300c6403b6f02b5f0235700b540125f00a37008442aa4f015680086407b6f0084e00d70063670545b04c530145900c580325f0146100c6001a5700d6a00a4f0085c21a4701458008541056b0103600834014700087c0dd670103600834014600086c0267401c5800b4a008540956300b4907c5b00b6106c5700b5101d64),
    (20, 0xa6600924009660714700c6805d6f00c700157600c5803d6b0147200c700256700c580156300b6a00946f71231945b18c5700d6417c5300c6400b6f1624f00d680236f0084e00d7000b671324700c5804d6b0083600c70035670083600c600167400c5800d630da3700b5400a5f0213f00b4800c53009270a16e00c580295f00c600195700b500092706846009440545b0096c04457015640094402c5300944),
    (17, 0x632095c828f00c6805bf1f14c48b61c53062902d38a6d43a4f192582d40448e126c05260290c14c00b66bd1a0759428f00c68acbf275f41d188d6f0ac603160eac66c70323003588a8b4446d06be0d17c28f80b480e2983148169409245cbb031c09cec083606380d5d816a824720e340516016f4616e2a3d1318086f40d7019bb08da834d40c60),
    (19, 0x2b10035e006474056304ad60758c06b100c5e7b8f4f51d8263504469078d00d19815b502366024b00295004b320d6f028b203160fab585c710126c131c01d268324901298089140d20809400124c029c0cab381d7e028b203160bab196c6e016cc571acaa350146c014c04f19805b312c63248c4119f81f390357a05ae4051e006340137e016e43716c06b10cc5a188ac119f806320357a),
    (19, 0x30cc02920042f00844cd29e025901eb78095405ad6025f00eb38095401ac78852826bd0457907af00d5d8163d02476026d002d9004bb5667f02ad2035a2a73d81d810128c03602973b81e8e02ad2035a28739809649fafc031da76bdce57a02af8025f266bb00c7697ae72d5c823c703f8206d140ba080ac400d780291c0320a36b580e728bad4025b226b30478e01ae80da2806ba02682),
    (18, 0x32321e7709a381d640519008647d9cded76791f9dc7675198246607190136602d90fd6f02d50ed6b0adf01a39048d4092e029c0bd67095f81c5404d5008542558c2a4f0892c1a47029b00a43029805c6614db8324f0a92c2247049b008240290c0a6004d980b562c8d0146402dd0997e091f01b6c04d58087c1c5d80c7c071d8137e02d90496e0f5ac0c5b0a4900a60),
    (20, 0x9240d96e0ab710158000b8c0934b00d800834700c700145400b8c06343052610147000a7c03a3b00c7002a3700b600134400a7c00a33009240287e01b4300a33009240087c9a9670137c00b5605b4b00d7004b470146000b4e02c540237c01b6c00a600083400b4393966009440545b0096c044570095c0256400b4d00c540094401453009448d9620357602d740247601c7400c640097623e7f00c6422e7b),
    (17, 0xe3e839c018ab6b5f05b20b5f446f80d7009ab020d266a62d7e12b906df826f80b5681a58f5f818d82d7912b9075c4128c0d7061a3831f158fca47c22370317068d22c6212308251828c00b4e2e2a14df822bc085e1dbe028e01adc236c09310298010680b43b11a02e30f6960d8035a3831c028a80b8c25a18e8ec18e02a3705b004d1014f80a33),
    (19, 0x3b1a03e0006b2ccc6f018e80ba34124600e80028cc021124a318368e0131809a080e470148c018cd1716c234700d7c06d120ba0813408095602d00025ba0a2b80d8c15b1c2963022bf00d6c06af20b5c812b881d70028bc025782eb20548e01af8045b804370348c01cfc091f009b900b7001088d714c06b20147d018aa76dbce9b681464016c8095f40eb880c70016ac66d8c16be00d64),
    (20, 0xe46500c660d45b016790096e0bc5701d690145e0095e00d64094530224f01a4b0124700a4300a6005b5500b5604b4b015690095e0334701c590134e0094e00c5400b4300a34fa96f00b6403b4b00d6802b4701c540137400b6400b43f616e01466009440445b0096c0345700c5e01d64011440084400c53f096a00e740158d00d655447f53c7d0157400c7402e8d0268100d80014660098c4fc7302e8c00e74),
    (21, 0x36b7802d500bad60147c005be01159c038a8013540042a00958c036dc01356005310628fc014c80556f0052a0115ac014f8035670052a00958c034dc00c620052b04a8ec018d00556f0062c0115ac018e0035670062c00958c038c400d6a0062d0328dc028c800a64056b780295013ad600a7c046b38069500129800854036b1818db8018ca0526e00635010958048be01c5b00a2b80314c0324800c5b004120028cc0125b09234),
    (18, 0x91900c58051500b6408d0c0a5c028cc0854ec97c0a442516c0a6c2115c0a5c095901a44024f008441514c0b5210918234b06d1c0c5402d0c192402d0c0824c496c536d02df0434b035c03347091501b7c04db0083402d0eba5702910ac5b029b09c57075900c54029107c530cd2c2b47071500b44028d00b4310d900b5a0c918234b06d1c0c5402d0c09248094c0b64),
    (19, 0xbf68e0253c6e2a0d36e014c030d985c9a8a25b0e48a1a8f405220592a0327204078040903928012500a0a8040c01826014b402090152981b6a024dc029980417811340106944d0c162d82457038aa0496c052bcdb5f016ad32d6c0e368126c014c12ad5c0db7013560106922d4c09b700b568e6960497c0529c5b470369c0493c052181c54026dc020d211a186b55016c816d2c06b404b47),
    (19, 0x24c0025b7f5ab80b5434ad606df0051c80a7030ace0ed7c051c02b5b012d806d5c049a00b530a6d81093c1d258135c012b80891c09220092401486029807a330eb6e1c6ac364d405248b45b024c2025804e2b8413f0727602900149b8093c03266044bc049180950096ac0258006330324b012c00719805ab0092801486064d0062d80834c76a608db80db3013560126b84d2c08af8095d),
    (17, 0x2d279492c38f8147004ae0c91c44f80d6c0936024901487ba62052ce717f26bc136e04a2de93c48dc1b5d092b02496a496956945b7035a0f6bc72490ab402970b2bc515d052f1057072a41568042e0817826b8095c04292e91c88dc0a5c19aa8a9b0447c192505af02490e4862b5e11ad06d5826a40a5620978cd6854bc225a0d2b04948125c0927),
    (21, 0x9b5802d8c01289c745b014b78085b402ace00856004b671115c012c80b47e004be0291d81328a0836b025aa810d34014700313a0141d0020a00306c00b6a0041a00cd8c048f400b78009bf002dd80107e01144004226e114c0128a0445b004be80d15c058aa014590062a80455c012aaaa35f026b78111b80349e0092400521802980036cc013560049aa94d6c4c8de25c6d004a209318c488be23b5e03e368025100d8c200d7c),
    (21, 0x4aa02d5cc15ade0095404e370051f4014f80827e016be80255003ae20137c005b80149c8028fa00c7101cbf00c5f4018be0217c00abe8035c4012e5dd467006320419ec029180098c0773b802550088de0094401a358025f0048ce0094400a318025b8018f8095760463f0025b00f8cc07145005ac8135ac026e200b7001ab380b19801aec01b5b006bb002d4c0328800d6b0042273118c012c80447e004be00d1d8058cc02145),
    (22, 0x1b5ac014720029f8055670045600085800f58c00c540055ac00d6700718800c6e0031480a34a008d6c013660028d000b4301e0f001c5b00515c00c55014d7c013560020d003b53004db800b56008d2c0136e0020d000b430020c2ef1270025540856b002634075670025f0065650165a8015690035940416700e5980316500917c01c5300417800852002591ef46f0119fc0096400d5f802c760025b001c66004514009447ab1ac0d57f0025900c57d),
    (17, 0x2a3782d2088d60b701a3382d2048c61469063082d88a8f8425f1d2d831b054ae1b64052a0295014a60b7046bb02da0f8fc0b603633055ac1ace53480eb582dc01ace31481424075ac18b60a3004227918c16d02c7e05b8071d828cc0b48d62d82d2338a63c610e3e0519814881c5b05220314eb6d434690a3a0291038b60a440629c8d88fade0d76),
    (18, 0x1696c158c036004257029702b64029501a8c039f00a7c0294d6b72029a5556f531b80c7e4e97c2d7e08db40a5504db00a664296c5679131f80e780f1b832590a5880e78061b80c6c02188b257295f80a6c24d946d69191b85c5e14978104e021083a5c02970295202570185e02970085208d901a7c048f809280294c0b70d319c0c64579ec1c8c029240b804f9dc0b58),
    (22, 0x35ac0084403718c0094403316c00b64002d2c0b16e002df000b4b02659803d6f0035d802d6b0051c800b7200559c00d6301651800c660111ac01c7e0051980084400918c0147e00319800c5b0024bb5112b00d5ac02d67002dc001d65004da800b6817b1bc06e7f0195f800a6800897c00a5c002d9000a53002dc002c76002d8001c660031b800b4815f1ac22d7f002da021d7d004d60009580815cc1fd6f07d1b80857d01f5c400e8c01a97c00b6c),
    (18, 0xbb1bc3e7f0d5f8097c091d8096c051980944ab1acf57f04590092e375f40954335ccc56f2f1b8757d1b5c40e8c16d7c158c0360043570d5f40b58095c4147c031c00a56024d84372035bc3370051f40c71065f80c5f025f1b46703190ce7b07230138002630ae7702550446f02510346b025f02467025101463025b80c7c155d80964111f8096c0d198156b0359c1944),
    (22, 0x71f00146c00211003a4f00c92c00d7000891c0127c0029b000a430585980546a0035a00426f0029b00326b0035c0022670049b000a3e00298c10956002d980856f01f5ac00c7c01b59c0157e0021500556300d1b400d7c00917c0147c00211000c53006d9800d6a002d580793e0035940636f002d980536b0035f404367002d980336300ad7c00b77006d6c00b4e002d4c0092ee124cc0092e0115ac0092e00d59c0117c0024b801d6500459800964),
    (18, 0xecd8c09640b5f8097c075d81154021537b5f16dfc096412df809340ede83377025f02376024d01372024d31b5b025b30b57329bc0c7c231f8847c1e9b81c7c04df00a7c165f8157c02dc04172021f0307e0a1f01c7c049f0097c021c8326708de81b72029800a760209c09348cd4c1d6e049bc0a6313194147403190324f0a92c0d680691c0a640290dc96e035b45c5d),
    (17, 0x4b67ed981269eb4ef1a682990e6de0c7c31b5829f0a6ce0a6c063a0ed8c14d22a6e0e370496414a20a66b09b029569ad6147c053ecd59e56d5236609bd02dda14be347a163b08db414aa136c05333496ca8dc4c6c21bd035c066ec0b6c11b7031b026c40a593d2b82910c8f40a7c2a3b029b086ca2c5e11a90294024bc0a5c09b2028f814a60934),
    (19, 0x12ce602590423f01164010c81adbc31b38096c0a6cc029a0112f80a5c016c80294c049a01b4e0226c024d391b589d7d01d18235bc16c600c7d032a8031c0042a05d63038de02510063183c7c048be051f0042200c53022f8021f341b380b6458cf60763009c60098c54cee025502a3780944088d6025f01a3380944048c604db405b28096e016f88f1d919b78257e03af8045f804be20b67),
    (20, 0xc8c0d37f02d8c00d8c0193600c7c009340a37300a630093408b710237c01a7d0092400a710627e0247c011360093400b7103a720127d00a710217e0126f00a630097c8dd67009640436f009340336b0097c0236700934013630096e00d7c07676009640657e05b590456600e760324b00d7001e760156800b5c00a470115400854815630357b0148c0098c01d7701565009647db6f0b67f00a560116400864),
    (23, 0x36e2004d7c005ad8149670018f800493c005258129660012a8004d7c005ad810962007cfe00d9ec0173b8026730036fc004dd8005b300c93f0014c80115bc0052a00356b0014f800959c00abf000a54001ac601e4f80063c00667f0018d00159ec00a40000b80007cee0051a0005b40026730038f40051c80063500093785327600edac0049a002b690012f8006d9c008b3000964142ade0025900173f00097c003aec004d64004aa09dd6b0012a803d5b80763f00e47c),
    (18, 0x2590336f0ad9c2366064e81136024d32b6b115f40e8c0d5bc0d8c0958c145f0314c097cb8d9c0b644d9ec0b8c499dc0954111bc09440d1ac097c0919c09440518c096e02df0cc7630dbc1d72045f8097c28d9c9b6624d341b6e025b00b661c8e81462025b80a66148d80b66104e81a6e031880a66084d8156b0359c093468d8c1576025518b5f044dc09345cd6c257d),
    (23, 0x18f804299c005b600fa6600dad600252002eb1800d620098bc0109b801a2c802c510046dc006db000628000b4e0014cc02295400eb5800970001ace01a95000937000a6600a48a00b5ac004b8001d670028be00315c01122000a4400247c0028f405d31800c7c0026ec002d5004d2f803d6f006ad60025c0012b380157e0010a800358c02d1c8009490088b600257c018ad800a600042ae0051980052400094f00106918c4fc00ebd8015650012c80dedbc0273f80447e),
    (23, 0x326e0044b800496c9e1530756cc0075ec00ab2800b640714de01b9fc031bf001c640016b800219002137803a670016d800a99801122801a440014880028f818d3580bd7d001d1802b5bc006c6009d630038de0031b000631807b7c004ade005150005aa000d6300a2e00121f001eb78014540016a800958c00a2f800c530010680021c012d33800a64032cf6002a300c33b800a540088de00291001a35800a7c0048ce00291000a31800a6e0014f804add80913780147e),
    (17, 0x151d888dc14780b440519851c014e27567093302970b4d64d7d1daf831b056b6235705ae0319016a60c700533dc51916ac1466052a1c578cad65d6a2ab1835a886bc0d6219a90318444cc156a06b10297812ace13f0a330291048d6157d053e0319d527c8c5a3eb59d5a826900a482eb18558414bc436a0ab50358856a4156a06b10494814a00956),
    (19, 0x836d6051f404be40367016de1c97c352d86257028de0318c25298126f014c60c57c14ad82157026de02d8c04a98096c6f4cc0b19811a48136401472025b9a4a780b491ead63b5a805a48dd63028a802d20073d0bb5f03cf4059c8049b09b53126a2071a0092c80a410e2dc1918c2e308536e096c4055c006b40324f03ae005580053e01243014820259924a381458014b2315ac1d1f80b4c),
    (23, 0x86ac0071980092a0008440042bc0055a80053300095600c27e00559400532000c6f00827c00b16800eb500136a0014a00025580089b80092e9eb2b6040db401ebe00347d001ce000915400abe800a7c0014b2030d7c00dbe000d7d001472028d4c00ab2800a640048de00519800522000c6300d4c2006df400636800b550094be0101b00062a802b5f0016ac006d4c005aa800a5f0010c139455c004b6001c660026920025102263580097c0878ce002570009ab000934),
    (23, 0x10dac00524800c5b0056aa00519800522000c6b0014b343c57c0ca37800c650306de05e9b802233003b490026c80028e4010b7000a480010bc002110098a7804d6a0086a20091a000d2c800a540014820065b80052080096601c28e0051a00053480256f002aca0031a00053780a946)] 6) 11
def cert_links : Nat → Nat → Option Nat := unpackLinksPaged (unpackPaged [
    0x52020a4001460828c00518009b2013600268104c820970812e00258104b00094081260824420480208f0411c0823410468008c041160821c4043020850410a002140042800820c0fe181d4a03a80074040e8001cc103980072040e4001c4103880070040d6281ac00350206a000d2081a4003402068000cc101980032820620c0c400184103002060000c00017820299603d58003e00001,
    0x8e8a11b0822c2845410880a10f04212304144081060fa201f4003e8007b860f7001ee003cc4079020f2001e4003b84077000ed041da003b01074080e11c1c200384006f060de001bc0036c306d800db001ae2033c8067800cf00198183300066000c90c192003240063840c118182002fc205f800be04174202e4105a880b014160002bc1056060ac00158002a82054820a90014a202940,
    0xcb821970032e0064460c880190043200063c10c78018e0431c0063020c60018c003141060880b82416c102ce2859c00b3021630c2c60058810af8615f002bc0856840ad00159042aa2055400aa80155002a02853c10a70214d042980853000a58214a0428c2051410a280144042880051000a10414104278284f0009e0013c00278004f0009b8a1370026c084d8009a821320c248704882,
    0xfc821f4143e6087ac80f5801eb003d0187a000f3821e3103c60078420f0801e1003b63076c00ed021da003b20875440e70e1ce0039c0072c30e5801cb003901872000e4001c6083803070000e0001bd0c37a006f400dd061ba00374006e020d90c1b200362086c400d8021b000360006a080d4001a70434e0069420d2801a5003461068c00d1021a2003420866480cc8019900330086600,
    0x1358e26b004d6009a0313400267044c428984112f8425f004bc08978012e82257184ae0095c012b80252144a400944112880250044a00093c11278024e0449c0093411230e2460048a089140122022410c48008900011f0423e0047a088ec211c0623800470008dc111a842350046a008cc21190222e1045c008b021160022b0445018859210a0420f1441a1082051038220214400107e86,
    0x17d002f5145e808bd0017a002f2085e010bc00177822e7205bc48b74116e802db085b600b64216c802d9005b008b58216b002d6005a810b308166002ca0859400b1c3163022c50458220b040160022c00057e08afc015f022be0057c00af0215c082ae2853698a64214a0a2901051040a200144002850c50a00a1011400828000500009f4313e8027c044f0209e0013c002750c4ea009c83,
    0x1c9803920471440dd941ba82371106de10da851b482365106c808d7c51ab12355046a028d3c11a78034f0069c08d3801a40c3411c67e10cf8119d0833a0067010cd4319a023340066800cd00199043320066400cc021980032f0465428c945192803250064028c7c118f0231b0c63408c50618a003140062410c4801868a30a0c61400c20218010300005fc10bf4117d842fb005f408be80,
    0x2150c4222081aa903402058440b008140902802040440800810010182203004050480a0100051efc23dc0c7b020f5431e80a3cf0479a10f1c61e3803c60478c00f1411e2023c01078000efc11df023bc0877410ee801dc823b80476e08ed031d5923ab0075408ea411d4803a80474e08e8461d0803a00474000e7c11cf8039e0473228e6401cc023980072c10e5801cb003940872800e4c1,
    0x24402488009100121822408a4810090009200023f8247b108f6011ec023d8047a048f4011e8023c04474108e411181223000460008c001174322e0245b048b211160122b82453108a60114c022902450088a00114002278244f0089e0113032260044b0488e2110072200043f0487e010f8121e8243d00878090f0021e0043c0086c310d4121a8043404866090c422188043100862010c01,
    0x274824e60c9c03137c126e844dc049b4113506269044d2009a4013480268824d00499e0933c0267804cd08984593080261004bf0c97e012fc025e844bd0097a012f4025e024bb04976012e8125a8a4b01495e092bc0257024a818950012982251864a2049440128802500449f049362126c024d8049b0093211264024c804990092e1125812478e48e049181123002460048c00912192240,
    0x2c10058104afa215bce2b78056e04adc015b412b68056b08ad6015a812b30856504ac80958c12b08455f08aba1157012ad825580ca986152c12a50254610a8a0951012a00853a18a70114dc129a8452e1ca5c014b022948652510a422148012900051d0ca361145852890851104a200943432860250b04a140941c3282844fd209f6113d8527b004f4089e6093c81277084ed049d6113a81,
    0x2ec8a5d804bae0975812ea825d014b9a1972442e2885c110b820170402e0805c100b78296f002dd045ba00b74016e412dc025b50cb64196c802d9005b200b64016b842d7005ae00b5c016b802d6825a910b50096a002d4005a800b50016a002d4005a608b442168412d08059824b300166002ca8659500b2a0165402ca8058f18b1e0163812c70058e00b0a4961012c20058304b06016081,
    0x32d0a65808cae0995813298665108c9c1993413258464a04c8e1991813230064600c881190c13208464100c8009900031f0463818c62398c013180062f04c562184993090061200c201183c13068460d00c1a0182c23058060b00c160182813030860210c04018041300025fe08bfc017f022fe005fb04bf4097e022fc005f218be0117bc12f7025ed04bda017b012f28e5e404bc0217782,
    0x371006e104dba21b74036e026db04db601b68136d006d514daa01b501369826d300da409b288364046c704d8a11b083360826c004d7a19ad0935a006b208d6401ac41358806b004d5c11ab80357006ac08d5801a8c9350846a100d4201a78334f0069d04d3809a70034e0069a08d1a699dd633b8067508ce6119c033378266d08cd8099a433348066804ccc1199803328266500cc61197c4,
    0x3c30278408efe29df813be0477a08ef209ddc23bb0277018ede09dbc03b6067690cece11d9423ae127590ceae11d5033a80874e08e9811d2043a38273c2ce7609ce0339b8273508e6809cc823978672d08e5419ca413948071e2ce3619c6c038c8471804e2821c4c13888471004e1e09c30337f1c6fe00df811be8237a0c6f010de001bc00377046eb0cdd601ba423720a6e304dc601b881,
    0x40f8281b110321205c24071280d050180a02c14020e800110000200004000080000ff821fec13fd807f80cfee09fd813f78e7ef00fde01fbc03f48c7e60cfb851f34f3e6807cc04f9801f2823e5007ca00f9401f1c33e1887c300f8601f0423e0807be0cf7c01ef413de807bd00f7419ed843da827b20cf5e19ea073d08e7a004f3e09e7033cc0879704f2819e4c13c60e78a08f1209e1c2,
    0x44c008970512e0225c044a848950112a02254044906892011240224804458e88b011140a228044482889011100a2200443048860110c02214143f8c87f010fc0a1f8043e0487c010f60a1ec043d0287a010f4021e414398c873010e6021c034380086c110d8021a4343480869010d00a194343280865010c80a190043182863010c60218c04318085f110be02178142a9283d61048ca0804,
    0x484009070520e02408548100901052000a3dc947b808f5091e80a3c43478808ef091de023bc0477028e71d1ce023981473008e5051ca023901470088e0011be0a35c846b808d7011aa123540469068d1051a2023440468808cc1518a3a3140460888c10117a222e8345c828b709166222cc0459028b105162022c01457048aa11154022a41454808a8051500229c14518889929132022601,
    0x4c7889881d30c1261804c282985013041a60414c002980012f8225f004be0097c012f0225e004bb82977012ea125d404ba0296b252d6025ac04b5809680d2c62a58424ab16956012ac0255414aa80955012965252c04a30a9450528a02514049e9093d012780a4e824998e93301266024b464960292b052405a4800490009200122e4a458148a0490d1d2180a43004858290a05210124200,
    0x50a82a024d404027fc34ff809ff013fa127e834fd009fa013f20a7e404fc029f8013ee0a7cc44f9029f1053e2027c404f7069ee013dc027ac34f30a9e30d3c01a77434ee809dd013b80a77004ee009da093b40276804ed009d9053b20276014ec009d8013a04273434e6809cc053960a72c04e4849c9013900a71824e08a9c10137a226c4c4d8029b00135a1a6b404d30e9a0193400264cd,
    0x54e82a9d0153a02a70154c08a980153002a5c154b02a92115163aa2c054502a861150c02a18053e92a7d014f80a9ec153d80a6f314d81a9ac153580a680d4d0029a0053400a64114c802990053104a61054c202984052f84a5f014be02974252526a490549202920152304a460148c02918052204a392d472028e4051c80a39014700a8bc951780a2f0145e028bc051780a2f0144c4a8590,
    0x5ae80b5b0969e62d1c85a302b460168c02d08459728b2e0165422ca8059386b260564422c84158f84b1f0163a12c70158e00b181162e0ac54258594b090961202c1c258302b02115f832be045749eae8055c822b90056f0cadb0d5b40ab64156a88ad5015888ab0c156102ac20158402b04155e88abc055760aaec055798aae0555a0aaac255484aa70954c0aa8c355180aa00d54002a782,
    0x5f88cbee0d7dc02fb025f600bec017d21afa405f480be8057d002f9c15f188be3017c602f8425f002be0017bc12f7805ee82bda0d780d2efc15dd88bba0577402ed845db00bb40976802ec825d882baf0975c0aeb025d600ba6197461ae7855cf00b981972e0ae5815ca04b930572602e4035c686b8c0571412e2415c384b81197000adf045b71cb6e016d61adac05b484b5e2d6ba0ad740,
    0x65300ca6019461b28c065180ca00d9400327c164f80c9d0993a03270164b0cc960192c03258064a04c910d92203244064880c8d1191a03234064584c8b0191603224264480c890190c1b1f8862fbec5d098b22316016290cc520189a2b130162504c470d88233100161f82c3f0187e030fc061f80c3919846b3084261080c1e0d8361b06c060c84c180582c1301905ff8ebff017f81afdc5,
    0x69d02d370da6e034d4269a80d320da64034c8069804d2a19a520b4a0169382d240da460b48c069084d1e0da322b458368b00d1409a2803444368880d1101a1a23434068680d0c05a121b420168304d0601a0a0b4083678a2cf1019da233b4067506ce6119c813368a66b08cc34d9860330c066180cc3019801b300065d8acb51996a032d4065a80cb3099640b2bc36548cca805950032982,
    0x6f482de805bc62b78c06f006de001bbc1377416ed84dd615b9c4373416e584dc615b8a0b6fc66df02dbc09b78036e826dc82db121b5a236ac26d502da611b4a0b68c26d102d9f0db3c0b66c36c69cd8b09b140b62026c400d8801b100361046c200d8401b041360806c082d8101b000b60006bf82d7529ae80b5cc16b980d6a25ac24b54ce6a884d4a1da920b52016a208d3d1da7a034ec2,
    0x74c84e9025d2003a24774480e8805d0823a10074104e7e11cfa0b9f4073e02e7c01cf8039e8273d00e7611cec039d0273a00e7401ce8039c0473800e7001cda1b984c7252ee4809c8c13918072186e4301c82138c1171704e2b0dc540b8a0271400e2705c4a13880570e86e1d01c361386c070c06e0c31c1413828070404e0801c0e0b80466ff06dfc09bf0237cc56f902dee11bda0b7a83,
    0x77e82efc05df803be8277d00ef809dec13bb0a77504eea01dd403ba0277400ee411dc21bb84076f06edc09db803b6c176d02ed905dac1bb54176a80ed309da603b4c076884ece0dd922bb24076384ec701d8e03b14276280ec309d648bac8075786eaf01d5e03abc075588eab01d540baa8075482ea901d500baa0075382ea701d442ba84175080e9f09d3e03a74274e80e9d01d3613a6c0,
    0x7b480f6901ecc1bd9417b280f6405ec803d9007b104f5d15eba03d7407ae02f5c01eb413d6807ac04f5801eb003d5437a80af5001e9c13d3807a700f4c09e9803d2c17a406f4801e9003d1c17a380f4701e8a13d0837a100f4105e7633cec079d02f3a01e720bce4079c02f3801e6e0bcdc079b80f3509e6a03cd0179418f115de2203c40178800f0f05e1e03c3c078684f0d01e1a03bf8f,
    0x7ed00fd809fb003f5827ea04fd305f944bf2417e480fc805f9003f1c17e302fc601f8a0bf1407e202fc401f725bee407d812fae09f5c03ea457d480fa805f5003ea007d400fa315f4603e8c07d084fa101f3e13e7c07cf80f9f01f3e03e6857c61cf8c01f160be2c07c502f870df042bde497bc80f7901ef203dd837bb00f7601ee813dcc17b980f7109ee203dbc27b50af6a01ed20bda40,
    0x8250504a020901411c1823810440e0860c0fc481f8103c0e078040ec181c070380206c140d8081b01036020622c0a878150102906052040a40813850231203e2407c080f8101a1603404068080c830190202e1405c08080f00d0e01a0403408068100c060180402c1805810090a01203ff8b7ff00ffd05ffa03ff017fe00ffb05ff603fe817fd00ff905ff203fd447fa80ff015fd043f68e,
    0x85b010b40a168042d00859050b202164042c02857830ae0615c042b41856030a81214e0c29c085285095421261424818470908c0a118042243844810860e1003420008400107f060fa141f4083e8107d020f6141dc483b8106a360d4041a0283383067020ce0418c4831810610a0c20418018300105e0a0bc04174182e8105d020b614158582a05053060a40c144182881051020982c1300,
    0x8908911f0a23e04474288e8111a0e2263c44c0889031100a2200444008880110f062181c43008860110c02214144202884011080220c14418088301102121de9c3bc0877030ee021da0c3b40876030ec021d60c3ac08730b0e40a1c8043882870830df0a1be04378186f010dd061ba04374086d070d5161a41c3249864030c802190043143862030c306176442e8185d010b906172042d83,
    0x8d2811a40633c3467808ce8319a0e32c2465808ca831930a31e2463c08c78118f0231e0463c08c78118f023103c62008c3051860230a0c61408c107182023040460028be0917c022f60c5ec08bd0317a022f4045e028bc01178022ec145d808bb01175062dc3c551a8aa01154022a41454808a80514f0629a144f8f89f0113c0a278044ec189d031380a25a5c4b40896031281224a1c4940,
    0x9160522c024560c8ac09158122b0242ea4854290a812130a426048403908012100241c1480cb901812010a402047f838ff011fd063fa047f018fe011fb063f6047e818fd011f5163e80c7c438f7851ee063da0c79878f2051e4023c80479008f1831e10a3c20478408ef851de063bc0477418ee811dd023b80c76828ed011da023b01470968e1011c20236e5c6dc08db811a54a34a046940,
    0x95a092b4025660cac81959012af0e55c0cab02956012ac025560caac0955812ab025540ca9459500b2a00254004a78294d8729b0253604a64294c81299025300ca60094c012941252804a4829490128146502049fc293d8926e364da0c9b409368126b0a4d6049ac093485265124ca04990193201263064c604988193101262024c01496c591ebd23c064760c8ec09181722f0645c0c8b80,
    0x9ad1934e3265914ca04993833260664814c68a98c833180663004c60098b833140e62804c500989833130262214c440988032fe4a5fc04bf8097d092f9065e43cbc80979012ef0e5d624bac0975812eb025d01cb982973012e5065ca04b940970892e1025c204b7c296d892ce3659c04b2c3965812c61658c04b141962812c40658804b0c1961812c20658404af4595e032ba0a5720cae01,
    0x9fa833f5027e80cfcc19f7893ee067d61cfac09f5813e80e7d004f9c19f3033e5067c80cf9009f1833e2067bc24f6c39e8953ce0e79c04f3809e38f3c50a78a04f0c29e1813c10a78204efc29df813be0677c04ef809de053ad3e73a84e7409ce8139a0e73404e6809cb8738d2a71614e2429c4813890271204e0c69c1813830270214e0409c08137f0a6fe04dfc09be0737c026e064d98a,
    0xa73854e3129b44d3680a69114ce12994253280a65014c222984053080a5d114b612964252c80a59014aa22924c5214da41074800a900052000a3c1146d2e8d61518c8a2f0b45c0a8a8451500a2a0144f168942d1202a218b44302876450dc4a1b814370286e050c07a180142e0a858150a82a150142a02850150a00a14014280284a1d0940a082b3fc527f804ff009fc873f8067ee0cfd81,
    0xb018160302c06057fc4aff815ff02bf81d7c0caf8015f002bdc157988af2835e502bca057940af0895d922b9a656968acd9559712b2a156540ac90759202b24056402ac31558212b04056002aba9757502aea055c44ab80357002ad825588aab00556002abc15550aaa78b54f02a981d52c1aa38954702a82354d0da8abf51502a26154481a870950526a02253e09a7c014f60a9e4253a49,
    0xb4d1369a02d320da448b488169102d1e15a1c8b353b66126cc00d95c9b251b64612c88159100b220163d1ec7a058f01b1c0962e2ac54258984b130162602c4c058941b108962102c3c1d848cb090161202c20158400b080160e0ac0c4580c3] 19 6)
  (unpackPaged [
    0x21053c0dd34f0370d2c0d43470310d0c0bd24f026491c0bc23f02608dc08104602000d807846801c1160068468018116005846001d15bc06c56301909bc05c25f015095c04c264011091003c24400b114003426c00801b802c56400a091001c07e00804d001c343005118801045a01255bc04156301211bc04046300e517c03845b00c115c02445300601b800d05600301181f956f07c558c1f846f07c118c1e945f07a116c1e0457075114c19436f05b4d7c14535705b0d3c14434704c05b8125156049051810013e03901b807c066014415805004600200fa7aec5fa1eb16e4f2c579cab14e7ae35fa1e8d6e4f23579ca8d4da8a34f6a2ad2c7ba3475de8d0e878a5f9eb296e728a5793c294e319a4f853692dc27a47709690e318a3f85328edc2723770928ce87815f9eb056e72815793c054e31914f853452dc26947709450e31813f85304edc2613770904cda8892f6a204ad7781271ee048c6ee05f1bb016c552057154014c2ba84f107a12c006847080a10c2ba03f10780ec00603708080cc41c82f0ae20ac200827001208c41c01f0ae006c200017001004c00003f,
    0x4f05f811813e03c01f80c4076076011002403e07411d01a807407301101c467806e11401a407407001b01a006406e15901b447406701d01b00440680d001a045406a4d3c1a834b0690d1c19c343072517c1c845b06f115c1ac4530660190065056019011819047406301d0178044061119018006405d011017856f05d158c13806e04b415818867f05f19cc13417e04a45980ec07e02f01d805d06605c011016857805901d015005c05715a0158064053017015056f053158c16067f05519cc0e807e02601d8055066052017014003400700b813803404f0d0c13524f04d08fc01802e0228d8808647204b916008407604b0150082462003916812825f020019800c02e04405b810c27e048091011c0440450d901100340430d0c11845304209b810525604109180f434003d11500fd34f03f0d2c0f834703c0d0c0ed24f03a491c0ec23f03a08dc0e037c0340d400d85700330d000d046003311500c837c02441180c037c02141580b436802a0d500b446c0290d400a835c02911900b835f02c0d6c0ac3570280d4c09c470023053c09047c0230dc00883480250d8001634a,
    0x10511bc40c463101517c40445b0ff115c3ec4530ea0dbc38135f0d64d5c38034f0d60d1c33c06e0c301982ed0560bb01182bc03e0a44dbc28536308b49a82102320aa0dec29c37709f09e824c27208208c82ac3540aa158c22926a08a09682a048c0a7114c22525a08909282944640a419ec27827a09109c822126a0a20d9028467b09d09e823427208749a827c45309e4d7c27535309e0d3c27434309a092025c23409a0d3025823009708f025834409b08fc26423b09808dc2542330940510248144090097c23c25308e04d024c4530914d7c2353530910d3c23434308b15ac22836b0890d9c22035f0870d4c214144083051021156b08411ac2084530ad55ac2b446b0ac114c2a436b0a60d9c28d35f0a04d4c28c34f0a00d0c27026a08c098821925a0860928204232063493c1652470624d7c16135707f019007505601200f818125f056495c17d36f0554d9c06d06607d011004003e07309bc1c837f03f01f80dc07607b011003803e07009bc1dc45006f0dfc0f807e03501d81e406c00c00f81b836f03d01b80cc06600b00f81b026f05001b811c02e07715901ac37f,
    0xfd11403d437f0d401f832c07610001b02cc03e0f4097c3cc36f0d301b83280660fe01702c803e0f109bc3f45640f00dfc34807e0c801d83010640c001503f00440b000f83e84740ef01d03e40440f40d003dc6780f311403b80740f601b03b40640f401703cc5640f211d03b00740bf41902fc0540f101103b43400ed11503bd34f0ef0d2c3b83470ec0d0c3e145f0f8116c3d44570f0114c3ac0640be41582f80460e911d03a00740e301103984640e501903880440e315bc3885630e719fc3906730d101f83180760bd41983840440df15e03780740d901703705680db019036005c0d915bc3605630dd19fc3686730d001f83100760bc419835c05c0d30d0034c4540d54d3c35434b0d40d1c3483430d1493c3412470d108fc3402370ce0df03305700ca0d003284540c90df031c37c0c511c033534f0cd0d2c32c3470c80d0c31924f0c4491c31823f0c408dc2fc26f0bf0d4830856f0c1158c3003520be09bc2f425f0bc095c2e82640b809102d82440b211402d026c0b215902c42440b955bc2dd5630b911bc2dc4630b5517c2d445b0b3115c2c045310555bc40d563,
    0x149123051818c1480510518343147114c51417c127455849c1461431190508164140051050056b115018843285a14119ec4d017e12f05d849516613f051044807210b41a84f436413c05904e813413a15ac4ec67b13205f84b817612345984e413404520884dc36404320884d436413309904d8343134493c4c924313408fc4c823304220884c034312f493c4b924312f08fc4b823312c11604a825c12811c049845812409704ac56b12909ac49c267125097c48c253109a168104822121091047c24412055ac48046b11e114c44002e11b0130464034119049446823711800d8470144117011043c03e1140d7c4541441130110444244110011043c453116114c44935f1120d3c43803e10c855043005410a015842c35f109855842403e15255ac54846b150114c52836b1440d9c4f935f1384d4c4f834f1380d0c4c416e12d0598489156122051847413e10d018842105a10801281008320e8493c3792470e74d7c37535710601903090560b900f839525f0db495c39136f0da4d9c30506610401102dc03e0f909bc3e037f0d501f833407610201102d403e0fe0d003d826f,
    0x1774d8461434918115806004501830d8460435118015905f136917c0d645fc34917e0d205ec46817b15805e823417c15885e446a17715b861145f184116c60845717d114c5e135b1764d4c5e034b1760d0c65156f19415ac63c567186158c5a106616801585d404c15620f055802c16a049c5c845816e28f45c046016c28f45b436c16e097c5b025716a11885a43501730d485c4a5f16f295c5aca3d171057c5bc15716b04f45a012715b08d8598144162114056823616405b056423611120b858856415708d858414410f20f857c14415d0570564450159159056034815b517c56c45b15a115c55c453165517c59445b163115c58045315e4d7c57135715e0d3c57034715608d843883e1b9517c6e445b1b7115c6c84531a96d7c65db571a92d3c65cb471a9497c65d2571a9093c65c24717408dc43493e10d04b859d056167011855483e15500b850925f13c494c50536f13b4d8c4ad166153051048013e14e09ac52026711c018812082214d0dec51c37713605f84c0176151051047813e11601c811883214f0d5053815414c04d053045314d158c4a5166129055852c134,
    0x1e7093c7842471d608dc73c16e04ca5581321461c841587200461bc20f86f002e195049c6502371ba011059483e16500b86d8340190049c6d445018f08dc6e006c16320f858c02e18b049c6282371b6017058883e16200b846882e1b428dc6d0137187049c45c82e11700786d456418608dc45893e11604b85cd06417301506cc04416020f858002e1ad01906c446416e61d06b186416e01506b004411420b86b43541af0d7c6b83571ac097c69da571ab08dc44c82e1b00dbc699b6711224f85c506616b01506a804415e20f85b586419f013067c4581a815a05b18741a7019067805c1a5013867004c1a415c066d87c19b017066825d1a0116467c45819d118467046019a15a868845b1a1114c67825f19b095c66424f1a60dbc68c36716f419866005c15c20f8658458195015061004c15b20f056c02c18e158063445018c158064c03619200d062c45018a158064447019001f060804c15a20f056802c18e00d863403418c118062c06c180013056483c15900b056084c17e00f056002c1880d285f834818a19d062445816a41d05a806418701505f404c15720f055c02c,
    0x5cc55bd70d56b5a8559d6195635cc11bd70c46b5a8119d61846357c517d5f045b576115d57845340008d0f8c16f3da05b8f3c16a323059cc541663090588aed15f2b245687f11571ef4558aec14f2b205287f01471ef05187b206f1b7819c3fe85f078a15c3fe04f078811c77c2371c620f871802e1eb11407702371c420f871002e1d908dc70c83e1c300b87ac5641d708dc74217e1c120f870402e1d505f87a44641d406387a036f1e56d9c74c17e04da5987350661bf20f87985681e4013878c5701e50dbc7883671cb41986f483e1e0116076c5601da15807780361d915807744701db00d87684601d205f87646741d8116074418e1df55bc77c56b1dc159c75c5631d005f813e96604f85587250661c901587543541d4097c7483481d1114c7423431d3693c74ca3f1d3453c74c13f1d0049c7384581cc11807283501cd297c72ca571cd057c72c1571c9049c71c1441c3114071416c1c315907081441c005106f815c1c6517c71845b1c4115c7044531bf4d7c6f53571bf0d3c6f43471ed517c7b445b1ec115c7a84531e76d7c785b571e72d3c784b471e7497c785257,
    0x23711488e445b238114c8d834e20105588c835023009b08bc24c234093c8cc24b231091c8b824322d09807fc14626c15bc9a456b25d159c96456325811b895846b25511a8948466250118c93c462246116c91045a24311588e84532350da88b036621405987f815622a15948a447822811a087012421b049089468c21a0490864124218049088c58c21e11a0888458217049085812421e158885412421b15f086447c2160d60860348216114887046d21a117c85c4532150d2889857d22415bc88456322011c087c46021d116885012421211c084003620f11c083435421119d883857620c11c882c46820a116082437a202049080412420004908105701ff049080046020255a880546a1ff519880836a20109a87fc26620759e881557a20355d881c47a206118081437a2030dd87f81242a819fca9467b2a119dca7467329b15f8a6457b29815e8a5457629315cca4857228915aca1c56a28515989f056327711e89d847622b08d089c17e21305d882016e1fd05987e05651fb11a07e44701f815d87dc4581f511c87d04701f211607e856f1f615ac7cc5671f1158c7c036a,
    0x28b1238a2848224608d091423421e05d8a2067224408d087417620b05b082814424308d0a1816c24208d090423428315d09fc48c27e115090023423f08d0a0457423e08d08f423423c08d09fc58827e15e08ec2342841e38a0868a2801a089e858a27d12388e823423908d09e456c23808d08dc23427915888d823427b15ac9e856327811788d423420905b881416622c08d080c15623c15b09bc16426e05509bc25826e09509d446a27411a49cc468272119891c46124e11649084512710da89c036621a05d89b416626b11649a8458201459080115426704d898c14c26004d09801402650934990249262091498424125f049897057d26811c499847025e09c07fd15423c11a086016625c15f893446924511a096c45925a116085c17623c118090445024c15a89005622570d9880815625411b094c26023f114092c56a23e158891c36a2510d9892847c2490d1092847824911a08f035c24e19f893467224c15e892c57223911e892037e2470dc8858166245158885416624111908f437c23c0d108fc46423d11e08f046824219f890057a23e15c88e047a23b0df88dc45c,
    0x2c10490afc0662bd0178c0867f30019ecbf86772f919ccbe05762f711f8bd84762f51198b442342ce05f8b241762c405b88211662bc0110ae81642b80550ad817c1f80518ad01542b915bcadc56b2b5159cacc56327508d09d023427308d09f867c27208d09c42342ab05d09c02342aa05909bc12426e0490aac3682aa0d909b41242b115e8ac05792af15e0ab857628a15c4a445692841584ab447a2ac11d89b02342240618aa417626b08d09a82342a715a4a9856826908d081517426808d099c12426608d084816c2044590a8c1462a01a34a905812a2160097423421105b080d16427e15e097023425b08d096823422205d8a8068e29015e4a2057829f15a4a7856825908d088418625808d0a7016427e15c0a0c56025708d0a3c67a28219c8a6847625608d095423422905f081c166228051095023429715f094823429605f0a0456025108d0a3867a28019c8a2847a29411d894023424f08d087c17420c05b888014424e08d093423428d1630a3045424c08d092c23424a08d092423428d1620a3057824808d09f846c24708d0a4478e2901e08a3c68a28e1a089ec58a,
    0x30f1140c4816c3100570c3414430e0d34c3445430f1590c30144313517cc4c45b311115cc2c45330a4550c281442f408d0c101642f308d0bc82342f108d0c1046430815d8c1c57430611d8c144742f008d0c0c1762a00514bbc2343011190bb823420945d0b0c0442ed08d0b2115c2fd1a34bfc48c2e808d0b1d16c1f80510b9c2342e608d0b942342e40490bf468e2fc1590bec4642e308d0be80642dc08d0b1c15e2114558b6c2342cc05d0a701642c60578b4c23429605f0b3c16c20e4558b482342cb05d8a1816c2c50570bd04662f31190bc83662f10d909701352ef0d50b08034263053098c1342ec08e4bac2352ea04b8b9c57d2ed0df0ba42702e715f8b984542e50d50b900542df09b0b8824f2e1092cb802472de090cb742602d709b0b580242da093cb6424b2d8091cb542432d40980bc056f2ee15acba05672e3158cb704662db0db8b4c3662d20d58b040342d01190b3c3742960d90b3447c29c0df0b3036c2cb0d58b2807c2bf00d0b2047c2c759d8b1957e2c711d8b154542c60df8b143642860d50af50542bd00d0b081242c2116cb002602be0920b0c56b,
    0x36f0d2cd9c3473500d0ccfc16e33f057885114621404d8ca406e32501b0d3838c3460490d283503450490d305803490d00d101243430490d284703420490d041243491150d2038c3400490d0c24034511c0d082303430d80d0834434109f0d1923f34608ecd1023734008ccd3534f34d0d2cd2c3473470d0ccfc12433c5178ccc1243320490cc412433c1600cec38c3300490cdc35032f0490ce45803360d00cb812432d0490cdc47032c0490cac1243361150cd438c32a0490cc934e33211c0cc427c32d0900cbc47032c08c0cb436032c0d10cac27c3334d84ccc26133048fccc023b32e08dcca823333d51c4cf437133a4d3cce834b3380d1ccd03433290490c9812432608ccc9c3433250490b2904e2ca00f8f2d57f3ca55f4a555753c255ccef156f3b5558cf2c47f3ca11f4a544753c211ccef046f3b5118ceb945f3ae116ce9445738e114cd3c23433e05f8cf816e2c9457884d1562c9053884c14632801f8c9007c3220df0c8435631d0d40c7c57031b0d00c7446031c0d38c6026031b1150c6837c3190db0c5c0343204d3cc8034b31e0d1cc583433140510c40340,
    0x3270230e3c04438d1590d9834038759c0e2146038c11f4e1947136e1174e2c4553744d38d9434237f51bcde94633640d088711463881190e1c3643845150e1036436d0d50db457038411c0e1857d38515c4dcd45e3830d58ccc07c21b4558e0056437e19c0e0457c37f11f4df445521a4518dec3642194518de057037a15f4de437c3770d5885d15637600d0cc807c33101f0db457037415f8dcc5723720df8dc437c3700d58d1817e34605b8cc007e36d15f0d8c3403620d40db446c3610d40d8035034505f0cbc07c35f0d40d7825035d0d40d1416e3690518db857e36c15e4dac57236a15c4da057035b0d00d1017e34405b8cb807e36611f0d8c45c36211b0d8845c34305b0cb406c3430578d7814636311b8d844693601188d7c46135d1180d7034e34205b8d0815e32c01b8d0417c32b01f0d0416e3590578d6005e35608e0d5456e3530988d4826036555f8d9157c36511f8d9047c35b1150d6837e3570df0d5036c34005f8d0016e32a01f8c9807c35100d0e2946f38951b4949465382518cdf145f375514ce2836f3890db49483653820d8cdf035f3750d4cdbd34f,
    0x2244558dec2343bb11d0de823437908d088d15637808d0ee068037708d0dd81243ba1a34ee448c3b71198dd42342214598ed804437408d0dcc2343b30630cf008c37208d0d3818c33b0230dc423434e05f8eb068037008d0ed068e3b21a08ec448e3b01230ebc46636f08d0d3418e34d05f8ce808e3ac1a30e8445036e08d0e8046036d08d0eb057c39f1180db023439e1180dac23434c0630ce408c39d1180da82343698d80da412439c1180da023434c05f8ea015639a0d00eb468e3ab1a24ea86823a91a04e9c6803991140d9c23434b0638d2c17e3a605b8ce008e36608d0e9058c3a115b0d9423436408d0e8057c36308d0d882343a015b0d8423436008d0d2817c33701f0d7c23436d8550d7423434a05b8da615635c08d0e8457e39f15e4e7857239d15c4e7057039b1178d6c23434905f8d2416e39a0578cd807e35a08d0d2018c3350230e5c57c3590490d6012435708d0d2017e39605b8e5406e35508d0e4c67e35408d0d4c1243520490e443723900dc0d441243a35a38e8968c3a31638e8858c3991590e6048e3941230e4847c35008d0d1c18e34705f8cd008e,
    0x3f4093cfcc24b3f2091cfc42433f00980fb835634605d8d181663e90d40f9c2303ec15a4e7e5613e60d00d101763440598dc01653eb0578fa44593619144fa034e3420598d081563e70538f9845434005d8d001662585174fbd4552580d74fbc3553ed4d3cfb434b3ea0d1cf9434333f0598cfc15629b55b4ffd56529b11b4ffc4653fd517cff445b3fa115cfd44533e408d0cf817633e0598b3915e2274558b3814e2270518f883643e015a0f783403de1150f743743dc0d90f8534f3e10d2cf7c3473db0d0cf644663d80510f4c45032105d8f5816c3d41178f4c5643d20510f440443d7517cf5c45b3d5115cf4045338d08d0f386743a41140e302343c85e00f2557038b08d0f3458d3c75604eb456d3cc1594ed145e3a31148e282343bf55fcee95733a21148e2423429c05908991562cd0530e2023438708d0f245743c811d0e182343c55590f144743ac1190e1423438408d0eb06803c51600e0c2343b35178f1c68d3c61a04ec956e3c41198e082343c30630cf408c38108d089516638008d0f0067437f08d0df82343be1e00df42343c11a30efc58d3bd1594df0234,
    0x427095909446841c11a108c45842111c107c45841c15a909056f42215ad08056741e158d07446241b1169064464418099102412440b0991058254408049101002441409f103426c407049104414c4120951018124410015103446540b11a902445f408116d01c457406114d01045b41715bd05456b413159d03c56340e0db903026e40a0959014124403009127145f49a516d259457492514d27035f49a0d6d2583574920d4d23d34f48f0d2d2303474850d0d1dc25f463096d160257441094d0c924f426492d069247402490d0c823f42608ed06823740208cd55145f54a516d3f54574c7514d55035f54a0d6d3f43574c70d4d30934f4c20d2d2fc3474a20d0cf9015f34f055cb4514f22b451cb4413f22b04dd00412d1eb817c6d60570fda13c1de8470fd80fc1de0373ef08d0a5817c22a4558b4014c3ee08d0ff84663ed08d0d3418634d05d8fe44603ec08d0fdc3403eb0490ff06793ab99c4fd84503ea08d0d2c18634b05d8ebc17532105d0fec16e3e908d0fa02343e70490fe456936c9584fe045e3e608d0d241763490598fdc15e3f61590f942343470618d1c176,
    0x48451552103554824d3d20834b4800d1d1ec34340e490903823247801511d824446a04911c834047111411d026c46904911c825c46804911bc13c47115911b126446c09511c024446704911b804446500911b03524680d011a045446a4d3d1a834b4690d1d19c3434650d0d1d545f475116d1cc45746d114d1ad25646b0919198124464009118437c44f098117c57045d0d0113826044d094117445445c0df116c36c44a098116803446251b518836d4604d3d18034b45e0d1d164343449094113c374448095115c244446049114c45044e0dd115426c4450491134364452091111012444c095114845444b099114c56444a0dd1144244443049113434044c08d113034444d115112c23444f4d3d13c34b44e0d1d1283434480d69110340444115111934f4460d2d1143474430d0d15945f456116d150457450114d1243644334d790cc34e447495911c246442049110036443e0d510f047c43b0df10e44544380d510dc05443f15bd0f456b43a159d0d85634350db90d035643309890c426442f09510b427c42809910ac25442811890c056f42e15ad0b056742a158d0a426e,
    0x4b549512d42444af00a12b40244b345252cc1394b200792c40124af04a12ac13c4ad00612ac25a4b60da92dd2554b709152d823d4b404a92c01284ae00a92b00264aa00912a036a4a709b92982664b8096d2a42531da817c6320574a500bcd4405748600752f44544bc0db92e83663e505bcd401674b904d529013448504b476606f18a819d28c0344194904f5245d4a1116d28045749f115527825b49d095d0fd24f430492d091247417490d26c35643d497d0b925b422495d05525343c493526446d4950db526026c49709810e924f42c492d081247413490d0e524d437453d0411434950db9250356436497d0a925b41e495d03d25349300d124436e4900d5920826f47509ad180267456098d2283404891140f5256e3f895ace6e56331c958922034048009bd1cc26b45e099d15026348e097d2342533e8916cd7245348b0d391f425f471096d174257453094d22824f489090d16c26546e056d168157488115121c36e47b09bd1b426b459099d14026348600d11fc3424830d911f835048115a11f434047e11611fd56447f11911f445447c0d911e406447a09711e4233,
    0x4c900d13e42394de04d13e837c4f809c13741344f508e13cc16c4f104d13d835f4f40d6d3c83574f00d4d3701344db05113b035c4eb05713641344e9091135c1444e804913b824f4ed092d3a82474e7090d3501344ef0db13982604d304d0b9d14f25c451d25412d377059cb9914d49404b53842494df09853781604da090136013c4d208ed33c2334dc04fd36c13b4d904dd35c1334d604bd3541234d108ed3382334d405413481604d1119933c1604cd04a13343564ce11993301284e0116d3744574d30d5934024b4cb090d32445b376015cb9104f49300753ec56b4f7159d3944664e40db938c356375059cb8d15f259455d3881354ca04d124812d4c800d124412d3ee05bcdc016749004b531836e4c50d993103563ed05bcdbc1674c304d523c12d3f799e8e6a67236c15e8e7e5724be0d00fac17e3d395b8fda56b3de95a8c3e566399958cc6e5624bd0d00fa816f367059d30415f4c0057490c15548c04b4f9e56a36111a8d864623e705b8f9a45b35b914d22234e3e6057cd6c1574be053d22012d354059521c12d4bb09812d83624b608f52a003d4b504a12ac024,
    0x23404d543012d505049545025426345714b446e4ed11894b035d5240d554ac2565240954b8414d233051542c13d50404d499112d52a049549836c52305b147006c51f0531498568522057146405052315a148825c51b017146005051f09793ac252263457147056851b017146435c51805714a0569524117944445d5270db93a83625250d79490249513090548415e520057547815c26245554741522e004f48c413550a04b540c12551a017945c05250f049145025c2df04f48c013550f0d793a035251511b939c4625130d5544826c51108f8b7814d22e051542413d50204d544012550e049098d15c50c0d7942c35a50a0d5942435226449694202562ea4579404136501049941835a2624d5941425e504096940c256502094897d15650104f940412e532117d3e14535310d7939835252e093d4a424b516091d4342432e9453c9791472dd04f48b413550704bd25c12d500049c94c125497098152446f54811b4c3e465546118d51445f4f7514d51036e4e40db551035e4e50d494d02624ff09813f816d2520594ba114f25d451cb7013d22c04d525812d4fc0d51380134,
    0x4a4049077606f191819d58403f4a30490f4406a38f019cc5c0664bf95915d047e57211d92882343f505fcf6c17e3d005e8e3817731605d8c2c17257105155801441dc81fc63e07755f01108f146855805949c515555d051528412d55b05f49c91755570554bd114d270451528012d37d055cbcd14d49f04b49bd15426e45109c9465558116555c45526d451954d46b545519cf4e45d55c116d568457559115554836a5440d9951035654d0d54df016725805755581575550554bc114f26c451d27012d4fa4d913bc354550049154424f511092d4ac24754f090d53826049b04b554c56f4fb558d54846e54d0d995303562ee457c9a5157235051552c13549a04b43ce85f06ea15d50c27049904b499d361542058150427054705113f157c53209c14c4260511094550024d53d09154f0255511092550814454015f14c037c52d11f147c26c53d11f14f04705270df14ec15c53815b143c36c51511f14e427c53709b14d812454311b55044615310db14fc24f53e092d4e8247535090d4cc25953008fd4b423b52708dd4542335300db93b836252c09654ac24552f0514b8813d,
    0x58815ad3201243b6019cbe905f5a619ed68c67759815d965c47e595119931c2343b505dcbe516f2b345a8a751671f14599650145589051161c0443d995b5318234585059131423458305f0f6667e3fe99ecebe67332199c93124504c408d0ff817f3d905e8ebc17732105d8a1816c4c308d15fc36b57e0d8d61047e58211d96044664c208d0ff417f3e105f8f5c17a3ae05dcc8017631305c960014557d0510fee78a3a69e08eac68a3ab9a093064504c108d0fec18e3a6061930023457995bd5e456757881695e00563d599f8fea67b3df99e8c466763a599ccc7a6724bf91412fc2343fa05fcf7c17e3d505e8e9417731e05d8c4417257b05bd5ea16e57a05b55dc16c2850594a161624bc08d0e4817531905d15d41644ba08d15cc17c3dd05b12e423456e11c95b834d4b8049159404d4b704912d812456800d15b423856a00d12b812456809315a892856a00a12b00144ab00515a036a4aa00515b847a56f4d955bc35556e0d355b0a3a56c04e92a412456b00e95a403656700d159047c4a804915903784a7049129812456511e958c37e5620dd92941245700dad598363,
    0x5ab0600f6646d54808d17041642a351c47e54705b629c16d817054704916d4b805b50a015182345b006316a81805bf055169d68c54508d16b418c54408d16f01545ba11f56e427c5b429c16d815454e08d16dc57d5b515c56d037c5b30dc16c447d5b011c53f82345ad117d6914531f945516ac57d5aa15c4a5817c5c215fd70057d31195d56f85735bd15bd68d5635bb11f965c47d5bb11b96604625b82df96c8b725b809f96c82724fd08d16bc17e5ae05f56b017c29505d56a41722fe457cad515a2a1455c7cd1562f805349d81454fc08d169c4644fb08d164814458801113e82345a512313dc2345a4063163c1444f608d16881544f408d16801444f304913c823459e05f13c41244f008d16701445a111bd67c46b59d119d66c4634ef08d166816e59911f139423458e0510f6656d4e408d0a701642fd457ca811573d999f8c866724e308d0edc17759605b0bf115d4e208d13841245930d653801244df04916443715900dc137412458d0d2d62c3434d3049134412458d15d93401244ce049162c5764cb049164856b58f159d63846658c0d6d6283534ca0491324124,
    0x55f8d1d78034369b55bda3556b647559d86956369b11bda3446b647119d868463613517d84c45b55e915d8444536090da98083625f24d697c834a40004807aa06f1d601ac6ca067174018c3ee85f150a16c1d68570aca14c3ee04f150812c1d60470ac810d7b403c5df00c09f957855d08d15702345d605d4ab51655dd055556c23455a08d176c18d2ae46157541653084574ab11553d995f55642345d905f0ef41673074574a7016455808d0aad16455708d0c1115c2aa4550ab95755d615a575456555608d0c0d15e2a945596f035455508d174445f5d0114d72836a5bc0d9973c05e5ce014972d57b5bd55dcf5656d5dc15ad7685675d8159572447a5bb11d96ec4665c811955502343bc05dca6c16d5d705a97501675d305997481655cd0590c0915f2b94568aa11571fa455969547455308d166446455208d172816454d08d0a5817c1f845595302345c705b152c2340f7a17c1c68575cb19fd6996735c915f97204765c6119952823430045bcadd16a2a5459c7d916627705547c01545c505157101440f5a1bc1be8675ba2e316dcb805ba0a316dc28054908d16c418c,
    0x62b15d98a447e62711998403785f94da97d43586240d21880a48620052131c120147a1ac29e86361f012186c0445e600c183c3786190da13181205e500c185c3706070d8131412060e0de881a3604c404817900301e001ac65806361811f9858476615119983037a6050dc98503484c2048077c07b19401cd78c0301d881bc76006b189819c6240634a2959182a47e60391d982837a6030dc97cd3685f30d618483485f3c9217ce1484a2048075e07f1d701ec61a07718601cd7ba0485e081117b803c5e000c183c47c60e11998342444bc95917d334860b09117d21485e28111841561610118583145f60c116d5d245760a114d81c47460609112ee4544ba95918102445f0812182156960811a581545f605116d5ca457603114d80056560015d97dc4725fe11c97d84625fd09f97ecb585fb05617e80585f811517dc56b5f6159d7d046e60115bd7fc56b5fc159d7e45635f511897cc4525f00d997bc2345f1516d7c435b5ee0d0cf4645d5ec116d7ac4575ea11557a03565e700d179436e5e40d5928e4545e20db97840345e9517d7994535e90d7d7983535e34d3d78c34b,
    0x64f097196856965911b98c04626581179948b52657097995025c652054994005e64e0149448130511050197457e62d15c996c36564d0d9193027c64a293192c23e50d050192812867215bd90956367111b98b046266f097d9a425b65e095d9242534ff04c1a3057f68a15f4c2e57568715cda1856f641558da1447e62911f5a1446e62b11899d03726480dc17f135a4fd04817e03484fc04819184645f70d61898348623292188c1484fb04818780444fa04813e41406222d2190c24962205213e013064412319083805f60d6189434862129218841484f704819003584f604813d41306380dc18f83484f404818f03704f204818dc37063a0d213c012063811a58dc46163f11bd8f446b63b119d8e44636360d893bc1204ee04c13b41404ec04c18c846c63009413a813062f09118bc2544e904c18c036462e095139c140634097d8cc25b631095d8b42534e604c18d447c62c0dc139412062a0da13901206280d8138c1205e800c189856b625159c52685b0a8a14d88837062315ad8845675fb4d697e935a61d08c132401061d116d87856b61c08c132001064519ed904677,
    0x6720e015141206710dc151012064b0985a0825d67e095550c13064a2d619f426564b096592815854104c15001306821a319c048c68009a14fc13067b09519b858c6800db14f814053d04c14f013067e16319f458066712319e825053a04c196447c67909f19ec25c67909514e413053804c19dc67c53704c197458c67a0d919e028c67609f14d414068415f5a0c57167111f1a0425f67f096d9f0257675094d4d013053305019cc26953204c19c024f66e092d99c24765d090d4c413053004c19c047e63411c99b426966b09a19a825552e04c14b414065c09914b014066c095595025452b04c19b857e63315c99b436d66b0db199036566a0999990265529050199847c65a09814a013066201f196424052704c149813066619e196025052504c1980060524050194825051d04c147002066219e194014051a008146413066011b193825051704c19a067966415b992c56d66711f98c447266511b998cb62664096596c25164d094198c16251604c198406e65f0189964354515050145013065c09b144c140653294194c150651017193c0506560139954042653097194415c,
    0x584cd1d8633436b31595acc5766b111c9ac03726b415bdac856b6af159dab85636ac11988a01446aa11f9aa44662200511aa00446a611f9a9446620a051165d56f6ab55ad7215676a7558d65c46f6ab11ad7204676a7118da9145f6a4116d604457615914dbfd56f6f755adb615676bd558dbfc46f6f711adb604676bd118daed45f6bb116d5f3457613d14dae016e6b50599ab51566ad0519a8c12e1edc1bc6e7067101e17c1eb857101c13c1eb04755c04817b003055a04817ac03069f0dc15641205ea00c053e85b0aba14da6957b68655dcf4256d6a115ada8056769e1595a6447a68511d9a144666921195a7436a69c0da180535a554048053685b0aaa14d7a403064451d154c1206351191a3c3485520481a5825469809a15441306960971a5436454f0501a5c25f64b096d9a8257694094d5381306930dc180135a54d0481a4436054c0481a3c46e0f2a17c1b685769a19fd91567369915f9a4847669011998203705ff4da9a3834854a04803c286f06ba19d7c403c6840e0152412068b0da152012064a0dc1a0c3805fe4da1a243586882961a20158546048191968c,
    0x62904d965c12e6d551d1b204646fc05f1acd1566fa05b1ab012e0fae17c1d38576fe19fdb596736fd15f9bec4766f91199ac91666f80511aac12e0f8e1bc1cb8676ee0e01b7418c6f50591bd012e6ed0e01b7018c6b04591bc81546d75a31b7c3806da0631bb035d6ea0d55b9c1366e90d95b941366ec1a31b901346e304d1ba858c6e91601b881346e40951b983586e30991b9047c6e311c1b9c57d6e515c5b882566ee15f5bb45716eb0d7dba03576e104d9b7c56f6d4558db7447d6dc11c5b6845f6d3514dbd857f6f315f4c4f5756f115cdbc056f6d2558dbbc47e6c511f5bbc46e6c71189b803726de0dc1b6c17e6d905f1abd15669204d972012e6d71191b081446bf0111b5448c6d40e01b4c18c6c10511b441546cf0511b3417c6cb0511b4046f6ce11adb304676ca118db2416e6c811f1b181646aa04b9b1016c6a904b9b0856b6c1159dafc56b6a80079b5867b6d219ddb1c5766c511f9b0c4666ae4599b001446a704b9af80446b6f1f9ae7c766a4d199ae417e6b605d9af01446a404b9ae83646b94d3dae434b582cd1d85b3436b70df1a9b3566b64d3dad834b,
    0x70b6d39d0c17e73605d9d4013470b04b878a07f1a381ddd3856e74d09bdd3026374a11d1d24464715e5a5d1856871aed71cdda747440991d2c465748093dd1c24b745091dd0c24374115b5cfc47c73e11b1cf4044711e5c5ce857073809f1cdc26c7401175cf024f73b092dce4247736090dccc5686aad195cc426c72c19f5cbc57072d09b1cb023e1f88585cd046a73209bdcc026b72e099dcac26371f0dd9ca436672415f5c9847c71d0999c9057e71c0dd9c8c05472015f1c7847c71d0111c8446d71f117dc7045371a15a9ca056f72715adc94567722158dc6c3667190d59c5c5657150d99c4c57d7110d99c3a37f70e0dddc3034e71495bdc5a56b710959dc4a5637160dbdc5036b7120d9dc4036370f0d7dc3435b70b8d5dc2c35384b15be11056b824159e02c5638040dbdfb436b7d90d9ddfc3637780d7ddb035b76a0d5dd3c35374205b9cd416672a0559c6013e70a04b878606f197819c35a85f051a15c4e083f0a020ddc2012e70604b9c1017c70304b9bf957b6f055dcf5f56d70715adc145677021595bf447a6ef11d9bbc4666fb1195c041667000591ad1156,
    0x7890945e0c25078e0911e3027c78a09b1e1825c7860941e2045e7870d49e1425e7840971e3447a78b11d9e243657830d91e0823e7a915ade985677a50da9e903667a1097de6825b78f095de042537d719edf4c6777bb11e9f184767c50dbddb836a7c00d9def83667bc0d39eec34d72b0599eac13678004d1c4012e73e05d1df816477c05f1d2816c1e681bc6a206773d0199df457e77b15d9d2017e73c05d9de815470f04b879607f1a681ddde405470e84b9dd816477404d1c3812e77105f1dbc1347770dfddd437e7730de9dc83777700dd9db837274705f9cec17670f6579db413470d04b9d17e7a739f9c9c2dd6d719f1b1d1417e73905d9dac16c71904f1c2e12e76509d9d9426676811f1d91b7c7606dc1d8c17c75a01c1d6407076411f1d8c37c76209f1d7407c75801c1d8057c75f0dc1d75a7c75d01f1d69d7c75a11f1d61b7c75909f1d6017c76775f9d99d7c76711f9d9847c7616df9d79b7276509f9d9426e76105f9d7817275c01f9d6c07c75701c9d480257530dd1d4c2607550de9d5037275209d9da426f756099c78e06f1a4819dd440277436df9cd9b76,
    0x7e20511f8c46f7e1118df7847c7dd0111f7c45f7dc114c37284f057a11def067d7ec15f5fa856f7e4158df8047c7c60d89f6c17c72e0559c6c13c71204b9f6807c0daa17c1568577d80d91ea41347a804d1f5858c7d50e31f5018c7a604d1f2817c7d20551f401447ce05f1f2416c7cc0511f2836d7c90d95f4446f7cf11adf344677cb118df2016e7c70df1e901347b004d1ebc13479804d1f1057e7c315f1f0817e7c105f1eb01347bf05b1c4412e72c0599ef41347a504d1ee03787ba0991e8c24c7b40991ee047c7b10df1eb83747a00d71ecc3607b609f1e5c24c7b409b1ecc4747ad0dd1e3435c7b109a5e6c2557af11b9e6046c79b0995eb82597ad0945ee436f7b70daded43677b20d8dec026e7ac0999e9424c7aa0955ea047c7a709f5e8c25f7a0096de5c25778d094de8824f79f092de5424778b090de8c37a7a20dd9e7826979c09a1e6c25578a0991e742557840951e8047a79f11d9e7836d79c0db1e4036579b0999e402657940db1e483607880941e585707940db1e4846c7870941e4056e78215b5e6446e79811b1e5c37a7950dd9e4c36e7910d89e40259,
    0x84215ba06456284111fa10047c83e0dfddcc3798380dce0d43718070dbdf4c36383009fa0ac27282805fa09417c74b05b1c9413e71084ba08c16482104d207c17c81d04d208836f8200dae07836781c0d8e06c16e81a15f20541548180591c9013e71384ba05024b811091e05067681215c204467681015a203c35c815159a00426b7e7099e04c24b80e091e00026b7e5099dc8c02e81919da05c57e7ff0dedf903778160d6603415472204f9c4a12e80c0151f545747d81a3202448c8080631c5c12e7fe09a9fc067e80a15ee01c5778061595ff437a8050591cc815671604b9fa43748020959fac36480105920000647c70d91ff81647fc0591fec0647f805b1c5412e7f40951fd82687f40971fcc3647f5097de0825b79b095dfc82537f104d037e85f05aa15e00c67f7ff19cdff447e7bb11c9fe836f7730da9fe43677f70d99fc034e7bb0d35cc01667ef04d9fb813471404b837686f058a19dc8413c71304b9c8013c7eb1a31f8c48c7df0631c7c13c7de05b1c7813c7e811f5f7847c7e20df1f984707dd01f1c7402c7e91631f8448c7dc0631f9c15471c04f1f94054,
    0x86a15be1a056b866159e18c56386111e217c46885d120217038085a11a216436870c0d0a18067f85e19ee16c67785819ce15c47a85611ca15446a8b895be30a56b887959e2be5638c20dbe2e036b8af0d9e21c3638840d7e20435b76ced5ddb1b5387c85be1e216e87485aa1f0167878059a1d0162854857caca15a86c855e18a15686c04fe18813e85404dcac813285104d1c5612e84f05f1ca413c843115212846a843119a12457a84215da108566847159600c37b7ea0dde14836b8500da613836776e0d85d0017484d059a13016472804f9c5212e81a159212816484805f1c5e12e13d20bc28882784919fa11c57680a0dfdf5c3738460d65cd01648450551c9c13e71684b84ec83f0a120de10c15483f0df60f437183409f20bc2708090d7df5835372604fa0fc48c8330a320a818c74d05b20f013683a04d20f058c82e06020e847c83205f20b417083d16320c428c82c0a020a418c74c05f20ec13683904d20dc26383604d1c4612e83204920d037c83309f60c427182e04da0b413482f11f20b037182a09f60a427182709be098263808097df5025384215fa05c57d,
    0x88986322241348aa05522a01448a605f22901448a911be29c46b8a5119e28c4638a205ba28437c7110d9226023888e04d225023488d04d224c12489704a227857289608e224823489d05fa27017c89004e22301347118d8617215d89705b226036e8960d9a25046289305ba2482668900d9a23446288e09ba23026688a15ae2245678ad19ee2ac67789911ea2804767160dfa27c36f8756daa26c36789a0d99c5034e8990d3625423a89108da16e16f2b585aa1c6167866859a11e15688f04ea22c13688804d1fc012e88695fa21857670b15b9c2e35587e85fe1ea17e87685ea1f817787a05da1d817288505521f7b7f879edfa1d7b7a87d6dde1e5b768756dc9c2e36670b0d3a1f617f87985fa1d617a87d05de1e417687505c9c2f95688304de20813470b64b9c3b98d88015f61fc37187e0d7e1f435b777ed5ddc9b5387b11f1c4dc7d717e5c5c3994b87a093e1e424b775e91ddc1a438770551c45956715e4ba1d835f8750d6ddcfb5776e6d4e1cc67f87219ee1c467787019ce1bc37e86e0dda1b436686b0991c90929869095219457d86709f1acca4686515fa190254,
    0x8ca61107a606f1e901ac6c60671b1018e36fd7e8db75da36e37e8db0dda3683541e881fc7a007b1b081dc6c00738c8e1623218548c880e23200346aa448635057d8d605c235057e8d3015236056f8d715ae3545678d2158e3401498ce057e3302608ca119a3242488cf116e33415b8cb055e32014f779650e4a656f93795ae376567911958e4ee36e93b0d9a34635693709be4a426b911099e3742638d9097e211a5b778e95dde1a538d108e479e06f1e701ac6a60671a9018c38285f13ea16c16e8570a3a14e31e0388c700d04f882f0e020ac28c82705b208e2b057470c0de5c4067e8c515ee2b65778c4159630037a7120d9630c16485e857cade15a872855e1a21568b40dd22843647150d922fc1647158d8630467f8b599ce30047e89911c9c483768be0dbe1d7b6a8bd0d9e2f03667100d3a26434d86085bcae616a873859e1aa166817855a2ec13a8ba04da2e41347bc04b9c3036185985762d868c8b206322d058c8b106322c61548b2117e2c445371419f62dc57d8b515be2cc5637160df62803628b005f216215f2b3856a1c2157863855a2b836488a04d22b038c,
    0x62a19e3340449271a3248c38c91f06024640809220db249458c91c915248438c9218d52470180916020245a05492211b2476344917811248c46f921118c39a84f061a11e47845491d0d5246205491f15be47056391500d24604549170d5008d85491400d245445f914114e46456f916158e34e35691300d237c67d92815f649856f924158e48037c8d28d5a40826291b05c246807c91201c039285f05fa15e32c03491009923b42548e6091239248c90e0a323ac2548e409123ae18090c095242824490809f241824490b11be42446b907119e41446390409ba40c27c8f609523a42448f309123c824490011fa3fc47c8ef09523a02448fd0db23d42748f815b23d02748fa05223c43648f8158a3c03668f111723c44508f511663d04518f30dba3c836c8f00d3a3ec56b8f9158e3dc45e8f609ba3bc2668e58df23b01708ed15ae3ac5678d68d5a3a426e8e8099a3941708e615ae3905678e3117e3884578d4919a38024490f19ee4346778d59199fc045e8de0dea40837690109be1d9a6a8fe099e3f02668ee09563a82548e709163842448df08fa37823d847851637047c,
    0x946158a51056a9431589ba6c6a94f15ae53856a5aa959a52c5636edb1a96d64669480daa5143527f12d42249a6a942094a5042506f195bdbc6d6b5be959da1e56395051aa54045a8916daa244b5a940459a5001566c5917db16c5b597915d8a64538df6d7dc51b5b817ed5def1b538df2d3dc50b4b817cd1def0b436ef917dbbec5b5bb915da164538de6d7e265b5b842ed5deedb538de2d3e264b4b842cd1deecb439c555ae70d5679c511ae70c4676d8917db62c5b5a8915d91e4539bf0dae6f03678dd6d7e21db5b824ed5ddfdb538dd2d3e21cb4b824cd1ddfcb4393d09aa6ac2669a5457e1d115a985455e5a91569a5053e1d014a985051e5a814695804fe54413e93f04dcc2413293e04ba4f412d8db093e219a4b77de91ddeda4390e15d2342038143a12c29684392a19fa4e857b90f95de4e45659380d9235e35693509e850685b0a4a14e33e03892509d240c2649330d724d0464932019233804492f0db03a685f064a15e4ac24493619fe49a6738d89199ef045e9350dfa37837293109be1dba6a930099e4b826692d09164b024492a08fa37823d817851439e86f,
    0x99305ba61816695904fa500136984116260c2598ed28f660024897d08d260034c97c08c25f423c97c0d1260423f97f08ee5f823797b08ce3b0b4c97a11c25e42718eb28f5b7ec6a977099a5d825c9720da25bc35497211b25b835096f0d725b84649730d7e5c435b9700d5e5b435397415f65b04706d4ed6a60856b978159db7ab5a97509ae5ac2678fc697e269a5b835e95def9a538ea28f6575166848c57259c14c5ba959a5a04668986daa0ffb66834cd5259c254848c91258836c95c09b258036095b09b258856a6ecb1aa5805626eab1aa57846195c15aa56c56296515ae59056a5ab959a58c5636eeb1a96de4668966daa0f7b669610d7a57c35282fcd12241a6a95d099a56825e92b2971bda56f6f6b5ad70a56768c958e255c6a841f19a254c5a841d15a23db6a9694d9a23cb5a9690d5a59916e959459a59815e959055a55c466809ed9a55824495415f5f5bb5695309f255556b952559e55446b952119dbce45f6f3b16d70245768a914e103b56840cd19a22562948459a51c36094409825283789460d8253434889469e250c26094c0922528561949097a51c56a,
    0x5b991926a14549a80d90a5a354833e99669d259833c91669c2395b8959a6a84669016dbe27db6b83eed9df15b63830cd566a43499a605ba64d16696604fa67846c99f0db1f11b7199d0db666c3618fb2d7669034999045d259413e94f04d9f0db6199605b1bf294496404fa5381368fa317253014489e6de66683618f92d7668434998f45d264414496304fa52c13699f115267834898d05d257015496204f267467a6ebb5ea63017695a051258413c944051251c13498a05d262c154960053250c14494604d266c67a99a19c9ba2d7a98805da57c14c942051266413694504d265016e987059a5041447f124d26584686fcb1616d2364831e99665425999409063d8a3d98e097662c25198d49b63d5a5d98a49863d1a5d98e15c263456898b15c262856098909f2648463991518a644461693918264145998f514664036e98f0d896ce35498c49be241a69988498e61d2618ef69760b3a5598c093e240a49988090e61c2418ef28f60b32359a315ae68856a5a9959a6805636e0b1a96ca4668fe6dbe26db6b838ed9df01b6399c0d7e23cb599980d4e65c3518ee2d360af345,
    0x978cdc6435b5f8ab6d6df4fb577d36d4e71017c978455a54813e977459a70815c6d7d17db5fc5b5a7d15d91b4536f095bdbc2d6b5bd959da1a5639c14d9a704356975459a5d41569c004d18874529744559b5734f6d5ed2d697347644cd0e6f957d9be11f5b4b45f6d2f16d68f457641d14e6f417c96b455a5ac1469bb0dbe6dd3639b405be6bc16390b64fe2a593b81ce4ddf45933909653e29d94b81ee51df3d94390764fe29593b820e4ddf359339b711be6d84639b305be6b8163905653e28d94b822e51df2d9439b44dbe6cd3639b409be6cc2636ca88fdb2aa3b59b88dd8e62336cc8d3db32b4b59d8d1d8ee3436ce88fdb3aa3b59f88dd8f62339af51be6b94639af0dbe6b83636d08d3db42b4b5a18d1d8fe3439ba4d7e6e535b9b84d5e6d53539ba097e6e425b9b8095e6d42536c888fdb22a3b59988dd8d62339b2057e6c415b9b0055e6b415390364fe28593b81ae4ddf1d93390324be28492b81ac49df1c9236c78d3db1eb4b5988d1d8ae343902693e281a4b819e91df19a4390228fe280a3b819c8ddf18a339ac05b0a5a16c9a805725a013e9a705ba655166,
    0x9df95f678437c9d88d5a760271924697e2cda5b7e4e95df91a539df08e67380709ce80d277456591f6d7a7702646aa0486479b5c9da119a471b6e9d9091273e0449db55be7615639db11be7604636c3917db0ec5b595915d89e45391b6d7a46cb4e9d5519588e3429d511b67340609c035f275947d9d4515675837d9d40d55b5a34f6d6ad2d69a3476458d0e73007061f88ce46993f7da64ce46892f7da248e744455919693e003a47918693673c356916697df97a5702500d27354559cd0d55afe34f6bfad2d62234761e8d0e74145f9ce514e74035f9ce0d4dafa34f6bead2d61e34761b8d0e73025f912693e033a4791228fe03323793e15b67a946d9e2517e7794539ea0db678835f9de0d4daf634f6bdad2d61a34761a8d0e75c2619d3097e6f0a53911693e2bda4b80be91df65a4391128fe2bca3b80bc8ddf64a339ab054a74806c9cb018040e84f07ca11c40e03f07c80dc51082f0a6209e72416c95704fa60d166910697e2b9a5b7d8e95df61a539c8119a43db6f8ad6dae01fb677d76d8e71c349982459a71814495504fa439a4f8ac692df57a477d5690e54a57d,
    0x9fc01127e856a9f9099a380a5c70595bdc16d6b5da959da825638bb6daa7fd3668bb2d6a7fc3569fb45ba7e11669fb057a7e01569f615967d42649f455be79ad639f411be79a463702917dc0ac5b5d8915da7a4539f0459a7c456a9f00da9ef4b509ef0941c1e56f707b5ad7725676a1958e7c946a9f2116a7b91669ee0559bee45f6fbb16d722457692914e4a9b5f7106d6e11fb577f06d4e4a8b4f7102d2e11f3477f02d0e87556f9e2b58e87446f9e2918dbfe45f6ffb16d73245769b914e86c36f9bf2d8e4a5b5f8b86d6e12fb577ed6d4e4a4b4f8b82d2e12f3477ed2d0e86826e93d098a84515f874a56a81d157a00455a84414f874852a81c147a00051a7dc13f9f304fa7b41373cf04ca7b012e93d04b441685f07ea15c41604f07e811c52883f0a920de7a146f9dfb18d8823429d609be6f8a63928693e2dda4b816e91dfb1a437e028c649da5f8b6696dfafa577eb694e7942697e3690679c6709dd09867440609e515f679027c9e915f27a047d9e6115676c2719e30966499a4f8b5692dfffa477ea690e740070925693e2d1a4b7e9e91dfa5a439e015f5f87b56,
    0x6f78d3dbdeb4b5c38d1da36343a1b29ae74ca67a1f09664dda4f8c2692e113a47804690e4dca3f8c228ee11323780428ce86816a152a12c2b684315280ec2b60330ea20ac1948239f495968133699366d7e305b5b803ed5e00db539e105928111569f404fa80d156a1c55968704656fed17dbfbc5b5cbd15da6b4539bd2592805156a010519bf634f6fdad2d7263476998d0e4d5a4f8c0692e127a477fd690e4d4a3f8c028ee1272377fd28ce6b01546aa9194a7216ca1705727f813ea1605ba835166a17515285c36429c8d52859259a1608e684d054a1300d2850248932697dfeda53a13017a7f002ea19119a4c5b6f8be6dae13bb677fa6d8e860349a1505ba8291669fb04fa848044a0e05b1b1a9449fa04fa7c4136a0b05ba8241669ef0511ef4934a0c09528384686c6b162834259a0b09058aa460a094986824241a1015a975e5669306dbe2f5b6b852ed9dfe5b638bb2d6683c351a0a05ba8201669f804fa7b8136a0611a2814269a031596808468a0415be78ed63a0109be704a6392e697e2f1a5b850e95dfdda539f9459a06315c9fd05327f84669fd0952063244,
    0x28915659c40d92882356a2009a64e9a5f8c5696e02ba5780a694e893239a25092689045b9c7b15e870a5b9d4295e4e5a4f8c4692e11ba47806690e888466a21091288156b9c8b59e88046b9c8919dbe645f6f9b16d71a457690914e7b056ea2651ae716c67a23515689836b9c58d9e88c355] 26 7) 6 11 7
def cert_trace := dagTraceF cert_mask cert_stock 12 cert_forest
set_option maxHeartbeats 0 in
def cert_sym0 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def cert_sym1 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78beeb6caeaa68df6d74cf2c709e69648e28607de75c6da6583ce34c2ca2485d65544d24501c61440c2040
  invFun := decodeRows 0xffef7cefae78beeb6caeaa68df6d74cf2c709e69648e28607de75c6da6583ce34c2ca2485d65544d24501c61440c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def cert_sym2 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffeefaf7ce78df6cf2d74c70beeaeab6ca689e68e29648607de6da75c6585d64d25544503ce2ca34c2481c60c2144040
  invFun := decodeRows 0xffeefaf7ce78df6cf2d74c70beeaeab6ca689e68e29648607de6da75c6585d64d25544503ce2ca34c2481c60c2144040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def cert_sym3 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffeefaf7ce78beeaeab6ca68df6cf2d74c709e68e29648607de6da75c6583ce2ca34c2485d64d25544501c60c2144040
  invFun := decodeRows 0xffeefaf7ce78beeaeab6ca68df6cf2d74c709e68e29648607de6da75c6583ce2ca34c2485d64d25544501c60c2144040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def cert_sym4 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0x120941161908328b49369b10530d51571d18738f59779f821a29c31e398a3aabcb3ebb925b2dd35f3d9a7bafdb7fbf
  invFun := decodeRows 0x120941161908328b49369b10530d51571d18738f59779f821a29c31e398a3aabcb3ebb925b2dd35f3d9a7bafdb7fbf
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def cert_sym5 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0x120941161910530d51571d08328b49369b18738f59779f821a29c31e39925b2dd35f3d8a3aabcb3ebb9a7bafdb7fbf
  invFun := decodeRows 0x141120961908349328b69b10551530d71d18759738f79f821c31a29e398a3cb3aabebb925d35b2df3d9a7db7baffbf
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def cert_sym6 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0x141120961908349328b69b10551530d71d18759738f79f821c31a29e398a3cb3aabebb925d35b2df3d9a7db7baffbf
  invFun := decodeRows 0x120941161910530d51571d08328b49369b18738f59779f821a29c31e39925b2dd35f3d8a3aabcb3ebb9a7bafdb7fbf
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def cert_sym7 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0x141120961910551530d71d08349328b69b18759738f79f821c31a29e39925d35b2df3d8a3cb3aabebb9a7db7baffbf
  invFun := decodeRows 0x141120961910551530d71d08349328b69b18759738f79f821c31a29e39925d35b2df3d8a3cb3aabebb9a7db7baffbf
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel


private def axis12 : RowAction64 := maskedRow64
  0x0c0c0c0c0c0c0c0c 0x3030303030303030 0xc3c3c3c3c3c3c3c3 2
  (by unfold goodMaskLanes; decide +kernel)
private def axis34 : RowAction64 := maskedRow64
  0x0000ff000000ff00 0x00ff000000ff0000 0xff0000ffff0000ff 8
  (by unfold goodMaskLanes; decide +kernel)
private def flipSwap13 : RowAction64 := maskedRow64
  0x0033003300330033 0xcc00cc00cc00cc00 0x33cc33cc33cc33cc 10
  (by unfold goodMaskLanes; decide +kernel)
private def flipSwap24 : RowAction64 := maskedRow64
  0x00000f0f00000f0f 0xf0f00000f0f00000 0x0f0ff0f00f0ff0f0 20
  (by unfold goodMaskLanes; decide +kernel)
private def flip0 : RowAction64 := maskedRow64
  0x5555555555555555 0xaaaaaaaaaaaaaaaa 0 1 (by unfold goodMaskLanes; decide +kernel)
private def flip5 : RowAction64 := maskedRow64
  0x00000000ffffffff 0xffffffff00000000 0 32 (by unfold goodMaskLanes; decide +kernel)

private def reversePairs : RowAction64 := flipSwap13.comp (flipSwap24.comp (flip0.comp flip5))

def certifiedFastRows (i : Nat) : RowAction64 :=
  [RowAction64.id, axis34, axis12, axis12.comp axis34, reversePairs,
    axis34.comp reversePairs, axis12.comp reversePairs,
    axis12.comp (axis34.comp reversePairs)].getD i RowAction64.id

def certifiedPermutations (i : Nat) : Equiv.Perm (Fin 64) :=
  [cert_sym0, cert_sym1, cert_sym2, cert_sym3, cert_sym4, cert_sym5, cert_sym6, cert_sym7].getD i (Equiv.refl _)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
theorem certifiedFastRows_source : ∀ k : Fin 8, ∀ i : Fin 64,
    (certifiedFastRows k.val).source i = certifiedPermutations k.val i := by
  decide +kernel

def certifiedFastCanon (k w : Nat) : Nat := canonF fullMask ((certifiedFastRows k).apply w)

theorem certifiedFastCanon_eq (k : Fin 8) (w : Nat) :
    certifiedFastCanon k.val w = rowCanon (certifiedPermutations k.val) fullMask w :=
  (certifiedFastRows k.val).canon_eq (certifiedFastRows_source k) w

set_option maxHeartbeats 0 in
def cert_syms : List (TableSymmetry cert_mask cert_goal) := [
  ⟨(⟨cert_sym0, by decide +kernel⟩, certifiedFastCanon 0),
    fun w => certifiedFastCanon_eq (⟨0, by decide⟩ : Fin 8) w⟩,
  ⟨(⟨cert_sym1, by decide +kernel⟩, certifiedFastCanon 1),
    fun w => certifiedFastCanon_eq (⟨1, by decide⟩ : Fin 8) w⟩,
  ⟨(⟨cert_sym2, by decide +kernel⟩, certifiedFastCanon 2),
    fun w => certifiedFastCanon_eq (⟨2, by decide⟩ : Fin 8) w⟩,
  ⟨(⟨cert_sym3, by decide +kernel⟩, certifiedFastCanon 3),
    fun w => certifiedFastCanon_eq (⟨3, by decide⟩ : Fin 8) w⟩,
  ⟨(⟨cert_sym4, by decide +kernel⟩, certifiedFastCanon 4),
    fun w => certifiedFastCanon_eq (⟨4, by decide⟩ : Fin 8) w⟩,
  ⟨(⟨cert_sym5, by decide +kernel⟩, certifiedFastCanon 5),
    fun w => certifiedFastCanon_eq (⟨5, by decide⟩ : Fin 8) w⟩,
  ⟨(⟨cert_sym6, by decide +kernel⟩, certifiedFastCanon 6),
    fun w => certifiedFastCanon_eq (⟨6, by decide⟩ : Fin 8) w⟩,
  ⟨(⟨cert_sym7, by decide +kernel⟩, certifiedFastCanon 7),
    fun w => certifiedFastCanon_eq (⟨7, by decide⟩ : Fin 8) w⟩]
def cert_hint_pages : List (Nat × Nat × Nat) := [
  (0x1e20e7cf21b677aa4cbee39af5b728ae5d44278b28c8f1c261fdee92706b27980ea864caa368eb271c31e94a084a3340e2835000e000, 13, 0x103011880808c28880c0d4e2a04614449862c0c426880008ca0335c2010232c0d4398911caa960290d4260230a251703108a2b462c540ad60404612448ac0008d70310ca7030353808139406a19583048581a920409c25885142344b99c7c0ac3505809d20330e25175004e144328ed58f8148c0009410406ab8128711469010290c0d4a02560c12120409c249606a214508d12a6b0e0606a14cf1c280d429865094180270a61c462c0008c22a4080d570250e29150230c0d5202046501a86560312120409c258612c0d4528d1326f9f0606740a03308ab8188b57c581684b18092021040a4e0270c0d459803808411406a14c428208b81285560c040a04e081482056581a8a51823cca8aaa0e8e0270834012889080c5506280942ad06009c288b31810188c080c4e24540d4238651800138431c2a831404a155830102813aa05610149606a284628f12a630e0213818a0250aa1cc61c06ac016b00561000330863040a04e481027096205716066154729b14c7270350a69890234c08118452090b0250a61d47880200d4e022409c25b06010118470d240128e148a8118606a901023280d432b04860119c04a18448953393a7120409c80290ca2045a80207120270a61d4489c200890270824012889001001004e14480251062ac01c04a8138004a1a4408648601185128581884516a54df4e9c205027082195703116aa80029096a880a200b4e0272009440aa0524001004a104359350090e027000ac0025540a4508654601185128581884516a5cd84e1420138419c09449905408b03508a1cc48aa200d521005a70129c48094238a1540ad80420a81385120094418a954181a82280d422b0546011822c0d4228811624cd5005408428901440169c04e401288154001484b0ca818942c0c4228932ea0a74e1028138410ca25402edc09c2a871045816800521ac1004870138005600128205228469840c0cd703120c8198451440169c04e081480001011847006011853156b8129413ea7182a06612ca02d3860e0270920150210960021004a4031404a144398e05630ca02921a60e027204031404a144398e0462b4e102809426b05409480312018a0250a21cc659291428802d09230a02d0863000251448109c0524018900c50128510e6381191529692502d39281684719281a801809c2488b5470602b480015847280b4548c54870129c480942398380d420801809460004a11c802915a6060004a4090210a64031404a14c388f5300a495b204670206066b8188a200b4e027044813801809c2488b1c240a1606214c329b5381818ae280c4229c2c0d41000523830406211c369604a30489fe),
  (0x184abacd912aef4749a6c85222306878eb9d1a9acec5f4abe12ee8983a69c40e126f03509a68d265fc28e902069a2ec13c88602ba000, 13, 0x51c04a70502508ea80023000a43586001011a40661c4a2e2c0cc288651dae861c1409c22ba062b031404a14c216066b8128711aa50d806480c4a16062114448ad58b050005270129c14094238b518618a0250090b0250a61c4568a38094e0a04a11c3000808d20330e251716066144328ed0400119605a001488b1470138605a0012a04e10400290c0cc55803828139406a1cc42ae0809c0242c0942a87316228e025382812847581011840521b56060661182405214c3880280cc22a0409c20ae06a2446296b141816a406228e0270c0cd21c04e144559c1409ca0335c70e2404e12c398911ca99f3e0808d70250e222c00606a20a03508aa8188b31018a025540c436801009c90606a14c002280d4298654c10c0335c581984512a2c4c1aa0008c00290d622336140cd82e062114418ab6018b031640943488d54a8402108ac010210c501285312a21802d540ac40406a10d702554a8c0232c0943a8932a29a30290c5012aa2c0942889300a810880c0d42980280cc22a610a81484b0808d7025542150232c0d432893262080260808d70250e29853204a10c39802c0ac269356818b03164094368894c08b02d09698316062c81286d1120120804e001286124081286280942a89310101ab0300d429805c58198550ca3c4f18000181a8530020a0350a619531204698102308ab931604a1043a8f14c20138004a813841000a445882408c30350e600402046501a87310a997044c60118535c094408b51a208902b2c6013853fc481035180820310aa48403108bfbf244c09c00c04e12cf025240a413206a9013873044813880524810275c0a432880c50128550e6c17305c09420875122209023100811845101020854081384b0c2214598d16018a0250a6b982e04a104388d51021402d18a819d0a409c26889a40c682e280c4298652aa71a5008e01885394084438ab68329031a0094202500d428873186d2802510b81382280d428893686152e04a14c31b41009c61605a00128628094298b51e260c0804211460004a144408540a425ae04aa840250c501285512244cb180030138490c0c449ae280c4228ed),
  (0x1e7aea0f18b6e3a14c64dff2df359ca67ceea4bb17e83dbd51c12d72640b03958699c4829e58c4e57e26a8eb86e233413386f822a000, 13, 0x22460601a8430e6d8302700581a8530400158411a201714062581987510ab922a046701286911a9291c0c0d429aa9c0a4228a354001484b6c9180230a601703508a2c52064809c26d26c0c6704062115b06056c01880640d4228b3246d8002b092700031a4b8188a1009c203304481386066001488b1c33891c0522810005212c338a15c0c472846409421a55381170250c501285112a00b035487013825409c24800060118470d6b830e06212436802c0d4229813a680e30056b816aa68b013d20461ac448f33810a0315c0cc35885607022e04a154389c0c501285560c1a0ab00a4239606a481027096304729112e670102338c019b048481027092184428cf54c015ae480a426840c0c4b03330b018841146b971406210c32995380814841c90138490dac0302d6c8290335c50188451062a4759c0411502108a0813889081295c04e1043288b60101886480c42980280cd70310ca3d521c04e0980336c315000620813865106284206062b8a03108a59b30480c424a4600c4258a12c0947997549ec1b0404a14522c06a727031054818845a4c812855186a9802909654d20c05a30002504101aae04a1c414e04f4812d2640942a8b3286b813005614c349c6018a0250a61d670a1009c11204e12c40d2102813920409c2588114a1181604a14c3a9b138c181c4809d50204e124408a51a61170250c50128512cc0c02304c0158515cc01484d182581291332a00e2a05602902909ab8128b30548e0210aa1c4e000c5012960621a446983809c25206613571406611461aa6008c00290d60170333860159c04f48e0210aa2c401c04a81384b6070138490009460ae0809c289c300a4e027000c431404a70216046381586d122354a9983809ce300c58188535409c458a90cc0b0331c0ac3888d386150290965019ae380cc288c505481482080d4298c2c0b40025a470108531629010293809c102554a8102108a1c460406200203108aa9702309218b00080a4c02b0409c408b128581884522675460c2c0ac24aa0c0d429803890139406a1cc4298003013a43809cb0330d260b033300855027116b8b03308a5d4c8a438094e2404a11d20210db818ee04a1b550005212c100063497031a40cc5525c0a42982000a4258a122a0970354870129c48094238935c0b403006a12c1305d48a0250a61d441862809570310da4260025c38168550e2c0802505481a851000830350a65012b05c0d4288a3809c5029380013851540ac60aa1409580a14a81484b0ca18a0250a6b870210a245462a0c0d4e2404e501a86516631703514a815841122a9803138a815a404e194206066b8b2406610572a600a4258671a2b8a1606214c32975),
  (0x25b891b62ec863dfea79edca06d9d9e6634573e561d4a84f6d290467d0d23e64e8436dccb42d14a4225448f01fb467e14844300cb41e203c4000, 14, 0x38c293204a12436de4c09c90234d7813820461958062809429de4c09c2023480cd716066114689353d6902023600ac00606a14571406211522a0409580310c6c015964870102b0a290202709a90c023600c4349012c094aa9f3a54290270a20890270821011d02408138415c0c4429c000ac249c0c0d5824042144e1406a00b0350a2214899c000ac004046b8128628094288a90c501284d007012a04e001286910290c0232c70102908381484d00181684b1823c4b0252aa7cd5507c09c20235c09446be14084e025394050215c0c432887000ac84920c0d402a06a14410006250b0310aa21489aa0090109c04e0012893381818ae280c422aa2c09cb0404258128711664d550e05aa813b0046224000081818982c0c4298875c50188451c6181692b616030358c501a84512628402510281284710318e0c05b60158670808d70255408b03508a1cc989c540cd502b601151804e14c318895ca8b0210a619582a389013845040cc40862c11502b600a4308932858198451ea64551c000ac2486062b8a03108aa802a042144b2a54101384d54001584914258128f52a74290270808c00330438302709a1ac1000634850210aa72902d08e00158e939405160561043382280d429ae00581a8530e249410048084e02700094499c0c0c4b0404214d71406258198651ea00302d0960870604e135800081818982c0c429887156b8a03108a40cb4aa380019851988290335c5018845106a8302d09690b025000ac3495538a81584540cc21aa000c696a04a7018875994a8025086184848460a9202b0821cd5062c0cc2a84000ad50290c234402a062b8a0312c0843a8a55c9171c0621143488d38a814b006270f2c04e12d05206610d702d54c01584908501896066194bab04960118606a923023280d4328d35c1013aa2ca8148450e62c522a066c1524040cc228611221030312ca82031540ad23006290168691823cd72e280c42186532a1150336c18b0330aa9010aa0008c00290d6b8702909a4c5500062b8b140461443a8a5047000330a2d9052066b8a03108a20c5aae05a90e025000ac349c6cb81284d04181684b980a690406341703108a080031a40016b204a1d459923040011ae5c90c02308219c4a820c0d401606a14c20205200158610458a0230aa194a8ae48b812a43809c2888915a7120279c78138004a1a550005212e63e0433012ba600c6902d8cc81a84516640c13004670202b5c09438aa387a702709318118850c9018b22c08422895266712027540adb2c54094298636c1816e4280b422805c0d4288a3809d203138094102b9c781380056001288924338f0253d381284718001284062481025480d4398c33818a0255c11203308e1c4558c90c5012ae0890198470e22b522a04690102308a9023000094218691221031404a144b033486011a404001484b0e2b9202909a701290132a71003578d013aa000a42592a40d421ae480a4269130010a0312c0cc3a885381016aa05612c3404e00158004a20454880c0d580318cc81a8454870128411e67000335400128413808118005e1ac22e04a18a0250a259218046a8002b0a2b9202909a304b025226654e020521072404e12436a004501884500da90230c0b4b02512a2cc002925670002b3810188205212e5204e00148004a2045586480c591604211449995),
  (0x160aa9ed25278f33098bcc425ef26092cc94a353136810be71d32e6e718b62192eb8253fa4d101a70a315941098e3b2196886022a000, 13, 0x1302052c000310878128606290e0250a62d471a4640c590250da98002042a8138694c0942000421818a438094298b54c2012a04e12430a604a00f02909690402509a780021640d4388854c01484b0c0c52300627151c06a12c328b3201018fe20101890080c4e2a052198031096b0002b380d4338f3fdf830a0009c00a04e12c10405690138691e241903308a0821004ac81986d909018800561a4532046c880404e105902511a00c02d097218045c094303100c812a404e1cc6a8e3212f011204ea01486178094500062c81a8730800108a0c0d42880480d5e025409de0250c0b4448000c01184764094459212e6a81027240ad5025409c249604ab812a04aa8102508eb816a8052344500062c81a873002970004214c38a8480cc5025409c24a805a01702909601903308a404aa8a54c01484b0c0c52305409520350d64020270c0a411204e00602709222d902520264ce0404671702308af814c83808428be600c4e2804640202709b2014b204a304899c08a06025640c43688318c81184b18b8189c0c0c580330408550270c0b4e06062c81986526ab8159890870109c0c0d4289c54a01ab0062080031640d4328c308181484d600810aa04ec01288b366101021900c5f243809c102b0c2f8128405aa0602508720148c30c8128550e264d23e38084238c056f812825c0ac24c85008c60250db2174804214c38aa480946031483019aa180a460330d628402704a81384b201013860521b46025202c8189d5407812ac640d429a43809c002042a8138004a22481e00301384b0448138605a00158891c24012b2062555020102813841200ac42c860c8168510e6080243809c002b00095502914234c806062b920804f201480300c425ae04a30479935549012901420138605a089027003013849116401290126ac122a05611590351229153005212d52404a181a8736091502b08a6030404a18100052181986510e3047a951),
  (0x1f40f66f72b96bb6ad2ae6b310b7eeb63d90aa7f4a89d2cb1a45f13e81dbdb9bdaca25fcab912a28a83a59848aae45418d8938296000, 13, 0x90b170350a2b09033082a0b02509a3170404e14522a04690102308a181ab0189090204e12c30a8046581a8c51e264df48487013841900a64025166f9703504c019881409c1029900ad41606a10c629012a23002a0008c208650810e2404e11410351022c550606ac18081409c2029540ac30355008c608e522254c61c0c0d4298c380d5802d600ac20006610c6081409c90204e12c40ae2c0cc2a8e536298e0606a14d31204698102308a4120335c09c3a8f100708022409c209004a22c830200942086922a9150234808118450c0d581c0c0d4208712267102024081390052194408b500b830210aa1c48283808429a4000950270820012889000ad71c0448138495000c02308e1ad70251c2454e8be408040a04e10432be056b830210a23d48280408429aa5c0d520213809d502954b81a8452c0b542e0008424ae04a22cc8b040284027082801289320a8b0355409c3989154401aa40c0b4e027540ad80293890139006a19480aa0c0d58020c0d4208711664150606a14c02a042a8b0605613570a1009c20ae04a00158a922a5450203c28802b08e18442c806601706042154389050081085304b81aa40c0b4e027040a40283008c2986b00b81a8452425c4e100c0cd70a1009c302d0c2b812ae044813801809c248815c094302d1d6644ea9c5c0943031385820604a181482000a4b02d0c094458e122a4cce00056a019aa500cc0045c094218606622c649c04290e033480950270c0d43480380814855080b543204612c62941322914033000ae43008b812860661d4418a904601a86487013aa0521cd502b041016a8056c8118852425c570606671702d540a4c2850f13027092194408ab2227140330470128410418e02509ac1902508601aae04a1cc5191100b815a45c08c26889381012a04e124e0251027003004e90149c04a204559c60a8128490c0d449a45c0cd21c040a59023001819ae0521ac628e1262124033381016c82c08c25b055319023082194449116c90e0270821016a85408c2584900bd20405eb812b00009430350e6a8003308081284730c8128551a260ce4843808551c0408c228606a24ce30066601a9c00c81a843080b4302000a420aa380d4298ab24a644e3605610303309aa8002b09210303360c9703308a1c451a43809c224062d8002b08c81884310aa0002000ac208004a60e0250aa344799af080010a8066a920250090e027000ac12a04e12400251823ccc18041016a8056c811885142354f8c8380814b0740014a604e184458c55c0b522804a19803108624d21c04ea012a04e70148004ac0158a104a016a85c0a425a46409570330c63c4d780487013825409c24881500cd402500b81484b549012ae0008429980ca1902304b81584910a2846a951),
  (0x19d6c8de13ae4f690ad8d1e277b3028ffc3aa016f2c753b721966b9e571aa093228fa40d9dc8dfe6202df92f0892334133859012e000, 13, 0xe0405aa8e025092c0b02d5c19a2c04e10430251222a475b0381170250aa1c4e0606ac0234240ae00205611c428a11a244ce02046718033609090204e1243088519e0030335c08c32a600ad72405213430251423449a9c600ad702d5c1818c86da0118604a1ac408c9607030350a610208540a7402b800814847142314224066b8128752a21240316059802062c01586112a2cd82a0400118490409c40ae0c0c42a8e55c90e2406211c3488d4890e2006211c16806211451aa056c030335c181685112ac0e4804614d202400cf40250c60814ae6058128410ea44581c0c0d429a0142013822409c25881d020502724081384b102295706042154c89c60c0e2404ea81027092204528d35c00303308218130056b8302909a18128a11a24d451c04a70502508ea80023000a43586001011a4066b8b03308a2c466ba1870502708ae818ac0c0cc216066b81287116a48c3300c0ac2886d58a021004aa819871106a0316062124368a3809c3000808d20330e223642e3940148530e2216400046001486b1470129c1409423862c11203308e1c446a804a813841000a5402500b940210aa1c485ac5c0c451c04a70502508e24d606066118305408138410ca24c588eb0cc170270a21b451c04a70502508e1819a43809d71c4858168470e621468a84cf820235c09435aa0662c4406540c426aa4c0c5408042a012842c0cd70250e235481aa0008c00290d7198400808d70250e222602a380a550270e224d80204221802d540ac30406a10d70251a2a83035540c550804a10459a850a81084b4c2150290961011ae04aa800210a63c5426681011ae04a1ace5c04a14c68c86898148800094218814d2015a6086019ae04a1d441a6380cc24911510130254d00128475c0d458882408c40204611540804a813800521ac002514235532e5c00c02308e1844a8b180089027100a430c004a1180330a22090231008118450c1020810901384954081384b14a30479911601819ae0008428895103011880008c228606620202338a811853100811ae06a19478a454301484b0430002538181a85308c019a85c0d42289121248c3300c0ac2886d7d20e0210a691f02904101ab0066a1703508a28d80605613498c81808640c2c0d4219c5c0958033180ac448f1),
  (0x1b1ace7e4e30fb77ab0ed54294f392959c82a20f0947e3bbe9ca2d6065bb03977eb16500a3b106275232796989d63e818d89802de000, 13, 0xe2a066a815b008a8198430d2b951605214c32b00c0d5504540ac2ab005271202704181a85310a404a8a8b0701ac6b009c24c65c0d422a82c0a42691154a022a0561812861122717025543816853000ad40311932050804e106402504001484b90100033086718033000ac34805c58198550ca4c4e300660015aea00cc22c84870138406aa012802c0b4258c11e320230066a01898040c420ae0c0c4228e3212a952e04e15662a05690002b092a340211400198606a1945193148a9f2804a181987598b81a851186a94025000a4359c0808c10004670702d5c0ac3aaa0c0d42025409c24802c0b425a80c0ac228e126273ce2a052c018ae1c0b431c540a632c04e12c3025142b8302909a444aa826008d70404e14525804692302308a181aaa06234d22a066c1524040cc228611221170250c0c4e1608a815b0052184b02515e34c9aa4500d4258480d429c65c0d4228b154b81ab60c0d428a438094208e0818148510daa15021000a435823800198515c1818b6d008d702d0c094408d5487012800561a4e020573014e8900ce40250c7317035487012841122d921c04e10402e06b20188400581684b50096418040c4b0250c62248096f54a01a805c0d4289c540ad00005678138695009460aa3d0013c604619413004618198755ca8302d0a61c55360469152805a14439c800b81a851492015a0000acf0270d2a0b02d08a38601e04a7a002508e3000250867030350a700f0253d00128472408128435c1810855222915023480811845481180004a10c348915c1818a404001484b5c181484d380946091538a815ae05aa97035500c6b5a04e1816e804618128a121210e406809d50005212c0031000946a8e138181a802c90138550e22cce020467000335c1818855009019aa000ad706052134488c100b830310aa194d79c6c0ad702d90001584960b812a8d008540250e228d41c81a01384b0c2a01282000ac2480089019ae04a1d4488448c0c0350861ce42806608002b08224402e0c0c42a8655c90e2406211c3488d48ab42004a1819875106a800290960800335c90b0250821d458a4500b742004b2019b66000b03508a1cc488e304001584938a050804e105402550089027082a012800522ac9a805ca000230821d448805ca0c0235c094308955090102908200159c000a430350ca71402550a810a804a1a540004a12c73ae0c0a426a11),
  (0x1892bfdda7aacb4e0a6cd27292b4589e9cb8a4972448c4c14204afe87a8bae9b6ecea5f3add15969a442c9de8c5e52c1d58aa022a000, 13, 0x14e9c7851005611c3288116a0312e04a15438820090e027000ac0025540a4508d3081819ae06241903308a904027040a4004046001886b300cd70252026d552404ac122a05611438840c0cd703120c81984548080029096a84300561243398066b81290136a095027480180270961a6a2e640cc2286dfc4032e06214ca0271c90850052501886d05417025640cc36a464b81084d000ac44a400c01384b5cc813b204a1b41025409c22e04a3819b206222c61b205a4240545caaa02d0821c44aa4080b403004e12c449248119033b408436aa54f012847080c4002900c81a8531d690002b000810aa04e001288908b812b206290202d48c01084b48a810b205a0120230962a499995144015b20662810005212ea02d480015b205a0821004a4018b0640d4298a31929081204240602109222d2305409425b206a24d22a600a570250d69072e04213439b260a81296540842aa46008424b205a3cc88b0080c413206b98e2404a11d80405213411605b981486b22254c22e04a0990350a290e02704c01184b040018b006a19413005612573204e134b9b0940cc812640d4298716008590234870129c48094239024085802964c018853156c816a43809d53005212d7025640c551c4809c228e06ac0189c600ad22a0561457320621346097348a9802909618a0250a2a920251c0d410005210b02909a38128a16091502b08a60c0e0521343a8d13a6c0e0606a14e02604ec0169c0521150330869a00270408d703510a544e2e380cc22b00808d22a04614d202046b81a8651c0b484b00c0d4e0205610b02b09ac0149c04a30488a804481384160a01685108601984350ba81605a14c388853818b03109a0015889007010a40010c0330861ad7160661146aa4000950270820012889000ac31c040a420605213401605a12c608604a454e8a814084e02750101184d50b81884554001484b54181a80540ad51604e154488d30008109c540a5502d001011960661ad7160661148aaa48084e2a05211d5025000ac30208a81484700581684b14218128f5362c010218c70602db00ac3384046b8128d1b028109c04a7230a042114338606aa818913),
  (0x22fa85e5fd47afdde0717db80676d85a5f0d66657854ba5165344482d0f63ef4e8434e4ca22c84a6625448601d2c6b415144c00dd41be052c000, 14, 0x2a2a0c0d429ce48501a8530ca284025102812847044812920409423800522ac9084000858180809420b01c0b4258b31e210002154181aa4280d4228916008002b08581484d1020121c04e0015825409c248a1300d47880300015b204610702909a2d462a5348701382052b880e05214436a0185018845600cd33a000a4c0310ce38e03108a304a59c040a4330062c8e02108a23402e380cdc3a04e00148004a2046a8eb04a813800018c03308ec81288315a0180270960180333808432e066601087100c019945c0cc28885487013ae05e1acd4a43809c10290008002909501886300c429f0640cc228c322a4ad702d5c0010aa0c0d521406a11449a4cc2010845a82010a404a19d8033a80810aa04aab30204211433805c0d580270e6001494b5c0b52880487013825409c248810009402e05212d50606a90a03508a245800045816ae0561a440ae6008428b05c58118510ca54c038066e021004a10c50205212c002d540cc78800418a0250aa1cc51c04e28148004aa8158a11400168a080d570250c6080029096c15002c08c228611265c4038066115387809c2298080842a8b31a2f050404e1012920c0d580318cc81a84516640c2025409c0025000a440862809580310e642c038066a9c0204611570351222970a580b412a04e001486b00094608f55428102308a001886300c4a2e0621144a91354c030336090148a0808cc033540a4458d122a2801006210c52a056125802d140811b206a1cc92a41009c302d1090139405a195326086019ae2c0cc2289514670148f154c011800521ad20804e001021000a550270c0cc558605a0042404e501a87310a20200042155800380d4228731a2a930314d181184508181990280cc22ae06290f02d1009c12a04e001486b300cc01c066114909d554c03033482042a05212d802d10e60198d122a2042a05212d802d28701885348919029096c81688728a71f02b0d9b10230a2f9d02728701885310a3b46023808148c05a1d448be1810188437c01703108619465a40427010290c0d4a0256030e021040a4e16046154528d12a6f1e2e04ab81386378d150277809430862809580310e63ace2e4809502709230159c04a2846aa418a860204211c328890c601894380c4228952679810215409f3025080c43300625001c06a144328b33810168ccc09c25889187020353808438aa0c0d4e02046501a86560c0e120409c259c2c08c2a8a118a3c4c9be04181a853cc08a0350a61942309408429871189010290470108470c0d4598004501a8530ca082020421558301028138205208116046154358405a39480933322f9f0606798a03308ab8188b554301484b7cf840214809c32aa0409c24ae0c6018b204a1cd21c04e08148c05608128a126a1950315cc81184511aa860606615462406ac016871181819aa600cc60404660198691623ac024280d429aa600b580804212523005ac01021096b8118a726261561e04a7270350a60176204e154389e200810aa04e1a4f025000ac21000084289004a20c02404a8138004a1a44086300c4a2e0621144a933),
  (0x22e88a6612a8325f2479a5dc0757dd3470c5b88693d9165e555f051bd2b8471d0d63d54eac36a4b862a9c9c820446d816343fa0c24218037c000, 14, 0x8102702108a0170350a228e027382813845000950270820012ce64089027082c81289316a4a404e0000a027300c5902512a2cc618eb5c0b58409c0b429ce8009570350e33850804e095027092c015ae05a3067081409d50204e124014066154608e51470129c140942394780842ab06060119604a1d4499511410148a1009c0025000ad50004612590351e611902309aa840a04e115503300c01884314101684640cc218955428002b080b43aa8640b421bc6c0cd7023140012881409423820520015845c0c420270100c031640943a8931c611902309a105021080c451c04a70502508ec822e04e1043a8f35c9014b20400148410d671904042135912180a42086b18e71902d14c8168475c5019b20621ac728a38094e0a04a11c52e05a70139606668c03104001484b081814960561b470ae640c4b0330ca755602042e018aa580b422aa580b5c02042114438420094219c000ac249c0c0d4e1406a115800380d422b0380b4238b1266715029001011805c08c2288b38181a9c280d4228916070102908581484d000ad2025182712025409cc0350d2204e16046114789d3c950138404600c0310a7500021c809d702310a08702d09693208042116a0804290128670418a0250aac018893000acb4824800158038084238004a2cd20005618a0250a2382021000ac7025600c459935041170250c501285100a813b204a1cc71961c0c4269495c18a0250a271702d600ac1267809c25d404638129605aa8e0250a2424b99c040a4002b5c901029cc02a02908e1ace02518218c03138c8118451265d41005410199c0c0c4c0330ea29dc10640d42886524601702b09238e0290c5012ae0661c4e0864094219c480c4238a129a70002b040a5e7004ac032a06212d902512630d702d38f011204e00602709220433006214d530053c0100052105903310e314d5ae05a702025409c249c04a204e006009d202938094408ab38181a9c280d42289160381aa4540a4229c043812849003812ae0521ac608e3808470250dab920215c58118451228cce0405aa81582000c6604a80ce9031c8c818845146354b0e062134a49c39502031c8101884512a28d502b04001886300c4e320461144a8d338101a9c000ad70230cac0e000561016b00470168550d230400e06a11499a4000ad536066124e0270c60198550450e1604614c3a8852e2d8302db85016845a80815b804e00128814800159c04e1a520400b8118450dac001c06a114398f160e2a0270008ce2a05212c52843808428880c0d551806a14471406ae2a0270408ce035380ac588e52e610e02138181a9404a1c5530062701023380011851540ac528e080815841300c471c000ac209806222471c2c08c288652ea94ce0405a08b0e06213434a070095b0605a0014d4600c472e062114418f32569000313810188205211c3a04e00148004a204558628094c1c04a1444999508c019b60c6019b204a1d44882000ad302300d42880640d4228a31c210302b389013aa0461a4569c38181384d6d5015b6600cc28ce080c403206a14c429036c0015849),
  (0x1e68f27f72b893be8df0ef6b717a88d37e5b2fd75fea47cf0a3cf11a79fba11c8ed68617ab913e68ba37899b0a4248a18487d02ba000, 13, 0x50581384900ad42854094239a500b590250e6325b36c80942380056481027500ce00c0009d90330ca22c718a1009c102934101685508a00180461243988b00b81a8452e212003304a81aa82c09c258890060100063181692180c423bc60f1f0250a2095027600943a8c961001a84b790019b200c0199604e1c4448c378c01abc780950270aa02b4604e144003510a3a404006a12e60c042a1902da809c398a3780890252408128470810502508e0060251800128471163a4b08406228e025382812847646810862c09c20290da2d499bc08084e0454084248460084258a5387020310a62820204212420004212c529075cc8189a3000158515c101384d041816843008c20310d62a570252c26d451c04e0170290c08c36821800118490d60013206a14c32820808c51c04eb8128c05622583004581a8410ca24ca88a3809df02d7c0ac10406210e82e06211410606ac280250a224c60c1408148205618443861420138205208128206a284698a3809c1029180b5f0404612c12e06a11460c00281382052081588114ac0b0250aa44d088a3809d50c05212e80404613682e06211550606ac280270a224c60014181482056001188114aa833204a154398a3809c302954301484b0808d8033384815860522862a04214c33ae2c0cc2a90518a8b0270a61b528cc140814be05618600205220303508ec018be640d4228f380a9f023640943a8a000cc202904301484b54181a84308c019881409c60335c0d4428d11470129c14094238614086029096184302716a28e027180ad702500101184d60c0b0250821cc988c0c0d4208180ac55005611d50204e00158691c2c81692508281029600d580004612c59805c0d4229110828e0253828128470c0d459d0593013822409c20290d62858033a0094888c0c0d460406a205027540813ae05a1a4602b18a40451c04a70502508e3014846058128530ea44451c60084239c3858108551409c42b05cc018b22c0c42288915a3060404614402e06211580c0c08cb0310d23090204e1059160621545293339701f02b0d5310230a2a810d45c08c228cd1470139c1409c22aa0008c248000103031640cc33ae280c590330ca38c85b25c1013aa062185902515b00a3006213633604601703108aa990250a632c51c04ea8159c240ac50205611c4280046c0200280d550270e6b8a03308a5180330a240c94b25c1013aa062185902515aa802a042145706540cc28a405271902d08a705025641010b204a1b453aa000a4259b58102a620461457320661145682280b400290d628e025382812847000ad9100809c20b204a23410008b81294062c8198600601885364094409152465816969),
  (0x1922c69df42f93768b32d85aa93410908c4ca0a6ec0753b7f99d2bf8532a97944299c4679ee8d926b02b28de06be2261068308176000, 13, 0x244860095802b0d2b818b008b8128511420138204a0814b0040a428825808c10250d61981604a1443a99308a82031640cd83860094238690820502708ac1502b0a61152c0621012863112c0303308b812b02c09c298911aa0970255c1018aa06619d6025409c2025580ac44ae0809c21c080d81484560581285116628e0250cc01884d382812b0640a42688760b020235c09438ac640d411204a48102508e2046994b1470129c1409423ae0c0c424b008b8128606218c45b060205027540813849102294b303008d80310400158c04e1a4609604a454e9b26010138410c0a5902515aa1503310281396066a814885980ad416056b9f0215009d90251063342081409c22aa0521023ea009c20865116a8002b0ca818b204a1d459a8541015920409c002b0ca28450804a00178814094002f0ce32422a066b812b20448138405aa81598500bc24ae04a384889752d1814aa0008c50804aa813b005668198a954b811b204a1b450804e1015b0066d1e0272c0cc32aa0008c202b0d2a97462c0ac30290c2245902519aa953004614432e06210c023080a440a04ea815ac8c09c24ae0663149097560a020250a2a8202354094308a1009440a04a11d802f1561151804614d702564a980405212c206052a81586d5c0947091132b18d00052a8b02709a68c0312d18b025082181488d6c581684b501164604e11430a8102813800561944484646010ae04e18c46a8640d422a066115035500ad70404e181486d1a2205027000ad50295cc81885518a7054081409c229a300c429820525a6021096a0b02b649010a85c0942388319aa0b0250820502708a0814a85c0c4204a008422867156c010250409cd0405a155918042b81386350c81284b2a6094045408138450c220c50005e2023004213c328814094002f0ce425b1a0c0bc24ae0809cc1604a14c41b20c0970404e1343998500bc24b204a384889f5505813a854f0118495428102908ef8002709629420311420138004a0015aa0008c24b25408590250ea4cd50804ef1502550181285308c01985108a812aa056c1e023191813845112a8c023102813822c0d4298851a268552a191812847080c5428c80942386900a818a8046c812893),
  (0x238a89d61f0824dfa279edd0c6cc5a0a5f9d708573d4a84d2d1284094eda387cd6433c4ba62b649461d1c68c166c43e10dc2da05640b0001c000, 14, 0x12000808c25ae05a0012a04e10400259c91b0805a48002b480c4338a16409479915312c0203148c816d4057392035a8094308d349381a886018a0270861ac40b048c150204e10434885489011204e9018869600ad70404e13470b204a4d4e9a464b82027082c81288d64080029243014a406219c50ae280cd90310ca4ad22e05a2013ae640c422a41009442404a11cb035300800290961030292c0ac369604a384c9ba7c09d502b081800310a618d732066a8b02d09621451c04a70502508ea8d033082b9503164581884511a00159690008108a38a81484754094488a5c0b4e0275cc818845540a4b2a0408d5040c0a42686714258128f336a000040c0c4b0330ceb9903108a30cb02d216aa32c04e0820310871960270c08cb03112628e027540ad702d112001021640cd703110a85451c04a70502508ea815ae6409426aa58a8158512ca950404e134309604a2d489802c0d421b00800c0350a618d80604608b0356008439960c084268f15cc81896066194e48a38094e0a04a11e32c04ab2302508e00118a9005815ae640942488d5428e02754084002b112b8b0295410302908e18456802c0d550270c6b990315400189606a1cc52b00c08d0330aa19d0280661354320860198510c622d732066205027a00d5402b640a4508e505402023a01811802c0ac2889319a28e1c34084288675c0b4002b19200b02b04c81a8535c00b0350a61c472800408450205270138204a00158b114b8169c04e0814800808c00604614445ae640c4229a300c4b04042581286d2c00b02d0821acb020460118470c0b4b025142324e9b15142013c804a68c031040ad702d12b2150235c09643204f30108605ac8128b121200d04900a421806610d702515e35643206a28c0351009c100056b8302909a23e40005ec81a86528264762a0470019c004a11b02d5c094d5004618b02509a24c78c00903602709ab812d00662c7602046a818c02c0cc228a1992a4025341016c8056c8128951a79240259009e602b05b0138406300203108a28c50804e08148606a6a602d900ad802312331903508a54e06c540813c006a19444d49808570250dbb1730066c81286311608902780101185180481027082b8188851470138005601703108a2a451c04a70502508e0018b234084332052c81286d16a54c51c04e002023096b8128a38094e0a04a11c33204a15468802c0d451806a081488540a4d0350ce0001804611c35802c0d4229612c5820212c09433860522b529c8600d5c3c04e581a8655c0b5732062c240315c094308a9600814881409c10290d29e0270821ac62b0080c59303008c20b204a24c6a8a1009c102f600cd8081409c102f0c22142303008c29ae04ac810405b2014b00008c60270d6305902522265452e5408570252cb0f025540d41023102812aa05219c70840c0a426b2600011b004e185920042c8128691d68c42306060158430e62050270ca81084f5c0d452aa600cd9040448138605a1a440b204ac98000463013b204a20455975362b1530bc09c2a86958096027080b57025640cc5a8c304d8202d0a2b812ac2408c20c88009d81604e1444982),
  (0x1a8ac8de452fb765ab29d7829df434950c3aa137016765b9f1b16c645a7ab7141e99c455a008dda5c62b291887962920fd862010a000, 13, 0x142a080ac90204e0015865142284025000bc40a04a0017867192b9903154b816aa500bc24a40462857320621149a8878d012b0066205025340cd802b10ea80023080ac34aa8c58158510c0a4b0255c9010b204a18c86b0501012851541011aa04a18450804a20502508ec0178ab5cc818b05c0b552a0c0b4202b0de22520231c2b9903108a5d7f2a3118302909a1c4b0256c581684b0820502708aa814aa2c0942aa8056b8302909aa060215c9010b204a1d451a810281384534a0168535c9010b204a18e402998581684b04a022a0409c2286110628002f1011802109e19440a04a001786721209702d30a0178490818189648084298835cc8188452aa904025109012847081180004e1043288b5cc8c00056b816ae04a204588d55c1190350a21010605a154202b4808d50204e581a8652025a451c04e69202b0aa20128a780d4e027349015a405a1c400806611454006670302d08e1812a04e001280052204558a00101184d54001484b5c09531a04290402509a24ca89a480b4e0a04e201986508715029c809d61e062001386b18aa830354870d240561543389164094799c780c45027081150204eb00027092204528cb8090189c34085702d0cec15025640d43591348c0e1a04212c338a5c0b52031602019aa04e1ac648814a81484b640cd71c06614462824cf813ae04ac81988d4cc816849480815be0523030330890198c0409d70350ca2c47186600c426aa4c1011ae04ac81988d4cc816849481814aa180a4258c00095903308b812a45409520270e62c48186600c426840c0cd3022409c20b006740128b14c0a573204a13460606a30203548a8102718001384b112295702d202902035609041606a114308931a29060c0808c28805c0c4228c0c08d9025483090204e104b03510a2c4899ab60b990250921b523e05652a62046b81287111a90002b64402027082c81288d540022e04a5018806409520270e6354719605a4a5214600c426c66c08c02e06211553204a14c65a454001184b601001406aa8138735c50198450418c033640943a8912865a592e0809c20b204a235500046c880404e105902511a90b02d000ac3482480015849295310235c0943888d480015b220101384164094468200117025280c403204a90138731aa38cb02d25292a4e04a15402e0809d21604a14c4a8b1),
  (0x20cc81adfb07875d5072e5b026b15a4066a58825fad70c57dd57250e536c4ac51d240b4e2e33d4b5029349261ce466c14cc51a10142ba0334000, 14, 0x3c10169e4011803109619441a040d81284118a819900460012e06a14c32a00008c209111880148c200ac21920c0d4a029400b449a01808d70350e209003124b1d2005214c102b10e2840200008c2494066b8188b530a3080350400304052134802512a2846100560012b2080842a8b16818a0250a6b031404a13434842009580330e2b010c05248602908e481027180a4328eb1800128604501a8450e60820352009580c14481027096194408b322268c31404ac170250a223561e062e0e0310a6b0f03158f890805210432b8380c42a8d374181684600cc28ba28b81884d0caf9802d0963010606a14c12c042101ab00662440080420880350a23040a04e08148205620590351a651461205678149258085c0350e67980805214c388c080c412c05630139006221490204ab01086280942ab010084288f318b030350a6082035600cc388004501a85320c019851240813885828188470d2284a2ac0c0b561405a115f02b084012b00661c563e052b090210409c60004a1080250a2198031180813b206a1945992b30618a02560b81285111a0060215820138606a216027280d4328d3084012b014084298911818a0250a611803320c040a04e481027096204598c52221080250400148410c101484d0c501284042b990293058128431263c520804e9040275c0b550405a1045aaa2c181084d0d20150315cc818960661d452b0046000040c0c520330ceb9903108a30cb02d216904025109012847540ad8023601011ae04aa819b00c08c11606a14d90251624a55304808c24881409c11606a14c428e15cc812962c10302908258128871663b5500046904025109012847540018aa3409c2a893000ac94ae64094b160818148412c094438b31da0920804e001287348201398066b8202109ab990312c0cc3291500581684b040020606290198755cc8188451865830212c09436949053014aa046b812ac6809e6025300815ae05aca424046104002b64094549152e33010004a28002f1009e402511630573206208202d900a401a05a12d2023182b9903108a55520804e0012a04e10434a41009cb03364601029082c820210c0a4368d126a212027000cd716066c81887518a00b02d08b81286062c920212c094398c3217218035102813b0056581a8855c0b57320632120235c094308a91420138205ec019b01028138205e1844284600cd70256408206052135802b4808c50b204a3c4aa88400cd61e04ea81a840c0a426881409cb0355c0a442840c0c581605a8120232c094348b31d6a840a04e115830102813aa05e184428b308b812866409428965410302909ac015a4046284b0251e65d520804a21202508eb83031092c022e04a1818863116c18081409d50204e124408a52cc0c02052145802b4808c509604a3d4d9b264101086052c81288715aa1503310281396066a814885500b661605a12d724042c812863),
  (0xf6eee9ebeda9d48d41ce0cd9cc0c95c6abd3abe8d18a683382c7dd75870960658150e4893622831ec1791600ff08c02b000, 12, 0x52004280198c000948245c094298751632952e04a15503e04680138a000acf0270d2481292400811845400d4499018a81a805c0d4228931628040294000802d380cc38883242840315c0cc9001809c2886b9429703360a1703308b2972a05615450c05a80148c046415031088170230a21945990402810a05008c20330d22d500805630802d000957033402015a0066b81188122a54500c0468019a00008d002280d42187314a3000251008442006a14c548c00094a033280a4459018b81aa06008c20a010805029040ac338815c0d4629532e279c033400acf200667810be200c413205214c459c7c7811b8a4c81284d0e6f8f0213c0c5f3206a804025040ac308b37c8019aa9409d70250e228a0337cb81a851140814be2409df02b140944a8a5c0d520a3008c2686716258493e04e8160210a6f882e5409c29875122810081409c208657c0adf3206a14dc205c0d4289e7c7163006611c31895142f962006208148c046081340661441029040ac529217c4018b2066f802e066c0138631023d4f205808c20822409c00c04e124459e04ae1002d1800129c06a1c459a0407851005611c3088590d81085300b81a851708170350a27902c0467813869102790023407970330a278f10046154308c080ccf0c40081484b0ea70128b13c8060294000b0330a218c5a88080b50023),
  (0xbc6bbfb4cb45b3eaefa34a1ba029fb9889038fc8f58ee89f8988918427cf70262358c5615243fd2e82991f01a11400cd000, 12, 0x90a3c09c1025400970356009c38893fdf862006628010066154329e180ac10256c481084318801184940c018825c0d422893400015904009c008400cc802510101a84600cc258913c10189e180ad7281009d70250c225469fefdf8420600c42a845c0d423fefcb9000180ad80330e221cf0c0463170330920180315c0a4369e1808c6100461060210a27980310a6324030062b8202109223461004240118004a10188c04085700042b812ae0010148410da35489ac3c0c5620244a302308e184f02914ac81a8f370b170350a280f02558c81a85358b06023082b163a0409c258610480188a04218c72ac583011847580011845200c590331ea7861005600128636c40129004e1c500840d0902b74081584710a2c460a0540c42a933184ab02b68001a84710a2180296800902f0962850205e12c33805c0cc2a90560d2502794081384b10b5840291409d8005c0d4238736020502052281586700b81985518a810120409c209005221450804a20502508e0015b2980842a8f3),
  (0x111e879c0e1d6ee4470cb531706aec54ea7891e28b44299dd0e9268e2b394f0a2249e1fa8fb87ce3aa1ad8b103ee118040815809e000, 13, 0x1420380c429803c0a411204a48102508e40003309232c12e400842a863180012b60809428821878128515c0d4499e00101484d4020803508a18c6090080c411204a48102508e0014ae04634c858c400cc5120409c2580200cc2a8a50400199004a08002d1400202d0a63013889043050275c0cc3488508b819843184014b606200203108a0860204a12d703512628f1e200cc2a8653c2812847000b5b02904400033092310033600c41005c0cc2a8651864ad108a180ac2031142890204a10c35ae780842a8d3188019920040198550ca301029180acf0a04210d00333c401184508c170250a61c4f022409c209e04a00602710094f0404214c548460101080380d42289316221802d248016849188018a020094e20042144498c3c8013a005a1cc22004e209023606011855100811ae06a194799314078902b08a30f0251808149e05608602b08e1018a0600c570250e64d5e022409c20bc04af051e056401386111228602318001284b5cf141806210d70251022d4998c400815855048013b00620850204a12c902710801a9004a1cc52e06a31002d3ca81a85110e0890273c0ac5025113f810c400cc53606a11402e0663101806214c338c04094f02056301484062b900215c094398f524101882180c570350e620102b24d81aae04a8150310862cc7092142013801809c259204a2842031243000250a2b822e04a1043a8d318806081409c209006a21459845480108530e230920066157f080409411006a8013873),
  (0xa4ca45a2c9cb8c889d87286b81c77369466963e59556a53f51450d5064ed33630b2aa19514613f08407d07606f032007000, 12, 0x415850271880002b0aa280031200d4328c404000405a10434a00562d501e04b81a8c2408c2088f1663441205c0cc2a8654000149004a8000292009502000c81684320c8188454078129e000adc0290c2a0802908679904042154389e700a483e000a42086b3c40108457078109404ac0f10046104398d1182010270972800332009c10a05278129e0428148450ce101892080b570230e6a811606a11c90c200cc2a9200401a8539528f4a06a7861005600128636c10128510478148c062b81a9e20801385514201288180a450250ce2c411204a48102508e00148ab00101484d3c29cc1200409429b63c10188493c11702309a1ccf0c200a400256c0c441821808128515c0d4f0005a8011006a11431b6000ac248e12e640400100b4298754009c0022409490204a11cf1e000ac298405a22422e4008429863fc83f08540ac21606a11c10a04ea019fe),
  (0x12aa936c63a01af7676fb9f9b1ac305f9ae0151ea524b0a010f6a7543709928c8662a2e496309363bc13887682860f4076827810a000, 13, 0x10006a80159004a4190311408148005630103508e40202909a305027200d4102910a58451e04a78502508e0811820400128430430118204a19c802b1de4190310481803108640202909a28002f096b8129012aa9880314c4811a60408c2294480c590270ea3cc512180c410250c63015a0200950240661444a8c4000158552400189006a194602180a4298c05630f0a04213c319e04a817200008d002b0c2b8128b31aa3000252021a02900b01384b0c101484d18240129157010109c0400158413809581c24084249c04a21c8995140a815b8180ac248c700ccf1204678102308ab81a8b11048119e0808d00330ea40f0204614c32b8600ccf06300cc21b204a20468a0000acf4a05211460206678602709630f0253c0bc34a04001002b0868016b0062b8128d31ea300025140c45022409c50250d278802709630483206229d02900305180461243388b20101484d5c09490975180814a0000a42a9005631030062154802b04001a84910801a822409c502b0e220803508a28f027400d411204e7815b005224452e06a1150460409c620000ac2a8a000c480350ca0103006211d7025408012006a114338c4000202d092801589520094f3004b81a8490de244a98a000ac102718801a84320094908066095023092244804052c81186d1800129224281988180a42388100301384b240948890640c5d1005a00602709648202d09240128e126a3100a1009c20a004a24c8125c0d550270e624490c1820502708219448a02009502a0661444a8c240a5000052154802b40084031400d411006a114820052086029400d451e600d42387104b81a845),
  (0x137096ccaba40b126811bf99deaeb86feb6b997ac6e5e2ab994c2a2446ca1e10527da3e99f30e6a55a28591406522da169881810a000, 13, 0x60c2004211c3890540c53020461150035166008033d40c40643009c2882480815aa4c0c4238810409500351e6608031549012800625122a000a42598080ac80290da40128e122a5cc0102050198492000602308240128871ea01903508080025000ad7023126284788c200c5a3206a14d6022409c8025180a445823c0a480a0424012875146b190350a2b8a02909a31c03374b81a8513c79f0290448138431024012be3c08590350e2b8a02909a31c033240812ae06a1c4838062b060357c09580313c30188205648139e00301a8430cae014901326308031580815b206a1cd63e052f883206215412e04ac013861186b8a02909a4050804e104802520501484d2008902708240128c0522aca3006614460a6809c2a9004a22b03504281a847112280035400ac802514d013822409c249004a18202909a0162004611c802511608402510081284794401384b08c81185522222b18062155002904b81a8452430188a000ac80250ea0090331400159004a1d654a2078534240ac22b41408158450ce34479ca06a0850333c09cf0a04e401a8650408cf4a0448138491840158431662890204e124003110a4190311408902709280118005640202909a40129012aaa3c120000a5002b0ea40129e0410168492809d02708218c83206200102720094308ab0440159e04301982000c4228831524010605ae1002309278002f096304802508c8118512aa79000052801587520094810640c4f022409490204a11c202d1520062005211c8025116504f1e000ac2a822409490204a11c202d3c00179e04a1ac84821840179e000c42289320c818a0000bc2090640c4228d52c6310000561545120409c2480062401a8a5),
  (0xd0ad03ca2c53c04b6db66b5fb46b3fb38afbad0a399c69418f28b576a71b6cc64758c49b4823eb31e2bd1de0ed08c02b000, 12, 0x3f0001681384b5c81803108e1cd40a0427970004215439a83c084f2e500842a8735000502708228512040942186b5c10108551a7fbf080809ff7e00b819a0b40ac23a820701885350a0402108e2001206208128635ca0108551a6a09121028138410cab940210aa34d402042a012a8052017285c0942087512680f0213cc9002d0aa1cc0380667970350a28051e04f58119e1409c10230ca0018b206a44c80a06a08002909679d02b00901184d10e01702d08a5053205c0c53340521044aa6200c5332400842a873004018a625181284328a818b204e1d469e64060e02708218d3000408550270d20012a6400d4298eb4d5811a6062981023000c432a05c0c500205698148804601703308a3048a88400d6320640cc2a9e040ad810640cc22863000b460c6004018b20661d451204628102b4c901a84712319702b08a4040100631990351118188411268133406a0815c60520811a0000ac228e18c0011ae5c80108470ea2c5202200b424825409c302d0c660803100e000292880109404a18c5a8d321679b02b6ca015983c0cc28883506152404a4020210aa24c58d048801a853),
  (0x1400999c7122c70967dbb9f9a42c785cca9c92de95647aa3b90f67423799898b665ac2c095e895a3501898ac847e1a804081e80e6000, 13, 0x1400129006a7990350a369002305581384b7000158493c094709e000ac11204a48102508e0015b805a324100066401aa0ac09c80250c2080033640d432a06601903508a204789a3b48062406212c3a805c0d422da1498139005a1d43023041016849b4c01a84b004190310aa196d0a4c09c10290eb681590080a426a0600c5902d0c600832062154328a1009c0025040a48031616880290861acf14149813b005ba01582000ac802d0d2401290126a54cf020460010211478138005e1ac00251a641903104801190080a4268a4c09c00c480c42186f156b81294132a78802320e0602b0a61a403206a78a023000ac308b114481025000c4318005641903114e8002909640202909a40128c122a7883404212cf0257000158492408129006a10403320094308c300c8f06046501286112a2c49121028138410ca4800310a641903174481492000a42590080a4269004a3849a80480d45280672815a82090188530c602d0004aa01aa8100012ae06a1cc418a1009db03104481384b5009540a000ac20a804a224f02046780031092a172e480842386312a44ed2805aa012a85c0cc219e0400158493c00138004ad8188833c081480056a170230aa2ccf040627850004a14422e04615459fe1048158404e7011204e0012800660172e540842387310678002b04401a8431127811204e00148004a22c1283c00128406219c4a8a33c080031086b8f0005aa014a0540c421ae04a3047a953b4901680380b422da0009ed282008c26873500c542eb4a0168410e60142e066154328a3c09c002d6c601484b0009425a200b428863040015a85c0cc2a8a3c09c1029040900230a6001488b50901184d24201b03100b81a85310bfbf08b48180310a61d42005c0cc2a867),
  (0x1814bacd7f2b374ce9f7cc424cf22a8a5bf29d6ae30696b2a1726b5654daa094669784169fc0db668c2df96089224781f087d0296000, 13, 0x8c2030350a71811406a14c328420094e46380d42287316230102b10101a8511030118606a48002b3860118551223cc0020424018881118138432870b0230a21d4699254d18148628094e0004214449be000ac40606a14c22a066146310062506082c08c2a8711263140080c0d42980280cc2284540cc446046b81a8654ca8b02708618488824c00e02b09a002031480cd432066114519156818e031640943688968281180200c4a3406214c42862809401c06614446b4a018a0250961b5a3068901a8530c6d280232008a0350a21cc52800c501284b300a446b4240030330aa2013b604a28d30804e98a0230a622431404a13440406a401280380d5a30380b401606a11c418a11e654440c0462030350a610e12300d421873122200023280cc8080408ce16046154498b120a2883a04e008027092f8198ab28b81884d74001580200800a04a12c61205211c50b20623d481901438b0250861aca02915a2a33a04a423029640cc338ab28b81884d74b01490740cc11204e00602714094348a158c81a8512464050e2c0942186b280a45680200a524605212d600046419031584016965409c218a280b4002b0d23849aae4809d6145c01203308e1c446821400158491409c803114080023096c8a2406211c3a8d3140000a18084218671164050e2c0942186b11a080100448138a04a185914480cc238711ea40ca02d29230a0332090198511440a02909a4011204e28128612000602714094308892165120e04690b02308a24c588a180ac8025009019851b400128a4c09c802d04481384b200946aec052436031600ac3180140d5a0272009450605b31303308e089027097b01488400d58031640b4418020c8188550ca925025212819a406ad0f2406a14c33805c0b650270ca08f0310478178430028002508208902700094348a3c09c002f000944595320c8188a0448138494008c80405213452604e0062406210c378ab5c094c09d53c08202d09368159004e9f02b08e18403206a1446182000cc10004a104f02046781986b200812004612400c04612c338052134709004a1000336408c38995),
  (0xf02e7dd56c9bc94c7bc08befb8eb87b4ab31a88a15a0ea079b89b198697f96695f8c883176464f5824fd3a02d322a15d000, 12, 0x42006a7170230a290f1c06611de02511621602314781384b3c0011845200c48087408c51e04e12cf0204611468a048b8138510ea54ce025409c00290d678119c400d42980200c401406a14c42a040001296540cc40004a155203140401284f40401296540cd22005e15481e056117f16540cd21005615502e04a595033480d4e0270409582406a801780200d4228b1382012a04e124358004aa100230a7fbf16540ccf035400012847405950333c097f16540d5716540cd824062154e2006611c002200d42986538b95300628019a004a25451a00840188450da718023380957031107150230a2501aa04808c209c280d42291300a920804a0015869389012aa000a4258872024000405640149440084a0250c634c76805470138a1009d50290d600128c108a082000094238631222cd53006271502d4809c32845c10108510e6c0c08540a425a404e21590404214cc106040128470daa842404e114824080b442a05211c8025142354959b1202010006210c3990204050230821cc81406612592e0421448aa67c1080250a21ac00606a20a03508aa8e0250a234c60004e20203520094388818181aaa06318a16062154328c31e62090234c00402108e181989510101a8004084e18046154498d100201023280d439802070b0230a61d448905),
  (0x7b2f57e93b3f4edb7ac354ea2c17812fed8ab0744245b52576ad120a283b2748ca96a1a62a0508640ba15827800, 11, 0x67e50a080235c0ac39aa5c09d410180ad50315c09542e0461346980480d570255cb94282008d702504b8c0215c094102912a2ac89fefca120204ea1702309a09703508a34d204480c4102950401184300c42488d20a01a8248a0169004690102b0922d468906c28002350095402b112a040004a10433915040018ae06a090023500a4100062b81a8651824cc4000461018901008118515c1010ae04a1d46980204810270a690f02700b81984512b28802720a8f0a5c0d423865127f881054b8138530e3a17027000a483a580c429a43c90198470ea0802e06a144328a3c09d7033201040315c0d4602bfcb970a3c09d71c4809c26873),
  (0xb6cb2fb28ad99e89e196e8e98e28b780e70b6ce6a36785f35b64594404394203f53b83b129c1511380d7052039032019000, 12, 0x44812820624813fe40a81492040cd70350ca206080560012bc06220c51006a21e0c04e15430a43809c28825c0d422933fc480025040ac90275c81503108e1cd43c2008c24a824901a825c0d422893156295025c0d42288500d443c056ab4035086a9802d08e09703508a44443c046080025500a435bc0009cf2004210c00804e901a871040018ae06a194a982540d502e06211c9205c0c42a80140d5702704a011a8240ad7025180812ae06a18c69aa3c01703308e19482814001584950095408042a0128671ea4810250400118515ca80029082b812a85cb9002108e18c46915326a9702718b950271881703108e004031043019855fc081000461142031044812920409423b005a808025944013ae06a1c421004613474993180815820008c2290080d4288a1009c9023000ad730080a492004612c408b510281382062b81a885366010035100100350a60982e04e1543888084019a84008c2088d6c3010290821ad52e04ff8b1804e317035),
  (0xc32c07beebc3b50b25ae8a1b9de9d79ac96f8c689b7f27d97666bd5605474c24853a62a329c2952342092021c50d4007000, 12, 0x16163009c288c5c0d630c04e4012808c00138555c094804052c81186d14a818ae04aaa50298cb81a845184000330a241903114a81890080a4268c000a425ae04a3849aa000601a8515c097f0048b8138552c9000250aa001382200d403206a14411005b3120230009c34ae04a3048140622819a404001484b201014b20461b41100520190350a2215210052912100c08c2486d041016800521af802000c4a2420097802d041016800521ac608f5266401031002840270009410291020040005e00128611164cc8320620880405213400a400bc2186b5c0947093530b81382000941031948016847016813a00521ad02804aa970270922000806210c102b1000402108a1018ae408180230a218570251664d4608042301584062304031184810250861ac00804a40138615c1170250821d4b9fefc3011204e12d00330040168450480198004a0150004b81a8530ca2000331009d42e0662010005212c6023400cc508f5500040235c0d439885044812920409423900662040c06612c34bc0621170337808436fe),
  (0x108e7fbbf31e8edea6d6b4598b6c305deab7936e9564a7a4491ce7e43c19808b8a5ac2b795109c64dc1c88d0831617207f80c800e000, 13, 0x53405649012056154502910e481033200d432ba040ac90274049203568481384b11e4810335c0d4328a68001484b3c98602b08219c40a06a18202909e23411006a114f0a1820178530009592464094258751c644450204a08902709629a1204e125002b240814aa04e1c402e06a114f34056401292040948035d828118411522195a0421543882740ac90274049203568481384f11609703508bc1702554081280062501a8ae00b5a2a04e10168005222c80251c25ccf026810168550d200a0350862040004614c020640c421a405a2547582000cc83206215442ba4c0bc12a06614502e04a11cf12400cc42e04e11402006ab8128c040948320621540022409c25be000ac00270d240202909a4001006a11c32961148017aa0622000335c0d432ca040940033204818821400158510e6201382000cc2290120c818822409c02004612c52a06240202909e23570252425d562a0628017ae04ab0602740b0c031096b8128c400d57025002010310a7186027200943a8c142013820620800270924000204e124002310a4190318c20902940301484b10e40202909a40129012aaaa51005213e32e06a11480a1009c602310281384516248002f180817851040800230a21947990640c411204e401680080b4602714a818a005e18c64ae04a504ca80400d4002100c423ac600c5002f5c0944aac1009441004a11c10c0421241004009c2186b201014b20461b562a062b812fe),
  (0x118a84cbfc1f42f5271eb57998ec785d5ac9942299e483a2e10f67e439d9c40d3a63c2a590007f23e01bf8d086762c80fd847007a000, 13, 0x1d3a182812841581080250a218c03164094398d524618a02558901985111ab0002314181a9404a1cc21004ab1200042154398b100e0199e04701a8530e201c0333c0920350a61c41001400128410c501285316a0800290962820352009402406a0972404e10c308b322228602314181a853089150230a61c450004650198a0408d70350e2314814600cc28b4200b764604630138804a224608828b81884d7c501684b000810901008902709200158804a2846aa6640d428ae280a426c610501a8538cba302154b81284312a2c4400040c424820008108450d64011204e401286b2118a02d1809c40251022a590312ab284467c09c258804a50168a93808c84604240168c04e401280640d428a6280b424824c0a480314cc81a85305a016a6200b424b44c08c814052134800640d4288038094208ab1040a02909a4011204e0060270922048025640c475a0300c57025243018a006a08803524001985110a8092c540c42a86f00b81a845100018881000128470e608403109e8172040b180310861b440ae04a34c7a88184810250861a400c06630402108a40603308e344832062b040277c0ac802d181016849200947093540b0102718089027092801a80200d42282400d401006a11501274a818855400bc100066b81a86514e012b81409423827409c0025000a4458a3c09c00255c0d44888000cc4081808c2888040a4278a14080e0330a21d50005c0d4298653cd0202d0920060a05211c359e04a7811204a48102508e22590231a228102504481384b),
  (0x1178828bf79d02e44703b1d1892c30602ad293da9e64efa6d12828f24099ec8d5e6a83479558a9e5482a093c87962c80eb862009e000, 13, 0x3c41f0210967812b8180ac24920409480350830199004a18461b8600ccf062809c2186116230420052154f0a04e0080350a621650204a001990040cc50a000bc258713c09c00251c24190311008902709240202909a01002309640129012aa2a30351809c8025184014c604b281590240014853147813820663010290862c4f0a04e08100046144398a520c818822409c802d4000158405ab01388920094809558c30128c04e4040299519703508a4060006214c832062308025200b440405a00158691824548020620050205228002f09608f03108e00128e122641903110081490080a426804090188430d6b8129012abfbf3000b81984740280027480cc00a04e12c58ae04a786029180b4f2e06a14cf0c3c0cc20418084238c2408128435c0d4498f12521170404214c36a03c09400c1409480350e621c8281400158415009541e042a0128671ea48102504001185108b812ae0461d4798a18b8158c040ac10004611480406a14451e04e481180056785027040c432a020095703108b81184916a64ff7e94a25285c09570230ea24c8281408540256ca01484b5078002508219c8a820400118515ca102406210d70251022d4898a3c094f0a04a11c0023080c480a3c094f0a04a11c1023162b822e04a1043a9332028f0253c28128470400188431a6419040421448141008c20b20622247a80700ccf2a480942987114e890606a14c338605ae8202700901a853122e80023480b400291160011406a14c02e06a14452ba587818b8480c429895),
  (0x746e7fb3311e1cae72e258caa8b71520bc1073ae11beb76696bf17aa824f6820f79d639e6d8bc9722461581e800, 11, 0x3f0c9c0c58033008018825c0d4298850448138a00301384b0d22812800633ad2e05a14c31fe94284027240cc00c04e12c90251933982a04a14c388c4008500230009670004214672e06b38f02056114308b361f851e04e9014805c0b422fe9c0818a0380cc229e9c08189210a8198490ce71002708a58c027fcc12005c0cc22ce5008c4200660815869400100334029502704581a8451262c7f002420502708a401589340a819851003013a09c09ff2e6009c0200628170310a7f8018066a92025400d438a0407810a004a19d0020009400290c222c02e5c00138410ea24d70404211704052b815873),
  (0x6fedcbb7b50e9ad279131ee36c5f7cac8d1e97b05206b9a726da1b0b2463aaf109a0c30e2a0508881021a030800, 11, 0x50004bf810004a8270270a3f8f089c0c4000400d428865fdfbf02000170350a619404e067395022c0d422873122009081409c229004624e72a066144420067381882000a425a004738f0004b3818820009400290d630404e5c0c42a873fc2811204e12c6025003013a806a1cff02500cc60253d384031500cd0025fd38103150c01885340b819845180012a0000b428a02428c0230aa09703508a2c469aa18001292102813845200ac49a0540cc28a040001031082801288b407a702b0828012887180012ae500842a893fc305025fc3010253c32703124081380400c42a885),
  (0x5ccb6766ac9d8cb0b5fa97c628b70c214bc8782ee9d9b766deda1b0b5a6a6ca163ac042e7f8fb9f03ae42803800, 11, 0x2c60138c10097f7e149040004a827027380cc389e3c08118459d38002308b3970310a62d4f2004739703309222ff4e000c50025fd3810005214490c05211d002501f8000480cd02e066117f7efdfbf0a3890138533c80f0210a27902e06215439fe18005027000b4328c240813845180d445a05c0cc21a09c09ff7e3890138a1009440a04a11c50804a20502508e8018a05c80108510e645501e9c78168510c28010005210500254009c558a3c094f0a04a11d02e06215469fe),
  (0x692d17a1335e40b9b71adfd3a796f11bab6e686cf191b0a606bf156aa648a8f91ba303e6690c592a1020800c800, 11, 0x67e5ca813802c60138531478138204a0002e4809c2a873123f952a600c4f2a05a2813865300a4c4e06a14c51e04f3816ce056785027400c670004612cf02118a8051e04a78502508e24674e0408c2286b5cba70270821d4b9fe040015aa04e21703308bf95085c0cc22fe5ca813963009ff249c08002b0a281703308a3061e24081384b0ca817033087fbf7e4138139c4809c299e3c8018a05c0c42989538a813b03ca81498066194f2006a14501e04001484b3c095002d1427972e4009c208751267a702d9ca811606a11439891fc200025),
  (0x10467cebd81e8edc66b2b219802bb25a8a8f139293244d9dd0e0267c2aa94f09fe3b41d68e9871a32c15c89182ce0be05b815809e000, 13, 0x10a06228128c00096720240ac228715c10168531ea2a70315c901385340281a801478129e1409423820462c460a3c09c28801809c269e9c0c421803c28138c0009c26a00462c462ae066782033082854f009c80128515c001685316a7804e400942186d0008108004a001488b3c00f0210a2b800210aa2ccf0c0009671205280128715c10168531eb38f029180012ae0661b460004a80189e40b8188550e67a72004a10c00c04a30002508e234f0004630002509222cf1e0408c22ae080842a8b3156a72a06609016066154328b11864810a04e11401006738902940095503312232c51e04a78502508e001680546016853d00c4448a3c094f0a04a11c00230008108004a0014805c0d4298cb01390025086b970004e104398cd013900250a24810255c0016855127686081409c228206a20672004aa8198710078108004a0272004a10c3880044812920409423891000a465920409400315c0d5b021166806035193818ae5409c299204094f021000ac6001809c28822409c25829c0c4218c0009d0023004810270a21a462ae066d8109f501f972a04e0060005a14462e06a0010873040054e05680128715c00168531aa08024067a018875040a40180521341009c80128430da00f02100094002b1120800315c0d412e046104598a180a400a04b381a8639ca012aa04581a8450e62c7f4e00801884504b81aaa04e1cff4e5c09550a400d422867),
  (0x9ce8a78587f774e6ff67a5bf54c4d94c04b94a049949248b47246b41c4153b43ad3942fd2f62ef2e82751cc135032019000, 12, 0x60205600102108a101880003013aa05660118955c095502056a813825c0d4228405a324c98c5008d74a500b42087350a15033096a142e05614c32a804290023480c450205612570251aaa1202b09a4cd4020527811c06a14439a85020108473ca010823810108550e22cdb2040205027082195402b1520800315c8170250821d459a04080c0290a658128916ca01484b0440139e05a0003006214d702511278002dfc080029fdfbf02000b7f02000a57027006018853fc095027000c403004e5816869fc6100314080c0335c09438b6500a4836000a422867156b97184080b0236c0ad8185c094298691a2a10020660812e066154328b108a102e04a1243888d5008c242009429875122a0168208601884d0d20802e0561354000060188550e611703308a30c100062a142e080b42287312a324512062085031),
  (0xc68c61c5abc3bbcbb5baeb5fb58b09b02afbaaca27a20a199289218f68ef8e882d7967476c25654aa44937c2c11760df000, 12, 0xfc2040010085e0330c68120330428139c06a19458fefdf9024066202027380d432fe40280027480c4e025117fbf08400b501c06270158730880e0330a220202d7820203308e18c55fefc09002b40284027300cc002b1222a401006a0852805614433845c0c4218e5fc284027000cff00400811a4000ac24a02060198510ce01b2e062d81387510aa1024066b852e05211c32a848b8128490da445e36500acc1e06614441a83029502750601484d14401a8451a63c40040060118530cea0102100901a8531162800315090002b080b439895192a0500062b942e0461043a8b318aa05200462811204e12c34aa06209703508aa1202b09a54d41e5408e03508a1c54021166a01021248011aa062c0202909a4840a04e10570404215452953240812800628172004214d0081409c802b0c2b8198a522a0011005aa81386b00a001806a14c3388324a01a8400a8202d0aa1cc488c9500800315c1010855126296d5a2048202d0aa1a4408c080d552e04a14c488c000942031402840270824818a0040c422ae406011ae04a1844a953),
  (0xb6ca8d98a89985c7c577676f67e57b57456d56655f54653f5024b349a49348c48543642f4283eb3782f323816b068061000, 12, 0x103020313c00602709ac0188931aa00602d00101884720701885318a7822e180842986d4078129e40094238c080c40200621157205c094208731ea5a460004a1018801008118513c006027080a436b03008c28ae04a10109152e6f141e380c4298631009403508609402b092f0f00380d428863126f0f02308f120230a61c7f003c0ac11204e20148610008118a04e19401e0461002a04670128731223344022409c00290009445bc046f0502052781a8010084e1c540842387516240c99fefc13f245c09ff0a0009d20335c094f040421121c04e14c38841009c02040012080809ce0350ca24d0201401203308eb8128a3c00108535090e027480b4398915020109e50084e240567013a8042244698a0008d402d181018da480c502a06209703508a20c6990b50295027500b49200469018aa04e22c10a04eb820210aa214b9a04048102708219502020094208691478129e140942380056b902e04a1043a913fcf1b28056801025380cc388a3),
  (0x692d179cb1ae2ec4f762e8dcaaf734a4ac8e90f1ba33c608b30b995b24616b393fa42332648bc9601fe2c054800, 11, 0x3f00400a443006a10e03108ffbf042c0c580404ec019875fdf8e1806a1021c066154338c0010158450820128404e401a89304c0e0250a61c4500480cc23ae04bfbf0a0008ff20fc01b031400cc0020828188004e185b025040800c04e08128611122ac1026009d70250c6234eafe2080198400c170270a61d4f0c05680e3004e144398c0009c8031400ccf02200cc00c04a30002508e22465805c80108550c62042004e808027080100804e14c3ab03809c28ae4000602b600cc38887382000232080108804ec0e0270a22b410c052401986b),
  (0x584ab350293d0ea0f29a3dc748db19a0bb92716bd164ac25768910ea1638e670708b60ce1801a82e04e08003800, 11, 0x5020138204a01b0351870188c380cd4281009420276000e03308e1ac00c06a0813fe14a14001809c25ae6009c298c1008401e06a14c20c05a70199c056245e0c000945021080c411e06a70e0a04e114388b3147819a4063f900c00095b0310820102508e08c0275c094358d3fdf843006a1002e06615433a030581384904d800a05611400a04a30002509621c748030b8128550e61021c0661544360561013a43809c2afe080180330aa03f7e201013a0),
  (0x13ca963c4d21ef04e808bde9ca6e166f5b431812b18525a7a93c69dc4bda4b10e27a43989798a0e3e01a489a82f2106052827800e000, 13, 0x118080ac26980418a025080843a8930011203320901384512a1816800563c4c484200941062809420210ea24402e06a0015865c60b0250861c4468f3041000330c00c0350a61c48320621147184640c42694918801380200cc228c780c410a040ad20315c0944a8b378f090230a218411004e801a9004a286023780c52025c0d42282140c5e0290c234c60004a101880480ac1124008c2aa406210168a924b81a84554c0168a5c10108550ca29ce9da2009505a04a11d02a06368128ab40812849181018ae0661d451e06a28198c05a42d035080b4348e11800128406278108a3c094f0a04a11d012040942186b5c0d5018046b8128612e6300025080c400a0408c28801809d202b4810168493008d7040421148a97378089027000a4002511608f0353c0a431bc7800e0350861cc48803c0d5e021089020210a61c7f7e140013a4066005027096b8128c0009cf03338c0168515020202308278202110481025086701a9c05610108d1226a091e380c42a924008d50310d62010275c0d432a8540ac269733c0018a03c09422e080842987116a002003008c2986750b81684b040854005c0d4298650078198405a0015840070002b080b43a8931624a440c00101a8510c60840290878118551008402108a701a8405a2c4998c00094203104781a8804e490023096006027080a43692200d422aa10085504052134489d34078128800101a8430e62013006a10c388405a20600080d4288630478e0310aa20412046145b2e6009c218751824cc50c05600128a3c0d42988780d420887808de2a380ac11606a114418b31e2f0f2406214c60405a78203108622440c046d820270a278e0310a67840c0460820270a27811e046c0e0250a222c59fe),
  (0x157aa7ad01257310283ebde9d12e286a4ae015d29c24b9a208f466c43169778bae57626693188ca45e2108b5850e28012a88a82de000, 13, 0x1f4a04b285021400150310aac8128931868250257d2811204e008027100a4358a11860252a04614653204611459995404830350a628102b1030158471021002a06a14c38881409c8031240813800521ac100062c81a87324a10002042089027000ac3a86080a4268f3241820210aa01518046154398d104001990240813802008c25881645811b2052101089126a59656c0532861004a104a309408429871186490201809c2487540c0198a1009d018046154408d14008803500b81a85112629764a1408d00354128a0230aa19460c640a819ca04b2a52e046114338d51e32b620d80d422aed80d4258b1182840270c0d43984540cc2880200c50081409c2082062c81a8b31ca1090206a001492180a42386080a4268f3044090c0524010005212c338a11aa3946062809420210eac011806a10c02e2c08c2a865040847997168080200629190250a625451a00090198510da0820a1480118470e628802308a354304052134006480cd9025080844a8b1049016800521ac0380667811c06a14c389e04701684b70001584904781a84100cc80250c20031404a701987512248c12006a0100315c0d50066c0a4219e1408148005619c803514a404b9a04080c1604a1443988d04801684900805023400c503204a14c548cb400003006214c3a822009cf02b0d241903308a80f0293c001484b38095002000aca0006211d03204a14c12e06200e029096b8003108e8001806215590251261012a04e5816a0066018027097f95200009424a006680000300c42986d20c8198450408802308e80168890000802308e804023400c4024062c8128731924ac40a5c09cc0330eab812fe5c28e02908e80e2404e1155002c0a425a006680c0354008d202052b81aae05621478824028402510281284710200158c90418202128101084512a2cc202000a502e052c8159804623469805c0d422931),
  (0x19b2cb1e57326392ac6de232feb728adcd4425ff1ea8f1c3ca1d709c7b1bb79daed9e6a7af814be95c3c9969898e36a18d886019a000, 13, 0x206062081990280c422fe249018ae04bf810a0009d20350e2b8129204095c0333c70198513ce0e0330a27930405a09d02709678128a918279c029142013b806a18cf027409cf025000a440b8480cc288eb1418168404e81385320e81027082194658c1449003508e18c602200d421865080b484a82809660216020108531620100a0409c20a004a24d02a4008522e04a10c498b1084012920408431404a1010875162485021000c450804e1816a4062b840a04e1043282240949027540c445924008d20312409c92e04611422a062134002b252a5579803c085006980a4219004a25451e04a78502508e8019b206a808120409c24865102544108040a4f02b04802031740813900621945a8c310f014b800701a8510c62cc40a1009df02b20c81984d1008902524081284711678148a040a50060665012875146784042009c218610020109c06a1cc78b840e01284b3c084f1c480ace0270e6247f204821202d08e1d500290040188806a28102908e81703109a394002400c4024062c81287315232c5100625019a0100a4238a000ac80006211d0029400cc1120421819a00090198550e230c01006228002b08e081482080a42a90640cc21925402810005212c91005211c508a0c10108550e61002406a14c38920409c8031202813800561a4500062c820210aa24ca29814101ab80461cd2020c0b424b8000a42582000ccf03504e8139004a1846197130a8303514501a8451260020a1009c29901008450270ca35400404a8138535440102108e1946a8005242cf898080ac30404218188404a2246684141820210aa1c400004084248a1009c1029000ac304052135200042601187126a64c50006641916046c8148710820198a040a42380056b8118c12aa614000400c492406a09032046154328b31d601003114801aa40621cc5492142900270861d4502200d4218650c101484d0018a025480cc202112a2c411204a48102508e90168005232c03806679d1c06a14c389e04481384b3c095c0005612490204a781a8820094208a370781080380d4298910410802558084302d12a08158c00801a8c04e4012883080b4648c0c0d4a025600cc402066101a8611e2481025400d4020062b81aa010281390052401a885000ac60933),
  (0x1922c21dac29ab4989eeccd25a71be89cc3f2082faa7a4ba39bcad18625acd94ae9544439ee8db65002108d505561a801c808000e000, 13, 0x602700d4299e4008c209e1080118413c09442004678129c06a24c889e040ac10405a30158693c08f0350a649b02000a460270e625441e05e1147094304e01a883d20118550c2c181c04a104399110048198804e08128a1809c00250e279c1c0661443a880818188806640a03108a28c508680d4239e080a42682000a490c05211c458a3c0d42296f44299c1e380cc2886d3ce01480700d4219e1409d0273c094348817090198511d67861e06278e0310a622c30c05a781488680d4258a14011c03508a78158c380cc289470e2402308a1cc6080423030293cd01084b3c30108431a678406052104e033122654f14600cc289e0808c102b10f81a84914369908080d4208733c0815827c0d4248c3cc818b0080b4209e640c4228d51c610f02764c01384d3830a031640cc10211122acf087c0ac2094600ccf0210e278f08052f8158c046205c000c0d4202d0c2c040210a634461e0620890313c09cf12040c4218657070188552267ab0205610cf0271008198450430f031707180270a21cc518d51800f0004610432903c0d428b8107890204a10c349c06a2c469a03c0a4f0274010403308618481e0408c29865400030350865012b000701a8450e63c460004a785340422812863700d4599e2478139e0409c229c06a2cc68a03c09c01206210c6060661180330a22540382808c299e4009c10235c0d4488e53d2815ea180ac249e24d013827409c258811467812b8600cc289e04501684904301484b184190310449802b08eb8128811aa38cf100448138410d67812b8200050251809c3088b152e180804214c38843c28402708218202909a0800291809c35913001830404211c3ab03008c298d13c205027043000270921ac5082200d421806410e03309a1d4489853ce0e0330a27933a04e12cf025102781027408c238405a204002b1920800333c0d5c2406614410005679c02909b19d0275c094318e114781ab8380cc28be7409cf02d3c095c0005612460804008158805278902b08e284002514181a9404a1ccf0a00a8e0250aa18c498b11408178006679c1c0661443a9e000ac11204a48102508e0015b805a103031040015aa04e1cc832062114719a93c260b027244012fe),
  (0x20a88165f8c7cf5d2c7375af069f585a5ded7085b2d5fe535d38c4b8d23a46d513040b4e5234accdc2ff4ac428fc8521eec61610142ba08d4000, 14, 0x3818198438581a8530e2182040400148450d62042043008c29842c08c22840c0cc258f14030103509640003108a1050224084218a4c09c2a827409c25827409c602b0d254c826740adf027043015849142314602180cc2386480cc2a8c640d4228f10818198604610148a6008c258cd04401392400bc2a9004a2811006a98108650898198a04a19c30405213450420095f1204a49f02508e089025240812847180a4579212ea62c50606a5012b00662810406a134308f17c82402314501a8451268150330a210802504481386080842a8a2810168550ca3c492004608159204e4850804e15400c04e12c5486080a426b006208003120a818855244011881409c60004e12c448c128ab4d3100448138412009463206a144658c4c09530c04a11c44ae280a42690140814820561d5002720096d0314049203509f681290b40812853b40a763006614455ad80a4f2406ab81286315e30452604a98502508e4131204094218711123020314c40188450c9018b24c58118410ca2cc9aa04040128411478138c056785027000ac32a0240812843207813851152b900a300c421ae04a2045aa134c0b6035b48022406615433a05c0d6d0270ca3c491a6b409012062104364300ac28b2b409c228b522648ed2604a9ad02508e9014a45c0ad00350e7b130214d6011a6b808c22ae480842a8d118101880200c4228a2098188454c20108a04a19c90204a10c324062c8128752e61050804e0800291809c3586080a4268f3001820210aac0c0230a62c4502046404100522813821800138490d63047a80645811b20521010895162714100066781a82700bce0330e22853404e15411204e12402c04e12cf38052134f10046114b0a6380b5c1e380cc288691428f027086783023700a4369e04e8138413c09400297070198511d678f0204212c91e06a10403308220cf02200d421865700060270961a5c300667831404e10c308b16801003154c8128531068002a0661443684200949080409c22862809420210ea34490804200189e1420128814094238810c0b55031540ac920046a8189204e49702308a11503109a001592946aa4c020000ac80250ea7900213c09502e06615458ac1408440273c801384d0081902d04481384112a00148cb0000c0310a618dc2c700ac239405a4860290428148471020170350a25142080c10108550e200f1c0621540003008c2386b1420138205200158810cb8c0230a21190310922b4f988000cc8081409c102900401184b142c821c066134389352ca7811006a11413806ac019871100811880667811204e12cf0252410168005621f03508e78128c929e685a3e400c553204a14c41a040a8198510da48f035142013841240ac91210801a8430ce00602709632430405213410804e1820210aac0198b104401a881409c90204e12df5604e40118691c24800332810169c0661d4589c5),
  (0x10b27d7bc19d26d4867cb2a9796ba058daaa14229d44b9a29901e7e43d39c88d3a6182b793f085e3e01bf8b104c61de09a83e0176000, 13, 0x248066f960a1009c1029080b5b02b5008c60251ea40463e0008c22b006a24cd882980d660c042114412046181a8c38a8138550e234c42806a30203554a8e0250821cc588298a050291009c308405a2d411204e101486b0830188455809602108a181ab06000102b08219c48913092015ac0850198430d209702d581190330861a563e05211f03198301284158081086600c42a893206182300661443684580c6003310f811cc0562a40237c0011a406a1c45984802240230921cdf0a6008c2a871082830350a63000204212d808000ac208751a211403304c01a85109201982604800290821d4488418284027080b411204e101486b1823c420c06211433006214e6025409c20cc04a6140330a2900023000ac34cc31201985199532025900cc38b648a8158416c094c28066095023082245824540a422840666152404a181a8731223240337808b0350a61c450a2408c28861143011c00400148410e6f050214084229606a24c588c00094e0606a14c258380ac298713830148004aa030250a67010843828b03509608b0350862cc68cc38181ad8380a428893987010d2a0094e0606a14c489c5008e029082a0128950800e0212c58002108e1d4598d1501091606a14c21c06611458cc0408461c1828108470ca181ad806234c90204aa141c042a01286712a10002042581a873122a021cb809429871994a8025900cc38c838086402504001484b080010212c58002108e1d4598d1),
  (0x184ab9ad95abeb594a51cc4255f1ac89cc0d9e8add663caef9576a5a4f3a4211727c83b39a68bbe57e28592a879636a14e8788176000, 13, 0x21c1409c2284080810845000a4458a38094e0a04a11c0031641120235c09c3089526661b0336ca0198517820c02d4809c1029740014a6080cc2388b20a48660a05481ad00c0c4228831673295004aa850250c0d4388b330a85025080d439a80820502708a1150204e114002911660203309a484a88a081040a04e081480056204528d550001021000952035122a030270000c1604a10c34891196103242c094288630c0ac56a1378f1302108b0002406a14439920c0d410606a11423c1408c90204e001486b14a305e004890202108e1d4498b17421d027000ac34860870198510da4810250c10404066481027000a4358a51823d6600381010aa38094218951663464045808158c080cc24885142306081409c20865080d582a5009c208732221011204a1013800408432a062154302d16642e64c1028138410ca00159204094303500a81aa82c08c228911e6625402080d4902980cc2380056214609204094203500a81a845458128430da2cd4040060b0250861cc448ab36212402b6cd840a04e1043280057214182c094218711264a54360408c30004a12c40b60810c0332c0943188d501001806a58128731062aca884500cc01c06a08002b0822442409008c2980384810a60521d448840d201285318d040a04a0019867102d81a8c7808d803338094449514cf815860870198510da1140204214d308000a42382000cc229c0808902709200158804a2846a971901131c05a14c38c8000a425b60809d4020c08c208736800158204a71b00056701286112a3c42080c0d42984380a4e022409c00c04e124409c04a32c8884500cc02406a08002b08224423a0c0d4298074a0149c0661d448be14f815840621920310a62d42280408429ba480cdd02708901984d50a120c04210c33a404a2aca8b6980a64000408520350e224c228040842982480d5b00056b0002b4809c398a000cc228e12621050606a14c2240529011204e006027092205202519644422c0408c30350e6b011204e12d60c5008421869080b4602560b0102b0030138431022ccd884812012853101016b6056c062806a10403006a11451911),
  (0xe3cdffdf8d97d7ecf9ce0c37c30c29ba4afbae2adbad4a73a6ca65a5e9eb98a8638146ed64450b41a3291de15911c097000, 12, 0x84812a43809c29fe4c90e0270a611d0204e11435982c09c2120478188470ca19203170701884712660b0270890006480c42a86712698102b3c0c5c1c06214c52fe78104022409490204a11c448ab507018853501130406621d0204e124358a51821121c04e14c38841009c07e081920310a6202027380d432fefdf851e052e013b80c09ce2404e14449cc8020303508ef010a40622cc40a0522013860c21d0204e12de02910a2050270863848acc487010a405a90e02d08e2cc68bc78981084580c018853784810250c18502108a1d451860ce8102708219460004e12465846091e1c04611c308931621233a6c09d402b8c094408b18c281086540c42a8932428108608205027240a490005212c203318a3848a92042813845080d402a5410108470ea24c8882780d5e361408148477400148804e1ac628e1152011804870138550e22cc13c06af093e04e1016861100a452c00428138606a1940243809c2a8711e61020a04a11e000480d4288730d30c1604a10c3888d993090204e10432800521802406a14540251264adb3a700c420d6052f1c00380d428863126f011406a10eb02b70f011d6056f05020520018b206a20c598414085402b080c4500062c82100521043a8b3),
  (0xd0ac85b3aac7ac0aa7aa0a99a92a8ba84a7da76a6fa68a61a5aa53a4ca339f69dd9a081f70a59b4bc3a72c82c119a007000, 12, 0x20206218c0310a670202738481885510a1020206212440405a20203108e215b3a04a08202908e22c30804a10302309ac0004052701a86512244c51e056e0e0310a73032406214c33fe044818fe6df827efdfbf04fdfbf046d2019b60c08c50004612411204ee1b03500501a843000833006214c31c0621145aa814001285100301284b240b5b363808c22869103015b604a0833006210c202b11239d0084101820210aa1cc11204a48102508e1016a800301284b0809c44b000701a8450e664440204618208141019847043000270921ac628e122a00203560101098600b4218038101096380b42189514a4ccb8c00821d2604e12c3086066294336000ac208697871202d3809c3989114201a88140d423b6000ad4067498138450c220c67b610001a84b6c90e0250a618c68c0789893e05212df0a000ac24867780cc7290178f151c04a10c3989100085027080ad42406214c4022409c00250d2f0002b08f8202708a18e2a04e144398c322a605e280662030351048148a0410198490ce20002f0963949088780890270009434800562bc50205e101aa454084e0250e630cc8fe),
  (0xa289fd9ae95f8c88c18ba8b387686f8687ad6bc69157c53f53843542e41540e40738225b20c19919213112a0a509e007000, 12, 0x504817b60620840406211c61c04a14c60206a7012920409c25cc08d81a8510cc0188531010139c240ac2a885fdfbf00140cc10276c0d7f0a040000c04e12cf0404e12458a87009491c6009c2987115a0020404481292040942388b16220602b092454406080842ab010084288b314101abc062f1b3a04ae9b02508e22c20a68094288404e20c108052181a8c00094e0350e2f0108f37901e021480c439fe6d21800380d42287112611b02910d81a8472408c14c040a42a8c056d8138a5283f8902063f81360cc01885310101ab604e00e03509229400606a0980333809438b60009420014094289204094248a70030128c0009423840522acc084240c4303308701a84710d8148404e1032406214ce02712bf82040cc0188531809c902b16a082020621980310a620202738481585510bf8216066c02027040cc206066c013871240ac7afe),
  (0x1a1ecb1dfd2e2b55e9eeca4a3d31e28e4c70a377100819bd09de6d966acafa94ae91e4679d80d4a60e2738d504ea16002e811000e000, 13, 0x2287c08602b08219df025080b468be1408432a0621544992140843042448102709620502718001384b080cc5490524255411204e28128406a31503500a820210aa19459931793011bc4c200027092184428a4c09530a04a11d30310c90188551e6f022606211411204a48102508e1016841000138450d240452604a98502508e181ab00091802b0aa10302b789813960461a45690526274c502046182081409c20331808002908e1ac628e122a00203560101098480b4218048c015840c0ac26960462d46295332220203508d09029580aeb3405211c508c57820128a04e1b5e28046705022409c24a405a204e0251a244e03c08e8102708a001488b142f0e243809420873123f8112057fbf021400f02909601e02b08e2c5c0604e48e2404e14c388ad081011204a48102508e00148b11962030404215580804214459882408c40204611430410101982000a4258851423542306070138410e6245a460561822a06614436921008430410281392052481027000a43584066394809352420102708a101a80541010aa38094218951664c4228066b120330a21040405a1142027993090204e10432800522ad60804ea015869860118510c0ac46885809c303500701a85114a64d4041028102908f3019800562946088080d400204200129c06a24c2043008c29843808c228ad50100182c094218731122ad08881008128470c11a08240a420330ce481027180a4358e52024d410805e101ab06070138410e6345a3e0561822a0661443692080d410004e101a881409c902924301482000a42388b1ca50490606ac001c06a114388808a8e0270861d44093300d9b382408168470c230158a51ab21830380842287112720238040ac2386100101ab038c0118450e62c40020622013840820102b0430158491022946a880448108436c181185560c0e02108a1c48980240cc402f0c0d410606ad050273c0cc90204e2060004e13c348ab20251443c0469019bc78c000a04e701a8651062cc679318010602578f1d0204e12c328891820020351090e02709a90158931a220202d044813840808138510ca2ac236180ac288404e224f080c0d421886008c288b3101016b62408128470d211b3a062114202711621b0604615583038094208711a608902b5020903508e0812b6),
  (0x1c3adbfe9631d37f8b4dd97ab234c4a28ce5a5931c687cc069f2aefe6f4b3e189eba653fa71115e7be34b97289b23d61968938272000, 13, 0xc38066da60330a29011e05ae8138404a22db000561247098542812862809420210ea2ccc0a9820108405a19e60251533010215409c0029980945597108283035981811841123300243008c2a87114081488080b4238005628499cc14c81acc0421c42322c0b4288631cb3050216c0ae608180ac2086724181a80540d42889398080031640d439885084830404215438cc00a8c0230aa1c4112080b4238005620489cc080ac100066c8b023640a4202112a34482cc70a920250a21ce60a0009560005212c40920c0d411406a115d00046901a8711e6286023140011845080c420606a9150230a2281023640d4328f3113016cc0c5012aa380942889315730426052001286124181a82280d4228004084e0350e23cc40c04620002308a1018840c0d4e2a046144402046c81a8651e63160606a14c02c0408ca0350e6215b0404a316120409c25cc04621580351a64446080008c228a04095c0350e611830113011841540ac428b31a231b2c04214410606a5012b018205027040a4102b9808c528c11e254c64c04a209023700d439b60809580330e20a60c042154412046e01ab09808580270e234c60004ad820250a2b03035600c412c0423040a04e48102709730118a11a2c81a925326b1f029180012b6062083035600c663206a1145990308c190250a6101488d18101886600c4a30102813920409c25881162314898020c8188553c1016924008c80250d2480029096384f280460001018084218675c0b4558004084002520089027000b4002b1024012b20623d4a4920409480350cc0198517808902709631002309278128c19500402704481384b248011800561a4708a200d42292042813845000cd90404215468aa3c2813845d0101085500401a822409cc02d802013800561a480251c24c451e04e00199e040a4209e1409c00290ca419031142013822409c248405a0015ae04a3849a9204094003120f13027082089027000a4359004ac820210a24d450804e08158605a40620046104349004a3040a04e00198656410108551a2480023c09c2087304001984520c8188a1009c11204e124202d000ac80251c24d4832062284027080b411204e00602709222c80252021010005210420250809c30404210c023640a439b208084b0230ca44454808f090230a699d02974301484b7c1019a605619c729412def1b02778c011853122f20020c0d422b006224de244c09420a04a11c41bc040c4912180a427be04001484f0ce314859a1),
  (0x16beaf8d44a867342943c6ea16ef5a758b671a0abf057fa52128290447ea30117287c43aa008f666f830c965092243016988a824e000, 13, 0x80a200b5c3604ad0108637c0ac6982700d58002c0d422873162206031100018845201019862809570330e22010c05212c802d1024d4156062e012b870102020661443188514e302031707018853080b45a881808c40406a1441382408dc0270409440820cc018b204a18c4a8405a54c608042e1c0405a124398410e090204a10c349c06a2cc688c00095e03170d011aa062f014b65c0d5e0210cae0e0310964cc60004a1018e070095c6004a11e60404e4810250a220c330062c81284042254c9880408c00c06600128710810503304001484b10301584718218202160601185312211904380cc2687110a7d4238380cc28bc4ce81384b7009411e05a00158691c22840276ce014800573133a04e10128611063bdc24066d840006ac8302708622c508f178e0e0330a2f9d027080b42025700015849182284027044813bc04a1a4838046134804066e0e0330a201906c0a8188530ce20c5092b7980102b100a40025103a820237809433bc78001886540c590250ea28c69bc980cc4022409c2480056e01284700a4208080942386315a505e400c0bc11406a114418a0448138004a1a521c00a8118470c222c899b1fc4811204e1242025fc782027041012853fc1892406214d9025fc09d0270c280027480d4398916409490204ae01984380cc28840c08ce02b7898f02d04e81384b0809450b8380cc2890970f01188080b4238404e813841080940029156e1203310f01a8411233026006af130254cf012847480d4588f3781013a04e1042025000a455920409420a0421012875146a0a025600cde0211233300a0409c20e004aa8188b32408502708a485021000c439840c5012840421c422a062284027240a411204e001486b080b4202520254cea88040015849c0d81884378095c4005200e0350a224df1204e2014e00470019bc0428139406a1cc42887813002108e18c01c06a14c688a1410128404f3011204e1066025000a455862809429955080120350a61003206a14c328d1),
  (0x1706ae6d13272330c8f2c6a20def12692af216f2abe49ea1c0e0250221a8e7853629412b88f84261c40d5869028613c09a8470152000, 13, 0x502046101a8a1009c1001809c2486b0809460800c5012840421d581804601916046154328b3262f0002b1531a02108f301288378e0e0330861c5e4c06609c035380cc38823c0b4902770094408580bc23bc04a22c809a978a0a025380cc388a3c0b5e02704e8138404a001488b1c331c4c05ae09023700811845380d4588f37020202d08e48208080b42387520d819845186101021080940029116e0202160201085312331a6006aa81887324101a8a1009c902b240015849080b440406a1148092100813845000cc31404a1010aa06625488ac5820138606a1cc10a05248602908e20560804f301584986011853640ac468f198216027000c590351262942080c10108550e33001c000ac2a84280a4268b114081480056184008080a42a840c0a426cc0860188430d641d19cc080ac400042c821c0661343a8b11ca2040204a11c404046104120527816b4080b423822409c60290d640420252a665440406a09c035600cc318b17cd300350a61150330a27860004ac81a8713c4815d610f81a8470d278128405a38490406a284027240a410005248602908e22c202d10101a8452820840270c10108552450202d0aa195800380d4228732a220602304e01a8537000204c008423875c010129c06a1cc71911101016823c0b42482180a425cc08095b0332411a0330aa10128811c609c035600cc4366419803308e18c4a8a122228f380461344000621190310aa21440478d0118410ea2812b86028128530e241c4022409c00c04e124202515ef053806a1449041009c2ab604a90188b320672c404700a42680700d4218a0809d02708210128897090198511d6d82027700cc4386809c2abe056205c30066145b042009420330d6e180330a221a1005a15410c052c8360600c42986710632c90b40820102508e0817b428094a02c00ac29b60c0bc21406a11da033681018820440188404ec833006211c39942811c035981013b810c0118510e6f880310961080257020f02908211f0210962cdc301008429871),
  (0x1be0da4ec3357ba38cd0e50312f7caba2d952b0f4189b7c96a28affa772b9c98e6bca524a5f103e7ac34b984892241e18d87401e2000, 13, 0x205023700d4398820201382052b81a8831622253604b281386b3cb812b600e0198470e200f031042013b806ad920295c094388d3200031404a14c3a84100ad74c5c09c208751633090606ae0129c24084288b39810303554b815851126008031080818b206a1cc5280081819ae062284027000b411204e001486b18241903308a5d564e600cc2a925008d6029080b56025143396021583011204e10435ac58a0118410d2b1f02318084328405ac01899304401286062e180310a6e080404e134902bac0a540237009470b800301384b7009602b082e012889001080250a2c01ab8000ac11204e40202709600168c04a32540c04a10ca09d39ce180310a6e011204e12eb28046124202d700947084700c5c045008c11204e12c40b87c08c60210cac003206a11c38973700015ce0461a562c0009c2482200943031600cd6022409c25d65008c24900809c00290da301292136ab02325008590250da20c63204612d6022409c20ac04ae080404e30128731160016842009590350e2625f2c7009c2082052f812ce1420138405a0815a80463012c805238593064094208712ea2940331809483804ad8802508e23d63804e3050804e104398c0563083604e104369070b013841000ac603314a10102b04401592080ac238c04a00168d3212481025084012820421cd900042154788a1009ed025040a6602bc008d9106c09c60250c223642c7009c102904094002b0c50128511c20021004a14580351420138205a0814a80460080404e124358c7c0a4229413a60063206208902720101384d1420138005a00158891809490975001800210a200a0004214432803008c10405a1040006458118550e22140006400158550e201903109a324e9bc7c49312052e81587510e40128d36c289023149813855040a533a180a42386b2021012bc05a0831404a1558033780845882140cdf0350898199205619c51006a115e3c1498138410c60820351409c32bc14f81a9204e185e0250448138404a301488f25628303528095803304f0178411a2fb04804628a03508a24c22a06614654a7c08c209204ef0402700301384b11228803508a086033000959040421545892080d490405a28402700301384b11228203508a40411204e181ab006628003328a81985510a1010931983030334c501984512af1e2604a99e02508e901a8b31a2c0202909a300025080c5e2604a99e02508e481025087302027082192031640943a973),
  (0x18b6c21df8af276c6ad8d4b289b3c898fc7e220f0167d1bb59c7ecbe625ad21562a1a482a0e0f1e6322a992f072a2ec0fd82c0056000, 13, 0x26080c501284b980b411c06a14469cc6851a03108a1ce61c05613584c0418a0250aa1c449b49930802108e0840204a104318062c8128751a648e61c056134f1e6c40128430c2781021080c400291162090230c0d4402046501a86500701a85122730102124181a9c062784027640d4328d39930102108a1020804211431404a15491e056701a82380d4228b12a600f0290018a0250a67811c06a14c388cb007818b4066d051e062081486711600e02b3c0a4369e3c08002909610403120094318c110481029086181a82280d42286280942680380d42895300202023104011845000b458800c0d4e2a0467013871100811b206a19489ba1009443a04a11c002d240010310921ac90a04218a0250aaa810230a234c02a05730f5204679902b08a24c54cc7410802708618490606aa818927408118a04e185903514a44c02a056f012a06210c03c062f190230a6214748420095d02124101a927808c90270d22090a04211c90351008c5292000a425ba05a6c492604218a0250aa0150350a234e63a042483035540c633206a114598024181a9208205027092184a03514a3cc22a0673153204e10c43a06a124508f17519d02575181284711618a02500a81985111a982380667018ba24001484b7808c4025142455d04046e890270a2e8802308ae81021240949027000a455ba000c432a062c812875166009000840128510c622c90606aa81892102813841640d4428f3980830352809550311262810d620101aca04e1cc449e047810845040019851081819ae06228002d69301184710241903308a08a02d5409c83206611400291967d4f02046001582052781029053011800521ac80250cb818b204a1cc9a8c20c81284d3cb816822409490204a11c448cb3c08100066144206066ba60210a241903308a3549180045016aa04e41903308a2d400291d7588062809429ae062254f0a05330119e04a206b02b0428f0804211cf100422813865300ac7480200ac80290da5021404a12c318a3c7840210aa19c1023040a414c0cc0188530c600148ab04401a8028b8188550e629432e062c81286d980840270c0d481406a11550804214479888cc819843),
  (0x107c83ac009ff6f76781bbf1deaeee74fb629a9ad10684b2e97feab447ea3010be7da3869b40d265c624f918874e34612a859022a000, 13, 0xfd3960310cc0188538d1990330aa197f30480ce30252ca810270a6a980330aa2c520004e0016aa0531812822809421fefdf8c2e8c0c633206a14c428420094102b8d1850210871814900009400270da3c630631181685164094002b16a34d20804e90188804a28e0315c09e303330623085c09d90330ea215718485816851300cd802b540a460c65c0ad92e06214c4282000c4206066402027142013c63008c298891a24230311028138005a185903318a75413205a001486b0408303504501a84512208002b0820010004a10422e04a08c0236409436820808d902d0d24440003008c26900809c24805c0c4228eb4a6e9c00380cc2886d00e019a6740ac22a06610c48ba4c0c5304100b421b8380c4298b5ac0ac0240408c258004481292040942389114181aa4062c81289325331c02380d42887398e012406a14439cc04192031640943a893140812826490138430d62866240561342020424830350a6e8802904501a85310ae8500056124102d74d8149004a18c02406a14c98cc74e120310aa1ce63a0008c20840c0d5d0a04e501a865980b5d2406a1448980700cc21004a0920350a6244004040c453a05a0800290962048020421148a820c501285500901a8511660050404628802308a00168b100181aa448a8118470e2281023640d432913680031c062c81287311a20002d0029a0256828128470448129204094238892224ac40606a701882640d4228b3),
  (0x1688a71d25276b37894cc65a16ef486feb5e187ec0257fa7192827f63ca9ad8bae4321c487d81c20da057825808e04001c80c800e000, 13, 0x8001590052001984040a4002b142013820520080404e124358004a3cca08a0840128530c50128004290c02364b8158451263d4a8cc68192031640943a893053050004a11602909a20410005212c7acc0c5012a4066001089516331c02380d428873049818cc1011c02909a18660257070198511ea08e02d0018118491160010606a14c14c05331902b09aa8118b1991990350a619450804f3012820562041180620031404a14d24c04b30138711ab30302309a09802d300a4358208181884280c422895980261804615438cc64c8b02309a1d442cc04c8128430c25cc13205b3011800c08c258a9ac41b00200a425ba05ad840231079b02d6c0a43789318e554b080ac0ac22b60018a025086a81989516200f0313c481025086192031640943a8d30840128a0c0d4a0250e2481025000d402406a144598a201013ac0521b411204e001486b000948088ac0adc2e0621353380070188530030138606220199404a2848192700b48100010108430ce22c64b674001588200b4238936c0a6b0a740cc802f0c2d8138a3ac00168456c0031404a10d503312a2c4038066e821004a7019875122e8e02d096108025709810851249810005212c41205611c5a82000d4228020e0148404e001288115a00e0350a27cc5560c08c25ae6409570270da289029001811900521ac00a580a4208004a192033289019845122435b120c0d402a06a14449b61028138005a0015881040018b206a1cc8280080815849241800210aa1c40045460118550e208802b200b493605a101586718254c80006608a0355c581185312208003508241664c0c0d550310e7326081409c2082062c81a8b318a1020606a14490006a01518046154388b30808410005aa813800c08c248ab053018cc645811b20521c44a82000cc00290c249421004a0831404a15439c605718802d0118402108619d82405a14e3005c0d4298652a3fa346600cc2abe4c0c6300200c4a2406214c4afefdf866006b1819fe),
  (0x78ef0fdbbb3f60e2388303ddcb636aac8d8aabf56296d267b6f51b9b6c616c1175ae45bab5967ac84f298093800, 11, 0x3f12040c7f021918002b0aa98102b08e1850005608802b092001280240812849000ac43921041920310a6c81288d00481aac0c0aeb03158101aa604ff962604bf841206b1813fe8c00903508a0821004a0031404a10c3984040ac802d11581a84510101280040ac2a8870008002b48b81285312a2a4e8fe140013a4066005027096c812fe140013801409c25a4066c812fe044818fefdf807e011810310c081685312a0890270428902d0009400271020814820c9018b204a18c49820c0cc0100009424801408c00290ce30485842009661000094268004e089025240812847000a45593114001886480c59025000844a8d3),
  (0xf14e6bca2c41b50a83a34a09a029b397692792091985e8457427297106c15ac49749039f3503492101c118417d176007000, 12, 0x101880200c422d60c0d410a04e501a865540c46984ac28102bac0a4802d1048149205610168872024cc85614001a8410e6216b021409c00330ca0060210009c318600084a56056115503316a645e3c4c08422b800701a8510e69840004a089027700b530251123040100809c2486b700010ae100842989114005027409d602d00094448a11a6e0e0330a29831c05a10c358c000d40027ac081384b04481480063589000400128510009c4ac6251813800561c560206b3018e0240d422fe8c0800a04e12480004e00903109222c53204a01203308e23411204e2960292100a0250a618c5002409410270d201d0004a11c359005a0120350a654401204a08002704281892480cc26900562880235900a0250861cc5360408e402b0009eb3604e0014865200b48a80480d429971140080290960031404a155703112628002d000ac11204a48102508e28189005632490a610b01484700cc81406611441a60408c102900e8002508e1ac01c06a14c8888ac0a462604ec016873009821004a28303504501a84512630d34674095d4604a11c458a6c08400250009c01c06a14c61971709810a600701a8530e299c260427018873fdf820804e08148204b3080004a13400205611c1000561247a8404181a853004920330aa1c48020620190350a6214a1fe),
  (0x14d8a05cf3a6ff2fa8fbc3d1da2d98626ae4958a9d4405a010f8e7c03af9d60e7e73838f9c60e226c231594a074e36a14e8938272000, 13, 0x4cd2503108698138a05298000040c42986710b31c1c06214c3acc7098e0350a21cd808080d413806a1444988980d41260409420b83890138510ea34c0080c0d4298498a8118530871902d0a61ac68cc0130402b0408c38b206a2cc629898181184d98904025109012847600b431404a0010215409c0025122324b998b081030359818118411233023004614401804612d30038c8168510ea00158a90808158a1009c002b0d2284f984100a41023980010855005191c05a14e6320461045a8d12ca99c0231040202709a0012803ce813841000944580380d428800409d02308e0015ac05a28464a1304281a80066e021004a701a8731220930020101384900094498ab14e01484d042816ba04e0012883302b011204e20148a04b28198ab00b014b84870138530e228c52606ad9b3a04611c002510299c1c06615438b800181184b0d29a302bac98148476c1014843540cc808052281880640d4298a570701884d4c0841006612c90405611c548a700a4268a000cc50804e089027092204618a000cc22a614181a82280d4228830820139806ab8e02f08a2cca8fe5878902b0a60012fe5808198004ac832406611c38fe3c0012fe04001280fc481025700cc01c066145338380cc28a63cb016827409c258004a2a4608a0808420004e8138410d69814a604a0052c05210436933709810a6380d429891140019822408c13a04e14c5000661146080200a42584000cc50004a29602f092204668a0018a0250861d452e04614c6882140a401204e14d6020009c802b1409490c05a14c648a000cc31404ab81987114600503304d8148551409490004a4032406214c8320661145a8a04001384b14094802d0400158004a0013889242282023140019c00c0b4a0255c0cc488a040d4902714b01484d00401484b14001580066194a0a0f),
  (0x1a54c7be2eafff744b56d6aa9073ec92cc94a473232915c60a0fef3473cb2c153e91e4169ab0b9a5c6297921872a24a0d085d81be000, 13, 0x400502909609c03508600100200a420270d621e027700a4368e10009450404e901a90380d4e02d0ca344f980700ccf1c06a14450005699c1c0661445027409c0025000a445b805a3049aa61040168205328002909641c0333802b0270821c45195548201382052e083c04e001286111ac1c0230960801005212dc02d4cd0802b24f01984710001984518238c126056e170330862441340664813a604a008029096e01682100a4034200ade02700094408b31c699c2e06610c38b4ac096b3404a11da02900195031640943988d095850804e4815861ac4813849004020270821b49990ac2000350821cc42920c00108557008a03508f581588500a81a853263f8112057fbf0214001385124901984d002813900009c2488b64094004044812920409423891000b4324062c81287326a9053205a11400604612c548a000cc502580b493a06611c448a000cc228e114181a8a280d422ae10084298d100181190052901688b00e1e0a0009c21a604a2045abc000b4402578701a853162f082606211450004b30002d08e089025240812847000a45592178201386000c425865cc815a67809cc0230d22c466a6780018847640d4429d3080015900408424801420138205218400250020108004a1b4000200a4202700094408ab3662021004a14c30004250002108a71902900b81484b3058128431a6554d884ac284027240aeb0291033016cc24d8138410c75840006a10432993ac08402708358128600084a00042115503316a4c663800701a8530e22011204e125302568f01380052001288b08b01484d2822090331009c1025980d453806a00e0350a62445022409c0025000a44584700a42686480cda0405a11c03206a114619a14d304020561016b6000ad602d0d298128e100e011a43809c2989132a0130014101485104001886480c590250ea2cc8182117310270009435889601014b25c10138410c62b41044808c28b6480a5804052136638066c03033080c4014066114508e32ea9850405e0831404a154388a304001a80380d4288a080b4100056e01686948101380640d4228832426cc14c06ae011c05614c3888080b4602910d01a84b14299c3606210d62604a98202d08e0a6023707180270a61c455cc1008420c05213664c040842486b981811862809443006a14c448d1),
  (0x197ccbae4e3263918c64ded2d8762ca79cea262330a8c4c60a2d312c877bf21cd6d445aba9093329023d298d8a6636a0d0866819a000, 13, 0xfc7920310809d9025fc400025001080250a2e0e0310a6e1302b4cd010a604a981580380d4288d30c08c01e0809d60290009440b8380cc288ed1028118804e08002970081084311600f0404eb0148004a205c1c06614476d668095a5604a11da02900192031640943988d14108025ac0cc50804e001286118600202100095602911a00324066c812875122a80060461243590000cc50804e0015906c09c268220101384b0d240003308a504106280942aae066281029000ac308f14ce130210a69844605212ce2405670138731a3f820606640a03308a2810298c0d400278c0945082142012c605a1d63029053050250ab181488700901a80640d422893363f962604a21b02bac181185340b1f0230c0b439c60d1920350a21cc54c04e101590046d8148a1981190350a6205027040a400358c0c450905040054605610802508624410606a9002406a11c3882000c590350ca44cd4800c08d902b0c9018b204a1a46682300c40062809400210e6280025000b4008080b4208a000b4228a704c016980521acb89f514082023040943582000ac24820c5012800421d44882000d40243008c2a87100019160461443a88514201382052080029096101680040ad90230ca485298a6c981984398e0e0330a2d821e046e8158670009413a0009423ac05a98158a92826d66385408b03508a1cc48ac3c08c202d58481584914298512056781080040ac22cc7070188530ea40c4022409c25a604b301484700a4268a240bc1025980c6638380cc288a0c081984b3c4815847280946093534612b126c08c9027142013800561a460d614001a8410cb301697304481386000842a8a2958158550ca0150350a64c660a980ac01e2408c288670c90188551e73001e0622a602b08e0811b206a34c728a981050804e14c202d040ac508d5981920330aa1c663205b3033006614420211063245040520811cc000a42a80645811b205200108951625145022409c2480144020270a61a445a604ae016a614d013887809c26881142013a62010138410de2ac00252c69813805e108025380d4398a31a29930420095c0330c6284027040a403c046001286b00701a853222284027040a580604612c53820b015bc04e184014046114698ed),
  (0x14129bdc9523571a48aac462072ea673db431782b4e56da9e940e92845aa2b91067ec3749990b764ca2198e2850e09a04981a00c2000, 13, 0x456062e001e042701887312b58602d7008c3488ac0ac210100d420b89c084288a3ac00e0350a211c029ac0adb1e240ac238004a20c70953ace001c06214cb02b10622d0804e14d92604211454a6998019a605e20002508e0190331158148414c0820354c09431881000118450cf58400046105c1c06215459d605698802d4c09491220101384b0e75812b805a32411206210402f700c43a8008701a9c04a1c4f022409c2480100c4228a126670c2000562018901008490606a08a03508a24c20804a20202508e00e0350a69970335c09c36931044812920409423ae05a00148cb2000198a1009c002b200b411204e401586920001984524248303504501a8455c0cc41205200158612235ab383c0b4208690c9815aa05a1c532a062e0002d087811920561a450864c0b401c06210ce1205212dc6005a0001c06a14431aa000a425a64c20138004a18f02d240ac348c128981a86240ac24aa10084298d14cc8f02109b58a02328701384d11298456056c81182700d59033100015a604a4841006612c348c110c8f0216409c36ce10095c031acc81a853100030350a218481d66448108430d73131e0460012a606a48148a170a818853115819a66c20168434c40118457070188531eb5815804c0d40560808eb10046114488a9100013a62408128430e2e0e0310aa3ce62620981a843ac0a440b85408e03508a1c449a6ac0ce62605a981386540c429a6640cc228f5ac0ac008000b415604b58102508e10802508632488880c0d55031000818b206a1946982101011860621d5c1404611411204a48102508e00302309232c90006a284027080b4100052481386b182015180461543882000d4032380b42a87114a84ff2c080d40025fc0160270c0c480404e14ca025),
  (0x1f64f8af803b63d50ddeed7361b9e6c9ee17af236c4acecf0a6571aa877bdb9d42d0e599abd94529a43f699b09b22fe160874022a000, 13, 0x64a2d02b08369902d08af9f36062e020204a13c308a95031902908a10a03150308021096c018b204a2cc7195564a2d02b08369902308ae19031504011841b4c81184504101aac500d4288c50a061004213c3189508c01a8511e6e0602b70481027640d4378897009403308e10a031640cc3a8c330ac94300636815861b4c81684551681286200a5902d0c609402d6c09562805e12c1285008128470e610a2804e14540c2008425b0062c8128b322a60dc280448138804a1015889142a0602508701a851126b14022409c202b500cc448a118b014845141019a82809520330ea2c490a1009c209204a3015840524940350a2a0602508a81a851126a14280408424865083015a806231410046105803164094599150400148c0c10168530ce18002160601185312201902080b420b218001384b0d258118f520b5850a6808c2386108001580140015b404e41e02709a284698004a4ab0a200cc202700094408ab580b474920c0d4a02508901aa404a1ceb0211e2bbde2e6409421822409490204a11d702d000a46590000cc50804e00159005a08902720101384b11240003308a504906000842a822800108550cab850215c4810849126544500940c42a8a940a4534042181aaa06249903508a30c89d61429a02308e186b04240ac20d604b5ab0a6809c20863580b660a04e11474ccac401086480cd91605a1144a8c31e293da5668095a5604a11c10004e00198611c600324062c81287311a00556040a425b468481484b0cad1a1205212c556040a42586518e10802508600169f10400138606aa81880040c590350ca3cc504046089025240812847000a455820c5012800421d44892000d4508080b423822409c00290d63040243008c2a87104001a806458118550e229509b47000e0330a21b450a4c09c21a60c08c25803c1013ac05200128817070198511da01c0334d582023ac4011845112a8198d14c20f0404e13430a604ae014b8380cc288420095c031ac00e0350a21cc50804e3030350a200a03508a304c182540c550270018118491564000331420138005641b02709a0880404e12c3490000cc22941041800210aa08a0004215432ae1008412e06a124499510008006280942987500e8e0250aa21d32066114338d12920933a04ae9302508e224002180942984300cd70250e230d902d31620104046081286b0400158490418002128001084512a2c410006a284027040ac100056124202d0009470803808002b092c816982c094218d51e284da380070198510da0095604e00f0404e104002511a355c2a06614453805a7013800c08c258a900e01aa610781684138a81185116759c1204210dc02d1120060004612530804208902524081284711232c30c04250602108aa811c06a114398f1),
  (0x1e20ea0f06b45b8bec1cdcdac1f4e8a43cf325b720e86abf91cc6d2a649af6163aa504f7a1b901a70a34b94e88fe3fa13c8620272000, 13, 0x584011204e10434a8056a0198c580a422ac200a541404ab81987516339f0a1009d40357c0a560804ea050230aa234899217c302029086195f2864c0138530ea24750204a284025102812847080a4a0316c1818ac1009c20a8040a427ea5040118410ca4acfa8c080c5803504a140a0461243a8810040102f0a2c01a8852e6a0202350094a03158201288580942394062a0158c950a05023082b04027500d434885809c1023180d442b00625cd60628094298404701a8530e2d0202d0923010606a14c002280d42986568d0402704094230380942987518610e03309a4c4f1e6c40128430c2781021080c400c04e781286919648303504501a8456000e03508a1c4798c10181a8533800e0336009c3684540cc218d10020802318001384d122201023640d43990504c016bc181018b20661ac44bc9cc013204a105802712628df3c0448138410c650168a974301100809c50250e622455ba20d8138a04a18441ba0808c602b640d448946008802d082c012b024101684160094439131450168c0561a56022409c24ce046a140405a11c39a8180cc22ac5030128530d6b013805e1080250a6c81a8a31a2a01040664012b206a245f4e046a019a8180cc228a108c818b87c08c2488d04c81ab8080b4602b0c2096031500d5c4e046105f1204e13c62806ae02023300d4388b350a0603570b8118511262951482640d5f0405a10564e7c0ac21a8066b010404611d43006615458ac2050188c5c0c42988314a726728062289023500d563e0463010865600c479ce500c4412046a01ab87c08c60210cac141c06a11c38933244840a04e104329218a0138510e739903150301284112aa0102150094602b501016a80523012893084012b206a3010891180012b49c0d429b45c0d4289e0478108450430198004a1c482c140a5b02b0c21970310a641903308a1030335c0c5a12180a42586120c81984520e85460004a0a70350a6e970350a27810c0560012863040a4f02056d8149e0430158490ce4012865c0c590250e655460004a7a70350a64810255c0d4389e04001484b08781886600c4298833c201092180a4258873c080031086001590640cc2a8c50cb818b204a1b412c0624031404a14d703112a78102b580a670233c094508c0009414e06a14e72e06b38802508224451e3c20108550ce081182052080029041080310cc01885310630148c7216088035005170310aa1cc52865c0c590250da300025081819ae06228602d04001484b1048602909619c7090640cc2299564a2d02b08369902d08ae1403350b010920409c2488558081184b5031902908a10a03150308021096c018b204a2cc71955),
  (0x1f1cefaf69baafc8ad7be15af37716b75d87aa7f526a8fd07260f216892c11a05af0670ab56991ab5446b9f08dc651a2388d7019a000, 13, 0x428002909a2961005213c35ac042816ba04eb1f02d08a28461ac8120169404ab819883162085029584813853d40b56026c0a42a8a04ba816ac20a019a406228802d04481384b50d940330861a450252025d560a0c0d4a0255c0cc48ac040d4902558401484b1428002909e1b480ac0c5012ae0661c492c080a42580580d4228a05a304a384241800210aa1c48021409ca00042154488a524b01a8a1009c20822409c259214a01a8430c0ac44900809c00290da3090c0461252035122080031640d440a04e48159205220403206a10c22a062b81386d30aecd62c0809d027000b56025100ac598c91c2e16021380cc38ac205018b2066e9d2c056124802d1023d6d0a640d4298ad40a560004a10c8002808c28b275a96027092401688116645560458c81886140cc20895146b1d100562816ac04a204a2e066144748c240d562c20181884358b120350a228902b580013a85809c2a8891824cd7065808c2486d141011ac056b1203128181984111a1963a200ac502d0c224d7480424015ae04a244949014501a85115a8159005ba8602b092b0002560d8902718094308951865cd60458a010b20621d441ac7c0890270a61856025280b4802b28b819851252405025808c2482580a542c04a10c459005a4456062809520310ea24c61206a288402809429863140890275809435822409d602b5008d6025152b00025480d439ae05a6c452c0448138415809444ac200a4258c05a30303500501a8455c28108511a62823806640a03308a20c50204ea01aac04aa0e0350a634442c5009c10290c6108025500cd42c04a70198711aaa16025096108025503012a81440168450cea14120409c20865500a45595114181ab0062b0002b640d4328d358103033500b431801809c50804e14c408c04001685520101384b15228300042181387508c1202b0aa1cc788014401985114081094062c840c05a28102908e204598c0009d70330840138491566d50284042010605212c200052135438052301286322a4cdc4c04230e03500701a84512634460406208303550c01a8511260020317c2050270820815b206a2cc728408f8198404219412804e30128630410118005a1030330962a4106000842ab00408581805a10c4982000cd900040cc20b22c0b4218b51ca746d32062d86023000c5b28052a81187318369902308ad9b081409c20b605a215b28062a152e04a1443ab654c8128430da44db2805aa01486b241030310aa3020204214483604ea08021086089027000b434b0062454b9801809c3023540b480204610138691d600110066144814062c819875240813b61808c80270da28460004eb819842009c248ab40ab090c05212d404500cc80c066115903116a30d432062c81286d),
  (0x1ed4f15f2f36e3918c1cde42c8b3da8e4c361e1ee1e63caf895e29dc3dc9b20ad64c218e8c5856a2ae13889a847e2380fd86b01e2000, 13, 0x10401682052a01590780ac80250c6e141c06a14439827008c00c04ee0128604620802f09232c106200a425b805a300025700d5703168f1803108ec9f02d08a284919b3180012b806ae170330a2201035680cc90270030303308e401488b7009443c04af0402508ee0148ad38210906000842a8712020102728001085512229493806a28402708248159210a01a8430c0ac44900809c00290dac1502b0a2201027000c59081409c21004e13490c04612460aa056454b2b33782012b806231703110089027280b46025112a0118c200a4259012a6f1c025180012b806a1cde0c05a2012bc380d4298b178a020a04e1143084500c4828240813841500a4488a51d6f040270c0d5803110f01380062c81a88522630404066145c045000148530c6284027100b410291020060606611c80404e12455860008581804614c48a3570501680200c590350e6205027100b46023040a4508c0009d703308401384915679410804e4812840c5012851000844a92700d450804e10411204e12c904500d4218605622420005213582a05614440204e0018b268e8138c0461016881540ac6a9255e6b1c2c380d42987110089027092e01284000a426b47809d602958094459410809c0290a6b1c1c066154388a10d01a847044813ac0521adc0251c220903304095603558e0e0330aa1c423805211803100c81a845106304d682580c5638380cc28875100815b6580ac24a8300c590250c610002909a484202700d428ac58701a8510e6201029580ac13204a19803308e20c70ac04b019b8380cc2a89108e01484600c403206a114418c12daa010297009dc28040a4238655010e0330a21d5408080d42882500d5203170a011b804e0812ac6419803108e18c4a9012e630203110a01aa8704811847600d4488d30010188c7008118515009d41c06215469905081031404a145800640d4228204224c75a80809c330300b429871040018b22c0b42a8852461031404a00108717028108804e001686056c0189c00c850210aa19c42953392e162c380d4288731008149e7409d60295809445900809c002958094469410428002909ab040820101384f0e6b0128a9196b163805a11dc0420094e0350e6244f06740cc239404a204b1a67008d6365008c20ac04ae16027092b0e0350a244c5022409d60250d2b04100809d60250e622455ac14e0148c3c0d400c06a114418c11dab200605e08a03508a108025380d4398e3223f86120448138490e600603308bf813004e01903308bf83120665012fe0419d03308e50129204095c0335870198515818119c056b0f0005a09d027096b0128a17070198512122050235809d027082b014ac04a2adc380008561c06a14c458b148e01484d),
  (0x1af6d02e52af6f77ab71d8a29df39296bc9da2e70ee819bcc1c7ee026b5b3517a2b70548a999452980474a070e0e52c21d8980152000, 13, 0x13000408424a604b8130213802402908481480056901188738094709112aa980027409c208694c0970260429001c066135702512235421004a282023200b42020521040001408c2286b2220050804e0814861000943243008d71604611448805c90138430c2454d9cc8008e0350a21cda4c900840204a11ce0351222cc61cc0c0ac26cc902840270832150230a32242e04614432cc0c0ac26953053244c0560800250862045a82000c644c0c60189604a18c46cc0c60b0250a218c302d156554c99000084f023c084228606a24c11080d0139004a18484c04240128630448139004a001488b2ea0170350a6744f4898401284b0c608002b09320f0606a11c02e06a14459903d58158413c0018b206a1ccf020460800330a24030335c0c4f022409c00292009445cc0c0cc80250c6404bad6201819ae0621d60200467812861ac0ac04805628f0253c28128471420139004a184c02b0c0b494823c0848401009c102b0400158499808c609004a4564005cb8102108e1d4488b3004000210c0cd70a1009c20ae04ab816ae0448138415c0940029156544daa4e00b640005212c0240408c24800410118204a1ccc4806614465a6e18019a494a81984b200813800561a460915481011a405a6012a04aa8402042114338005234c7580084012860669010895163312021c54012a40c0d429891001120230a731202109660c0404211d5040408c22a4056181a8b322330c480661466629409640330e20a602042154c020426013c8480864025900ac498f1006018a4000b551805a12552404a181a8711e61810004a0013800522040060860198430c58118604e194668f10411c0310aad9b383ce8158410ce30128a358701a85122608002d580adb3805e10c548404481386000842a8a2800108550ca3c4904540c426ac5060188551800b0350a21946192580d450804a20502508e204302b000b562a06a144a4a73501161e04e4811a406a24c5880080c461e0622813a80408c25b206a34c828458284025102812847040ac508405a3cc2045008c23840c0cc258404301a8430ca0016929081800210aac1202d0a601916046c81480042254529511008118a1009c2988581080250a21cc47ac0428803309648202b08e2a5c025700b5c0a6809c43c04e1344086300cc28b22c0ac2292346ab1c2c380c4298804e813ac04a1ad6029700b460935),
  (0x107c7e0bab1c06ca6634b1897debc458daa594faa4051ca83940e9dc4aba2b902e7ec3989a20bbe5242348e286be2800eb85480c2000, 13, 0x818011804810802d040ac10005612400271409470915262020031c090188551408198206a4813c004a0002404614c02e052114558a200bc2698100101880200c422d60428139205619432a0621546980140815d6052209029240ac338c124101a85100085027200d438885ac281086540c402e4809c2186116a3cdf000522812aa0660063a0660800290c90188535c0945a82000add031981819805c0cc50210e2f85025200ae5031600cc54c07cb81a851809011ba056f9d02709228762a057b1d06066901887581b052e06a147f48240ac0027803000255c0d438c0809013851240ac40acc1001085580e8108a200b4002b480cd702516a3c5f06086019ae04a1c44aa64808dd02b7c0a440ec0040118454c4860290970010606a1143182080d4802500c0118531622830350028602b09218421004ac000216009c398b1010019c05c0d428c0040a401204e12e00006a1146080800ce02e06a14560a04001384b8009640004e124688e1c02811204e1260025000ac508a200b4002b00901a853162281027001080250a21d6440380d428a600e81384b00094102914244f656380d428804d0010606a124318938009b033ac09c30c004a108025380cc3a911810010270920a01204210c35ec089019ae04a1c44aec80081884380097604480cd70250e22540042009428c0980013822409490204a11c458c10c0010a45c094288952e73040606af13025380d4388b3),
  (0x11e48afc4d22130847f6bbf1c5ede06c8b3a18c6bcc5beaa7911a79c33a96e890247a21590487623aa1b68d9862e2b6106850007a000, 13, 0x49814cc640cc2ac004001484b6808c40ec000966031113360330ab01b4c056080031640d4398a3040015849982010cc0408400290d698002b640010855126615084809c2286b98198303808c238a1009c12a04e124002515640498955049814cc640cc2a8a04001484b684815a606619d31606211480bc0c0cc10c052181186b989a402b65b01084312701b002c0d4298718008002b0920a80252c0b4318c105301a88100813845c54012860661d468806c0cf15004b0019871100815d0c409c21881998a802510181a8531233010219809660a04220138005730128a94c0015b26400138410ea2cc2040408c22880521820a05208002909620138606602603308a4049acc0810c0332c094318950010e0330aa1ac2003800158550e62243043070128530c610148ad4622844006611c10290c79d027000a400251022ad326089019ae04a18c4a8b14d201584200943033480c44a8274081a847100b600254c0050804e901a8735c094518cb2c301b3a000cc238004a98148a14c21b02d38901385312a2c53042009430330eb024025480d43888044813c004a1a5302b00281286380c550004a11c498c32c3f8902052a81380380cc22963009c106480c429807070188530cbf962a06200e03308bf813a480cc2380380cc22920409400310c98e0350a21cd3003c09d027096184448004b000021389013851126983240629813a04e12d30294c09450804e90199c04a20c90975010018e0480c42a822408c13a04e14c802d8009404000b812a404e18c448ab2c321b0005212c5025),
  (0x1da2e19ed53653a26cb5e1a2ea762ca1fcbd247317e885c261fbaefe745b501976b28548a5a8fae69e2c490b06e22920eb8620206000, 13, 0x5040808108450d2102000421143584140cd90310819b02998101484b12610a02909a4011a406229902b08a584ea880c08d9100809c2094052c8128ad64089027003013849102c8128cb1418109c0622831404a145224640a42686300c4218a6458118550ca18202d04001484b10264c00606600e02b104810250862021004a10ce03312a3a498b64c0ae4363ce8158470c218128a3142019c006a1b443604600e2404e154398b10448138a04b31b0a053581592100a4238004a3047ad61408432a06201202308225469801478129e14094238605a2ac00614181a8450e61262405614c22a06609703508a20c789691410202046114348614080029096202029000cc338004a3848acc089019855080120350a619e604600cc01606a114418a90c1121604a14c31840522b50882000cc21004a18198754d20129c06a1c45022409d30250d29815bc14d013a406a1cc01c06a11461961801813a04e10435c004b02602109330e0353890138411222300234d202485408c248675c0b410005212ce02522a4c410005a92e5204e201286b1138011e04cf0118804a08802d092c0158c14d80e0310aa08802d4c0ac11206af01580380d4228a32029b01c06215443406608802d0aa4813a604a99e2a0667012863116506b000840128510d2d032a0621543980140844027240aeb1204e12490406a1440080409c80350e2216b08042195031007150270861845a8f3c0f1302508299e0005620129c06625458800840128517898128004481284b0c221e1204212de26063201086518e18e267809cc0230d67012805c0a4302b0da4449aa939902602d150011204e1060025116901a8d122603008000cc2087580901a8a080d413a240d42386900301380480cc2488b80b8158452c26c44001420138205218400251661080250808148410c70188531aa002003009c28865c0a4228a31961970605660b0250862445692980d450804e089027097581292000adb0270009444921ac201086540c401c5409c2186116a3cd3064c08902700094348a1009c21b47809c002900094459411410169c4809c298913eb002022409c0025000a4478ab4c29a027000943092100bc10250c0d4499034c2820350090e0250aa1cc518d19098102b6c0012800561a450a6141016a43809429895163001260561260340c0cc208604a20c43604608002348701285512634444c06b0090805608129c06a245334300d6c0250c620499a6981921c04e14439895153011c8480c530204a90e0250aa20469800020128606a18138939800302b09a49203504b81a84510610e0405a14c34951),
  (0x13a697ecbda49b2228e0c53a04ef00734b8219e6c265d9a95931283e3ca9a00c626062ae9510a5643a1fe8e2855629211886681be000, 13, 0x83206631d0005a155e0c04e12c54a052401a865202e9d0c140ac0025780c6d0c0424a302708ac81a8b32476a30004e155e3a0536920350a601703108af19033b4006031096f0003108a28453c140b480250ea2810290800188c04e3001004611c328cb2022860004a0810869640d459bc1408c8025140cc50205200502909618a02d0809c50251264045042009429b206a28108b1004031404a14d703112ae963c0464012869102b0f02511381a85300b81a851144011204e104349e04a0015900808480250c60050200094248610c7018b204a1d4798c000948062809429ae062255d1200301384b0d2f0119e04a30543c3c094f3c04a11d70c042154689e101011822409c00c04e124458c12009440606a91802b0a2201023002010851640d4529330c9018b204a1b45040c0cd7031140800290961090c05212c338c120c8198452eab190c9809c20b204a1124c042155802711640d6022409c63606a14c40ac04a5016840561190350a2525802080d424ba180a5f02b040015ba05219d90331ca2800c04a30002508e22c604084810277c481384b10a28590331ea424a24062c81386d092812b00058198470d2d880005211413a066301384480cc2abe180013820521ad903314a486035545812ba740060272409435895080b42126c08490250e2e810006211d903512640c13605648002b08e0881206211490405611d73004e14d6022409490204a11c002b152b060004a1443984780c42027640cc41be740c464a0809c24ba062b980270a611602d640cdd2c06631e0a052144358405a30420c04228a0a042154398c00095712080b450290c2254688a180012820421a4232066112033140814b206630002709629470935),
  (0x12ce95ac8c24532228c5c461fe2e3a6c8b4316f2aac549aa314e6a2450ea8592fe8e83ce9900a324a62108ba04a218406d830807a000, 13, 0x804062209029080d46027201819b0062701388bfdf800a000adc027041015a404e1a46890640cc22c83988119c5c08c2289190a01484b103090204e11411204e401287519230158a081819ae9800148416009c4890640cc229152460840c0009420804a144418c05a08902524081284718282031200943188921675450606a085027280d432b0602090204e12c3088516254dd0c780c440606a5012b006224c6126809c22861246f011204e20148617809442806ac0188731028138c1848102708219444840c0cce031140814841202010b20661948abc1800602709218432406214c808062c81986525630203108181a9404ac018893743011ba680a5d0205611c428c1044815fe24081a8c041819855242019845fdf850004e005027096481482480d428e0640cc22822409490204a11d4029080c442806ac01887318004000461043288080d440210e22030351008119406a1958300021902308e481027096284628f13263050606a14c53005a302023600cc35b004e34400a04e30168c0564011801409c6120409c2086b640d469965782863e06a124602b0848148a06a281029140d4338c52833816ac64b020232809430895162e963c046b0802308a22403206a14c03c0625181204214439bc00c8198430d22803c2009590330ea0ab027015810270aa19450929640b5e000010118490c200802308ac8198ebb408203594094348a0030138557840128491572863206a14c5001809c25927808c24ca2408139005618c42921b400602709649b03578901984b180013ae05619474927c0b5e32067688023580c5636080d424865182b9e3a062c019867),
  (0x160aaf8d762a833e498bca0246308c797baf1bded345d0ad9152e9ca463a1e10be7ec3c59d38e4669e2cd8e284ea1f009a808000e000, 13, 0x230204e426027044813be000ac23e080b42986716a48503508b3862c14d8178450e2205e2406a3013a04e145f0405a154602b7809461405af01590000d450250c6324d09f304e813bc0564012847d28138005b29f0270962d480a06a1148982000b463c066e920330aa21c80a5c0c4298650830203109630503508af060255808413a04e1014841409d60290d629f0005200a02909a1801005213c202711640499ba0409c5033140ac428a6408c28ab51800128a2030108530e2405033640c45001430198471409445901409426822409c8025280cc802b152604faba0808dd3e04ef81486b7cc81a853740816be05641b0200301384b0d240128a1740813b206a1cc91907cc81a8531428602d040a5f02b04e813843200947a90114f9d021280cc3a8a040a5f02b7c281029040ac32a406a2cc88be041015be04a1c5f3206a14c602000d422861246f9903309a30002b74281384558001029140d432a82809421004ac019b0000a580270d6344818c25681292080a425ca05a2c4a3006214c93a0008c29ba04a20404c240ac202d0e24a502b08a518124809c22871126e8002d249060290aa18c508c20101385594001384bb4101ada200ac6031983015b6080d424885180890270aa29e0290972812b608e818847600cc64a6c09c228c04481385508301384b9400189006a194510580815b60535863a06212c338c1200948a8a940c450c0620012b206a20c698a0030128c000942388d180012920808c288890448129204094238a180c4248c140a420310c64ac50a0448602308e1c40025152089025240812847116c850210aa64c50c0009410210d22800c04a30002508e10118ab1400158a04a501689364281085132ae820237440118457c0ac12806ac01887320192031640943988040a463604600602709240128ab1c2284027040a5f0c080c433006214df100525180310a600108a524652c31404ac01886d201018fe),
  (0x1bceccce0aad2f54ca75cfea637260911c79a1a304c7e3ba39acecbe640b1115ceae053fa6390f28063ae98489d646618488182de000, 13, 0x40a0662010805a12430880c20108550820109c06a1cc68881409c414062124a02d3890138a5c0c42489324a108025101818a4066005100809c2986910220a031480cc3295531611612140d42186040ac202d193013801809c258805a2a480ac0408c50350ca74c40606bb0a02908ac019ac04234703804ae3002508e20158c0009421841008428840c0d5c025100844023c0e012b8c0094239c06a70159204094e0350c64c4e988102010006210c328870818a0250a228108848c81284348080029082901288b481040290821b4a99d5684860310aa4810006215432ac380cdc2c05ab1d0204a10d6043c09421873196b1c02100701a85312262401c056e0004480c4299e380c4228a30009d02708200129c0662acb4b874081280080d4f0250e6b0e0330a238d61c066b01486d580890270920012827409d6029000940380429960004e81384100094458a91a2e000404600f02308a235c1c06a144e02b226a130271809401e380c42984600c4238b558184027480d4202d12600f1c06214c32b8780cde3a0461019bc0408c228ab70085c3c5808de00046114459e0c0ac4027389013855166545c0404620f027409c208693c094f1c066144759e00b0139e05278128813c7120270a61c486b870e810255800128510870188531aa38c21c062135e001809c269004a016027780b4802570e0f3804214421c06214cf005809cf0293c094409e380cc288ed32a20f027409c208693c094f1c066144759c102830210a670e2404e12c38ba580a4004200945033640c431206650128611ea40d9329808590250ce2356321930138416409570004212c61ac04481394066426027096b0128c128b8198512522801406719d0270a222c032066135610140016820531815c67409c219004a385903326a2800a040a6302b0408c408004a281029000b6302b8c12302508e18c789b51401d0210009438b206a2cc506046ca6021640943680040840025640d44480001050c04214c31889002819845640c485801809c80250042602709a40503508a2cd60c1408188490c6e812ba580a56047409450330d222d90317c0015800c501784d0d2e9f02308e28129013ea2800c04a30002508e22c902918109100561145033640c490a04a1047a903640b5d0c04ed80100564016cc04e254598a200a42282740ac602714e8178496c302029096281982000ac01405a18102f096224608c0409c50330cac992404e10438a15),
  (0x1f88f42f53396bc0cd3ce66b2077dcb5ad5f29a7376927c6e2266fe87a8b981b92d2065faea96269b64479c80b1a4c017b8a58296000, 13, 0x1020102308a2000330a38170313d312033086089027000a435ae3c0a4229012aa204020461154035100019a80808d4025100015849380cc6a911500815a804a90e02d08620148c1149818900c0cd7031948011a605240128811ea9840606a14d31204698102308a1120335c09c3a8f100208022409c209004a22c5100808480250c64000c04e4012861116424da8a1408118450c0d4e30056004021380d4328b126620902924001484b2008109204e80802509228e02805200e0350a224c42040481027200a43288116a01700042154388820089027082401288900402021200943188b502010a448081084948094e2404e12c689131010302d200800290821ac80250cb818853104012902430148412009445865c0c42990742a31600046114208042145612046b0148a5008c208c5808118510ca18e0310aa54c304380cc2886d1430159e06279a1204a181a9204094e0350e230c798c00200023082194406100842a8733c1864c04e114309e2418148204a901a883380ac699510c10e0330a21b440405618202b0009431840c0d440210e620208042154e2405618202b04095203510634c98a438094e2404a11d530052c150250c0cc388ad4c98904046b8128711122831606215439880008c40c00094248606622c50404628b0350a670148a0408d70350ca4443001809cb0335c094488ad10a01a80380a49040476019aa04eb8128ab1e221402100a420a804a2545040460015ae04a0040212c58002108e1d459931103014880c0d4299e2408cf0204611570351622850004611450606a14c50a0408c22ae100842a8b1101819885c09441606a14c48860c18e02d0a2194206300c4298604a181002c0cc2a86510e40c40606670302d0a222da2c04ab1a02508ed014862809401c06614446ba14a018822409c208830c5012a40808520250e62b56040c0c5d1204ec018873205018a4066194819c05a525606280952109809c20a404a24c61ac0448138805a402027096b0128c10c5012ae0661c4a4ac70b0138510448138410808dc2c7009c28920409c2090046314006380c590250ea24c40628094269c06200158a9102813800808c00250d60050351008402d09210138a04a28450004212c99880c0d4e033140814841105040210aa701988526221408042155404540cc21a804b81a8430caa0e03309a7015931101011801809c25800c20108550e22060004e12ca080421445288143015851480d440404e0800c04e124358a1100811801008428a406a294e9cc58981286380c590250ea2cde3c180ac10005630138805a22460bc10481027092281a88114af031404a10c31404a12561c06a14c78a0100a5010280cc2286b407019c8500a4212180a425867142e0e03314481027180013849116284729d1),
  (0x1bf2d65e8d33cb93cbf8ddfadab5aea3acf7a6fb2208a0bfd9f06ec8745b66989eb70551a5a8f8a6682e8926082638e14584280e6000, 13, 0x270c0cf814ce05a1d4602b14338412052201a84040a440350ce3047288180cd9080421544888240ae5462409e00250c200158a900c81a853803010ce6100108530e3c001880095027083001288b16a34c4400620015869084012c00622015604e1260025000ac2000624012863202200020420012869647200270821d479b205a9890299c4012b0640ac29883640b44120530130250864815887c9812ce05618d903316a108025800c6004200942182000ac602780094448e1110060314c0810845112c81a8d3640b6708046401288066201080661240080521040250a622c2140521349088084012853640d44021162293031210019ae0632a70234c0a480251023d54404c09534004a11d7035162420031102820230920890270030138491164012901810011406a10c32c004e71802b0020109c06a19458953101030335c0c420805a2013822409c00c04e124458e120c81984532a30f0353c3015822409db0333c094202b280b4649013d30602719301384d10094508c33cc840210aa1c530c2410f025086c819895152c816c0080b5b1e04a10c2001809c259204a224412052c8118733c9814a6640d42988081200c0463010005611c348a51823d4440180c530204211444b206a34c4040808108450d2102000421143584100cd903110d814cc080a4258804a401184280a440270da484ca8a0c08d9100809c2094052c8128ad64089027003013849102c8128cb1018a0250a27030230418002b09218590404260b02508623499801009c6025182010860661d4e0310cc01884d1818198c24081284318108025086c0198951e24ac4404c0943033044812920409423880522848a880030128c000942388b4d0012c04c0942388d0840128436000e03508a70148933e2e840c0560012ba0809c83a05211448c82409490204a14431c062154699a30c006025180012847380cc588cd4c99f04046f8802308a24455880c0d550310e698406100842a8734c2090290961820350c4030290aa19451862409420aa38a8102108619c499d14d8011a674bab3404e10434ae04a2d468cc10181abc3c094f3c04a11ce0351623cd3080408c00310cb8170313c089027096112033086b812a62818138430d2484ba8c10301484b0009450606a14c40210c00602518001284711a7014a40562020350c28158451420138204a901a8932067c5408042a022a06610d4025c0d421865380a478e000b81a8517559e0230927812881),
  (0x1b98d53e6dafb765aa90d34a733272908c5a20ef04c7dabba1b82d1861caf616eeb4c55aa51915e6e62e8953098e34616089c82ba000, 13, 0x144050210c0cd204480cc23ae04ab811204e0060270922057025196544da8a0c0cc3060008c2286b481920290961811606a11421806618128671864c450404600602709600308042154388a18001384b28201085114a2840c056144e0351010168a0520800c04e124358c11408118010084289c06a294f99e2408129e06a18cf0a05330602710094318a13c0800291809c40251022ac406100842a882820108550ca91802b0a644450a0408c50004614442840c50128511008451c04670100052104e0251167020a0521043693336a28e0354820119c0521ac412000c42988241080250861a490005212c4033640c444c05a48a02d092201292000a4258e13ea78002b007811204e104802b3c094a02d1aa3a4f109809c40250c220cf00056c840210aa24402a8008c25c05008d902d0d30204c04e40128638c0a633206a7207004611c308b3811814800400128410c700a0290a70000480094e0330ea20e31c05a1247880800aec0290090148200601884e0094a0310e628ca02d1d66120804e52602128094368a95400a2a280942387512600148cb100010210009434880010118004a201988b640c44149820128470da00602338094358e136a989029181040333c09590312420128411aa38d902d4cc8002108699902d08a9811204e40129406640158a128b81985121299f02b4c50e2a04e1443a89320c819c06c08cf0257c0a440be3cc81a8532100f025082f814a6045181c04a14431895167006040621980310a620e0000409c21887c001384b640d4498e57cc81984d7cf820237c09438be0409d90350e63a4826640d429c06808e00273c09652605212c60c0044812920409423c02408138410c63ae00c100ac00250c7002023800943888803011808009c22891640d4699a90030128c0009423b20662b440c4c09410210d22130c04a31302508e10118ab28004025096201389364201085132a99602558981284780701884990001484b6901203109b3060272009601c06214c55ac04481292040942388b58300025086b0202314308023096194589091020102708b001ab0182890204e12c328811624cd61e0630183024d813841380a4428b11a6b0f025800cc23006614462c0008c22845810802708618448c08008a03508619583014481027096184428b12663040606a14c61c06ac016b005610c03308634440004e30168c0564011880009c6120409c2086b640d469965),
  (0xb1321a09ada3ae59093800, 11, 0x285020461154035502140290808c428052114e0331aa3c4502000a400250d6205d605c0c5c360464012be0562046ac8182140211809c4025086019ae04a1d471911900adc0c0009640330c6202023380cce0251224246001809c50250c0d449a4600b461204094218c084012843600cc4a8e92622810ba5880118493c095c00380d4288735881c0255c0c43a9e14089027092006027001011849116384f1005611540804270102138094e027480ac588f3)]

def cert_boundsFor (i tok : Nat) :=
  hintedBounds cert_bound_chunks (hintWordAt cert_hint_pages i) tok
def cert_ref := symDagRef cert_mask cert_goal 2599 3 cert_syms cert_trace cert_links
def cert_check : Nat → Bool := fun i => forceW (hintWordAt cert_hint_pages i) (fun code =>
  checkNodeViaF cert_mask cert_goal (hintedBounds cert_bound_chunks code) cert_trace cert_ref i)
set_option maxHeartbeats 0 in
theorem cert_roots : dagCheckRootsF cert_mask cert_goal cert_bounds
    (cert_ref 0) cert_stock 12 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row0 : treeBlockF 0 16 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row16 : treeBlockF 16 32 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row32 : treeBlockF 32 48 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row48 : treeBlockF 48 64 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row64 : treeBlockF 64 80 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row80 : treeBlockF 80 96 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row96 : treeBlockF 96 112 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row112 : treeBlockF 112 128 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row128 : treeBlockF 128 144 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row144 : treeBlockF 144 160 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row160 : treeBlockF 160 176 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row176 : treeBlockF 176 192 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row192 : treeBlockF 192 208 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row208 : treeBlockF 208 224 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row224 : treeBlockF 224 240 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row240 : treeBlockF 240 256 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row256 : treeBlockF 256 272 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row272 : treeBlockF 272 288 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row288 : treeBlockF 288 304 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row304 : treeBlockF 304 320 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row320 : treeBlockF 320 336 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row336 : treeBlockF 336 352 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row352 : treeBlockF 352 368 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row368 : treeBlockF 368 384 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row384 : treeBlockF 384 400 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row400 : treeBlockF 400 416 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row416 : treeBlockF 416 432 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row432 : treeBlockF 432 448 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row448 : treeBlockF 448 464 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row464 : treeBlockF 464 480 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row480 : treeBlockF 480 496 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row496 : treeBlockF 496 512 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row512 : treeBlockF 512 528 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row528 : treeBlockF 528 544 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row544 : treeBlockF 544 560 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row560 : treeBlockF 560 576 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row576 : treeBlockF 576 592 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row592 : treeBlockF 592 608 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row608 : treeBlockF 608 624 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row624 : treeBlockF 624 640 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row640 : treeBlockF 640 656 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row656 : treeBlockF 656 672 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row672 : treeBlockF 672 688 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row688 : treeBlockF 688 704 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row704 : treeBlockF 704 720 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row720 : treeBlockF 720 736 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row736 : treeBlockF 736 752 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row752 : treeBlockF 752 768 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row768 : treeBlockF 768 784 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row784 : treeBlockF 784 800 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row800 : treeBlockF 800 816 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row816 : treeBlockF 816 832 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row832 : treeBlockF 832 848 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row848 : treeBlockF 848 864 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row864 : treeBlockF 864 880 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row880 : treeBlockF 880 896 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row896 : treeBlockF 896 912 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row912 : treeBlockF 912 928 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row928 : treeBlockF 928 944 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row944 : treeBlockF 944 960 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row960 : treeBlockF 960 976 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row976 : treeBlockF 976 992 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row992 : treeBlockF 992 1008 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1008 : treeBlockF 1008 1024 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1024 : treeBlockF 1024 1040 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1040 : treeBlockF 1040 1056 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1056 : treeBlockF 1056 1072 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1072 : treeBlockF 1072 1088 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1088 : treeBlockF 1088 1104 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1104 : treeBlockF 1104 1120 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1120 : treeBlockF 1120 1136 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1136 : treeBlockF 1136 1152 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1152 : treeBlockF 1152 1168 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1168 : treeBlockF 1168 1184 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1184 : treeBlockF 1184 1200 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1200 : treeBlockF 1200 1216 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1216 : treeBlockF 1216 1232 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1232 : treeBlockF 1232 1248 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1248 : treeBlockF 1248 1264 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1264 : treeBlockF 1264 1280 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1280 : treeBlockF 1280 1296 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1296 : treeBlockF 1296 1312 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1312 : treeBlockF 1312 1328 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1328 : treeBlockF 1328 1344 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1344 : treeBlockF 1344 1360 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1360 : treeBlockF 1360 1376 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1376 : treeBlockF 1376 1392 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1392 : treeBlockF 1392 1408 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1408 : treeBlockF 1408 1424 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1424 : treeBlockF 1424 1440 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1440 : treeBlockF 1440 1456 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1456 : treeBlockF 1456 1472 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1472 : treeBlockF 1472 1488 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1488 : treeBlockF 1488 1504 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1504 : treeBlockF 1504 1520 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1520 : treeBlockF 1520 1536 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1536 : treeBlockF 1536 1552 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1552 : treeBlockF 1552 1568 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1568 : treeBlockF 1568 1584 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1584 : treeBlockF 1584 1600 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1600 : treeBlockF 1600 1616 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1616 : treeBlockF 1616 1632 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1632 : treeBlockF 1632 1648 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1648 : treeBlockF 1648 1664 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1664 : treeBlockF 1664 1680 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1680 : treeBlockF 1680 1696 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1696 : treeBlockF 1696 1712 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1712 : treeBlockF 1712 1728 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1728 : treeBlockF 1728 1744 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1744 : treeBlockF 1744 1760 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1760 : treeBlockF 1760 1776 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1776 : treeBlockF 1776 1792 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1792 : treeBlockF 1792 1808 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1808 : treeBlockF 1808 1824 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1824 : treeBlockF 1824 1840 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1840 : treeBlockF 1840 1856 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1856 : treeBlockF 1856 1872 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1872 : treeBlockF 1872 1888 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1888 : treeBlockF 1888 1904 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1904 : treeBlockF 1904 1920 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1920 : treeBlockF 1920 1936 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1936 : treeBlockF 1936 1952 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1952 : treeBlockF 1952 1968 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1968 : treeBlockF 1968 1984 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1984 : treeBlockF 1984 2000 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2000 : treeBlockF 2000 2016 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2016 : treeBlockF 2016 2032 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2032 : treeBlockF 2032 2048 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2048 : treeBlockF 2048 2064 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2064 : treeBlockF 2064 2080 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2080 : treeBlockF 2080 2096 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2096 : treeBlockF 2096 2112 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2112 : treeBlockF 2112 2128 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2128 : treeBlockF 2128 2144 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2144 : treeBlockF 2144 2160 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2160 : treeBlockF 2160 2176 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2176 : treeBlockF 2176 2192 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2192 : treeBlockF 2192 2208 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2208 : treeBlockF 2208 2224 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2224 : treeBlockF 2224 2240 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2240 : treeBlockF 2240 2256 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2256 : treeBlockF 2256 2272 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2272 : treeBlockF 2272 2288 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2288 : treeBlockF 2288 2304 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2304 : treeBlockF 2304 2320 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2320 : treeBlockF 2320 2336 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2336 : treeBlockF 2336 2352 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2352 : treeBlockF 2352 2368 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2368 : treeBlockF 2368 2384 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2384 : treeBlockF 2384 2400 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2400 : treeBlockF 2400 2416 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2416 : treeBlockF 2416 2432 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2432 : treeBlockF 2432 2448 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2448 : treeBlockF 2448 2464 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2464 : treeBlockF 2464 2480 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2480 : treeBlockF 2480 2496 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2496 : treeBlockF 2496 2512 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2512 : treeBlockF 2512 2528 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2528 : treeBlockF 2528 2544 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2544 : treeBlockF 2544 2560 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2560 : treeBlockF 2560 2576 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2576 : treeBlockF 2576 2592 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2592 : treeBlockF 2592 2599 cert_check = true := by decide +kernel
theorem cert_nodes : ∀ i, 0 ≤ i → i < 2599 → cert_check i = true :=
  joinBlockSpecs
    (joinBlockSpecs
      (joinBlockSpecs
        (joinBlockSpecs
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (blockSpec row0)
                (blockSpec row16))
              (joinBlockSpecs
                (blockSpec row32)
                (joinBlockSpecs
                  (blockSpec row48)
                  (blockSpec row64))))
            (joinBlockSpecs
              (joinBlockSpecs
                (blockSpec row80)
                (blockSpec row96))
              (joinBlockSpecs
                (blockSpec row112)
                (joinBlockSpecs
                  (blockSpec row128)
                  (blockSpec row144)))))
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (blockSpec row160)
                (blockSpec row176))
              (joinBlockSpecs
                (blockSpec row192)
                (joinBlockSpecs
                  (blockSpec row208)
                  (blockSpec row224))))
            (joinBlockSpecs
              (joinBlockSpecs
                (blockSpec row240)
                (blockSpec row256))
              (joinBlockSpecs
                (blockSpec row272)
                (joinBlockSpecs
                  (blockSpec row288)
                  (blockSpec row304))))))
        (joinBlockSpecs
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (blockSpec row320)
                (blockSpec row336))
              (joinBlockSpecs
                (blockSpec row352)
                (joinBlockSpecs
                  (blockSpec row368)
                  (blockSpec row384))))
            (joinBlockSpecs
              (joinBlockSpecs
                (blockSpec row400)
                (blockSpec row416))
              (joinBlockSpecs
                (blockSpec row432)
                (joinBlockSpecs
                  (blockSpec row448)
                  (blockSpec row464)))))
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (blockSpec row480)
                (blockSpec row496))
              (joinBlockSpecs
                (blockSpec row512)
                (joinBlockSpecs
                  (blockSpec row528)
                  (blockSpec row544))))
            (joinBlockSpecs
              (joinBlockSpecs
                (blockSpec row560)
                (blockSpec row576))
              (joinBlockSpecs
                (blockSpec row592)
                (joinBlockSpecs
                  (blockSpec row608)
                  (blockSpec row624)))))))
      (joinBlockSpecs
        (joinBlockSpecs
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (blockSpec row640)
                (blockSpec row656))
              (joinBlockSpecs
                (blockSpec row672)
                (joinBlockSpecs
                  (blockSpec row688)
                  (blockSpec row704))))
            (joinBlockSpecs
              (joinBlockSpecs
                (blockSpec row720)
                (blockSpec row736))
              (joinBlockSpecs
                (blockSpec row752)
                (joinBlockSpecs
                  (blockSpec row768)
                  (blockSpec row784)))))
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (blockSpec row800)
                (blockSpec row816))
              (joinBlockSpecs
                (blockSpec row832)
                (joinBlockSpecs
                  (blockSpec row848)
                  (blockSpec row864))))
            (joinBlockSpecs
              (joinBlockSpecs
                (blockSpec row880)
                (blockSpec row896))
              (joinBlockSpecs
                (blockSpec row912)
                (joinBlockSpecs
                  (blockSpec row928)
                  (blockSpec row944))))))
        (joinBlockSpecs
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (blockSpec row960)
                (blockSpec row976))
              (joinBlockSpecs
                (blockSpec row992)
                (joinBlockSpecs
                  (blockSpec row1008)
                  (blockSpec row1024))))
            (joinBlockSpecs
              (joinBlockSpecs
                (blockSpec row1040)
                (blockSpec row1056))
              (joinBlockSpecs
                (blockSpec row1072)
                (joinBlockSpecs
                  (blockSpec row1088)
                  (blockSpec row1104)))))
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (blockSpec row1120)
                (blockSpec row1136))
              (joinBlockSpecs
                (blockSpec row1152)
                (joinBlockSpecs
                  (blockSpec row1168)
                  (blockSpec row1184))))
            (joinBlockSpecs
              (joinBlockSpecs
                (blockSpec row1200)
                (joinBlockSpecs
                  (blockSpec row1216)
                  (blockSpec row1232)))
              (joinBlockSpecs
                (blockSpec row1248)
                (joinBlockSpecs
                  (blockSpec row1264)
                  (blockSpec row1280))))))))
    (joinBlockSpecs
      (joinBlockSpecs
        (joinBlockSpecs
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (blockSpec row1296)
                (blockSpec row1312))
              (joinBlockSpecs
                (blockSpec row1328)
                (joinBlockSpecs
                  (blockSpec row1344)
                  (blockSpec row1360))))
            (joinBlockSpecs
              (joinBlockSpecs
                (blockSpec row1376)
                (blockSpec row1392))
              (joinBlockSpecs
                (blockSpec row1408)
                (joinBlockSpecs
                  (blockSpec row1424)
                  (blockSpec row1440)))))
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (blockSpec row1456)
                (blockSpec row1472))
              (joinBlockSpecs
                (blockSpec row1488)
                (joinBlockSpecs
                  (blockSpec row1504)
                  (blockSpec row1520))))
            (joinBlockSpecs
              (joinBlockSpecs
                (blockSpec row1536)
                (blockSpec row1552))
              (joinBlockSpecs
                (blockSpec row1568)
                (joinBlockSpecs
                  (blockSpec row1584)
                  (blockSpec row1600))))))
        (joinBlockSpecs
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (blockSpec row1616)
                (blockSpec row1632))
              (joinBlockSpecs
                (blockSpec row1648)
                (joinBlockSpecs
                  (blockSpec row1664)
                  (blockSpec row1680))))
            (joinBlockSpecs
              (joinBlockSpecs
                (blockSpec row1696)
                (blockSpec row1712))
              (joinBlockSpecs
                (blockSpec row1728)
                (joinBlockSpecs
                  (blockSpec row1744)
                  (blockSpec row1760)))))
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (blockSpec row1776)
                (blockSpec row1792))
              (joinBlockSpecs
                (blockSpec row1808)
                (joinBlockSpecs
                  (blockSpec row1824)
                  (blockSpec row1840))))
            (joinBlockSpecs
              (joinBlockSpecs
                (blockSpec row1856)
                (joinBlockSpecs
                  (blockSpec row1872)
                  (blockSpec row1888)))
              (joinBlockSpecs
                (blockSpec row1904)
                (joinBlockSpecs
                  (blockSpec row1920)
                  (blockSpec row1936)))))))
      (joinBlockSpecs
        (joinBlockSpecs
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (blockSpec row1952)
                (blockSpec row1968))
              (joinBlockSpecs
                (blockSpec row1984)
                (joinBlockSpecs
                  (blockSpec row2000)
                  (blockSpec row2016))))
            (joinBlockSpecs
              (joinBlockSpecs
                (blockSpec row2032)
                (blockSpec row2048))
              (joinBlockSpecs
                (blockSpec row2064)
                (joinBlockSpecs
                  (blockSpec row2080)
                  (blockSpec row2096)))))
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (blockSpec row2112)
                (blockSpec row2128))
              (joinBlockSpecs
                (blockSpec row2144)
                (joinBlockSpecs
                  (blockSpec row2160)
                  (blockSpec row2176))))
            (joinBlockSpecs
              (joinBlockSpecs
                (blockSpec row2192)
                (blockSpec row2208))
              (joinBlockSpecs
                (blockSpec row2224)
                (joinBlockSpecs
                  (blockSpec row2240)
                  (blockSpec row2256))))))
        (joinBlockSpecs
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (blockSpec row2272)
                (blockSpec row2288))
              (joinBlockSpecs
                (blockSpec row2304)
                (joinBlockSpecs
                  (blockSpec row2320)
                  (blockSpec row2336))))
            (joinBlockSpecs
              (joinBlockSpecs
                (blockSpec row2352)
                (blockSpec row2368))
              (joinBlockSpecs
                (blockSpec row2384)
                (joinBlockSpecs
                  (blockSpec row2400)
                  (blockSpec row2416)))))
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (blockSpec row2432)
                (blockSpec row2448))
              (joinBlockSpecs
                (blockSpec row2464)
                (joinBlockSpecs
                  (blockSpec row2480)
                  (blockSpec row2496))))
            (joinBlockSpecs
              (joinBlockSpecs
                (blockSpec row2512)
                (joinBlockSpecs
                  (blockSpec row2528)
                  (blockSpec row2544)))
              (joinBlockSpecs
                (blockSpec row2560)
                (joinBlockSpecs
                  (blockSpec row2576)
                  (blockSpec row2592))))))))
theorem cert_lower (hknown : KnownBin cert_bounds) : LowerBin cert_mask cert_stock cert_goal 13 :=
  lowerDagRefF (boundsFor := cert_boundsFor) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hknown cert_sub cert_goals
    (fun _ _ _ hb => hintedBounds_mem hb)
    (symDagRef_sound (by decide +kernel) cert_syms cert_trace cert_links)
    cert_roots
    (by intro i hlo hhi
        have h := cert_nodes i hlo hhi
        simp only [cert_check, forceW_eq] at h
        change checkNodeViaF cert_mask cert_goal
          (hintedBounds cert_bound_chunks (hintWordAt cert_hint_pages i)) cert_trace cert_ref i = true
        exact h)

theorem knownNil : KnownBin [] := by
  intro b hb
  exact (List.not_mem_nil hb).elim

theorem knownCons {b : Nat × List Nat × Nat × Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hb : LowerBin b.1 b.2.1 b.2.2.2 b.2.2.1) (hs : KnownBin bounds) : KnownBin (b :: bounds) := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | hm
  · exact hb
  · exact hs a hm

def r0_mask : Nat := 0xcccc0000cccc
def r0_stock : List Nat := [0xcccc, 0xcc000000cc, 0xc0c00000c0c, 0x444400004444]
def r0_goal : Nat := 0x4440000444c
def r0_bounds : List (Nat × List Nat × Nat × Nat) := []
theorem r0_sub : ∀ b ∈ r0_bounds, r0_mask &&& b.1 = b.1 := by
  have hall : r0_bounds.all (fun b => Nat.beq (Nat.land r0_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r0_goals : ∀ b ∈ r0_bounds, canon b.1 r0_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r0_bounds.all (fun b => Nat.beq (canonF b.1 r0_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r0_forest : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def r0_links : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
def r0_trace := dagTraceF r0_mask r0_stock 5 r0_forest
def r0_check : Nat → Bool := dagCheckNodeF r0_mask r0_goal r0_bounds 64 r0_trace r0_links
set_option maxHeartbeats 0 in
theorem r0_roots : dagCheckRootsF r0_mask r0_goal r0_bounds
    (dagRefF 64 r0_trace r0_links 0) r0_stock 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r0_b0 : treeBlockF 0 12 r0_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r0_b12 : treeBlockF 12 24 r0_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r0_b24 : treeBlockF 24 36 r0_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r0_b36 : treeBlockF 36 48 r0_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r0_b48 : treeBlockF 48 60 r0_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r0_b60 : treeBlockF 60 64 r0_check = true := by decide +kernel
theorem r0_nodes : ∀ i, 0 ≤ i → i < 64 → r0_check i = true :=
  joinBlockSpecs
    (joinBlockSpecs
      (blockSpec r0_b0)
      (joinBlockSpecs
        (blockSpec r0_b12)
        (blockSpec r0_b24)))
    (joinBlockSpecs
      (blockSpec r0_b36)
      (joinBlockSpecs
        (blockSpec r0_b48)
        (blockSpec r0_b60)))
theorem r0_known : KnownBin r0_bounds :=
  knownNil
theorem r0_lower : LowerBin r0_mask r0_stock r0_goal 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r0_known r0_sub r0_goals r0_roots r0_nodes

def r1_mask : Nat := 0xf0f00000f0f0
def r1_stock : List Nat := [0xf0f0, 0xf0000000f0, 0x303000003030, 0x505000005050]
def r1_goal : Nat := 0x105000005070
def r1_rows : Fin 64 → Fin 64 := decodeRows 0xbee000b6c0009e60009640000000000000000000000000003ce00034c0001c6000144000
set_option maxHeartbeats 0 in
theorem r1_lower : LowerBin r1_mask r1_stock r1_goal 6 := by
  apply lowerBin_of_rowPull r1_rows (stock' := r0_stock)
  · have hall : r1_stock.all (fun w => availBF r0_stock
        (rowCanon r1_rows r1_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r1_rows r1_mask = r0_mask := by decide +kernel
    have hg : rowCanon r1_rows r1_mask r1_goal = r0_goal := by decide +kernel
    rw [hm, hg]
    exact r0_lower

def r2_mask : Nat := 0xff00ff00
def r2_stock : List Nat := [0xff00, 0xf000f00, 0x33003300, 0x55005500]
def r2_goal : Nat := 0x1005700
def r2_bounds : List (Nat × List Nat × Nat × Nat) := []
theorem r2_sub : ∀ b ∈ r2_bounds, r2_mask &&& b.1 = b.1 := by
  have hall : r2_bounds.all (fun b => Nat.beq (Nat.land r2_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r2_goals : ∀ b ∈ r2_bounds, canon b.1 r2_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r2_bounds.all (fun b => Nat.beq (canonF b.1 r2_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r2_forest : Nat → Nat × Nat := unpackForestF 0x32eb2c32932232132000f 3 9
def r2_links : Nat → Nat → Option Nat := unpackLinksF 0xe78c70c30341 0xb2cb2cd2e92972252132000f 6 3 9 3 4
def r2_trace := dagTraceF r2_mask r2_stock 4 r2_forest
def r2_check : Nat → Bool := dagCheckNodeF r2_mask r2_goal r2_bounds 7 r2_trace r2_links
set_option maxHeartbeats 0 in
theorem r2_roots : dagCheckRootsF r2_mask r2_goal r2_bounds
    (dagRefF 7 r2_trace r2_links 0) r2_stock 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r2_b0 : treeBlockF 0 7 r2_check = true := by decide +kernel
theorem r2_nodes : ∀ i, 0 ≤ i → i < 7 → r2_check i = true :=
  blockSpec r2_b0
theorem r2_known : KnownBin r2_bounds :=
  knownNil
theorem r2_lower : LowerBin r2_mask r2_stock r2_goal 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r2_known r2_sub r2_goals r2_roots r2_nodes

def r3_mask : Nat := 0xaaaa0000aaaa
def r3_stock : List Nat := [0xaaaa, 0xaa000000aa, 0xa0a00000a0a, 0x222200002222]
def r3_goal : Nat := 0x2020000022a
def r3_rows : Fin 64 → Fin 64 := decodeRows 0xbed9e53cd1c5000000000000ae98e12c90c1000000000000
set_option maxHeartbeats 0 in
theorem r3_lower : LowerBin r3_mask r3_stock r3_goal 5 := by
  apply lowerBin_of_rowPull r3_rows (stock' := r2_stock)
  · have hall : r3_stock.all (fun w => availBF r2_stock
        (rowCanon r3_rows r3_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r3_rows r3_mask = r2_mask := by decide +kernel
    have hg : rowCanon r3_rows r3_mask r3_goal = r2_goal := by decide +kernel
    rw [hm, hg]
    exact r2_lower

def r4_mask : Nat := 0xffff
def r4_stock : List Nat := [0xff, 0xf0f, 0x3333, 0x5555]
def r4_goal : Nat := 0x577f
def r4_bounds : List (Nat × List Nat × Nat × Nat) := []
theorem r4_sub : ∀ b ∈ r4_bounds, r4_mask &&& b.1 = b.1 := by
  have hall : r4_bounds.all (fun b => Nat.beq (Nat.land r4_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r4_goals : ∀ b ∈ r4_bounds, canon b.1 r4_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r4_bounds.all (fun b => Nat.beq (canonF b.1 r4_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r4_forest : Nat → Nat × Nat := unpackForestF 0xc7463629d6490a6c43a492209086c00f 3 10
def r4_links : Nat → Nat → Option Nat := unpackLinksF 0x1a2d58b12a44890e8701 0x192430919242090d24209263a88d9d3a54d903a10d800f 7 3 10 4 4
def r4_trace := dagTraceF r4_mask r4_stock 4 r4_forest
def r4_check : Nat → Bool := dagCheckNodeF r4_mask r4_goal r4_bounds 10 r4_trace r4_links
set_option maxHeartbeats 0 in
theorem r4_roots : dagCheckRootsF r4_mask r4_goal r4_bounds
    (dagRefF 10 r4_trace r4_links 0) r4_stock 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r4_b0 : treeBlockF 0 10 r4_check = true := by decide +kernel
theorem r4_nodes : ∀ i, 0 ≤ i → i < 10 → r4_check i = true :=
  blockSpec r4_b0
theorem r4_known : KnownBin r4_bounds :=
  knownNil
theorem r4_lower : LowerBin r4_mask r4_stock r4_goal 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r4_known r4_sub r4_goals r4_roots r4_nodes

def r5_mask : Nat := 0xff000000ff
def r5_stock : List Nat := [0xff, 0xf0000000f, 0x3300000033, 0x5500000055]
def r5_goal : Nat := 0x570000007f
def r5_rows : Fin 64 → Fin 64 := decodeRows 0x2082082082082082082082082082082082082082082082082082082082082082082082089e69648e28601c61440c2040
set_option maxHeartbeats 0 in
theorem r5_lower : LowerBin r5_mask r5_stock r5_goal 5 := by
  apply lowerBin_of_rowPull r5_rows (stock' := r4_stock)
  · have hall : r5_stock.all (fun w => availBF r4_stock
        (rowCanon r5_rows r5_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r5_rows r5_mask = r4_mask := by decide +kernel
    have hg : rowCanon r5_rows r5_mask r5_goal = r4_goal := by decide +kernel
    rw [hm, hg]
    exact r4_lower

def r6_mask : Nat := 0xcccccccc
def r6_stock : List Nat := [0xcccc, 0xcc00cc, 0xc0c0c0c, 0x44444444]
def r6_goal : Nat := 0x44444c
def r6_bounds : List (Nat × List Nat × Nat × Nat) := []
theorem r6_sub : ∀ b ∈ r6_bounds, r6_mask &&& b.1 = b.1 := by
  have hall : r6_bounds.all (fun b => Nat.beq (Nat.land r6_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r6_goals : ∀ b ∈ r6_bounds, canon b.1 r6_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r6_bounds.all (fun b => Nat.beq (canonF b.1 r6_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r6_forest : Nat → Nat × Nat := unpackForestF 0x63a84c203018d981814a452130b0429108400f 4 10
def r6_links : Nat → Nat → Option Nat := unpackLinksF 0xb162c4a910604072e0701 0x253080c181830b2a3a78d95294484829108400f 7 3 10 4 4
def r6_trace := dagTraceF r6_mask r6_stock 4 r6_forest
def r6_check : Nat → Bool := dagCheckNodeF r6_mask r6_goal r6_bounds 11 r6_trace r6_links
set_option maxHeartbeats 0 in
theorem r6_roots : dagCheckRootsF r6_mask r6_goal r6_bounds
    (dagRefF 11 r6_trace r6_links 0) r6_stock 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r6_b0 : treeBlockF 0 11 r6_check = true := by decide +kernel
theorem r6_nodes : ∀ i, 0 ≤ i → i < 11 → r6_check i = true :=
  blockSpec r6_b0
theorem r6_known : KnownBin r6_bounds :=
  knownNil
theorem r6_lower : LowerBin r6_mask r6_stock r6_goal 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r6_known r6_sub r6_goals r6_roots r6_nodes

def r7_mask : Nat := 0xff000000ff00
def r7_stock : List Nat := [0xff00, 0xf0000000f00, 0x330000003300, 0x550000005500]
def r7_goal : Nat := 0x170000005700
def r7_rows : Fin 64 → Fin 64 := decodeRows 0x209000a2900028b000aab00030d000b2d00038f000baf000
set_option maxHeartbeats 0 in
theorem r7_lower : LowerBin r7_mask r7_stock r7_goal 5 := by
  apply lowerBin_of_rowPull r7_rows (stock' := r6_stock)
  · have hall : r7_stock.all (fun w => availBF r6_stock
        (rowCanon r7_rows r7_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r7_rows r7_mask = r6_mask := by decide +kernel
    have hg : rowCanon r7_rows r7_mask r7_goal = r6_goal := by decide +kernel
    rw [hm, hg]
    exact r6_lower

def r8_mask : Nat := 0xffff00000000
def r8_stock : List Nat := [0xff00000000, 0xf0f00000000, 0x333300000000, 0x555500000000]
def r8_goal : Nat := 0x175700000000
def r8_rows : Fin 64 → Fin 64 := decodeRows 0x821000a290008a3000aab000925000b2d0009a7000baf000
set_option maxHeartbeats 0 in
theorem r8_lower : LowerBin r8_mask r8_stock r8_goal 5 := by
  apply lowerBin_of_rowPull r8_rows (stock' := r6_stock)
  · have hall : r8_stock.all (fun w => availBF r6_stock
        (rowCanon r8_rows r8_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r8_rows r8_mask = r6_mask := by decide +kernel
    have hg : rowCanon r8_rows r8_mask r8_goal = r6_goal := by decide +kernel
    rw [hm, hg]
    exact r6_lower

def r9_mask : Nat := 0xffff0000ffff
def r9_stock : List Nat := [0xffff, 0xff000000ff, 0xf0f00000f0f, 0x333300003333, 0x555500005555]
def r9_goal : Nat := 0x17570000577f
def r9_bounds : List (Nat × List Nat × Nat × Nat) := [(0xcccc0000cccc, [0xcccc, 0xcc000000cc, 0xc0c00000c0c, 0x444400004444], 6, 0x4440000444c), (0xf0f00000f0f0, [0xf0f0, 0xf0000000f0, 0x303000003030, 0x505000005050], 6, 0x105000005070), (0xaaaa0000aaaa, [0xaaaa, 0xaa000000aa, 0xa0a00000a0a, 0x222200002222], 5, 0x2020000022a), (0xff000000ff, [0xff, 0xf0000000f, 0x3300000033, 0x5500000055], 5, 0x570000007f), (0xff000000ff00, [0xff00, 0xf0000000f00, 0x330000003300, 0x550000005500], 5, 0x170000005700), (0xffff, [0xff, 0xf0f, 0x3333, 0x5555], 5, 0x577f), (0xffff00000000, [0xff00000000, 0xf0f00000000, 0x333300000000, 0x555500000000], 5, 0x175700000000)]
theorem r9_sub : ∀ b ∈ r9_bounds, r9_mask &&& b.1 = b.1 := by
  have hall : r9_bounds.all (fun b => Nat.beq (Nat.land r9_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r9_goals : ∀ b ∈ r9_bounds, canon b.1 r9_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r9_bounds.all (fun b => Nat.beq (canonF b.1 r9_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r9_forest : Nat → Nat × Nat := unpackForestRelative (unpackPagedWidths [
    (17, 0x10ad0655822940946191d088e832b4084a04160216b502e0854c9af821b306ae085cb9a3849141089595e1da50c958228808440caf02530128d193604221293c12a03a4704260a8dc1028113a049b024a982486a5d31269691424a0094420130c4f4108021350c210410010340814282b10d6816b8335615a508d1834ac12460423020d81026001f),
    (18, 0x2d30123a02148ca5604d600a542c57c094c2856c0b602455c19540453009341c54c094c1852c135002970494706d28125602118285a06d68125602158084ac609c085432d7c086c2ed5c085c2ad1c1236028d0925202918823a02170092a1a5581a5d02570092a121583b5a0cd582b4a08d181a56045280856020da401b029608b5f029807b57029406b47024d85a5a),
    (19, 0x22960251ef4238085c1068e06d2809a300a460c06c0c8ec151b8212f032560449c0491828340146e060b0051b80824ab08602150722f8136c010d83315c042a0ba5f010482a96c043609a57034a804910041207a53010481a92c09ae809500a2ac02d74202b0345a058ac08d580c9c80850010ac0211a341581358014a84f17c05b012c570148c46d680e2f0125a014ac3ed2815a682345),
    (19, 0x10b80a1780d2e0115c012a002148722b00b5c04ac806d70081c00834168a60ad2411a081a5e0248c02910412b01148012881a13c04a40295c04068060b0042600824060960297010238084c012a80210f751b80b5d0548a071600a2a00a540146fac13c21ab8085c0668e0a96c0da501346014ac020db342580b450e4ba0297031238146c018c0128dc08a380927062b80491c051b81950),
    (20, 0xb459324f0cb5f0c35d01c6c0106c008600a35700c5e0934d00a6c0834700a5e073450685f0116c008540505b0246c01b6c0116c0096002857011500085c00964008538624700a5416c5f00d6c15c5b00b5614c5a01a6c0106c0086012c570445e03a5e)] 6) 11
def r9_links : Nat → Nat → Option Nat := unpackLinksPaged (unpackPaged [
    0x28805084a00932726404b8897012c1248843ac860906320c03e1c7b08ec51d4239886e28da11b0236006c00d421a8034086230c4018042f845d10b8116842d005908b20158627204e009a1128625004a009021200240047088e011c023803f4064d0c80190031086200c40188031006200a500d3c01c8001,
    0x42028401013a02040027e8cfd01f813f007d84fb01f603ec07c0cf801ee13dc07b04f221e403c807900ef19de03bc07780ec19bce37806e84dd01b4336806c08d801b0034ca6980cf219e033826494c90192032026118c20184030806100c20184030805d9caf615e02b445604a91952029865300a221440,
    0x5e80b5416a02c865900b2016402bc65780af015e02bc05780af01554aaa05502aa01530a8ec51c0a30546028c0504aa081400a8004fc29f813d127a04f409e813a1a7404dc69b81360a6634cc0980d30026004c00980130025e14a4c8e351c0238046088c01151a2a0448688851102220428e84850902120,
    0x7fc4ff81ff03fe07ec8f9a1f303e417c80f901f203d487a80f501ea03d407a80f295e40bc807846f005dd1bba07740ee05db0bac57580e98dd303a417442daf1b5036056c00d801b0035846910d109a20340267c2cf819f033e066c8c6b98d031246240c30d86030c06088c1018202fe35fc0bf817a2af40,
    0x4da498d5300e5a34b4096812c86523ca4093c727824b24960910f2186420c8408fc71f823f047e08f831c1a38047008d851a0a16f42c0848908860d241a082c505820b0416080d101820114020] 15 6)
  (unpackPaged [
    0x1901b0100640b01500a0340f80503c1241801700c0540221100803414c490518261440585cb451709144f93613c4985a04413651028044148510500441368e04c14c158d28542561385784a1460981580684609015046044088110421500801103a0380e05203e04c0e80503813a0d84d81a046112d3c40b4711093c402470f08dc3493a0d04a818046090050291240a0090200140a89402814408810024a3d0828d42413d0804d41e0420701001a82a06806830b5d042d542eb4d0b2d143025d0409542e24d0b09142793609c4982683609809818014048d701435a040d580e34a030d180a2560209180714601811866c5f18b15c6635f188d5c5e34716497849a461248d85815e122518481360c84901605601211804036932d3e18b4793093e182476e88ddad14f66c52d7b14755c50d1b93b31e4dd1b12b31c49dac04f66812d7a04755810d1a83b31a0dd1a02b31809c9101f24006c6a01700804c0001f,
    0x3d8d60f4254138040f014c3b0d80e8154398530e41343805304c010370d40dbb483689704a010358d28d4256348118ce35a330958ca05645117d10457430d690434a3e0958f215f3b856cea15738854cde14b36051cd005a32012848012310150c006c278190980342f01709a0542e2918b6a442e08d8b62341bc090b22462b0558a405625a118ae05c2b24e8ac12a16817094836250098a615c2a2d749eb552a09749e2552924e8a412a280d689e356270d289a3462609589614a250158c2c5f2fb15cc235f2f8d5cba3472d0948b0a4a2c08e8aa156288158928462480d88e258110040420201f89a08a2601000407a2582189403c0101fa528829461f84e8821360e0080360101d49687e15a1f05587a14a1e05187405a0d00807112c1c00b07004a1d29287423a1c85686e02c23317c88c57230d7c88357210d1c8025a1da9287623a1b45686c05a0c8040460141104902e0641a0150552341504d040124,
    0x62049d84b4761091d822374c20e93002a65ad7592b47658975922476308dd8615c6005417e14b5f051d4193b3ae4dd4112b3ac49d2e83a4b80a8aa01a5e0171720545c2111700345780b15a0245d0d29723465c09193d129394494b901e5b08ed6a2374fe4ece99375a04bd6612b59049d621232dc0795e2375688dd763474e692ce3a474e48ece32372d44b96e8465821116e0365800d15c02c56009154054540db0cc9445381b1260644901114a054518090ad12c5081b13e2544f09113a02448e911220544d8091200364c8d75301504780d92c35d498d54ca8364801412845a499159243564884e51e0562cc0795245f53115d4825f51096d402574e094d3424b37e91d2e156322518b112e4a81591c046460d610a34840899116254420da1123604009510824a438918ce04a3f8d510a45e3f0d590825a418958db945358168560123f88e0fe34c408d35003453f08e8fa052350128cc03a15004852010,
    0x7e4141fab5c7e8971f815c7d85420245e7b117600b5e800979fd15e7d4549fc05e7d0149f035c7b9591e2c647b0d71e22647ac4e1e91347a80e1e8034790d25e2341780979de246770911d2048760521d61447401603a014748521c00447280503a038728131d015c73a111ce0347300b1c8024712d71c425c6f8101c004c6f85521445f84116e0c45a81115df245679914ddab56768959af15f69c56d8d1575dc54dd514f71c52dc31476f450dae05f69816d8c0575d814dd404f71812dc20476f010cbb01f2e806c8401717804db835d6c8d55b02363d44945c0126d1161b24546c2d51b02546dad15b62456b88dd4993b3ce4dd4912b3cc49c580123504d19e0346a0171a00541c84d1a234a680d199e25634a119aac576a8d5da634769096d7f25751692cefa475148ecef237342518d01361b04999c8466700d99034d660d15942564ca0e99425c628571841506411b18e4606205b18216062a91d8a147,
    0x20e25585a8d51793545a0d63cb55938d155393b4564dd5283b4520dcc301f30806c8c01719804e00b648dad51e02348ead5a00b46838d160aa355464e5508397ead724646c802d723a26c9145b2431609101b2420608f9179031254080960e5648ead723a26c7788d236b4e8d8979dc2344064d5011254020d5000258c01a21e0548c05b22e0546780d2200508a91b22836c6509b22616c8905821c0508805421e05c870590fa134928d7e4835d900d5df23558f0d36383478d0d15da2368cc57e2d15b88c55e1b1536ac52d931475364ed119373e44963205f8b016e2205786814daa04b64811d4c83b4420dcf80252fc07cbe01b22005c620138491a20e45485ad52162547c0d521256c809591e4c647909920e356808d56024587b91420ab6c8289b20916c81c5820806c818181fb1507e8141fe05c] 22 7) 5 11 6
def r9_trace := dagTraceF r9_mask r9_stock 8 r9_forest
set_option maxHeartbeats 0 in
def r9_sym0 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r9_sym1 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeaeab6ca689e68e29648607de75c6da6585d65544d24503ce2ca34c2481c60c2144040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeaeab6ca689e68e29648607de75c6da6585d65544d24503ce2ca34c2481c60c2144040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r9_sym2 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa683ce34c2ca2487de75c6da6585d65544d24509e69648e28601c61440c2040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa683ce34c2ca2487de75c6da6585d65544d24509e69648e28601c61440c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r9_sym3 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeaeab6ca683ce2ca34c2487de75c6da6585d65544d24509e68e29648601c60c2144040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeaeab6ca683ce2ca34c2487de75c6da6585d65544d24509e68e29648601c60c2144040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r9_syms : List (TableSymmetry r9_mask r9_goal) := [
  ⟨(⟨r9_sym0, by decide +kernel⟩, rowCanon r9_sym0 r9_mask), fun _ => rfl⟩,
  ⟨(⟨r9_sym1, by decide +kernel⟩, rowCanon r9_sym1 r9_mask), fun _ => rfl⟩,
  ⟨(⟨r9_sym2, by decide +kernel⟩, rowCanon r9_sym2 r9_mask), fun _ => rfl⟩,
  ⟨(⟨r9_sym3, by decide +kernel⟩, rowCanon r9_sym3 r9_mask), fun _ => rfl⟩]
def r9_profile : Nat → Nat := unpackPagedWidths [
    (7, 0xc007e4040091f1f842803f18f620a1c1030000080043e085020800640000078f8000080083010208080021cfe000190002a01037ff83),
    (7, 0x2e0013f06709bc180473f82700047b001017e00000737e136083427c8038f007e0003e000003f8010048840042fff01f020a01e403f),
    (7, 0xf1e3f81ce060e1fe030c2218006703df0effe03220058c06405601782050977276c07efc03f804010c00017ff80099d36100fd00040fc020),
    (7, 0x1000000083d8000000810e081030ebd7a103840008204041c2070800387f807e01c01ceff11cc3e000003fff81fe071010b840015f830b7),
    (7, 0xfffc3fb0200081001c087081f30003800800083080000737f0214007f1ec0810214081)] 6
def r9_boundsFor (i _ : Nat) := chooseBounds r9_bounds (r9_profile i)
def r9_ref := symDagRef r9_mask r9_goal 296 2 r9_syms r9_trace r9_links
def r9_check : Nat → Bool := fun i => checkNodeViaF r9_mask r9_goal (r9_boundsFor i) r9_trace r9_ref i
set_option maxHeartbeats 0 in
theorem r9_roots : dagCheckRootsF r9_mask r9_goal r9_bounds
    (r9_ref 0) r9_stock 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b0 : treeBlockF 0 12 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b12 : treeBlockF 12 24 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b24 : treeBlockF 24 36 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b36 : treeBlockF 36 48 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b48 : treeBlockF 48 60 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b60 : treeBlockF 60 72 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b72 : treeBlockF 72 84 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b84 : treeBlockF 84 96 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b96 : treeBlockF 96 108 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b108 : treeBlockF 108 120 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b120 : treeBlockF 120 132 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b132 : treeBlockF 132 144 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b144 : treeBlockF 144 156 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b156 : treeBlockF 156 168 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b168 : treeBlockF 168 180 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b180 : treeBlockF 180 192 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b192 : treeBlockF 192 204 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b204 : treeBlockF 204 216 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b216 : treeBlockF 216 228 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b228 : treeBlockF 228 240 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b240 : treeBlockF 240 252 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b252 : treeBlockF 252 264 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b264 : treeBlockF 264 276 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b276 : treeBlockF 276 288 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b288 : treeBlockF 288 296 r9_check = true := by decide +kernel
theorem r9_nodes : ∀ i, 0 ≤ i → i < 296 → r9_check i = true :=
  joinBlockSpecs
    (joinBlockSpecs
      (joinBlockSpecs
        (joinBlockSpecs
          (blockSpec r9_b0)
          (joinBlockSpecs
            (blockSpec r9_b12)
            (blockSpec r9_b24)))
        (joinBlockSpecs
          (blockSpec r9_b36)
          (joinBlockSpecs
            (blockSpec r9_b48)
            (blockSpec r9_b60))))
      (joinBlockSpecs
        (joinBlockSpecs
          (blockSpec r9_b72)
          (joinBlockSpecs
            (blockSpec r9_b84)
            (blockSpec r9_b96)))
        (joinBlockSpecs
          (blockSpec r9_b108)
          (joinBlockSpecs
            (blockSpec r9_b120)
            (blockSpec r9_b132)))))
    (joinBlockSpecs
      (joinBlockSpecs
        (joinBlockSpecs
          (blockSpec r9_b144)
          (joinBlockSpecs
            (blockSpec r9_b156)
            (blockSpec r9_b168)))
        (joinBlockSpecs
          (blockSpec r9_b180)
          (joinBlockSpecs
            (blockSpec r9_b192)
            (blockSpec r9_b204))))
      (joinBlockSpecs
        (joinBlockSpecs
          (blockSpec r9_b216)
          (joinBlockSpecs
            (blockSpec r9_b228)
            (blockSpec r9_b240)))
        (joinBlockSpecs
          (joinBlockSpecs
            (blockSpec r9_b252)
            (blockSpec r9_b264))
          (joinBlockSpecs
            (blockSpec r9_b276)
            (blockSpec r9_b288)))))
theorem r9_known : KnownBin r9_bounds :=
  knownCons r0_lower (
  knownCons r1_lower (
  knownCons r3_lower (
  knownCons r5_lower (
  knownCons r7_lower (
  knownCons r4_lower (
  knownCons r8_lower (
  knownNil)))))))
theorem r9_lower : LowerBin r9_mask r9_stock r9_goal 9 :=
  lowerDagRefF (boundsFor := r9_boundsFor) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) r9_known r9_sub r9_goals
    (fun i _ _ hb => chooseBounds_mem (r9_profile i) hb)
    (symDagRef_sound (by decide +kernel) r9_syms r9_trace r9_links)
    r9_roots r9_nodes

def r10_mask : Nat := 0xf0f0f0f0f0f0f0f0
def r10_stock : List Nat := [0xf0f0f0f0, 0xf0f00000f0f0, 0xf000f000f000f0, 0x3030303030303030, 0x5050505050505050]
def r10_goal : Nat := 0x10105000505070
def r10_rows : Fin 64 → Fin 64 := decodeRows 0x10530d51571d18738f59779f000000000000000000000000925b2dd35f3d9a7bafdb7fbf
set_option maxHeartbeats 0 in
theorem r10_lower : LowerBin r10_mask r10_stock r10_goal 9 := by
  apply lowerBin_of_rowPull r10_rows (stock' := r9_stock)
  · have hall : r10_stock.all (fun w => availBF r9_stock
        (rowCanon r10_rows r10_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r10_rows r10_mask = r9_mask := by decide +kernel
    have hg : rowCanon r10_rows r10_mask r10_goal = r9_goal := by decide +kernel
    rw [hm, hg]
    exact r9_lower

def r11_mask : Nat := 0xcccccccccccccccc
def r11_stock : List Nat := [0xcccccccc, 0xcccc0000cccc, 0xcc00cc00cc00cc, 0xc0c0c0c0c0c0c0c, 0x4444444444444444]
def r11_goal : Nat := 0x404440044444c
def r11_rows : Fin 64 → Fin 64 := decodeRows 0x8328b49369b18738f59779f0000000000000000000000008a3aabcb3ebb9a7bafdb7fbf
set_option maxHeartbeats 0 in
theorem r11_lower : LowerBin r11_mask r11_stock r11_goal 9 := by
  apply lowerBin_of_rowPull r11_rows (stock' := r9_stock)
  · have hall : r11_stock.all (fun w => availBF r9_stock
        (rowCanon r11_rows r11_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r11_rows r11_mask = r9_mask := by decide +kernel
    have hg : rowCanon r11_rows r11_mask r11_goal = r9_goal := by decide +kernel
    rw [hm, hg]
    exact r9_lower

def r12_mask : Nat := 0xff00ff00ff00ff
def r12_stock : List Nat := [0xff00ff, 0xff000000ff, 0xf000f000f000f, 0x33003300330033, 0x55005500550055]
def r12_goal : Nat := 0x1700570057007f
def r12_rows : Fin 64 → Fin 64 := decodeRows 0x208208208208208208208208df6d74cf2c709e69648e28602082082082082082082082085d65544d24501c61440c2040
set_option maxHeartbeats 0 in
theorem r12_lower : LowerBin r12_mask r12_stock r12_goal 9 := by
  apply lowerBin_of_rowPull r12_rows (stock' := r9_stock)
  · have hall : r12_stock.all (fun w => availBF r9_stock
        (rowCanon r12_rows r12_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r12_rows r12_mask = r9_mask := by decide +kernel
    have hg : rowCanon r12_rows r12_mask r12_goal = r9_goal := by decide +kernel
    rw [hm, hg]
    exact r9_lower

def r13_mask : Nat := 0xf0f0f0f
def r13_stock : List Nat := [0xf0f, 0xf000f, 0x3030303, 0x5050505]
def r13_goal : Nat := 0x107070f
def r13_bounds : List (Nat × List Nat × Nat × Nat) := []
theorem r13_sub : ∀ b ∈ r13_bounds, r13_mask &&& b.1 = b.1 := by
  have hall : r13_bounds.all (fun b => Nat.beq (Nat.land r13_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r13_goals : ∀ b ∈ r13_bounds, canon b.1 r13_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r13_bounds.all (fun b => Nat.beq (canonF b.1 r13_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r13_forest : Nat → Nat × Nat := unpackForestRelative (unpackPagedWidths [
    (16, 0x193a152d103e0c360826041ed81b3a3e363a0b4807402a36094c05441e32183a043408300424083604199c17042c9125081e041d8524803e0924044c743d703c1524104c041408440434583a04145036152404140c4c041404443835081504142c340c4c0844041c1c32181e1124041408340414041d0413000f)] 6) 10
def r13_links : Nat → Nat → Option Nat := unpackLinksPaged (unpackPaged [
    0x2d836a1b40da02cc35c59aa4d026813409a04c0a6012c290347863c11a28a1c312104d796b0340da00d005c62e01684b405622b01504a8054029854829c44e026852c49604a0a5012428664302180f8a7c03e01f00e4a7203711b80d826c03220ce4070001] 13 6)
  (unpackPaged [
    0xd423ed023ac4236b8232b554aa5546b513aa5136a012e1c12db444aa4446b403aa4036a102e1d02da101ea001995012940118801038444380349802c8043d7043a5843650435344348002d7002a5802650025340249001e8c01d4c43414024801247c04c484446003468034140246801414014701246c04c6404460034580144c03c440344c01444014501244804c400442603c1102c1001c1101d1001a3901638015340142c04c280442603c2502c2401c1443414024140141812410444100340c0140912d0812a9512694125881248444e7844d7444c5c44a544463c44530444204428403e7803d7403c5c03a540363c03530034200321d02e0902d1c01e0801ddb63fdaa3b9ea3706a33db13fd9d3b9dd3705d33da52fd992b9d92705923dac3fd8c3b9cc3704c33da02fd882b9c82704823d901fd801b9c017040130000f,
    0x240149802424028180101812426c4c604442603c60034f054ab4d46f013ab4936ed12eec12da012508122e844ed5c4ae44465cc42e803ed583ae40365c832e0026a0025dc01e0801dcc348c8340b1924b0824ada34c014cbc14460924ac8346181470010b00341402414120148201581061930ac920ac030a80240c02c1801cd464ed064ac4646b8642] 20 7) 5 10 6
def r13_trace := dagTraceF r13_mask r13_stock 6 r13_forest
set_option maxHeartbeats 0 in
def r13_sym0 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym1 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d96985d65544d14903ce34c2c92881c61440c1080
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d96985d65544d14903ce34c2c92881c61440c1080
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym2 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da4d25d65546584503ce34c2ca0c21c6144248040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da4d25d65546584503ce34c2ca0c21c6144248040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym3 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d94d15d65546984903ce34c2c90c11c6144288080
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d36925d65546516103ce34c2c32821c6144241200
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym4 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65542ca2483ce34c4d24501c61440c2040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65542ca2483ce34c4d24501c61440c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym5 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d96985d65542c92883ce34c4d14901c61440c1080
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d96985d65542c92883ce34c4d14901c61440c1080
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym6 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da2ca5d65546582483ce34c4d20c21c6144450040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da4d25d65542ca0c23ce34c6584501c6144248040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym7 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d92c95d65546982883ce34c4d10c11c6144490080
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d36925d65542c32823ce34c6516101c6144241200
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym8 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da4d25d65542ca0c23ce34c6584501c6144248040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da2ca5d65546582483ce34c4d20c21c6144450040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym9 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da2ca5d65544d20c23ce34c6582481c6144450040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da2ca5d65544d20c23ce34c6582481c6144450040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym10 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d32c35d65546922823ce34c6512411c6144610200
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d32c35d65546922823ce34c6512411c6144610200
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym11 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d94d15d65542c90c13ce34c6984901c6144288080
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6cb68a5d65546496083ce34c4c34821c6144441400
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym12 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d92c95d65544d10c13ce34c6982881c6144490080
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6cb68a5d65544c34823ce34c6496081c6144441400
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym13 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d32c35d65546512413ce34c6922821c6144610200
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6cb4c35d655468a4823ce34c6494411c6144608400
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_syms : List (TableSymmetry r13_mask r13_goal) := [
  ⟨(⟨r13_sym0, by decide +kernel⟩, rowCanon r13_sym0 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym1, by decide +kernel⟩, rowCanon r13_sym1 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym2, by decide +kernel⟩, rowCanon r13_sym2 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym3, by decide +kernel⟩, rowCanon r13_sym3 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym4, by decide +kernel⟩, rowCanon r13_sym4 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym5, by decide +kernel⟩, rowCanon r13_sym5 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym6, by decide +kernel⟩, rowCanon r13_sym6 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym7, by decide +kernel⟩, rowCanon r13_sym7 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym8, by decide +kernel⟩, rowCanon r13_sym8 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym9, by decide +kernel⟩, rowCanon r13_sym9 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym10, by decide +kernel⟩, rowCanon r13_sym10 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym11, by decide +kernel⟩, rowCanon r13_sym11 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym12, by decide +kernel⟩, rowCanon r13_sym12 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym13, by decide +kernel⟩, rowCanon r13_sym13 r13_mask), fun _ => rfl⟩]
def r13_profile : Nat → Nat := unpackPagedWidths [
    (1, 0x0)] 6
def r13_boundsFor (i _ : Nat) := chooseBounds r13_bounds (r13_profile i)
def r13_ref := symDagRef r13_mask r13_goal 61 4 r13_syms r13_trace r13_links
def r13_check : Nat → Bool := fun i => checkNodeViaF r13_mask r13_goal (r13_boundsFor i) r13_trace r13_ref i
set_option maxHeartbeats 0 in
theorem r13_roots : dagCheckRootsF r13_mask r13_goal r13_bounds
    (r13_ref 0) r13_stock 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b0 : treeBlockF 0 12 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b12 : treeBlockF 12 24 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b24 : treeBlockF 24 36 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b36 : treeBlockF 36 48 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b48 : treeBlockF 48 60 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b60 : treeBlockF 60 61 r13_check = true := by decide +kernel
theorem r13_nodes : ∀ i, 0 ≤ i → i < 61 → r13_check i = true :=
  joinBlockSpecs
    (joinBlockSpecs
      (blockSpec r13_b0)
      (joinBlockSpecs
        (blockSpec r13_b12)
        (blockSpec r13_b24)))
    (joinBlockSpecs
      (blockSpec r13_b36)
      (joinBlockSpecs
        (blockSpec r13_b48)
        (blockSpec r13_b60)))
theorem r13_known : KnownBin r13_bounds :=
  knownNil
theorem r13_lower : LowerBin r13_mask r13_stock r13_goal 7 :=
  lowerDagRefF (boundsFor := r13_boundsFor) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) r13_known r13_sub r13_goals
    (fun i _ _ hb => chooseBounds_mem (r13_profile i) hb)
    (symDagRef_sound (by decide +kernel) r13_syms r13_trace r13_links)
    r13_roots r13_nodes

def r14_mask : Nat := 0x5555555500000000
def r14_stock : List Nat := [0x555500000000, 0x55005500000000, 0x505050500000000, 0x1111111100000000]
def r14_goal : Nat := 0x115155500000000
def r14_rows : Fin 64 → Fin 64 := decodeRows 0xfbceb8000000db4cb0000000bacaa80000009a48a0
set_option maxHeartbeats 0 in
theorem r14_lower : LowerBin r14_mask r14_stock r14_goal 7 := by
  apply lowerBin_of_rowPull r14_rows (stock' := r13_stock)
  · have hall : r14_stock.all (fun w => availBF r13_stock
        (rowCanon r14_rows r14_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r14_rows r14_mask = r13_mask := by decide +kernel
    have hg : rowCanon r14_rows r14_mask r14_goal = r13_goal := by decide +kernel
    rw [hm, hg]
    exact r13_lower

def r15_mask : Nat := 0x5555555555555555
def r15_stock : List Nat := [0x55555555, 0x555500005555, 0x55005500550055, 0x505050505050505, 0x1111111111111111]
def r15_goal : Nat := 0x115155501555555
def r15_bounds : List (Nat × List Nat × Nat × Nat) := [(0x5555555500000000, [0x555500000000, 0x55005500000000, 0x505050500000000, 0x1111111100000000], 7, 0x115155500000000)]
theorem r15_sub : ∀ b ∈ r15_bounds, r15_mask &&& b.1 = b.1 := by
  have hall : r15_bounds.all (fun b => Nat.beq (Nat.land r15_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r15_goals : ∀ b ∈ r15_bounds, canon b.1 r15_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r15_bounds.all (fun b => Nat.beq (canonF b.1 r15_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r15_forest : Nat → Nat × Nat := fun _ => (0, 0)
def r15_links : Nat → Nat → Option Nat := fun _ _ => none
def r15_trace := dagTraceF r15_mask r15_stock 7 r15_forest
def r15_check : Nat → Bool := dagCheckNodeF r15_mask r15_goal r15_bounds 0 r15_trace r15_links
set_option maxHeartbeats 0 in
theorem r15_roots : dagCheckRootsF r15_mask r15_goal r15_bounds
    (dagRefF 0 r15_trace r15_links 0) r15_stock 7 = true := by decide +kernel
theorem r15_nodes : ∀ i, 0 ≤ i → i < 0 → r15_check i = true :=
  fun i _ hi => absurd hi (Nat.not_lt_zero i)
theorem r15_known : KnownBin r15_bounds :=
  knownCons r14_lower (
  knownNil)
theorem r15_lower : LowerBin r15_mask r15_stock r15_goal 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r15_known r15_sub r15_goals r15_roots r15_nodes

def r16_mask : Nat := 0xaaaaaaaaaaaaaaaa
def r16_stock : List Nat := [0xaaaaaaaa, 0xaaaa0000aaaa, 0xaa00aa00aa00aa, 0xa0a0a0a0a0a0a0a, 0x2222222222222222]
def r16_goal : Nat := 0x202020002022a
def r16_rows : Fin 64 → Fin 64 := decodeRows 0x100901101900300b01301b00500d01501d00700f01701f02102903103902302b03303b02502d03503d02702f03703f
set_option maxHeartbeats 0 in
theorem r16_lower : LowerBin r16_mask r16_stock r16_goal 8 := by
  apply lowerBin_of_rowPull r16_rows (stock' := r15_stock)
  · have hall : r16_stock.all (fun w => availBF r15_stock
        (rowCanon r16_rows r16_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r16_rows r16_mask = r15_mask := by decide +kernel
    have hg : rowCanon r16_rows r16_mask r16_goal = r15_goal := by decide +kernel
    rw [hm, hg]
    exact r15_lower

def r17_mask : Nat := 0xf0f0f0f0f0f0f0f
def r17_stock : List Nat := [0xf0f0f0f, 0xf0f00000f0f, 0xf000f000f000f, 0x303030303030303, 0x505050505050505]
def r17_goal : Nat := 0x10707070107070f
def r17_bounds : List (Nat × List Nat × Nat × Nat) := [(0xf0f0f0f, [0xf0f, 0xf000f, 0x3030303, 0x5050505], 7, 0x107070f)]
theorem r17_sub : ∀ b ∈ r17_bounds, r17_mask &&& b.1 = b.1 := by
  have hall : r17_bounds.all (fun b => Nat.beq (Nat.land r17_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r17_goals : ∀ b ∈ r17_bounds, canon b.1 r17_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r17_bounds.all (fun b => Nat.beq (canonF b.1 r17_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r17_forest : Nat → Nat × Nat := fun _ => (0, 0)
def r17_links : Nat → Nat → Option Nat := fun _ _ => none
def r17_trace := dagTraceF r17_mask r17_stock 7 r17_forest
def r17_check : Nat → Bool := dagCheckNodeF r17_mask r17_goal r17_bounds 0 r17_trace r17_links
set_option maxHeartbeats 0 in
theorem r17_roots : dagCheckRootsF r17_mask r17_goal r17_bounds
    (dagRefF 0 r17_trace r17_links 0) r17_stock 7 = true := by decide +kernel
theorem r17_nodes : ∀ i, 0 ≤ i → i < 0 → r17_check i = true :=
  fun i _ hi => absurd hi (Nat.not_lt_zero i)
theorem r17_known : KnownBin r17_bounds :=
  knownCons r13_lower (
  knownNil)
theorem r17_lower : LowerBin r17_mask r17_stock r17_goal 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r17_known r17_sub r17_goals r17_roots r17_nodes

def r18_mask : Nat := 0x33333333
def r18_stock : List Nat := [0x3333, 0x330033, 0x3030303, 0x11111111]
def r18_goal : Nat := 0x1131333
def r18_rows : Fin 64 → Fin 64 := decodeRows 0x8208208208208208208208208208208208208208208208208208275c65808208255445008208234c248082082144040
set_option maxHeartbeats 0 in
theorem r18_lower : LowerBin r18_mask r18_stock r18_goal 7 := by
  apply lowerBin_of_rowPull r18_rows (stock' := r13_stock)
  · have hall : r18_stock.all (fun w => availBF r13_stock
        (rowCanon r18_rows r18_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r18_rows r18_mask = r13_mask := by decide +kernel
    have hg : rowCanon r18_rows r18_mask r18_goal = r13_goal := by decide +kernel
    rw [hm, hg]
    exact r13_lower

def r19_mask : Nat := 0x4444444411111111
def r19_stock : List Nat := [0x11111111, 0x444400001111, 0x44004400110011, 0x404040401010101]
def r19_goal : Nat := 0x4044401111111
def r19_rows : Fin 64 → Fin 64 := decodeRows 0x41041041041041041041041041041041041041041041041041041fbadb2041041baa9a2041041718510041041308100
set_option maxHeartbeats 0 in
theorem r19_lower : LowerBin r19_mask r19_stock r19_goal 7 := by
  apply lowerBin_of_rowPull r19_rows (stock' := r13_stock)
  · have hall : r19_stock.all (fun w => availBF r13_stock
        (rowCanon r19_rows r19_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r19_rows r19_mask = r13_mask := by decide +kernel
    have hg : rowCanon r19_rows r19_mask r19_goal = r13_goal := by decide +kernel
    rw [hm, hg]
    exact r13_lower

def r20_mask : Nat := 0xc0c0c0c030303030
def r20_stock : List Nat := [0x30303030, 0xc0c000003030, 0xc000c000300030, 0x4040404010101010]
def r20_goal : Nat := 0x4000101030
def r20_rows : Fin 64 → Fin 64 := decodeRows 0x10530d00000051571d0000009a7baf000000db7fbf
set_option maxHeartbeats 0 in
theorem r20_lower : LowerBin r20_mask r20_stock r20_goal 7 := by
  apply lowerBin_of_rowPull r20_rows (stock' := r13_stock)
  · have hall : r20_stock.all (fun w => availBF r13_stock
        (rowCanon r20_rows r20_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r20_rows r20_mask = r13_mask := by decide +kernel
    have hg : rowCanon r20_rows r20_mask r20_goal = r13_goal := by decide +kernel
    rw [hm, hg]
    exact r13_lower

def r21_mask : Nat := 0xcc00cc0033003300
def r21_stock : List Nat := [0x33003300, 0xcc0000003300, 0xc000c0003000300, 0x4400440011001100]
def r21_goal : Nat := 0x40001001300
def r21_rows : Fin 64 → Fin 64 := decodeRows 0x20930d00000061971d000000aabbaf000000ebbfbf
set_option maxHeartbeats 0 in
theorem r21_lower : LowerBin r21_mask r21_stock r21_goal 7 := by
  apply lowerBin_of_rowPull r21_rows (stock' := r13_stock)
  · have hall : r21_stock.all (fun w => availBF r13_stock
        (rowCanon r21_rows r21_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r21_rows r21_mask = r13_mask := by decide +kernel
    have hg : rowCanon r21_rows r21_mask r21_goal = r13_goal := by decide +kernel
    rw [hm, hg]
    exact r13_lower

def r22_mask : Nat := 0xcccc000033330000
def r22_stock : List Nat := [0x33330000, 0xcc000000330000, 0xc0c000003030000, 0x4444000011110000]
def r22_goal : Nat := 0x4000001130000
def r22_rows : Fin 64 → Fin 64 := decodeRows 0x41151500000061971d000000cb3db7000000ebbfbf
set_option maxHeartbeats 0 in
theorem r22_lower : LowerBin r22_mask r22_stock r22_goal 7 := by
  apply lowerBin_of_rowPull r22_rows (stock' := r13_stock)
  · have hall : r22_stock.all (fun w => availBF r13_stock
        (rowCanon r22_rows r22_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r22_rows r22_mask = r13_mask := by decide +kernel
    have hg : rowCanon r22_rows r22_mask r22_goal = r13_goal := by decide +kernel
    rw [hm, hg]
    exact r13_lower

def r23_mask : Nat := 0xcccccccc00000000
def r23_stock : List Nat := [0xcccc00000000, 0xcc00cc00000000, 0xc0c0c0c00000000, 0x4444444400000000]
def r23_goal : Nat := 0x4044400000000
def r23_rows : Fin 64 → Fin 64 := decodeRows 0x8a39a7aabbafcb3db7ebbfbf
set_option maxHeartbeats 0 in
theorem r23_lower : LowerBin r23_mask r23_stock r23_goal 5 := by
  apply lowerBin_of_rowPull r23_rows (stock' := r4_stock)
  · have hall : r23_stock.all (fun w => availBF r4_stock
        (rowCanon r23_rows r23_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r23_rows r23_mask = r4_mask := by decide +kernel
    have hg : rowCanon r23_rows r23_mask r23_goal = r4_goal := by decide +kernel
    rw [hm, hg]
    exact r4_lower

def r24_mask : Nat := 0xcccc00003333
def r24_stock : List Nat := [0x3333, 0xcc00000033, 0xc0c00000303, 0x444400001111]
def r24_goal : Nat := 0x44400001333
def r24_rows : Fin 64 → Fin 64 := decodeRows 0x8208208208208208208208208208208208208208208208200110520930d0820820820828a39a7aabbaf082082082082
set_option maxHeartbeats 0 in
theorem r24_lower : LowerBin r24_mask r24_stock r24_goal 5 := by
  apply lowerBin_of_rowPull r24_rows (stock' := r2_stock)
  · have hall : r24_stock.all (fun w => availBF r2_stock
        (rowCanon r24_rows r24_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r24_rows r24_mask = r2_mask := by decide +kernel
    have hg : rowCanon r24_rows r24_mask r24_goal = r2_goal := by decide +kernel
    rw [hm, hg]
    exact r2_lower

def r25_mask : Nat := 0xcc00cc00330033
def r25_stock : List Nat := [0x330033, 0xcc00000033, 0xc000c00030003, 0x44004400110011]
def r25_goal : Nat := 0x4004400130033
def r25_rows : Fin 64 → Fin 64 := decodeRows 0x820820820820820820820820820820820820820820820820011054115150820820820828a39a7cb3db7082082082082
set_option maxHeartbeats 0 in
theorem r25_lower : LowerBin r25_mask r25_stock r25_goal 5 := by
  apply lowerBin_of_rowPull r25_rows (stock' := r2_stock)
  · have hall : r25_stock.all (fun w => availBF r2_stock
        (rowCanon r25_rows r25_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r25_rows r25_mask = r2_mask := by decide +kernel
    have hg : rowCanon r25_rows r25_mask r25_goal = r2_goal := by decide +kernel
    rw [hm, hg]
    exact r2_lower

def r26_mask : Nat := 0xc0c0c0c03030303
def r26_stock : List Nat := [0x3030303, 0xc0c00000303, 0xc000c00030003, 0x404040401010101]
def r26_goal : Nat := 0x4040401030303
def r26_rows : Fin 64 → Fin 64 := decodeRows 0x820820820820820820820820820820820820820820820820012094116190820820820828a3aabcb3ebb082082082082
set_option maxHeartbeats 0 in
theorem r26_lower : LowerBin r26_mask r26_stock r26_goal 5 := by
  apply lowerBin_of_rowPull r26_rows (stock' := r2_stock)
  · have hall : r26_stock.all (fun w => availBF r2_stock
        (rowCanon r26_rows r26_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r26_rows r26_mask = r2_mask := by decide +kernel
    have hg : rowCanon r26_rows r26_mask r26_goal = r2_goal := by decide +kernel
    rw [hm, hg]
    exact r2_lower

def r27_mask : Nat := 0x8888888822222222
def r27_stock : List Nat := [0x22222222, 0x888800002222, 0x88008800220022, 0x808080802020202]
def r27_goal : Nat := 0x20222
def r27_rows : Fin 64 → Fin 64 := decodeRows 0x6316726b36f47357767b77f
set_option maxHeartbeats 0 in
theorem r27_lower : LowerBin r27_mask r27_stock r27_goal 5 := by
  apply lowerBin_of_rowPull r27_rows (stock' := r4_stock)
  · have hall : r27_stock.all (fun w => availBF r4_stock
        (rowCanon r27_rows r27_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r27_rows r27_mask = r4_mask := by decide +kernel
    have hg : rowCanon r27_rows r27_mask r27_goal = r4_goal := by decide +kernel
    rw [hm, hg]
    exact r4_lower

def r28_mask : Nat := 0xcccccccc33333333
def r28_stock : List Nat := [0x33333333, 0xcccc00003333, 0xcc00cc00330033, 0xc0c0c0c03030303, 0x4444444411111111]
def r28_goal : Nat := 0x4044401131333
def r28_bounds : List (Nat × List Nat × Nat × Nat) := [(0x33333333, [0x3333, 0x330033, 0x3030303, 0x11111111], 7, 0x1131333), (0x4444444411111111, [0x11111111, 0x444400001111, 0x44004400110011, 0x404040401010101], 7, 0x4044401111111), (0xc0c0c0c030303030, [0x30303030, 0xc0c000003030, 0xc000c000300030, 0x4040404010101010], 7, 0x4000101030), (0xcc00cc0033003300, [0x33003300, 0xcc0000003300, 0xc000c0003000300, 0x4400440011001100], 7, 0x40001001300), (0xcccc000033330000, [0x33330000, 0xcc000000330000, 0xc0c000003030000, 0x4444000011110000], 7, 0x4000001130000), (0xcccccccc00000000, [0xcccc00000000, 0xcc00cc00000000, 0xc0c0c0c00000000, 0x4444444400000000], 5, 0x4044400000000), (0xcccc00003333, [0x3333, 0xcc00000033, 0xc0c00000303, 0x444400001111], 5, 0x44400001333), (0xcc00cc00330033, [0x330033, 0xcc00000033, 0xc000c00030003, 0x44004400110011], 5, 0x4004400130033), (0xc0c0c0c03030303, [0x3030303, 0xc0c00000303, 0xc000c00030003, 0x404040401010101], 5, 0x4040401030303), (0x8888888822222222, [0x22222222, 0x888800002222, 0x88008800220022, 0x808080802020202], 5, 0x20222)]
theorem r28_sub : ∀ b ∈ r28_bounds, r28_mask &&& b.1 = b.1 := by
  have hall : r28_bounds.all (fun b => Nat.beq (Nat.land r28_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r28_goals : ∀ b ∈ r28_bounds, canon b.1 r28_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r28_bounds.all (fun b => Nat.beq (canonF b.1 r28_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r28_forest : Nat → Nat × Nat := unpackForestRelative (unpackPagedWidths [
    (17, 0x322b02910a4ac0c6020a10e138609a093404a30613010a80842311b8ed2828b0084c11a30691812680846101382940168e08269c218415410a91b5f04220d58854bc205e0c2e8417010a4db470426028dd84bc0b55582f83160146e985e042e02d1d00a40854062f9a0e810a83c6e1a310b16810b81c56083702158406e0b58062f820d81036001f),
    (18, 0x82918d2c5b4a021004b46024d03946091881c5a041b80856040cc08318649c08341d168085c)] 6) 11
def r28_links : Nat → Nat → Option Nat := unpackLinksPaged (unpackPaged [
    0x7a377377076176076076075173273071262f6206206206025f15f05e156856055154148c4804803f93f03e13e03e03e03d13c131b3102f22e12e02862802712612602512412402312212202112102102102012002001a61a01911810bd01a001,
    0xa509d89c19c09939819629519509509508e78d17fe7f07e17e07d1] 12 6)
  (unpackPaged [
    0x8800c610034800171c184c7020f1c002c7c0911b885c6e00f1e04607004d1b92466e0519a8054600131dac61821169f84567a4d59e82567605089205a528159d004e720135b004c5e0115a00425c40d5700256211618004c5a00d168134642d6978b56640d29783465c2959702465821596004654094148347666d1d98a476608dc8a04a56811d420462240e9590375040d88802a56009d400261ef1741bc551801746305a4cc159300554a01507884a062119180443605784805c1ef5b9105623409b90825e2a01b890062400178f805d3c0170400553a0148dac58360130d0237183174c0c55180d74c03550e2118380362c1160a8237260170903472001507845f1a01504805c1811b858462141168404560e01b830056080d601845f48317d2035f380d1cc825e2e017ca005e2201487084a0a211c108461c00e8280370400d80c34f02c93e19a3702a53e1893786049d380430280ec0902b02006c0001f,
    0x10c56e90b18a82a6e3b09890a059900106800293a8086080539ab141f80539a0101f00439604d1e805378058248462901169d81628e01b9a00623a816a3005645117ce445f1cad7a2ab5388ad4a7834b9c0d2a6034694491a5014666014ce204b1c00e628033] 22 7) 4 11 5
def r28_trace := dagTraceF r28_mask r28_stock 9 r28_forest
set_option maxHeartbeats 0 in
def r28_sym0 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r28_sym1 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cdf6e78efad74cf2c70beeb6c9e6a68aea9648e28607de75c6da5545d66584d24503ce34c2ca1441c62480c2040
  invFun := decodeRows 0xffef7cdf6e78efad74cf2c70beeb6c9e6a68aea9648e28607de75c6da5545d66584d24503ce34c2ca1441c62480c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r28_sym2 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78beed74aeac70df6b6ccf2a689e69648e28607de75c6da6585d634c4d22483ce5542ca4501c61440c2040
  invFun := decodeRows 0xffef7cefae78beed74aeac70df6b6ccf2a689e69648e28607de75c6da6585d634c4d22483ce5542ca4501c61440c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r28_sym3 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cbeee78efad74aeac70df6b6c9e6a68cf29648e28607de75c6da34c5d66584d22483ce5542ca1441c64500c2040
  invFun := decodeRows 0xffef7cdf6e78beed749e6c70efab6ccf2a68aea9648e28607de75c6da5545d634c4d21443ce6582ca4501c62480c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r28_sym4 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cdf6e78beed749e6c70efab6ccf2a68aea9648e28607de75c6da5545d634c4d21443ce6582ca4501c62480c2040
  invFun := decodeRows 0xffef7cbeee78efad74aeac70df6b6c9e6a68cf29648e28607de75c6da34c5d66584d22483ce5542ca1441c64500c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r28_sym5 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xfddf7ced9e78dd5d74cd1c70bcdb6cac9a689c59648c18607def9c6dae985d6d944d2c903ceb8c2caa881c69840c2880
  invFun := decodeRows 0xfddf7ced9e78dd5d74cd1c70bcdb6cac9a689c59648c18607def9c6dae985d6d944d2c903ceb8c2caa881c69840c2880
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r28_sym6 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xfddf7ced9e78bcdd74ac9c70dd5b6ccd1a689c59648c18607def9c6dae985d6b8c4d2a883ced942cac901c69840c2880
  invFun := decodeRows 0xfddf7ced9e78bcdd74ac9c70dd5b6ccd1a689c59648c18607def9c6dae985d6b8c4d2a883ced942cac901c69840c2880
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r28_sym7 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xfddf7cbcde78ed9d74ac9c70dd5b6c9c5a68cd19648c18607def9c6dab8c5d6e984d2a883ced942ca9841c6c900c2880
  invFun := decodeRows 0xfddf7cdd5e78bcdd749c5c70ed9b6ccd1a68ac99648c18607def9c6dad945d6b8c4d29843cee982cac901c6a880c2880
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r28_sym8 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xfddf7cdd5e78bcdd749c5c70ed9b6ccd1a68ac99648c18607def9c6dad945d6b8c4d29843cee982cac901c6a880c2880
  invFun := decodeRows 0xfddf7cbcde78ed9d74ac9c70dd5b6c9c5a68cd19648c18607def9c6dab8c5d6e984d2a883ced942ca9841c6c900c2880
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r28_syms : List (TableSymmetry r28_mask r28_goal) := [
  ⟨(⟨r28_sym0, by decide +kernel⟩, rowCanon r28_sym0 r28_mask), fun _ => rfl⟩,
  ⟨(⟨r28_sym1, by decide +kernel⟩, rowCanon r28_sym1 r28_mask), fun _ => rfl⟩,
  ⟨(⟨r28_sym2, by decide +kernel⟩, rowCanon r28_sym2 r28_mask), fun _ => rfl⟩,
  ⟨(⟨r28_sym3, by decide +kernel⟩, rowCanon r28_sym3 r28_mask), fun _ => rfl⟩,
  ⟨(⟨r28_sym4, by decide +kernel⟩, rowCanon r28_sym4 r28_mask), fun _ => rfl⟩,
  ⟨(⟨r28_sym5, by decide +kernel⟩, rowCanon r28_sym5 r28_mask), fun _ => rfl⟩,
  ⟨(⟨r28_sym6, by decide +kernel⟩, rowCanon r28_sym6 r28_mask), fun _ => rfl⟩,
  ⟨(⟨r28_sym7, by decide +kernel⟩, rowCanon r28_sym7 r28_mask), fun _ => rfl⟩,
  ⟨(⟨r28_sym8, by decide +kernel⟩, rowCanon r28_sym8 r28_mask), fun _ => rfl⟩]
def r28_profile : Nat → Nat := unpackPagedWidths [
    (10, 0xffccd7340b3ac3810c000111f0201cbfc990040001e39064d90fc6c371ff0fc8047cbf00673354242461f010ff000651fcca1fc00b5bbf001fc6fc004933f000008ed0c00011a298c1fc00603bf0fc1f),
    (10, 0xed37f7f0fe7f37c5f8ad2582d0d3ff3f17c407f401)] 6
def r28_boundsFor (i _ : Nat) := chooseBounds r28_bounds (r28_profile i)
def r28_ref := symDagRef r28_mask r28_goal 81 4 r28_syms r28_trace r28_links
def r28_check : Nat → Bool := fun i => checkNodeViaF r28_mask r28_goal (r28_boundsFor i) r28_trace r28_ref i
set_option maxHeartbeats 0 in
theorem r28_roots : dagCheckRootsF r28_mask r28_goal r28_bounds
    (r28_ref 0) r28_stock 9 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b0 : treeBlockF 0 12 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b12 : treeBlockF 12 24 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b24 : treeBlockF 24 36 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b36 : treeBlockF 36 48 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b48 : treeBlockF 48 60 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b60 : treeBlockF 60 72 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b72 : treeBlockF 72 81 r28_check = true := by decide +kernel
theorem r28_nodes : ∀ i, 0 ≤ i → i < 81 → r28_check i = true :=
  joinBlockSpecs
    (joinBlockSpecs
      (blockSpec r28_b0)
      (joinBlockSpecs
        (blockSpec r28_b12)
        (blockSpec r28_b24)))
    (joinBlockSpecs
      (joinBlockSpecs
        (blockSpec r28_b36)
        (blockSpec r28_b48))
      (joinBlockSpecs
        (blockSpec r28_b60)
        (blockSpec r28_b72)))
theorem r28_known : KnownBin r28_bounds :=
  knownCons r18_lower (
  knownCons r19_lower (
  knownCons r20_lower (
  knownCons r21_lower (
  knownCons r22_lower (
  knownCons r23_lower (
  knownCons r24_lower (
  knownCons r25_lower (
  knownCons r26_lower (
  knownCons r27_lower (
  knownNil))))))))))
theorem r28_lower : LowerBin r28_mask r28_stock r28_goal 10 :=
  lowerDagRefF (boundsFor := r28_boundsFor) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) r28_known r28_sub r28_goals
    (fun i _ _ hb => chooseBounds_mem (r28_profile i) hb)
    (symDagRef_sound (by decide +kernel) r28_syms r28_trace r28_links)
    r28_roots r28_nodes

def r29_mask : Nat := 0xffff00000000ffff
def r29_stock : List Nat := [0xffff, 0xff0000000000ff, 0xf0f000000000f0f, 0x3333000000003333, 0x5555000000005555]
def r29_goal : Nat := 0x11700000000577f
def r29_rows : Fin 64 → Fin 64 := decodeRows 0x141008341010541018741020941028b41030d41038f410410c31410cb3410d35410db7410e39410ebb410f3d410fbf
set_option maxHeartbeats 0 in
theorem r29_lower : LowerBin r29_mask r29_stock r29_goal 10 := by
  apply lowerBin_of_rowPull r29_rows (stock' := r28_stock)
  · have hall : r29_stock.all (fun w => availBF r28_stock
        (rowCanon r29_rows r29_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r29_rows r29_mask = r28_mask := by decide +kernel
    have hg : rowCanon r29_rows r29_mask r29_goal = r28_goal := by decide +kernel
    rw [hm, hg]
    exact r28_lower

def r30_mask : Nat := 0xff00ff00ff00ff00
def r30_stock : List Nat := [0xff00ff00, 0xff000000ff00, 0xf000f000f000f00, 0x3300330033003300, 0x5500550055005500]
def r30_goal : Nat := 0x100170001005700
def r30_rows : Fin 64 → Fin 64 := decodeRows 0x20961900000028b69b00000030d71d00000038f79f000000a29e39000000aabebb000000b2df3d000000baffbf
set_option maxHeartbeats 0 in
theorem r30_lower : LowerBin r30_mask r30_stock r30_goal 8 := by
  apply lowerBin_of_rowPull r30_rows (stock' := r17_stock)
  · have hall : r30_stock.all (fun w => availBF r17_stock
        (rowCanon r30_rows r30_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r30_rows r30_mask = r17_mask := by decide +kernel
    have hg : rowCanon r30_rows r30_mask r30_goal = r17_goal := by decide +kernel
    rw [hm, hg]
    exact r17_lower

def r31_mask : Nat := 0x3333333333333333
def r31_stock : List Nat := [0x33333333, 0x333300003333, 0x33003300330033, 0x303030303030303, 0x1111111111111111]
def r31_goal : Nat := 0x113131301131333
def r31_rows : Fin 64 → Fin 64 := decodeRows 0x82082f7ce78082082d74c70082082b6ca6808208296486008208275c65808208255445008208234c248082082144040
set_option maxHeartbeats 0 in
theorem r31_lower : LowerBin r31_mask r31_stock r31_goal 8 := by
  apply lowerBin_of_rowPull r31_rows (stock' := r17_stock)
  · have hall : r31_stock.all (fun w => availBF r17_stock
        (rowCanon r31_rows r31_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r31_rows r31_mask = r17_mask := by decide +kernel
    have hg : rowCanon r31_rows r31_mask r31_goal = r17_goal := by decide +kernel
    rw [hm, hg]
    exact r17_lower

def r32_mask : Nat := 0xffff0000ffff0000
def r32_stock : List Nat := [0xffff0000, 0xff000000ff0000, 0xf0f00000f0f0000, 0x3333000033330000, 0x5555000055550000]
def r32_goal : Nat := 0x117000001570000
def r32_rows : Fin 64 → Fin 64 := decodeRows 0x41161900000049369b00000051571d00000059779f000000c31e39000000cb3ebb000000d35f3d000000db7fbf
set_option maxHeartbeats 0 in
theorem r32_lower : LowerBin r32_mask r32_stock r32_goal 8 := by
  apply lowerBin_of_rowPull r32_rows (stock' := r17_stock)
  · have hall : r32_stock.all (fun w => availBF r17_stock
        (rowCanon r32_rows r32_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r32_rows r32_mask = r17_mask := by decide +kernel
    have hg : rowCanon r32_rows r32_mask r32_goal = r17_goal := by decide +kernel
    rw [hm, hg]
    exact r17_lower

def r33_mask : Nat := 0xaaaaaaaa
def r33_stock : List Nat := [0xaaaa, 0xaa00aa, 0xa0a0a0a, 0x22222222]
def r33_goal : Nat := 0x2022a
def r33_rows : Fin 64 → Fin 64 := decodeRows 0x4314700000024b34f00000045355700000065b75f
set_option maxHeartbeats 0 in
theorem r33_lower : LowerBin r33_mask r33_stock r33_goal 7 := by
  apply lowerBin_of_rowPull r33_rows (stock' := r13_stock)
  · have hall : r33_stock.all (fun w => availBF r13_stock
        (rowCanon r33_rows r33_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r33_rows r33_mask = r13_mask := by decide +kernel
    have hg : rowCanon r33_rows r33_mask r33_goal = r13_goal := by decide +kernel
    rw [hm, hg]
    exact r13_lower

def r34_mask : Nat := 0xff00ff
def r34_stock : List Nat := [0xff, 0xf000f, 0x330033, 0x550055]
def r34_goal : Nat := 0x57007f
def r34_rows : Fin 64 → Fin 64 := decodeRows 0x2082082082082082082082082082082082082082082082082082082082082082082082085d65544d24501c61440c2040
set_option maxHeartbeats 0 in
theorem r34_lower : LowerBin r34_mask r34_stock r34_goal 5 := by
  apply lowerBin_of_rowPull r34_rows (stock' := r4_stock)
  · have hall : r34_stock.all (fun w => availBF r4_stock
        (rowCanon r34_rows r34_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r34_rows r34_mask = r4_mask := by decide +kernel
    have hg : rowCanon r34_rows r34_mask r34_goal = r4_goal := by decide +kernel
    rw [hm, hg]
    exact r4_lower

def r35_mask : Nat := 0xffffffff
def r35_stock : List Nat := [0xffff, 0xff00ff, 0xf0f0f0f, 0x33333333, 0x55555555]
def r35_goal : Nat := 0x157577f
def r35_bounds : List (Nat × List Nat × Nat × Nat) := [(0xaaaaaaaa, [0xaaaa, 0xaa00aa, 0xa0a0a0a, 0x22222222], 7, 0x2022a), (0x33333333, [0x3333, 0x330033, 0x3030303, 0x11111111], 7, 0x1131333), (0xf0f0f0f, [0xf0f, 0xf000f, 0x3030303, 0x5050505], 7, 0x107070f), (0xff00ff, [0xff, 0xf000f, 0x330033, 0x550055], 5, 0x57007f), (0xff00ff00, [0xff00, 0xf000f00, 0x33003300, 0x55005500], 5, 0x1005700), (0xffff, [0xff, 0xf0f, 0x3333, 0x5555], 5, 0x577f)]
theorem r35_sub : ∀ b ∈ r35_bounds, r35_mask &&& b.1 = b.1 := by
  have hall : r35_bounds.all (fun b => Nat.beq (Nat.land r35_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r35_goals : ∀ b ∈ r35_bounds, canon b.1 r35_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r35_bounds.all (fun b => Nat.beq (canonF b.1 r35_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r35_forest : Nat → Nat × Nat := unpackForestF 0x10fa1b42f4910981f 2 9
def r35_links : Nat → Nat → Option Nat := unpackLinksF 0x38e31c29301 0x410524a1f81b61721301f 6 3 9 3 4
def r35_trace := dagTraceF r35_mask r35_stock 8 r35_forest
def r35_check : Nat → Bool := dagCheckNodeF r35_mask r35_goal r35_bounds 6 r35_trace r35_links
set_option maxHeartbeats 0 in
theorem r35_roots : dagCheckRootsF r35_mask r35_goal r35_bounds
    (dagRefF 6 r35_trace r35_links 0) r35_stock 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r35_b0 : treeBlockF 0 6 r35_check = true := by decide +kernel
theorem r35_nodes : ∀ i, 0 ≤ i → i < 6 → r35_check i = true :=
  blockSpec r35_b0
theorem r35_known : KnownBin r35_bounds :=
  knownCons r33_lower (
  knownCons r18_lower (
  knownCons r13_lower (
  knownCons r34_lower (
  knownCons r2_lower (
  knownCons r4_lower (
  knownNil))))))
theorem r35_lower : LowerBin r35_mask r35_stock r35_goal 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r35_known r35_sub r35_goals r35_roots r35_nodes

def r36_mask : Nat := 0xffffffff00000000
def r36_stock : List Nat := [0xffff00000000, 0xff00ff00000000, 0xf0f0f0f00000000, 0x3333333300000000, 0x5555555500000000]
def r36_goal : Nat := 0x117175700000000
def r36_rows : Fin 64 → Fin 64 := decodeRows 0x821a29c31e398a3aabcb3ebb925b2dd35f3d9a7bafdb7fbf
set_option maxHeartbeats 0 in
theorem r36_lower : LowerBin r36_mask r36_stock r36_goal 9 := by
  apply lowerBin_of_rowPull r36_rows (stock' := r35_stock)
  · have hall : r36_stock.all (fun w => availBF r35_stock
        (rowCanon r36_rows r36_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r36_rows r36_mask = r35_mask := by decide +kernel
    have hg : rowCanon r36_rows r36_mask r36_goal = r35_goal := by decide +kernel
    rw [hm, hg]
    exact r35_lower

def r37_mask : Nat := 0x55005500aa00aa
def r37_stock : List Nat := [0xaa00aa, 0x55000000aa, 0x50005000a000a, 0x11001100220022]
def r37_goal : Nat := 0x1500550002002a
def r37_rows : Fin 64 → Fin 64 := decodeRows 0x5d54d10000001c50c1000000db4cb00000009a48a0
set_option maxHeartbeats 0 in
theorem r37_lower : LowerBin r37_mask r37_stock r37_goal 7 := by
  apply lowerBin_of_rowPull r37_rows (stock' := r13_stock)
  · have hall : r37_stock.all (fun w => availBF r13_stock
        (rowCanon r37_rows r37_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r37_rows r37_mask = r13_mask := by decide +kernel
    have hg : rowCanon r37_rows r37_mask r37_goal = r13_goal := by decide +kernel
    rw [hm, hg]
    exact r13_lower

def r38_mask : Nat := 0x50505050a0a0a0a
def r38_stock : List Nat := [0xa0a0a0a, 0x50500000a0a, 0x50005000a000a, 0x101010102020202]
def r38_goal : Nat := 0x10505050002020a
def r38_rows : Fin 64 → Fin 64 := decodeRows 0x6d94d10000002c90c1000000eb8cb0000000aa88a0
set_option maxHeartbeats 0 in
theorem r38_lower : LowerBin r38_mask r38_stock r38_goal 7 := by
  apply lowerBin_of_rowPull r38_rows (stock' := r13_stock)
  · have hall : r38_stock.all (fun w => availBF r13_stock
        (rowCanon r38_rows r38_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r38_rows r38_mask = r13_mask := by decide +kernel
    have hg : rowCanon r38_rows r38_mask r38_goal = r13_goal := by decide +kernel
    rw [hm, hg]
    exact r13_lower

def r39_mask : Nat := 0x1111111122222222
def r39_stock : List Nat := [0x22222222, 0x111100002222, 0x11001100220022, 0x101010102020202]
def r39_goal : Nat := 0x111111100020222
def r39_rows : Fin 64 → Fin 64 := decodeRows 0x759551000000349141000000f38d30000000b28920
set_option maxHeartbeats 0 in
theorem r39_lower : LowerBin r39_mask r39_stock r39_goal 7 := by
  apply lowerBin_of_rowPull r39_rows (stock' := r13_stock)
  · have hall : r39_stock.all (fun w => availBF r13_stock
        (rowCanon r39_rows r39_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r39_rows r39_mask = r13_mask := by decide +kernel
    have hg : rowCanon r39_rows r39_mask r39_goal = r13_goal := by decide +kernel
    rw [hm, hg]
    exact r13_lower

def r40_mask : Nat := 0x4444444488888888
def r40_stock : List Nat := [0x88888888, 0x444400008888, 0x44004400880088, 0x404040408080808]
def r40_goal : Nat := 0x4044400000008
def r40_rows : Fin 64 → Fin 64 := decodeRows 0x8a6aae000000cb6ebe0000000c72cf0000004d76df
set_option maxHeartbeats 0 in
theorem r40_lower : LowerBin r40_mask r40_stock r40_goal 7 := by
  apply lowerBin_of_rowPull r40_rows (stock' := r13_stock)
  · have hall : r40_stock.all (fun w => availBF r13_stock
        (rowCanon r40_rows r40_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r40_rows r40_mask = r13_mask := by decide +kernel
    have hg : rowCanon r40_rows r40_mask r40_goal = r13_goal := by decide +kernel
    rw [hm, hg]
    exact r13_lower

def r41_mask : Nat := 0x50505050a0a0a0a0
def r41_stock : List Nat := [0xa0a0a0a0, 0x50500000a0a0, 0x50005000a000a0, 0x1010101020202020]
def r41_goal : Nat := 0x10105000000020
def r41_rows : Fin 64 → Fin 64 := decodeRows 0x926b2e000000d36f3e00000014734f00000055775f
set_option maxHeartbeats 0 in
theorem r41_lower : LowerBin r41_mask r41_stock r41_goal 7 := by
  apply lowerBin_of_rowPull r41_rows (stock' := r13_stock)
  · have hall : r41_stock.all (fun w => availBF r13_stock
        (rowCanon r41_rows r41_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r41_rows r41_mask = r13_mask := by decide +kernel
    have hg : rowCanon r41_rows r41_mask r41_goal = r13_goal := by decide +kernel
    rw [hm, hg]
    exact r13_lower

def r42_mask : Nat := 0x55005500aa00aa00
def r42_stock : List Nat := [0xaa00aa00, 0x55000000aa00, 0x50005000a000a00, 0x1100110022002200]
def r42_goal : Nat := 0x100150000000200
def r42_rows : Fin 64 → Fin 64 := decodeRows 0xa2ab2e000000e3af3e00000024b34f00000065b75f
set_option maxHeartbeats 0 in
theorem r42_lower : LowerBin r42_mask r42_stock r42_goal 7 := by
  apply lowerBin_of_rowPull r42_rows (stock' := r13_stock)
  · have hall : r42_stock.all (fun w => availBF r13_stock
        (rowCanon r42_rows r42_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r42_rows r42_mask = r13_mask := by decide +kernel
    have hg : rowCanon r42_rows r42_mask r42_goal = r13_goal := by decide +kernel
    rw [hm, hg]
    exact r13_lower

def r43_mask : Nat := 0x55555555aaaaaaaa
def r43_stock : List Nat := [0xaaaaaaaa, 0x55550000aaaa, 0x55005500aa00aa, 0x50505050a0a0a0a, 0x1111111122222222]
def r43_goal : Nat := 0x11515550002022a
def r43_bounds : List (Nat × List Nat × Nat × Nat) := [(0x5555555500000000, [0x555500000000, 0x55005500000000, 0x505050500000000, 0x1111111100000000], 7, 0x115155500000000), (0xaaaaaaaa, [0xaaaa, 0xaa00aa, 0xa0a0a0a, 0x22222222], 7, 0x2022a), (0x55005500aa00aa, [0xaa00aa, 0x55000000aa, 0x50005000a000a, 0x11001100220022], 7, 0x1500550002002a), (0x50505050a0a0a0a, [0xa0a0a0a, 0x50500000a0a, 0x50005000a000a, 0x101010102020202], 7, 0x10505050002020a), (0x1111111122222222, [0x22222222, 0x111100002222, 0x11001100220022, 0x101010102020202], 7, 0x111111100020222), (0x4444444488888888, [0x88888888, 0x444400008888, 0x44004400880088, 0x404040408080808], 7, 0x4044400000008), (0x50505050a0a0a0a0, [0xa0a0a0a0, 0x50500000a0a0, 0x50005000a000a0, 0x1010101020202020], 7, 0x10105000000020), (0x55005500aa00aa00, [0xaa00aa00, 0x55000000aa00, 0x50005000a000a00, 0x1100110022002200], 7, 0x100150000000200)]
theorem r43_sub : ∀ b ∈ r43_bounds, r43_mask &&& b.1 = b.1 := by
  have hall : r43_bounds.all (fun b => Nat.beq (Nat.land r43_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r43_goals : ∀ b ∈ r43_bounds, canon b.1 r43_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r43_bounds.all (fun b => Nat.beq (canonF b.1 r43_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r43_forest : Nat → Nat × Nat := unpackForestF 0x1f 1 5
def r43_links : Nat → Nat → Option Nat := unpackLinksF 0x9 0x1f 2 1 5 1 2
def r43_trace := dagTraceF r43_mask r43_stock 9 r43_forest
def r43_check : Nat → Bool := dagCheckNodeF r43_mask r43_goal r43_bounds 1 r43_trace r43_links
set_option maxHeartbeats 0 in
theorem r43_roots : dagCheckRootsF r43_mask r43_goal r43_bounds
    (dagRefF 1 r43_trace r43_links 0) r43_stock 9 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r43_b0 : treeBlockF 0 1 r43_check = true := by decide +kernel
theorem r43_nodes : ∀ i, 0 ≤ i → i < 1 → r43_check i = true :=
  blockSpec r43_b0
theorem r43_known : KnownBin r43_bounds :=
  knownCons r14_lower (
  knownCons r33_lower (
  knownCons r37_lower (
  knownCons r38_lower (
  knownCons r39_lower (
  knownCons r40_lower (
  knownCons r41_lower (
  knownCons r42_lower (
  knownNil))))))))
theorem r43_lower : LowerBin r43_mask r43_stock r43_goal 10 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r43_known r43_sub r43_goals r43_roots r43_nodes

def r44_mask : Nat := 0x5500550055005500
def r44_stock : List Nat := [0x55005500, 0x550000005500, 0x500050005000500, 0x1100110011001100]
def r44_goal : Nat := 0x100150001005500
def r44_rows : Fin 64 → Fin 64 := decodeRows 0x218000a3800029a000aba00031c000b3c00039e000bbe000
set_option maxHeartbeats 0 in
theorem r44_lower : LowerBin r44_mask r44_stock r44_goal 5 := by
  apply lowerBin_of_rowPull r44_rows (stock' := r6_stock)
  · have hall : r44_stock.all (fun w => availBF r6_stock
        (rowCanon r44_rows r44_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r44_rows r44_mask = r6_mask := by decide +kernel
    have hg : rowCanon r44_rows r44_mask r44_goal = r6_goal := by decide +kernel
    rw [hm, hg]
    exact r6_lower

def r45_mask : Nat := 0xf0f0f0f00f0f0f0f
def r45_stock : List Nat := [0xf0f0f0f, 0xf0f000000f0f, 0xf000f0000f000f, 0x3030303003030303, 0x5050505005050505]
def r45_goal : Nat := 0x1010500107070f
def r45_rows : Fin 64 → Fin 64 := decodeRows 0xffe104f7c104df6104d74104bee104b6c1049e61049641041046da1046581044d21044501042ca1042481040c2104040
set_option maxHeartbeats 0 in
theorem r45_lower : LowerBin r45_mask r45_stock r45_goal 10 := by
  apply lowerBin_of_rowPull r45_rows (stock' := r28_stock)
  · have hall : r45_stock.all (fun w => availBF r28_stock
        (rowCanon r45_rows r45_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r45_rows r45_mask = r28_mask := by decide +kernel
    have hg : rowCanon r45_rows r45_mask r45_goal = r28_goal := by decide +kernel
    rw [hm, hg]
    exact r28_lower

def r46_mask : Nat := 0x5050505050505050
def r46_stock : List Nat := [0x50505050, 0x505000005050, 0x50005000500050, 0x1010101010101010]
def r46_goal : Nat := 0x10105000505050
def r46_rows : Fin 64 → Fin 64 := decodeRows 0x10c18e92c9ae00000000000051c59ed3cdbe000000000000
set_option maxHeartbeats 0 in
theorem r46_lower : LowerBin r46_mask r46_stock r46_goal 5 := by
  apply lowerBin_of_rowPull r46_rows (stock' := r2_stock)
  · have hall : r46_stock.all (fun w => availBF r2_stock
        (rowCanon r46_rows r46_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r46_rows r46_mask = r2_mask := by decide +kernel
    have hg : rowCanon r46_rows r46_mask r46_goal = r2_goal := by decide +kernel
    rw [hm, hg]
    exact r2_lower

def r47_mask : Nat := 0xa0a0a0a0a0a0a0a
def r47_stock : List Nat := [0xa0a0a0a, 0xa0a00000a0a, 0xa000a000a000a, 0x202020202020202]
def r47_goal : Nat := 0x202020002020a
def r47_rows : Fin 64 → Fin 64 := decodeRows 0xef90006d9000cf10004d1000ae90002c90008e10000c1000
set_option maxHeartbeats 0 in
theorem r47_lower : LowerBin r47_mask r47_stock r47_goal 5 := by
  apply lowerBin_of_rowPull r47_rows (stock' := r6_stock)
  · have hall : r47_stock.all (fun w => availBF r6_stock
        (rowCanon r47_rows r47_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r47_rows r47_mask = r6_mask := by decide +kernel
    have hg : rowCanon r47_rows r47_mask r47_goal = r6_goal := by decide +kernel
    rw [hm, hg]
    exact r6_lower

def r48_mask : Nat := 0xff00ff0000000000
def r48_stock : List Nat := [0xff0000000000, 0xf000f0000000000, 0x3300330000000000, 0x5500550000000000]
def r48_goal : Nat := 0x100170000000000
def r48_rows : Fin 64 → Fin 64 := decodeRows 0xa29aab000000b2dbaf000000e39ebb000000f3dfbf
set_option maxHeartbeats 0 in
theorem r48_lower : LowerBin r48_mask r48_stock r48_goal 7 := by
  apply lowerBin_of_rowPull r48_rows (stock' := r13_stock)
  · have hall : r48_stock.all (fun w => availBF r13_stock
        (rowCanon r48_rows r48_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r48_rows r48_mask = r13_mask := by decide +kernel
    have hg : rowCanon r48_rows r48_mask r48_goal = r13_goal := by decide +kernel
    rw [hm, hg]
    exact r13_lower

def r49_mask : Nat := 0xffff000000000000
def r49_stock : List Nat := [0xff000000000000, 0xf0f000000000000, 0x3333000000000000, 0x5555000000000000]
def r49_goal : Nat := 0x117000000000000
def r49_rows : Fin 64 → Fin 64 := decodeRows 0xc31cb3000000d35db7000000e39ebb000000f3dfbf
set_option maxHeartbeats 0 in
theorem r49_lower : LowerBin r49_mask r49_stock r49_goal 7 := by
  apply lowerBin_of_rowPull r49_rows (stock' := r13_stock)
  · have hall : r49_stock.all (fun w => availBF r13_stock
        (rowCanon r49_rows r49_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r49_rows r49_mask = r13_mask := by decide +kernel
    have hg : rowCanon r49_rows r49_mask r49_goal = r13_goal := by decide +kernel
    rw [hm, hg]
    exact r13_lower

def r50_mask : Nat := 0x4444444444444444
def r50_stock : List Nat := [0x44444444, 0x444400004444, 0x44004400440044, 0x404040404040404]
def r50_goal : Nat := 0x4044400444444
def r50_rows : Fin 64 → Fin 64 := decodeRows 0x8a18e8aa9ae00000000000049a59ecbadbe000000000000
set_option maxHeartbeats 0 in
theorem r50_lower : LowerBin r50_mask r50_stock r50_goal 5 := by
  apply lowerBin_of_rowPull r50_rows (stock' := r2_stock)
  · have hall : r50_stock.all (fun w => availBF r2_stock
        (rowCanon r50_rows r50_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r50_rows r50_mask = r2_mask := by decide +kernel
    have hg : rowCanon r50_rows r50_mask r50_goal = r2_goal := by decide +kernel
    rw [hm, hg]
    exact r2_lower

def r51_mask : Nat := 0xcc00cc00cc00cc
def r51_stock : List Nat := [0xcc00cc, 0xcc000000cc, 0xc000c000c000c, 0x44004400440044]
def r51_goal : Nat := 0x400440044004c
def r51_rows : Fin 64 → Fin 64 := decodeRows 0xdf6000cf20009e60008e20000000000000000000000000005d60004d20001c60000c2000
set_option maxHeartbeats 0 in
theorem r51_lower : LowerBin r51_mask r51_stock r51_goal 6 := by
  apply lowerBin_of_rowPull r51_rows (stock' := r0_stock)
  · have hall : r51_stock.all (fun w => availBF r0_stock
        (rowCanon r51_rows r51_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r51_rows r51_mask = r0_mask := by decide +kernel
    have hg : rowCanon r51_rows r51_mask r51_goal = r0_goal := by decide +kernel
    rw [hm, hg]
    exact r0_lower

def r52_mask : Nat := 0x5555000055550000
def r52_stock : List Nat := [0x55550000, 0x55000000550000, 0x505000005050000, 0x1111000011110000]
def r52_goal : Nat := 0x115000001550000
def r52_rows : Fin 64 → Fin 64 := decodeRows 0x418000c3800049a000cba00051c000d3c00059e000dbe000
set_option maxHeartbeats 0 in
theorem r52_lower : LowerBin r52_mask r52_stock r52_goal 5 := by
  apply lowerBin_of_rowPull r52_rows (stock' := r6_stock)
  · have hall : r52_stock.all (fun w => availBF r6_stock
        (rowCanon r52_rows r52_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r52_rows r52_mask = r6_mask := by decide +kernel
    have hg : rowCanon r52_rows r52_mask r52_goal = r6_goal := by decide +kernel
    rw [hm, hg]
    exact r6_lower

def r53_mask : Nat := 0x2222222222222222
def r53_stock : List Nat := [0x22222222, 0x222200002222, 0x22002200220022, 0x202020202020202]
def r53_goal : Nat := 0x2020200020222
def r53_rows : Fin 64 → Fin 64 := decodeRows 0xf79000759000d71000551000b69000349000961000141000
set_option maxHeartbeats 0 in
theorem r53_lower : LowerBin r53_mask r53_stock r53_goal 5 := by
  apply lowerBin_of_rowPull r53_rows (stock' := r6_stock)
  · have hall : r53_stock.all (fun w => availBF r6_stock
        (rowCanon r53_rows r53_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r53_rows r53_mask = r6_mask := by decide +kernel
    have hg : rowCanon r53_rows r53_mask r53_goal = r6_goal := by decide +kernel
    rw [hm, hg]
    exact r6_lower

def r54_mask : Nat := 0xaa00aa00aa00aa
def r54_stock : List Nat := [0xaa00aa, 0xaa000000aa, 0xa000a000a000a, 0x22002200220022]
def r54_goal : Nat := 0x200020002002a
def r54_rows : Fin 64 → Fin 64 := decodeRows 0xdf59e55d51c5000000000000cf18e14d10c1000000000000
set_option maxHeartbeats 0 in
theorem r54_lower : LowerBin r54_mask r54_stock r54_goal 5 := by
  apply lowerBin_of_rowPull r54_rows (stock' := r2_stock)
  · have hall : r54_stock.all (fun w => availBF r2_stock
        (rowCanon r54_rows r54_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r54_rows r54_mask = r2_mask := by decide +kernel
    have hg : rowCanon r54_rows r54_mask r54_goal = r2_goal := by decide +kernel
    rw [hm, hg]
    exact r2_lower

def r55_mask : Nat := 0xc0c0c0c0c0c0c0c
def r55_stock : List Nat := [0xc0c0c0c, 0xc0c00000c0c, 0xc000c000c000c, 0x404040404040404]
def r55_goal : Nat := 0x404040004040c
def r55_rows : Fin 64 → Fin 64 := decodeRows 0xefa0006da000cf20004d2000aea0002ca0008e20000c2000
set_option maxHeartbeats 0 in
theorem r55_lower : LowerBin r55_mask r55_stock r55_goal 5 := by
  apply lowerBin_of_rowPull r55_rows (stock' := r6_stock)
  · have hall : r55_stock.all (fun w => availBF r6_stock
        (rowCanon r55_rows r55_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r55_rows r55_mask = r6_mask := by decide +kernel
    have hg : rowCanon r55_rows r55_mask r55_goal = r6_goal := by decide +kernel
    rw [hm, hg]
    exact r6_lower

def r56_mask : Nat := 0xff00ff0000ff00ff
def r56_stock : List Nat := [0xff00ff, 0xff00000000ff, 0xf000f00000f000f, 0x3300330000330033, 0x5500550000550055]
def r56_goal : Nat := 0x10017000057007f
def r56_rows : Fin 64 → Fin 64 := decodeRows 0x1208083208105208187208411208493208515208597208208a29208aab208b2d208baf208e39208ebb208f3d208fbf
set_option maxHeartbeats 0 in
theorem r56_lower : LowerBin r56_mask r56_stock r56_goal 10 := by
  apply lowerBin_of_rowPull r56_rows (stock' := r28_stock)
  · have hall : r56_stock.all (fun w => availBF r28_stock
        (rowCanon r56_rows r56_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r56_rows r56_mask = r28_mask := by decide +kernel
    have hg : rowCanon r56_rows r56_mask r56_goal = r28_goal := by decide +kernel
    rw [hm, hg]
    exact r28_lower

def r57_mask : Nat := 0xc0c0c0c0c0c0c0c0
def r57_stock : List Nat := [0xc0c0c0c0, 0xc0c00000c0c0, 0xc000c000c000c0, 0x4040404040404040]
def r57_goal : Nat := 0x4000404040
def r57_rows : Fin 64 → Fin 64 := decodeRows 0x18738f59779f9a7bafdb7fbf
set_option maxHeartbeats 0 in
theorem r57_lower : LowerBin r57_mask r57_stock r57_goal 5 := by
  apply lowerBin_of_rowPull r57_rows (stock' := r4_stock)
  · have hall : r57_stock.all (fun w => availBF r4_stock
        (rowCanon r57_rows r57_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r57_rows r57_mask = r4_mask := by decide +kernel
    have hg : rowCanon r57_rows r57_mask r57_goal = r4_goal := by decide +kernel
    rw [hm, hg]
    exact r4_lower

def r58_mask : Nat := 0x3333000033330000
def r58_stock : List Nat := [0x33330000, 0x33000000330000, 0x303000003030000, 0x1111000011110000]
def r58_goal : Nat := 0x113000001130000
def r58_bounds : List (Nat × List Nat × Nat × Nat) := []
theorem r58_sub : ∀ b ∈ r58_bounds, r58_mask &&& b.1 = b.1 := by
  have hall : r58_bounds.all (fun b => Nat.beq (Nat.land r58_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r58_goals : ∀ b ∈ r58_bounds, canon b.1 r58_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r58_bounds.all (fun b => Nat.beq (canonF b.1 r58_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r58_forest : Nat → Nat × Nat := unpackForestF 0x1ee 1 4
def r58_links : Nat → Nat → Option Nat := unpackLinksF 0x882 0x3ee 4 2 4 1 3
def r58_trace := dagTraceF r58_mask r58_stock 3 r58_forest
def r58_check : Nat → Bool := dagCheckNodeF r58_mask r58_goal r58_bounds 2 r58_trace r58_links
set_option maxHeartbeats 0 in
theorem r58_roots : dagCheckRootsF r58_mask r58_goal r58_bounds
    (dagRefF 2 r58_trace r58_links 0) r58_stock 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r58_b0 : treeBlockF 0 2 r58_check = true := by decide +kernel
theorem r58_nodes : ∀ i, 0 ≤ i → i < 2 → r58_check i = true :=
  blockSpec r58_b0
theorem r58_known : KnownBin r58_bounds :=
  knownNil
theorem r58_lower : LowerBin r58_mask r58_stock r58_goal 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r58_known r58_sub r58_goals r58_roots r58_nodes

def r59_mask : Nat := 0x3300330033003300
def r59_stock : List Nat := [0x33003300, 0x330000003300, 0x300030003000300, 0x1100110011001100]
def r59_goal : Nat := 0x100130001001300
def r59_rows : Fin 64 → Fin 64 := decodeRows 0xf7c000e78000b6c000a6800000000000000000000000000075c00065800034c000248000000000000000000000000
set_option maxHeartbeats 0 in
theorem r59_lower : LowerBin r59_mask r59_stock r59_goal 4 := by
  apply lowerBin_of_rowPull r59_rows (stock' := r58_stock)
  · have hall : r59_stock.all (fun w => availBF r58_stock
        (rowCanon r59_rows r59_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r59_rows r59_mask = r58_mask := by decide +kernel
    have hg : rowCanon r59_rows r59_mask r59_goal = r58_goal := by decide +kernel
    rw [hm, hg]
    exact r58_lower

def r60_mask : Nat := 0xf000f000f000f0
def r60_stock : List Nat := [0xf000f0, 0xf0000000f0, 0x30003000300030, 0x50005000500050]
def r60_goal : Nat := 0x10005000500070
def r60_rows : Fin 64 → Fin 64 := decodeRows 0xdf6000d740009e60009640000000000000000000000000005d60005540001c6000144000
set_option maxHeartbeats 0 in
theorem r60_lower : LowerBin r60_mask r60_stock r60_goal 6 := by
  apply lowerBin_of_rowPull r60_rows (stock' := r0_stock)
  · have hall : r60_stock.all (fun w => availBF r0_stock
        (rowCanon r60_rows r60_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r60_rows r60_mask = r0_mask := by decide +kernel
    have hg : rowCanon r60_rows r60_mask r60_goal = r0_goal := by decide +kernel
    rw [hm, hg]
    exact r0_lower

def r61_mask : Nat := 0xff000000ff0000
def r61_stock : List Nat := [0xff0000, 0xf0000000f0000, 0x33000000330000, 0x55000000550000]
def r61_goal : Nat := 0x17000000570000
def r61_rows : Fin 64 → Fin 64 := decodeRows 0x411000c31000493000cb3000515000d35000597000db7000
set_option maxHeartbeats 0 in
theorem r61_lower : LowerBin r61_mask r61_stock r61_goal 5 := by
  apply lowerBin_of_rowPull r61_rows (stock' := r6_stock)
  · have hall : r61_stock.all (fun w => availBF r6_stock
        (rowCanon r61_rows r61_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r61_rows r61_mask = r6_mask := by decide +kernel
    have hg : rowCanon r61_rows r61_mask r61_goal = r6_goal := by decide +kernel
    rw [hm, hg]
    exact r6_lower

def r62_mask : Nat := 0xf0f0f0f000000000
def r62_stock : List Nat := [0xf0f000000000, 0xf000f000000000, 0x3030303000000000, 0x5050505000000000]
def r62_goal : Nat := 0x10105000000000
def r62_rows : Fin 64 → Fin 64 := decodeRows 0x9259a7b2dbafd35db7f3dfbf
set_option maxHeartbeats 0 in
theorem r62_lower : LowerBin r62_mask r62_stock r62_goal 5 := by
  apply lowerBin_of_rowPull r62_rows (stock' := r4_stock)
  · have hall : r62_stock.all (fun w => availBF r4_stock
        (rowCanon r62_rows r62_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r62_rows r62_mask = r4_mask := by decide +kernel
    have hg : rowCanon r62_rows r62_mask r62_goal = r4_goal := by decide +kernel
    rw [hm, hg]
    exact r4_lower

def r63_mask : Nat := 0x3030303030303030
def r63_stock : List Nat := [0x30303030, 0x303000003030, 0x30003000300030, 0x1010101010101010]
def r63_goal : Nat := 0x10101000101030
def r63_rows : Fin 64 → Fin 64 := decodeRows 0xf7c00075c000d74000554000b6c00034c000964000144000
set_option maxHeartbeats 0 in
theorem r63_lower : LowerBin r63_mask r63_stock r63_goal 5 := by
  apply lowerBin_of_rowPull r63_rows (stock' := r6_stock)
  · have hall : r63_stock.all (fun w => availBF r6_stock
        (rowCanon r63_rows r63_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r63_rows r63_mask = r6_mask := by decide +kernel
    have hg : rowCanon r63_rows r63_mask r63_goal = r6_goal := by decide +kernel
    rw [hm, hg]
    exact r6_lower

def r64_mask : Nat := 0x3333333300000000
def r64_stock : List Nat := [0x333300000000, 0x33003300000000, 0x303030300000000, 0x1111111100000000]
def r64_goal : Nat := 0x113131300000000
def r64_rows : Fin 64 → Fin 64 := decodeRows 0x821a29c31e39000000000000925b2dd35f3d000000000000
set_option maxHeartbeats 0 in
theorem r64_lower : LowerBin r64_mask r64_stock r64_goal 5 := by
  apply lowerBin_of_rowPull r64_rows (stock' := r2_stock)
  · have hall : r64_stock.all (fun w => availBF r2_stock
        (rowCanon r64_rows r64_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r64_rows r64_mask = r2_mask := by decide +kernel
    have hg : rowCanon r64_rows r64_mask r64_goal = r2_goal := by decide +kernel
    rw [hm, hg]
    exact r2_lower

def r65_mask : Nat := 0xf000f000f000f00
def r65_stock : List Nat := [0xf000f00, 0xf0000000f00, 0x300030003000300, 0x500050005000500]
def r65_goal : Nat := 0x100070001000700
def r65_rows : Fin 64 → Fin 64 := decodeRows 0xefa000e78000aea000a680000000000000000000000000006da0006580002ca000248000000000000000000000000
set_option maxHeartbeats 0 in
theorem r65_lower : LowerBin r65_mask r65_stock r65_goal 4 := by
  apply lowerBin_of_rowPull r65_rows (stock' := r58_stock)
  · have hall : r65_stock.all (fun w => availBF r58_stock
        (rowCanon r65_rows r65_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r65_rows r65_mask = r58_mask := by decide +kernel
    have hg : rowCanon r65_rows r65_mask r65_goal = r58_goal := by decide +kernel
    rw [hm, hg]
    exact r58_lower

def r66_mask : Nat := 0xf0f0f0f00000000
def r66_stock : List Nat := [0xf0f00000000, 0xf000f00000000, 0x303030300000000, 0x505050500000000]
def r66_goal : Nat := 0x107070700000000
def r66_rows : Fin 64 → Fin 64 := decodeRows 0x821a29c31e390000000000008a3aabcb3ebb000000000000
set_option maxHeartbeats 0 in
theorem r66_lower : LowerBin r66_mask r66_stock r66_goal 5 := by
  apply lowerBin_of_rowPull r66_rows (stock' := r2_stock)
  · have hall : r66_stock.all (fun w => availBF r2_stock
        (rowCanon r66_rows r66_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r66_rows r66_mask = r2_mask := by decide +kernel
    have hg : rowCanon r66_rows r66_mask r66_goal = r2_goal := by decide +kernel
    rw [hm, hg]
    exact r2_lower

def r67_mask : Nat := 0xf0f0f0f0
def r67_stock : List Nat := [0xf0f0, 0xf000f0, 0x30303030, 0x50505050]
def r67_goal : Nat := 0x505070
def r67_rows : Fin 64 → Fin 64 := decodeRows 0x7de00075c0005d60005540003ce00034c0001c6000144000
set_option maxHeartbeats 0 in
theorem r67_lower : LowerBin r67_mask r67_stock r67_goal 5 := by
  apply lowerBin_of_rowPull r67_rows (stock' := r6_stock)
  · have hall : r67_stock.all (fun w => availBF r6_stock
        (rowCanon r67_rows r67_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r67_rows r67_mask = r6_mask := by decide +kernel
    have hg : rowCanon r67_rows r67_mask r67_goal = r6_goal := by decide +kernel
    rw [hm, hg]
    exact r6_lower

def r68_mask : Nat := 0xffff0000
def r68_stock : List Nat := [0xff0000, 0xf0f0000, 0x33330000, 0x55550000]
def r68_goal : Nat := 0x1570000
def r68_rows : Fin 64 → Fin 64 := decodeRows 0x7de75c6da6580000000000005d65544d2450000000000000
set_option maxHeartbeats 0 in
theorem r68_lower : LowerBin r68_mask r68_stock r68_goal 5 := by
  apply lowerBin_of_rowPull r68_rows (stock' := r2_stock)
  · have hall : r68_stock.all (fun w => availBF r2_stock
        (rowCanon r68_rows r68_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r68_rows r68_mask = r2_mask := by decide +kernel
    have hg : rowCanon r68_rows r68_mask r68_goal = r2_goal := by decide +kernel
    rw [hm, hg]
    exact r2_lower

def r69_mask : Nat := 0xf0f00000f0f0000
def r69_stock : List Nat := [0xf0f0000, 0xf0000000f0000, 0x303000003030000, 0x505000005050000]
def r69_goal : Nat := 0x107000001070000
def r69_rows : Fin 64 → Fin 64 := decodeRows 0xefa000e78000cf2000c700000000000000000000000000006da0006580004d2000450000000000000000000000000
set_option maxHeartbeats 0 in
theorem r69_lower : LowerBin r69_mask r69_stock r69_goal 4 := by
  apply lowerBin_of_rowPull r69_rows (stock' := r58_stock)
  · have hall : r69_stock.all (fun w => availBF r58_stock
        (rowCanon r69_rows r69_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r69_rows r69_mask = r58_mask := by decide +kernel
    have hg : rowCanon r69_rows r69_mask r69_goal = r58_goal := by decide +kernel
    rw [hm, hg]
    exact r58_lower

def r70_mask : Nat := 0xff00ff00000000
def r70_stock : List Nat := [0xff00000000, 0xf000f00000000, 0x33003300000000, 0x55005500000000]
def r70_goal : Nat := 0x17005700000000
def r70_rows : Fin 64 → Fin 64 := decodeRows 0x821000c310008a3000cb3000925000d350009a7000db7000
set_option maxHeartbeats 0 in
theorem r70_lower : LowerBin r70_mask r70_stock r70_goal 5 := by
  apply lowerBin_of_rowPull r70_rows (stock' := r6_stock)
  · have hall : r70_stock.all (fun w => availBF r6_stock
        (rowCanon r70_rows r70_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r70_rows r70_mask = r6_mask := by decide +kernel
    have hg : rowCanon r70_rows r70_mask r70_goal = r6_goal := by decide +kernel
    rw [hm, hg]
    exact r6_lower

theorem cert_known : KnownBin cert_bounds :=
  knownCons r10_lower (
  knownCons r11_lower (
  knownCons r12_lower (
  knownCons r9_lower (
  knownCons r15_lower (
  knownCons r16_lower (
  knownCons r17_lower (
  knownCons r29_lower (
  knownCons r30_lower (
  knownCons r31_lower (
  knownCons r32_lower (
  knownCons r36_lower (
  knownCons r35_lower (
  knownCons r43_lower (
  knownCons r14_lower (
  knownCons r44_lower (
  knownCons r5_lower (
  knownCons r45_lower (
  knownCons r33_lower (
  knownCons r46_lower (
  knownCons r1_lower (
  knownCons r18_lower (
  knownCons r47_lower (
  knownCons r48_lower (
  knownCons r13_lower (
  knownCons r49_lower (
  knownCons r50_lower (
  knownCons r51_lower (
  knownCons r52_lower (
  knownCons r53_lower (
  knownCons r54_lower (
  knownCons r55_lower (
  knownCons r3_lower (
  knownCons r56_lower (
  knownCons r28_lower (
  knownCons r57_lower (
  knownCons r0_lower (
  knownCons r59_lower (
  knownCons r60_lower (
  knownCons r61_lower (
  knownCons r62_lower (
  knownCons r4_lower (
  knownCons r8_lower (
  knownCons r63_lower (
  knownCons r64_lower (
  knownCons r65_lower (
  knownCons r23_lower (
  knownCons r66_lower (
  knownCons r7_lower (
  knownCons r34_lower (
  knownCons r6_lower (
  knownCons r67_lower (
  knownCons r68_lower (
  knownCons r58_lower (
  knownCons r69_lower (
  knownCons r70_lower (
  knownCons r2_lower (
  knownNil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem binaryLower : LowerBin cert_mask cert_stock cert_goal 13 :=
  cert_lower cert_known


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev X := Fin 6 → Bool
abbrev F := X → Bool

def target : F := fun x => Nat.testBit 18368186892755183744
  (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def witness : Circuit :=
  ⟨[
    ⟨.and, [3, 4]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [5, 7]⟩,
    ⟨.and, [5, 7]⟩,
    ⟨.or, [0, 9]⟩,
    ⟨.and, [0, 6]⟩,
    ⟨.and, [2, 10]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.or, [6, 13]⟩,
    ⟨.or, [12, 14]⟩,
    ⟨.or, [2, 11]⟩,
    ⟨.and, [14, 16]⟩,
    ⟨.or, [1, 17]⟩,
    ⟨.and, [15, 18]⟩], 19⟩

theorem witness_mono : Monotone2 witness := by simp [Monotone2, witness]

theorem witness_size : witness.size = 14 := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem witness_eval : ∀ x : X, witness.eval (List.ofFn x) = target x := by
  decide +kernel

theorem binaryLowerRoot : LowerBin fullMask rootStock (canon fullMask 18368186892755183744) 13 := by
  intro vs hbuild hhit
  have hstock : ∀ w ∈ rootStock, w ∈ cert_stock := by
    have hall : rootStock.all (fun i => cert_stock.contains i) = true := by decide +kernel
    intro w hw
    exact List.contains_iff_mem.mp (List.all_eq_true.mp hall w hw)
  have hbuild' := builds_weaken hstock hbuild
  have hhit' : Avail (vs ++ cert_stock) (canon fullMask 18368186892755183744) :=
    avail_weaken (fun w hw => by
      rcases List.mem_append.mp hw with hv | hs
      · exact List.mem_append_left _ hv
      · exact List.mem_append_right _ (hstock w hs)) hhit
  exact binaryLower vs hbuild' hhit'

end PEqualNP.Outside.L_meta_48488

theorem PEqualNP.Outside.L_meta_48488 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6
      (fun x : Fin 6 → Bool => Nat.testBit (4276676776 * 2 ^ 32 + 4272466048)
        (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s →
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 4272466048)
        (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_48488.table2_from_lowerBin 18368186892755183744 14
    PEqualNP.Outside.L_meta_48488.binaryLowerRoot PEqualNP.Outside.L_meta_48488.witness.gates PEqualNP.Outside.L_meta_48488.witness.output
    PEqualNP.Outside.L_meta_48488.witness_size PEqualNP.Outside.L_meta_48488.witness_mono PEqualNP.Outside.L_meta_48488.witness_eval
