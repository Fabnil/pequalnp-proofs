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

def dagCheckChildren (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
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
                        dagLocal mask goal bounds ch || ref (makeToken a b op keep) ch))))))))

def dagCheckNode (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some st => dagCheckChildren mask goal bounds (dagRef count states links (i + 1)) st

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

def dagCheckChildrenF (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
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
                          Bool.rec (dagLocalF mask goal bounds ch) true (ref tok ch)))
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

theorem dagCheckChildrenF_eq {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
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
        congr 1; funext a
        simp only [getDN_eq]
        congr 1; funext b
        congr 1; funext op
        simp only [binOpF_eq, forceW_eq]
        cases Nat.beq (binOp mask op (ws.getD a 0) (ws.getD b 0)) 0
        · cases ws.contains (binOp mask op (ws.getD a 0) (ws.getD b 0))
          · dsimp only; simp only [Bool.false_or]
            congr 1; funext keep
            simp only [insertSortedF_eq, dropValF_eq, forceWs_eq, makeTokenF_eq, dagLocalF_eq hgoals]
            cases Nat.beq (keep &&& 1) 1 <;> cases Nat.beq ((keep >>> 1) &&& 1) 1
            all_goals dsimp only
            all_goals simp only [Bool.false_eq_true, ite_true, ite_false, Bool.not_true, Bool.not_false]
            all_goals cases Nat.blt fuel _
            all_goals try rfl
            all_goals cases ref (makeToken a b op keep) _ <;> cases dagLocal mask goal bounds _ <;> rfl
          · rfl
        · rfl
    · rfl
  · rfl

def dagCheckNodeF (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some st => dagCheckChildrenF mask goal bounds (dagRefF count states links (Nat.add i 1)) st

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
    rw [href]; exact dagCheckChildrenF_eq hgoals _ st

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

def checkNodeVia (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option DagState) (ref : Nat → Nat → DagState → Bool) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some st => dagCheckChildren mask goal bounds (ref (i + 1)) st

theorem dagAllNodesRef {mask goal fuel count : Nat} {stock : List Nat}
    {boundsFor : Nat → List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {ref : Nat → Nat → DagState → Bool}
    (hgm : Masked mask goal) (hknown : ∀ i, KnownBin (boundsFor i))
    (hsub : ∀ i, ∀ b ∈ boundsFor i, mask &&& b.1 = b.1) (snd : stock.Nodup)
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
          · have hopen := dagLocal_open (state := (rem - 1, ws', (z, x, y) :: hist)) hgm (hknown i) (hsub i) hnd' (k := k') (by omega) hlive'
            rw [hopen] at hloc; exact Bool.noConfusion hloc
          · obtain ⟨dest, saved, hdest, htr', heq, moved⟩ :=
              good (i + 1) (makeToken a b op keep) _ href
            exact ih (rem - 1) (by omega) dest saved hdest htr' heq k' (by omega) (moved k' hlive')

theorem lowerDagRef {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {boundsFor : Nat → List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {ref : Nat → Nat → DagState → Bool}
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hroots : dagCheckRoots mask goal bounds
      (ref 0) stock fuel = true)
    (hknownFor : ∀ i, KnownBin (boundsFor i))
    (hsubFor : ∀ i, ∀ b ∈ boundsFor i, mask &&& b.1 = b.1)
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

def checkNodeViaF (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option DagState) (ref : Nat → Nat → DagState → Bool) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some st => dagCheckChildrenF mask goal bounds (ref (Nat.add i 1)) st

theorem checkNodeViaF_eq {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (states : Nat → Option DagState) (ref : Nat → Nat → DagState → Bool) (i : Nat) :
    checkNodeViaF mask goal bounds states ref i = checkNodeVia mask goal bounds states ref i := by
  unfold checkNodeViaF checkNodeVia
  cases states i with
  | none => rfl
  | some st => exact dagCheckChildrenF_eq hgoals _ st

theorem lowerDagRefF {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)} {profile : Nat → Nat}
    {forest : Nat → Nat × Nat} {ref : Nat → Nat → DagState → Bool}
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true) (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (good : RefSound mask goal count (dagTraceF mask stock fuel forest) ref)
    (hroots : dagCheckRootsF mask goal bounds (ref 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → checkNodeViaF mask goal (chooseBounds bounds (profile i))
      (dagTraceF mask stock fuel forest) ref i = true) :
    LowerBin mask stock goal (fuel + 1) := by
  have htr : dagTraceF mask stock fuel forest = dagTrace mask stock fuel forest := by
    funext i; exact dagTraceF_eq mask stock fuel forest i
  rw [htr] at good hnodes
  rw [dagCheckRootsF_eq hgoals] at hroots
  have mem i b (hb : b ∈ chooseBounds bounds (profile i)) := chooseBounds_mem (profile i) hb
  refine lowerDagRef hgm hgnz hcs snd hknown hsub hroots
    (boundsFor := fun i => chooseBounds bounds (profile i))
    (fun i b hb => hknown b (mem i b hb)) (fun i b hb => hsub b (mem i b hb)) good ?_
  intro i hlo hhi
  have h := hnodes i hlo hhi
  rwa [checkNodeViaF_eq (fun b hb => hgoals b (mem i b hb))] at h



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

def unpackPaged (pages : List Nat) (width pageBits i : Nat) : Nat :=
  unpackF (getDN pages (Nat.shiftRight i pageBits)) width
    (Nat.land i (Nat.sub (Nat.shiftLeft 1 pageBits) 1))

def unpackForestPaged (row : Nat → Nat) (tBits : Nat) : Nat → Nat × Nat := fun i =>
  let code := row i
  (Nat.shiftRight code tBits, Nat.land code (Nat.sub (Nat.shiftLeft 1 tBits) 1))

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
  {p : Equiv.Perm (Fin 64) // rowPull p mask = mask ∧ rowCanon p mask goal = goal}

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
      eqListN (rowSort (rowCanon p.val mask) st.2.1) saved.2.1

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
      have moved := liveBin_rowSymmetry p.val hm p.property.1 p.property.2 live hcanonical
      rw [← rowSort_finset, hc.2] at moved
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
def cert_bounds : List (Nat × List Nat × Nat × Nat) := [(0xf0f0f0f0f0f0f0f0, [0xf0f0f0f0, 0xf0f00000f0f0, 0xf000f000f000f0, 0x3030303030303030, 0x5050505050505050], 9, 0x10105000505070), (0xcccccccccccccccc, [0xcccccccc, 0xcccc0000cccc, 0xcc00cc00cc00cc, 0xc0c0c0c0c0c0c0c, 0x4444444444444444], 9, 0x404440044444c), (0xff00ff00ff00ff, [0xff00ff, 0xff000000ff, 0xf000f000f000f, 0x33003300330033, 0x55005500550055], 9, 0x1700570057007f), (0xffff0000ffff, [0xffff, 0xff000000ff, 0xf0f00000f0f, 0x333300003333, 0x555500005555], 9, 0x17570000577f), (0x5555555555555555, [0x55555555, 0x555500005555, 0x55005500550055, 0x505050505050505, 0x1111111111111111], 8, 0x115155501555555), (0xaaaaaaaaaaaaaaaa, [0xaaaaaaaa, 0xaaaa0000aaaa, 0xaa00aa00aa00aa, 0xa0a0a0a0a0a0a0a, 0x2222222222222222], 8, 0x202020002022a), (0xf0f0f0f0f0f0f0f, [0xf0f0f0f, 0xf0f00000f0f, 0xf000f000f000f, 0x303030303030303, 0x505050505050505], 8, 0x10707070107070f), (0xffff00000000ffff, [0xffff, 0xff0000000000ff, 0xf0f000000000f0f, 0x3333000000003333, 0x5555000000005555], 10, 0x11700000000577f), (0xff00ff00ff00ff00, [0xff00ff00, 0xff000000ff00, 0xf000f000f000f00, 0x3300330033003300, 0x5500550055005500], 8, 0x100170001005700), (0x3333333333333333, [0x33333333, 0x333300003333, 0x33003300330033, 0x303030303030303, 0x1111111111111111], 8, 0x113131301131333), (0xffff0000ffff0000, [0xffff0000, 0xff000000ff0000, 0xf0f00000f0f0000, 0x3333000033330000, 0x5555000055550000], 8, 0x117000001570000), (0xffffffff00000000, [0xffff00000000, 0xff00ff00000000, 0xf0f0f0f00000000, 0x3333333300000000, 0x5555555500000000], 9, 0x117175700000000), (0xffffffff, [0xffff, 0xff00ff, 0xf0f0f0f, 0x33333333, 0x55555555], 9, 0x157577f), (0x55555555aaaaaaaa, [0xaaaaaaaa, 0x55550000aaaa, 0x55005500aa00aa, 0x50505050a0a0a0a, 0x1111111122222222], 10, 0x11515550002022a), (0x5555555500000000, [0x555500000000, 0x55005500000000, 0x505050500000000, 0x1111111100000000], 7, 0x115155500000000), (0x5500550055005500, [0x55005500, 0x550000005500, 0x500050005000500, 0x1100110011001100], 5, 0x100150001005500), (0xff000000ff, [0xff, 0xf0000000f, 0x3300000033, 0x5500000055], 5, 0x570000007f), (0xf0f0f0f00f0f0f0f, [0xf0f0f0f, 0xf0f000000f0f, 0xf000f0000f000f, 0x3030303003030303, 0x5050505005050505], 10, 0x1010500107070f), (0xaaaaaaaa, [0xaaaa, 0xaa00aa, 0xa0a0a0a, 0x22222222], 7, 0x2022a), (0x5050505050505050, [0x50505050, 0x505000005050, 0x50005000500050, 0x1010101010101010], 5, 0x10105000505050), (0xf0f00000f0f0, [0xf0f0, 0xf0000000f0, 0x303000003030, 0x505000005050], 6, 0x105000005070), (0x33333333, [0x3333, 0x330033, 0x3030303, 0x11111111], 7, 0x1131333), (0xa0a0a0a0a0a0a0a, [0xa0a0a0a, 0xa0a00000a0a, 0xa000a000a000a, 0x202020202020202], 5, 0x202020002020a), (0xff00ff0000000000, [0xff0000000000, 0xf000f0000000000, 0x3300330000000000, 0x5500550000000000], 7, 0x100170000000000), (0xf0f0f0f, [0xf0f, 0xf000f, 0x3030303, 0x5050505], 7, 0x107070f), (0xffff000000000000, [0xff000000000000, 0xf0f000000000000, 0x3333000000000000, 0x5555000000000000], 7, 0x117000000000000), (0x4444444444444444, [0x44444444, 0x444400004444, 0x44004400440044, 0x404040404040404], 5, 0x4044400444444), (0xcc00cc00cc00cc, [0xcc00cc, 0xcc000000cc, 0xc000c000c000c, 0x44004400440044], 6, 0x400440044004c), (0x5555000055550000, [0x55550000, 0x55000000550000, 0x505000005050000, 0x1111000011110000], 5, 0x115000001550000), (0x2222222222222222, [0x22222222, 0x222200002222, 0x22002200220022, 0x202020202020202], 5, 0x2020200020222), (0xaa00aa00aa00aa, [0xaa00aa, 0xaa000000aa, 0xa000a000a000a, 0x22002200220022], 5, 0x200020002002a), (0xc0c0c0c0c0c0c0c, [0xc0c0c0c, 0xc0c00000c0c, 0xc000c000c000c, 0x404040404040404], 5, 0x404040004040c), (0xaaaa0000aaaa, [0xaaaa, 0xaa000000aa, 0xa0a00000a0a, 0x222200002222], 5, 0x2020000022a), (0xff00ff0000ff00ff, [0xff00ff, 0xff00000000ff, 0xf000f00000f000f, 0x3300330000330033, 0x5500550000550055], 10, 0x10017000057007f), (0xcccccccc33333333, [0x33333333, 0xcccc00003333, 0xcc00cc00330033, 0xc0c0c0c03030303, 0x4444444411111111], 10, 0x4044401131333), (0xc0c0c0c0c0c0c0c0, [0xc0c0c0c0, 0xc0c00000c0c0, 0xc000c000c000c0, 0x4040404040404040], 5, 0x4000404040), (0xcccc0000cccc, [0xcccc, 0xcc000000cc, 0xc0c00000c0c, 0x444400004444], 6, 0x4440000444c), (0x3300330033003300, [0x33003300, 0x330000003300, 0x300030003000300, 0x1100110011001100], 4, 0x100130001001300), (0xf000f000f000f0, [0xf000f0, 0xf0000000f0, 0x30003000300030, 0x50005000500050], 6, 0x10005000500070), (0xff000000ff0000, [0xff0000, 0xf0000000f0000, 0x33000000330000, 0x55000000550000], 5, 0x17000000570000), (0xf0f0f0f000000000, [0xf0f000000000, 0xf000f000000000, 0x3030303000000000, 0x5050505000000000], 5, 0x10105000000000), (0xffff, [0xff, 0xf0f, 0x3333, 0x5555], 5, 0x577f), (0xffff00000000, [0xff00000000, 0xf0f00000000, 0x333300000000, 0x555500000000], 5, 0x175700000000), (0x3030303030303030, [0x30303030, 0x303000003030, 0x30003000300030, 0x1010101010101010], 5, 0x10101000101030), (0x3333333300000000, [0x333300000000, 0x33003300000000, 0x303030300000000, 0x1111111100000000], 5, 0x113131300000000), (0xf000f000f000f00, [0xf000f00, 0xf0000000f00, 0x300030003000300, 0x500050005000500], 4, 0x100070001000700), (0xcccccccc00000000, [0xcccc00000000, 0xcc00cc00000000, 0xc0c0c0c00000000, 0x4444444400000000], 5, 0x4044400000000), (0xf0f0f0f00000000, [0xf0f00000000, 0xf000f00000000, 0x303030300000000, 0x505050500000000], 5, 0x107070700000000), (0xff000000ff00, [0xff00, 0xf0000000f00, 0x330000003300, 0x550000005500], 5, 0x170000005700), (0xff00ff, [0xff, 0xf000f, 0x330033, 0x550055], 5, 0x57007f), (0xcccccccc, [0xcccc, 0xcc00cc, 0xc0c0c0c, 0x44444444], 5, 0x44444c), (0xf0f0f0f0, [0xf0f0, 0xf000f0, 0x30303030, 0x50505050], 5, 0x505070), (0xffff0000, [0xff0000, 0xf0f0000, 0x33330000, 0x55550000], 5, 0x1570000), (0x3333000033330000, [0x33330000, 0x33000000330000, 0x303000003030000, 0x1111000011110000], 4, 0x113000001130000), (0xf0f00000f0f0000, [0xf0f0000, 0xf0000000f0000, 0x303000003030000, 0x505000005050000], 4, 0x107000001070000), (0xff00ff00000000, [0xff00000000, 0xf000f00000000, 0x33003300000000, 0x55005500000000], 5, 0x17005700000000), (0xff00ff00, [0xff00, 0xf000f00, 0x33003300, 0x55005500], 5, 0x1005700)]
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
def cert_forest : Nat → Nat × Nat := unpackForestPaged (unpackPaged [
    0x3a696074d1c0f62a01d34303a47e0748dc0083701c37c02069606d5c0081a381a4600328a8064df0081a181837c02047e050d7c0b63601435b0286ae054d700a6320143530278e00408dc085b001147c0226e0044d20084a78100360020cc03d1a0056b780e458015ac60351a00553780c4580154be02d1800552b8010460134c80071bc04522001c6300f48800716c03536001c5700aac801491000e298041340076860061b80123100245a00308c0040f80040980003f,
    0x7f0c80051bc1f42200146307b08800516c1e436001457076ac80ec11000a29839c740730880cd16c1c33c03806c0668ae0d95901b23a0360440668a60ced2c19da38344540676860cc190009b7831c740630e80b99fc1823203006405cce60bb5bc176b182e04400269e0b35e01643a02967f056ad00ac19014b39829d6f053ac60a4170009a382803404d68609c0d01351f80116e04b0a809497c008a3023a4404708808314c111b20220340436860829b81052300113e,
    0xbf6a41789bc2f12f85e2570af08c1749902c23785c2440b08c616c9102c22d85a26c0b08ae1635902c5220584530af07c00206c20635840c530ab6a815558c205b585448c0a78a6102d9c2963205267b08169e144d902873d840b4309d8a613ad3c275a1840a6a09547e134d302551d84aa3709747812cd102551984a14408d8a6124510235a7847a5f08f4a611c4d0235a1840a62087ad610edac21db3843b5f0876a6102928214a204146b08328810514c20519000817,
    0xaf8ae1fc1703f2b207e0440af8a61f31d03e422075c5b0f6cf01ec1b03ae2b87a05c0f1ac81e31d03c422075c530ec6961d8d1c3b62a0763430eb0c815edbc3a23a0740740e1cfe1cb19039432070e730e2ade1c558c38422057b4f0deaf01bc1d035f3f86dd680db0c81af9cc362b786c5630d70b815ed1c341a58683470d38a81a0d0c3411f8682370af0dc19cdf0311a58665700c468e193150325be0623430c76f81888fc316380622370af0cc1795bc2f2b185e352,
    0x13f288210d3c4f1b209e164139cf62755ac4e49a0843431376c8264d0c4d5b209923f1334c82648cc420b709734312e47e25c8cc420b3096458123ad625497048d358944701234ce24d16048d2f89225c1234a62105184852208f46b11f48823d14c4209f08b94411b0982308dc4649288c03611708821d14c44ca208a35f11308821cd3c4412208804410f8a621c0f8420310860541096be2141584241f08404a00103e20c1902be378820440af8c62041102be2d88006c,
    0x17e6922fcd205da298bcd6217aac02f48d05e6350bb34b177adc2ecd0c5d4260aaa371686a42e51605a0af8b84601682ae2d897c5b5b60b625716827a2d31885a5a80b412715508c2cc51055a2d8b216c1568ae2c3590584a20ab45315f2882acd3c574ae0ab3471578b62af15c562b20ac3481578a62ac8d8554170008531532882111ac544a208445314e6a829c55052eb18a645314b268210dac522460a41441458a628cd0c514be0843671428c82845904ff3d8a056b,
    0x1bd69e37c5706f5a38de02e0010b63741105562d8dc06c1558ae36c1706ceb20da1371b30882ab14c6c6320d536f1ab6be356d5c6b5aa0d5a5f1ab46e354110555278d3d681a70c8330dbc694270d25701986ce33316c666298cfc5919f8b033297c672308ce4601994ae3355a8665278cc05c15548e32b1606542a0bad6b19206c3240d0642380c807c175ace31a0d86341a0c5c6018b0d830f9d061e2c0c434a1870a82eb58c615a48bb45b1836c22ed15c605a88bf564,
    0x1ff4cc3fc4907f4b30f79471fb8d03e15bc7e6380fbd761f78b03e15ac7d2390fa4701f0ace3e51607c2b18f836a1ef28c00248c6f22d8de4571ebac837914c7a6320f436f1bc49e3cd5a0789b78f204e1e3ae03c4d9c6f1238f04581d7ad63bc0d8776380ebd671db06c3b51807633a0ec4581d7ac63788dc755aa0ea25f1d027e3a4d20746298e81271bc2dc39d160724af8e64601c92ae394d40724938de0461c728837b16c714b60dec571c2ac83845106f6298e0144,
    0x23f8c84775c88f23c11e46823b6fc45914c8da2d91b4532378a446cd388b1b511724f22e496464d408b923917a6c22f49845c90c8b5301163661fd4684515948a23c1144681fd2fc4295f48974610a56f222b18445160852b190a4702148c043d5888522d10ac6d21baf842b17c8623e10c3482158a642d148855a510a1241fd2ec4251c08273b10803620f8e04135d8835aa104c722098d0413160825bd0fe96e1fe8f43fd1807f9bd1025701fe6ec3feda87fd35100460,
    0x27eb104fd5e09f6470fed63278ad64f158c9e6b113c45e1fd8f43fb1d89b635136c6926d8d04db1989b5b5136b6626e4b04dc9509b4b311656f26a8b24d51608b2b592f47126726c4bd1c097d2692fa492632984be91497d2093014025f24c4bc9c08b2b392d57e25a8b24b51608b2b191646e2576cc4591ac8b235129c6c2534c0459198945b311646322c8c448f9f891f39123d7a247ae44931e092634123b7e2476e445916c916b111645a22c8ac4779f89063211dd7a,
    0x2bd0cc57c920af42f15e0441ef29e574590aceb795c1542b3ad656c5f0aceb395a1542b3ac63de528aa6bd154d792a9af05535d8aa63d154c762aa6d0554d90aa4bb0fee7f2a6ad254d5a07f73d9515812a328c5456007f73b94f68e29ead253d5a07f73994e1641fdafc5351d87f6bd8fed7a296af852c5f07f6bb14a4761fdae63fb5c8a2bc714578228ad14515a08a32c414657828a91c5152087f6b59446721fdad450c5b07f6b313ef8e283ae84fba28a06ba13ee82,
    0x2ff9185799dcbeb4717d5642fa8c85f4190af33995e5762bc8fc5791d8af233178c662f18c85e2d98bc5b216956f2ef6a85a55acba5be1752392ea46a5d44b8ba5381695672e4afc5c9150b91aa1720542d2ac65bc93cb792596f2472df4d85bc90cb75301694662d26dc5aa93cb552596aa472d64d85ac090b552196a2602d26cc5a4d58af11a167c642cf6e85785f8b2a3e16536c2ca6ac5941f0af0bb16447c2c58ec58adf8b15b215e16e2bdad658516caf492160260,
    0x33f2486485b8ca5b899dd8033b718652d2cce6c0194b473378e066b150cd5c6194b4332a4c26631c0cc53e19523b32f8e06548dccb5b0195b4432b4f86548ccca49219207e32568664c8ccc949219207c1ef2ce642df0c85ab18b34b31fae062cd1cc723018e34e3178a862edf0c5db618c26031706862cd0c7bcb318a14430a8b66245b0c2a2b98815c30cac861cd34c362a18614430a8a66145107bcb1181d76303ae86071d8c0e3a1824643032ec5799fcc063215e67b,
    0x37d8fa6fd9c0df62a9a835f37b6c86ed5f4dd9be1bc5703766ac6ec0d0d41a99b857e370ae46e0df8dc1be1b83563506966d15f8db6361b4579368ae46d15c4da4a31b457035068e6cd1f0d463f1a8c7c35c8dc6c5170d72349ae46235c8c26bc518d72301ae34e3518a86a2df8d60af1ac05e3516f86ac8e0d56b71a8b6c3524c46a4980d441a1a834332446869ce30cfda59a658033f68e6951c0d222a1a438c33f6866808ecd16381a02373436c0682d10d053e1a0233,
    0x3bdb1a77de00ef6b299246f3bb8e876da34eda461dc6803b68cc76c110c92319d7e8e3b331875fa08ebe471d7c8c3af8cc64916ce9b471d657c3a6d1274da08e9b409d41563a6d0074c5b8c922b9d258c38fb1c71f630e6abf1d056c39aaf27355c8e6ab89cd57039a8bc734578e3eb21c7c8e397af872a5b8e54371c7c8c393cfc71f1f0e41b91c837038f08864914ce36b21c5c7d38b8aa6a0dbcd41b69c3c643876c87075f4e0eb89c24703836ac6a0d8cdf6be1c0564,
    0x3e48ca7fd198f922d9fde793fb2dc7c915cfdeb49fbc5e3f72bc7ed590f92299f8a4f3f14967e291cfc5219f82603e56aa7dcd58f95a59f5d693eb2bc7cad1cf9e2c9f3b4e3e729c7cd150f95a19f22341ef2de7c4d90f6da59f05683db68e7b9150f71ba1ee3643db6863de5b8f62331ec1443d08b67ac5b0f422b9ea45e3d1ac87a2510f44221e84531ef2d479d9d0f32c69e65653248fe6491f4f22ba1e44743c3d1a787a04f16c01e1c663c33186491ccef7461e0674,
    0x433ade87cd510ceb5a1dc7c43b6f886759d0de2a21bb544370a886758d0cdb7219b564334c48048fd0c532213d6f42f4a884f5ad0b53e213d6742b4a884f58d09d372144624274ac8048ed0963420dd6f4238b08375ad0863820dd6741f8b083758d06e3120e56a41b8b48048dd0623220c264403ade82c95100eb5a0a27c403ace820951044a6208054403ac6806db903632a01a6e40b8d480695901a2fa0345b4068ae80d14d00c9220245b4030488048cd004968f7a34,
    0x47c8c88fd1611f22a23e3644786868f49711e519a3c0544024be8ec9111922da3a26c4648ae8e49711bab223724446f2788dc11119229a3635246448c8ced2d19da3a344544676868c8491195a1a320244024b68b2db5185be22cb4b45fae08b2d1d16a2a22d37c45a6d88b40d1165a1a0125745748888516d15536221457451ac88a51511452222145344a696894d1d12e2a22634444b468894d0d109b222435a44248c886d2d10da3a2245444368688449100929a20364,
    0x40168e97c53d28e2a251b6e4bb4c0946d9928c9aa52a5b4aa48a9548f52d52225512a4b12729620792c4092551284af2509540a92b40c2550264ab4b495409129529a5336a4a64dc94c99929417a519344a3068802d0d2762da4ec5749d8aa93a96d2752ba0135f49b6ac804d6d25e36a4ba6c4974c0804d5d24db7249b56493068804d4d241b724835640269691a97d23529a0134748969c91293d22521a434544866dc90c0d1009a1a3c3554836c88f0d2d206b423c347,
    0x4fe4c09fc5b5005aba7e3544c8ad69f0df13e51ca7c2704c8ace9e0d7d3d51c27835b4f32d89e0d5d3c49a2783534e66d89ce93d39d25a75b5c4eb2b89ce91d3a1222741244e74869cc9813223326436e4c86ac9904d538524a65c5b4de4c29bc58132e2ba6a93f4d52769b49013549ba6c13c4d52669aa4bd35491a6a1504cb6ac9a458134633265a4b4cf2c0999199335ab2661284cb4869904d13262da640344016a6986db930db3261b564c326a802d2d300afa6015d,
    0x53549ea6a92d4ee3e29dc7053b2b8a6a91d4d93e29c56c5364d8a6c4914d521a7f2625334b2a0117d401af297b6e52f28aa0093d4aa3729535d52a4aca5449540125a8bd695176dca4d5a145daf28ba49522ad0a4497145caf28b95d51f4bca2e57145ca928dd6851b0b8a2e179461ae28c15c5170a4a0091d43a3728a25c50e6aaa1c9b14391f28712550f6bca1c49140121a8435e5086b4a10d59421a928425650025ea02d694052f280a5a5014aca0294940497280127,
    0x57e6d6afcd8d5f4a20f7c5b5772deaee5b55e2b3abc0565772d83df15d5d4b22afc7e5732f8abf1d957ca2ab0b6b5676aaaced355b51c2b393a567074ad40a159c1b2b436a567068ac2d8d58a3d2b23785626fcac4dd95841faaf94455f0883df14d574a2aaac5b55b2faaab15d5562aaabc595578aaaaa55d554aaa00b5f54badea971b953d27aa812454f486a9c98152db32a5b5654b26a802d6d3fa37a7f46d5472889fd18d3fa2fa7f35e5358daa845114d630aa057c,
    0x5bf2a8b535cd6a6b7ade1545a98dcb731f56e53e2d4a7e5b3afab6c5516ceb8ad9b7c5b36e0b529c96c23ead84715a92fcb525f56b62fad497c5aaafab555c56a4b90f7c675a78c8b0f9ed692462d218c587ceeb4455166a37ad014459a8d6b3c5f166a33ace14459a8c6b345b96663e2c3d765878fcb2c5b161e332c39455936b2b155ad641b8ac837058aaceb15199636bb2c535b58baecb14d4d61ca22c456b5870883df18d614b22bec7e5832f8afb1d95f6332be945,
    0x5f3ad6bfb1c97f53f2f9d675fa2b0bf41617ceb1afc4545f6ad6bed59d7ce312fa46e5f38a4bbed297b9adaf7b665ef468bdcd0d77c1e2f545b5ea8aebd5155781afaf3b565e7068bc0d4d791b72f23565e0696bc2db97841a2f03435df06000249d774aaae6d6b5db31ab9b59d764be2e6d655cd2d4bab5a5756b2ae69675cd2ccb9a59573a2fae74535ce0bcb9c149734b20f7c6f5c4cfeb94591712bf2e24765c72d8b89199710a2ae21441ef8d6b535fd704b22d4d7d,
    0x6368dec7cd218da35b1e3706368cec74d218da31b1bc696378c2c6cd898b23e316a5f62d4b6c651b18b52bb1736462f4a8c5c9518b529b1637061baecc54da186e3f31436061b8ccc4b5ad896b3b0db48621ad6c44dc1886b3b0d94861b090c395ad8762db0e23061b088bbf18d865b430a47e6176e0c291d98523330a3485df8b6c24d2177e29b0546160d8f8c1b1998352230545b60b488c1514d77db5301c696068e8c0c91180e2db022446038a6bbed897ceb7b00576,
    0x6754b6cfb6319f6c033aa5767b4b8cecd919e52a33b28c677cf8cec9f19d529b243726734d2c935bd9263733847e6494becd55f99a9b6b3625566a6d8cd49999252db2fe7965f8fcccd9e197e3732fa5965f2c4cc59e197c3733046c65f0c4c9295d92abf32e26c64a6cac9d5a593a3732745e64e4bccaa1399542132725c6534b8c9c549944ae32705e64f4b8c9c149929b232527c64a47cc944a192529b243705df8cec8d19186f3db2148c643492c84e0186f3bb20358,
    0x6bfad6d7c111a8e31b5e1446a38b6d74d91ae5a5b5196e6b76f8d6cd2da8cb335756f6b3aecd5d5adac2393583726aeaced5d58da8ca33564666a48d6d511f9aa2333540446a48c6d4b1f9a963335245b6a325c0024ada72b5b4e56769f6e0d39595a71b534e3685df8ded1d9fda3abf34c2686944bed2c971a55b234a2536936e0d1d1d9a45b034746668f8dcd1cd2177e35b2457f68b6d0c915f5a21ac344158648ae6c915bd9223733ad7d675ae2d05a319d52fb4036c,
    0x6a38dedf19fdbe2bf37e17c6f88ecdf45b1be23337c1446a38d6db35fdbd0b237a12e6d9afade4551b66b9b6cd6f6d98dcdc35f5b86b8b7668c6e16bedd3631ba6c0370b576e2afadccd61b8ab8b71c7c6e38e0dc4959b849b36cb726dfadedb2dc1b723eb6e4716d92fcdb517db64be351c676d78c8d7d9edb4e46369b806d3318d7d9ddb44aa364c6f6cf288d931adb34be364c676cb288d9318db24b736447c6beaecd8c591afa3f36216c6be8ccd835adb06b3b5f144,
    0x73d8f8e7b1b1cf42239b24f736496e755c1cd923b9ba7c7374d8e6c90dc28b3395c6a733ad0e569bdcc536395a6b72fae0e5699dcb13639623e72b4c6e14559ca5b338cd6f719ad6e4d1f1c66b3b91d7e7230a8e3358dc7236b9057c71c8bee3b1f1c742238e4537196cce355a9c65ab38513e717acae16dbdc55b3385b6b713afae16d9dc45b3385b6370b6bee1cdddc2dadb8634e70b6a6e144b800499b8412e700ad6e0c4b9c02b3b8197c70325ce01595c00b3380164,
    0x70a6c6efc591de6bf3be17c779aecef2551de42a38535f76d6feeec591db5bf3ba13476d6f4edaddddc4be3b6b7676f268edadc9db49a38535b76b2d8e14d5dd4537bb447c7578fceaf1f1d5d373b147c7626f8ec49f1d5cbf3afd7c75f6e0eae5c9d743e3ab87e7570f8eb11f1d613e3ac17c7570e4ea299dd49bd3a93727534c0ea49d9d4413ba813470a6a6e995b9d3137ba62637438cae931d1d26323a1a4f743496e8d5a1d0d23ba2264743486e145b9d06b6b9b45d,
    0x7bf2d8f00d99ef49a3c034e78069af74991eb1b7bdc47c7ac6d6f6c9f1eb1b3bda26c7b38e8f58d8dec534bd626e7ad8dcf5a965eb528bd626678026cf54955e06b5bd3c7c7a74faf0359de05b53c0b667a26f4f44dd9e052fbcdc7a79b8ecf36db5e752abcdb6c79b4ccf0296de42373c846c7906f4f2d5c1e41bb3ca36c7906dcf251b1e41b13c82597814aef1c911e0a3d3c627c7828ecf149b1e09b2bc245e7846a4f0c941e112f3c225c7826c8f048f9e0529bc0134,
    0x7eece6ffc591fba3f3fd9647fb0c8fdcdbdfb9b3bfc16c7ee6ccfec9a1fc92fbfa25c7f36c8fe494dfc49a3f734e7ee26cfdc4d1c29b5bed57d7ebd18fb55bdf96c63f447d7e52a8fcd1c1f942a3ed5637e18defc4511f8631bed47c7dc8befbb1f1f74223ee4537da2f8fb41f1c29b3bec364780cf6fa9631f51c63ea18c780ceefa4551f2237be81447c88d6f9c5f1f2233be61447c88c6f92db5f25b2be416e7c76f8f011d9e01b7be0d7e7c1af8f825f9f04be3c0367,
    0x83f91904adfe0e6c641e58c83926d0751f20e49a412b738374c706c4d2095b8c18b7c8314fb0644920c538c12a7e82c8f905a4da0b49a4163718254e50529f60a538c1297e8264df04c98e094be3855678232c9036dbe0849a40db6b81f2f9036d9e0749a40db6381b2dd0355f20333b40c16480cafd018d6603ab340a67680e4970255c203f3b407d6880f6b901c91e030aa40605470aac700b5ee0224640418c805aef00b596014b238536f7eecff00495a000b2400064,
    0x87d6e30fad7e1f5adc2a16787b8f90f293e1e525c2a1668772a90ead7e1d5adc2a16286dcff0db9ee1b73bc36e7386d6fd0dadda1b5b342a13f86b4c90c75be1a52a431d6b8674f90c759e192bf432254863ac70a84fa1863c42ae7f85f8d10ab9ee1724042e380855cef0b31a2165b442ae738558f50ab1ca1563542a137001277098dae1449a42636984f2f9098d9e130b342616470aadf0945921173f42417c845aed08ad66114aa38556b8432a904b5ba0963f412c7c,
    0x8bf2c9172dbe2e5b3c5cb668b92751724da2e49a42a36b8b0afb16da322c2b7c5a58c8b0ac716317e2c629c5817c8546cf15cd922233dc5638c888cef15455228a37c541448a28d714c5f228a33c521448a28c71445ba285be4444768886df1395ca270bf44e17c8886cf110d9a221a6c4b36e8972d912cd9a2211d449c628932dd12499a2211b4483668882751189ba2363144626688826d1135ae226b3c441348546c710b5da214aa42a35f88226f1044d2151adc3ed7d,
    0x8ff8f91bc99e3f5b646f2668efad71f45223beb1c7c5628ef8bd1de9ba3c22cc784518f06dd1e0db23c62847834e8ef4cd1bc9563aeb5c761708ebacf1bc9523a1374742668de48b1c55ae394b84715678e28bf1c515e379224702448de47d1bc8f631d31c6e47c8da6ed1b4d5231d2fc6956f8d2ad71ac5c234ab3c69d7e8d30a91a558e31d1cc681498c88b719c57e320adc662608c82af19319a3252446414f8c70680024fe30ebdc61d658c32c90a8dbe2e73fc5cc7e,
    0x93d26f27a4ba4f4968009538c76cd2715ee4e2b2c9c3648c74df2559fe4a9bf4994649336b92641924a937c9526792f6d925499a4a922c9524492b4892548fa31d35c8957d927d192255be496c64895639218df2451b248631c8937c91cadf23b152475aa48e5639122e12241f244eb7c8bc549176a922758e4522fc8a4539130692241c231d33c882648decf721ca3237b3bc862549048df21491241235c8427c9048cf20c91241231c8226e9034f91bcdda37937c7fc7e,
    0x97b4772f68de5f51e4be34497b4672f31c25e538cb5d679764cd2ec9725ad35cb657d96d6bf2e51b25b5adcb6b5796f6b92dd1925b5a9cb647096b4cf27a51a565ab4b3c669674a92b257a56ab5cad56a95aac72c55aa569af4b056295a6a52bd186569334add6a95bac52b497a564ab49e93f9568cd2ac91254a35ca9d7d9534f92a519e4f49f4a045a941ad72835aa531a44a6248941ac72935865252f4a0b6a946ad528d58a505a94a1d6a943ac528294a505284a0156,
    0x93d6d737b1f66f4be49eb679bb6df35a97e6b52dcd6a579b68df36d18e6b529cd9a6f9b34c735a57e6b4adcd69579ae6df35cd8e6b4a9cd616c93d4cd34d19a699a4cd3b649a747334c5ba4f4a7cd2349986ad730d5aa685a4cc356399e8a933cd226773d4c335f999cf53339ca6649b4c33539866a33291a26512ccca2419862dd30f18e61e30cc3b6e9876c531b5c2636b44c3a4f989ae13135826253e4c3a4398748330c59a4f4a3cc1c589834b32d75ae5ed1fcc034c,
    0x9f86ad3f919a7f12a4fe0449f82bd3f35aa7e5334fc1569ec27f3eb5967d5324fa46f9ec27d3dd16a7beb54f7b6a9ef4a13dc55a7b09bcf612e0012b7396db678ebe4f1c7d9e7ce13c7156792becf227c9e34b3396d7e77dbe4f057d9df473396d4e772b2cee2649d88df3b319a765224ec4639cb4c33a8df675636cea3559cb4bf3961b27462ace635f9cf6ad398d4e735aace625f9cb0c000255e724b64e34669c669338c5124f635ce217c93d8cf384572701ab4e0134,
    0x143edae89524d1245ba1f6ab44319a8852251046ba1f4b200257e7b237d0e4659ec6df3d89ba84a33509349a166c942c8e6848b750a248a130bd4241127b0a7d0456aa086a34171a282d2cd06254a0b4834105ba82520d041669ec28f40b1a281534d00d6fa02acb4051a280537cf6146] 23 6) 11
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
set_option maxHeartbeats 0 in
def cert_syms : List (TableSymmetry cert_mask cert_goal) := [
  ⟨cert_sym0, by decide +kernel⟩,
  ⟨cert_sym1, by decide +kernel⟩,
  ⟨cert_sym2, by decide +kernel⟩,
  ⟨cert_sym3, by decide +kernel⟩,
  ⟨cert_sym4, by decide +kernel⟩,
  ⟨cert_sym5, by decide +kernel⟩,
  ⟨cert_sym6, by decide +kernel⟩,
  ⟨cert_sym7, by decide +kernel⟩]
def cert_profile : Nat → Nat := unpackPaged [
    0x200533fdf80000100291fffc0000000048ff5c00000400847dbf00000100113f5f80000000489fbfc00000001087fde00000000881f9f00000200511fcf800002002807f7c00000801407fbe00000800a01c9a00000000101fcf00000001200767c00000801087fbe00000000081e9f00000100111fcf80000000000680800000000000000000000000002020000000000012b8000000000000000000000000000000000000841e4b00000000800f6f80000000488fb7c000600014439b200010004021c170001800000022f80004000008b45c00000800047abe00000000a23fd900000000401fef800000012097ffc000000010cfffe00000000c65dff00000200433fff800000001197bfc000000004cfffe00000080025cff00000300032e7f800040000097bfc000008004cbdfe00000001825fff00000000062fff80000080091fffc0001000008bf7e00000200267fbf00000040002fdf800001800997efc0000100040bffe00000600245fff00000100102fdf0000200000176fc00000c0008bb7e00000000007d1300000300103e9f80000080481f6f000000400047ffa00000600065fff00000100032fee800000800017ffc00000c0104f91e00000000000000,
    0x400000462fff80000180299f3fc000600010cbf5e00000600a67cbf00080040512fdf80000180299fa3c0020100140bffe00000600a67ecf00000300503f470010810020976fc00000c010cf91e0000460006bebf00080040017f5f80000180089fafc00000c400d7dfe0010080000feff00000300513f7f80000180081faf800000c100df97e0042040082fdbf00000300013e5f8000212008b7afc0001180141bdfe00000000204aa600004200006e5f800020000137bbc00000c024cf97e00000644063ebf00080102012f5f80000180019fafc00040c100c797e00420600025cbf00000300813e5f8000c001019fafc0006080204f97e00030000025ebf00000300133e4780000181118fbfc0020000a04bdfe00000601067eff00010304031e7f8010810048973fc00000c0344f9fe00820004047eff00410200403e7f802080004017bfc00000c024cf99e004202008075bb00000300503e5f8000c080081d2f40000040044f97e00000201a07cb800010300032a6f80000180019733c00000c014cb99280000600066daf000103000326d780000180099b63c00000400001316000202000061ab000001001036df80000080480bfb000000c004c9fda00000601266d8c,
    0x13d67000000000c9ebfc00000c002cb1fe00000400365aff00000000412dff800000000316ffc0000040048f7fe00000000015bbf00000100113ddf800000200016efc00000c004cb77e00000800205bff00000300122dff800000800816ef80000000002b37e000006000459bf00000100002dff80000180209e23c00000c0544e17e00000602a6788f000003230118df80000180899e6fc00000c064ce37e0000060a0278bf00000301d33c5f80000180c89e2fc00000c1404617e000006020278bf00000301133c4780000188828c7fc00000c0644e37e0000060326718f00000200521ccf80000080098ea7c000000024c673e000000012033df00000000000082000000000000000000000000002080000000120590f000000000000000000000000000000000000400325e000000000011af00000200501cdf800000100804abc000004004475fe0000000020020200000000100d11800000000804fbc0000000244677e000000012033ef000000004938ff800000000d9cffc0000040064f5fe000006001658ff000002001b28ff800000000984ffc00000400c0a77e000002002073ff000001000288df8000018009166fc000004024827fe0000060126308f,
    0x300533d6780040200201622800000c0140f51c000014008259bf00000300433c478000118000aeafc0000000025f57e00000600227abf00000310015d7f80040200003ebfc00000c0144f5fe0010080000788e00000300103d5f0000018200be2fc0000280005f17e000006000278bf00000280114d5f800001400826bfc0000000040155c000005000098bf00000080006d7780000180489e2fc00000c8804757e00000304021abf00000300033d5f84000182018e2fc20002c0004317e000006010278bf000000020b3d5f84000100049e2fc0000000024b57e0000060026788f00000302211d7f800000414086bfc00000c020cf5fe100006080238ff08000a00910c7f80000180689e3fc2100000808f5fe108004000078ff08400000002d7f80000180499e33c0000080144f77e00000400a07bff00000000103dd700000100201e6fc0000040044f57e00000001227aff00000000401df7800000002206e7c0000080144773e00000100a01bdf00000200501def80000000080ee780000000900333e0000040080399f00000000040d4f80000080088ea7c000002000035be00000001263adf00000000401def80000000259effc0000080124f3fe00000000825acb,
    0x4020100120f5f80000180099f23c00000c4014fbfe00000031021dbf00000300913edf82010008001f7fc10080001483ffe00000601a67d8f00000008000ad780000100281f6fc00000080402d5e00000200223ebf00000008100bf780000000488fefc00000002407fde00000400a43d9f00000100133f4f80000000499fe7c0000000240ffbe000000200055ff00000000413eff800000100815ffc000000004cfffe080000002056ff00000100113f7f8000002001053fc00000c000cb9fe000000800417ff00000200132fff800000000987ffc00000400c0af7e00000200207fbf00004100420adf8000018029176fc00000403483ffe04040001a07dbb000000000000000000000020016200000000000010000400000003d9200200100403ed580000180681f2fc1008040240f97a0000000000020000100120103f5680000080489f2fc000000000051560004020000292b000003001016df80000080481ffb00000040340f95008000600067cef00000300033e67800001800087f3c000004000cbfda00000600a67cc900000300931e47800000402216ffc00000c014cf1fe00000000925baf00000300513c5f800000002496efc00000c014cf51e00100800805bff,
    0xc0300000002000e07c000008850074fe0000004020080f0000000000000100000000000400000000000000486000000c122387f0000002000002300020210488e1fc0000008000f4de00000201a0783f00000001c13d3780000020609e5bc0000080304f3fe00010000a27b6f00000200513dbf80000180008e1fc000000004050dc0000040022387f00000000c13c3780004080288e9f80002000004f4de00000200a27a7f00000001c13fb780000040281fcbc0000080144ff7e00000100a07f6f00000200503fff80000000081feb80000020100fa5e00000400807dbf00000080003f1780000080089fafc0000020000fcde00000001227eff00000300110e9b8000018000074dc00000400401a4c00000008000c2600000380400e9b80000080001f4b00000000100ffde0000000280782f00000008302fcf80000180289f2fc08080000083b7e00000600a67c8f00000322013edf81010010011f6fc00000c004cfb7e00000450205dbf00000028902fff80000180499f6fc00080c1004f97e04040200007cbf00000300d33e5f8001018429172fc0008042240bdbe00000601227cbf00000314013e5f8000008c00872fc00000c0004f97e08040220007cbf,
    0x100131f5f80002000010f97c000000024c7ffe00000000843fdf00000301431c4f80000028a89fcbc0000080544f47e00000822807f7f00000201503d3f80000208a01e8880000000540f45c00400002813c9f00200201403e9780000100a01e0fc0000200000707e000006000238bf00000284501d0f90000140280e87c0000200000703e4000070002383f20000184501c8f80000040209ecbc0000000144f17e0000100100387f00001220811c3f80000180408e1fc0000000000400000000000213a7f00000200911d3f80000100380e9fc00000813c074fe0000000000000200000000000c2f80000180100e1fc0000000000000800000000001a5f00000200301d3f80000000200681800000411c072fe00000001c07b6f00000000d13c3f80001020000e8fc0000054104747e00000600a23a3f0000000010140000000000080e97c000010004074fe00000a20803a7f00000300501d3f8000000008020000000000040501c0000080020380e00000510401c1f00000080280e8f80000001000707e0000000000180600200301401e9f80000180e80e0fc0000000000100a000004c0223a3f00000000000d0200000310080e9fc0000000000040800000800203a0e,
    0x2000084aa8000110268c2d1c00000843c63e9e00000001821d4f00000000820fbf80000001118fdfc00000000003aa60000040002355f00000010802ebf80000000109f5fc0000000080befe00000000605f7f00000200213fbf8000000041075fc000008038c7efe0000000140457d00000000810bbf80000080200743c00000c054c757e00000602a63aff00000301521d4f00000180a18e2fc00002c000c717e000006000638bf00000300531c5f80000580418e3fc00000c020c71fe0000000004280000000300139d7f80000180498ebfc00000c034c71fe00004600263abf00000300531d5f80000000000200000001c004c75fe00000600a63aff0000000000000000000280080e23800000c0148757c000006080638bf00000301d31c5f80000180698e2fc0000000008f0000000000004780300000000533c4f80000000011e0000000000748f01e00000201a4781f00000001d23c0800000000238e57c000008010c73fe000000008e3b5f00000200531dbf80000000038e97c000004014c74fe00000002863f5f00000040421f8f80000100298fefc00001001087ebe00000400a43fff00000000121fcf00010000210f47c00000801087b7e00008000043e1f,
    0x1000000100060601880000000000000000000000000000000000000080b8800011004066d1c000000000200020000000001014100000000000000800000000050554000000020182ea0000000000000000000000000000000000000000000000000020280a80000000000000000000000000000000000004050504000000020182ea0000000100c17500000000c10ca3800003001087dfc00000000808afa00000000445f3f00000010e31ebf8000010100c7dfc001000000004c60000000484027300001002000c318000000021001c4000000030880e600004000055f3f0000000042a2be80000800290000000000901427efe00000400010315000000000001000000000020009c4000040000010400000000080002000000000c02030800008002800000000000014236c80000400181597500000000c1bebf8000000000014c800000100053a7e0000000000081000000000002e9980000020008f57c00000001083ade00000400843f7f00000210100baf8000002028074fc0000090280bafe00000485c21f4f00000200209faf8000000228474fc00000800823afe0000000000057d00000200008ebf800000000042558000008000212aa00000000000055,
    0x2000010000000000000084000000000202e200000401419f4f0000004000808180000000004050c000000000200060000008141455d00000000a062be8000002050315f4000000000000a40000000000016100000000000dbb800000000084048000000000006c00000000000032100000000400000800000002000080000000010106400000000083bb77000000000080018000000000365dc0000000007f2ee0000400001011100000000000000800010000036ddc00000000000000000000000100000000000000000000000000008485800008000000044000000000000000000200000a0008000000000f6ccc0000080007f6ee00000000010363000000000000218000000020065dc000008030772ee00000000043367000000000081b180000000407e5dc0000000000d6ee000000000003550000000080a0aa8000000000d8d5c000000000104240000400185b977000020000219bb8000000000409080000000202008400000000010332000020005041b90000000000000000000000000000400000000010172000020000018a0800001004866d1c000008004226ac00000400201377000002001089bb8000000000409000000000000000000004000010112,
    0x171a8f80040000018143c000008005c2a1e0000000026150d00000000410ea7800000014107dfc000004088d7efe00000001005d7f00000100217fbf800000000817dfc00000c0085fefe00000001441d7f00000300e31ebf800000804081dfc000000080002e60000400000016100002002620fbf8002000100844c8000000000006c20000000000036100000000420190800000002100d80000000090906c600000000c7bf7f000000000080a18000000840375fc0000000287fafe0000408001015100000000000028800010001837dfc00000800c7fefe00000000010363000000000000a18000000021075fc000008030f7afe000000008c1f7f00000050021bb7800000000040d8c0000010283fafe00000004006f7f000000000023ae800000000037dfc0000000806cebe0000008001835300000040e2debf80000008010ddfc000000000206860000000101014300000040208199800000282860dcc0000000010004000000000000003000000000080b980001000000c58400000902c33e9e0000040025137f00000210100bbf800002002807dfc00000840422efe000000004103410000000200010000000001104044c0000100000068400000001c18163,
    0x140000146fbf800201000affcfc004000000a82c2000000010c056f00100000460eb78008000042855fc000008011f7afe0000000100c57d00000010021b9f80000001001bcfc00000840402e7e00000000040021000000000309b2800000000000004000000000032ee0000000086bb3700000000000cab8000000000be4dc000000000032ee000000000000000000000000010b0000000000100000000000045b6660000040023fb370010000002203080000000000059c004000010032ce002000010211370000020043dc9b800000000000000000000000000000020000101411500000000000000000800004050404000000020182ea0000000100c1750000000002199b80000000000000000000000000000000000000000140000000000000000000000000000000400000028202000000000041150000000000359b800001000804cdc0000000104320e0000000104856d0000000000629e8002000821af4fc00000002108abe000000008c453d00000600541f9f80000000099d4fc0010000114fa7e0000000000051300000200806e9f80000100230fcfc00000000400e3e000004048a1d0f00000000129a8f80000000010c41c000000004c220a0001000026151d,
    0x406c1a00000008313f4fc0000000846aa3e000000000100010000000000001080000000094244400000000400640000000002509100000000000000000000000090244000000000001044000000012559130000000011a88b80000000000000000000000000000000000002109110000000010000000000000080244000000000000000000000002008000000000000040100000000495644c0000000242f228000000052d7d1c0000020012aa9f8000010008544dc000000024862280000000124351c00000000403e9f800000000017c7c00001800007e3e00000400023f1f00000000002faf80000300001fd7c00000000008a3c00080800002f1e0000040000378f00000001001747c00000000000a7e0000040002151f00000200011a8f80000100001fd7c0000000000debe00000020041f2f00000310011fbf800000000107dfc00000c40087efe0000002004052e0000011002139700000000210008000000041080e5c00000000841d2f00000300421fbf8000000001015b000000400084ede0000000004016100000000870bb780000001000058400100009083efe00000000840061000010024240b08002000023efdfc0000004100babe0000000083fd7f,
    0x111000000000000000000000010a06240000000084797700000000000000000000000850c0c0000000008b66e000000000000200000000042010900000000280c4dc000000010ef26e00000000a10013000000004081088000000020000840000000000366e00000000a0021200000200519d9b8000000028008800000000000040000000000002a000000002040010000000000000084c0000000000000000000040201b7700000200509dbb8000000000400080000000302002600000000010356000000005000000000000000000000000000000500000000000800200000000000001000000000000000000000000040060c00000000a0000000000000501d830000000020060c8000000010000040000000000080200000000400c9b80000000000000000000000000000000000008401270000000002080000000000010441c0000000008620e0000040081793700000000403c8b80000000000000400000001090666000000000001200000000042419a000000000000000000000010806040000000000181200000010626099800000002020084000000000002000000000080023400000000000000000000002000008000000000010040000000084c032,
    0x2040191000000000000888000000090a0664000000048c7d7f00000000000111000000010850c8c0000000808be7e000000000002220000000242819900000001280c4fc000000090efa7e00000020a1011300000000004000800000002040c440000000100026200000080205f3f000000005081990000010028dfcfc000000414206600000000000022000000410001580000000002040cc000001000000666000000000002000000040010afbf80000a002810cc00000080142fefe0000000001000200000000e08089800000005050d7c000000414002200000000000000000000010001400000000002000c40000010000006400000080020431e0000000050009800000a0028108c00000000140fe7c00000000801932000000000000000000000021000080000000008100400000000805d3f000000000002910000000021114bc000000000822200000040004111f00000000021a9f80000100205f4fc0000000000300400000000010343000000005081898000000060d65dc0000000204a6ee0000000000000000000000000000000000000040c0c0000000002000600000000000002000000005001098000000020d655c0000000000b6ee00000000000000,
    0x40834bbf800000000060cc8000008010f7e7e000008000003300000140042019800000108216fdfc00001000000420000000000001300000140042011800000000210fcf8000008010b7a7e0000000000000000000000000000000000002100104000000010a024200000001048165000000008349bb800000000060c880000080105766e000000000000200000000040018000000100206eddc00000000000000000000000000000000000040010000000000200ec18000008010b726e0000000084b92700000000425e9f800000000107cbc00000840047e7e00000000041f7f00000210021fbf80000008010dcb800000000000a7e00000000041d2f00000200421e9f80000000010ddbc00001800007e3e00000000005f1f00000200011f8f800002000017d7c0000180000febe00080800002f120000040000378f00000000001747c00000800046a3e00000400007d1f000000000037af800000000006088000000081206c600000020a1031300000002e5aebf800000205095dfc00100000000080000000000000220004000200819180000000004040c0000100000040400000020a1031300000010015e9f8000000120d757c0000000800befe00000000000222,
    0x1080000000000000000010000020006000000000000000000000000400000002000004004400000000000000000000000000000000000000000000000000200000c00010000006666000084000013330000400000808b8000200020e641c000000000000000000400000026300000000000000000010000000108000000000100000000c00001005000000000000000000030006040108000080000266ee00000000200000000022001089bb8000300060e651c00000000000000000000000000600000000000000000000000000010800000000010000000080000102530000000000000000002000604010c000180000066ee00000000000000000062001009bb8000200060e651c00000000080080000000000000000000000042401080000000000000000010000028006000000000080000000400010a10980000000000600000000000000000000000010010000000000042000180002000204045c000000000200000000000001333300000000000000000001000044ccc0000000000008200008000010000000000000000000000000060000000000000302000200000000000000000000001388808000000020e640c0000000100020800000000800104,
    0x10000000000000000000000001400400000000000018020000000042401180000000000000000000000402000000080012191240000400042dc938000000000000000000000140042600000000000000000000005001080000000000000000000000140040000000000001800000000000000000000000001040000001000102802600000000000200000000000189bb80000000000000000000000000000000000000000000000400002a0000000001001700d00000000040a000000000012531140000000040fc8b800020000084ddc000000000000000000000000001100000000000c00000000000000840000000000000000000000000000000000000000010000000000100000000100000280240000800081f91700000000000000000020000040084000000000000000000800001026300000000000001000000000000000000000000000040000000084002200000000000000000000000000000000000000000000000000000000000000000000000000000000110080000000000b8268000000000000000000000003c9bb8000200000400000000000000000000000000000000000000000220000000000021500d0000100010b724e00000000000000,
    0x200500da3800008002806c180000000140060c000000000531270000000000608b80000000003a45c0000000102326e0000000001380700000000c0408180000000002000800000000000000000000000000030000000000000000000000000000000000000000000000000000000030000000000000000000000200400c00000000000000000000012020030000000000000000000000004401c0000000102720e000000008000000000000040000000000000000800000000c0106700e000000008100070000020003088380000100200641c0000000000044400000000000022000042000289bb800020002100080000000000200400000800085b9670000420000898980002000207e44c0001080002a6ee0000800100c1550000000080e0aa8000200040fe55c0001000002666600008400011323000000001148908000200021ee48c00010000026646000084000113330000420051cd818000000000408000001000140040000008400a19b47000000000000010000000000000000000000140040000000000a003020000400000989180000100018440c00010801033206000080000293770000000000000000002000284088c0000000000000000008000a10220,
    0x8060aa800000004076ddc0000000205f2ae0000000000991700000000017c8b8000000000264dc000000000000000000000022fb1700000200117d9b80000000000000000000000000000000000000000040000000000000000000000011040000000000000000000000000441210000000000608a8000000000000500000000000000200000000010000000000000080000000000001100540000000002000000000000010000000000000220908000000000304d40000000001826a0000000005733700000200128993800000002166cdc0000000000000000000000013817000000000000000000000000000440000080002706e0000000000000000000000000000000000000000000000000000a8028000000000000000000000002a01080000000000000000000000000000000000000140150000000000a01a8000000000000000000000000000000000400811937000000000000000000000000000c4000000000000000000000000000100000200008c1b8000000021404940000000041622e0000000022112500000000431c9380000000014cc9c0000000001d62e0000040021133700000000508d9b800001002886c1c0000400140368e00000000a11b77,
    0xb8000000200000140000000000c0a0000000000040500000000000000280000000401015c0000000000004e00000000000000000000000000100000000000000140000000200828a0000000000c1550000000000001180000000002e5dc0000000001826a000000000000000000000000808000000100000655c0000000000000000000000000000000002000008aa800000000046400000008000032c6000000000040140000000402200a0000000000000000000000200008a0000000000200000000000000000000000000000000000000000002080000000001014100000000000000000000000040004000000020080a8000000000000000000000000000000000100400001000000000000000000000000000000000000000280200000100401655c00000000088242000000000000000000000000000000000000000008400000000000000000000000101410000000000000000000000004001c0000080200b2ce000000000000000000000000808000000000401041400000002028282000000000101410000000080ecbb80000000000004000000000020020000000000101000000000080a00a8000000040505040000000000802800000001015957,
    0x1040103f9f80000820290fcfc00000101403e7e00000600a21f0f00001000500fa7800000002847dfc0000500042fefe00002800a41f4f00000400500fbf800001802807d3c00000008083a7e00000200053d3f00000000002e8f80000080003f47c00000001023a7e00000000017d3f00000000c0c29180000000007000800000000020000000000020104270000000140a81180000000000001000000002424046000000000000000000000000881780000000214f4fc00000001007020000000000000000000000040101800000000011e0c000000c010e7b1e00000000811d3f00000300030a8780000180200743c000000000206c200000400041b77000000000080910000010001065dc000008004a26ee00200000850302000000004281810008000021265dc000000010b36ee0000000084396700000000005d9b8000000000304d40000000000000000000000000000000000000220908000000000305540000000005c6ae0000040021d3170000000040ed9b80000000203e45c0000080001b2ee0000040021d3770000000000a0ab800001004036d5c000000000576ee0000000000e13500000200006cbb8000000000004480000080201b2ae00000000000000,
    0x80400afaf800005824037d7c00000408057efe000000000c453d00000110007e9f8000010100365fc000000000192be0000100000cd5f00000202002ebf8000000000035780000080200babe00000000004d5f000000000026af80000000001357c0000080801befe0000040100df7f00000000006fbf800000004077dfc00000008017efe0000000101df7f00000302002fbf800001804017dfc00000400009efe0000020102fd7f00000110044e8f8000008800bf47c00000540013e7e0000008022ff3f00000300117f9f800000000006000000000000006000000000000000000000000000287000000000000000000000000886000000000000000000000000022091800000000007c7c0000044011ba3e0000022000dd3f0000011002bf9f800002000907cbc00000c004a3e7e00000000859f3f0000000000000100000008004f47c0000000000002000000000001d3300000240009f9f8000000000514f40000000000000000000400851f3f00000000008298800001012147cfc000000010a3e7e0000022020b51f00000100110a9f80000080218f4fc00000000183e7e00000200053f3f00000000002f8f80000080003fc7c00000c40423e3e00000000a11f3f,
    0x2000213c3f80000000009097c0000000040b4fe00004400427a7f0000000002023780000000008a1fc000088028c70fe0000000000005f00000000001c3f80000120000e1fc000000020800fe0000000000006f000000008001278000000040849fc0000000048603e0000000000300f4200000002000780000100090403c0000000248201800000000000a7f0000020000043f800001800002bfc0000040000d1de00000600000aaf0100810000245680000080001a2bc0000040000555e00000600000abf0000030000254780000080000a23c0480040000811e0000020000488f0000010000244600000080000603c000000000206c6000006200c1f7f00000000008191000001a00307dfc00000100483ede00000600251f7f000001000607bf800800002140c88000000011a064400200000849d7f00000000060fbf800000002367dfc00200801583efe044004048c1f7f02000000560eb68014000023175b400000001183efe00000200843d7f00000102205f9f8000000003114f40000044001ba7e0000020002ff5f00000002102f8f800001800877cfc0000000183be7e0000000040df3f00000100407e9f800001810037dfc0000000840bebe0000060021df7f,
    0x221020000000000000000000004018800c00000000001800000000080261070000000000060000000002019805e000000000000000000000000001200000000000683c0000044018b03e00000000000014000000000000008000000000000000000000008803a00000000000000000000000000000000000000000000000002009805a0000000000403d00000110022c1f8000000003168fc0000044008f4fe00000800241a2f00000300020d1f80001008011e0fc0000890008f47e00004000041a2f00000010001e9f8000000000014fc00000800007e7e0000000204052d0000010042341f80000008000c0fc0402000040003e0201000022002d0000000011081f80000080018e0fc0000000008345e00000200043a3f00000000002d0f80000080081e87c00000c4040347e00004000201a3f00000300110d078000000200060fc00000c0000301e0000000000401f0000000000011f80000110000e8fc0000000000b43e00000400023a1f00000000002c0f80000100001e07c0000000000d4be0000000004402f0000000000011f8000000001068bc000008400474fe0000000004182f00000200021c1f80000000010c9bc000080088c74fe0000440002305f,
    0x4000103800000000018158000000000084a40000000100425f000000000000000000000000000000000000000000000000000000027000000000000000000000000000800000002201849e00000000005a7f0000000000001380000001000e9fc0000000000807a0000000000000000000200802d2f80000000000000000000000000404000000000000000000000000000100000100000417c0000080040b4de0000000000421c0000000402200e0000000000000000000000200049a000000000020020000000080212f0000000000000000000080200041c000000000000000000000000290700000100481697c0000002009805a00000000000000000000000001010000000000000000000001000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000100000000000001c0000000000002f0000000000010100000004000143c0000080200b4de00000001005a7f00000100813c3f80000088031607c000004400cf07e000002a0045a3f0000000000000080000020089e8fc00000c004cf47e00000000000000,
    0x10005a4f8000000008852fc000004040c797e00004002201f3f00000301110f478000000001078bc00000840047c7e0000000004366f00000000002f0f80000100008f87c0000000000dcbe00004004463e7f00002200011a2f80001000109f1fc0000000000bcfe0000000002465f00002200213f3f80001100d18f1fc00000002042cfe00000604001b3f00000100407dbf80000080020ecfc00001c0000367e0000020022933f00000100435d9f80000080020ecfc00001c0000367e00000600a29b3f000001004005bf80000080800723c00000c401834fe000006800c1a7f00000040120d378000018001069fc000000001834fe000000400c1a7f00000100021c3f80000081111e8fc0000044008b07e0000000000000000000000000101000000000000000000000000000000000001004c22f00000000002d0f80000080019e87c0000000840b43e00000600205a3f0000200000201e80001000101687c0000040000f07e00000604205a7f00000002102d2f8000018008169fc0000001200b4be0000000000455f00000300802d2f80000081019e9fc0000044008f07e00000400005a7f00000200802d3f8000000000008080000000000042e00000008000000,
    0x101021e7f80000081102fafc0000044001b97e00000010005f1f00000100017fcf800000010817c7c00000c0000bd7e00004000405f1f00000100003e5f800001810037bfc0000000840bebe00000604005b7f00000300002f7f804000020017d7c00000c0201bdbe0000020402beff00000110007e5f8000018100175fc02000c0200babe000000040000020000000000000b000000010009000020000000008040000000400041e0000000400000300000000000000800000002008a1c000000000004000000000000020000000000000101000000000009abe00000200004d5f00000102001ebf80000080401357c0000082000befe00000411005f7f00000008002fbf80000005000fdfc0200002200befe00000201027cff00000110044e4f8000008800bf27c00000540013d7e01000200227f1f00000048113f9f8000018008bfafc000000000000000000000000020600000000000000000000000020018000000000000000000000004460c000000000000000000000801110bc00000000003e1e0000022008dc9f00000110006e5f800000000317cfc0000044008fd7e00000800241f2f00000300020f5f80001008000f47c02008900007e7e00004002041f2f,
    0x2e0f8000000000010fc0000080000683e00000600007d1f00000304003f8f80000000001787c00000800017c3e00000000005f1f0000000000029f80000100002fc7c0000000000de3e0000002020463b00000000120f1f80000108010fcfc000000c040be7e00000460007f3f00000010102f1f80000188881f8fc00000000483e7e00000440003e1f00000310021f9f800001000805cfc00000401081e7e0000420484bf7f00002100007ebf800000000013d7c00008c0001fefe00004200007d7f00000300000abf80001180212f5fc00000800008e3e00000000000d3500000100401f9f80000000011345c00000401002a2e00000600807d1f0000010040269e800000000003c7c00000801401e1e00000200800f7f0000020401097f80000000558ebfc000008002427fe00000051527bff0000020401097f80000084d49ebfc000008002c27fe00000211563fff00000309a90c7f8000000204009c000000c32c437fe000006080202ff00000208a90eff800000004080ffc0000000404381e0000002008032600000310060f7f800000200200c9800000d00183dfe00000080241f6f00000340020dbf800001800107bfc00000000183efe000000420c1f7f,
    0x100431e9f8000000001071bc0000000084787e00000000005c5f00000008011e0f8000100080071fc000008020c281e00000602021c0f00000004135f9f800000000107dbc00000000847e7e00000000005f5f00000208011faf8000000a089fcfc0000000000bebe00000010023f1f00000000020fb780000080108fcfc00000011403efe00000608a21f0f00002001100f3f80000100888783c00001001087efe000000000000000000040080002980000000000014c00001000080a060000000000000000000000000000000000000000000020010000000a6000000000000000000000000000000002200d00016c000000000000000000080124081300000000020a8980000000000000000000000000000000000000000000000040140100980000200201fdfc00000000081060000000008030300000000000080000000000200f44c00001c010c7b1e00000800801f7f00000200410e878000000800118ec0000040000bc7e00000200005e3f0000000002231d8000000000010fc0000000008385e00000602043c3f00000304021f9f8000000001078bc00000840007c7e00000000041f2f00000210001e9f80000000010dcbc00000008008c760000000400463b,
    0x40000120fb7800001000187dfc0000000010bcbe00000010027f1f00000010213e1f80020000000010c00000000000406000800000000000000000000010180000200000085c0000000080060e0000000000000000000400000000000000002101cac0000000000040400000400041f7f0000000000010080000000000800c0000000008065400000400041f7f00000000020fbf80000000000005800000040007afe00000000000a790000000000000080000102000fdfc0000000000887a0000000000443d0000000000000000000000000000000000801083e3e000000000000000000000000000000000000000080800000000000000000000000000020000000000002b800001002107cbc00000000000402000000004002490000000020000a8000000000000000000000080000a00000000000000000004000001088000000000000000000000000040e0000000000200200000200420faf80000000000000000000000088852000000000000000000000002221480000000000000000000000000404000000000000000000000000000000000000000000000000000000002000000000000000000040000000580000000000080800000801083e5e00000000841f7f,
    0x220213e9f8000100000110740000004084b83e00002000005f5f00000020810a8f800001140097c7c000008a804be7e00000004205f5f00000200012f9f800000000000000000000000004040000000000000000000000000000000000000111cac0000000008bcfe00000220467e3f00000020042fbf800000100217dfc0000000004fa7e00000408025e3f00000022210f0f80000081918f8fc000000108cb83e0000000000000100000101021e2f80900000600007c0000040204683e00000602467c1f00000002001e3f80000000000017c0000080200f8be0000000100445f00002002001f3f80000000000617c000000000020ae00004400007c5f00002000002f2f80000000498d0fc0000040404f87e00000020429d1f00000110211e9f80000080000fdfc00000050843e3e00000208083f7f00000300211f9f8000000000000000000000081040200000000000000000000002222058000000000000000000000001040200000000000000000000000000018000000000000040000000000000000000000005e4f00000010216e0f8000000810970fc000008408c3e7e00000000000223000000000203b780000000000008c00000000083ade00000400461f3f,
    0x100046f2f8000208400b7c7c0000040010befe000000000000110080000000000a8000000002139440000000000bcbe00000210025f3f0000000000000a800000000817d7c0000040004be7e0000000008ca5b00000100006d0f8000000000128640200040000b67e0000000000ce1b0000000004672d80000000000004400000000009c2200000200005f3f0000400000670d800000800217dfc0000040010befe00000000085f7f00000100142f9f800000800a17dfc0000000050befe00000400227e3f00000000000000000000001000014000000000000000000000040050d00000000000000000000000130014000000000000000000000000010100000000000ea78000000110b707c0000000085b87e00000004045d7f00000000233e9f8000008201874fc000010000088760000000000000000000500420ebf800000000000000000000008000220000000000003f000000002000278000028081074fc00001004083ade0000040102143f00000201031e1f8000000810af07c00000000017cbe0000000008be7f00000200215f1f8000010201878fc00008004093cde00000002063c3f00000022211f9f80000000000080c00000080007afe0000004102353f,
    0x100a827bf80000180541f1fc00000c10e0fefe00000001507c7f00000000002e2f80000180401f17c00000c1000febe00000000006f5f00000000020e3780000180810fbfc00000c10087ffe000000000427ef00004108aa1fbf80002084541f5fc00010c20e0fefe00008601d43d7f000000000a1bbf80000000041bdfc00000800602efe00000201101d4f00000000420fbf80000081012fdfc0000000200bafe0000020000fd7f00000000102fbf80000180003fdfc00000408007afe00000000841d7f00000300c25ebf800000806003dfc00000002283efe00000213543f7f00000004882eaf80000084541f5fc0000000060befe00000200304f5f00000308383fbf80000002c5075bc00000002280ade00000603543d7f0000000408373f80000002050d9fc00000810602cfe0000020b101d4f00000001810e67800000911187cfc00000081083ede00000200061f3f00002000020fbf800000819187cfc00000008083efe00080006041f7f00000001031f1f8000000100110ec0000000085b87e00000000085d5f00000208017fbf8000008200974fc0000004010babe00000000027c3f0000000200221d8000000010bf0fc00000000119cb600000000204e5b,
    0x20082faf80000114449777c000008a824bffe00000410325fff000000200923ff800000100417dfc0000008220befe00000011127dff0000020c192f7f800000111487b7c0000040c2c7dfe00000008165cdf000003018b3e6f80000001040f9fc0000082220f8be00000001105e7f00000109893e7f8000000814a777c00000440247bfe00000008121fdf00000300091fff80000000000000000000000000486000000000000000000000002202180000000000000000000000000c90000000000000000000001000022500000000000797c0000004085b9be00000020425cff00000a502b0eff880000000000988400000100000c400000008141f6f000002002b0fff800001001d87ffc0000004084f9fe00000420041dff00000000000ab4080001001107ffc00000040082bda0000000000024000000000000030000001001506ffc00002040a82bda20000408061fff000000400b03ff800001081507dfc0000000000048000000408541f7f000000002a0fbf80000008040f5fc00000810207efe00000000941f7f00000100eb1eff80000000049f37c000000062038fe00000603121ccf10000004580fa7800000022807dfc00000c13643f9e0000040070577f,
    0x20c97800001002186efc0010000048365e00000400861bbf00000040020111800000000000004000000410800d600000000000203000000400209b68000012801865fc800000000844004000002004000a000000000000109000000000044a4000000000000000000100000020300000200030d9f8000000801845b4000000400c72be0000000000074100000200031dbf8000000041845b400000a0008367e00000500041b3f00000080020d9f80000048000e47c0000000000143200000508003b3f00000280420d8f800001402106c7c0000020108367e00000000085a1f00000000033d4f80000008019e2fc000004010c737e0000000000581f00000300003c0f8000040000060fc00000c0004311e0000420404bb3f00002100007c9f800000000013c7c00008c0001f67e0000420000393f0000030000089f80001180212e4fc0000040100167e0000020002111f0000000003180f800009000004c7c000000004c623e0201000026101d0000000013180f80000000008c03c080200000c001e0000040006100f0000000013080480000000008623c000000402579be00000408761eff000000010a4f3f80000000d58f3fc00000088247ffe00000020425cdf,
    0x2105020e9f80000000001ad7c0000000000c07000000002043caf0000000000358f8000000801be27c000008100c357e00004000049a2f00000000031c5f80000011019eefc000000400cb13e00001000005b1f0420000000008f80000010008447c0000088004b73e00000444225bbf00000002102d8f800001000896efc0000008010b67e00000040085b3f00000080022d1f80000088019ebfc0000000004f37e00000408225abf00000022032d5f80000081019eafc000000100cb13e0000060006789f00002002023d1f80000000011607c0000880008f03e00004000005a1f00000002001e1f80000000000111c0000000008801e00000400007c1f0000000100220f80000000099c0fc0000000800757e0000000000005f0100080000040f80000100000a27c0402000000207e0201040000001f0100810000000e8000008000022fc0000040004f17e0000002006d9bf00000110033cdf8000000a0196e7c00000c000cf77e00000000000000000000000221018000000000060000000002008801600000000000000000000002221008000000000000000000004008800600000000001a0f00000010036c4f8000000801962fc000008410c377e00000000000023,
    0x82000000000110d7c000000000000000000000000000000000000022293800000000017dfc0000840004befe00000400027f7f00000202012bbf800000100017cfc0000000004fefe0000040802567f00000000000101000000000000000000000000004040000000000025b0000000000000000000000000000002000000088c4e00000000005e5f00000101033f3f800000004185dfc000001000c2ede00000608041f3f00000000020bb68002009001875fc000040c00006ce00000608041f7f001000244201b3800000020000c1000000050882ada0000006084236000001110021ab680000000000088c000018000c3efe00000000000203000000004201b38000000001069fc000004800c3afe00000240041d3f00000304002f9f80000000101787c0000040000fe7e00000608005f7f00000000006fbf80000080009fdfc00000401081efe0000400806167f00000051020133800001a081079fc0000400000348a00000000000345000000010201338000000000009040000000000340600000408061e7f00000000000101800000002100d9c000000000834fe00000080000204000010104201320000008811051b400000400080eda00000202061c7f,
    0x3edf80001000009fbfc0200008000bcbe00000202047cbf000008000001218000000c10b617c000000608db03e0000003042d85f0000080020010180000008100000c0000006085b03e0000000014c05d0000000022600e8000008c113607c0000046089b23e0000023040d81f000000000800a28000000010005140000046081b23e000000000040180000000000201c000011000105cfc00008400081efe0000000004162f00002300020f9f8000010001870fc000080000c38fe0000400000016700000250020f37800001000105dbc000080100006ca0000040a041e6f000000000000018000100000004000000010000044e000002a8041d6f00001060000193800000082100d9c000000000000ca000002a0041d6f000001000207b78000000801059bc000084500c3efe00000620041f7f00000240030f3f80000000000098c000000000832fe0020200004366f00003010030b378000000000005140040000000440c00200008000347000000000001b38000000a01009980000409000048e0000200000036700001304020fbf8000010001879fc000000000c38fe00000020005d1f00000104012ebf80000000009f5fc0000000000020800000000000000,
    0x40012baf800001820017cfc00000000008aba0000030022153f00040180012ebf800001820017dfc00000800143efe000003000a5d7f00004100002e9f800001820017dfc0000000010bcfe00000200007f7f000001004027bf80001002009597c00000c0001bcbe000004080a1e7f000000000026ae800000c002971fc0000841000ba3e000000000463ff00000000003e0f800000004094d7c0000020010b6be00001400007b7f00000000042caf80000100011effc00000c100036fe00000000085a5f00000100423fff80000000011e3fc0000000028b63e00000608001b1f00002100423dcf80000000019e27c00000c1000b6fe000000000c5a5f00000100003dbf800001820006c7c0000000002b43e00000200027b1f000001004025af80000000049e97c000028000424be00004000067adf00000000023c4f80000000490c060000008000017fe000000008038ff000002000005cf80000000208a27c000000000415be0000000000289f0000000040044c00000000001e27c0000000800ba3e00000400007fbf00002100003fdf800000041017c7c0000000000f97e00000000105f7f00000000013e7f800000000217cfc0000000004fffe00000050005f7f,
    0x1e07c000004100432be0000000012795f000000008309b7800001820006c7c0000000080b43e00000200007b5f000001004205b780000000010e0bc0000000000f8fe00004000027e7f00000000003e1f8000000000100600000880000ae3e00004200004f5f0000000000230dc0001180001747c0000080004b83e0010000002041b80000200010a0f8000100008850640000800004b8be0000040000575f000001000027af80000100081596c00008410043efe00000000001e5b00000300802eaf8000014042979fc00000c10003efe000005040a5e7f00000000052e3f800000010017cfc00008400043efe00000000027f7f00000204010b3f8000000002178fc0000000004fefe0000000102577f] 57 6
def cert_ref := symDagRef cert_mask cert_goal 2599 3 cert_syms cert_trace cert_links
def cert_check : Nat → Bool := fun i => checkNodeViaF cert_mask cert_goal (chooseBounds cert_bounds (cert_profile i)) cert_trace cert_ref i
set_option maxHeartbeats 0 in
theorem cert_roots : dagCheckRootsF cert_mask cert_goal cert_bounds
    (cert_ref 0) cert_stock 12 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row0 : treeBlockF 0 4 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row4 : treeBlockF 4 8 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row8 : treeBlockF 8 12 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row12 : treeBlockF 12 16 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row16 : treeBlockF 16 20 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row20 : treeBlockF 20 24 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row24 : treeBlockF 24 28 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row28 : treeBlockF 28 32 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row32 : treeBlockF 32 36 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row36 : treeBlockF 36 40 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row40 : treeBlockF 40 44 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row44 : treeBlockF 44 48 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row48 : treeBlockF 48 52 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row52 : treeBlockF 52 56 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row56 : treeBlockF 56 60 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row60 : treeBlockF 60 64 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row64 : treeBlockF 64 68 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row68 : treeBlockF 68 72 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row72 : treeBlockF 72 76 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row76 : treeBlockF 76 80 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row80 : treeBlockF 80 84 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row84 : treeBlockF 84 88 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row88 : treeBlockF 88 92 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row92 : treeBlockF 92 96 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row96 : treeBlockF 96 100 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row100 : treeBlockF 100 104 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row104 : treeBlockF 104 108 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row108 : treeBlockF 108 112 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row112 : treeBlockF 112 116 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row116 : treeBlockF 116 120 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row120 : treeBlockF 120 124 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row124 : treeBlockF 124 128 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row128 : treeBlockF 128 132 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row132 : treeBlockF 132 136 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row136 : treeBlockF 136 140 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row140 : treeBlockF 140 144 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row144 : treeBlockF 144 148 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row148 : treeBlockF 148 152 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row152 : treeBlockF 152 156 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row156 : treeBlockF 156 160 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row160 : treeBlockF 160 164 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row164 : treeBlockF 164 168 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row168 : treeBlockF 168 172 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row172 : treeBlockF 172 176 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row176 : treeBlockF 176 180 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row180 : treeBlockF 180 184 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row184 : treeBlockF 184 188 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row188 : treeBlockF 188 192 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row192 : treeBlockF 192 196 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row196 : treeBlockF 196 200 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row200 : treeBlockF 200 204 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row204 : treeBlockF 204 208 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row208 : treeBlockF 208 212 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row212 : treeBlockF 212 216 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row216 : treeBlockF 216 220 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row220 : treeBlockF 220 224 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row224 : treeBlockF 224 228 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row228 : treeBlockF 228 232 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row232 : treeBlockF 232 236 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row236 : treeBlockF 236 240 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row240 : treeBlockF 240 244 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row244 : treeBlockF 244 248 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row248 : treeBlockF 248 252 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row252 : treeBlockF 252 256 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row256 : treeBlockF 256 260 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row260 : treeBlockF 260 264 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row264 : treeBlockF 264 268 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row268 : treeBlockF 268 272 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row272 : treeBlockF 272 276 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row276 : treeBlockF 276 280 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row280 : treeBlockF 280 284 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row284 : treeBlockF 284 288 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row288 : treeBlockF 288 292 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row292 : treeBlockF 292 296 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row296 : treeBlockF 296 300 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row300 : treeBlockF 300 304 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row304 : treeBlockF 304 308 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row308 : treeBlockF 308 312 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row312 : treeBlockF 312 316 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row316 : treeBlockF 316 320 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row320 : treeBlockF 320 324 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row324 : treeBlockF 324 328 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row328 : treeBlockF 328 332 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row332 : treeBlockF 332 336 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row336 : treeBlockF 336 340 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row340 : treeBlockF 340 344 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row344 : treeBlockF 344 348 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row348 : treeBlockF 348 352 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row352 : treeBlockF 352 356 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row356 : treeBlockF 356 360 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row360 : treeBlockF 360 364 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row364 : treeBlockF 364 368 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row368 : treeBlockF 368 372 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row372 : treeBlockF 372 376 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row376 : treeBlockF 376 380 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row380 : treeBlockF 380 384 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row384 : treeBlockF 384 388 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row388 : treeBlockF 388 392 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row392 : treeBlockF 392 396 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row396 : treeBlockF 396 400 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row400 : treeBlockF 400 404 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row404 : treeBlockF 404 408 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row408 : treeBlockF 408 412 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row412 : treeBlockF 412 416 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row416 : treeBlockF 416 420 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row420 : treeBlockF 420 424 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row424 : treeBlockF 424 428 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row428 : treeBlockF 428 432 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row432 : treeBlockF 432 436 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row436 : treeBlockF 436 440 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row440 : treeBlockF 440 444 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row444 : treeBlockF 444 448 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row448 : treeBlockF 448 452 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row452 : treeBlockF 452 456 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row456 : treeBlockF 456 460 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row460 : treeBlockF 460 464 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row464 : treeBlockF 464 468 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row468 : treeBlockF 468 472 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row472 : treeBlockF 472 476 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row476 : treeBlockF 476 480 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row480 : treeBlockF 480 484 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row484 : treeBlockF 484 488 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row488 : treeBlockF 488 492 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row492 : treeBlockF 492 496 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row496 : treeBlockF 496 500 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row500 : treeBlockF 500 504 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row504 : treeBlockF 504 508 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row508 : treeBlockF 508 512 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row512 : treeBlockF 512 516 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row516 : treeBlockF 516 520 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row520 : treeBlockF 520 524 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row524 : treeBlockF 524 528 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row528 : treeBlockF 528 532 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row532 : treeBlockF 532 536 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row536 : treeBlockF 536 540 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row540 : treeBlockF 540 544 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row544 : treeBlockF 544 548 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row548 : treeBlockF 548 552 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row552 : treeBlockF 552 556 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row556 : treeBlockF 556 560 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row560 : treeBlockF 560 564 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row564 : treeBlockF 564 568 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row568 : treeBlockF 568 572 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row572 : treeBlockF 572 576 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row576 : treeBlockF 576 580 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row580 : treeBlockF 580 584 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row584 : treeBlockF 584 588 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row588 : treeBlockF 588 592 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row592 : treeBlockF 592 596 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row596 : treeBlockF 596 600 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row600 : treeBlockF 600 604 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row604 : treeBlockF 604 608 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row608 : treeBlockF 608 612 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row612 : treeBlockF 612 616 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row616 : treeBlockF 616 620 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row620 : treeBlockF 620 624 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row624 : treeBlockF 624 628 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row628 : treeBlockF 628 632 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row632 : treeBlockF 632 636 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row636 : treeBlockF 636 640 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row640 : treeBlockF 640 644 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row644 : treeBlockF 644 648 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row648 : treeBlockF 648 652 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row652 : treeBlockF 652 656 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row656 : treeBlockF 656 660 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row660 : treeBlockF 660 664 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row664 : treeBlockF 664 668 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row668 : treeBlockF 668 672 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row672 : treeBlockF 672 676 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row676 : treeBlockF 676 680 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row680 : treeBlockF 680 684 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row684 : treeBlockF 684 688 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row688 : treeBlockF 688 692 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row692 : treeBlockF 692 696 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row696 : treeBlockF 696 700 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row700 : treeBlockF 700 704 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row704 : treeBlockF 704 708 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row708 : treeBlockF 708 712 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row712 : treeBlockF 712 716 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row716 : treeBlockF 716 720 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row720 : treeBlockF 720 724 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row724 : treeBlockF 724 728 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row728 : treeBlockF 728 732 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row732 : treeBlockF 732 736 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row736 : treeBlockF 736 740 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row740 : treeBlockF 740 744 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row744 : treeBlockF 744 748 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row748 : treeBlockF 748 752 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row752 : treeBlockF 752 756 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row756 : treeBlockF 756 760 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row760 : treeBlockF 760 764 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row764 : treeBlockF 764 768 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row768 : treeBlockF 768 772 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row772 : treeBlockF 772 776 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row776 : treeBlockF 776 780 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row780 : treeBlockF 780 784 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row784 : treeBlockF 784 788 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row788 : treeBlockF 788 792 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row792 : treeBlockF 792 796 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row796 : treeBlockF 796 800 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row800 : treeBlockF 800 804 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row804 : treeBlockF 804 808 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row808 : treeBlockF 808 812 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row812 : treeBlockF 812 816 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row816 : treeBlockF 816 820 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row820 : treeBlockF 820 824 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row824 : treeBlockF 824 828 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row828 : treeBlockF 828 832 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row832 : treeBlockF 832 836 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row836 : treeBlockF 836 840 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row840 : treeBlockF 840 844 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row844 : treeBlockF 844 848 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row848 : treeBlockF 848 852 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row852 : treeBlockF 852 856 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row856 : treeBlockF 856 860 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row860 : treeBlockF 860 864 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row864 : treeBlockF 864 868 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row868 : treeBlockF 868 872 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row872 : treeBlockF 872 876 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row876 : treeBlockF 876 880 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row880 : treeBlockF 880 884 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row884 : treeBlockF 884 888 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row888 : treeBlockF 888 892 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row892 : treeBlockF 892 896 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row896 : treeBlockF 896 900 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row900 : treeBlockF 900 904 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row904 : treeBlockF 904 908 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row908 : treeBlockF 908 912 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row912 : treeBlockF 912 916 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row916 : treeBlockF 916 920 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row920 : treeBlockF 920 924 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row924 : treeBlockF 924 928 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row928 : treeBlockF 928 932 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row932 : treeBlockF 932 936 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row936 : treeBlockF 936 940 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row940 : treeBlockF 940 944 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row944 : treeBlockF 944 948 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row948 : treeBlockF 948 952 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row952 : treeBlockF 952 956 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row956 : treeBlockF 956 960 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row960 : treeBlockF 960 964 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row964 : treeBlockF 964 968 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row968 : treeBlockF 968 972 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row972 : treeBlockF 972 976 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row976 : treeBlockF 976 980 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row980 : treeBlockF 980 984 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row984 : treeBlockF 984 988 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row988 : treeBlockF 988 992 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row992 : treeBlockF 992 996 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row996 : treeBlockF 996 1000 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1000 : treeBlockF 1000 1004 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1004 : treeBlockF 1004 1008 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1008 : treeBlockF 1008 1012 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1012 : treeBlockF 1012 1016 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1016 : treeBlockF 1016 1020 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1020 : treeBlockF 1020 1024 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1024 : treeBlockF 1024 1028 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1028 : treeBlockF 1028 1032 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1032 : treeBlockF 1032 1036 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1036 : treeBlockF 1036 1040 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1040 : treeBlockF 1040 1044 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1044 : treeBlockF 1044 1048 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1048 : treeBlockF 1048 1052 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1052 : treeBlockF 1052 1056 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1056 : treeBlockF 1056 1060 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1060 : treeBlockF 1060 1064 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1064 : treeBlockF 1064 1068 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1068 : treeBlockF 1068 1072 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1072 : treeBlockF 1072 1076 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1076 : treeBlockF 1076 1080 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1080 : treeBlockF 1080 1084 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1084 : treeBlockF 1084 1088 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1088 : treeBlockF 1088 1092 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1092 : treeBlockF 1092 1096 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1096 : treeBlockF 1096 1100 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1100 : treeBlockF 1100 1104 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1104 : treeBlockF 1104 1108 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1108 : treeBlockF 1108 1112 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1112 : treeBlockF 1112 1116 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1116 : treeBlockF 1116 1120 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1120 : treeBlockF 1120 1124 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1124 : treeBlockF 1124 1128 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1128 : treeBlockF 1128 1132 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1132 : treeBlockF 1132 1136 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1136 : treeBlockF 1136 1140 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1140 : treeBlockF 1140 1144 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1144 : treeBlockF 1144 1148 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1148 : treeBlockF 1148 1152 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1152 : treeBlockF 1152 1156 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1156 : treeBlockF 1156 1160 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1160 : treeBlockF 1160 1164 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1164 : treeBlockF 1164 1168 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1168 : treeBlockF 1168 1172 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1172 : treeBlockF 1172 1176 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1176 : treeBlockF 1176 1180 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1180 : treeBlockF 1180 1184 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1184 : treeBlockF 1184 1188 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1188 : treeBlockF 1188 1192 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1192 : treeBlockF 1192 1196 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1196 : treeBlockF 1196 1200 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1200 : treeBlockF 1200 1204 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1204 : treeBlockF 1204 1208 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1208 : treeBlockF 1208 1212 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1212 : treeBlockF 1212 1216 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1216 : treeBlockF 1216 1220 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1220 : treeBlockF 1220 1224 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1224 : treeBlockF 1224 1228 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1228 : treeBlockF 1228 1232 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1232 : treeBlockF 1232 1236 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1236 : treeBlockF 1236 1240 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1240 : treeBlockF 1240 1244 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1244 : treeBlockF 1244 1248 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1248 : treeBlockF 1248 1252 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1252 : treeBlockF 1252 1256 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1256 : treeBlockF 1256 1260 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1260 : treeBlockF 1260 1264 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1264 : treeBlockF 1264 1268 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1268 : treeBlockF 1268 1272 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1272 : treeBlockF 1272 1276 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1276 : treeBlockF 1276 1280 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1280 : treeBlockF 1280 1284 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1284 : treeBlockF 1284 1288 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1288 : treeBlockF 1288 1292 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1292 : treeBlockF 1292 1296 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1296 : treeBlockF 1296 1300 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1300 : treeBlockF 1300 1304 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1304 : treeBlockF 1304 1308 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1308 : treeBlockF 1308 1312 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1312 : treeBlockF 1312 1316 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1316 : treeBlockF 1316 1320 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1320 : treeBlockF 1320 1324 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1324 : treeBlockF 1324 1328 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1328 : treeBlockF 1328 1332 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1332 : treeBlockF 1332 1336 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1336 : treeBlockF 1336 1340 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1340 : treeBlockF 1340 1344 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1344 : treeBlockF 1344 1348 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1348 : treeBlockF 1348 1352 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1352 : treeBlockF 1352 1356 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1356 : treeBlockF 1356 1360 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1360 : treeBlockF 1360 1364 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1364 : treeBlockF 1364 1368 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1368 : treeBlockF 1368 1372 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1372 : treeBlockF 1372 1376 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1376 : treeBlockF 1376 1380 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1380 : treeBlockF 1380 1384 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1384 : treeBlockF 1384 1388 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1388 : treeBlockF 1388 1392 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1392 : treeBlockF 1392 1396 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1396 : treeBlockF 1396 1400 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1400 : treeBlockF 1400 1404 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1404 : treeBlockF 1404 1408 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1408 : treeBlockF 1408 1412 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1412 : treeBlockF 1412 1416 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1416 : treeBlockF 1416 1420 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1420 : treeBlockF 1420 1424 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1424 : treeBlockF 1424 1428 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1428 : treeBlockF 1428 1432 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1432 : treeBlockF 1432 1436 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1436 : treeBlockF 1436 1440 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1440 : treeBlockF 1440 1444 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1444 : treeBlockF 1444 1448 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1448 : treeBlockF 1448 1452 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1452 : treeBlockF 1452 1456 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1456 : treeBlockF 1456 1460 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1460 : treeBlockF 1460 1464 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1464 : treeBlockF 1464 1468 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1468 : treeBlockF 1468 1472 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1472 : treeBlockF 1472 1476 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1476 : treeBlockF 1476 1480 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1480 : treeBlockF 1480 1484 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1484 : treeBlockF 1484 1488 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1488 : treeBlockF 1488 1492 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1492 : treeBlockF 1492 1496 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1496 : treeBlockF 1496 1500 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1500 : treeBlockF 1500 1504 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1504 : treeBlockF 1504 1508 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1508 : treeBlockF 1508 1512 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1512 : treeBlockF 1512 1516 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1516 : treeBlockF 1516 1520 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1520 : treeBlockF 1520 1524 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1524 : treeBlockF 1524 1528 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1528 : treeBlockF 1528 1532 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1532 : treeBlockF 1532 1536 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1536 : treeBlockF 1536 1540 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1540 : treeBlockF 1540 1544 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1544 : treeBlockF 1544 1548 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1548 : treeBlockF 1548 1552 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1552 : treeBlockF 1552 1556 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1556 : treeBlockF 1556 1560 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1560 : treeBlockF 1560 1564 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1564 : treeBlockF 1564 1568 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1568 : treeBlockF 1568 1572 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1572 : treeBlockF 1572 1576 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1576 : treeBlockF 1576 1580 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1580 : treeBlockF 1580 1584 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1584 : treeBlockF 1584 1588 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1588 : treeBlockF 1588 1592 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1592 : treeBlockF 1592 1596 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1596 : treeBlockF 1596 1600 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1600 : treeBlockF 1600 1604 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1604 : treeBlockF 1604 1608 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1608 : treeBlockF 1608 1612 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1612 : treeBlockF 1612 1616 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1616 : treeBlockF 1616 1620 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1620 : treeBlockF 1620 1624 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1624 : treeBlockF 1624 1628 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1628 : treeBlockF 1628 1632 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1632 : treeBlockF 1632 1636 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1636 : treeBlockF 1636 1640 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1640 : treeBlockF 1640 1644 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1644 : treeBlockF 1644 1648 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1648 : treeBlockF 1648 1652 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1652 : treeBlockF 1652 1656 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1656 : treeBlockF 1656 1660 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1660 : treeBlockF 1660 1664 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1664 : treeBlockF 1664 1668 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1668 : treeBlockF 1668 1672 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1672 : treeBlockF 1672 1676 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1676 : treeBlockF 1676 1680 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1680 : treeBlockF 1680 1684 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1684 : treeBlockF 1684 1688 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1688 : treeBlockF 1688 1692 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1692 : treeBlockF 1692 1696 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1696 : treeBlockF 1696 1700 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1700 : treeBlockF 1700 1704 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1704 : treeBlockF 1704 1708 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1708 : treeBlockF 1708 1712 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1712 : treeBlockF 1712 1716 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1716 : treeBlockF 1716 1720 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1720 : treeBlockF 1720 1724 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1724 : treeBlockF 1724 1728 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1728 : treeBlockF 1728 1732 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1732 : treeBlockF 1732 1736 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1736 : treeBlockF 1736 1740 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1740 : treeBlockF 1740 1744 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1744 : treeBlockF 1744 1748 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1748 : treeBlockF 1748 1752 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1752 : treeBlockF 1752 1756 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1756 : treeBlockF 1756 1760 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1760 : treeBlockF 1760 1764 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1764 : treeBlockF 1764 1768 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1768 : treeBlockF 1768 1772 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1772 : treeBlockF 1772 1776 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1776 : treeBlockF 1776 1780 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1780 : treeBlockF 1780 1784 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1784 : treeBlockF 1784 1788 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1788 : treeBlockF 1788 1792 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1792 : treeBlockF 1792 1796 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1796 : treeBlockF 1796 1800 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1800 : treeBlockF 1800 1804 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1804 : treeBlockF 1804 1808 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1808 : treeBlockF 1808 1812 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1812 : treeBlockF 1812 1816 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1816 : treeBlockF 1816 1820 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1820 : treeBlockF 1820 1824 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1824 : treeBlockF 1824 1828 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1828 : treeBlockF 1828 1832 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1832 : treeBlockF 1832 1836 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1836 : treeBlockF 1836 1840 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1840 : treeBlockF 1840 1844 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1844 : treeBlockF 1844 1848 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1848 : treeBlockF 1848 1852 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1852 : treeBlockF 1852 1856 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1856 : treeBlockF 1856 1860 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1860 : treeBlockF 1860 1864 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1864 : treeBlockF 1864 1868 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1868 : treeBlockF 1868 1872 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1872 : treeBlockF 1872 1876 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1876 : treeBlockF 1876 1880 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1880 : treeBlockF 1880 1884 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1884 : treeBlockF 1884 1888 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1888 : treeBlockF 1888 1892 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1892 : treeBlockF 1892 1896 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1896 : treeBlockF 1896 1900 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1900 : treeBlockF 1900 1904 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1904 : treeBlockF 1904 1908 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1908 : treeBlockF 1908 1912 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1912 : treeBlockF 1912 1916 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1916 : treeBlockF 1916 1920 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1920 : treeBlockF 1920 1924 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1924 : treeBlockF 1924 1928 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1928 : treeBlockF 1928 1932 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1932 : treeBlockF 1932 1936 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1936 : treeBlockF 1936 1940 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1940 : treeBlockF 1940 1944 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1944 : treeBlockF 1944 1948 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1948 : treeBlockF 1948 1952 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1952 : treeBlockF 1952 1956 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1956 : treeBlockF 1956 1960 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1960 : treeBlockF 1960 1964 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1964 : treeBlockF 1964 1968 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1968 : treeBlockF 1968 1972 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1972 : treeBlockF 1972 1976 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1976 : treeBlockF 1976 1980 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1980 : treeBlockF 1980 1984 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1984 : treeBlockF 1984 1988 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1988 : treeBlockF 1988 1992 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1992 : treeBlockF 1992 1996 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1996 : treeBlockF 1996 2000 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2000 : treeBlockF 2000 2004 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2004 : treeBlockF 2004 2008 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2008 : treeBlockF 2008 2012 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2012 : treeBlockF 2012 2016 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2016 : treeBlockF 2016 2020 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2020 : treeBlockF 2020 2024 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2024 : treeBlockF 2024 2028 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2028 : treeBlockF 2028 2032 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2032 : treeBlockF 2032 2036 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2036 : treeBlockF 2036 2040 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2040 : treeBlockF 2040 2044 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2044 : treeBlockF 2044 2048 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2048 : treeBlockF 2048 2052 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2052 : treeBlockF 2052 2056 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2056 : treeBlockF 2056 2060 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2060 : treeBlockF 2060 2064 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2064 : treeBlockF 2064 2068 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2068 : treeBlockF 2068 2072 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2072 : treeBlockF 2072 2076 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2076 : treeBlockF 2076 2080 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2080 : treeBlockF 2080 2084 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2084 : treeBlockF 2084 2088 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2088 : treeBlockF 2088 2092 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2092 : treeBlockF 2092 2096 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2096 : treeBlockF 2096 2100 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2100 : treeBlockF 2100 2104 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2104 : treeBlockF 2104 2108 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2108 : treeBlockF 2108 2112 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2112 : treeBlockF 2112 2116 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2116 : treeBlockF 2116 2120 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2120 : treeBlockF 2120 2124 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2124 : treeBlockF 2124 2128 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2128 : treeBlockF 2128 2132 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2132 : treeBlockF 2132 2136 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2136 : treeBlockF 2136 2140 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2140 : treeBlockF 2140 2144 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2144 : treeBlockF 2144 2148 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2148 : treeBlockF 2148 2152 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2152 : treeBlockF 2152 2156 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2156 : treeBlockF 2156 2160 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2160 : treeBlockF 2160 2164 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2164 : treeBlockF 2164 2168 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2168 : treeBlockF 2168 2172 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2172 : treeBlockF 2172 2176 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2176 : treeBlockF 2176 2180 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2180 : treeBlockF 2180 2184 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2184 : treeBlockF 2184 2188 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2188 : treeBlockF 2188 2192 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2192 : treeBlockF 2192 2196 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2196 : treeBlockF 2196 2200 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2200 : treeBlockF 2200 2204 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2204 : treeBlockF 2204 2208 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2208 : treeBlockF 2208 2212 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2212 : treeBlockF 2212 2216 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2216 : treeBlockF 2216 2220 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2220 : treeBlockF 2220 2224 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2224 : treeBlockF 2224 2228 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2228 : treeBlockF 2228 2232 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2232 : treeBlockF 2232 2236 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2236 : treeBlockF 2236 2240 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2240 : treeBlockF 2240 2244 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2244 : treeBlockF 2244 2248 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2248 : treeBlockF 2248 2252 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2252 : treeBlockF 2252 2256 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2256 : treeBlockF 2256 2260 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2260 : treeBlockF 2260 2264 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2264 : treeBlockF 2264 2268 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2268 : treeBlockF 2268 2272 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2272 : treeBlockF 2272 2276 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2276 : treeBlockF 2276 2280 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2280 : treeBlockF 2280 2284 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2284 : treeBlockF 2284 2288 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2288 : treeBlockF 2288 2292 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2292 : treeBlockF 2292 2296 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2296 : treeBlockF 2296 2300 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2300 : treeBlockF 2300 2304 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2304 : treeBlockF 2304 2308 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2308 : treeBlockF 2308 2312 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2312 : treeBlockF 2312 2316 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2316 : treeBlockF 2316 2320 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2320 : treeBlockF 2320 2324 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2324 : treeBlockF 2324 2328 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2328 : treeBlockF 2328 2332 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2332 : treeBlockF 2332 2336 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2336 : treeBlockF 2336 2340 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2340 : treeBlockF 2340 2344 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2344 : treeBlockF 2344 2348 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2348 : treeBlockF 2348 2352 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2352 : treeBlockF 2352 2356 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2356 : treeBlockF 2356 2360 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2360 : treeBlockF 2360 2364 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2364 : treeBlockF 2364 2368 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2368 : treeBlockF 2368 2372 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2372 : treeBlockF 2372 2376 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2376 : treeBlockF 2376 2380 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2380 : treeBlockF 2380 2384 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2384 : treeBlockF 2384 2388 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2388 : treeBlockF 2388 2392 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2392 : treeBlockF 2392 2396 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2396 : treeBlockF 2396 2400 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2400 : treeBlockF 2400 2404 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2404 : treeBlockF 2404 2408 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2408 : treeBlockF 2408 2412 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2412 : treeBlockF 2412 2416 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2416 : treeBlockF 2416 2420 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2420 : treeBlockF 2420 2424 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2424 : treeBlockF 2424 2428 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2428 : treeBlockF 2428 2432 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2432 : treeBlockF 2432 2436 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2436 : treeBlockF 2436 2440 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2440 : treeBlockF 2440 2444 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2444 : treeBlockF 2444 2448 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2448 : treeBlockF 2448 2452 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2452 : treeBlockF 2452 2456 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2456 : treeBlockF 2456 2460 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2460 : treeBlockF 2460 2464 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2464 : treeBlockF 2464 2468 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2468 : treeBlockF 2468 2472 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2472 : treeBlockF 2472 2476 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2476 : treeBlockF 2476 2480 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2480 : treeBlockF 2480 2484 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2484 : treeBlockF 2484 2488 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2488 : treeBlockF 2488 2492 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2492 : treeBlockF 2492 2496 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2496 : treeBlockF 2496 2500 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2500 : treeBlockF 2500 2504 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2504 : treeBlockF 2504 2508 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2508 : treeBlockF 2508 2512 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2512 : treeBlockF 2512 2516 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2516 : treeBlockF 2516 2520 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2520 : treeBlockF 2520 2524 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2524 : treeBlockF 2524 2528 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2528 : treeBlockF 2528 2532 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2532 : treeBlockF 2532 2536 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2536 : treeBlockF 2536 2540 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2540 : treeBlockF 2540 2544 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2544 : treeBlockF 2544 2548 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2548 : treeBlockF 2548 2552 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2552 : treeBlockF 2552 2556 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2556 : treeBlockF 2556 2560 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2560 : treeBlockF 2560 2564 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2564 : treeBlockF 2564 2568 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2568 : treeBlockF 2568 2572 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2572 : treeBlockF 2572 2576 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2576 : treeBlockF 2576 2580 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2580 : treeBlockF 2580 2584 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2584 : treeBlockF 2584 2588 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2588 : treeBlockF 2588 2592 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2592 : treeBlockF 2592 2596 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2596 : treeBlockF 2596 2599 cert_check = true := by decide +kernel
theorem cert_nodes : ∀ i, 0 ≤ i → i < 2599 → cert_check i = true :=
  joinBlockSpecs
    (joinBlockSpecs
      (joinBlockSpecs
        (joinBlockSpecs
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row0)
                    (blockSpec row4))
                  (joinBlockSpecs
                    (blockSpec row8)
                    (joinBlockSpecs
                      (blockSpec row12)
                      (blockSpec row16))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row20)
                    (blockSpec row24))
                  (joinBlockSpecs
                    (blockSpec row28)
                    (joinBlockSpecs
                      (blockSpec row32)
                      (blockSpec row36)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row40)
                    (blockSpec row44))
                  (joinBlockSpecs
                    (blockSpec row48)
                    (joinBlockSpecs
                      (blockSpec row52)
                      (blockSpec row56))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row60)
                    (blockSpec row64))
                  (joinBlockSpecs
                    (blockSpec row68)
                    (joinBlockSpecs
                      (blockSpec row72)
                      (blockSpec row76))))))
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row80)
                    (blockSpec row84))
                  (joinBlockSpecs
                    (blockSpec row88)
                    (joinBlockSpecs
                      (blockSpec row92)
                      (blockSpec row96))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row100)
                    (blockSpec row104))
                  (joinBlockSpecs
                    (blockSpec row108)
                    (joinBlockSpecs
                      (blockSpec row112)
                      (blockSpec row116)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row120)
                    (blockSpec row124))
                  (joinBlockSpecs
                    (blockSpec row128)
                    (joinBlockSpecs
                      (blockSpec row132)
                      (blockSpec row136))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row140)
                    (blockSpec row144))
                  (joinBlockSpecs
                    (blockSpec row148)
                    (joinBlockSpecs
                      (blockSpec row152)
                      (blockSpec row156)))))))
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row160)
                    (blockSpec row164))
                  (joinBlockSpecs
                    (blockSpec row168)
                    (joinBlockSpecs
                      (blockSpec row172)
                      (blockSpec row176))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row180)
                    (blockSpec row184))
                  (joinBlockSpecs
                    (blockSpec row188)
                    (joinBlockSpecs
                      (blockSpec row192)
                      (blockSpec row196)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row200)
                    (blockSpec row204))
                  (joinBlockSpecs
                    (blockSpec row208)
                    (joinBlockSpecs
                      (blockSpec row212)
                      (blockSpec row216))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row220)
                    (blockSpec row224))
                  (joinBlockSpecs
                    (blockSpec row228)
                    (joinBlockSpecs
                      (blockSpec row232)
                      (blockSpec row236))))))
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row240)
                    (blockSpec row244))
                  (joinBlockSpecs
                    (blockSpec row248)
                    (joinBlockSpecs
                      (blockSpec row252)
                      (blockSpec row256))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row260)
                    (blockSpec row264))
                  (joinBlockSpecs
                    (blockSpec row268)
                    (joinBlockSpecs
                      (blockSpec row272)
                      (blockSpec row276)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row280)
                    (blockSpec row284))
                  (joinBlockSpecs
                    (blockSpec row288)
                    (joinBlockSpecs
                      (blockSpec row292)
                      (blockSpec row296))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row300)
                    (joinBlockSpecs
                      (blockSpec row304)
                      (blockSpec row308)))
                  (joinBlockSpecs
                    (blockSpec row312)
                    (joinBlockSpecs
                      (blockSpec row316)
                      (blockSpec row320))))))))
        (joinBlockSpecs
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row324)
                    (blockSpec row328))
                  (joinBlockSpecs
                    (blockSpec row332)
                    (joinBlockSpecs
                      (blockSpec row336)
                      (blockSpec row340))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row344)
                    (blockSpec row348))
                  (joinBlockSpecs
                    (blockSpec row352)
                    (joinBlockSpecs
                      (blockSpec row356)
                      (blockSpec row360)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row364)
                    (blockSpec row368))
                  (joinBlockSpecs
                    (blockSpec row372)
                    (joinBlockSpecs
                      (blockSpec row376)
                      (blockSpec row380))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row384)
                    (blockSpec row388))
                  (joinBlockSpecs
                    (blockSpec row392)
                    (joinBlockSpecs
                      (blockSpec row396)
                      (blockSpec row400))))))
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row404)
                    (blockSpec row408))
                  (joinBlockSpecs
                    (blockSpec row412)
                    (joinBlockSpecs
                      (blockSpec row416)
                      (blockSpec row420))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row424)
                    (blockSpec row428))
                  (joinBlockSpecs
                    (blockSpec row432)
                    (joinBlockSpecs
                      (blockSpec row436)
                      (blockSpec row440)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row444)
                    (blockSpec row448))
                  (joinBlockSpecs
                    (blockSpec row452)
                    (joinBlockSpecs
                      (blockSpec row456)
                      (blockSpec row460))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row464)
                    (blockSpec row468))
                  (joinBlockSpecs
                    (blockSpec row472)
                    (joinBlockSpecs
                      (blockSpec row476)
                      (blockSpec row480)))))))
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row484)
                    (blockSpec row488))
                  (joinBlockSpecs
                    (blockSpec row492)
                    (joinBlockSpecs
                      (blockSpec row496)
                      (blockSpec row500))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row504)
                    (blockSpec row508))
                  (joinBlockSpecs
                    (blockSpec row512)
                    (joinBlockSpecs
                      (blockSpec row516)
                      (blockSpec row520)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row524)
                    (blockSpec row528))
                  (joinBlockSpecs
                    (blockSpec row532)
                    (joinBlockSpecs
                      (blockSpec row536)
                      (blockSpec row540))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row544)
                    (blockSpec row548))
                  (joinBlockSpecs
                    (blockSpec row552)
                    (joinBlockSpecs
                      (blockSpec row556)
                      (blockSpec row560))))))
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row564)
                    (blockSpec row568))
                  (joinBlockSpecs
                    (blockSpec row572)
                    (joinBlockSpecs
                      (blockSpec row576)
                      (blockSpec row580))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row584)
                    (blockSpec row588))
                  (joinBlockSpecs
                    (blockSpec row592)
                    (joinBlockSpecs
                      (blockSpec row596)
                      (blockSpec row600)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row604)
                    (blockSpec row608))
                  (joinBlockSpecs
                    (blockSpec row612)
                    (joinBlockSpecs
                      (blockSpec row616)
                      (blockSpec row620))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row624)
                    (joinBlockSpecs
                      (blockSpec row628)
                      (blockSpec row632)))
                  (joinBlockSpecs
                    (blockSpec row636)
                    (joinBlockSpecs
                      (blockSpec row640)
                      (blockSpec row644)))))))))
      (joinBlockSpecs
        (joinBlockSpecs
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row648)
                    (blockSpec row652))
                  (joinBlockSpecs
                    (blockSpec row656)
                    (joinBlockSpecs
                      (blockSpec row660)
                      (blockSpec row664))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row668)
                    (blockSpec row672))
                  (joinBlockSpecs
                    (blockSpec row676)
                    (joinBlockSpecs
                      (blockSpec row680)
                      (blockSpec row684)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row688)
                    (blockSpec row692))
                  (joinBlockSpecs
                    (blockSpec row696)
                    (joinBlockSpecs
                      (blockSpec row700)
                      (blockSpec row704))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row708)
                    (blockSpec row712))
                  (joinBlockSpecs
                    (blockSpec row716)
                    (joinBlockSpecs
                      (blockSpec row720)
                      (blockSpec row724))))))
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row728)
                    (blockSpec row732))
                  (joinBlockSpecs
                    (blockSpec row736)
                    (joinBlockSpecs
                      (blockSpec row740)
                      (blockSpec row744))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row748)
                    (blockSpec row752))
                  (joinBlockSpecs
                    (blockSpec row756)
                    (joinBlockSpecs
                      (blockSpec row760)
                      (blockSpec row764)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row768)
                    (blockSpec row772))
                  (joinBlockSpecs
                    (blockSpec row776)
                    (joinBlockSpecs
                      (blockSpec row780)
                      (blockSpec row784))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row788)
                    (blockSpec row792))
                  (joinBlockSpecs
                    (blockSpec row796)
                    (joinBlockSpecs
                      (blockSpec row800)
                      (blockSpec row804)))))))
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row808)
                    (blockSpec row812))
                  (joinBlockSpecs
                    (blockSpec row816)
                    (joinBlockSpecs
                      (blockSpec row820)
                      (blockSpec row824))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row828)
                    (blockSpec row832))
                  (joinBlockSpecs
                    (blockSpec row836)
                    (joinBlockSpecs
                      (blockSpec row840)
                      (blockSpec row844)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row848)
                    (blockSpec row852))
                  (joinBlockSpecs
                    (blockSpec row856)
                    (joinBlockSpecs
                      (blockSpec row860)
                      (blockSpec row864))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row868)
                    (blockSpec row872))
                  (joinBlockSpecs
                    (blockSpec row876)
                    (joinBlockSpecs
                      (blockSpec row880)
                      (blockSpec row884))))))
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row888)
                    (blockSpec row892))
                  (joinBlockSpecs
                    (blockSpec row896)
                    (joinBlockSpecs
                      (blockSpec row900)
                      (blockSpec row904))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row908)
                    (blockSpec row912))
                  (joinBlockSpecs
                    (blockSpec row916)
                    (joinBlockSpecs
                      (blockSpec row920)
                      (blockSpec row924)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row928)
                    (blockSpec row932))
                  (joinBlockSpecs
                    (blockSpec row936)
                    (joinBlockSpecs
                      (blockSpec row940)
                      (blockSpec row944))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row948)
                    (joinBlockSpecs
                      (blockSpec row952)
                      (blockSpec row956)))
                  (joinBlockSpecs
                    (blockSpec row960)
                    (joinBlockSpecs
                      (blockSpec row964)
                      (blockSpec row968))))))))
        (joinBlockSpecs
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row972)
                    (blockSpec row976))
                  (joinBlockSpecs
                    (blockSpec row980)
                    (joinBlockSpecs
                      (blockSpec row984)
                      (blockSpec row988))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row992)
                    (blockSpec row996))
                  (joinBlockSpecs
                    (blockSpec row1000)
                    (joinBlockSpecs
                      (blockSpec row1004)
                      (blockSpec row1008)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1012)
                    (blockSpec row1016))
                  (joinBlockSpecs
                    (blockSpec row1020)
                    (joinBlockSpecs
                      (blockSpec row1024)
                      (blockSpec row1028))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1032)
                    (blockSpec row1036))
                  (joinBlockSpecs
                    (blockSpec row1040)
                    (joinBlockSpecs
                      (blockSpec row1044)
                      (blockSpec row1048))))))
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1052)
                    (blockSpec row1056))
                  (joinBlockSpecs
                    (blockSpec row1060)
                    (joinBlockSpecs
                      (blockSpec row1064)
                      (blockSpec row1068))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1072)
                    (blockSpec row1076))
                  (joinBlockSpecs
                    (blockSpec row1080)
                    (joinBlockSpecs
                      (blockSpec row1084)
                      (blockSpec row1088)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1092)
                    (blockSpec row1096))
                  (joinBlockSpecs
                    (blockSpec row1100)
                    (joinBlockSpecs
                      (blockSpec row1104)
                      (blockSpec row1108))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1112)
                    (joinBlockSpecs
                      (blockSpec row1116)
                      (blockSpec row1120)))
                  (joinBlockSpecs
                    (blockSpec row1124)
                    (joinBlockSpecs
                      (blockSpec row1128)
                      (blockSpec row1132)))))))
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1136)
                    (blockSpec row1140))
                  (joinBlockSpecs
                    (blockSpec row1144)
                    (joinBlockSpecs
                      (blockSpec row1148)
                      (blockSpec row1152))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1156)
                    (blockSpec row1160))
                  (joinBlockSpecs
                    (blockSpec row1164)
                    (joinBlockSpecs
                      (blockSpec row1168)
                      (blockSpec row1172)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1176)
                    (blockSpec row1180))
                  (joinBlockSpecs
                    (blockSpec row1184)
                    (joinBlockSpecs
                      (blockSpec row1188)
                      (blockSpec row1192))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1196)
                    (blockSpec row1200))
                  (joinBlockSpecs
                    (blockSpec row1204)
                    (joinBlockSpecs
                      (blockSpec row1208)
                      (blockSpec row1212))))))
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1216)
                    (blockSpec row1220))
                  (joinBlockSpecs
                    (blockSpec row1224)
                    (joinBlockSpecs
                      (blockSpec row1228)
                      (blockSpec row1232))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1236)
                    (blockSpec row1240))
                  (joinBlockSpecs
                    (blockSpec row1244)
                    (joinBlockSpecs
                      (blockSpec row1248)
                      (blockSpec row1252)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1256)
                    (blockSpec row1260))
                  (joinBlockSpecs
                    (blockSpec row1264)
                    (joinBlockSpecs
                      (blockSpec row1268)
                      (blockSpec row1272))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1276)
                    (joinBlockSpecs
                      (blockSpec row1280)
                      (blockSpec row1284)))
                  (joinBlockSpecs
                    (blockSpec row1288)
                    (joinBlockSpecs
                      (blockSpec row1292)
                      (blockSpec row1296))))))))))
    (joinBlockSpecs
      (joinBlockSpecs
        (joinBlockSpecs
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1300)
                    (blockSpec row1304))
                  (joinBlockSpecs
                    (blockSpec row1308)
                    (joinBlockSpecs
                      (blockSpec row1312)
                      (blockSpec row1316))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1320)
                    (blockSpec row1324))
                  (joinBlockSpecs
                    (blockSpec row1328)
                    (joinBlockSpecs
                      (blockSpec row1332)
                      (blockSpec row1336)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1340)
                    (blockSpec row1344))
                  (joinBlockSpecs
                    (blockSpec row1348)
                    (joinBlockSpecs
                      (blockSpec row1352)
                      (blockSpec row1356))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1360)
                    (blockSpec row1364))
                  (joinBlockSpecs
                    (blockSpec row1368)
                    (joinBlockSpecs
                      (blockSpec row1372)
                      (blockSpec row1376))))))
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1380)
                    (blockSpec row1384))
                  (joinBlockSpecs
                    (blockSpec row1388)
                    (joinBlockSpecs
                      (blockSpec row1392)
                      (blockSpec row1396))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1400)
                    (blockSpec row1404))
                  (joinBlockSpecs
                    (blockSpec row1408)
                    (joinBlockSpecs
                      (blockSpec row1412)
                      (blockSpec row1416)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1420)
                    (blockSpec row1424))
                  (joinBlockSpecs
                    (blockSpec row1428)
                    (joinBlockSpecs
                      (blockSpec row1432)
                      (blockSpec row1436))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1440)
                    (blockSpec row1444))
                  (joinBlockSpecs
                    (blockSpec row1448)
                    (joinBlockSpecs
                      (blockSpec row1452)
                      (blockSpec row1456)))))))
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1460)
                    (blockSpec row1464))
                  (joinBlockSpecs
                    (blockSpec row1468)
                    (joinBlockSpecs
                      (blockSpec row1472)
                      (blockSpec row1476))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1480)
                    (blockSpec row1484))
                  (joinBlockSpecs
                    (blockSpec row1488)
                    (joinBlockSpecs
                      (blockSpec row1492)
                      (blockSpec row1496)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1500)
                    (blockSpec row1504))
                  (joinBlockSpecs
                    (blockSpec row1508)
                    (joinBlockSpecs
                      (blockSpec row1512)
                      (blockSpec row1516))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1520)
                    (blockSpec row1524))
                  (joinBlockSpecs
                    (blockSpec row1528)
                    (joinBlockSpecs
                      (blockSpec row1532)
                      (blockSpec row1536))))))
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1540)
                    (blockSpec row1544))
                  (joinBlockSpecs
                    (blockSpec row1548)
                    (joinBlockSpecs
                      (blockSpec row1552)
                      (blockSpec row1556))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1560)
                    (blockSpec row1564))
                  (joinBlockSpecs
                    (blockSpec row1568)
                    (joinBlockSpecs
                      (blockSpec row1572)
                      (blockSpec row1576)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1580)
                    (blockSpec row1584))
                  (joinBlockSpecs
                    (blockSpec row1588)
                    (joinBlockSpecs
                      (blockSpec row1592)
                      (blockSpec row1596))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1600)
                    (joinBlockSpecs
                      (blockSpec row1604)
                      (blockSpec row1608)))
                  (joinBlockSpecs
                    (blockSpec row1612)
                    (joinBlockSpecs
                      (blockSpec row1616)
                      (blockSpec row1620))))))))
        (joinBlockSpecs
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1624)
                    (blockSpec row1628))
                  (joinBlockSpecs
                    (blockSpec row1632)
                    (joinBlockSpecs
                      (blockSpec row1636)
                      (blockSpec row1640))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1644)
                    (blockSpec row1648))
                  (joinBlockSpecs
                    (blockSpec row1652)
                    (joinBlockSpecs
                      (blockSpec row1656)
                      (blockSpec row1660)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1664)
                    (blockSpec row1668))
                  (joinBlockSpecs
                    (blockSpec row1672)
                    (joinBlockSpecs
                      (blockSpec row1676)
                      (blockSpec row1680))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1684)
                    (blockSpec row1688))
                  (joinBlockSpecs
                    (blockSpec row1692)
                    (joinBlockSpecs
                      (blockSpec row1696)
                      (blockSpec row1700))))))
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1704)
                    (blockSpec row1708))
                  (joinBlockSpecs
                    (blockSpec row1712)
                    (joinBlockSpecs
                      (blockSpec row1716)
                      (blockSpec row1720))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1724)
                    (blockSpec row1728))
                  (joinBlockSpecs
                    (blockSpec row1732)
                    (joinBlockSpecs
                      (blockSpec row1736)
                      (blockSpec row1740)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1744)
                    (blockSpec row1748))
                  (joinBlockSpecs
                    (blockSpec row1752)
                    (joinBlockSpecs
                      (blockSpec row1756)
                      (blockSpec row1760))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1764)
                    (blockSpec row1768))
                  (joinBlockSpecs
                    (blockSpec row1772)
                    (joinBlockSpecs
                      (blockSpec row1776)
                      (blockSpec row1780)))))))
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1784)
                    (blockSpec row1788))
                  (joinBlockSpecs
                    (blockSpec row1792)
                    (joinBlockSpecs
                      (blockSpec row1796)
                      (blockSpec row1800))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1804)
                    (blockSpec row1808))
                  (joinBlockSpecs
                    (blockSpec row1812)
                    (joinBlockSpecs
                      (blockSpec row1816)
                      (blockSpec row1820)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1824)
                    (blockSpec row1828))
                  (joinBlockSpecs
                    (blockSpec row1832)
                    (joinBlockSpecs
                      (blockSpec row1836)
                      (blockSpec row1840))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1844)
                    (blockSpec row1848))
                  (joinBlockSpecs
                    (blockSpec row1852)
                    (joinBlockSpecs
                      (blockSpec row1856)
                      (blockSpec row1860))))))
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1864)
                    (blockSpec row1868))
                  (joinBlockSpecs
                    (blockSpec row1872)
                    (joinBlockSpecs
                      (blockSpec row1876)
                      (blockSpec row1880))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1884)
                    (blockSpec row1888))
                  (joinBlockSpecs
                    (blockSpec row1892)
                    (joinBlockSpecs
                      (blockSpec row1896)
                      (blockSpec row1900)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1904)
                    (blockSpec row1908))
                  (joinBlockSpecs
                    (blockSpec row1912)
                    (joinBlockSpecs
                      (blockSpec row1916)
                      (blockSpec row1920))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1924)
                    (joinBlockSpecs
                      (blockSpec row1928)
                      (blockSpec row1932)))
                  (joinBlockSpecs
                    (blockSpec row1936)
                    (joinBlockSpecs
                      (blockSpec row1940)
                      (blockSpec row1944)))))))))
      (joinBlockSpecs
        (joinBlockSpecs
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1948)
                    (blockSpec row1952))
                  (joinBlockSpecs
                    (blockSpec row1956)
                    (joinBlockSpecs
                      (blockSpec row1960)
                      (blockSpec row1964))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1968)
                    (blockSpec row1972))
                  (joinBlockSpecs
                    (blockSpec row1976)
                    (joinBlockSpecs
                      (blockSpec row1980)
                      (blockSpec row1984)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1988)
                    (blockSpec row1992))
                  (joinBlockSpecs
                    (blockSpec row1996)
                    (joinBlockSpecs
                      (blockSpec row2000)
                      (blockSpec row2004))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2008)
                    (blockSpec row2012))
                  (joinBlockSpecs
                    (blockSpec row2016)
                    (joinBlockSpecs
                      (blockSpec row2020)
                      (blockSpec row2024))))))
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2028)
                    (blockSpec row2032))
                  (joinBlockSpecs
                    (blockSpec row2036)
                    (joinBlockSpecs
                      (blockSpec row2040)
                      (blockSpec row2044))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2048)
                    (blockSpec row2052))
                  (joinBlockSpecs
                    (blockSpec row2056)
                    (joinBlockSpecs
                      (blockSpec row2060)
                      (blockSpec row2064)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2068)
                    (blockSpec row2072))
                  (joinBlockSpecs
                    (blockSpec row2076)
                    (joinBlockSpecs
                      (blockSpec row2080)
                      (blockSpec row2084))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2088)
                    (blockSpec row2092))
                  (joinBlockSpecs
                    (blockSpec row2096)
                    (joinBlockSpecs
                      (blockSpec row2100)
                      (blockSpec row2104)))))))
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2108)
                    (blockSpec row2112))
                  (joinBlockSpecs
                    (blockSpec row2116)
                    (joinBlockSpecs
                      (blockSpec row2120)
                      (blockSpec row2124))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2128)
                    (blockSpec row2132))
                  (joinBlockSpecs
                    (blockSpec row2136)
                    (joinBlockSpecs
                      (blockSpec row2140)
                      (blockSpec row2144)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2148)
                    (blockSpec row2152))
                  (joinBlockSpecs
                    (blockSpec row2156)
                    (joinBlockSpecs
                      (blockSpec row2160)
                      (blockSpec row2164))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2168)
                    (blockSpec row2172))
                  (joinBlockSpecs
                    (blockSpec row2176)
                    (joinBlockSpecs
                      (blockSpec row2180)
                      (blockSpec row2184))))))
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2188)
                    (blockSpec row2192))
                  (joinBlockSpecs
                    (blockSpec row2196)
                    (joinBlockSpecs
                      (blockSpec row2200)
                      (blockSpec row2204))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2208)
                    (blockSpec row2212))
                  (joinBlockSpecs
                    (blockSpec row2216)
                    (joinBlockSpecs
                      (blockSpec row2220)
                      (blockSpec row2224)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2228)
                    (blockSpec row2232))
                  (joinBlockSpecs
                    (blockSpec row2236)
                    (joinBlockSpecs
                      (blockSpec row2240)
                      (blockSpec row2244))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2248)
                    (joinBlockSpecs
                      (blockSpec row2252)
                      (blockSpec row2256)))
                  (joinBlockSpecs
                    (blockSpec row2260)
                    (joinBlockSpecs
                      (blockSpec row2264)
                      (blockSpec row2268))))))))
        (joinBlockSpecs
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2272)
                    (blockSpec row2276))
                  (joinBlockSpecs
                    (blockSpec row2280)
                    (joinBlockSpecs
                      (blockSpec row2284)
                      (blockSpec row2288))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2292)
                    (blockSpec row2296))
                  (joinBlockSpecs
                    (blockSpec row2300)
                    (joinBlockSpecs
                      (blockSpec row2304)
                      (blockSpec row2308)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2312)
                    (blockSpec row2316))
                  (joinBlockSpecs
                    (blockSpec row2320)
                    (joinBlockSpecs
                      (blockSpec row2324)
                      (blockSpec row2328))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2332)
                    (blockSpec row2336))
                  (joinBlockSpecs
                    (blockSpec row2340)
                    (joinBlockSpecs
                      (blockSpec row2344)
                      (blockSpec row2348))))))
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2352)
                    (blockSpec row2356))
                  (joinBlockSpecs
                    (blockSpec row2360)
                    (joinBlockSpecs
                      (blockSpec row2364)
                      (blockSpec row2368))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2372)
                    (blockSpec row2376))
                  (joinBlockSpecs
                    (blockSpec row2380)
                    (joinBlockSpecs
                      (blockSpec row2384)
                      (blockSpec row2388)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2392)
                    (blockSpec row2396))
                  (joinBlockSpecs
                    (blockSpec row2400)
                    (joinBlockSpecs
                      (blockSpec row2404)
                      (blockSpec row2408))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2412)
                    (joinBlockSpecs
                      (blockSpec row2416)
                      (blockSpec row2420)))
                  (joinBlockSpecs
                    (blockSpec row2424)
                    (joinBlockSpecs
                      (blockSpec row2428)
                      (blockSpec row2432)))))))
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2436)
                    (blockSpec row2440))
                  (joinBlockSpecs
                    (blockSpec row2444)
                    (joinBlockSpecs
                      (blockSpec row2448)
                      (blockSpec row2452))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2456)
                    (blockSpec row2460))
                  (joinBlockSpecs
                    (blockSpec row2464)
                    (joinBlockSpecs
                      (blockSpec row2468)
                      (blockSpec row2472)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2476)
                    (blockSpec row2480))
                  (joinBlockSpecs
                    (blockSpec row2484)
                    (joinBlockSpecs
                      (blockSpec row2488)
                      (blockSpec row2492))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2496)
                    (blockSpec row2500))
                  (joinBlockSpecs
                    (blockSpec row2504)
                    (joinBlockSpecs
                      (blockSpec row2508)
                      (blockSpec row2512))))))
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2516)
                    (blockSpec row2520))
                  (joinBlockSpecs
                    (blockSpec row2524)
                    (joinBlockSpecs
                      (blockSpec row2528)
                      (blockSpec row2532))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2536)
                    (blockSpec row2540))
                  (joinBlockSpecs
                    (blockSpec row2544)
                    (joinBlockSpecs
                      (blockSpec row2548)
                      (blockSpec row2552)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2556)
                    (blockSpec row2560))
                  (joinBlockSpecs
                    (blockSpec row2564)
                    (joinBlockSpecs
                      (blockSpec row2568)
                      (blockSpec row2572))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2576)
                    (joinBlockSpecs
                      (blockSpec row2580)
                      (blockSpec row2584)))
                  (joinBlockSpecs
                    (blockSpec row2588)
                    (joinBlockSpecs
                      (blockSpec row2592)
                      (blockSpec row2596))))))))))
theorem cert_lower (hknown : KnownBin cert_bounds) : LowerBin cert_mask cert_stock cert_goal 13 :=
  lowerDagRefF (profile := cert_profile) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hknown cert_sub cert_goals
    (symDagRef_sound (by decide +kernel) cert_syms cert_trace cert_links)
    cert_roots cert_nodes

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
theorem r0_b0 : treeBlockF 0 16 r0_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r0_b16 : treeBlockF 16 32 r0_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r0_b32 : treeBlockF 32 48 r0_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r0_b48 : treeBlockF 48 64 r0_check = true := by decide +kernel
theorem r0_nodes : ∀ i, 0 ≤ i → i < 64 → r0_check i = true :=
  joinBlockSpecs
    (joinBlockSpecs
      (blockSpec r0_b0)
      (blockSpec r0_b16))
    (joinBlockSpecs
      (blockSpec r0_b32)
      (blockSpec r0_b48))
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
def r9_forest : Nat → Nat × Nat := unpackForestF 0x6849140169f8fa5fc7d2ee751b33a2d99d160ce8366741831f4af8f95fcd93666c5531f2b798c6ccc5366621b3310c18f957cb8ae65c1432d4c98f953c7c2fe525b3290a98f85bc92366489b3242d992160c7c2be42543210b990164c7c29802d1f1d8bd8db55c6da280293ef06bf7835dc4e366265b3132c18986cc4c305e0d5f118bd7834dc39ae61c9b2f068f85b4ec2d2f5e0d16f02bf83a6cc1caa5e056f028d98136cc0836604182f02af7f95cbfc285fc992f02a77805fbe8b65f4152f00b77ac6cbd5b65ea5b2f52c178057bc8a85e4172f12c97805300523ddad52ed4a94ec5fbaeb653b16ee96ad4ec5ab89b65c49b2e22d971160b88365c41829d8af6945eb49af5a497ad22bd6db5cb6d2e5a454ad80b96c050b482f5a6d72d34b96995cb4ca85a414a9d8ad6835cb2ab2594d72ca27165134b281c5940d29d8a763349b19a0d8c97a9d6ad60349b01a0d8097ac048d60244a752b57a122bd0894e94faec2456a972b52895a934ad40c56c532b50294e94bac9ae5649729d28f5814cabd2a53a50eac29156144a7427d54522a42b952044a901a5480b2a509952024a7425d42d72a14b94e847a7c2653c5529d08600a37a6d2ed26d16996bb49a45a522c529152946a94a254a4d1b80253e878af43b57a3cae50ed1e8c6ad4624da1ca3510d2a8868d44256a1c9b00252e8548b39b5da0dae4e6d1e8168b39a5d9fd2e4e691e7c8d93e4609cd1bcf08de7826f3c1279cc2e4e8d1e7448f3a2379cc2800251e712b92bb479b926cdc8d65728d33a3f99d1bcce0fe670773383799c19cae5126369531b4698d234ae4da5c4772e23797017cb80ae5c04f2e02395c9a4b48de570312c23795c0a00250e552a92335f94a364a45b2466af27a5d93c2848c95a4d4bb2315691dad48ed5a474ad2405091cab48c4d801277222358c22d48454a306ad1f4588f9b247cd52304bf1dc608edaa46095e358ad1ab5a8d5ab46cd52354bd1824d8c5ab4629363124d1815a0049bc5c5521b8bf15b6c8acb643715e286bb1405086d2b44b16a256ad0da46889aec444da1b2ad0e45a8722b438d5a1d0a10e15686ca30024ae186b10c2548062fc2cd82018af0a246805ad42117a104b508256805a5414d360a68b0634c8291d41454a014ad0334a8192b40c51a012b50135a8092b40455a01294009277fd2ebdad15fd6baf6a457e22c3f1151f86a8fc2547b51bbec551ed276f9c587cdaa3da4ddf12a8f692b7b9ac3dc951ed24e0084f75e2bbaed5de90b8ebb4775d2dbae95de5048eba4b78c2e3ae91de1048eba3b77c263ae8dddc6acee24d75c233b0d29d868cec25675c1b00212dd548adcb5d74dae372d1dd168adca5d73d2e37291dcc8d8e64606e51bb9091dc828ee41276e4ae388d1dc448ee22376e4a837252db928ee016c6e49db7d181b926ede16c6e495b74d81b924e008476dc2e31ad1db5048c6a4b6cc2e31a91db1048c6a3b6bc2631a8ddaa49ad52356a89cb544d58d08cd0a3f6851bb424fda1276d093768499b424ada124ec684466da5336d199b48ccd92966c92b1a0d992476c92376489db244dd9225ec912b64893b2448d8d068c82376341631c8dd8d0480084362c2a2d8d7d888d8c406c5b1abb0c1516c4bec20245b12db041b16c4aebf2545f9222fc0916c4a6bda545ec122d88ed79098b62375d92eaec5416c2acba25d5b02b2dad696d6acb6a565b494adc1416d0acb60360041dad48d5458b4b4052515ab2c9161646c8b23545152fac3181616a8a2a5756e2b2b6d695b6acae35456d2f28a935588b0ac354514afaac571452b6aa460514abaa057150288a8134514a9a9c57145256a5350529a42949714524ea335651926a8c099450b40083750c2a24117d406d8a006c4822ba7c151204be9e0244812da741b1204ae9b2544d92226c091204a699a444cc1224092d310b8902474b9aea5c541202ac95c5a4adab240519286ba940364802b243169218ac90b564849ca44141210ac9004600415a3ad611d4a87ac5f46db01eb15d1948c7ab5a4562f22a969154ac7ab4a43da6a1ed151169887a3a43c291ea9590c6b0862543d4afa14530f52b6843603d4aba0855104298821343d4a9a04530f52967f3503f9a41fc970f528e7d34a3e92b1f4118f50b47b35a3d92b1ec158f5094008273ccaa18d17cf12d8634573bcaa18cd7ced2d8633573acae18cd1cc64ac73b5d39d2e98c558e18b470c56385ab1c2934e12ac63146369ad1b4d58da6946d3463692b1b4558c626c6a846354221aa0d8d50686305234cae19c958d10b8671563389b19c0d8c60946615c31d2b194170c72ac6394631c2318c0e80103e6205425e2f9841b0978ae6005425daf97c1b0976ae5e05c25da396e918b74885ba362dd1a12e948b546c4ba4a2cd2312e8e8b10b85713a2bc2e15c4a8972ac53b5d29d2e954570a72745415c29c9512e158a08b450456281ab140934a02545005625c23130d68986ac4c34a261a3130958982944c05625c1b00206c954b03ac5f24d300eb15c914b03ab5f23d300ead5c8d4a03ab47228a31144d8754b44315a218ab10c4d8754944095a204ab1025288128c3aa3a1f5250fa8e87d2583a95a1d9250ec8e8792583b15a1dc250ec0b0750b4008171cc2a00517c710d8014571bc2a004d7c6d0d8013571ac2e004d1c6768a33a4519c22004978646ac3224d009230c2d28614ac0123615da28ae9145d4882b93616ca20ae4985804c2c01615c220045784e6ac2724d149220a41104e2bc27a3813ca609c4980228c22b4a1152b092510490882295e1191c08c5304528c0113610c22068d3c412a01a3470fc2206893c3d2a01a2470ec260688dc3924c1a13a0dc0a06a4e83526c1a12a0089202cd741669a0b3450592e82c9341648a15b500ad2202c4d8284a0141440589304ad40254880b036089280445101604c0ba3d07c2002e8d41727a0e04005c9a82e108170800b82a05c0d02c050020ac06c5a04d2e01b1580d6ac06a4d0351a81a4980d04c0104600dad014d70036ac01b4a00da30069580348c0194600c230040d8010260001f 10 11
def r9_links : Nat → Nat → Option Nat := unpackLinksF 0xb224b0eab083afc6afc0afc0afa1afa0af81aea7ae81ae61ae60ae03ae00ae00ae00ade1ad26ad20ad20ace2aca2ac81ac61ac60ac03ac00ac00ac00abe1ab26ab20ab20aae2aaa2a6fea6e0a683a604a4caa463a3a6a3a0a3a0a381a380a361a287a280a223a220a220a1a4a1a0a1a0a0c7a0a1a081a080a023a020a020a020a0019f469f409f409f029ec29ea19e819e809e239e209e209e209e019d469d409d409d029cc2991e990099009884986197e497e097a297a097a097a097a097a097a096a896a09662962295e295e095e09564956095609522952095209520952094a493a893a0938193809380938093809380928892809280928091e591e091e091e091e091e091459121912090c390a19043904090409040902190018f658f608f608f038f008ee18ec18ea18ea08e438e218dc38dc08dc08dc08da18d818ce58ce08ce08c838c808c618c4188dc88c088258820878587808780878087808704860885c28582858085428540854084c484c084c084c08444828e82808204820081a381a08124812080c380c080c080448040804080407fe37fe07fe07fe07f457d507d407c867c807c807bc67bc07bc07bc07bc07bc07bc07aa97aa07aa07aa079e679e079e079e079e079e079e078c978c078a178a07881770c770076e176e076e076457640762175c375c0756375607560756075607541748672ed72e07283728071a771a07181718071047100710070a3708170807080708070616f876f806f806f806f236d6e6d606d416d406d406ca56ca06c816c236c206c206bc36bc06bc06b636b606b606b606b606b416a8668ed68e068e0686468606803680067a367816780678066a7668166806680666166606587658065806580652365206520652064c3630e63006265626061c561c061c061c061c06144614061216120610160a360a060816080606160035f085ec25e825e805e425e215e205e205e015e005de15de05dc15dc05da15da05da05d245d205d205d205ca45aee5ae05a645a605a035a005984598059235920592058a458a058a058a0584358405840584057a557a057a057a057625760574157405702570056e154f054e05426542053c353c0536353605303530052a352a052a052a052a051e651e051e051e051e051e051e051e051e050c950c050c050c050c050c05006500050005000500050005000500050004ee94ee04ec14ec04ea14d2c4d204d014d004d004c654c604c414c404c214c204be24be04be04be04b834b804b804b234b204b014b004ae14a834a804a234a204a204a204a204a204a01494647ad47a047434740466746604641464045c445c045c045634541454045404540452144474440442143c343c043a143a04381438043804380432343204301430042e142c1424442404240424041e3402e40204001400040003f653f603f413f403f213f203ee23ee03ee03ee03e833e803e803e233e203e013e003de13d833d803d803d233d203d203cc33cc03cc03cc03cc03cc03ca13be63a4d3a403a4039c439c039633960390338e138e038e0380737e137e037e037c137c036e736e036c13663366036413640362136203620362035c335c035a135a03581356134e434e034e034e034833480348034803423326e32603241324031e331e031c131c03163316031223085308030802fc62fc02fc02fc02fc02fc02ee72ee02ee02ee02ee02ee02ee02e072e002e002e002e002d652d602d412d402d212d202d202ca42ca02c812c802c612c602c602be42a6c2a602a412a4029e329e029c129c0296329602922292029202920292028852880280428002784278027612760274126a526a026a026a026812680266125a625a025a025a025a025a025a024c724c024c024c024c024c024c024c023e7226c22602222220121a321a02162214120e320e02083208020802004200020001fe11f071f001f001ee11ec11de71de01de01dc11d441d401d401d401d021d001ce11c641b0b1ae11a831a8019a7198119231920184718211785176117411702166516411621156615411521146614411421142013e213e013a213a013a0136212c512a112811280128012421240124012021146112111011100110010c210c010c010820fc60fc00f820f610f220f200ee20ec10e820e610e220e200dc30dc00da10da00d430c480c400c210bc30bc00ba10b430b400b400b020b000b000ac20ac00ac00a820a800a800a420a400a400a210a200a200a010a000a000a000a000908076d0760076007410740074007400740074006480640064006210620062006200620062006200528034f00390001 0x174b45bb51b4304951d04b88255d0922c5a4ae1724ea102b470139e407cc30364a0171c809dbc9930b48963234b792b5d29570e48d732368b094a820a6db4b96aa5ccfa3661edb2de4b99e96ccf0b06761b33a0c19b968cbcaa66e9b3362a946944cb8a86691b2836d999a6ccb4a86641b3310c19795ccb82865a9924248995068c842a6545b3290a8ee844c882864f1b1d36d99326cc94b6648583200a191150c842e64059168289a025fcfd2ee7295ed14ab8e24dc3523e14916c546b9c15fcd4ade6055f2c2a74894ba08a3c824d62a2570a927cac2fe5016f230af8f8537ac25ba411d6706a9f82b468139e007cc1036490171c009e3b17a3f26ab2835ba52addc8d63e26ab2035c71aae36d16542771e9376281dac60dcee03e5f81b2400b8dc04edf6c986354b091a61ed5adf68d74b45b9d1aca64e5890736e35cb59ae62f1b2df6b98726cc58b662a583140d989860c462f41c4951304b74d64c3dae61c9b2c14698634ec2d2f5808d23b26b069255841aa24097082d180154c213660e552882697f950c1636608db27f4d97f150c0c36604183002b97f850bf9324148d2fb0d179054becb65f4151d806979850be2365eedb1cf4d97b16cbd4b05e2142f32a17905cbc4b221e4d3196bf8c35dc49abda2d571069b86b47c29a2d7e8db092bf8315bc04abdfa54e902973f1479449dc744de0924b7e05fbe42dde815ef00a6f504b73823b0e0ed6006e870253b00f97a06c8e02e36013bae345d3152ee6a976a54b41aa5d75b2e0ac964464b11325d2d5ae06ab70458b3e285cedb2e64d97296cb90b05c61b2e20c16e150b58285b6542d50a16c85cb50285b8d72db4b96c05cb4c285b2172d80a16b35cb552e5a8572d32a17045eb3a2edbed7ade4bd6e95eb68a95ae17ad20a56835cb3eb258f192ce6b961a64b349c5984d2cb07165034b21a4d8ed06c64bd60a46b0122588d26c36836125eb0523580912bb2915d158af82457a1103702958144aec2456c050370715b14cae92e572512b82695b818ad40a566d72b24b957940ac0a655e952aa09156948ab0a25521603702955148a7c2254a050370715284caa4ae550112a70695302ca9012544d72a14b94f040a7c2653c552ec8bf7545bba22d5c315ed18ad64c53b15ab57e95a932bf4715b9ecabce054ebc29f5a14bac4a3d5c50df70bef405b72c2bb6c14eab09f5184ba8023d3a10cea03e5d81b2300b8d404e9b4bb4b255a551aab00d4690234cb5da59aad288d90c04a34011a5e2c52d152956a94a254a69a2d309169346ec283b55c1ba7a0ad0b04e330118cd2251a5120746944134a3cae5125528d6ad4624da2522c0c49a8a69544b46a212b46251a918af48357a39a3c6091a0546d45946a1c9b3ce16dc20aec184b55423a760ed0906e3e025a0dab4fa9368548b1492aa0dae4f4172760a13eb4da05a2cfe95a502753fa5c9e42e4ea1427d8d93e4609e0364e81827a46f3c9379e093cecd1e7548f3a23793c9d4504aa846bb41347a012ecfc91e7b46f2713a89c954ee172730a0f304b70423b020ed5306e9c82b41c139d2076712b9321549b8a24c64d25a0312c0149bd26cc89166e46ac00395441a9740666c47f35a379a81fcd20ee6806f338334e015a0c09cb903332b4a991a34c691937052820252e00ccc28ee6046ebf83b5401bcbe0be5e0572e8279701196e0665a46f2c2379c1a3cda51a662893113696c9a2fa12d4f08e9a83b40c1b96c0a6590312b814954aa4a71b2034692916c928b24924d24824d2825d91c9349e1424d4bb25255808934901424b6b5253569252b48e559340525a819951afca2d5e4e4ad00a36930ab48c4d9f50bef205b6fc2bb6814d32076808372d014c708f64446b1312a8fd26c769163947b211528cca544a4a8650231b23c9022c47ed923e6a91aa4c8e2344791823b6a91b24c8d9aa47315a386b51bb568d52f464568fe04a320118cdab4649363124d21c5a905ab47a97e3a4af1a24d8c0ad4484a9f20bef105b6f42bb6414d300567e82718c08c5c5522c6d912a448acb643e5921e2890e9368a5aec384da280a11345a895ab44455a236bb0fb558889b43a142208b50fc56879ab4385597c072598198b62fc5515e274ad12246884ab436519f00bef005b6ec2bb6014d7a096a68472c814c32d6212691072648612a422da2166c106a548452542891a042950635484a2f416d5a114b508256820ad2961146202306238831a641cd360d68b05a3a828a940e52a0327430811821a540e95a0628d0235a80d2b40455a178bf0ac5784dad41ed2a094ad0295a804a53da17dde0b6dc8576b829af012d4908e300117fd2ebf4955f946af993517c093fad75fa6aafc2367b8928bc049fb8b0fd4547e5aa3f0951f62a82e8107d22c3e6d505c020f895416c083ded61ee4a82d0107f9a2bf8915f746efa93b7c89bbe04aded24e2b012520a23ba110fb268ec0347a42e3b215078268f282478c2e3c2091df098eeb5677126bb2914fa04ced34a765a33b09594608cf5c577a9abbd0d1de74b6f325779125bc491de0476ef237514a31f24d87524ced84675c1b3a6d59cd49aeaa454bc153a6d71ca2b8e3150735a6ba2d15cf4acbb83a73d2e392571c52a0e6c6c732303905b1c42c0e5247724a3b9049dc668ee2a477111baec0e92e054e016c2c01437d181bc2d8570286e9b03a8d75d268ee825d73923b968ddc72b8e1950708a5b8251dbf276de9376ec95b7249d750749682a2b40d36e1719e0a8d60446741a3200b18e048d585465c2236a091b30b8d50446581a3441519c088d88246842a35e1319b068d6a4d67922b588d5ab272d51353600f3508fda746ed313f6949db484dda3266d112b684939ae0799f694cf346675233384a59b24a6b01e6651db308dd97276cb13765497b284ad9324ec91233540f3208dd8e46edb3476d125b6491db0476d723735097352119a0088cd0366441a31e0b18d048c5854626361ee4d1880d8b88645c01a30c151840486912c608363009517f488bf0245f12a2de1117b048bc84c5b8132ee975762a0b68265d12eae2954f604cb70505c9ad2e2d59704acb79295b42b19c0798a6bec3b576152fb0696d814aebea535e91daf08dd752ac7a936334972e61596c06caf23d5a91aa580a96549ab0a4557d1ead0149480949582a154092b88f1668b0b2b64591aa2b69315e8d0b1460585aa2b89315c6a8afc56579ad2bad595b4bca512551c2d0a804853020acc58561aa0a2041562b8aa460548ae2a251150268a715c1400809e0414c6a0a5b485292e09c041486aca3a4d518132d3169676acb1a5f5812bab4935572beaa95b54caba9e54d4d256a49275142d2540a84d024a1854505b6256511400d8928644902227c1513c0486592c4e836270951374889b0244d122246151330489885c4881b25ed752e2a0908364b22d256d59280ac94b5d495aaa500d9220a09345a4962b248d59232729085631c0f28517d3f8ae9ea5f4ed2da7295d354a69924b4c123a5a5592a28c6312e49c2b2401191e6b08bb4844d3223a951166d08db604492a22c9291948c7c04a445aa22f179106ac8b25a4552b1fe514fc0b4260124451c222d311369a893454411d21e148fb0947b83a12c090940410d6b08625412008214531086c083154414a62084d1022982381011808200d40ff6907f25c114081f8d28fb4ac7d0463e1ad1ee958f60ac8e45f46a2ba30d69146948725642cafa1256d072ae81953404a59fa51cf90b47a84a110091e6550f12d87216438ca21de550ed2d86f16436c9a1d6570dc2a83395c3849b1b4498d20746582a3a1ae9c8d54e74ba6f2553401d1920a8e58b47245638dab1c4934dc48a70956320151bed68de6ac6eb4a371a31b6958da2ac6784a360231ae110d606c6a8341d80a1a6570d10b869256340ab19e4d8ce06c6615c3282e196958c92ac6414631c231e517cf08ae7735f3b1ab9d4d1ce94ac73156380a31b24d8d40a46684a3181d188150c20d85206428c22180150be0d84e8642681a1781709b0a85d2462e5221708d8b74683e8242d51b160558a90ac4c8362cd2315c558a70ac508462c42e15e170b02745712a15c2e1400d89804c5515c2a0ae158d74a46aa55a5d2752a9524e8a725452c5a2922b146d58a249a4da45284951401589e6b44eb56271a5136d189a4ac4c94a2602b18717cc18ae5fb5f2f5ab976d1cb64a45a24a2c91d15a558a60ac4f84625c1b12a9604202020820221341269804002048a580f80807a080844d047a600f0081049608d4a01d010220a511651884274451360e4080fe968882b4439562089d10c4d87b0b41c0200d81006a0407e4b44215a20cab1045288128c3d05a0d0100f21287f4943f23a1f4960f0168792583b82c1dc250f69287a4743c15a1d81612917c928ae4835f239ab918d1c894b442a4a2011d0f8568750b41981010c0a084490310c839854195220aa510402483886c04832060150110881f8140f89205c1906f0a830a3412c9a0784906d0d8048640b42a00c0d03b0281d1241ac2e00e1500f0880283414c9a0944905204c248161a5a28d09145126c2412619c220561104624832b56191268b85784524c15056010130a0510280883134a1852b0b45784e28c13856038230ba4d05b2482ea44164220b6510580882c8261600b0bed145e48a2e136168930ae110250882792414d220a4110504702794c155ab0a8934512bc271260902b0060984728811044128a2092110474702314c131a5096958482bc229460842b01a118200a82184407c220825401e0880e8540fc220381103d2a00d8440dc1c06c5203b0981b12a0e493030118370281b13a0d49b02e1184269e203470f92787891c3a46e1c13a0d09502c11820028159340941a03c0501d02814124088120360502c6a015a440a528050510266a012a4408d280445101f0800e0400811e83c8d41d27a0d93506821032100180540b81a0c9ae824d543169a183450bd2e8129542e49a16a450a89b04e4982406c108260580a026970148b409456045ab0209340748a07a350389301a0980a6b805b5a025ab010d280768c03256015230085180308c3945f1c22b8dcd7c6c6ae353471992f0c69186046c2b15e134a30884d8332480a856030230040db4169f8f347c6927dde91e9c46f4914fa18a5ce451e562872293b8bc9bc344ae0024ef604f75825b7011d8c086b583b5101ba3e0acf404e6281f2580d8e805c010260001f 16 5 11 10 6
def r9_trace := dagTraceF r9_mask r9_stock 8 r9_forest
def r9_check : Nat → Bool := dagCheckNodeF r9_mask r9_goal r9_bounds 835 r9_trace r9_links
set_option maxHeartbeats 0 in
theorem r9_roots : dagCheckRootsF r9_mask r9_goal r9_bounds
    (dagRefF 835 r9_trace r9_links 0) r9_stock 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b0 : treeBlockF 0 16 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b16 : treeBlockF 16 32 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b32 : treeBlockF 32 48 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b48 : treeBlockF 48 64 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b64 : treeBlockF 64 80 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b80 : treeBlockF 80 96 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b96 : treeBlockF 96 112 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b112 : treeBlockF 112 128 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b128 : treeBlockF 128 144 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b144 : treeBlockF 144 160 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b160 : treeBlockF 160 176 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b176 : treeBlockF 176 192 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b192 : treeBlockF 192 208 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b208 : treeBlockF 208 224 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b224 : treeBlockF 224 240 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b240 : treeBlockF 240 256 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b256 : treeBlockF 256 272 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b272 : treeBlockF 272 288 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b288 : treeBlockF 288 304 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b304 : treeBlockF 304 320 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b320 : treeBlockF 320 336 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b336 : treeBlockF 336 352 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b352 : treeBlockF 352 368 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b368 : treeBlockF 368 384 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b384 : treeBlockF 384 400 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b400 : treeBlockF 400 416 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b416 : treeBlockF 416 432 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b432 : treeBlockF 432 448 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b448 : treeBlockF 448 464 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b464 : treeBlockF 464 480 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b480 : treeBlockF 480 496 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b496 : treeBlockF 496 512 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b512 : treeBlockF 512 528 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b528 : treeBlockF 528 544 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b544 : treeBlockF 544 560 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b560 : treeBlockF 560 576 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b576 : treeBlockF 576 592 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b592 : treeBlockF 592 608 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b608 : treeBlockF 608 624 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b624 : treeBlockF 624 640 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b640 : treeBlockF 640 656 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b656 : treeBlockF 656 672 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b672 : treeBlockF 672 688 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b688 : treeBlockF 688 704 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b704 : treeBlockF 704 720 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b720 : treeBlockF 720 736 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b736 : treeBlockF 736 752 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b752 : treeBlockF 752 768 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b768 : treeBlockF 768 784 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b784 : treeBlockF 784 800 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b800 : treeBlockF 800 816 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b816 : treeBlockF 816 832 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b832 : treeBlockF 832 835 r9_check = true := by decide +kernel
theorem r9_nodes : ∀ i, 0 ≤ i → i < 835 → r9_check i = true :=
  joinBlockSpecs
    (joinBlockSpecs
      (joinBlockSpecs
        (joinBlockSpecs
          (joinBlockSpecs
            (blockSpec r9_b0)
            (joinBlockSpecs
              (blockSpec r9_b16)
              (blockSpec r9_b32)))
          (joinBlockSpecs
            (blockSpec r9_b48)
            (joinBlockSpecs
              (blockSpec r9_b64)
              (blockSpec r9_b80))))
        (joinBlockSpecs
          (joinBlockSpecs
            (blockSpec r9_b96)
            (joinBlockSpecs
              (blockSpec r9_b112)
              (blockSpec r9_b128)))
          (joinBlockSpecs
            (joinBlockSpecs
              (blockSpec r9_b144)
              (blockSpec r9_b160))
            (joinBlockSpecs
              (blockSpec r9_b176)
              (blockSpec r9_b192)))))
      (joinBlockSpecs
        (joinBlockSpecs
          (joinBlockSpecs
            (blockSpec r9_b208)
            (joinBlockSpecs
              (blockSpec r9_b224)
              (blockSpec r9_b240)))
          (joinBlockSpecs
            (blockSpec r9_b256)
            (joinBlockSpecs
              (blockSpec r9_b272)
              (blockSpec r9_b288))))
        (joinBlockSpecs
          (joinBlockSpecs
            (blockSpec r9_b304)
            (joinBlockSpecs
              (blockSpec r9_b320)
              (blockSpec r9_b336)))
          (joinBlockSpecs
            (joinBlockSpecs
              (blockSpec r9_b352)
              (blockSpec r9_b368))
            (joinBlockSpecs
              (blockSpec r9_b384)
              (blockSpec r9_b400))))))
    (joinBlockSpecs
      (joinBlockSpecs
        (joinBlockSpecs
          (joinBlockSpecs
            (blockSpec r9_b416)
            (joinBlockSpecs
              (blockSpec r9_b432)
              (blockSpec r9_b448)))
          (joinBlockSpecs
            (blockSpec r9_b464)
            (joinBlockSpecs
              (blockSpec r9_b480)
              (blockSpec r9_b496))))
        (joinBlockSpecs
          (joinBlockSpecs
            (blockSpec r9_b512)
            (joinBlockSpecs
              (blockSpec r9_b528)
              (blockSpec r9_b544)))
          (joinBlockSpecs
            (joinBlockSpecs
              (blockSpec r9_b560)
              (blockSpec r9_b576))
            (joinBlockSpecs
              (blockSpec r9_b592)
              (blockSpec r9_b608)))))
      (joinBlockSpecs
        (joinBlockSpecs
          (joinBlockSpecs
            (blockSpec r9_b624)
            (joinBlockSpecs
              (blockSpec r9_b640)
              (blockSpec r9_b656)))
          (joinBlockSpecs
            (joinBlockSpecs
              (blockSpec r9_b672)
              (blockSpec r9_b688))
            (joinBlockSpecs
              (blockSpec r9_b704)
              (blockSpec r9_b720))))
        (joinBlockSpecs
          (joinBlockSpecs
            (blockSpec r9_b736)
            (joinBlockSpecs
              (blockSpec r9_b752)
              (blockSpec r9_b768)))
          (joinBlockSpecs
            (joinBlockSpecs
              (blockSpec r9_b784)
              (blockSpec r9_b800))
            (joinBlockSpecs
              (blockSpec r9_b816)
              (blockSpec r9_b832))))))
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
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r9_known r9_sub r9_goals r9_roots r9_nodes

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
def r13_forest : Nat → Nat × Nat := unpackForestF 0xa7139a7135a7039a70350063fa4f4ea4f4da4e46a4e3ea4d29a4d25a4c29a4c250063ba223ea2239a214da3418a3414a2141a204da242ca2424a204100637a1a4c96346a124c96345a063ea063d963449624e9624d9623e9f3449623d9eb449612a96129961289db44961269d344961259ba3d9ba3a9ba369ba359ba34961249a7449a5289aa349a5249602a960299602898744992349841898a34984149602697f44960259663d9663a96636966359663496024006339464d94645946399463594439944350053f9224e9224d921469213e921369212e92019920150053b8de4d91028910248de418de3d904248fa308fc148f9408de358dd3e8dd398dc4d8e03c8e0348dc41005378d54c81e468cd4c81e458c13e8c13d81e4481d4e81d4d81d3e8ae4481d3d81d3c8a14481d3689a4481d358853d88536885358853481d3481d2e876448753481d2d862448613c865348613481c1a81c1981c188424484d348403c845348403481c1683a4481c158213d8213a82136821358213481c14005337eb4a7eb467ea4e7ea4a7ea467f7447f4287fa347f4247ea427e8297e8250052f7a64a7a6467a63e7a63d7a54e7a54a7a5467ba447b8187bd347b8147a5427a5367a52e7a4197a4150052b7274e7274a7904c79040727467842878424727427264a76a407742476a3076c1476940726467254a7424075814742307501474140745307452074134725467252e725297243d7284c72844724310052771d3c632367153c632357092e7092d632346314e6fe346314d6314c6e2346e1446e0186e5246e0146314a6d924631466d234631456c1266c1256c124631446a94c6a93c6a92c6a8186a814631426313e69d446313d6312e68a3468d24689446312d676346754c67924675446301a630196301865634661246544c65924654446301664e34630156352d6352a635266352563524630140052360e4d60e4560e3960e3560d4d60d4560d3960d350043f5e94e5e94d5e8465e83e5e8365e82e5e8265e81e0043b58e4d5d9285d92458e4158e3d5cd245c2305c4145c04058e3558d4d5b13c5b13458d4158d3d5a5245993059c245984058d3558c3e58c39004375844c4cd4657c4c4cd455703e5703d4cd444cc4e4cc4d4cc3e55d444cc3d4cc3c550444cc36549444cc355343d5343653435534344cc344cc2e51d4451c3c5203451c344cc2d4cc2c510444cc264f944504344f83c4fc344f8344cc254e43d4e4364e4354e4344cc244cc1e4d1444d0344d0244cc1d004334934a493464924e4924a492464a7444a5284aa344a524492424913d4913549129491250042f44d4a44d4644d3e44d3d44c4e44c4a44c46461444602c464344602444c4244c3644c2e44c2644c1e0042b3b74e3b74a4394c439403b74642d2842d243b7423b64a4124041d244123041414410403b6463b53d4014c401443b5313b52d3f5343e9203ec343e8303b5253b44a3c2403d8143c2303d0143c1403c5303c5203c1343b4463b42e3b429004273ac3c2c1363a43c2c1353982e3982d2c1342c04e38d342c04d2c04c37134370443702c37424370242c04a368242c046361342c0453502635025350242c0443384c3383c3382c338243381c2c0422c03e32c442c03d2c02e315343144c31824314442c02d2c02c308342c0262f1342fc242f04c2f4242f0442c0252dc2d2dc262dc252dc242c0242c01e2c5342cc242c4442c4242c01d0042326e4a26e4626e3a26e3626d4e26d4a26d46292442913c295342913426d4226d3e26d3a26d36272342714c275242714426d320041f2094a209462093a209362092e2092d2084e2084a20846235442343c2383423434208422083e2083a20836215342144c218242144420832208262081e0041b1364e1364a1f64c1f640136461e93c1e934136421363e1363a1d7481d740136361c94c1c944136321354a1ad401b9241ad301b0241ac40135461353a1913019d34191201943419030135361344a169401802416930178241684016c3016c2016834134461343a1413015834141201503414030144201441014024134361341e134190041712c2c009261242c009251181e1181d009240084e10d240084d0084c0f1240f0440f03c0f4140f0340084a0e814008460e124008450d0160d0150d014008440b84c0b83c0b8340b82c0b81c008420083e0a1240a04c0a4140a0440083d0083c085240844c08c1408444084340083a07c140083606524070140644c0681406444008350541605415054140083403c4c03c4403c3c03c2c03c1c008320082e02c4402c340082d0081e00d2401c1400c440141400c3400c140081d004130000f 10 10
def r13_links : Nat → Nat → Option Nat := unpackLinksF 0xb841b840b821b820b5b4b581b561b541b4a5b481b480b461b460b1f4b1a2b162b160b160b122b066b060b060b022af66ac59ac40abe3abe0ab83ab80ab80aa0caa00a984a980a942a8c4a882a804a800a800a7c2a706a700a6e1a6c1a6a1a6a0a6a0a6a0a605a5c2a5c0a5c0a5a1a524a520a520a4e2a4e0a4c1a4c0a4a1a3e6a3e0a3c1a3a1a381a380a380a380a2e59fd99fa19f819f619f609f419f409cd49ca19c819c619c419c409ba59b819b8099149900990098c2980697e197e097a297a0976296e496a2966296609660962295669259924091e391e0918391809180900c90008f848f808f428ec48ec08ec08ea18e628da68d818d808d808d808ce58ce08ca28c818c048bc28bc08bc08ba18b248b208b208ae28ae08ac18ac08aa189e689e089c189a1898189808980898088e585d985a18581856185608560852285208520850184848461846081f481c181a18181816181418140814081028100810080e1806480417fa57f817f807d147d007d007d007d007cc27cc07c827bc67ba17b817b807b427b407b027a847a617a417a407a027a0079c279c079c0796378e478a2786278607860782277667459744073e373e0738373807380720c720071c271447140710270e170e070e070c17044704070216fe26f266f206f206f206e856e806e806e806e806e806de56de06dc16d446d406d026d006ce16c646c226c206c206c016b846b806b806b426b406b216b206b016a466a406a216a0169e169e069e069e069456639660165e165c165c065a165816561656062f462c162a16281626162606241624061a55f345f205f205ee25e265e015e005dc25dc05d825d045d005d005cc25c065be15be05ba25ba05b625ae45aa25a625759574056e356e0568356805680550c550054845480544253c453c053c053a1536252a6528152805280528051e551e051a251a051a0518151045100510050e150a250a05081508050614fa64f814f804f804f804ee54ee04ea24e814e614de44ad94aa14a814a614a604a604a224a204a204a014984496149414921492046b4468146614641462146014600460045c245c045c045a14524450144e144e0444541d441c041c041c041c04182418041424086406140414040400240003fc23f443f403f403f023e463e213e203de23de03da23d243d013ce13ce03ca23ca03c623c603c603c033b843b423b0237f937e03783378037233720372035ac35a0356234e434e034a2348134803480346133e433e033c1338232c632c032c032c032253220322032203220322031853180316130e430e030a230a030a030813004300030002fe12fa22fa02f812f802f612ea62e812e802e802e802de52de02da22da02d812d612ce429d929a129812961294129212920292028e228e028e028c1284428212820282027e227e027e027c1274424d424a12481246124412421240123e123e023e023a223a023a02381230422e122e022e022a222a022a02281220421e121451ed41ec01ec01ec01ec01e821e801e421d861d801d801d801d801d421d401d021c461c211c011c001bc21bc01b821b041ae11ac11ac01a821a801a4219c419a1198119801942194019021900190018a31824180117e117e017a217a0176217601760170316841642160212f912e01283128012231220122010ac10a010620fe40fe00fa20f810f800f800f610ee40ee00ec10e820dc60dc00dc00dc00d250d200d200d200d200d200c850c800c420c400c400c210ba40ba00b620b600b600b410b210aa40aa00a810a420a400a210a200a01094609400940094008a508a008a008a008a008a00805080007e107c1074407400702070006e106e006c106c00644033900380001 0x6b94c3484ca5f4e9fb4da6a4aa6649a46469fa41a4636a62359594d9094579d3da7d39a79357b5316284d5d0454443da7439a703545c31a1a34a12449f2309f3446b12875d24338283dc246b53c3443ca6b4ea674da43459ef42a6246a4245a5e3e9ee3d8153d77d358092da5929a55256dd214c43d424354b82da5029a4c2536c2100e4c9f23c00e4c9f23c8fd3476d248fa4476a346ed4477934a3818a34145c434414245c1444113437c4442034a282ca2424a434e9f74da464e9fe4da463ea4239a1632a0e31a0230a3d4d7cd4978d45a31419553d8f5358112d76525a2c4d4744943445a20416243d5bc354c02d40c25a1a4c9c12496c24a124c9bd2496824a0a3ea063d8012d9e92a9d9269d1259b9244b02d9b02a9942697c25964249f34400e449c92497424745243c4249f34400e349c5249702474524990249eb4475d249ac2898c249a818988149db449c94c9c53c6b12c9a418984149d34474634746349ca3d9c63a9c2369be359ba349a9243c4249aa349b3449ad289a5243dc2499018988149923498a34997449754c9713c3392c98c189841497f443c6343c6349763d9723a96e3696a35966349fb4d9ef4aa1746a0f45a03449fe4e9fa4d9f63e9ee3d7f12d9e52a9e1299dd289d5269cd259b5246a5214a02d9a02a99c2999828980269782596024334216bb44802306ba4c0c84c92b4e8b74d95a4d9564579e3d9523994e357f23193d4a939498f1468b5418f136935356184d5a8452003d9483994435230318d5348cd44879306b12887a446b53c779340b818184140bc2c93e4e93a4d8ee45872427e23a76236935468ed459313e7cd3a92d366dd329292e8712d2b82d1c0252a41d92419920150ec119063475024903446ee4474d3475d2491428910247c5307452490424749248fc146ef40902308f9407412400e4c87a3c00d4c8792c59c341b014599441ad240fc448e43c8e0341bc248ef4e87f4d91a4d80a4978e4590e4190a3d8f6358f14e8b94d8f13e8ed398d1328c9318bd307dd2a73d268e84d248491f0458dc416143d594352b41d1a8158d54c88d24828148cd4c88934824148c53e8c13d8ad2d7c52a8a126899258852429c1d86c1a85016838158201487a4400d4489134830147492484c148ae447793486818848148a144864188441489a448914c6b53c8752c8601884014749348913d8753a88d3688935885347492416c147493487a448753400d2482c148652416c148653486e448693c861341841484c2c8442484d3484534852448304c8483c8403482c2c0b81c83a4416d3416d348313d82d3a8293682535821348b64d8724a8d2468ca458be448b94e8b54d8b13e8a93d8a53c7b53a89d3689535881346a53287d2e8712d28c1d85c1a858198541883c168341581c140b4116b634802306b638745247f8247fa348034475d247fc287f4240443c8174a8134680e4e80a4a806467f2427ae3e69a3d7d93a7d5397393669931739267b12549c3d3f8351e02d7ec297e825210216b1247c53071d24715346b138749247bc147bd347c644779347c0187b81469120692346b94c6ed4403c1815c140402c7e24a7de467da3e7d63d73635686327d14e7cd4a7c9467b5427b136735357ad2e6852d2b02d1a4252841d7a8197a415080117944c7904077634758347734477a347554475d2478828784246f12074934745247742468d3476c1477a407723076940741346f12074634749247581468d347501468e30749307452075e407563074d407413400d3c6912c00d3c6912c3ec24194143e9341912472c4c72844084341a02479f4e79b4a78f467834277e4a766467363e6963d7614a73d467393e6a13d7392e735297192271121705207303d228391d035724314982d3e4252ac1d18c156c94471d3c63c146c5447153c638146fd3d6f13a6d9366d1356c13470d2e7092d27c1d6801a6641664c156341468d34660146fe346ed4467c1865c1468d346e41468d246e5246f2346ed446e8186e0146d92467818658146d2346b94c69d3c6892c674186541469d2d6892a6c9266c5256c1246b94c6b53c6b12c6ac186a81468d246923469d4400d346441468d341441468d24692346894400d24640146793414414679246823467d4c6754415c146603c6583466124659246663465c4c654446443c6402c03c1c64e3414524145246452d6412a63d26639256352469a3d6863a71a3671235706347014e6f94d6f54c6dd4a6d5466cd456bd446a5426a13e6993d6952e6852d26c1d6701a66c19668186501664815630140381134b444b23034a4c0cb4429d300c94c5eb4e5674d62a4d626454463d6223961e354a2316194d615452013d6113960d3528d316044a600495904656441590365fc355843457c444d830338280b8184d9443443c420340bc2c1bc246054e6014d58d454cd424893a3e1362652a189265fc4658c455f83e4743a5f43636c325f02e2482a5ec260ec225e81e4cc1d5ce343d0245cb4437e445dd285d9243cc343dc2446c305cd243c4243c8245c41437f405ca305c0403c0245a534178145a2440fd445b53c5b1341742418414240305a52416c1459c24170140ff405a130598401681400e4c4da3c00c4c4d81c58f4e4df4d5e24d4ba49436455d6415d23d5be355b94d2a5491f1455ad415a93d595355904e5684d5903e58c39580325783156c304842a3bc262601a164165844c53c244ec1457c4c538344e8245743e5703d55c2d46c2a5502654825534245281d2401a51016508154e4144d94400c44540344f0243c8245041455d44420345242c50024550445201c4fc14549445404c3443c51c2c4f8244d41c3c8345403d4d43a53c365383553434520241701452034529445243c51c341bc24510445042c4fc24504344fc34509444f04c5003c4f8340bc2c4d01c170344f03d4d03a4ec364e8354e4343c824170143c834170344d9444d4344d02400c145654d4cd4a581465794556d445684e5644d5603e5583d5543c45c3a54c3654435530343343252c2e5182d5142c2302a50c264f4254e0240b4224dc1e4cc1d346344b230346384a9243c4244aa344b3444ad284a5243dc240463427d200453c4c74a4c3464be4e4ba4a4b6464a24244e3e32a3d49d3d499351e12d495294912526d214803a47c393b836328313b826458253381446c303ac243a434338383c824464144643446d44420344682c460242d02003c182d1343484c37c440402c1a0244894a485464813e47d3d3b5352c13225d2a161264784e4744a4704645c42458363b4354542e2282a450260802244c1e2c01d43d4c4394041e343d83441b44422344312842d243d4443dc24380203c83441d243c4242cc34414144224041a30410403c0343f524150143f2344054c401440853414c2415c14220203f534144143ec3414814086303f1203e83014014380203c6343c9243d8142cd343d0142ce303c9303c5203de403d6303cd403c13400d3c2d12c00c3c2d01c4474e4434a4374642b424264a40e463b63e2d63d4093d285391d1353fd313f92d3e5253e04a3bc463b83e3303d3b82e3b4293a8223a021394202581a13c16358443ac3c2e414354443a43c2e02438c3d3803a36836360353503439c2e3982d3201d2201a30816300152dc142cc342fc1438d3437c4431c2c2f8242cc34374142cc24374243813437c443782c37024368243181c2f414361343484c32c3c3142c2f0242c81c32c2d2c82a3582635425350243484c3443c3402c33c243381c2cc242d13432c4400c342e8243183414814318243213431c4c314441a024308342fc3c2f4342fc242f424301342f84c2f0442e83c0402c2c41c148242e82d2c42a2e4262e0252dc242cc34148142cc24148242d1342c8442c42400c143293d2c13a3a9363a135395343904e3884d3844c36c4a3644635c4534c44334423303e3283d3242e3102d30c2c2102a304262ec252d824038222d41e2c01d0bd2429d300412427d200bd382952416c142953429e442993c29134184140412827534144142752427e342794c2714415c142ba4a2b6462b23a2ae362a94e2a54a2a14628d422893e2853a2813626d322092e0292d2542a2502913826028211381620c150b8142403003c142202012c14124240b8382382417014238342414423c3c234341bc2403c282183414814218242213421c4c214441a02402010021240c84c0fc440443c084342654a2614625d3a259362552e2512d135250092224c4e2484a244462304222c3e2283a224362103220c26134252081e0081d1fa4c1f6401b934180341b6441ed3c1e9341bd2417c44184141db481d74019d241582419a341cd4c1c9441a1241543415c1410010170341b92416c1401c341b0241bd401b5301ac4016834094101482419d341441419434014241a1301992019030140241001016d34180241701401c341782401e301703016c201854017d30174401683409410145241583414814150340142401520148201441015d301552014c301402400c2c0201c00c2c0201c2024e1fe4a1f2461e6421e23e1de3a1d2361c6321c14a1a9461a53a18d361352e0252d1884a164461603a13c361382e0342d1381e134191281212011114100d84405c3412c2c0d444058341242c10c3d1003a0e8360e0350d0340ac2d0942a07c26074250542411c1e1181d01c340702410d240fc440a83c06c3401c340f42401c140f414101240fc440f83c0f0340e8140a42c068240e1240c84c0a03c064340302c0181c0301d0181a0d8160d4150d0140c84c0c43c0c0340bc2c0b81c0a434014240a4140ad240a84c0a0440843408c340142408c1401414095240904c088440843407c140703c0683407014068140752406c4c064440443c02c2c0101c02c1d0101a05c16058150541404c4c048440443c0402c03c1c01c1401414021240304402c3400c2401c340142401c140141402124018440103400c140292d0092a1292612125115241104e1084d1044c0ec4a0e4460dc450cc440b4420b03e09c3d0983c0803a078360603505034038320342e0282d0241e0081da6e3fa4a3ba1e3795e339413f91d3b8d937819337e52f7a12b7212762d236083f5e43b588374c83348c2f4482b3b0272bc232681f2041b13017004130000f 16 5 10 10 6
def r13_trace := dagTraceF r13_mask r13_stock 6 r13_forest
def r13_check : Nat → Bool := dagCheckNodeF r13_mask r13_goal r13_bounds 672 r13_trace r13_links
set_option maxHeartbeats 0 in
theorem r13_roots : dagCheckRootsF r13_mask r13_goal r13_bounds
    (dagRefF 672 r13_trace r13_links 0) r13_stock 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b0 : treeBlockF 0 16 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b16 : treeBlockF 16 32 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b32 : treeBlockF 32 48 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b48 : treeBlockF 48 64 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b64 : treeBlockF 64 80 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b80 : treeBlockF 80 96 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b96 : treeBlockF 96 112 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b112 : treeBlockF 112 128 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b128 : treeBlockF 128 144 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b144 : treeBlockF 144 160 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b160 : treeBlockF 160 176 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b176 : treeBlockF 176 192 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b192 : treeBlockF 192 208 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b208 : treeBlockF 208 224 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b224 : treeBlockF 224 240 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b240 : treeBlockF 240 256 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b256 : treeBlockF 256 272 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b272 : treeBlockF 272 288 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b288 : treeBlockF 288 304 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b304 : treeBlockF 304 320 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b320 : treeBlockF 320 336 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b336 : treeBlockF 336 352 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b352 : treeBlockF 352 368 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b368 : treeBlockF 368 384 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b384 : treeBlockF 384 400 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b400 : treeBlockF 400 416 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b416 : treeBlockF 416 432 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b432 : treeBlockF 432 448 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b448 : treeBlockF 448 464 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b464 : treeBlockF 464 480 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b480 : treeBlockF 480 496 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b496 : treeBlockF 496 512 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b512 : treeBlockF 512 528 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b528 : treeBlockF 528 544 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b544 : treeBlockF 544 560 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b560 : treeBlockF 560 576 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b576 : treeBlockF 576 592 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b592 : treeBlockF 592 608 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b608 : treeBlockF 608 624 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b624 : treeBlockF 624 640 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b640 : treeBlockF 640 656 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b656 : treeBlockF 656 672 r13_check = true := by decide +kernel
theorem r13_nodes : ∀ i, 0 ≤ i → i < 672 → r13_check i = true :=
  joinBlockSpecs
    (joinBlockSpecs
      (joinBlockSpecs
        (joinBlockSpecs
          (joinBlockSpecs
            (blockSpec r13_b0)
            (blockSpec r13_b16))
          (joinBlockSpecs
            (blockSpec r13_b32)
            (joinBlockSpecs
              (blockSpec r13_b48)
              (blockSpec r13_b64))))
        (joinBlockSpecs
          (joinBlockSpecs
            (blockSpec r13_b80)
            (blockSpec r13_b96))
          (joinBlockSpecs
            (blockSpec r13_b112)
            (joinBlockSpecs
              (blockSpec r13_b128)
              (blockSpec r13_b144)))))
      (joinBlockSpecs
        (joinBlockSpecs
          (joinBlockSpecs
            (blockSpec r13_b160)
            (blockSpec r13_b176))
          (joinBlockSpecs
            (blockSpec r13_b192)
            (joinBlockSpecs
              (blockSpec r13_b208)
              (blockSpec r13_b224))))
        (joinBlockSpecs
          (joinBlockSpecs
            (blockSpec r13_b240)
            (joinBlockSpecs
              (blockSpec r13_b256)
              (blockSpec r13_b272)))
          (joinBlockSpecs
            (blockSpec r13_b288)
            (joinBlockSpecs
              (blockSpec r13_b304)
              (blockSpec r13_b320))))))
    (joinBlockSpecs
      (joinBlockSpecs
        (joinBlockSpecs
          (joinBlockSpecs
            (blockSpec r13_b336)
            (blockSpec r13_b352))
          (joinBlockSpecs
            (blockSpec r13_b368)
            (joinBlockSpecs
              (blockSpec r13_b384)
              (blockSpec r13_b400))))
        (joinBlockSpecs
          (joinBlockSpecs
            (blockSpec r13_b416)
            (blockSpec r13_b432))
          (joinBlockSpecs
            (blockSpec r13_b448)
            (joinBlockSpecs
              (blockSpec r13_b464)
              (blockSpec r13_b480)))))
      (joinBlockSpecs
        (joinBlockSpecs
          (joinBlockSpecs
            (blockSpec r13_b496)
            (blockSpec r13_b512))
          (joinBlockSpecs
            (blockSpec r13_b528)
            (joinBlockSpecs
              (blockSpec r13_b544)
              (blockSpec r13_b560))))
        (joinBlockSpecs
          (joinBlockSpecs
            (blockSpec r13_b576)
            (joinBlockSpecs
              (blockSpec r13_b592)
              (blockSpec r13_b608)))
          (joinBlockSpecs
            (blockSpec r13_b624)
            (joinBlockSpecs
              (blockSpec r13_b640)
              (blockSpec r13_b656))))))
theorem r13_known : KnownBin r13_bounds :=
  knownNil
theorem r13_lower : LowerBin r13_mask r13_stock r13_goal 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r13_known r13_sub r13_goals r13_roots r13_nodes

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
def r28_forest : Nat → Nat × Nat := unpackForestF 0xcf95dcf851c9247c9245cd25dcd245cd051c9147c9145ca355ca255ca036ca026c904bc904900b4fc796dc7861c1347c1345c535dc5345c5051c1147c1145c2455c2255c2046c2026c104bc104900a4fb8c5ebf135bf039b8c53b8c52bcd62bcc6ebc849b894fb894db9d62b9a5db986eb9826b8843b884100a37b726db7061aab47aab45b4b6db4b45b4861aaa47aaa45af45aaf459af458af456b135caf451af14eaf854af041aaa37acc55acb55ac846ac836aa84bab85cab347aa8490094f9bc5ea8a35a88399bc539bc52a4c5aa4c59a4c58a4c56a505ca48599ba5fa1562a136ea2b5ca1362a126ea10399ba4f9ba4d9ba359dd629db5d9d86e9d8369b8439c8549c35f9b841009379835a9835998358983569884c980598a45f8a35e96256960298a3538a3529256e924629226e9324c92262920298a34b8a34a90450900408a3468a2468e9348a1468c4628c45a8c06e8c0568a0338b0548ac5f8a0310092784d618885484a5d87d60849528485e8485d8485c85024848525e3477dd61830447db5d8205c7db45815607d9527d85e7d85d7f2357d85c7e0347d8525e247724617c0347245a7b05c724567a05c723567904c77a44781347785c7225676c60721427204e7204d73a4674134739467204c72854720425e2376fb5d6fb456fa5d6fa455e0476eb506e1275e0466945a6c25c6c05c69456693566924d6923569a44690565e03768350679475e0366035a65b5c6585c603566034a63c586384c603466025660246619446005660934600465e0275f2505eb475e0260084340c5e5c85c5a2555a05a5a0565a0555a05440b5f5906c56b555685a56856568555685440a5f55c585056e548545046e5383450462504595004e5004d5145e5004c5004240a374eb554ea554085f4db584d1274085e4c04c4ba37408524a85448c6e48c6248a4d4886e4083747b584715f408364605442b6e42b6242b4a4404c42b464286e428464082741a584135f408260083b3f85c3d2553d05a3d0563d0553d05421c5f21b5e3b86c394553905a39056390553905421a5f3805432d6e3704432d623645832b6e32b5e3285e3285d33a5e3285c3285221a4731455312552185f304582f9372185e2e85c2e247218522d0542ca5f2184a2b85429d6e29d6229a5d2986e2184728c582815f218462705423b6e23b6223b5a2505c23b562386e238562182722a582245f218260082b2085c1e3551e05a1e0561e0551e0540145f1d06c1ac551a85a1a8561a8551a8540135f1985415d6e1884415d6215a5e1585e1585d1585c1585201347144581404c13a370125e12455123550105f1145810a370105e0f85c0f347010520e0540db5f0104a0c8540ad6e0ad620ab5d0a86e0104709c580925f010460805407c5f0103a068540346e034620345a0485c034560306e03056010370235801c5f010360081b0001f 9 11
def r28_links : Nat → Nat → Option Nat := unpackLinksF 0xac02b00aa9aa91aa42a90aa42a36a886a20a882a20a8829c6a6c68eda3828e0a21a871a1c2870a1c2816a006800a002800a0027a69e466cd9ac66b09ac264798c663098c263096e25a196465909642590949e51190fa43090c23d68f063c08f023c08d9a3518d423508d063318cc23218c823208c4626b89822608982260881a20087c61e184761018402100825e081820208081c606181820517eadfa07e81fa07e45f907e41f187c05ee27b45ed07b41ed0799de607945e4175b9d607581d517505d4074c5c8b71c5c7071c1c076fc5bf06fc1bf06fc1be16f81b686d45b506d41b236c09af16b49ac16b01ac06b01a576941a4168c595e650594064c59306485920648190264018e25ffd7e15f817d15f057935e417815e017805dc57525d41732593d63158c1621588161158055d357415a35681591558d560554555055415415501531544951053c940f50013f14fc13e14da13604d453414d013404d013224c453104c053004bc527849c12614945250494125048c923048c1230484920147c51f047851e04745158454114144c507c4185060414504141010404100fb93ec0fa13e44f903e40f903c24f003b88ee03b44ed03b04ec03b00ec03b00eb13a84dfb37c0df03658d903604d7135c0d613544d503504d403500d403398ce03344cc13300cb132c0cb032c0ca13280ca03118c4030c4c212d74b502d04b312cc0b302cc0aa92a44a902a04a7129c0a7029c09e927809d127409c127009a226809a026809a02644981236c8d0234087621c08612144850210483120c08212044810200480020008001e987a01e447811e007711dc07701dc07611d807601c187001bc46e1187461018045f117c05f017c056915805511504540150054012e44b012844a01244490124049012044710f2c3c00f003a20e443900e403360cc03210c443100c042f10bc02e10b442d00b042c00b002c0099826009442410900231088422008442100840210080420008001a6068019106040bd0068001 0xd015d99155cd9453e859cf851cb8492001bce25d99255cda451f859cd051cb0493f02bcbb55cb2553e83aca8361f82aca02698237c024dcf247cea45a994dcc947cc14597927c984bc90494b0415d0393c82b1d81bc816da5965c59455b869c7861c38491c81bc635da5b55c5b451c059c5051c30495c03bc3c55c32555b84ac28461c02ac2026a4a47c034dc7347c6b459714dc4947c4145a4137c184bc10492d8415983b3c0291a01b1901bbd95db093dbf93589061bb051bf039848311801bbdd62bd46eb0c62b016eba851bc84915841178198805387960bb562baa5d87162ba06e848621582ab9826af25fc045ebec53be452ae95fbc14fbb94d8f9459f9358f125840532c049b9043b88411501bb7a6db1a65b524558069b7061ae0493b02bb5b6db1b65b53453a869b4861ad8495883b14819b146cb135caf854b345ab2c59b2458b1c56b0c51b014eab0590f0512c849af04113819ae455adb555804aad0463a83aac836ab85cab347a9b4db6b47b63459724db4247b3a45aea37ac04baa8490e8415603b3882b130193782ba3a5da223da9235838619f051a88397d8313682b36029a2c6ca505ca745aa6c59a6458a5c56a2451a1a4ea48592e0510d8499c04135829a2b5ca3d62a336ea2362a1a6e9e851a10393283135029828538e92481853811609f5629eb5d809629e06e7d8623283a9d8369c8549c35fa9c5ea8453a7c52a425fa0a4fa024d8fa459fa358e1267d0530d0499d0439b8413202b558499345c9884c9ab5a9a35999b589935692b5194b49980594b85155049078398a8315403b9445a92a5a96a567c8618d84196029720215304b9324c94d6e9446293a6e92a62528598d04192029500217b85390c507a853900408e93479853788438e93477053769608dc628d45a761628c86e720625005a8c0568b0548ac5f97c5f9735e95b539535291b4b9134a8fb468f2468e146718534f84b070398b8338a031879608885487d60821357a1256c05c85024895618825d7aa5581a4579a35871528685e8605d8585c6b85584852708456b0350f02a5e82681160830447912478a348205c7f04c81560781247f235779266585c7e03483d6182b5d7ab5581b4577236809528005e7f85d7e85c650557d8526f8452e03a6783662825769507c0347b05c7913478a447a05c7483c7904c7803c7402c7813478a447785c7383c76c60741347413474a4673946728546384c7cc617bc5a7ac5679b5677256761424b85a6e0567584e7504d7304c63045720426a0356202569834618247135d6bb5570b457025d652556fa4569036610266eb506e1276ca5c6c05c698446082469a446d45a6bc566b3566aa4d632456a235690566002668350679476635c6585c644586384c6184460834619446093466b5a6535664b4a6334662a566224661056600465f2505eb47843477d24771a374b04a6f0476d8462d83a68837670360e82a5f8275e026552375c85c4a8545425d5c2554a05d5b85a5b0565a8555a0540d82a410265906c460545435d58b554585d5805a5785657055568542c83a4703655c585104c54854538345145e4404c5556e5446e5346252c594d06e4b8625204e5184d5084c43845500424a35d4f35545a5d4ea5548836430264db584d1274c04c4ba374a8544a46e49c624924d43a454886e4282647b584715f460544404c45b6e4536244b4a43b464306e4284641a584135f5d45e59b5f5625f4fa374e05f4c85e4b0522c03a48037468360d02a42027408263f85c2b85437a5d3f2552b05d3e85a3e0563d8553d0540782a2202635a373b86c2705437c5d3b4552685d3a85a3a05639855390542c84a280463805437044364583384c33a5e2505c37d6e36d6235b6e3535e2f86e2e0623485e3405d3305c24855328522b45d31c5526a5d312552984624026304582f9372e85c2e2472d0542ca5f2b8542b56e2ad622a25d24a552986e2382628c582815f270542505c26b6e2636225b5a24b562406e2385622a582245f3cc5f3c35e38a5f322473085f2f05e2d8522c04a29047278460702a23027218262085c0c8541935d203550c05d1f85a1f0561e8551e0540783a018361d06c068541945d1cc550605d1c05a1b8561b0551a8540d84a0904619854188441415e0485c1956e1856213a6e17a5e1086e0f0621705e1685d1605c040551585214c581404c13a370c45d12c550635d123550a846038361145810a370f85c0f3470e0540db5f0c8540c56e0bd620b35d043550a86e0303609c580925f0805407c5f068540485c0646e05c620545a044560386e030560235801c5f1dc5f1a35f153471325e1185f1005e0e8520d04a0a047088460703a0283701036c8b4fc0a4fb8237aa14f9b137899275d8434003b2102b0081b0001f 14 4 11 9 5
def r28_trace := dagTraceF r28_mask r28_stock 9 r28_forest
def r28_check : Nat → Bool := dagCheckNodeF r28_mask r28_goal r28_bounds 417 r28_trace r28_links
set_option maxHeartbeats 0 in
theorem r28_roots : dagCheckRootsF r28_mask r28_goal r28_bounds
    (dagRefF 417 r28_trace r28_links 0) r28_stock 9 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b0 : treeBlockF 0 16 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b16 : treeBlockF 16 32 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b32 : treeBlockF 32 48 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b48 : treeBlockF 48 64 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b64 : treeBlockF 64 80 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b80 : treeBlockF 80 96 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b96 : treeBlockF 96 112 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b112 : treeBlockF 112 128 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b128 : treeBlockF 128 144 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b144 : treeBlockF 144 160 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b160 : treeBlockF 160 176 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b176 : treeBlockF 176 192 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b192 : treeBlockF 192 208 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b208 : treeBlockF 208 224 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b224 : treeBlockF 224 240 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b240 : treeBlockF 240 256 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b256 : treeBlockF 256 272 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b272 : treeBlockF 272 288 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b288 : treeBlockF 288 304 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b304 : treeBlockF 304 320 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b320 : treeBlockF 320 336 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b336 : treeBlockF 336 352 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b352 : treeBlockF 352 368 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b368 : treeBlockF 368 384 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b384 : treeBlockF 384 400 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b400 : treeBlockF 400 416 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b416 : treeBlockF 416 417 r28_check = true := by decide +kernel
theorem r28_nodes : ∀ i, 0 ≤ i → i < 417 → r28_check i = true :=
  joinBlockSpecs
    (joinBlockSpecs
      (joinBlockSpecs
        (joinBlockSpecs
          (blockSpec r28_b0)
          (joinBlockSpecs
            (blockSpec r28_b16)
            (blockSpec r28_b32)))
        (joinBlockSpecs
          (blockSpec r28_b48)
          (joinBlockSpecs
            (blockSpec r28_b64)
            (blockSpec r28_b80))))
      (joinBlockSpecs
        (joinBlockSpecs
          (blockSpec r28_b96)
          (joinBlockSpecs
            (blockSpec r28_b112)
            (blockSpec r28_b128)))
        (joinBlockSpecs
          (joinBlockSpecs
            (blockSpec r28_b144)
            (blockSpec r28_b160))
          (joinBlockSpecs
            (blockSpec r28_b176)
            (blockSpec r28_b192)))))
    (joinBlockSpecs
      (joinBlockSpecs
        (joinBlockSpecs
          (blockSpec r28_b208)
          (joinBlockSpecs
            (blockSpec r28_b224)
            (blockSpec r28_b240)))
        (joinBlockSpecs
          (joinBlockSpecs
            (blockSpec r28_b256)
            (blockSpec r28_b272))
          (joinBlockSpecs
            (blockSpec r28_b288)
            (blockSpec r28_b304))))
      (joinBlockSpecs
        (joinBlockSpecs
          (blockSpec r28_b320)
          (joinBlockSpecs
            (blockSpec r28_b336)
            (blockSpec r28_b352)))
        (joinBlockSpecs
          (joinBlockSpecs
            (blockSpec r28_b368)
            (blockSpec r28_b384))
          (joinBlockSpecs
            (blockSpec r28_b400)
            (blockSpec r28_b416)))))
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
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r28_known r28_sub r28_goals r28_roots r28_nodes

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
