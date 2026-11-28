import Mathlib.Data.Fintype.Pi
import PEqualNP.Defs.MetaComplexityLgpMono

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

theorem masked_zero (mask : Nat) : Masked mask 0 := by
  unfold Masked; simp

theorem masked_self (mask : Nat) : Masked mask mask := by
  unfold Masked; simp

theorem masked_land_right (mask w : Nat) : Masked mask (w &&& mask) := by
  unfold Masked; apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and]

theorem masked_xor {mask a b : Nat} (ha : Masked mask a) (hb : Masked mask b) :
    Masked mask (a ^^^ b) := by
  unfold Masked at ha hb ⊢
  apply Nat.eq_of_testBit_eq; intro i
  have ea := congrArg (fun x => x.testBit i) ha
  have eb := congrArg (fun x => x.testBit i) hb
  simp only [Nat.testBit_and, Nat.testBit_xor] at ea eb ⊢
  cases hm : mask.testBit i <;> simp_all

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

theorem canon_masked (mask w : Nat) : Masked mask (canon mask w) := by
  rcases canon_cases mask w with ⟨h0, _⟩ | ⟨_, h1 | h2⟩
  · rw [h0]; exact masked_zero mask
  · rw [h1]; exact masked_land_right mask w
  · rw [h2]; exact masked_xor (masked_self mask) (masked_land_right mask w)

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

theorem block_join {a m b : Nat} {f : Nat → Bool}
    (h1 : ∀ i, a ≤ i → i < m → f i = true)
    (h2 : ∀ i, m ≤ i → i < b → f i = true) :
    ∀ i, a ≤ i → i < b → f i = true := by
  intro i hi1 hi2
  by_cases h : i < m
  · exact h1 i hi1 h
  · exact h2 i (by omega) hi2

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

def unpack (data width idx : Nat) : Nat :=
  (data >>> (idx * width)) &&& ((1 <<< width) - 1)

def unpackForest (data pBits tBits : Nat) : Nat → Nat × Nat := fun i =>
  let w := pBits + tBits
  let code := unpack data w i
  (code >>> tBits, code &&& ((1 <<< tBits) - 1))

def unpackLinks (index data idxW sizeBits tokBits destBits steps : Nat) : Nat → Nat → Option Nat :=
  fun parent tok =>
    let entry := unpack index idxW parent
    let sz := entry &&& ((1 <<< sizeBits) - 1)
    let off := entry >>> sizeBits
    let w := tokBits + destBits
    (Nat.rec (motive := fun _ => Nat → Nat → Option Nat) (fun _ _ => none)
      (fun _ next lo hi =>
        if Nat.blt lo hi then
          let mid := (lo + hi) / 2
          let code := unpack data w mid
          let key := code &&& ((1 <<< tokBits) - 1)
          if Nat.beq tok key then some (code >>> tokBits)
          else if Nat.blt tok key then next lo mid else next (mid + 1) hi
        else none) steps) off (off + sz)

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

def cert_mask : Nat := 0xffffffffffffffff
def cert_stock : List Nat := [0xffffffff, 0xffff0000ffff, 0xff00ff00ff00ff, 0xf0f0f0f0f0f0f0f, 0x3333333333333333, 0x5555555555555555]
def cert_goal : Nat := 0x11717570157577f
def cert_bounds : List (Nat × List Nat × Nat × Nat) := [(0xcccccccccccccccc, [0xcccccccc, 0xcccc0000cccc, 0xcc00cc00cc00cc, 0xc0c0c0c0c0c0c0c, 0x4444444444444444], 9, 0x404440044444c), (0xf0f0f0f0f0f0f0f0, [0xf0f0f0f0, 0xf0f00000f0f0, 0xf000f000f000f0, 0x3030303030303030, 0x5050505050505050], 9, 0x10105000505070), (0xff00ff00ff00ff, [0xff00ff, 0xff000000ff, 0xf000f000f000f, 0x33003300330033, 0x55005500550055], 9, 0x1700570057007f), (0xffff0000ffff, [0xffff, 0xff000000ff, 0xf0f00000f0f, 0x333300003333, 0x555500005555], 9, 0x17570000577f), (0xffffffff, [0xffff, 0xff00ff, 0xf0f0f0f, 0x33333333, 0x55555555], 9, 0x157577f), (0xffffffff00000000, [0xffff00000000, 0xff00ff00000000, 0xf0f0f0f00000000, 0x3333333300000000, 0x5555555500000000], 9, 0x117175700000000), (0x5555555555555555, [0x55555555, 0x555500005555, 0x55005500550055, 0x505050505050505, 0x1111111111111111], 8, 0x115155501555555), (0xaaaaaaaaaaaaaaaa, [0xaaaaaaaa, 0xaaaa0000aaaa, 0xaa00aa00aa00aa, 0xa0a0a0a0a0a0a0a, 0x2222222222222222], 8, 0x202020002022a), (0x3333333333333333, [0x33333333, 0x333300003333, 0x33003300330033, 0x303030303030303, 0x1111111111111111], 8, 0x113131301131333), (0xf0f0f0f0f0f0f0f, [0xf0f0f0f, 0xf0f00000f0f, 0xf000f000f000f, 0x303030303030303, 0x505050505050505], 8, 0x10707070107070f), (0xff00ff00ff00ff00, [0xff00ff00, 0xff000000ff00, 0xf000f000f000f00, 0x3300330033003300, 0x5500550055005500], 8, 0x100170001005700), (0xffff0000ffff0000, [0xffff0000, 0xff000000ff0000, 0xf0f00000f0f0000, 0x3333000033330000, 0x5555000055550000], 8, 0x117000001570000), (0x5555555500000000, [0x555500000000, 0x55005500000000, 0x505050500000000, 0x1111111100000000], 7, 0x115155500000000), (0xaaaaaaaa, [0xaaaa, 0xaa00aa, 0xa0a0a0a, 0x22222222], 7, 0x2022a), (0x33333333, [0x3333, 0x330033, 0x3030303, 0x11111111], 7, 0x1131333), (0xff00ff0000000000, [0xff0000000000, 0xf000f0000000000, 0x3300330000000000, 0x5500550000000000], 7, 0x100170000000000), (0xcc00cc00cc00cc, [0xcc00cc, 0xcc000000cc, 0xc000c000c000c, 0x44004400440044], 6, 0x400440044004c), (0xcccc0000cccc, [0xcccc, 0xcc000000cc, 0xc0c00000c0c, 0x444400004444], 6, 0x4440000444c), (0xf000f000f000f0, [0xf000f0, 0xf0000000f0, 0x30003000300030, 0x50005000500050], 6, 0x10005000500070), (0xf0f00000f0f0, [0xf0f0, 0xf0000000f0, 0x303000003030, 0x505000005050], 6, 0x105000005070), (0x4444444444444444, [0x44444444, 0x444400004444, 0x44004400440044, 0x404040404040404], 5, 0x4044400444444), (0x2222222222222222, [0x22222222, 0x222200002222, 0x22002200220022, 0x202020202020202], 5, 0x2020200020222), (0x5050505050505050, [0x50505050, 0x505000005050, 0x50005000500050, 0x1010101010101010], 5, 0x10105000505050), (0x5500550055005500, [0x55005500, 0x550000005500, 0x500050005000500, 0x1100110011001100], 5, 0x100150001005500), (0xaa00aa00aa00aa, [0xaa00aa, 0xaa000000aa, 0xa000a000a000a, 0x22002200220022], 5, 0x200020002002a), (0xaaaa0000aaaa, [0xaaaa, 0xaa000000aa, 0xa0a00000a0a, 0x222200002222], 5, 0x2020000022a), (0xc0c0c0c0c0c0c0c0, [0xc0c0c0c0, 0xc0c00000c0c0, 0xc000c000c000c0, 0x4040404040404040], 5, 0x4000404040)]
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
def cert_forest : Nat → Nat × Nat := unpackForestF 0x317c18ae0b5f05ab82d1ed4d96457052dd49b298ae0a539a37cd19c14971d6f8eb3828ee12d8f45779adbcd2c12b6e16c662bb2d6d969609534e37a719d36d69b634da58252cdade6d6735b59ad8cd6b6093b2cb2055bc92f815671cb2051bc52f814670cb60515c1246003f 6 11
def cert_links : Nat → Nat → Option Nat := unpackLinksF 0x96720e29c237aaf41e0b93720e05a9b506a0c158030056aac150aa05409cd382614c098119a304608c1182303ca780f01e03c0780ca990302600b89702c2580a89502823d40f001 0x24476893b2891c68ed027641239d25ae52c6247324b58a58848ec4d74a6380b5b658c22476a6cb22baa56cf297526ca62ba856ce2973c6f9a33be5ada2c6694b92b7c759de2d6c9634cadc25b208aefb5b79a5b85b1b8aed35b65a5af1bd68ceab6b51b1a6d2d1ade85673db59cd8cd6b6596424be0e59052f8196c2ab79159c68de24670a2be517f18af835fbdabdcd1eb4b742539525c48edd2b6c15348a5984ec1246003f 11 4 11 6 5
def cert_trace := dagTraceF cert_mask cert_stock 11 cert_forest
def cert_check := dagCheckNodeF cert_mask cert_goal cert_bounds 51 cert_trace cert_links
set_option maxHeartbeats 0 in
theorem cert_roots : dagCheckRootsF cert_mask cert_goal cert_bounds
    (dagRefF 51 cert_trace cert_links 0) cert_stock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem cert_b0 : treeBlockF 0 2 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem cert_b2 : treeBlockF 2 4 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem cert_b4 : treeBlockF 4 6 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem cert_b6 : treeBlockF 6 8 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem cert_b8 : treeBlockF 8 10 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem cert_b10 : treeBlockF 10 12 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem cert_b12 : treeBlockF 12 14 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem cert_b14 : treeBlockF 14 16 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem cert_b16 : treeBlockF 16 18 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem cert_b18 : treeBlockF 18 20 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem cert_b20 : treeBlockF 20 22 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem cert_b22 : treeBlockF 22 24 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem cert_b24 : treeBlockF 24 26 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem cert_b26 : treeBlockF 26 28 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem cert_b28 : treeBlockF 28 30 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem cert_b30 : treeBlockF 30 32 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem cert_b32 : treeBlockF 32 34 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem cert_b34 : treeBlockF 34 36 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem cert_b36 : treeBlockF 36 38 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem cert_b38 : treeBlockF 38 40 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem cert_b40 : treeBlockF 40 42 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem cert_b42 : treeBlockF 42 44 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem cert_b44 : treeBlockF 44 46 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem cert_b46 : treeBlockF 46 48 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem cert_b48 : treeBlockF 48 50 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem cert_b50 : treeBlockF 50 51 cert_check = true := by decide +kernel
theorem cert_nodes : ∀ i, 0 ≤ i → i < 51 → cert_check i = true :=
  joinBlockSpecs
    (joinBlockSpecs
      (joinBlockSpecs
        (joinBlockSpecs
          (blockSpec cert_b0)
          (joinBlockSpecs
            (blockSpec cert_b2)
            (blockSpec cert_b4)))
        (joinBlockSpecs
          (blockSpec cert_b6)
          (joinBlockSpecs
            (blockSpec cert_b8)
            (blockSpec cert_b10))))
      (joinBlockSpecs
        (joinBlockSpecs
          (blockSpec cert_b12)
          (joinBlockSpecs
            (blockSpec cert_b14)
            (blockSpec cert_b16)))
        (joinBlockSpecs
          (joinBlockSpecs
            (blockSpec cert_b18)
            (blockSpec cert_b20))
          (joinBlockSpecs
            (blockSpec cert_b22)
            (blockSpec cert_b24)))))
    (joinBlockSpecs
      (joinBlockSpecs
        (joinBlockSpecs
          (blockSpec cert_b26)
          (joinBlockSpecs
            (blockSpec cert_b28)
            (blockSpec cert_b30)))
        (joinBlockSpecs
          (blockSpec cert_b32)
          (joinBlockSpecs
            (blockSpec cert_b34)
            (blockSpec cert_b36))))
      (joinBlockSpecs
        (joinBlockSpecs
          (blockSpec cert_b38)
          (joinBlockSpecs
            (blockSpec cert_b40)
            (blockSpec cert_b42)))
        (joinBlockSpecs
          (joinBlockSpecs
            (blockSpec cert_b44)
            (blockSpec cert_b46))
          (joinBlockSpecs
            (blockSpec cert_b48)
            (blockSpec cert_b50)))))
theorem cert_lower (hknown : KnownBin cert_bounds) : LowerBin cert_mask cert_stock cert_goal 12 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    hknown cert_sub cert_goals cert_roots cert_nodes

theorem knownNil : KnownBin [] := by
  intro b hb
  exact (List.not_mem_nil hb).elim

theorem knownCons {b : Nat × List Nat × Nat × Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hb : LowerBin b.1 b.2.1 b.2.2.2 b.2.2.1) (hs : KnownBin bounds) : KnownBin (b :: bounds) := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | hm
  · exact hb
  · exact hs a hm

section Relabel

variable {n r : Nat}

/-- New row `i` reads old row `p i`. -/
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

theorem lowerBin_rowPerm (p : Equiv.Perm (Fin n)) {mask goal k : Nat} {stock stock' : List Nat}
    (hm : mask < 2 ^ n) (hg : canon mask goal = goal)
    (stocked : ∀ w ∈ stock', Avail stock (rowCanon p.symm (rowPull p mask) w))
    (known : LowerBin mask stock goal k) :
    LowerBin (rowPull p mask) stock' (rowCanon p mask goal) k := by
  apply lowerBin_of_rowPull p.symm stocked
  rwa [rowCanon_inverse p hm, rowPull_inverse p mask, Nat.mod_eq_of_lt hm, hg]

theorem lowerBin_rowPerm_iff (p : Equiv.Perm (Fin n)) {mask goal k : Nat} {stock : List Nat}
    (hm : mask < 2 ^ n) (hg : canon mask goal = goal) (hs : ∀ w ∈ stock, canon mask w = w) :
    LowerBin (rowPull p mask) (stock.map (rowCanon p mask)) (rowCanon p mask goal) k ↔
      LowerBin mask stock goal k := by
  constructor
  · exact lowerBin_of_rowPull p (fun w hw => .inr (List.mem_map_of_mem hw))
  · intro h
    apply lowerBin_rowPerm p hm hg _ h
    intro w hw
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    rw [rowCanon_inverse p hm u, hs u hu]
    exact .inr hu

end Relabel

def decodeRows (code : Nat) (i : Fin 64) : Fin 64 :=
  ⟨Nat.mod (Nat.shiftRight code (Nat.mul i.val 6)) 64, Nat.mod_lt _ (by decide)⟩

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
def r0_check := dagCheckNodeF r0_mask r0_goal r0_bounds 64 r0_trace r0_links
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
def r2_check := dagCheckNodeF r2_mask r2_goal r2_bounds 7 r2_trace r2_links
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
def r4_check := dagCheckNodeF r4_mask r4_goal r4_bounds 10 r4_trace r4_links
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
def r6_check := dagCheckNodeF r6_mask r6_goal r6_bounds 11 r6_trace r6_links
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
def r9_check := dagCheckNodeF r9_mask r9_goal r9_bounds 835 r9_trace r9_links
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

def r10_mask : Nat := 0xcccccccccccccccc
def r10_stock : List Nat := [0xcccccccc, 0xcccc0000cccc, 0xcc00cc00cc00cc, 0xc0c0c0c0c0c0c0c, 0x4444444444444444]
def r10_goal : Nat := 0x404440044444c
def r10_rows : Fin 64 → Fin 64 := decodeRows 0x8328b49369b18738f59779f0000000000000000000000008a3aabcb3ebb9a7bafdb7fbf
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

def r11_mask : Nat := 0xf0f0f0f0f0f0f0f0
def r11_stock : List Nat := [0xf0f0f0f0, 0xf0f00000f0f0, 0xf000f000f000f0, 0x3030303030303030, 0x5050505050505050]
def r11_goal : Nat := 0x10105000505070
def r11_rows : Fin 64 → Fin 64 := decodeRows 0x10530d51571d18738f59779f000000000000000000000000925b2dd35f3d9a7bafdb7fbf
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
def r13_check := dagCheckNodeF r13_mask r13_goal r13_bounds 672 r13_trace r13_links
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

def r14_mask : Nat := 0xaaaaaaaa
def r14_stock : List Nat := [0xaaaa, 0xaa00aa, 0xa0a0a0a, 0x22222222]
def r14_goal : Nat := 0x2022a
def r14_rows : Fin 64 → Fin 64 := decodeRows 0x4314700000024b34f00000045355700000065b75f
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

def r15_mask : Nat := 0x33333333
def r15_stock : List Nat := [0x3333, 0x330033, 0x3030303, 0x11111111]
def r15_goal : Nat := 0x1131333
def r15_rows : Fin 64 → Fin 64 := decodeRows 0x8208208208208208208208208208208208208208208208208208275c65808208255445008208234c248082082144040
set_option maxHeartbeats 0 in
theorem r15_lower : LowerBin r15_mask r15_stock r15_goal 7 := by
  apply lowerBin_of_rowPull r15_rows (stock' := r13_stock)
  · have hall : r15_stock.all (fun w => availBF r13_stock
        (rowCanon r15_rows r15_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r15_rows r15_mask = r13_mask := by decide +kernel
    have hg : rowCanon r15_rows r15_mask r15_goal = r13_goal := by decide +kernel
    rw [hm, hg]
    exact r13_lower

def r16_mask : Nat := 0xff00ff
def r16_stock : List Nat := [0xff, 0xf000f, 0x330033, 0x550055]
def r16_goal : Nat := 0x57007f
def r16_rows : Fin 64 → Fin 64 := decodeRows 0x2082082082082082082082082082082082082082082082082082082082082082082082085d65544d24501c61440c2040
set_option maxHeartbeats 0 in
theorem r16_lower : LowerBin r16_mask r16_stock r16_goal 5 := by
  apply lowerBin_of_rowPull r16_rows (stock' := r4_stock)
  · have hall : r16_stock.all (fun w => availBF r4_stock
        (rowCanon r16_rows r16_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r16_rows r16_mask = r4_mask := by decide +kernel
    have hg : rowCanon r16_rows r16_mask r16_goal = r4_goal := by decide +kernel
    rw [hm, hg]
    exact r4_lower

def r17_mask : Nat := 0xffffffff
def r17_stock : List Nat := [0xffff, 0xff00ff, 0xf0f0f0f, 0x33333333, 0x55555555]
def r17_goal : Nat := 0x157577f
def r17_bounds : List (Nat × List Nat × Nat × Nat) := [(0xaaaaaaaa, [0xaaaa, 0xaa00aa, 0xa0a0a0a, 0x22222222], 7, 0x2022a), (0x33333333, [0x3333, 0x330033, 0x3030303, 0x11111111], 7, 0x1131333), (0xf0f0f0f, [0xf0f, 0xf000f, 0x3030303, 0x5050505], 7, 0x107070f), (0xff00ff, [0xff, 0xf000f, 0x330033, 0x550055], 5, 0x57007f), (0xff00ff00, [0xff00, 0xf000f00, 0x33003300, 0x55005500], 5, 0x1005700), (0xffff, [0xff, 0xf0f, 0x3333, 0x5555], 5, 0x577f)]
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
def r17_forest : Nat → Nat × Nat := unpackForestF 0x10fa1b42f4910981f 2 9
def r17_links : Nat → Nat → Option Nat := unpackLinksF 0x38e31c29301 0x410524a1f81b61721301f 6 3 9 3 4
def r17_trace := dagTraceF r17_mask r17_stock 8 r17_forest
def r17_check := dagCheckNodeF r17_mask r17_goal r17_bounds 6 r17_trace r17_links
set_option maxHeartbeats 0 in
theorem r17_roots : dagCheckRootsF r17_mask r17_goal r17_bounds
    (dagRefF 6 r17_trace r17_links 0) r17_stock 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r17_b0 : treeBlockF 0 6 r17_check = true := by decide +kernel
theorem r17_nodes : ∀ i, 0 ≤ i → i < 6 → r17_check i = true :=
  blockSpec r17_b0
theorem r17_known : KnownBin r17_bounds :=
  knownCons r14_lower (
  knownCons r15_lower (
  knownCons r13_lower (
  knownCons r16_lower (
  knownCons r2_lower (
  knownCons r4_lower (
  knownNil))))))
theorem r17_lower : LowerBin r17_mask r17_stock r17_goal 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r17_known r17_sub r17_goals r17_roots r17_nodes

def r18_mask : Nat := 0xffffffff00000000
def r18_stock : List Nat := [0xffff00000000, 0xff00ff00000000, 0xf0f0f0f00000000, 0x3333333300000000, 0x5555555500000000]
def r18_goal : Nat := 0x117175700000000
def r18_rows : Fin 64 → Fin 64 := decodeRows 0x821a29c31e398a3aabcb3ebb925b2dd35f3d9a7bafdb7fbf
set_option maxHeartbeats 0 in
theorem r18_lower : LowerBin r18_mask r18_stock r18_goal 9 := by
  apply lowerBin_of_rowPull r18_rows (stock' := r17_stock)
  · have hall : r18_stock.all (fun w => availBF r17_stock
        (rowCanon r18_rows r18_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r18_rows r18_mask = r17_mask := by decide +kernel
    have hg : rowCanon r18_rows r18_mask r18_goal = r17_goal := by decide +kernel
    rw [hm, hg]
    exact r17_lower

def r19_mask : Nat := 0x5555555500000000
def r19_stock : List Nat := [0x555500000000, 0x55005500000000, 0x505050500000000, 0x1111111100000000]
def r19_goal : Nat := 0x115155500000000
def r19_rows : Fin 64 → Fin 64 := decodeRows 0xfbceb8000000db4cb0000000bacaa80000009a48a0
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

def r20_mask : Nat := 0x5555555555555555
def r20_stock : List Nat := [0x55555555, 0x555500005555, 0x55005500550055, 0x505050505050505, 0x1111111111111111]
def r20_goal : Nat := 0x115155501555555
def r20_bounds : List (Nat × List Nat × Nat × Nat) := [(0x5555555500000000, [0x555500000000, 0x55005500000000, 0x505050500000000, 0x1111111100000000], 7, 0x115155500000000)]
theorem r20_sub : ∀ b ∈ r20_bounds, r20_mask &&& b.1 = b.1 := by
  have hall : r20_bounds.all (fun b => Nat.beq (Nat.land r20_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r20_goals : ∀ b ∈ r20_bounds, canon b.1 r20_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r20_bounds.all (fun b => Nat.beq (canonF b.1 r20_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r20_forest : Nat → Nat × Nat := fun _ => (0, 0)
def r20_links : Nat → Nat → Option Nat := fun _ _ => none
def r20_trace := dagTraceF r20_mask r20_stock 7 r20_forest
def r20_check := dagCheckNodeF r20_mask r20_goal r20_bounds 0 r20_trace r20_links
set_option maxHeartbeats 0 in
theorem r20_roots : dagCheckRootsF r20_mask r20_goal r20_bounds
    (dagRefF 0 r20_trace r20_links 0) r20_stock 7 = true := by decide +kernel
theorem r20_nodes : ∀ i, 0 ≤ i → i < 0 → r20_check i = true :=
  fun i _ hi => absurd hi (Nat.not_lt_zero i)
theorem r20_known : KnownBin r20_bounds :=
  knownCons r19_lower (
  knownNil)
theorem r20_lower : LowerBin r20_mask r20_stock r20_goal 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r20_known r20_sub r20_goals r20_roots r20_nodes

def r21_mask : Nat := 0xaaaaaaaaaaaaaaaa
def r21_stock : List Nat := [0xaaaaaaaa, 0xaaaa0000aaaa, 0xaa00aa00aa00aa, 0xa0a0a0a0a0a0a0a, 0x2222222222222222]
def r21_goal : Nat := 0x202020002022a
def r21_rows : Fin 64 → Fin 64 := decodeRows 0x100901101900300b01301b00500d01501d00700f01701f02102903103902302b03303b02502d03503d02702f03703f
set_option maxHeartbeats 0 in
theorem r21_lower : LowerBin r21_mask r21_stock r21_goal 8 := by
  apply lowerBin_of_rowPull r21_rows (stock' := r20_stock)
  · have hall : r21_stock.all (fun w => availBF r20_stock
        (rowCanon r21_rows r21_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r21_rows r21_mask = r20_mask := by decide +kernel
    have hg : rowCanon r21_rows r21_mask r21_goal = r20_goal := by decide +kernel
    rw [hm, hg]
    exact r20_lower

def r22_mask : Nat := 0xf0f0f0f0f0f0f0f
def r22_stock : List Nat := [0xf0f0f0f, 0xf0f00000f0f, 0xf000f000f000f, 0x303030303030303, 0x505050505050505]
def r22_goal : Nat := 0x10707070107070f
def r22_bounds : List (Nat × List Nat × Nat × Nat) := [(0xf0f0f0f, [0xf0f, 0xf000f, 0x3030303, 0x5050505], 7, 0x107070f)]
theorem r22_sub : ∀ b ∈ r22_bounds, r22_mask &&& b.1 = b.1 := by
  have hall : r22_bounds.all (fun b => Nat.beq (Nat.land r22_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r22_goals : ∀ b ∈ r22_bounds, canon b.1 r22_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r22_bounds.all (fun b => Nat.beq (canonF b.1 r22_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r22_forest : Nat → Nat × Nat := fun _ => (0, 0)
def r22_links : Nat → Nat → Option Nat := fun _ _ => none
def r22_trace := dagTraceF r22_mask r22_stock 7 r22_forest
def r22_check := dagCheckNodeF r22_mask r22_goal r22_bounds 0 r22_trace r22_links
set_option maxHeartbeats 0 in
theorem r22_roots : dagCheckRootsF r22_mask r22_goal r22_bounds
    (dagRefF 0 r22_trace r22_links 0) r22_stock 7 = true := by decide +kernel
theorem r22_nodes : ∀ i, 0 ≤ i → i < 0 → r22_check i = true :=
  fun i _ hi => absurd hi (Nat.not_lt_zero i)
theorem r22_known : KnownBin r22_bounds :=
  knownCons r13_lower (
  knownNil)
theorem r22_lower : LowerBin r22_mask r22_stock r22_goal 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r22_known r22_sub r22_goals r22_roots r22_nodes

def r23_mask : Nat := 0x3333333333333333
def r23_stock : List Nat := [0x33333333, 0x333300003333, 0x33003300330033, 0x303030303030303, 0x1111111111111111]
def r23_goal : Nat := 0x113131301131333
def r23_rows : Fin 64 → Fin 64 := decodeRows 0x82082f7ce78082082d74c70082082b6ca6808208296486008208275c65808208255445008208234c248082082144040
set_option maxHeartbeats 0 in
theorem r23_lower : LowerBin r23_mask r23_stock r23_goal 8 := by
  apply lowerBin_of_rowPull r23_rows (stock' := r22_stock)
  · have hall : r23_stock.all (fun w => availBF r22_stock
        (rowCanon r23_rows r23_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r23_rows r23_mask = r22_mask := by decide +kernel
    have hg : rowCanon r23_rows r23_mask r23_goal = r22_goal := by decide +kernel
    rw [hm, hg]
    exact r22_lower

def r24_mask : Nat := 0xff00ff00ff00ff00
def r24_stock : List Nat := [0xff00ff00, 0xff000000ff00, 0xf000f000f000f00, 0x3300330033003300, 0x5500550055005500]
def r24_goal : Nat := 0x100170001005700
def r24_rows : Fin 64 → Fin 64 := decodeRows 0x20961900000028b69b00000030d71d00000038f79f000000a29e39000000aabebb000000b2df3d000000baffbf
set_option maxHeartbeats 0 in
theorem r24_lower : LowerBin r24_mask r24_stock r24_goal 8 := by
  apply lowerBin_of_rowPull r24_rows (stock' := r22_stock)
  · have hall : r24_stock.all (fun w => availBF r22_stock
        (rowCanon r24_rows r24_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r24_rows r24_mask = r22_mask := by decide +kernel
    have hg : rowCanon r24_rows r24_mask r24_goal = r22_goal := by decide +kernel
    rw [hm, hg]
    exact r22_lower

def r25_mask : Nat := 0xffff0000ffff0000
def r25_stock : List Nat := [0xffff0000, 0xff000000ff0000, 0xf0f00000f0f0000, 0x3333000033330000, 0x5555000055550000]
def r25_goal : Nat := 0x117000001570000
def r25_rows : Fin 64 → Fin 64 := decodeRows 0x41161900000049369b00000051571d00000059779f000000c31e39000000cb3ebb000000d35f3d000000db7fbf
set_option maxHeartbeats 0 in
theorem r25_lower : LowerBin r25_mask r25_stock r25_goal 8 := by
  apply lowerBin_of_rowPull r25_rows (stock' := r22_stock)
  · have hall : r25_stock.all (fun w => availBF r22_stock
        (rowCanon r25_rows r25_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r25_rows r25_mask = r22_mask := by decide +kernel
    have hg : rowCanon r25_rows r25_mask r25_goal = r22_goal := by decide +kernel
    rw [hm, hg]
    exact r22_lower

def r26_mask : Nat := 0xff00ff0000000000
def r26_stock : List Nat := [0xff0000000000, 0xf000f0000000000, 0x3300330000000000, 0x5500550000000000]
def r26_goal : Nat := 0x100170000000000
def r26_rows : Fin 64 → Fin 64 := decodeRows 0xa29aab000000b2dbaf000000e39ebb000000f3dfbf
set_option maxHeartbeats 0 in
theorem r26_lower : LowerBin r26_mask r26_stock r26_goal 7 := by
  apply lowerBin_of_rowPull r26_rows (stock' := r13_stock)
  · have hall : r26_stock.all (fun w => availBF r13_stock
        (rowCanon r26_rows r26_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r26_rows r26_mask = r13_mask := by decide +kernel
    have hg : rowCanon r26_rows r26_mask r26_goal = r13_goal := by decide +kernel
    rw [hm, hg]
    exact r13_lower

def r27_mask : Nat := 0xcc00cc00cc00cc
def r27_stock : List Nat := [0xcc00cc, 0xcc000000cc, 0xc000c000c000c, 0x44004400440044]
def r27_goal : Nat := 0x400440044004c
def r27_rows : Fin 64 → Fin 64 := decodeRows 0xdf6000cf20009e60008e20000000000000000000000000005d60004d20001c60000c2000
set_option maxHeartbeats 0 in
theorem r27_lower : LowerBin r27_mask r27_stock r27_goal 6 := by
  apply lowerBin_of_rowPull r27_rows (stock' := r0_stock)
  · have hall : r27_stock.all (fun w => availBF r0_stock
        (rowCanon r27_rows r27_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r27_rows r27_mask = r0_mask := by decide +kernel
    have hg : rowCanon r27_rows r27_mask r27_goal = r0_goal := by decide +kernel
    rw [hm, hg]
    exact r0_lower

def r28_mask : Nat := 0xf000f000f000f0
def r28_stock : List Nat := [0xf000f0, 0xf0000000f0, 0x30003000300030, 0x50005000500050]
def r28_goal : Nat := 0x10005000500070
def r28_rows : Fin 64 → Fin 64 := decodeRows 0xdf6000d740009e60009640000000000000000000000000005d60005540001c6000144000
set_option maxHeartbeats 0 in
theorem r28_lower : LowerBin r28_mask r28_stock r28_goal 6 := by
  apply lowerBin_of_rowPull r28_rows (stock' := r0_stock)
  · have hall : r28_stock.all (fun w => availBF r0_stock
        (rowCanon r28_rows r28_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r28_rows r28_mask = r0_mask := by decide +kernel
    have hg : rowCanon r28_rows r28_mask r28_goal = r0_goal := by decide +kernel
    rw [hm, hg]
    exact r0_lower

def r29_mask : Nat := 0x4444444444444444
def r29_stock : List Nat := [0x44444444, 0x444400004444, 0x44004400440044, 0x404040404040404]
def r29_goal : Nat := 0x4044400444444
def r29_rows : Fin 64 → Fin 64 := decodeRows 0x8a18e8aa9ae00000000000049a59ecbadbe000000000000
set_option maxHeartbeats 0 in
theorem r29_lower : LowerBin r29_mask r29_stock r29_goal 5 := by
  apply lowerBin_of_rowPull r29_rows (stock' := r2_stock)
  · have hall : r29_stock.all (fun w => availBF r2_stock
        (rowCanon r29_rows r29_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r29_rows r29_mask = r2_mask := by decide +kernel
    have hg : rowCanon r29_rows r29_mask r29_goal = r2_goal := by decide +kernel
    rw [hm, hg]
    exact r2_lower

def r30_mask : Nat := 0x2222222222222222
def r30_stock : List Nat := [0x22222222, 0x222200002222, 0x22002200220022, 0x202020202020202]
def r30_goal : Nat := 0x2020200020222
def r30_rows : Fin 64 → Fin 64 := decodeRows 0xf79000759000d71000551000b69000349000961000141000
set_option maxHeartbeats 0 in
theorem r30_lower : LowerBin r30_mask r30_stock r30_goal 5 := by
  apply lowerBin_of_rowPull r30_rows (stock' := r6_stock)
  · have hall : r30_stock.all (fun w => availBF r6_stock
        (rowCanon r30_rows r30_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r30_rows r30_mask = r6_mask := by decide +kernel
    have hg : rowCanon r30_rows r30_mask r30_goal = r6_goal := by decide +kernel
    rw [hm, hg]
    exact r6_lower

def r31_mask : Nat := 0x5050505050505050
def r31_stock : List Nat := [0x50505050, 0x505000005050, 0x50005000500050, 0x1010101010101010]
def r31_goal : Nat := 0x10105000505050
def r31_rows : Fin 64 → Fin 64 := decodeRows 0x10c18e92c9ae00000000000051c59ed3cdbe000000000000
set_option maxHeartbeats 0 in
theorem r31_lower : LowerBin r31_mask r31_stock r31_goal 5 := by
  apply lowerBin_of_rowPull r31_rows (stock' := r2_stock)
  · have hall : r31_stock.all (fun w => availBF r2_stock
        (rowCanon r31_rows r31_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r31_rows r31_mask = r2_mask := by decide +kernel
    have hg : rowCanon r31_rows r31_mask r31_goal = r2_goal := by decide +kernel
    rw [hm, hg]
    exact r2_lower

def r32_mask : Nat := 0x5500550055005500
def r32_stock : List Nat := [0x55005500, 0x550000005500, 0x500050005000500, 0x1100110011001100]
def r32_goal : Nat := 0x100150001005500
def r32_rows : Fin 64 → Fin 64 := decodeRows 0x218000a3800029a000aba00031c000b3c00039e000bbe000
set_option maxHeartbeats 0 in
theorem r32_lower : LowerBin r32_mask r32_stock r32_goal 5 := by
  apply lowerBin_of_rowPull r32_rows (stock' := r6_stock)
  · have hall : r32_stock.all (fun w => availBF r6_stock
        (rowCanon r32_rows r32_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r32_rows r32_mask = r6_mask := by decide +kernel
    have hg : rowCanon r32_rows r32_mask r32_goal = r6_goal := by decide +kernel
    rw [hm, hg]
    exact r6_lower

def r33_mask : Nat := 0xaa00aa00aa00aa
def r33_stock : List Nat := [0xaa00aa, 0xaa000000aa, 0xa000a000a000a, 0x22002200220022]
def r33_goal : Nat := 0x200020002002a
def r33_rows : Fin 64 → Fin 64 := decodeRows 0xdf59e55d51c5000000000000cf18e14d10c1000000000000
set_option maxHeartbeats 0 in
theorem r33_lower : LowerBin r33_mask r33_stock r33_goal 5 := by
  apply lowerBin_of_rowPull r33_rows (stock' := r2_stock)
  · have hall : r33_stock.all (fun w => availBF r2_stock
        (rowCanon r33_rows r33_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r33_rows r33_mask = r2_mask := by decide +kernel
    have hg : rowCanon r33_rows r33_mask r33_goal = r2_goal := by decide +kernel
    rw [hm, hg]
    exact r2_lower

def r34_mask : Nat := 0xc0c0c0c0c0c0c0c0
def r34_stock : List Nat := [0xc0c0c0c0, 0xc0c00000c0c0, 0xc000c000c000c0, 0x4040404040404040]
def r34_goal : Nat := 0x4000404040
def r34_rows : Fin 64 → Fin 64 := decodeRows 0x18738f59779f9a7bafdb7fbf
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

theorem cert_known : KnownBin cert_bounds :=
  knownCons r10_lower (
  knownCons r11_lower (
  knownCons r12_lower (
  knownCons r9_lower (
  knownCons r17_lower (
  knownCons r18_lower (
  knownCons r20_lower (
  knownCons r21_lower (
  knownCons r23_lower (
  knownCons r22_lower (
  knownCons r24_lower (
  knownCons r25_lower (
  knownCons r19_lower (
  knownCons r14_lower (
  knownCons r15_lower (
  knownCons r26_lower (
  knownCons r27_lower (
  knownCons r0_lower (
  knownCons r28_lower (
  knownCons r1_lower (
  knownCons r29_lower (
  knownCons r30_lower (
  knownCons r31_lower (
  knownCons r32_lower (
  knownCons r33_lower (
  knownCons r3_lower (
  knownCons r34_lower (
  knownNil)))))))))))))))))))))))))))

theorem binaryLower : LowerBin cert_mask cert_stock cert_goal 12 :=
  cert_lower cert_known

end PEqualNP.Outside.L_meta_48488
