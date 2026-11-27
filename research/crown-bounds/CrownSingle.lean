import CrownErase

/-!
Single-use elimination adapts the AND and OR cases of the proof of L_meta_18242
in open-goat/pequalnp-proofs at 661aa6ad1563cdaa2ecce4b9124db0eeaaa33885
(Apache-2.0). The proof here is uniform in the input dimension.
-/

namespace CrownSingle

open CrownRun CrownForks CrownErase

variable {n : ℕ}


theorem top_elim (O : (BF (n + 1))) :
    ∀ (m : ℕ) (S : (BF (n + 1)) → Prop) (F : (BF (n + 1))), (∀ w, S w → ∀ p, w p = true → O p = true) → F ≠ O →
      UC gF MonoA m (fun w => w = O ∨ S w) F → UC gF MonoA m S F
  | 0, S, F, _, hF, hu => by
    rcases hu with h | h
    · exact absurd h hF
    · exact h
  | m + 1, S, F, hS, hF, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (top_elim O m S F hS hF hu)
    · have hle : ∀ w, (w = O ∨ S w) → ∀ p, w p = true → O p = true := by
        rintro w (rfl | hw) p hp
        · exact hp
        · exact hS w hw p hp
      have free : (gF k a b = O ∨ S (gF k a b)) → UC gF MonoA (m + 1) S F := by
        intro hg
        refine Or.inl (top_elim O m S F hS hF (UC_monoS gF MonoA m _ _ F ?_ hu))
        rintro w (rfl | hw)
        · exact hg
        · exact hw
      by_cases hao : a = O
      · subst hao
        apply free
        rcases mono_cases k hk with rfl | rfl
        · have : gF 0 a b = b := by
            rw [gF_and]
            funext p
            cases hbp : b p
            · simp
            · simp [hle b hb p hbp]
          rw [this]; exact hb
        · have : gF 1 a b = a := by
            rw [gF_or]
            funext p
            cases hbp : b p
            · simp
            · simp [hle b hb p hbp]
          rw [this]; exact Or.inl rfl
      by_cases hbo : b = O
      · subst hbo
        apply free
        rcases mono_cases k hk with rfl | rfl
        · have : gF 0 a b = a := by
            rw [gF_and]
            funext p
            cases hap : a p
            · simp
            · simp [hle a ha p hap]
          rw [this]; exact ha
        · have : gF 1 a b = b := by
            rw [gF_or]
            funext p
            cases hap : a p
            · simp
            · simp [hle a ha p hap]
          rw [this]; exact Or.inl rfl
      have ha' : S a := ha.resolve_left hao
      have hb' : S b := hb.resolve_left hbo
      refine UC_gate k a b hk ha' hb' (top_elim O m _ F ?_ hF (UC_monoS gF MonoA m _ _ F ?_ hu))
      · rintro w (rfl | hw) p hp
        · rcases mono_cases k hk with rfl | rfl
          · rw [gF_and] at hp
            simp only [Bool.and_eq_true] at hp
            exact hS a ha' p hp.1
          · rw [gF_or] at hp
            simp only [Bool.or_eq_true] at hp
            rcases hp with hp | hp
            · exact hS a ha' p hp
            · exact hS b hb' p hp
        · exact hS w hw p hp
      · rintro w (rfl | rfl | hw)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr hw)

def XI (x : Fin (n + 1)) (w : (BF (n + 1))) : Prop := ∀ p b, w (Function.update p x b) = w p

def MonoF (w : (BF (n + 1))) : Prop :=
  ∀ p q : Fin (n + 1) → Bool, (∀ i, p i = true → q i = true) → w p = true → w q = true

def InvX (x : Fin (n + 1)) (w : (BF (n + 1))) : Prop := XI x w ∧ MonoF w ∧ w (fun _ => false) = false

theorem InvX_gate {x : Fin (n + 1)} {k : Fin 4} (hk : MonoA k) {a b : (BF (n + 1))} (ha : InvX x a)
    (hb : InvX x b) : InvX x (gF k a b) := by
  rcases mono_cases k hk with rfl | rfl
  · refine ⟨fun p v => ?_, fun p q hpq h => ?_, ?_⟩
    · show (a _ && b _) = (a _ && b _)
      rw [ha.1 p v, hb.1 p v]
    · rw [gF_and] at h ⊢
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨ha.2.1 p q hpq h.1, hb.2.1 p q hpq h.2⟩
    · show (a _ && b _) = false
      rw [ha.2.2]; rfl
  · refine ⟨fun p v => ?_, fun p q hpq h => ?_, ?_⟩
    · show (a _ || b _) = (a _ || b _)
      rw [ha.1 p v, hb.1 p v]
    · rw [gF_or] at h ⊢
      simp only [Bool.or_eq_true] at h ⊢
      exact h.imp (ha.2.1 p q hpq) (hb.2.1 p q hpq)
    · show (a _ || b _) = false
      rw [ha.2.2, hb.2.2]; rfl

theorem InvX_var {x m : Fin (n + 1)} (h : m ≠ x) : InvX x (var m) :=
  ⟨fun p v => by simp [var, Function.update_of_ne h], fun p q hpq hp => hpq m hp, rfl⟩

theorem mono_comm {k : Fin 4} (hk : MonoA k) (a b : (BF (n + 1))) : gF k a b = gF k b a := by
  rcases mono_cases k hk with rfl | rfl
  · rw [gF_and, gF_and]; funext p; exact Bool.and_comm _ _
  · rw [gF_or, gF_or]; funext p; exact Bool.or_comm _ _

theorem upd_single_true (i x : Fin (n + 1)) :
    Function.update (singletonInput i) x true = pairInput i x := by
  funext m
  by_cases hm : m = x
  · subst hm; simp [pairInput, singletonInput]
  · simp [singletonInput, pairInput, hm]

theorem single_eq_upd (x : Fin (n + 1)) :
    singletonInput x = Function.update (fun _ => false) x true := by
  funext m
  by_cases hm : m = x
  · subst hm; simp [singletonInput]
  · simp [singletonInput, hm]

theorem outF_rel (b' : (BF (n + 1))) (p : Fin (n + 1) → Bool) (hb : b' p = false) :
    ∀ (ys ys' : List (BF (n + 1))), List.Forall₂ (fun w w' => ∀ q, b' q = false → w q = w' q) ys ys' →
      outF ys p = outF ys' p
  | _, _, List.Forall₂.nil => rfl
  | _, _, List.Forall₂.cons h t => by
    have ih := outF_rel b' p hb _ _ t
    simp only [outF, List.any_cons] at ih ⊢
    rw [h p hb, ih]

def SUc (x : Fin (n + 1)) (y0 : (BF (n + 1))) (yt : List (BF (n + 1))) (s : ℕ) (r : List (BF (n + 1))) : Prop :=
  ((if otop x ∈ r then 2 else 3) ≤ s + yt.length ∧
    ∀ S : (BF (n + 1)) → Prop, (∀ w ∈ r, S w) → S (otop x) →
      UC gF MonoA (s + yt.length - (if otop x ∈ r then 2 else 3)) S
        (rst x (outF (y0 :: yt)))) ∨
  ∃ (c : ℕ) (h0 : (BF (n + 1))) (ys' : List (BF (n + 1))) (s' : ℕ), s = s' + 1 ∧ ys'.length = yt.length + 1 ∧
    ThresholdOn (outF (h0 :: ys')) ∧
    MR (h0 :: ys') s' (List.replicate (c + 1) (var x) ++ r)

theorem SU (size : 2 ≤ n) (x : Fin (n + 1)) (y0 : (BF (n + 1))) (yt : List (BF (n + 1)))
    (hF : ThresholdOn (outF (y0 :: yt))) :
    ∀ (s : ℕ) (r : List (BF (n + 1))), MR (y0 :: yt) s (var x :: r) → (∀ w ∈ r, InvX x w) →
      SUc x y0 yt s r := by
  intro s
  induction s with
  | zero =>
    intro r h _
    exfalso
    have hp := (TR.inv h).1 rfl
    have hm : var x ∈ y0 :: yt := hp.mem_iff.1 (by simp)
    have h1 : outF (y0 :: yt) (singletonInput x) = true :=
      (outF_true _ _).2 ⟨var x, hm, by simp [var, singletonInput]⟩
    rw [hF.1 x] at h1
    exact Bool.noConfusion h1
  | succ s ih =>
    intro r h hinv
    obtain ⟨k, u, a, b, r₁, hk, hp, hr⟩ := (TR.inv h).2 s rfl
    have consume : ∀ b' : (BF (n + 1)), r.Perm (b' :: r₁) → gF k a b = gF k (var x) b' →
        SUc x y0 yt (s + 1) r := by
      intro b' hrp hg
      unfold SUc
      rw [hg] at hr
      have hb' : InvX x b' := hinv b' (hrp.mem_iff.2 (by simp))
      have hr1 : ∀ w ∈ r₁, InvX x w := fun w hw => hinv w (hrp.mem_iff.2 (by simp [hw]))
      have sens : ∀ i, i ≠ x → gF k (var x) b' (pairInput i x) =
          gF k (var x) b' (singletonInput i) → False := by
        intro i hi hgg
        have hd := respectsInputAgreement (a := pairInput i x) (b := singletonInput i) hr (by
          intro w hw
          rcases List.mem_append.1 hw with hw | hw
          · rw [List.eq_of_mem_replicate hw]; exact hgg
          · rw [← upd_single_true]
            exact (hr1 w hw).1 _ _)
        have h2 := outF_congr _ _ _ hd
        rw [hF.1 i, hF.2 i x hi] at h2
        exact Bool.noConfusion h2
      have hbx : ∀ i, i ≠ x → b' (pairInput i x) = b' (singletonInput i) := fun i _ => by
        rw [← upd_single_true]; exact hb'.1 _ _
      have hv1 : ∀ i, var x (pairInput i x) = true := fun i => by simp [var, pairInput, singletonInput]
      have hv2 : ∀ i, i ≠ x → var x (singletonInput i) = false := fun i hi => by
        simp [var, singletonInput, Ne.symm hi]
      rcases mono_cases k hk with rfl | rfl
      · left
        have hone : ∀ i, i ≠ x → b' (singletonInput i) = true := by
          intro i hi
          by_contra hc
          have hc' : b' (singletonInput i) = false := by simpa using hc
          apply sens i hi
          rw [gF_and]
          show (var x _ && b' _) = (var x _ && b' _)
          rw [hbx i hi, hc', hv2 i hi]; simp
        have hbo : b' = otop x := by
          funext p
          rw [← hb'.1 p false]
          by_cases hex : ∃ i, i ≠ x ∧ p i = true
          · obtain ⟨i, hi, hpi⟩ := hex
            have : otop x p = true := by simp only [otop, decide_eq_true_eq]; exact ⟨i, hi, hpi⟩
            rw [this]
            refine hb'.2.1 (singletonInput i) _ ?_ (hone i hi)
            intro m hm
            have : m = i := by simpa [singletonInput] using hm
            subst this
            rw [Function.update_of_ne hi]; exact hpi
          · have : otop x p = false := by simp only [otop, decide_eq_false_iff_not]; exact hex
            rw [this]
            have hz : Function.update p x false = fun _ => false := by
              funext m
              by_cases hm : m = x
              · subst hm; simp
              · rw [Function.update_of_ne hm]
                by_contra hc
                exact hex ⟨m, hm, by simpa using hc⟩
            rw [hz]; exact hb'.2.2
        have hmem : otop x ∈ r := hrp.mem_iff.2 (by simp [hbo])
        have hdead : rst x (gF 0 (var x) b') = zF := by
          funext p
          show (var x _ && b' _) = false
          simp [var]
        have hc := complete_run y0 yt hr
        obtain ⟨hd1, hd2⟩ := pot_dead x (restrictionNonzero size hF x) hc
        rw [dcount_rep] at hd1 hd2
        simp only [hdead, ite_true] at hd1 hd2
        simp only [hmem, ite_true]
        refine ⟨by omega, fun S hS _ => UC_le (by omega) (hd2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hdead) hwz
        · have : rst x w = w := funext fun p => (hr1 w hw).1 p false
          rw [this]
          exact hS w (hrp.mem_iff.2 (by simp [hw]))
      · right
        have hzero : ∀ i, b' (singletonInput i) = false := by
          intro i
          by_cases hi : i = x
          · subst hi
            rw [single_eq_upd, hb'.1]; exact hb'.2.2
          · by_contra hc
            have hc' : b' (singletonInput i) = true := by simpa using hc
            apply sens i hi
            rw [gF_or]
            show (var x _ || b' _) = (var x _ || b' _)
            rw [hbx i hi, hc', hv1 i]; simp
        have hrel : List.Forall₂ (fun w w' => ∀ q, b' q = false → w q = w' q)
            (List.replicate (u + 1) (gF 1 (var x) b') ++ r₁)
            (List.replicate (u + 1) (var x) ++ r₁) := by
          refine List.rel_append ?_ (List.forall₂_same.2 fun _ _ _ _ => rfl)
          generalize u + 1 = copies
          induction copies with
          | zero => exact List.Forall₂.nil
          | succ n ihn =>
            refine List.Forall₂.cons (fun q hq => ?_) ihn
            show (var x q || b' q) = var x q
            rw [hq]; simp
        obtain ⟨ys', hy, hrun⟩ := TR.rel (A := MonoA)
          (fun w w' => ∀ q, b' q = false → w q = w' q)
          (fun k a a' b b' ha hb q hq => by
            show zeroGate k (a q) (b q) = zeroGate k (a' q) (b' q)
            rw [ha q hq, hb q hq]) hr _ hrel
        refine ⟨u, b', ys', s, rfl, ?_, ⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩
        · have := hy.length_eq
          simpa using this.symm
        · have e := outF_rel b' (singletonInput i) (hzero i) _ _ hy
          have h3 : outF (b' :: ys') (singletonInput i) =
              (b' (singletonInput i) || outF ys' (singletonInput i)) := by simp [outF]
          rw [h3, hzero i, ← e, hF.1 i]; rfl
        · have h3 : outF (b' :: ys') (pairInput i j) =
              (b' (pairInput i j) || outF ys' (pairInput i j)) := by simp [outF]
          rw [h3]
          cases hbp : b' (pairInput i j)
          · have e := outF_rel b' (pairInput i j) hbp _ _ hy
            rw [← e, hF.2 i j hij]; rfl
          · rfl
        · have p1 : (b' :: (List.replicate (u + 1) (var x) ++ r₁)).Perm
              (List.replicate (u + 1) (var x) ++ r) :=
            List.perm_middle.symm.trans (List.Perm.append_left _ hrp.symm)
          exact TR.perm p1 (frame b' hrun)
    by_cases hax : a = var x
    · subst hax
      exact consume b hp.cons_inv rfl
    by_cases hbx : b = var x
    · subst hbx
      have hp' : (var x :: r).Perm (var x :: a :: r₁) := hp.trans (List.Perm.swap _ _ _)
      exact consume a hp'.cons_inv (mono_comm hk a (var x))
    have hx1 : var x ∈ r₁ := by
      have : var x ∈ a :: b :: r₁ := hp.mem_iff.1 (by simp)
      simp only [List.mem_cons] at this
      rcases this with h1 | h1 | h1
      · exact absurd h1.symm hax
      · exact absurd h1.symm hbx
      · exact h1
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hx1
    have hr2 : r.Perm (a :: b :: (l₁ ++ l₂)) := by
      have p1 : (a :: b :: (l₁ ++ var x :: l₂)).Perm (var x :: a :: b :: (l₁ ++ l₂)) :=
        List.perm_middle (l₁ := a :: b :: l₁)
      exact (hp.trans p1).cons_inv
    have ha : InvX x a := hinv a (hr2.mem_iff.2 (by simp))
    have hb : InvX x b := hinv b (hr2.mem_iff.2 (by simp))
    have hsub : ∀ w ∈ l₁ ++ l₂, w ∈ r := fun w hw => hr2.mem_iff.2 (by simp [List.mem_append.1 hw])
    have p2 : (List.replicate (u + 1) (gF k a b) ++ (l₁ ++ var x :: l₂)).Perm
        (var x :: (List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂))) := by
      rw [← List.append_assoc, ← List.append_assoc]
      exact List.perm_middle
    have hinv2 : ∀ w ∈ List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂), InvX x w := by
      intro w hw
      rcases List.mem_append.1 hw with hw | hw
      · rw [List.eq_of_mem_replicate hw]; exact InvX_gate hk ha hb
      · exact hinv w (hsub w hw)
    have hih := ih _ (TR.perm p2 hr) hinv2
    unfold SUc at hih ⊢
    rcases hih with ⟨hA1, hA2⟩ | ⟨c, h0, ys', s', hs', hl, hthr, hrun⟩
    · left
      by_cases hgo : gF k a b = otop x
      · have hm : otop x ∈ List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂) := by
          rw [hgo]; simp
        simp only [hm, ite_true] at hA1 hA2
        refine ⟨by split_ifs <;> omega, fun S hS hSo => ?_⟩
        refine UC_le (by split_ifs <;> omega) (hA2 S ?_ hSo)
        intro w hw
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hgo]; exact hSo
        · exact hS w (hsub w hw)
      · have hiff : otop x ∈ List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂) → otop x ∈ r := by
          intro hm
          rcases List.mem_append.1 hm with hm | hm
          · exact absurd (List.eq_of_mem_replicate hm).symm hgo
          · exact hsub _ hm
        have hcc : (if otop x ∈ r then 2 else 3) ≤
            (if otop x ∈ List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂) then 2 else 3) := by
          by_cases h1 : otop x ∈ List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂)
          · simp [h1, hiff h1]
          · simp only [h1, ite_false]; split_ifs <;> omega
        refine ⟨by omega, fun S hS hSo => ?_⟩
        have h1 := hA2 (fun w => w = gF k a b ∨ S w) (by
          intro w hw
          rcases List.mem_append.1 hw with hw | hw
          · exact Or.inl (List.eq_of_mem_replicate hw)
          · exact Or.inr (hS w (hsub w hw))) (Or.inr hSo)
        have h2 := UC_gate k a b hk (hS a (hr2.mem_iff.2 (by simp)))
          (hS b (hr2.mem_iff.2 (by simp))) h1
        exact UC_le (by omega) h2
    · right
      refine ⟨c, h0, ys', s' + 1, by omega, hl, hthr, ?_⟩
      have p3 : (List.replicate (c + 1) (var x) ++ r).Perm
          (a :: b :: (List.replicate (c + 1) (var x) ++ (l₁ ++ l₂))) := by
        refine (List.Perm.append_left _ hr2).trans ?_
        exact List.perm_middle.trans (List.Perm.cons a List.perm_middle)
      have p4 : (List.replicate (c + 1) (var x) ++
          (List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂))).Perm
          (List.replicate (u + 1) (gF k a b) ++
            (List.replicate (c + 1) (var x) ++ (l₁ ++ l₂))) :=
        List.perm_append_comm_assoc _ _ _
      subst hs'
      exact TR.perm p3.symm (TR.step k u hk (TR.perm p4 hrun))

end CrownSingle
