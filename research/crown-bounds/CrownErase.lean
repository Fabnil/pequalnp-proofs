import CrownRun
import CrownForks

/-! Gate elimination under restriction, adapted from L_meta_18242
in open-goat/pequalnp-proofs (Apache-2.0). -/

namespace CrownErase

open CrownRun CrownForks

variable {width : ℕ}

def dcount (p : Fin width) (ws : List (BF width)) : ℕ := ws.countP fun w => decide (rst p w = zF)

theorem dcount_cons (p : Fin width) (a : (BF width)) (l : List (BF width)) :
    dcount p (a :: l) = dcount p l + if rst p a = zF then 1 else 0 := by
  simp [dcount, List.countP_cons]

theorem dcount_rep (p : Fin width) (n : ℕ) (g : (BF width)) (r : List (BF width)) :
    dcount p (List.replicate n g ++ r) = (if rst p g = zF then n else 0) + dcount p r := by
  simp only [dcount, List.countP_append, List.countP_replicate]
  split_ifs <;> simp_all

theorem pot_dead {A : Fin 4 → Prop} (p : Fin width) {F : (BF width)} (hF : rst p F ≠ zF) {s : ℕ}
    {ws : List (BF width)} (h : TR gF (fun k _ _ => A k) [F] s ws) :
    dcount p ws ≤ s ∧ ∀ S : (BF width) → Prop, (∀ w ∈ ws, rst p w ≠ zF → S (rst p w)) →
      UC gF A (s - dcount p ws) S (rst p F) := by
  refine TR.ind (P := fun s ws => dcount p ws ≤ s ∧ ∀ S : (BF width) → Prop,
    (∀ w ∈ ws, rst p w ≠ zF → S (rst p w)) → UC gF A (s - dcount p ws) S (rst p F)) h ?_ ?_ ?_
  · refine ⟨by simp [dcount, hF], fun S hS => ?_⟩
    have : dcount p [F] = 0 := by simp [dcount, hF]
    rw [this]
    exact hS F (by simp) hF
  · intro s xs zs hp _ ih
    have hc : dcount p zs = dcount p xs := (hp.countP_eq _).symm
    rw [hc]
    exact ⟨ih.1, fun S hS => ih.2 S fun w hw => hS w (hp.mem_iff.1 hw)⟩
  · intro s a b r k u hk _ ih
    obtain ⟨ih1, ih2⟩ := ih
    have hg : rst p (gF k a b) = gF k (rst p a) (rst p b) := rfl
    rw [dcount_rep] at ih1 ih2
    rw [dcount_cons, dcount_cons]
    have hmem : ∀ (S : (BF width) → Prop), (∀ w ∈ a :: b :: r, rst p w ≠ zF → S (rst p w)) →
        ∀ w ∈ r, rst p w ≠ zF → S (rst p w) := fun S hS w hw => hS w (by simp [hw])
    by_cases ha : rst p a = zF <;> by_cases hb : rst p b = zF
    · have hgz : rst p (gF k a b) = zF := by rw [hg, ha, hb, gF_zero_zero]
      simp only [hgz, ha, hb, ite_true] at ih1 ih2 ⊢
      refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
      intro w hw hwz
      rcases List.mem_append.1 hw with hw | hw
      · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
      · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · have hgb : rst p (gF k a b) = rst p b := by
          rcases gF_zero_left k (rst p b) with h | h
          · exact absurd (by rw [hg, ha, h]) hgz
          · rw [hg, ha, h]
        simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hgb]
          exact hS b (by simp) hb
        · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · have hga : rst p (gF k a b) = rst p a := by
          rcases gF_zero_right k (rst p a) with h | h
          · exact absurd (by rw [hg, hb, h]) hgz
          · rw [hg, hb, h]
        simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hga]
          exact hS a (by simp) ha
        · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · simp only [hgz, ha, hb, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => ?_⟩
        have h1 := ih2 (fun w => w = gF k (rst p a) (rst p b) ∨ S w) (by
          intro w hw hwz
          rcases List.mem_append.1 hw with hw | hw
          · exact Or.inl (by rw [List.eq_of_mem_replicate hw, hg])
          · exact Or.inr (hmem S hS w hw hwz))
        have h2 := UC_gate k (rst p a) (rst p b) hk (hS a (by simp) ha) (hS b (by simp) hb) h1
        exact UC_le (by omega) h2

theorem rst_var_eq {j p : Fin width} (same : j = p) : rst p (var j) = zF := by
  subst j
  funext x
  simp [rst, var, zF]

theorem rst_var_ne {j p : Fin width} (different : j ≠ p) : rst p (var j) = var j := by
  funext x
  simp [rst, var, Function.update_of_ne different]

theorem rst_var_zero_iff {j p : Fin width} : rst p (var j) = zF ↔ j = p := by
  constructor
  · intro eq
    by_contra! ne
    rw [rst_var_ne ne] at eq
    have value := congrFun eq (fun _ => true)
    exact Bool.noConfusion value
  · exact rst_var_eq

theorem dcount_vars (p : Fin width) (idx : List (Fin width)) :
    dcount p (idx.map var) = idx.count p := by
  induction idx with
  | nil => rfl
  | cons j js ih =>
    rw [List.map_cons, dcount_cons, ih]
    by_cases same : j = p <;> simp [rst_var_zero_iff, same]

theorem eliminateVariable {F : BF width} {s : ℕ} {idx : List (Fin width)}
    (run : MR [F] s (idx.map var)) (p : Fin width) (nonzero : rst p F ≠ zF) :
    idx.count p ≤ s ∧
      UC gF MonoA (s - idx.count p) (fun f => ∃ j : Fin width, j ≠ p ∧ f = var j) (rst p F) := by
  have h := pot_dead p nonzero run
  rw [dcount_vars] at h
  refine ⟨h.1, h.2 _ ?_⟩
  intro f found alive
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp found
  have different : j ≠ p := fun eq => alive (rst_var_eq eq)
  exact ⟨j, different, rst_var_ne different⟩

noncomputable def liftBits {n : ℕ} (p : Fin (n + 1)) (x : Fin n → Bool) (i : Fin (n + 1)) : Bool :=
  if h : ∃ j, p.succAbove j = i then x h.choose else false

theorem liftBits_on {n : ℕ} (p : Fin (n + 1)) (x : Fin n → Bool) (j : Fin n) :
    liftBits p x (p.succAbove j) = x j := by
  classical
  unfold liftBits
  split_ifs with h
  · rw [Fin.succAbove_right_injective h.choose_spec]
  · exact False.elim (h ⟨j, rfl⟩)

theorem liftBits_at {n : ℕ} (p : Fin (n + 1)) (x : Fin n → Bool) : liftBits p x p = false := by
  classical
  simp [liftBits]

theorem liftBits_fixed {n : ℕ} (p : Fin (n + 1)) (x : Fin n → Bool) :
    Function.update (liftBits p x) p false = liftBits p x := by
  funext j
  by_cases same : j = p
  · subst j
    simp [liftBits_at]
  · simp [Function.update_of_ne same]

theorem liftBits_single {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    liftBits p (singletonInput i) = singletonInput (p.succAbove i) := by
  funext j
  by_cases same : j = p
  · subst j
    simp [liftBits_at, singletonInput, (Fin.succAbove_ne p i).symm]
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq (x := j) (y := p) same
    rw [liftBits_on]
    simp [singletonInput, Fin.succAbove_right_injective.eq_iff]

theorem liftBits_pair {n : ℕ} (p : Fin (n + 1)) (i j : Fin n) :
    liftBits p (pairInput i j) = pairInput (p.succAbove i) (p.succAbove j) := by
  funext k
  by_cases same : k = p
  · subst k
    simp [liftBits_at, singletonInput, pairInput, (Fin.succAbove_ne p i).symm, (Fin.succAbove_ne p j).symm]
  · obtain ⟨r, rfl⟩ := Fin.exists_succAbove_eq (x := k) (y := p) same
    rw [liftBits_on]
    simp [singletonInput, pairInput, Fin.succAbove_right_injective.eq_iff]

theorem liftThreshold {n : ℕ} {F : BF (n + 1)} (test : ThresholdOn F) (p : Fin (n + 1)) :
    ThresholdOn (fun x => F (liftBits p x)) := by
  refine ⟨fun i => ?_, fun i j ne => ?_⟩
  · change F (liftBits p (singletonInput i)) = false
    rw [liftBits_single]
    exact test.1 _
  · change F (liftBits p (pairInput i j)) = true
    rw [liftBits_pair]
    exact test.2 _ _ (fun eq => ne (Fin.succAbove_right_injective eq))

theorem projectUC {n s : ℕ} (p : Fin (n + 1)) {F : BF (n + 1)}
    (compute : UC gF MonoA s (fun f => ∃ j : Fin (n + 1), j ≠ p ∧ f = var j) F) :
    UC gF MonoA s (fun f => ∃ j : Fin n, f = var j) (fun x => F (liftBits p x)) := by
  apply UC_map (fun f x => f (liftBits p x)) (fun _ _ _ => rfl) s _ _ F ?_ compute
  rintro f ⟨j, ne, rfl⟩
  obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq (x := j) (y := p) ne
  exact ⟨i, funext fun x => liftBits_on p x i⟩

theorem eraseProjection {n s : ℕ} {F : BF (n + 1)} {idx : List (Fin (n + 1))}
    (run : MR [F] s (idx.map var)) (p : Fin (n + 1)) (nonzero : rst p F ≠ zF) :
    UC gF MonoA (s - idx.count p) (fun f => ∃ j : Fin n, f = var j)
      (fun x => F (liftBits p x)) := by
  have phase := projectUC p (eliminateVariable run p nonzero).2
  have same : (fun x => rst p F (liftBits p x)) = fun x => F (liftBits p x) := by
    funext x
    simp [rst, liftBits_fixed]
  rwa [same] at phase

theorem respectsInputAgreement {outputs ws : List (BF width)} {s : ℕ}
    (run : MR outputs s ws) {a b : Fin width → Bool}
    (same : ∀ f ∈ ws, f a = f b) : ∀ f ∈ outputs, f a = f b := by
  refine (TR.ind (P := fun _ ts => (∀ f ∈ ts, f a = f b) → ∀ f ∈ outputs, f a = f b)
    run (fun h => h) ?_ ?_) same
  · intro _ xs ys perm _ ih h
    exact ih fun f hf => h f (perm.mem_iff.mp hf)
  · intro _ x y rest k u _ _ ih h
    apply ih
    intro f hf
    rcases List.mem_append.mp hf with hnew | hold
    · rw [List.eq_of_mem_replicate hnew, gF, gF, h x (by simp), h y (by simp)]
    · exact h f (by simp [hold])

theorem everyInputUsed {F : BF width} {idx : List (Fin width)} {s : ℕ}
    (size : 2 ≤ width) (run : MR [F] s (idx.map var)) (test : ThresholdOn F) (i : Fin width) :
    1 ≤ idx.count i := by
  by_contra! h
  have absent : i ∉ idx := by
    intro hi
    have := List.count_pos_iff.mpr hi
    omega
  let z : Fin width := ⟨0, by omega⟩
  let o : Fin width := ⟨1, by omega⟩
  have diff : z ≠ o := by
    intro e
    cases congrArg Fin.val e
  obtain ⟨j, ne⟩ : ∃ j : Fin width, i ≠ j := by
    by_cases e : i = z
    · exact ⟨o, e ▸ diff⟩
    · exact ⟨z, e⟩
  have eq : F (singletonInput j) = F (pairInput i j) := by
    apply respectsInputAgreement run _ _ (by simp)
    rintro f hf
    obtain ⟨k, used, rfl⟩ := List.mem_map.mp hf
    have ki : k ≠ i := fun e => absent (e ▸ used)
    simp [var, singletonInput, pairInput, ki]
  rw [test.1 j, test.2 i j ne] at eq
  contradiction

theorem restrictionNonzero {n : ℕ} {F : BF (n + 1)} (size : 2 ≤ n)
    (test : ThresholdOn F) (p : Fin (n + 1)) : rst p F ≠ zF := by
  intro bad
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have ne : i ≠ j := by
    intro e
    cases congrArg Fin.val e
  have yes := (liftThreshold test p).2 i j ne
  change F (liftBits p (pairInput i j)) = true at yes
  have eq := congrFun bad (liftBits p (pairInput i j))
  simp [rst, zF, liftBits_fixed, yes] at eq

theorem atMostTwice {n lower s : ℕ} {F : BF (n + 1)} {idx : List (Fin (n + 1))}
    (size : 2 ≤ n) (run : MR [F] s (idx.map var)) (test : ThresholdOn F)
    (floor : ∀ {t : ℕ} {G : BF n}, ThresholdOn G →
      UC gF MonoA t (fun f => ∃ j : Fin n, f = var j) G → lower ≤ t)
    (small : s ≤ lower + 2) (p : Fin (n + 1)) : idx.count p ≤ 2 := by
  have nonzero := restrictionNonzero size test p
  have enough := floor (liftThreshold test p) (eraseProjection run p nonzero)
  have actual := (eliminateVariable run p nonzero).1
  omega

theorem outF_true (ys : List (BF width)) (p : Fin width → Bool) :
    outF ys p = true ↔ ∃ y ∈ ys, y p = true := by
  simp [outF]

theorem outF_congr (ys : List (BF width)) (p p' : Fin width → Bool) (h : ∀ y ∈ ys, y p = y p') :
    outF ys p = outF ys p' := by
  rw [Bool.eq_iff_iff, outF_true, outF_true]
  constructor
  · rintro ⟨y, hy, hp⟩; exact ⟨y, hy, by rw [← h y hy]; exact hp⟩
  · rintro ⟨y, hy, hp⟩; exact ⟨y, hy, by rw [h y hy]; exact hp⟩

theorem or_chain : ∀ (ys : List (BF width)) (y : (BF width)), MR [outF (y :: ys)] ys.length (y :: ys)
  | [], y => by
    have : outF [y] = y := funext fun x => by simp [outF]
    rw [this]
    exact TR.done
  | y2 :: rest, y => by
    have h := or_chain rest (gF 1 y y2)
    have e : outF (gF 1 y y2 :: rest) = outF (y :: y2 :: rest) :=
      funext fun x => by simp [outF, gF_or, Bool.or_assoc]
    rw [e] at h
    exact TR.step (r := rest) 1 0 (by simp [MonoA]) h

theorem complete_run (y0 : (BF width)) (yt : List (BF width)) {s : ℕ} {ws : List (BF width)} (h : MR (y0 :: yt) s ws) :
    MR [outF (y0 :: yt)] (s + yt.length) ws := by
  refine TR.ind (P := fun s ws => MR [outF (y0 :: yt)] (s + yt.length) ws) h ?_ ?_ ?_
  · rw [Nat.zero_add]; exact or_chain yt y0
  · intro s xs zs hp _ ih; exact TR.perm hp ih
  · intro s a b r k u hc _ ih
    have e : s + 1 + yt.length = s + yt.length + 1 := by omega
    rw [e]
    exact TR.step k u hc ih

theorem frame (h0 : (BF width)) {ys : List (BF width)} {s : ℕ} {ws : List (BF width)} (h : MR ys s ws) :
    MR (h0 :: ys) s (h0 :: ws) := by
  refine TR.ind (P := fun s ws => MR (h0 :: ys) s (h0 :: ws)) h TR.done ?_ ?_
  · intro s xs zs hp _ ih; exact TR.perm (hp.cons h0) ih
  · intro s a b r k u hc _ ih
    have p1 : (a :: b :: h0 :: r).Perm (h0 :: a :: b :: r) :=
      List.perm_middle (l₁ := [a, b])
    have p2 : (h0 :: (List.replicate (u + 1) (gF k a b) ++ r)).Perm
        (List.replicate (u + 1) (gF k a b) ++ h0 :: r) := List.perm_middle.symm
    exact TR.perm p1 (TR.step k u hc (TR.perm p2 ih))

theorem thresholdRequiresGate {F : BF width} {s : ℕ} (test : ThresholdOn F)
    (compute : UC gF MonoA s (fun f => ∃ i : Fin width, f = var i) F) : 1 ≤ s := by
  cases s with
  | zero =>
    obtain ⟨i, rfl⟩ := compute
    have bad := test.1 i
    simp [var, singletonInput] at bad
  | succ s => omega

end CrownErase
