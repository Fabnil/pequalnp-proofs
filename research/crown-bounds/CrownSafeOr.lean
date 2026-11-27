import PEqualNP.Outside.L_meta_18677

/-!
Relocation of an OR input that vanishes on every negative sample.
The wire relocation is the one used for the diagonal tests of L-meta-18677.
Here the negative samples may be any part of the promise.
-/

namespace CrownSafeOr

open PEqualNP.Outside.L_meta_18677_aux

abbrev Gates := ℕ → Bool × ℕ × ℕ

variable {I : Type} (samples : I → ℕ → Bool) (target : I → Bool)

def Safe (S : Finset ℕ) (g : Gates) (w : ℕ) : Prop :=
  ∀ i, target i = false → val S g (samples i) w = false

def Correct (S : Finset ℕ) (g : Gates) (o : ℕ) : Prop :=
  ∀ i, val S g (samples i) o = target i

def Normal (S : Finset ℕ) (g : Gates) : Prop :=
  ∀ t ∈ S, Safe samples target S g (g t).2.1 ∨ Safe samples target S g (g t).2.2 →
    Safe samples target S g t

noncomputable def unsafeGates (S : Finset ℕ) (g : Gates) : Finset ℕ := by
  classical
  exact S.filter fun w => ¬Safe samples target S g w

private theorem chooseSafe {H : ℕ} {S : Finset ℕ} {g : Gates} {t : ℕ}
    (good : Good H S g) (member : t ∈ S) (notSafeGate : ¬Safe samples target S g t)
    (safeInput : Safe samples target S g (g t).2.1 ∨ Safe samples target S g (g t).2.2) :
    ∃ d b, d < t ∧ b < t ∧ Safe samples target S g d ∧
      ∀ x, val S g x t = (val S g x d || val S g x b) := by
  have op : (g t).1 = false := by
    cases h : (g t).1
    · rfl
    · exfalso
      apply notSafeGate
      intro i hi
      rw [vin good member, h]
      rcases safeInput with left | right
      · simp [bin, left i hi]
      · simp [bin, right i hi]
  obtain ⟨_, first, second⟩ := good t member
  rcases safeInput with left | right
  · refine ⟨_, _, first, second, left, fun x => ?_⟩
    rw [vin good member, op]
    rfl
  · refine ⟨_, _, second, first, right, fun x => ?_⟩
    rw [vin good member, op]
    exact Bool.or_comm _ _

private theorem relocate {H : ℕ} {S : Finset ℕ} {g : Gates} {o : ℕ}
    (good : Good H S g) (correct : Correct samples target S g o)
    (bad : ¬Normal samples target S g) :
    ∃ T h p, Good H T h ∧ Correct samples target T h p ∧ T.card ≤ S.card ∧
      (unsafeGates samples target T h).card < (unsafeGates samples target S g).card := by
  classical
  unfold Normal at bad
  push Not at bad
  obtain ⟨t, member, safeInput, notSafeGate⟩ := bad
  obtain ⟨d, b, beforeD, beforeB, safeD, oldGate⟩ :=
    chooseSafe samples target good member notSafeGate safeInput
  let f := S.sup id + o + H + 1
  have beforeNew (w : ℕ) (hw : w ∈ S) : w < f := by
    have bound : id w ≤ S.sup id := Finset.le_sup hw
    change w ≤ S.sup id at bound
    dsimp [f]
    omega
  have outputBefore : o < f := by dsimp [f]; omega
  have high : H ≤ f := by dsimp [f]; omega
  have dBefore : d < f := beforeD.trans (beforeNew t member)
  let T := nrSet S t f
  let h := nrGate g t b d o f
  have goodNew : Good H T h := by
    intro w hw
    change w ∈ insert f (S.erase t) at hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact by simpa [h, nrGate] using
        And.intro high (And.intro dBefore ((nrAliasLe beforeB o).trans_lt outputBefore))
    · obtain ⟨_, inS⟩ := Finset.mem_erase.mp hw
      obtain ⟨above, a, c⟩ := good w inS
      simpa [h, nrGate, (beforeNew w inS).ne] using
        And.intro above (And.intro ((nrAliasLe beforeB _).trans_lt a)
          ((nrAliasLe beforeB _).trans_lt c))
  have dSame (x : ℕ → Bool) : val T h x d = val S g x d := by
    simpa only [nrAlias, ite_eq_right beforeD.ne] using
      nrEval good goodNew beforeB oldGate x d dBefore (Or.inl beforeD)
  have newOutput (x : ℕ → Bool) : val T h x f =
      (val S g x d || val T h x (nrAlias t b o)) := by
    rw [vin goodNew (Finset.mem_insert_self _ _ : f ∈ T)]
    simp [h, nrGate, bin, dSame]
  have correctNew : Correct samples target T h f := by
    intro i
    rw [newOutput]
    cases hd : val S g (samples i) d with
    | false =>
      rw [Bool.false_or, nrEval good goodNew beforeB oldGate _ _ outputBefore (Or.inr hd)]
      exact correct i
    | true =>
      have ht : target i = true := by
        cases hi : target i
        · exact Bool.noConfusion ((safeD i hi).symm.trans hd)
        · rfl
      simp [ht]
  have outputSafe : Safe samples target T h f := fun i hi => (correctNew i).trans hi
  have fewer : unsafeGates samples target T h ⊆ (unsafeGates samples target S g).erase t := by
    intro w hw
    obtain ⟨wT, notSafe⟩ := Finset.mem_filter.mp hw
    rcases Finset.mem_insert.mp wT with rfl | wT
    · exact (notSafe outputSafe).elim
    · obtain ⟨notT, wS⟩ := Finset.mem_erase.mp wT
      apply Finset.mem_erase.mpr
      refine ⟨notT, Finset.mem_filter.mpr ⟨wS, ?_⟩⟩
      intro oldSafe
      apply notSafe
      intro i hi
      have agree := nrEval good goodNew beforeB oldGate (samples i) w
        (beforeNew w wS) (Or.inr (safeD i hi))
      simpa only [nrAlias, ite_eq_right notT, oldSafe i hi] using agree
  have cost : T.card ≤ S.card :=
    (Finset.card_insert_le f (S.erase t)).trans (Finset.card_erase_add_one member).le
  have badMember : t ∈ unsafeGates samples target S g := Finset.mem_filter.mpr ⟨member, notSafeGate⟩
  exact ⟨T, h, f, goodNew, correctNew, cost,
    (Finset.card_le_card fewer).trans_lt (Finset.card_erase_lt_of_mem badMember)⟩

theorem normalize {H : ℕ} {S : Finset ℕ} {g : Gates} {o : ℕ}
    (good : Good H S g) (correct : Correct samples target S g o) :
    ∃ T h p, Good H T h ∧ Correct samples target T h p ∧ Normal samples target T h ∧
      T.card ≤ S.card := by
  classical
  generalize count : (unsafeGates samples target S g).card = n
  induction n using Nat.strong_induction_on generalizing S g o with
  | ind n ih =>
    by_cases normal : Normal samples target S g
    · exact ⟨S, g, o, good, correct, normal, le_rfl⟩
    · obtain ⟨T, h, p, hTopo, hCorrect, hSize, hFewer⟩ :=
        relocate samples target good correct normal
      obtain ⟨U, k, q, topo, solves, shape, size⟩ :=
        ih _ (hFewer.trans_le count.le) hTopo hCorrect rfl
      exact ⟨U, k, q, topo, solves, shape, size.trans hSize⟩

end CrownSafeOr
