import CrownMargin
import CrownSharedCuts

namespace CrownTenCases

open CrownForks CrownForest

/-- A change is absorbed if every shared formula detecting a changed argument is
    already true, and the output formula has no changed argument. -/
def absorbed {A : Type} : SharedFormula A → (A → Bool) → (A → Bool) → Prop
  | .tree f, x, y => leafWeight f (fun a => rise (x a) (y a)) = 0
  | .share f _ tail, x, y =>
    (f.evalWith x = true ∨ leafWeight f (fun a => rise (x a) (y a)) = 0) ∧
      absorbed tail (withHead (f.evalWith x) x) (withHead (f.evalWith x) y)

theorem eval_eq_of_absorbed {A : Type} (E : SharedFormula A) (x y : A → Bool)
    (mono : ∀ a, x a ≤ y a) (hold : absorbed E x y) : E.eval x = E.eval y := by
  induction E with
  | tree f => exact eqOfNoRise f mono hold
  | share f _ tail ih =>
    change (_ ∨ _) ∧ _ at hold
    have head : f.evalWith x = f.evalWith y := by
      rcases hold.1 with on | zero
      · exact on.trans ((Bool.le_iff_imp.mp (evalMono f mono)) on).symm
      · exact eqOfNoRise f mono zero
    simp only [SharedFormula.eval, ← head]
    exact ih _ _ (withHeadMono le_rfl mono) hold.2

theorem pairNotAbsorbed {I : Type} [DecidableEq I] (E : SharedFormula I)
    (test : ThresholdOn E.eval) {i j : I} (ne : i ≠ j) :
    ¬ absorbed E (singletonInput j) (pairInput i j) := by
  intro hold
  have same := eval_eq_of_absorbed E _ _ (TwoShared.otherSingleton_pair i j) hold
  rw [test.1 j, test.2 i j ne] at same
  contradiction

/-- With the first three flags active at the distinguished input, the four
    groups of hot inputs must all be full, and there is one cold input. -/
theorem thirdFillsAll (cold p q r s : ℕ) (coldBound : cold ≤ 3)
    (hp : p ≤ 2) (hq : q ≤ 2) (hr : r ≤ 2) (hs : s ≤ 2)
    (count : 1 + cold + p + q + r + s = 10)
    (budget : 2 + 16 * cold + (4 * p - 2) + (4 * q - 2) + (8 * r - 4) + 8 * s ≤ 64) :
    cold = 1 ∧ p = 2 ∧ q = 2 ∧ r = 2 ∧ s = 2 := by
  omega

theorem thirdFullExceedsBound (c p q r s : ℕ) (hc : 16 ≤ c) (hp : 8 ≤ p) (hq : 8 ≤ q)
    (hr : 16 ≤ r) (hs : 16 ≤ s) : 64 < 2 + c + p + q + r + s := by
  omega

theorem fourthWithLink (cold pair p q missing last : ℕ)
    (coldBound : cold ≤ 3) (hpairs : pair ≤ 2)
    (h₀ : p ≤ 1) (h₁ : q ≤ 1) (h₂ : missing ≤ 1) (h₃ : last ≤ 1)
    (count : 1 + cold + pair + p + q + missing + last = 10)
    (budget : 2 + 16 * cold + 2 * pair + 4 * p + 4 * q + 2 * missing + 8 * last ≤ 64) :
    False := by omega

private def fourthPrice (cold pm qm dm p q m d : ℕ) : ℕ :=
  2 + 16 * cold + 4 * p + 4 * q + 8 * d +
    if dm = 0 then 2 * pm + 2 * qm + 4 * m
    else 4 * pm + 4 * qm + 8 * m + (if dm = 1 then 4 else 16)

theorem fourthWithoutLink (cold pm qm dm p q m d : ℕ) (coldBound : cold ≤ 3)
    (hpm : pm ≤ 1) (hqm : qm ≤ 1) (hdm : dm ≤ 2)
    (hp : p ≤ 1) (hq : q ≤ 1) (hm : m ≤ 1) (hd : d ≤ 1)
    (count : 1 + cold + pm + qm + dm + p + q + m + d = 10)
    (budget : fourthPrice cold pm qm dm p q m d ≤ 64) : False := by
  interval_cases dm <;> simp [fourthPrice] at budget <;> omega

end CrownTenCases
