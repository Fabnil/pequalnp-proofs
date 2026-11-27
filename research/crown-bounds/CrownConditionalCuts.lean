import CrownSharedCuts

namespace CrownConditionalCuts

open CrownForks PnpResearch Finset

/-- The cut inequality still holds after fixing an arbitrary common
    subassignment. Only leaves that change from that base are charged. -/
theorem packing {I A : Type} (f : Formula A) (S : Finset I) (base : A → Bool)
    (input : I → A → Bool) (limit : I → ℕ) (ceiling : ℕ)
    (below : ∀ i ∈ S, ∀ a, base a ≤ input i a)
    (off : ∀ i ∈ S, f.evalWith (input i) = false)
    (on : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → f.evalWith (fun a => input i a || input j a) = true)
    (used : ∀ i ∈ S, leafWeight f (fun a => rise (base a) (input i a)) ≤ limit i)
    (cap : ∀ i ∈ S, limit i ≤ ceiling) :
    ∑ i ∈ S, 2 ^ (ceiling - limit i) ≤ 2 ^ ceiling := by
  let lift (i : I) (a : A) := base a || input i a
  let s : Samples I A := ⟨base, lift, fun i j a => lift i a || lift j a⟩
  have lift_eq {i : I} (hi : i ∈ S) : lift i = input i := by
    funext a
    have join : ∀ x y : Bool, x ≤ y → (x || y) = y := by decide
    exact join _ _ (below i hi a)
  have mono : s.onBase := by
    intro i a
    change base a ≤ (base a || input i a)
    have le_join : ∀ x y : Bool, x ≤ (x || y) := by decide
    exact le_join _ _
  refine CrownThreshold.weightedPacking S (rowCode (s.rows f)) limit ceiling ?_ ?_ cap
  · intro i hi j hj ne
    have initial : s.leafWitness [] i j := by
      intro a yes noI noJ
      change (s.one i a || s.one j a) = true at yes
      simp [noI, noJ] at yes
    have positive : f.evalWith (s.two i j) = true := by
      change f.evalWith (fun a => lift i a || lift j a) = true
      simpa only [lift_eq hi, lift_eq hj] using on i hi j hj ne
    have negative {i : I} (hi : i ∈ S) : f.evalWith (s.one i) = false := by
      change f.evalWith (lift i) = false
      simpa only [lift_eq hi] using off i hi
    have found := Samples.outputSeparates mono initial f positive (negative hi) (negative hj)
    exact rowCodeSeparates (by simpa only [List.nil_append] using found)
  · intro i hi
    rw [fixedRowCode]
    have charge := s.charge mono f i
    have leaves :
        leafWeight f (s.riseAt i) = leafWeight f (fun a => rise (base a) (input i a)) := by
      change leafWeight f (fun a => rise (base a) (lift i a)) = _
      rw [lift_eq hi]
    rw [leaves] at charge
    exact (Nat.le_add_right ..).trans (charge.trans (used i hi))

end CrownConditionalCuts
