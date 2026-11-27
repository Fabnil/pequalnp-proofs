import CrownForest

namespace CrownSharedCuts

open CrownRun CrownForks CrownForest PnpResearch Finset

variable {A I : Type}

def rows {A I : Type} : SharedFormula A → Samples I A → List (Cut I)
  | .tree f, s => s.rows f
  | .share f _ tail, s => s.rows f ++ rows tail (s.add f)

def extraCharge {A I : Type} : SharedFormula A → Samples I A → I → ℕ
  | .tree _, _, _ => 0
  | .share f extra tail, s, i =>
    rise (f.evalWith s.base) (f.evalWith (s.one i)) * extra + extraCharge tail (s.add f) i

theorem weightAdd (E : SharedFormula A) (u v : A → ℕ) :
    E.weight (fun a => u a + v a) = E.weight u + E.weight v := by
  induction E with
  | tree f => exact leafWeight_add f u v
  | share f _ tail ih =>
    have eq : withHead 0 (fun a => u a + v a) = fun b => withHead 0 u b + withHead 0 v b := by
      funext b
      cases b <;> simp
    simp only [SharedFormula.weight, leafWeight_add, eq, ih]
    omega

private theorem weightMul (E : SharedFormula A) (u : A → ℕ) (k : ℕ) :
    E.weight (fun a => k * u a) = k * E.weight u := by
  induction E with
  | tree f => exact leafWeight_mul f u k
  | share f _ tail ih =>
    have eq : withHead 0 (fun a => k * u a) = fun b => k * withHead 0 u b := by
      funext b
      cases b <;> simp
    simp [SharedFormula.weight, leafWeight_mul, eq, ih, Nat.mul_add]

private theorem headWeight (E : SharedFormula (Option A)) (k : ℕ) (w : A → ℕ) :
    E.weight (withHead k w) = E.weight (withHead 0 w) + k * E.weight (withHead 1 fun _ => 0) := by
  have eq : withHead k w = fun a => withHead 0 w a + k * withHead 1 (fun _ => 0) a := by
    funext a
    cases a <;> simp
  rw [eq, weightAdd, weightMul]

theorem charge (E : SharedFormula A) (s : Samples I A) (ok : E.Valid) (mono : s.onBase) (i : I) :
    degree (rows E s) i + rise (E.eval s.base) (E.eval (s.one i)) ≤ E.weight (s.riseAt i) + extraCharge E s i := by
  induction E with
  | tree f => simpa [rows, SharedFormula.eval, SharedFormula.weight, extraCharge] using s.charge mono f i
  | share f extra tail ih =>
    have h := s.charge mono f i
    have t := ih (s.add f) ok.2.1 (s.add_onBase mono f)
    rw [Samples.add_riseAt, headWeight, ok.2.2, Nat.mul_add, Nat.mul_one] at t
    simp only [rows, degree_append, SharedFormula.weight, SharedFormula.eval, extraCharge]
    change _ + rise (tail.eval (s.add f).base) (tail.eval ((s.add f).one i)) ≤ _
    omega

theorem separates (E : SharedFormula A) (s : Samples I A) (prior : List (Cut I)) (i j : I)
    (mono : s.onBase) (known : s.leafWitness prior i j)
    (on : E.eval (s.two i j) = true) (offi : E.eval (s.one i) = false) (offj : E.eval (s.one j) = false) :
    separated (prior ++ rows E s) i j := by
  induction E generalizing prior with
  | tree f => exact Samples.outputSeparates mono known f on offi offj
  | share f _ tail ih =>
    simpa only [rows, List.append_assoc] using ih (s.add f) (prior ++ s.rows f)
      (s.add_onBase mono f) (Samples.add_leafWitness mono known f) on offi offj

theorem packing [DecidableEq I] (E : SharedFormula I) (ok : E.Valid) (test : ThresholdOn E.eval)
    (S : Finset I) (limit : I → ℕ) (ceiling : ℕ)
    (bounded : ∀ i ∈ S, E.weight (fun k => (singletonInput i k).toNat) + extraCharge E (Samples.raw I) i ≤ limit i)
    (small : ∀ i ∈ S, limit i ≤ ceiling) :
    ∑ i ∈ S, 2 ^ (ceiling - limit i) ≤ 2 ^ ceiling := by
  refine CrownThreshold.weightedPacking S (rowCode (rows E (Samples.raw I))) limit ceiling ?_ ?_ small
  · intro i _ j _ ne
    apply rowCodeSeparates
    simpa only [List.nil_append] using separates E (Samples.raw I) [] i j Samples.raw_onBase
      (Samples.raw_leafWitness i j) (test.2 i j ne) (test.1 i) (test.1 j)
  · intro i hi
    rw [fixedRowCode]
    have c := charge E (Samples.raw I) ok Samples.raw_onBase i
    rw [TwoShared.raw_rises] at c
    have b := bounded i hi
    omega

end CrownSharedCuts
