import PEqualNP.Defs
import Std.Tactic.BVDecide

namespace LeafWheelAndCount

/-- A disjunction of raw inputs and earlier AND or NOT outputs. -/
structure Disjunction where
  inputs : BitVec 8
  earlier : BitVec 3

private def Disjunction.eval (d : Disjunction) (x : BitVec 8) (a b c : Bool) : Bool :=
  ((x &&& d.inputs) != 0) || (d.earlier.getLsbD 0 && a) ||
    (d.earlier.getLsbD 1 && b) || (d.earlier.getLsbD 2 && c)

structure Skeleton where
  left0 : Disjunction
  right0 : Disjunction
  left1 : Disjunction
  right1 : Disjunction
  left2 : Disjunction
  right2 : Disjunction
  left3 : Disjunction
  right3 : Disjunction
  output : BitVec 4

private def operation (notGate left right : Bool) : Bool :=
  if notGate then !left else left && right

/-- Evaluate a circuit after expanding all ORs into disjunctions on earlier signals. -/
def Skeleton.eval (s : Skeleton) (negation : Fin 4) (x : BitVec 8) : Bool :=
  let a := operation (negation.val == 0) (s.left0.eval x false false false)
    (s.right0.eval x false false false)
  let b := operation (negation.val == 1) (s.left1.eval x a false false)
    (s.right1.eval x a false false)
  let c := operation (negation.val == 2) (s.left2.eval x a b false)
    (s.right2.eval x a b false)
  let d := operation (negation.val == 3) (s.left3.eval x a b c) (s.right3.eval x a b c)
  (s.output.getLsbD 0 && a) || (s.output.getLsbD 1 && b) ||
    (s.output.getLsbD 2 && c) || (s.output.getLsbD 3 && d)

private def contains (x edge : BitVec 8) : Bool := (x &&& edge) == edge

def target (x : BitVec 8) : Bool :=
  contains x 17 || contains x 18 || contains x 33 || contains x 36 ||
  contains x 66 || contains x 72 || contains x 96 || contains x 129 ||
  contains x 130 || contains x 144 || contains x 160 || contains x 192

private def rows : Fin 4 → List ℕ
  | 0 => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
      16, 17, 18, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32,
      33, 34, 35, 36, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 50,
      52, 54, 55, 56, 58, 60, 61, 62, 63, 64, 65, 66, 68, 69, 70, 71,
      72, 73, 74, 76, 77, 79, 80, 81, 84, 85, 86, 88, 90, 92, 93, 95,
      105, 107, 120, 124, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139,
      140, 141, 142, 143, 144, 148, 149, 152, 155, 156, 158, 160, 164, 168, 172, 174,
      189, 196]
  | 1 => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
      16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
      32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 46, 47, 48,
      49, 50, 52, 53, 56, 57, 58, 60, 64, 65, 66, 67, 68, 69, 70, 71,
      72, 73, 75, 76, 77, 78, 79, 80, 81, 82, 84, 85, 86, 88, 89, 92,
      96, 98, 102, 104, 106, 112, 120, 128, 129, 130, 132, 133, 134, 135, 136, 137,
      138, 139, 140, 141, 142, 143, 144, 148, 152, 156, 188, 193, 196, 203]
  | 2 => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
      16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 28, 29, 30, 32, 33,
      34, 35, 36, 37, 38, 40, 41, 42, 43, 44, 45, 46, 48, 49, 50, 52,
      53, 54, 56, 57, 58, 60, 62, 64, 65, 66, 67, 68, 69, 70, 71, 72,
      73, 75, 76, 77, 78, 79, 80, 81, 84, 85, 88, 89, 92, 96, 100, 101,
      112, 116, 128, 129, 130, 131, 132, 133, 134, 136, 137, 138, 140, 141, 142, 143,
      144, 148, 152, 156, 160, 168, 176, 184, 191, 192, 193, 196, 197, 212]
  | 3 => [8, 15, 16, 18, 28, 32, 33, 34, 36, 40, 65, 72, 80, 128, 129, 132,
      144, 192]

private def agrees (s : Skeleton) (negation : Fin 4) : Bool :=
  (rows negation).all fun y => s.eval negation (BitVec.ofNat 8 y) == target (BitVec.ofNat 8 y)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 5000000 in
private theorem invalid (s : Skeleton) (negation : Fin 4) : agrees s negation = false := by
  rcases s with ⟨⟨a0, b0⟩, ⟨c0, d0⟩, ⟨a1, b1⟩, ⟨c1, d1⟩,
    ⟨a2, b2⟩, ⟨c2, d2⟩, ⟨a3, b3⟩, ⟨c3, d3⟩, out⟩
  fin_cases negation <;>
    simp (config := { maxSteps := 2000000 }) only [agrees, rows, Skeleton.eval, Disjunction.eval,
      operation, target, contains, List.all_cons, List.all_nil, Bool.and_false, Bool.false_and,
      Bool.or_false, Bool.false_or] <;>
    bv_decide

/-- Three AND outputs and one NOT output cannot realize the edge function. -/
theorem noSkeleton (s : Skeleton) (negation : Fin 4) :
    ¬ ∀ x, s.eval negation x = target x := by
  intro correct
  have pass : agrees s negation = true := List.all_eq_true.mpr (fun y _ => by simp [correct])
  rw [invalid] at pass
  contradiction

end LeafWheelAndCount
