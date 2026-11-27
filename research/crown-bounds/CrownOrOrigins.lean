import CrownOrGraph

namespace CrownOrOrigins

open CrownForks CrownFourNetwork CrownFourNormal CrownAllOrModel CrownOrSupport CrownOrGraph
open CrownPairFormula Finset

/-- The order of the six forward pairs in the finite certificate. -/
def endpoints (k : Fin 6) : Fin 4 × Fin 4 :=
  match k.val with
  | 0 => (0, 1)
  | 1 => (0, 2)
  | 2 => (0, 3)
  | 3 => (1, 2)
  | 4 => (1, 3)
  | _ => (2, 3)

def maskSupport (r : Fin 16) : Finset Flag :=
  univ.filter (fun k => r.val.testBit (stage k).val = true)

@[simp] theorem mem_maskSupport (r : Fin 16) (k : Flag) :
    k ∈ maskSupport r ↔ r.val.testBit (stage k).val = true := by simp [maskSupport]

private theorem singleton_range : ∀ t : Fin 4, (1 <<< t.val) < 16 := by decide +kernel

def singletonSeed (t : Fin 4) : Fin 16 := ⟨1 <<< t.val, singleton_range t⟩

private theorem pair_range : ∀ k : Fin 6,
    ((1 <<< (endpoints k).1.val) ||| (1 <<< (endpoints k).2.val)) < 16 := by decide +kernel

def pairSeed (k : Fin 6) : Fin 16 :=
  ⟨(1 <<< (endpoints k).1.val) ||| (1 <<< (endpoints k).2.val), pair_range k⟩

inductive Origin where
  | cold
  | single (t : Fin 4)
  | pair (k : Fin 6)
  deriving DecidableEq

def Origin.seed : Origin → Fin 16
  | .cold => 0
  | .single t => singletonSeed t
  | .pair k => pairSeed k

def Origin.count : Origin → ℕ
  | .cold => 0
  | .single _ => 1
  | .pair _ => 2

def close (g : Fin 64) (s : Origin) : ℕ :=
  CrownOrProfiles.closure g.val s.seed.val

private def candidates : List Origin :=
  .cold :: ((List.finRange 4).map Origin.single ++ (List.finRange 6).map Origin.pair)

/-- Prefer the smallest direct reader set that gives the same profile. -/
def chooseOrigin (g : Fin 64) (r : Fin 16) : Origin :=
  (candidates.find? fun s => CrownOrProfiles.includes r.val s.seed.val &&
    decide (close g s = CrownOrProfiles.closure g.val r.val)).getD .cold

def incomparableSources (g : Fin 64) (k : Fin 6) : Prop :=
  CrownOrProfiles.includes (close g (.single (endpoints k).1)) (close g (.single (endpoints k).2)) = false ∧
  CrownOrProfiles.includes (close g (.single (endpoints k).2)) (close g (.single (endpoints k).1)) = false

private def legalOrigin (g : Fin 64) : Origin → Bool
  | .cold | .single _ => true
  | .pair k =>
    !(CrownOrProfiles.includes (close g (.single (endpoints k).1)) (close g (.single (endpoints k).2)) ||
      CrownOrProfiles.includes (close g (.single (endpoints k).2)) (close g (.single (endpoints k).1)))

set_option maxHeartbeats 1200000 in
private theorem choose_computed : ∀ (g : Fin 64) (r : Fin 16), (maskSupport r).card ≤ 2 →
    close g (chooseOrigin g r) = CrownOrProfiles.closure g.val r.val ∧
    (chooseOrigin g r).count ≤ (maskSupport r).card ∧ legalOrigin g (chooseOrigin g r) = true := by
  decide +kernel

theorem chosen_pair_incomparable {g : Fin 64} {r : Fin 16} {k : Fin 6}
    (bound : (maskSupport r).card ≤ 2) (isPair : chooseOrigin g r = .pair k) : incomparableSources g k := by
  have legal := (choose_computed g r bound).2.2
  rw [isPair] at legal
  simpa only [legalOrigin, Bool.not_eq_true', Bool.or_eq_false_iff, incomparableSources] using legal

theorem cold_closure : ∀ g : Fin 64, close g .cold = 0 := by decide +kernel

theorem single_nonzero : ∀ (g : Fin 64) (t : Fin 4), close g (.single t) ≠ 0 := by decide +kernel

variable {I : Type} [DecidableEq I]

theorem mask_readers (N : Network I) (i : I) : maskSupport (roots N i) = readers N i := by
  ext k
  simp only [mem_maskSupport, roots_bits, starts, decide_eq_true_eq, mem_readers]

theorem mask_support (N : Network I) (i : I) : maskSupport (actual N i) = support N i := by
  ext k
  simp only [mem_maskSupport, actual_bits, activeBit, mem_support, flagValues]

def origin (N : Network I) (i : I) : Origin := chooseOrigin (graph N) (roots N i)

variable {N : Network Ten}

private theorem seeds_small (C : Case N) (i : Ten) : (maskSupport (roots N i)).card ≤ 2 := by
  rw [mask_readers]
  exact (Nat.le_add_right ..).trans (C.read_bound i)

theorem realized (C : Case N) (i : Ten) : (actual N i).val = close (graph N) (origin N i) :=
  (actual_eq_closure C i).trans (choose_computed _ _ (seeds_small C i)).1.symm

theorem read_bound (C : Case N) (i : Ten) : (origin N i).count + reads (output N) (.inr i) ≤ 2 := by
  have bound := (choose_computed (graph N) (roots N i) (seeds_small C i)).2.1
  rw [mask_readers] at bound
  exact (Nat.add_le_add_right bound _).trans (C.read_bound i)

theorem pair_incomparable (C : Case N) {i : Ten} {k : Fin 6} (pair : origin N i = .pair k) :
    incomparableSources (graph N) k :=
  chosen_pair_incomparable (seeds_small C i) pair

theorem support_of_same (C : Case N) {i j : Ten} (same : origin N i = origin N j) :
    support N i = support N j := by
  have equal : actual N i = actual N j := Fin.ext ((realized C i).trans (by rw [same, ← realized C j]))
  rw [← mask_support N i, ← mask_support N j, equal]

end CrownOrOrigins
