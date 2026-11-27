import CrownFourGroups

namespace CrownOrProfiles

def flags : List ℕ := [0, 1, 2, 3]

def pairs : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

def successors (graph : ℕ) (node : ℕ) : List ℕ :=
  (pairs.zipIdx.filter fun (e, k) => e.1 = node && graph.testBit k).map fun (e, _) => e.2

def closure (graph roots : ℕ) : ℕ :=
  (pairs.zipIdx).foldl (fun mask (edge, index) =>
    if graph.testBit index && mask.testBit edge.1 then mask ||| (1 <<< edge.2) else mask) roots

def includes (larger smaller : ℕ) : Bool := larger &&& smaller == smaller

def incomparable (x y : ℕ) : Bool :=
  !(includes x y || includes y x)

def antichain : List ℕ → Bool
  | [] => true
  | x :: rest => rest.all (incomparable x) && antichain rest

def waysToStart (pairMask : ℕ) : List (ℕ × ℕ) :=
  ((pairs.zipIdx).filter fun (_, k) => pairMask.testBit k).map Prod.fst

def hiddenProfiles (graph pairMask : ℕ) : List ℕ :=
  (waysToStart pairMask).map fun (i, j) => closure graph ((1 <<< i) ||| (1 <<< j))

def repeatedProfiles (graph repeatMask : ℕ) : List ℕ :=
  (flags.filter repeatMask.testBit).map fun k => closure graph (1 <<< k)

def legal (graph pairMask repeatMask : ℕ) : Bool :=
  let hidden := hiddenProfiles graph pairMask
  let repeated := repeatedProfiles graph repeatMask
  flags.all (fun k => (successors graph k).length ≤ 2) &&
  (waysToStart pairMask).all (fun (i, j) =>
    incomparable (closure graph (1 <<< i)) (closure graph (1 <<< j))) &&
  antichain (hidden ++ repeated)

def outputReads (graph profile : ℕ) : ℕ :=
  ((flags.filter profile.testBit).map (fun k => 2 - (successors graph k).length)).sum

def price (graph profile rawReads : ℕ) : ℕ :=
  2 ^ (10 - (rawReads + outputReads graph profile))

def mandatoryCount (graph pairMask repeatMask : ℕ) : ℕ :=
  (hiddenProfiles graph pairMask).length + 2 * (repeatedProfiles graph repeatMask).length

def mandatoryCost (graph pairMask repeatMask : ℕ) : ℕ :=
  ((hiddenProfiles graph pairMask).map (fun mask => price graph mask 0)).sum +
    2 * ((repeatedProfiles graph repeatMask).map (fun mask => price graph mask 1)).sum

def optionalCosts (graph pairMask repeatMask : ℕ) : List ℕ :=
  let forbidden := hiddenProfiles graph pairMask ++ repeatedProfiles graph repeatMask
  let allowed := flags.filter fun k =>
    !repeatMask.testBit k && !(forbidden.any (includes (closure graph (1 <<< k))))
  [256, 256, 256] ++ allowed.map fun k => price graph (closure graph (1 <<< k)) 1

private def minCost : List ℕ → ℕ → ℕ
  | _, 0 => 0
  | [], _ + 1 => 1025
  | w :: ws, k + 1 => min (minCost ws (k + 1)) (w + minCost ws k)

private theorem minCost_le_sublist {chosen candidates : List ℕ} (sub : chosen.Sublist candidates) :
    minCost candidates chosen.length ≤ chosen.sum := by
  induction sub with
  | slnil => decide
  | @cons l₁ l₂ w _ ih =>
    cases l₁ with
    | nil => exact le_rfl
    | cons v vs =>
      change min (minCost l₂ (vs.length + 1)) (w + minCost l₂ vs.length) ≤ _
      exact le_trans (min_le_left _ _) ih
  | @cons_cons l₁ l₂ w _ ih =>
    change min (minCost l₂ (l₁.length + 1)) (w + minCost l₂ l₁.length) ≤ w + l₁.sum
    exact le_trans (min_le_right _ _) (Nat.add_le_add_left ih w)

private def impossible (graph pairMask repeatMask : ℕ) : Bool :=
  if legal graph pairMask repeatMask then
    mandatoryCost graph pairMask repeatMask +
      minCost (optionalCosts graph pairMask repeatMask) (10 - mandatoryCount graph pairMask repeatMask) > 1024
  else true

private def checked (graph : ℕ) : Bool :=
  (List.range 64).all fun pairs => (List.range 16).all fun reps => impossible graph pairs reps

/- Reduce bounded groups of graphs independently to keep certificate checking
   within the memory limit of a local Lean build. -/
section
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

private theorem checked_0 : ∀ g : Fin 8, g.val ≠ 0 → checked g.val = true := by decide +kernel

private theorem checked_1 : ∀ g : Fin 8, checked (g.val + 8) = true := by decide +kernel

private theorem checked_2 : ∀ g : Fin 8, checked (g.val + 16) = true := by decide +kernel

private theorem checked_3 : ∀ g : Fin 8, checked (g.val + 24) = true := by decide +kernel

private theorem checked_4 : ∀ g : Fin 8, checked (g.val + 32) = true := by decide +kernel

private theorem checked_5 : ∀ g : Fin 8, checked (g.val + 40) = true := by decide +kernel

private theorem checked_6 : ∀ g : Fin 8, checked (g.val + 48) = true := by decide +kernel

private theorem checked_7 : ∀ g : Fin 8, checked (g.val + 56) = true := by decide +kernel

end

private theorem checked_nonempty (graph : Fin 64) (nonzero : graph.val ≠ 0) :
    checked graph.val = true := by
  let r : Fin 8 := ⟨graph.val % 8, Nat.mod_lt _ (by decide)⟩
  generalize eq : graph.val / 8 = q
  have size := graph.isLt
  have within : q < 8 := by omega
  have reconstruct : r.val + 8 * q = graph.val := by
    rw [← eq]
    exact Nat.mod_add_div _ _
  interval_cases q
  · have eq' : r.val = graph.val := by simpa only [Nat.mul_zero, Nat.add_zero] using reconstruct
    exact eq' ▸ checked_0 r (fun h => nonzero (eq'.symm.trans h))
  · have eq' : r.val + 8 = graph.val := reconstruct
    exact eq' ▸ checked_1 r
  · have eq' : r.val + 16 = graph.val := reconstruct
    exact eq' ▸ checked_2 r
  · have eq' : r.val + 24 = graph.val := reconstruct
    exact eq' ▸ checked_3 r
  · have eq' : r.val + 32 = graph.val := reconstruct
    exact eq' ▸ checked_4 r
  · have eq' : r.val + 40 = graph.val := reconstruct
    exact eq' ▸ checked_5 r
  · have eq' : r.val + 48 = graph.val := reconstruct
    exact eq' ▸ checked_6 r
  · have eq' : r.val + 56 = graph.val := reconstruct
    exact eq' ▸ checked_7 r

/-- A connection between two of the four OR groups leaves too little cut weight
    for ten inputs. Optional entries are the cold inputs and unrepeated singletons. -/
theorem noTenWithConnection (graph pairMask : Fin 64) (repeatMask : Fin 16)
    (nonempty : graph.val ≠ 0) (allowed : legal graph.val pairMask.val repeatMask.val = true)
    (chosen : List ℕ) (sub : chosen.Sublist (optionalCosts graph.val pairMask.val repeatMask.val))
    (ten : mandatoryCount graph.val pairMask.val repeatMask.val + chosen.length = 10)
    (budget : mandatoryCost graph.val pairMask.val repeatMask.val + chosen.sum ≤ 1024) : False := by
  have h := checked_nonempty graph nonempty
  unfold checked at h
  have hPair := List.all_eq_true.mp h pairMask.val (List.mem_range.mpr pairMask.isLt)
  have hRepeat := List.all_eq_true.mp hPair repeatMask.val (List.mem_range.mpr repeatMask.isLt)
  unfold impossible at hRepeat
  rw [ite_eq_left allowed] at hRepeat
  have enough := of_decide_eq_true hRepeat
  have cost := minCost_le_sublist sub
  rw [show 10 - mandatoryCount graph.val pairMask.val repeatMask.val = chosen.length by omega] at enough
  omega

end CrownOrProfiles
