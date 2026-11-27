import CrownBlocks

namespace CrownQuotient

open CrownThreshold

/-- Rows retain their labels. A column moves to the other group under the
    straight cross-block matching. -/
def column (v : Fin 8) : Fin 8 := Fin.ofNat 8 (v.val + 4)

def adj (u v : Fin 8) : Bool :=
  decide (u.val / 4 ≠ v.val / 4 ∧ u.val % 4 ≠ v.val % 4)

theorem column_twice (v : Fin 8) : column (column v) = v := by
  fin_cases v <;> decide

theorem adj_column (u v : Fin 8) : adj u (column v) = CrownBlocks.adj (blocks := 2) u v := by
  fin_cases u <;> fin_cases v <;> decide

/-- The original promise after the eight ORs tests every quotient pair,
    including singleton inputs and two inputs on the same quotient side. -/
theorem pairedPromise_iff (f : (Fin 8 → Bool) → Bool) :
    (∀ u v : Fin 8, f (pairInput u (column v)) = CrownBlocks.adj (blocks := 2) u v) ↔
      ∀ u v : Fin 8, f (pairInput u v) = adj u v := by
  constructor
  · intro h u v
    have result := h u (column v)
    rw [column_twice] at result
    rw [← adj_column u (column v), column_twice] at result
    exact result
  · intro h u v
    exact (h u (column v)).trans (adj_column u v)

end CrownQuotient
