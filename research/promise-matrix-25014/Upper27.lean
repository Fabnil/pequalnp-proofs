import PEqualNP.Defs

namespace PEqualNP.Outside.Promise25014

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circuit : Circuit :=
  ⟨[⟨.or, [2, 13]⟩,
      ⟨.or, [4, 9]⟩,
      ⟨.or, [7, 15]⟩,
      ⟨.or, [16, 18]⟩,
      ⟨.or, [1, 11]⟩,
      ⟨.or, [5, 8]⟩,
      ⟨.or, [0, 10]⟩,
      ⟨.or, [3, 14]⟩,
      ⟨.or, [19, 21]⟩,
      ⟨.or, [22, 24]⟩,
      ⟨.or, [6, 12]⟩,
      ⟨.or, [22, 26]⟩,
      ⟨.or, [16, 17]⟩,
      ⟨.or, [20, 28]⟩,
      ⟨.or, [17, 19]⟩,
      ⟨.or, [17, 18]⟩,
      ⟨.or, [7, 12]⟩,
      ⟨.or, [6, 15]⟩,
      ⟨.and, [23, 25]⟩,
      ⟨.and, [27, 29]⟩,
      ⟨.and, [21, 30]⟩,
      ⟨.and, [20, 31]⟩,
      ⟨.and, [32, 33]⟩,
      ⟨.or, [34, 35]⟩,
      ⟨.or, [39, 36]⟩,
      ⟨.or, [40, 37]⟩,
      ⟨.or, [41, 38]⟩], 42⟩

theorem upper27 :
    RepSizeAtMost (fun u v : Fin 8 =>
      (14500150567228511850 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  refine ⟨circuit, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.Promise25014

#print axioms PEqualNP.Outside.Promise25014.upper27
