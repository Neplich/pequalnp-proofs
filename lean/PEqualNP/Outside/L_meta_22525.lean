import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22525 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16513 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let witness : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [1, 2]⟩,
      ⟨.and, [0, 6]⟩,
      ⟨.and, [1, 2]⟩,
      ⟨.or, [3, 4]⟩,
      ⟨.or, [9, 5]⟩,
      ⟨.or, [10, 7]⟩,
      ⟨.or, [11, 8]⟩,
      ⟨.not, [12]⟩], 13⟩
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  intro gate hgate
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hgate
  rcases hgate with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
