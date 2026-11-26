import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21940 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17335 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let witness : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.not, [1]⟩,
      ⟨.and, [3, 6]⟩,
      ⟨.not, [0]⟩,
      ⟨.and, [4, 8]⟩,
      ⟨.not, [0]⟩,
      ⟨.and, [5, 10]⟩,
      ⟨.or, [7, 9]⟩,
      ⟨.or, [12, 11]⟩,
      ⟨.not, [13]⟩], 14⟩
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  intro gate hgate
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hgate
  rcases hgate with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
