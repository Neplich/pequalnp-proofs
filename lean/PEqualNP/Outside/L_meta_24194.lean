import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24194 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4377535 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let witness : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.and, [3, 4]⟩,
      ⟨.not, [4]⟩,
      ⟨.or, [1, 2]⟩,
      ⟨.and, [7, 8]⟩,
      ⟨.or, [6, 9]⟩,
      ⟨.or, [0, 10]⟩], 11⟩
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  intro gate hgate
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hgate
  rcases hgate with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
