import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22532 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17293 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let witness : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [0, 1]⟩,
      ⟨.not, [6]⟩,
      ⟨.and, [3, 7]⟩,
      ⟨.and, [0, 1]⟩,
      ⟨.or, [4, 5]⟩,
      ⟨.or, [10, 8]⟩,
      ⟨.or, [11, 9]⟩,
      ⟨.not, [12]⟩], 13⟩
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  intro gate hgate
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hgate
  rcases hgate with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
