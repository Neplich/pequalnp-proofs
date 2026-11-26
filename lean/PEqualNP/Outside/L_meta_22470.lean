import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22470 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33554 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let witness : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [0, 2]⟩,
      ⟨.or, [6, 3]⟩,
      ⟨.and, [1, 7]⟩,
      ⟨.and, [0, 4]⟩,
      ⟨.and, [2, 3]⟩,
      ⟨.or, [8, 9]⟩,
      ⟨.or, [11, 10]⟩], 12⟩
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  intro gate hgate
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hgate
  rcases hgate with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
