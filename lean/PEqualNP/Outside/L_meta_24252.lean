import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24252 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (909 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let witness : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [0, 1]⟩,
      ⟨.and, [0, 1]⟩,
      ⟨.or, [5, 7]⟩,
      ⟨.or, [4, 8]⟩,
      ⟨.not, [9]⟩,
      ⟨.and, [6, 10]⟩], 11⟩
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  intro gate hgate
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hgate
  rcases hgate with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
