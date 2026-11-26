import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21974 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (393 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let witness : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.not, [1]⟩,
      ⟨.and, [2, 6]⟩,
      ⟨.not, [0]⟩,
      ⟨.and, [3, 8]⟩,
      ⟨.and, [0, 1]⟩,
      ⟨.or, [4, 5]⟩,
      ⟨.or, [11, 7]⟩,
      ⟨.or, [12, 9]⟩,
      ⟨.or, [13, 10]⟩,
      ⟨.not, [14]⟩], 15⟩
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  intro gate hgate
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hgate
  rcases hgate with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
