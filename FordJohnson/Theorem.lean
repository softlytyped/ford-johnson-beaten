import FordJohnson.Data.Certificates
import FordJohnson.Lib.ComparisonBounds

/-! The Lean formalisation was LLM-assisted. -/

namespace FordJohnson

/-- The theorem of *The Ford–Johnson algorithm, no longer unbeaten for less than 47 elements*. -/
theorem main_theorem :
    S 26 ≤ 90 ∧ S 46 ≤ 194 ∧ F 26 = 91 ∧ F 46 = 195 ∧
    ∀ n, (26 ≤ n ∧ n ≤ 32) ∨ (46 ≤ n ∧ n ≤ 64) → S n ≤ F n - 1 := by
  have at26 : S 26 ≤ 90 := calc
    S 26 ≤ S 21 + 24 := batch_insertion insert_five_into_twenty_one
    _ ≤ 66 + 24 := Nat.add_le_add_right MergeInsertion.base_bounds.1 24
    _ = 90 := rfl

  have at46 : S 46 ≤ 194 := calc
    S 46 ≤ S 42 + 23 := batch_insertion insert_four_into_forty_two
    _ ≤ 171 + 23 := Nat.add_le_add_right MergeInsertion.base_bounds.2 23
    _ = 194 := rfl

  refine ⟨at26, at46, base_counts.2.1, base_counts.2.2.2, ?_⟩
  intro n within
  rcases within with firstRange | secondRange
  · have initial : S 26 + 1 ≤ F 26 := by rw [base_counts.2.1]; omega
    have result := propagate_saving (steps := 6) initial
      (fun i hi => matching_increments (Or.inl ⟨by omega, by omega⟩))
      (n - 26) (by omega)
    simp only [Nat.add_sub_of_le firstRange.1] at result
    omega
  · have initial : S 46 + 1 ≤ F 46 := by rw [base_counts.2.2.2]; omega
    have result := propagate_saving (steps := 18) initial
      (fun i hi => matching_increments (Or.inr ⟨by omega, by omega⟩))
      (n - 46) (by omega)
    simp only [Nat.add_sub_of_le secondRange.1] at result
    omega

end FordJohnson
