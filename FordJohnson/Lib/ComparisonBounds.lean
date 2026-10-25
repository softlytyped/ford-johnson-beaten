import FordJohnson.Lib.Composition
import FordJohnson.Lib.MergeInsertion

namespace FordJohnson

/-- Ford–Johnson's count, using `⌈log₂(3k/4)⌉ = ceilLog2 (3*k) - 2` for `k ≥ 1`. -/
def F (n : Nat) : Nat :=
  ((List.range n).map fun i => ceilLog2 (3 * (i + 1)) - 2).sum

theorem base_counts : F 21 = 66 ∧ F 26 = 91 ∧ F 42 = 171 ∧ F 46 = 195 := by
  decide +kernel

theorem matching_increments {n : Nat}
    (within : 26 ≤ n ∧ n < 32 ∨ 46 ≤ n ∧ n < 64) :
    F (n + 1) = F n + ceilLog2 (n + 1) := by
  have table : ∀ n : Fin 65,
      (26 ≤ n.val ∧ n.val < 32 ∨ 46 ≤ n.val ∧ n.val < 64) →
      F (n.val + 1) = F n.val + ceilLog2 (n.val + 1) := by decide +kernel
  exact table ⟨n, by omega⟩ within

theorem propagate_saving {base steps : Nat} (initial : S base + 1 ≤ F base)
    (increments : ∀ i, i < steps →
      F (base + i + 1) = F (base + i) + ceilLog2 (base + i + 1)) :
    ∀ i, i ≤ steps → S (base + i) + 1 ≤ F (base + i) := by
  intro i
  induction i with
  | zero =>
      intro _
      simpa using initial
  | succ i induction =>
      intro within
      have previous := induction (by omega)
      have insertion := binary_insertion (base + i)
      have increment := increments i (by omega)
      simpa only [Nat.add_assoc] using
        (show S (base + i + 1) + 1 ≤ F (base + i + 1) by omega)

end FordJohnson
