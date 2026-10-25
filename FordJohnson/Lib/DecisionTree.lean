import Std

namespace FordJohnson

abbrev Ranking := Nat → Nat

/-- The labels `0, …, n - 1` have distinct ranks. -/
def Distinct (n : Nat) (rank : Ranking) : Prop :=
  ∀ i, i < n → ∀ j, j < n → rank i = rank j → i = j

/-- Two rankings describe the same input order on the first `n` labels. -/
def SameOrder (n : Nat) (first second : Ranking) : Prop :=
  ∀ i, i < n → ∀ j, j < n → (first i < first j ↔ second i < second j)

/-- The first `length` labels are already a sorted chain. -/
def HasChain (length : Nat) (rank : Ranking) : Prop :=
  ∀ i j, i < j → j < length → rank i < rank j

theorem reverse_comparison {n x y : Nat} {rank : Ranking}
    (distinct : Distinct n rank) (hx : x < n) (hy : y < n)
    (different : x ≠ y) (not_less : ¬rank x < rank y) : rank y < rank x := by
  have unequal : rank x ≠ rank y := fun equal => different (distinct x hx y hy equal)
  omega

inductive DecisionTree where
  | leaf
  | compare (x y : Nat) (less greater : DecisionTree)
  deriving Inhabited

namespace DecisionTree

def height : DecisionTree → Nat
  | .leaf => 0
  | .compare _ _ less greater => max less.height greater.height + 1

def path (rank : Ranking) : DecisionTree → List Bool
  | .leaf => []
  | .compare x y less greater =>
      if rank x < rank y then true :: less.path rank else false :: greater.path rank

def labelsBelow (n : Nat) : DecisionTree → Prop
  | .leaf => True
  | .compare x y less greater =>
      x < n ∧ y < n ∧ x ≠ y ∧ less.labelsBelow n ∧ greater.labelsBelow n

theorem path_length_le_height (tree : DecisionTree) (rank : Ranking) :
    (tree.path rank).length ≤ tree.height := by
  induction tree with
  | leaf => simp [path, height]
  | compare x y less greater ihLess ihGreater =>
      simp only [path, height]
      split <;> simp only [List.length_cons]
      · exact Nat.succ_le_succ (Nat.le_trans ihLess (Nat.le_max_left _ _))
      · exact Nat.succ_le_succ (Nat.le_trans ihGreater (Nat.le_max_right _ _))

/-- Every pair of distinct input orders reaches different leaves. -/
def Separates (n : Nat) (allowed : Ranking → Prop) (tree : DecisionTree) : Prop :=
  ∀ first second, Distinct n first → Distinct n second →
    allowed first → allowed second → tree.path first = tree.path second →
    SameOrder n first second

end DecisionTree

/-- A comparison certificate for inserting `pending` elements into a chain. -/
def InsertionBound (length pending budget : Nat) : Prop :=
  ∃ tree : DecisionTree,
    tree.labelsBelow (length + pending) ∧ tree.height ≤ budget ∧
    tree.Separates (length + pending) (HasChain length)

/-- A sorting strategy with a worst-case comparison bound. -/
def SortingBound (n budget : Nat) : Prop :=
  ∃ tree : DecisionTree,
    tree.labelsBelow n ∧ tree.height ≤ budget ∧ tree.Separates n (fun _ => True)

end FordJohnson
