import FordJohnson.Lib.BinaryInsertion

namespace FordJohnson

private theorem same_order_of_sorted {xs : List (Fin n)}
    (covers : ∀ i, i ∈ xs) {first second : Ranking}
    (distinctFirst : Distinct n first) (distinctSecond : Distinct n second)
    (sortedFirst : Sorted id xs first) (sortedSecond : Sorted id xs second) :
    SameOrder n first second := by
  have transfer (a b : Ranking) (distinct : Distinct n b)
      (sortedA : Sorted id xs a) (sortedB : Sorted id xs b)
      (i j : Fin n) (less : a i < a j) : b i < b j := by
    obtain ⟨p, hp, pi⟩ := List.getElem_of_mem (covers i)
    obtain ⟨q, hq, qj⟩ := List.getElem_of_mem (covers j)
    have positions : p < q := by
      by_cases equal : p = q
      · subst q; rw [← pi, ← qj] at less; omega
      · by_cases forward : p < q
        · exact forward
        · have := List.pairwise_iff_getElem.mp sortedA q p hq hp (by omega)
          simp only [id_eq, pi, qj] at this
          omega
    have ordered := List.pairwise_iff_getElem.mp sortedB p q hp hq positions
    simp only [id_eq, pi, qj] at ordered
    have different : b i ≠ b j := by
      intro equal
      have labels := distinct i i.isLt j j.isLt equal
      have := congrArg a labels
      omega
    omega
  intro i hi j hj
  exact ⟨transfer first second distinctSecond sortedFirst sortedSecond ⟨i, hi⟩ ⟨j, hj⟩,
    transfer second first distinctFirst sortedSecond sortedFirst ⟨i, hi⟩ ⟨j, hj⟩⟩

theorem decisionTree_of_computes
    (computation : Computes n (fun rank => Distinct n rank ∧ allowed rank) budget
      (SortResult id (List.finRange n))) :
    ∃ tree : DecisionTree, tree.labelsBelow n ∧ tree.height ≤ budget ∧ tree.Separates n allowed := by
  obtain ⟨tree, height, correct⟩ := computation
  refine ⟨tree.erase, tree.erase_valid.1, Nat.le_trans tree.erase_valid.2 height, ?_⟩
  intro first second distinctFirst distinctSecond allowedFirst allowedSecond samePath
  have firstResult := correct first ⟨distinctFirst, allowedFirst⟩
  have secondResult := correct second ⟨distinctSecond, allowedSecond⟩
  rw [← tree.run_eq_of_path_eq samePath] at secondResult
  exact same_order_of_sorted
    (fun i => firstResult.1.mem_iff.mpr (List.mem_finRange i))
    distinctFirst distinctSecond firstResult.2 secondResult.2

theorem sortingBound_of_computes
    (computation : Computes n (Distinct n) budget (SortResult id (List.finRange n))) :
    SortingBound n budget :=
  decisionTree_of_computes (computation.weaken (fun _ h => h.1)
    (Nat.le_refl _) (fun _ _ _ h => h))

namespace DecisionTree

def withResults (tree : DecisionTree) (valid : tree.labelsBelow n)
    (result : List Bool → α) : Program n α :=
  match tree with
  | .leaf => .pure (result [])
  | .compare x y less greater =>
      .compare ⟨x, valid.1⟩ ⟨y, valid.2.1⟩
        (less.withResults valid.2.2.2.1 (fun path => result (true :: path)))
        (greater.withResults valid.2.2.2.2 (fun path => result (false :: path)))

theorem withResults_height (tree : DecisionTree) (valid : tree.labelsBelow n)
    (result : List Bool → α) : (tree.withResults valid result).height = tree.height := by
  induction tree generalizing result <;> simp_all [withResults, Program.height, height]

theorem withResults_run (tree : DecisionTree) (valid : tree.labelsBelow n)
    (result : List Bool → α) (rank : Ranking) :
    (tree.withResults valid result).run rank = result (tree.path rank) := by
  induction tree generalizing result <;> simp_all [withResults, Program.run, path]
  split <;> simp_all

theorem computes_of_separates (tree : DecisionTree) (valid : tree.labelsBelow n)
    (separates : tree.Separates n allowed) :
    Computes n (fun rank => Distinct n rank ∧ allowed rank) tree.height
      (SortResult id (List.finRange n)) := by
  classical
  let possible path := ∃ rank, Distinct n rank ∧ allowed rank ∧ tree.path rank = path
  let representative path : Ranking := if h : possible path then h.choose else id
  let result path := (List.finRange n).mergeSort
    (fun i j => decide (representative path i ≤ representative path j))
  refine ⟨tree.withResults valid result, by rw [withResults_height]; exact Nat.le_refl _, ?_⟩
  intro rank h
  rw [withResults_run]
  have existsRank : possible (tree.path rank) := ⟨rank, h.1, h.2, rfl⟩
  have sample : Distinct n (representative (tree.path rank)) ∧
      allowed (representative (tree.path rank)) ∧
      tree.path (representative (tree.path rank)) = tree.path rank := by
    simpa only [representative, dif_pos existsRank] using existsRank.choose_spec
  have same := separates rank (representative (tree.path rank)) h.1 sample.1 h.2 sample.2.1
    sample.2.2.symm
  refine ⟨List.mergeSort_perm _ _, ?_⟩
  have ordered := List.pairwise_mergeSort
    (le := fun i j : Fin n => decide (representative (tree.path rank) i ≤ representative (tree.path rank) j))
    (by intro a b c; simp only [decide_eq_true_eq]; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) (List.finRange n)
  apply ordered.imp
  intro i j bound
  simp only [decide_eq_true_eq] at bound
  have reversed := same j j.isLt i i.isLt
  change rank i ≤ rank j
  omega

end DecisionTree

theorem SortingBound.computes (bound : SortingBound n budget) :
    Computes n (Distinct n) budget (SortResult id (List.finRange n)) := by
  obtain ⟨tree, valid, height, separates⟩ := bound
  exact (tree.computes_of_separates valid separates).weaken
    (fun _ h => ⟨h, True.intro⟩) height (fun _ _ _ h => h)

private theorem sorting_exists (key : α → Fin n) (xs : List α) :
    ∃ budget, Computes n (fun _ => True) budget (SortResult key xs) := by
  induction xs with
  | nil => exact ⟨0, Computes.pure [] (by simp [SortResult, Sorted])⟩
  | cons x xs ih =>
      obtain ⟨budget, sortTail⟩ := ih
      refine ⟨budget + ceilLog2 (xs.length + 1), sortTail.bind fun ys => ?_⟩
      apply Computes.of_nonempty_precondition
      rintro ⟨_, permutation, _⟩
      have length := permutation.length_eq
      have capacity := le_two_pow_ceilLog2 (xs.length + 1)
      exact (BinaryInsertion.insert key x ys ys.length (ceilLog2 (xs.length + 1))
        (Nat.le_refl _) (by omega)).weaken
        (fun _ h => ⟨h.2, by intro i hi after; omega⟩) (Nat.le_refl _)
        (fun _ _ h result => ⟨result.1.1.trans (h.1.cons x), result.1.2⟩)

theorem exists_sortingBound (n : Nat) : ∃ budget, SortingBound n budget := by
  obtain ⟨budget, computation⟩ := sorting_exists (n := n) id (List.finRange n)
  exact ⟨budget, sortingBound_of_computes (computation.weaken
    (fun _ _ => True.intro) (Nat.le_refl _) (fun _ _ _ h => h))⟩

private theorem least_exists {P : Nat → Prop} (existsValue : ∃ value, P value) :
    ∃ least, P least ∧ ∀ value, P value → least ≤ value := by
  classical
  obtain ⟨value, holds⟩ := existsValue
  induction value using Nat.strongRecOn with
  | ind value ih =>
      by_cases smaller : ∃ other, other < value ∧ P other
      · obtain ⟨other, less, holds⟩ := smaller
        exact ih other less holds
      · exact ⟨value, holds, fun other h =>
          Nat.le_of_not_gt (fun less => smaller ⟨other, less, h⟩)⟩

/-- The least worst-case number of comparisons needed to sort `n` distinct elements. -/
noncomputable def S (n : Nat) : Nat :=
  (least_exists (exists_sortingBound n)).choose

theorem S_spec (n : Nat) : SortingBound n (S n) :=
  (least_exists (exists_sortingBound n)).choose_spec.1

theorem S_le (bound : SortingBound n budget) : S n ≤ budget :=
  (least_exists (exists_sortingBound n)).choose_spec.2 budget bound

end FordJohnson
