import FordJohnson.Lib.Sorting

namespace FordJohnson.MergeInsertion

def Paired (key : α → Fin n) (xs : List α) (pairs : List (α × α) × List α)
    (rank : Ranking) : Prop :=
  pairs.1.length = xs.length / 2 ∧ pairs.2.length = xs.length % 2 ∧
  (pairs.1.flatMap (fun pair => [pair.1, pair.2]) ++ pairs.2).Perm xs ∧
  ∀ pair ∈ pairs.1, rank (key pair.1) ≤ rank (key pair.2)

theorem pair (key : α → Fin n) : ∀ xs : List α,
    Computes n (fun _ => True) (xs.length / 2) (Paired key xs)
  | [] => by
      simp only [List.length_nil, Nat.zero_div]
      exact Computes.pure ([], []) (by intro rank h; simp [Paired])
  | [x] => by
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceDiv]
      exact Computes.pure ([], [x]) (by intro rank h; simp [Paired])
  | x :: y :: xs => by
      have comparePair : Computes n (fun _ => True) 1
          (fun p : α × α => fun rank => [p.1, p.2].Perm [x, y] ∧
            rank (key p.1) ≤ rank (key p.2)) := by
        apply Computes.branch (key x) (key y)
        · exact Computes.pure (x, y) (fun _ h => ⟨List.Perm.refl _, Nat.le_of_lt h.2⟩)
        · exact Computes.pure (y, x) (fun _ h => ⟨List.Perm.swap _ _ _, by dsimp; omega⟩)
      apply (comparePair.bind (nextCost := xs.length / 2) (fun p => ?_)).weaken
        (fun _ h => h) (by simp; omega) (fun _ _ _ h => h)
      exact ((pair key xs).frame (fun rank => [p.1, p.2].Perm [x, y] ∧
        rank (key p.1) ≤ rank (key p.2))).map
        (fun rest => (p :: rest.1, rest.2))
        (by
          intro rest rank _ h
          obtain ⟨⟨permutation, ordered⟩, lengthPairs, lengthExtra, contents, bounds⟩ := h
          refine ⟨by simp only [List.length_cons] at *; omega, ?_, ?_, ?_⟩
          · simp only [List.length_cons]; omega
          · simpa using permutation.append contents
          · intro p' member
            rcases List.mem_cons.mp member with rfl | member
            · exact ordered
            · exact bounds p' member)
        |>.weaken (fun _ h => ⟨h, True.intro⟩) (Nat.le_refl _) (fun _ _ _ h => h)

/-- Jacobsthal insertion order for the sizes used in this proof. -/
def insertionOrder (pending : Nat) : List Nat :=
  [0, 2, 1, 4, 3, 10, 9, 8, 7, 6, 5, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11].filter (· < pending)

theorem insertionOrder_perm {pending : Nat} (within : pending ≤ 21) :
    (insertionOrder pending).Perm (List.range pending) := by
  have table : ∀ pending : Fin 22,
      (insertionOrder pending).Perm (List.range pending) := by decide +kernel
  exact table ⟨pending, by omega⟩

def insertionCost (inserted : Nat) : List Nat → Nat
  | [] => 0
  | i :: rest => ceilLog2 (i + inserted + 1) + insertionCost (inserted + 1) rest

def cost (size : Nat) : Nat :=
  if size < 2 then 0 else
    size / 2 + cost (size / 2) + insertionCost 0 (insertionOrder (size - size / 2))
termination_by size
decreasing_by omega

private theorem index_le [DecidableEq α] (xs : List α) {i : Nat} (within : i < xs.length) :
    xs.idxOf xs[i] ≤ i := by
  induction xs generalizing i with
  | nil => simp at within
  | cons x xs ih =>
      cases i with
      | zero => simp
      | succ i =>
          simp only [List.getElem_cons_succ, List.idxOf_cons, cond_eq_ite, beq_iff_eq]
          split
          · exact Nat.zero_le _
          · have := ih (by simpa using within)
            omega

private theorem index_growth [DecidableEq α] {xs ys : List α} (sublist : xs.Sublist ys) :
    x ∈ xs → ys.idxOf x + xs.length ≤ xs.idxOf x + ys.length := by
  induction sublist with
  | slnil => simp
  | cons y sublist ih =>
      intro member
      have := ih member
      have := sublist.length_le
      simp only [List.idxOf_cons, List.length_cons, cond_eq_ite, beq_iff_eq]
      split <;> omega
  | cons_cons y sublist ih =>
      intro member
      by_cases equal : y = x
      · subst y
        simpa using sublist.length_le
      · have := ih (by simpa [equal, Ne.symm equal] using member)
        simp only [List.idxOf_cons, List.length_cons, cond_eq_ite, beq_iff_eq,
          if_neg equal]
        omega

def Below (key : α → Fin n) (pending maxima : List α) (rank : Ranking) : Prop :=
  ∀ i, (hp : i < pending.length) → (hm : i < maxima.length) →
    rank (key pending[i]) ≤ rank (key maxima[i])

theorem insert_pending (key : α → Fin n) (pending maxima : List α)
    (indices : List Nat) (valid : ∀ i ∈ indices, i < pending.length)
    (chain : List α) (inserted : Nat) (sublist : maxima.Sublist chain)
    (length : chain.length = maxima.length + inserted) :
    Computes n (fun rank => Below key pending maxima rank ∧ Sorted key chain rank)
      (insertionCost inserted indices)
      (SortResult key (indices.attach.map (fun i => pending[i.val]'(valid i.val i.property)) ++ chain)) := by
  classical
  induction indices generalizing chain inserted with
  | nil => exact Computes.pure chain (fun _ h => ⟨by simp, h.2⟩)
  | cons i indices ih =>
      have pendingIndex := valid i (by simp)
      let position := if h : i < maxima.length then chain.idxOf maxima[i] else chain.length
      have within : position ≤ chain.length := by
        dsimp [position]; split
        · exact List.idxOf_le_length
        · exact Nat.le_refl _
      have bounded : position ≤ i + inserted := by
        dsimp [position]; split
        next h =>
          have := index_growth sublist (List.getElem_mem h)
          have := index_le maxima h
          omega
        next h => omega
      have capacity := le_two_pow_ceilLog2 (i + inserted + 1)
      have insertion := (BinaryInsertion.insert key pending[i] chain position
        (ceilLog2 (i + inserted + 1)) within (by omega)).frame (Below key pending maxima)
      have step := insertion.weaken
        (before' := fun rank => Below key pending maxima rank ∧ Sorted key chain rank)
        (fun rank h => by
          refine ⟨h.1, h.2, ?_⟩
          intro j hj after
          dsimp [position] at after
          split at after
          next hm =>
            have anchor := List.idxOf_lt_length_of_mem (sublist.subset (List.getElem_mem hm))
            have identity := List.getElem_idxOf (xs := chain) anchor
            have bound := h.1 i pendingIndex hm
            by_cases equal : chain.idxOf maxima[i] = j
            · subst j; simpa [identity] using bound
            · have ordered := List.pairwise_iff_getElem.mp h.2 _ j anchor hj (by omega)
              rw [identity] at ordered
              exact Nat.le_trans bound ordered
          next => omega)
        (Nat.le_refl _) (fun _ _ _ h => h)
      apply step.bind
      intro next
      apply Computes.of_nonempty_precondition
      rintro ⟨_, _, result, contains⟩
      have nextLength := result.1.length_eq
      have tailValid : ∀ j ∈ indices, j < pending.length := fun j hj => valid j (by simp [hj])
      apply (ih tailValid next (inserted + 1) (sublist.trans contains)
        (by simp only [List.length_cons] at nextLength; omega)).weaken
        (fun _ h => ⟨h.1, h.2.1.2⟩) (Nat.le_refl _) ?_
      intro ys rank h sorted
      refine ⟨?_, sorted.2⟩
      have permutation := sorted.1.trans ((List.Perm.refl _).append h.2.1.1)
      have moved := permutation.trans List.perm_middle
      simpa [Function.comp_def] using moved

private theorem select_perm (xs : List α) (indices : List Nat)
    (valid : ∀ i ∈ indices, i < xs.length) (permutation : indices.Perm (List.range xs.length)) :
    (indices.attach.map (fun i => xs[i.val]'(valid i.val i.property))).Perm xs := by
  have all : ∀ i ∈ List.range xs.length, i < xs.length := by simp
  have selected := permutation.pmap (fun i (h : i < xs.length) => xs[i]) (H₁ := valid) (H₂ := all)
  have identity : (List.range xs.length).pmap (fun i (h : i < xs.length) => xs[i]) all = xs := by
    apply List.ext_getElem <;> simp
  rw [identity] at selected
  simpa only [List.pmap_eq_map_attach] using selected

private theorem split_pairs (pairs : List (α × α)) :
    (pairs.map Prod.fst ++ pairs.map Prod.snd).Perm
      (pairs.flatMap (fun pair => [pair.1, pair.2])) := by
  induction pairs with
  | nil => exact List.Perm.refl _
  | cons pair pairs ih =>
      simpa using (List.perm_middle.cons pair.1).trans ((ih.cons pair.2).cons pair.1)

theorem sort (key : α → Fin n) (xs : List α) (small : xs.length ≤ 42) :
    Computes n (fun _ => True) (cost xs.length) (SortResult key xs) := by
  by_cases trivial : xs.length < 2
  · rw [cost, if_pos trivial]
    apply Computes.pure xs
    intro rank _
    refine ⟨List.Perm.refl _, ?_⟩
    cases xs with
    | nil => exact List.Pairwise.nil
    | cons x xs =>
        have empty : xs = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at trivial; omega)
        subst xs; simp [Sorted]
  · rw [cost, if_neg trivial, Nat.add_assoc]
    apply (pair key xs).bind
    intro paired
    apply Computes.of_nonempty_precondition
    rintro ⟨_, pairLength, extraLength, _, _⟩
    have recursive := sort (fun p : α × α => key p.2) paired.1 (by omega)
    rw [pairLength] at recursive
    have sortedPairs := (recursive.frame (Paired key xs paired)).weaken
      (before' := Paired key xs paired) (fun _ h => ⟨h, True.intro⟩)
      (Nat.le_refl _) (fun _ _ _ h => h)
    apply sortedPairs.bind
    intro ordered
    apply Computes.of_nonempty_precondition
    rintro ⟨_, _, permutation, _⟩
    have orderedLength := permutation.length_eq
    let pending := ordered.map Prod.fst ++ paired.2
    let maxima := ordered.map Prod.snd
    have pendingLength : pending.length = xs.length - xs.length / 2 := by
      simp only [pending, List.length_append, List.length_map]
      omega
    have pendingSmall : pending.length ≤ 21 := by omega
    let indices := insertionOrder pending.length
    have schedule := insertionOrder_perm pendingSmall
    have valid : ∀ i ∈ indices, i < pending.length :=
      fun i h => List.mem_range.mp (schedule.mem_iff.mp h)
    rw [← pendingLength]
    apply (insert_pending key pending maxima indices valid maxima 0
      (List.Sublist.refl _) (by omega)).weaken ?_ (Nat.le_refl _) ?_
    · intro rank h
      refine ⟨?_, ?_⟩
      · intro i hp hm
        have inPairs : i < ordered.length := by simpa [maxima] using hm
        have bound := h.1.2.2.2 ordered[i]
          (h.2.1.mem_iff.mp (List.getElem_mem inPairs))
        simpa only [pending, maxima,
          List.getElem_append_left (as := ordered.map Prod.fst) (bs := paired.2) (i := i) (by simpa using inPairs),
          List.getElem_map] using bound
      · exact List.pairwise_map.mpr h.2.2
    · intro ys rank h result
      refine ⟨?_, result.2⟩
      have selected := select_perm pending indices valid schedule
      have shuffled : (pending ++ maxima).Perm
          ((ordered.map Prod.fst ++ ordered.map Prod.snd) ++ paired.2) := by
        simpa [pending, maxima, List.append_assoc] using
          (List.perm_append_comm (l₁ := paired.2) (l₂ := ordered.map Prod.snd)).append_left (ordered.map Prod.fst)
      exact result.1 |>.trans (selected.append_right maxima) |>.trans shuffled
        |>.trans ((split_pairs ordered).append_right paired.2)
        |>.trans ((h.2.1.flatMap_right (fun pair => [pair.1, pair.2])).append_right paired.2)
        |>.trans h.1.2.2.1
termination_by xs.length
decreasing_by omega

theorem base_costs : cost 21 = 66 ∧ cost 42 = 171 := by decide +kernel

theorem sorting_bound {size : Nat} (within : size ≤ 42) : SortingBound size (cost size) := by
  have computation := sort (n := size) id (List.finRange size) (by simpa using within)
  simp only [List.length_finRange] at computation
  exact sortingBound_of_computes (computation.weaken
    (fun _ _ => True.intro) (Nat.le_refl _) (fun _ _ _ h => h))

theorem base_bounds : S 21 ≤ 66 ∧ S 42 ≤ 171 := by
  have first := S_le (sorting_bound (size := 21) (by decide))
  have second := S_le (sorting_bound (size := 42) (by decide))
  simpa only [base_costs.1, base_costs.2] using And.intro first second

end FordJohnson.MergeInsertion
