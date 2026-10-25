import FordJohnson.Lib.Sorting

namespace FordJohnson

def listRank (labels : List (Fin n)) (rank : Ranking) : Ranking :=
  fun i => if hi : i < labels.length then rank labels[i] else 0

theorem Computes.on_list (computation : Computes k before budget (SortResult id (List.finRange k)))
    (labels : List (Fin n)) (length : labels.length = k) :
    Computes n (fun rank => before (listRank labels rank)) budget (SortResult id labels) := by
  let label (i : Fin k) : Fin n := labels[i.val]'(by omega)
  have enumerate : (List.finRange k).map label = labels := by
    apply List.ext_getElem
    · simp [length]
    · intro i hi hj; simp [label]
  obtain ⟨tree, height, correct⟩ := computation
  have renamed : Computes n (fun rank => before (listRank labels rank)) budget
      (fun ys rank => SortResult id (List.finRange k) ys (listRank labels rank)) := by
    refine ⟨tree.relabel label, by simpa only [Program.height_relabel] using height, ?_⟩
    intro rank h
    rw [Program.run_relabel _ label rank (listRank labels rank)
      (by intro i; simp [listRank, label, show i.val < labels.length by omega])]
    exact correct _ h
  apply renamed.map (List.map label)
  intro ys rank _ result
  refine ⟨by simpa only [enumerate] using result.1.map label, List.pairwise_map.mpr ?_⟩
  apply result.2.imp
  intro i j ordered
  simpa only [listRank, id_eq, dif_pos (show i.val < labels.length by omega),
    dif_pos (show j.val < labels.length by omega), label] using ordered

theorem listRank_distinct {labels : List (Fin n)} (nodup : labels.Nodup)
    {rank : Ranking} (distinct : Distinct n rank) : Distinct labels.length (listRank labels rank) := by
  intro i hi j hj equal
  simp only [listRank, dif_pos hi, dif_pos hj] at equal
  have labelsEqual : labels[i] = labels[j] :=
    Fin.ext (distinct _ labels[i].isLt _ labels[j].isLt equal)
  exact (List.getElem_inj nodup).mp labelsEqual

theorem listRank_chain {labels : List (Fin n)} (nodup : labels.Nodup)
    {rank : Ranking} (distinct : Distinct n rank) (within : length ≤ labels.length)
    (sorted : Sorted id (labels.take length) rank) : HasChain length (listRank labels rank) := by
  intro i j less jWithin
  have hi : i < labels.length := by omega
  have hj : j < labels.length := by omega
  have ordered := List.pairwise_iff_getElem.mp sorted i j
    (by simp; omega) (by simp; omega) less
  simp only [id_eq, List.getElem_take] at ordered
  have different : listRank labels rank i ≠ listRank labels rank j :=
    fun equal => (Nat.ne_of_lt less) (listRank_distinct nodup distinct i hi j hj equal)
  simp only [listRank, dif_pos hi, dif_pos hj] at *
  omega

theorem SortingBound.batch_insert (sorted : SortingBound length sortBudget)
    (insertion : InsertionBound length pending insertBudget) :
    SortingBound (length + pending) (sortBudget + insertBudget) := by
  let labels := List.finRange (length + pending)
  let initialChain := labels.take length
  let suffix := labels.drop length
  have initialLength : initialChain.length = length := by simp [initialChain, labels]
  have initialNodup : initialChain.Nodup := (List.nodup_finRange _).take
  have first := (sorted.computes.on_list initialChain initialLength).weaken
    (before' := Distinct (length + pending))
    (after' := fun ys rank => Distinct (length + pending) rank ∧ SortResult id initialChain ys rank)
    (fun _ h => by simpa only [initialLength] using listRank_distinct initialNodup h)
    (Nat.le_refl _) (fun _ _ h result => ⟨h, result⟩)
  apply sortingBound_of_computes (first.bind ?_)
  intro chain
  apply Computes.of_nonempty_precondition
  rintro ⟨_, _, result⟩
  have chainLength : chain.length = length := result.1.length_eq.trans initialLength
  have permutation : (chain ++ suffix).Perm labels := by
    simpa only [initialChain, suffix, List.take_append_drop] using result.1.append_right suffix
  have fullLength : (chain ++ suffix).length = length + pending := by
    simpa only [labels, List.length_finRange] using permutation.length_eq
  have nodup : (chain ++ suffix).Nodup := permutation.nodup_iff.mpr (List.nodup_finRange _)
  obtain ⟨tree, valid, height, separates⟩ := insertion
  have second := ((tree.computes_of_separates valid separates).weaken
    (fun _ h => h) height (fun _ _ _ h => h)).on_list (chain ++ suffix) fullLength
  apply second.weaken ?_ (Nat.le_refl _) ?_
  · intro rank h
    refine ⟨?_, listRank_chain nodup h.1 (by omega) ?_⟩
    · simpa only [fullLength] using listRank_distinct nodup h.1
    · simpa [← chainLength] using h.2.2
  · intro ys rank _ sorted
    exact ⟨sorted.1.trans permutation, sorted.2⟩

theorem batch_insertion (insertion : InsertionBound length pending budget) :
    S (length + pending) ≤ S length + budget :=
  S_le ((S_spec length).batch_insert insertion)

theorem binary_insertion_certificate (n : Nat) : InsertionBound n 1 (ceilLog2 (n + 1)) := by
  let initialChain := (List.finRange n).map Fin.castSucc
  have initialLength : initialChain.length = n := by simp [initialChain]
  have capacity := le_two_pow_ceilLog2 (n + 1)
  apply decisionTree_of_computes
  apply (BinaryInsertion.insert id (Fin.last n) initialChain n (ceilLog2 (n + 1))
    (by omega) (by omega)).weaken ?_ (Nat.le_refl _) ?_
  · intro rank h
    refine ⟨?_, ?_⟩
    · apply List.pairwise_iff_getElem.mpr
      intro i j hi hj less
      simp only [initialChain, List.length_map, List.length_finRange] at hi hj
      simpa [initialChain] using Nat.le_of_lt (h.2 i j less hj)
    · intro i hi after; omega
  · intro ys rank _ result
    refine ⟨result.1.1.trans ?_, result.1.2⟩
    simpa [initialChain, List.finRange_succ_last] using
      (List.perm_append_comm (l₁ := [Fin.last n]) (l₂ := initialChain))

theorem binary_insertion (n : Nat) : S (n + 1) ≤ S n + ceilLog2 (n + 1) :=
  batch_insertion (binary_insertion_certificate n)

end FordJohnson
