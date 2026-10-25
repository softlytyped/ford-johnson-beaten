import FordJohnson.Lib.Computation

namespace FordJohnson

def ceilLog2 (n : Nat) : Nat :=
  if n ≤ 1 then 0 else (n - 1).log2 + 1

theorem le_two_pow_ceilLog2 (n : Nat) : n ≤ 2 ^ ceilLog2 n := by
  unfold ceilLog2
  split
  · simp only [Nat.pow_zero]; omega
  · have := Nat.lt_log2_self (n := n - 1)
    omega

def Sorted (key : α → Fin n) (xs : List α) (rank : Ranking) : Prop :=
  xs.Pairwise fun x y => rank (key x) ≤ rank (key y)

def SortResult (key : α → Fin n) (xs ys : List α) (rank : Ranking) : Prop :=
  ys.Perm xs ∧ Sorted key ys rank

namespace BinaryInsertion

def Before (key : α → Fin n) (x : α) (xs : List α) (position : Nat)
    (rank : Ranking) : Prop :=
  ∀ i, (hi : i < xs.length) → i < position → rank (key xs[i]) ≤ rank (key x)

def After (key : α → Fin n) (x : α) (xs : List α) (position : Nat)
    (rank : Ranking) : Prop :=
  ∀ i, (hi : i < xs.length) → position ≤ i → rank (key x) ≤ rank (key xs[i])

private theorem search (key : α → Fin n) (x : α) (xs : List α) (depth lo hi : Nat)
    (interval : lo ≤ hi) (within : hi ≤ xs.length) (capacity : hi - lo < 2 ^ depth) :
    Computes n
      (fun rank => Sorted key xs rank ∧ Before key x xs lo rank ∧ After key x xs hi rank)
      depth (fun position rank => position ≤ xs.length ∧
        Before key x xs position rank ∧ After key x xs position rank) := by
  induction depth generalizing lo hi with
  | zero =>
      have equal : lo = hi := by simp only [Nat.pow_zero] at capacity; omega
      subst hi
      exact Computes.pure lo (fun _ h => ⟨within, h.2⟩)
  | succ depth ih =>
      by_cases equal : lo = hi
      · subst hi
        exact (Computes.pure lo (fun _ h => ⟨within, h.2⟩)).weaken
          (fun _ h => h) (Nat.zero_le _) (fun _ _ _ h => h)
      · let mid := (lo + hi) / 2
        have lower : lo ≤ mid := by dsimp [mid]; omega
        have upper : mid < hi := by dsimp [mid]; omega
        have pivot : mid < xs.length := by omega
        simp only [Nat.pow_succ] at capacity
        have leftCapacity : mid - lo < 2 ^ depth := by dsimp [mid]; omega
        have rightCapacity : hi - (mid + 1) < 2 ^ depth := by dsimp [mid]; omega
        apply Computes.branch (key x) (key xs[mid])
        · apply (ih lo mid lower (by omega) leftCapacity).weaken
            ?_ (Nat.le_refl _) (fun _ _ _ h => h)
          intro rank h
          refine ⟨h.1.1, h.1.2.1, ?_⟩
          intro i iWithin iAfter
          by_cases equalIndex : mid = i
          · subst i; exact Nat.le_of_lt h.2
          · have ordered := List.pairwise_iff_getElem.mp h.1.1 mid i pivot iWithin (by omega)
            exact Nat.le_trans (Nat.le_of_lt h.2) ordered
        · apply (ih (mid + 1) hi (by omega) within rightCapacity).weaken
            ?_ (Nat.le_refl _) (fun _ _ _ h => h)
          intro rank h
          refine ⟨h.1.1, ?_, h.1.2.2⟩
          intro i iWithin iBefore
          by_cases equalIndex : i = mid
          · subst i; omega
          · have ordered := List.pairwise_iff_getElem.mp h.1.1 i mid iWithin pivot (by omega)
            omega

theorem insert (key : α → Fin n) (x : α) (xs : List α) (limit depth : Nat)
    (within : limit ≤ xs.length) (capacity : limit < 2 ^ depth) :
    Computes n (fun rank => Sorted key xs rank ∧ After key x xs limit rank) depth
      (fun ys rank => SortResult key (x :: xs) ys rank ∧ xs.Sublist ys) := by
  have locate := (search key x xs depth 0 limit (Nat.zero_le _) within (by simpa using capacity)).weaken
    (before' := fun rank => Sorted key xs rank ∧ After key x xs limit rank)
    (fun _ h => ⟨h.1, by intro i _ impossible; omega, h.2⟩)
    (Nat.le_refl _) (fun _ _ _ h => h)
  apply locate.map (fun position => xs.take position ++ x :: xs.drop position)
  intro position rank h cut
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa using (List.perm_middle (a := x) (l₁ := xs.take position) (l₂ := xs.drop position))
  · apply List.pairwise_append.mpr
    refine ⟨h.1.take, List.pairwise_cons.mpr ⟨?_, h.1.drop⟩, ?_⟩
    · intro y member
      obtain ⟨i, bound, rfl⟩ := List.getElem_of_mem member
      simpa using cut.2.2 (position + i) (by simp only [List.length_drop] at bound; omega) (by omega)
    · intro a memberA b memberB
      obtain ⟨i, bound, rfl⟩ := List.getElem_of_mem memberA
      have first : rank (key (xs.take position)[i]) ≤ rank (key x) := by
        simpa using cut.2.1 i (by simp at bound; omega) (by simp at bound; omega)
      rcases List.mem_cons.mp memberB with rfl | memberB
      · exact first
      · obtain ⟨j, boundB, rfl⟩ := List.getElem_of_mem memberB
        have second : rank (key x) ≤ rank (key (xs.drop position)[j]) := by
          simpa using cut.2.2 (position + j) (by simp only [List.length_drop] at boundB; omega) (by omega)
        exact Nat.le_trans first second
  · have sublist := (List.Sublist.refl (xs.drop position)).cons x
    simpa using sublist.append_left (xs.take position)

end BinaryInsertion
end FordJohnson
