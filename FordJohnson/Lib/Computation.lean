import FordJohnson.Lib.DecisionTree

namespace FordJohnson

/-- A comparison tree whose leaves carry results. -/
inductive Program (n : Nat) (α : Type) where
  | pure (value : α)
  | compare (x y : Fin n) (less greater : Program n α)

namespace Program

def height : Program n α → Nat
  | .pure _ => 0
  | .compare _ _ less greater => max less.height greater.height + 1

def run (rank : Ranking) : Program n α → α
  | .pure value => value
  | .compare x y less greater =>
      if rank x < rank y then less.run rank else greater.run rank

def bind (next : α → Program n β) : Program n α → Program n β
  | .pure value => next value
  | .compare x y less greater => .compare x y (less.bind next) (greater.bind next)

theorem run_bind (tree : Program n α) (next : α → Program n β) (rank : Ranking) :
    (tree.bind next).run rank = (next (tree.run rank)).run rank := by
  induction tree <;> simp_all [bind, run]
  split <;> simp_all

theorem height_bind (tree : Program n α) {next : α → Program n β}
    (bound : ∀ value, (next value).height ≤ budget) :
    (tree.bind next).height ≤ tree.height + budget := by
  induction tree with
  | pure value => simpa [bind, height] using bound value
  | compare x y less greater ihLess ihGreater =>
      simp only [bind, height]
      omega

def erase : Program n α → DecisionTree
  | .pure _ => .leaf
  | .compare x y less greater =>
      if x = y then greater.erase else .compare x y less.erase greater.erase

theorem erase_valid (tree : Program n α) :
    tree.erase.labelsBelow n ∧ tree.erase.height ≤ tree.height := by
  induction tree with
  | pure => exact ⟨True.intro, Nat.le_refl _⟩
  | compare x y less greater ihLess ihGreater =>
      simp only [erase]
      split
      · exact ⟨ihGreater.1, by simp only [height]; omega⟩
      · exact ⟨⟨x.isLt, y.isLt, by simpa using Fin.val_ne_of_ne ‹x ≠ y›,
          ihLess.1, ihGreater.1⟩, by simp only [DecisionTree.height, height]; omega⟩

theorem run_eq_of_path_eq (tree : Program n α) {first second : Ranking}
    (same : tree.erase.path first = tree.erase.path second) :
    tree.run first = tree.run second := by
  induction tree with
  | pure => rfl
  | compare x y less greater ihLess ihGreater =>
      by_cases equal : x = y
      · subst y
        simp only [erase] at same
        simpa [run] using ihGreater same
      · simp only [erase, if_neg equal, DecisionTree.path] at same
        simp only [run]
        split <;> split <;> simp_all

def relabel (labels : Fin n → Fin m) : Program n α → Program m α
  | .pure value => .pure value
  | .compare x y less greater =>
      .compare (labels x) (labels y) (less.relabel labels) (greater.relabel labels)

theorem height_relabel (tree : Program n α) (labels : Fin n → Fin m) :
    (tree.relabel labels).height = tree.height := by
  induction tree <;> simp_all [relabel, height]

theorem run_relabel (tree : Program n α) (labels : Fin n → Fin m) (rank : Ranking)
    (renamed : Ranking) (agrees : ∀ i : Fin n, renamed i = rank (labels i)) :
    (tree.relabel labels).run rank = tree.run renamed := by
  induction tree <;> simp_all [relabel, run]

end Program

/-- A bounded comparison computation, with its precondition and postcondition. -/
def Computes (n : Nat) (before : Ranking → Prop) (budget : Nat)
    (after : α → Ranking → Prop) : Prop :=
  ∃ tree : Program n α, tree.height ≤ budget ∧
    ∀ rank, before rank → after (tree.run rank) rank

namespace Computes

theorem pure (value : α) (proof : ∀ rank, before rank → after value rank) :
    Computes n before 0 after := ⟨.pure value, Nat.le_refl _, proof⟩

theorem weaken (computation : Computes n before budget after)
    (pre : ∀ rank, before' rank → before rank) (cost : budget ≤ budget')
    (post : ∀ value rank, before' rank → after value rank → after' value rank) :
    Computes n before' budget' after' := by
  obtain ⟨tree, height, correct⟩ := computation
  exact ⟨tree, Nat.le_trans height cost, fun rank h => post _ rank h (correct rank (pre rank h))⟩

theorem bind (first : Computes n before firstCost middle)
    (next : ∀ value, Computes n (middle value) nextCost after) :
    Computes n before (firstCost + nextCost) after := by
  classical
  let continuation value := (next value).choose
  have height value := (next value).choose_spec.1
  have correct value := (next value).choose_spec.2
  obtain ⟨tree, bound, sound⟩ := first
  refine ⟨tree.bind continuation, Nat.le_trans (Program.height_bind tree height)
    (Nat.add_le_add_right bound _), ?_⟩
  intro rank h
  simpa only [Program.run_bind] using correct (tree.run rank) rank (sound rank h)

theorem branch (x y : Fin n)
    (less : Computes n (fun rank => before rank ∧ rank x < rank y) budget after)
    (greater : Computes n (fun rank => before rank ∧ ¬rank x < rank y) budget after) :
    Computes n before (budget + 1) after := by
  obtain ⟨left, heightLeft, correctLeft⟩ := less
  obtain ⟨right, heightRight, correctRight⟩ := greater
  refine ⟨.compare x y left right, by simp only [Program.height]; omega, ?_⟩
  intro rank h
  simp only [Program.run]
  split
  · exact correctLeft rank ⟨h, ‹_›⟩
  · exact correctRight rank ⟨h, ‹_›⟩

theorem map {after : α → Ranking → Prop} {after' : β → Ranking → Prop}
    (computation : Computes n before budget after) (f : α → β)
    (proof : ∀ value rank, before rank → after value rank → after' (f value) rank) :
    Computes n before budget after' := by
  obtain ⟨tree, height, correct⟩ := computation
  refine ⟨tree.bind (fun value => .pure (f value)), ?_, ?_⟩
  · have bound := Program.height_bind tree (next := fun value => .pure (f value))
      (budget := 0) (fun _ => Nat.le_refl _)
    omega
  · intro rank h
    simpa only [Program.run_bind, Program.run] using proof _ rank h (correct rank h)

theorem frame (computation : Computes n before budget after) (invariant : Ranking → Prop) :
    Computes n (fun rank => invariant rank ∧ before rank) budget
      (fun value rank => invariant rank ∧ after value rank) :=
  computation.weaken (fun _ h => h.2) (Nat.le_refl _) (fun _ _ h result => ⟨h.1, result⟩)

theorem of_nonempty_precondition {after : α → Ranking → Prop} [Nonempty α]
    (build : (∃ rank, before rank) → Computes n before budget after) :
    Computes n before budget after := by
  classical
  by_cases possible : ∃ rank, before rank
  · exact build possible
  · exact (pure (Classical.choice ‹Nonempty α›) (fun rank h => False.elim (possible ⟨rank, h⟩))).weaken
      (fun _ h => h) (Nat.zero_le _) (fun _ _ _ h => h)

end Computes
end FordJohnson
