import FordJohnson.Lib.DecisionTree

namespace FordJohnson.Certificate

structure State (n : Nat) where
  above : Vector Nat n
  below : Vector Nat n

namespace State

def Sound (state : State n) (rank : Ranking) : Prop :=
  (∀ i j : Fin n, (state.above[i]).testBit j → rank i < rank j) ∧
  (∀ i j : Fin n, (state.below[i]).testBit j → rank j < rank i)

def learn (state : State n) (x y : Fin n) : State n :=
  let predecessors := state.below[x] ||| 2 ^ x.val
  let successors := state.above[y] ||| 2 ^ y.val
  { above := Vector.ofFn fun i =>
      if predecessors.testBit i then state.above[i] ||| successors else state.above[i]
    below := Vector.ofFn fun i =>
      if successors.testBit i then state.below[i] ||| predecessors else state.below[i] }

/-- Learning `x < y` records consequences `a ≤ x < y ≤ b`. -/
theorem learn_sound {state : State n} {rank : Ranking} (sound : state.Sound rank)
    {x y : Fin n} (less : rank x < rank y) : (state.learn x y).Sound rank := by
  simp only [Sound, Fin.getElem_fin] at sound
  constructor <;> intro i j known <;>
    simp only [learn, Fin.getElem_fin, Vector.getElem_ofFn] at known <;>
    split at known
  all_goals
    simp only [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true,
      decide_eq_true_eq, Fin.val_inj] at *
    grind only

/-- Every distinct pair is comparable in the recorded knowledge. -/
def total (state : State n) : Bool :=
  (List.finRange n).all fun i =>
    state.above[i] ||| state.below[i] ||| 2 ^ i.val == 2 ^ n - 1

theorem total_compares {state : State n} (total : state.total = true)
    (i j : Fin n) (different : i ≠ j) :
    (state.above[i]).testBit j = true ∨ (state.below[i]).testBit j = true := by
  have row := (List.all_eq_true.mp total) i (List.mem_finRange i)
  have equal : state.above[i] ||| state.below[i] ||| 2 ^ i.val = 2 ^ n - 1 :=
    beq_iff_eq.mp row
  have bits := congrArg (fun mask : Nat => mask.testBit j) equal
  have different_values : i.val ≠ j.val := fun h => different (Fin.ext h)
  simpa [Nat.testBit_or, Nat.testBit_two_pow, different_values, j.isLt] using bits

theorem same_order_of_total {state : State n} (total : state.total = true)
    {first second : Ranking} (hFirst : state.Sound first) (hSecond : state.Sound second) :
    SameOrder n first second := by
  intro i hi j hj
  by_cases equal : i = j
  · subst j; simp
  · have different : (⟨i, hi⟩ : Fin n) ≠ ⟨j, hj⟩ := fun h => equal (congrArg Fin.val h)
    rcases total_compares total ⟨i, hi⟩ ⟨j, hj⟩ different with forward | backward
    · have hf := hFirst.1 ⟨i, hi⟩ ⟨j, hj⟩ forward
      have hs := hSecond.1 ⟨i, hi⟩ ⟨j, hj⟩ forward
      exact ⟨fun _ => hs, fun _ => hf⟩
    · have hf := hFirst.2 ⟨i, hi⟩ ⟨j, hj⟩ backward
      have hs := hSecond.2 ⟨i, hi⟩ ⟨j, hj⟩ backward
      simp only at hf hs
      omega

/-- Initial knowledge: exactly the comparisons within the sorted chain. -/
def chain (n length : Nat) : State n :=
  { above := Vector.ofFn fun i =>
      if i.val < length then (2 ^ length - 1) ^^^ (2 ^ (i.val + 1) - 1) else 0
    below := Vector.ofFn fun i => if i.val < length then 2 ^ i.val - 1 else 0 }

theorem chain_sound {n length : Nat} {rank : Ranking} (ordered : HasChain length rank) :
    (chain n length).Sound rank := by
  constructor
  · intro i j known
    simp only [chain, Fin.getElem_fin, Vector.getElem_ofFn] at known
    split at known
    next hi =>
      by_cases hj : j.val < length
      · by_cases hij : j.val < i.val + 1
        · simp [Nat.testBit_xor, hj, hij] at known
        · exact ordered i j (by omega) hj
      · have hij : ¬j.val < i.val + 1 := by omega
        simp [Nat.testBit_xor, hj, hij] at known
    next => simp at known
  · intro i j known
    simp only [chain, Fin.getElem_fin, Vector.getElem_ofFn] at known
    split at known
    next hi =>
      simp only [Nat.testBit_two_pow_sub_one, decide_eq_true_eq] at known
      exact ordered j i known hi
    next => simp at known

end State

def check (n : Nat) : DecisionTree → State n → Nat → Bool
  | .leaf, state, _ => state.total
  | .compare _ _ _ _, _, 0 => false
  | .compare x y less greater, state, budget + 1 =>
      if hx : x < n then
        if hy : y < n then
          x != y &&
          check n less (state.learn ⟨x, hx⟩ ⟨y, hy⟩) budget &&
          check n greater (state.learn ⟨y, hy⟩ ⟨x, hx⟩) budget
        else false
      else false

theorem check_sound (tree : DecisionTree) {state : State n} {budget : Nat}
    (accepted : check n tree state budget = true) :
    tree.labelsBelow n ∧ tree.height ≤ budget ∧ tree.Separates n state.Sound := by
  induction tree generalizing state budget with
  | leaf =>
      refine ⟨True.intro, Nat.zero_le _, ?_⟩
      intro first second _ _ hFirst hSecond _
      exact State.same_order_of_total accepted hFirst hSecond
  | compare x y less greater ihLess ihGreater =>
      cases budget with
      | zero => simp [check] at accepted
      | succ budget =>
          simp only [check] at accepted
          split at accepted
          next hx =>
            split at accepted
            next hy =>
              simp only [Bool.and_eq_true, bne_iff_ne] at accepted
              obtain ⟨⟨different, hLess⟩, hGreater⟩ := accepted
              obtain ⟨labelsLess, heightLess, separatesLess⟩ := ihLess hLess
              obtain ⟨labelsGreater, heightGreater, separatesGreater⟩ := ihGreater hGreater
              refine ⟨⟨hx, hy, different, labelsLess, labelsGreater⟩, ?_, ?_⟩
              · exact Nat.succ_le_succ (Nat.max_le.mpr ⟨heightLess, heightGreater⟩)
              · intro first second distinctFirst distinctSecond soundFirst soundSecond samePath
                simp only [DecisionTree.path] at samePath
                by_cases firstLess : first x < first y <;>
                  by_cases secondLess : second x < second y
                · simp only [if_pos firstLess, if_pos secondLess, List.cons.injEq,
                    true_and] at samePath
                  exact separatesLess first second distinctFirst distinctSecond
                    (State.learn_sound soundFirst firstLess)
                    (State.learn_sound soundSecond secondLess) samePath
                · simp [firstLess, secondLess] at samePath
                · simp [firstLess, secondLess] at samePath
                · simp only [if_neg firstLess, if_neg secondLess, List.cons.injEq,
                    true_and] at samePath
                  exact separatesGreater first second distinctFirst distinctSecond
                    (State.learn_sound soundFirst
                      (reverse_comparison distinctFirst hx hy different firstLess))
                    (State.learn_sound soundSecond
                      (reverse_comparison distinctSecond hx hy different secondLess))
                    samePath
            next => simp at accepted
          next => simp at accepted

theorem insertionBound_of_check {length pending budget : Nat} {tree : DecisionTree}
    (accepted : check (length + pending) tree (State.chain (length + pending) length) budget = true) :
    InsertionBound length pending budget := by
  obtain ⟨labels, height, separates⟩ := check_sound tree accepted
  refine ⟨tree, labels, height, ?_⟩
  intro first second distinctFirst distinctSecond chainFirst chainSecond samePath
  exact separates first second distinctFirst distinctSecond
    (State.chain_sound chainFirst) (State.chain_sound chainSecond) samePath

/-- Preorder encoding: `.` is a leaf; characters `65 + x`, `65 + y` compare labels. -/
def decode (bytes : ByteArray) : Nat → Nat → Option (DecisionTree × Nat)
  | 0, _ => none
  | fuel + 1, offset =>
      if offset < bytes.size then
        let first := bytes[offset]!.toNat
        if first = 46 then some (.leaf, offset + 1)
        else if 65 ≤ first ∧ first < 129 ∧ offset + 1 < bytes.size then
          let second := bytes[offset + 1]!.toNat
          if 65 ≤ second ∧ second < 129 then do
            let (less, next) ← decode bytes fuel (offset + 2)
            let (greater, finish) ← decode bytes fuel next
            return (.compare (first - 65) (second - 65) less greater, finish)
          else none
        else none
      else none

def verify (data : String) (length pending budget : Nat) : Bool :=
  match decode data.toUTF8 (budget + 1) 0 with
  | none => false
  | some (tree, finish) =>
      finish == data.utf8ByteSize &&
      check (length + pending) tree (State.chain (length + pending) length) budget

theorem verify_sound {data : String} {length pending budget : Nat}
    (accepted : verify data length pending budget = true) :
    InsertionBound length pending budget := by
  simp only [verify] at accepted
  split at accepted
  next => simp at accepted
  next tree finish _ =>
    simp only [Bool.and_eq_true] at accepted
    exact insertionBound_of_check accepted.2

end FordJohnson.Certificate
