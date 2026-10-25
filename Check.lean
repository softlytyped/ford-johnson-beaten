import FordJohnson
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open FordJohnson.Certificate

example : verify "AB.." 0 2 1 = true := by decide +kernel
example : verify "." 1 0 0 = true := by decide +kernel

example : verify "." 0 2 0 = false := by decide +kernel

example : verify "AA.." 0 2 1 = false := by decide +kernel
example : verify "AC.." 0 2 1 = false := by decide +kernel
example : verify "AB.." 0 2 0 = false := by decide +kernel

example : verify "AB." 0 2 1 = false := by decide +kernel
example : verify "AB..." 0 2 1 = false := by decide +kernel
example : verify "?" 1 0 0 = false := by decide +kernel

example :
    FordJohnson.S 26 ≤ 90 ∧ FordJohnson.S 46 ≤ 194 ∧
    FordJohnson.F 26 = 91 ∧ FordJohnson.F 46 = 195 ∧
    ∀ n, (26 ≤ n ∧ n ≤ 32) ∨ (46 ≤ n ∧ n ≤ 64) →
      FordJohnson.S n ≤ FordJohnson.F n - 1 := FordJohnson.main_theorem

open Lean in
run_cmd do
  let permitted := #[`propext, `Classical.choice, `Quot.sound,
    `FordJohnson.insert_five_into_twenty_one._native.native_decide.ax_1_1,
    `FordJohnson.insert_four_into_forty_two._native.native_decide.ax_1_1]
  for dependency in ← collectAxioms ``FordJohnson.main_theorem do
    unless permitted.contains dependency do
      throwError "Unexpected proof axiom: {dependency}"
  logInfo "Axiom audit passed."

#print axioms FordJohnson.Certificate.State.learn_sound
#print axioms FordJohnson.Certificate.check_sound
#print axioms FordJohnson.Certificate.verify_sound
#print axioms FordJohnson.insert_five_into_twenty_one
#print axioms FordJohnson.insert_four_into_forty_two
#print axioms FordJohnson.S_spec
#print axioms FordJohnson.S_le
#print axioms FordJohnson.MergeInsertion.sort
#print axioms FordJohnson.MergeInsertion.base_bounds
#print axioms FordJohnson.SortingBound.batch_insert
#print axioms FordJohnson.binary_insertion
#print axioms FordJohnson.base_counts
#check FordJohnson.main_theorem
#print axioms FordJohnson.main_theorem
