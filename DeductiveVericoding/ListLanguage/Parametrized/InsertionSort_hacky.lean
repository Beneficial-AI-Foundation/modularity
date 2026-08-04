import DeductiveVericoding.ListLanguage.Parametrized.Tactics
import DeductiveVericoding.ListLanguage.Parametrized.Translation

open ListLanguage

namespace Parametrized.HackyInsetionSort

def insertVal (a : Nat) : List Nat → List Nat
  | [] => [a]
  | h :: t => bif Nat.ble a h then a :: h :: t else h :: insertVal a t

abbrev sorted : List Nat → List Nat
  | [] => []
  | x :: xs => insertVal x (sorted xs)

abbrev InsertionSortProblem := ImplP [] (.arrow .list .list) (fun _ f => ∀ l, f l = sorted l)

-- The whole derivation is found by a single search, once `vericode` is told to unfold the
-- problem-specific definitions. `insertVal` uses `bif Nat.ble a h` (a `Bool`), so the
-- if-then-else condition becomes `Nat.ble a h` and `LePTactic` closes it — no `decide` in sight.
def InsertionSortSolution : InsertionSortProblem := by
  vericodeP [insertVal, sorted]

-- Disabled: `toClosed` depends on the stubbed `sorry` in `toList'` (listRec case).
-- #eval Trm.pretty (toClosed InsertionSortSolution.code)
