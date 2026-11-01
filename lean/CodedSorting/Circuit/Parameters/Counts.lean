import Std

/-!
# Exact arithmetic for the three-copy Construction candidate

These results check the arithmetic of the proposed construction.  They do not
assert that a circuit, a network, or an external-memory algorithm with these
counts has been constructed.  Those are separate proof obligations.

The target exponent is `3 / 200000 = 0.000015`.  All comparisons below are
statements about natural numbers obtained by clearing positive denominators;
no floating-point or external numerical oracle is used.
-/

namespace CodedSorting.Construction

def lineCount : Nat := 111
def localHelperCount : Nat := 439
def copiedTotalCost : Nat := 63
def ambientDimension : Nat := 512

def streamCount : Nat :=
  3 * lineCount ^ 2 * (2 * lineCount + localHelperCount)

def rankBudget : Nat :=
  6 * lineCount ^ 3 * (ambientDimension - 1) +
  3 * lineCount ^ 2 * localHelperCount * ambientDimension +
  9 * lineCount ^ 2 * copiedTotalCost

def rankDeficit : Nat := 3 * lineCount ^ 2 * (2 * lineCount - 3 * copiedTotalCost)

theorem ambientDimension_eq : ambientDimension = 512 := rfl

theorem streamCount_eq : streamCount = 24432543 := by decide

theorem rankBudget_eq : rankBudget = 12508242237 := by decide

theorem rankDeficit_eq : rankDeficit = 1219779 := by decide

theorem fullRankBudget_eq : streamCount * ambientDimension = 12509462016 := by decide

theorem budget_add_deficit :
    rankBudget + rankDeficit = streamCount * ambientDimension := by decide

theorem rankBudget_lt_full : rankBudget < streamCount * ambientDimension := by decide

/-- The identity `rankDeficit / (streamCount * 512) = 33 / 338432`,
    with denominators cleared. -/
theorem deficit_fraction_exact :
    rankDeficit * 338432 = 33 * (streamCount * ambientDimension) := by decide

/-- `epsilon = 3 / 200000` is exactly `15 / 1000000`. -/
theorem epsilon_fraction_exact : 3 * 1000000 = 15 * 200000 := by decide

/-- The exact inequality `(3/200000) * (63/10) < 33/338432`.
    An analytic lemma `log 512 < 63/10` is required separately. -/
theorem epsilon_log_bound_lt_deficit :
    3 * 63 * 338432 < 33 * 200000 * 10 := by decide

/-- A strictly positive integer margin for the preceding comparison. -/
theorem epsilon_margin_exact :
    3 * 63 * 338432 + 2036352 = 33 * 200000 * 10 := by decide

theorem all_denominators_positive :
    0 < streamCount * ambientDimension ∧ 0 < (338432 : Nat) ∧
    0 < (200000 : Nat) ∧ 0 < (10 : Nat) := by decide

end CodedSorting.Construction
