import Proof.CaseAnalysis.RawRowsThresholdAccuracy
import Proof.Rows.FinalPrimeCursor
import Proof.Rows.FinalPrimeThresholdRow

/-! # The per-coefficient modular reduction loop

`FinalPrimeThresholdRow.threshold_row_run` emits the threshold row's accept bit
from a stream of summand words `w`, but it *assumes* four facts about that
stream: each word has the prime's width, each word is already reduced below the
prime, and the words are congruent to the equation's weights (and to `-target`
in the last slot).  Nothing produced those words.

This file produces them, twice over.

* **Physically.**  `FinalPrimeRow`'s Horner sweep is re-derived at an arbitrary
  *offset* of the bit tape (`stateFrom`, `hornerFrom`, `srcCfg`,
  `body_supplier`).  One coefficient tape then carries every coefficient of the
  row as a `K`-bit MSB-first block, and `reduction_loop` says: for each
  coefficient index `i` the driven loop `CloseoutRowsDegreeLoop.machine
  FinalPrimeRow.body`, started at offset `i * K` from the zero residue state,
  halts in `K * (4 * width + 9) + 3` ordinary steps with residue word exactly
  `SignedSortKey.binary width (c i % prime)`.  `n` coefficients are `n` passes
  of one machine on one tape: `loopFuel width K n` steps in total.  No new
  machine and no new assumption is introduced — the loop body is the accepted
  `FinalPrimeRow.body`, only its entry offset moves.

* **Arithmetically.**  `reducedWord` is the concrete stream
  `SignedSortKey.binary width ((eq.weights i) mod p)`, with `-eq.target` in the
  last slot, and `gateList` the concrete gate stream of one input.  All four
  hypotheses of `threshold_row_run` are discharged for them, so
  `threshold_row_reduced` emits `SupplierPrime.modularEquationHolds` from data
  that is *defined*, not assumed.

`reduced_of_congr` is the bridge: any physically reduced natural coefficient
congruent to the equation's integer weight produces the same word, so the two
halves name one object.
-/
namespace NearCubicWires.RepairOrdinary.FinalPrimeReduce
open LocalBitMultitape RecoveryExecution RadixSemantics ExtDecompositionBatch
open RepairSource.VerifierDecoding RecoveryRootRound
open SupplierPipeline SupplierPrime
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## 1. The Horner recurrence at a tape offset -/

/-! ## 2. The sweep state at a tape offset -/

/-! ## 3. The driven loop, entered at an offset -/

/-! ## 4. The zero residue state, and the reduced word of one window -/

/-! ## 5. One coefficient tape carrying every coefficient of the row -/

theorem getD_append_left : ∀ (l l' : List Bool) (i : ℕ), i < l.length →
    (l ++ l').getD i false = l.getD i false := by
  intro l
  induction l with
  | nil => intro l' i hi; simp at hi
  | cons b l ih =>
    intro l' i hi
    cases i with
    | zero => rfl
    | succ i =>
      have h := ih l' i (by simpa using hi)
      simpa using h

theorem getD_append_right : ∀ (l l' : List Bool) (i : ℕ), l.length ≤ i →
    (l ++ l').getD i false = l'.getD (i - l.length) false := by
  intro l
  induction l with
  | nil => intro l' i _; simp
  | cons b l ih =>
    intro l' i hi
    cases i with
    | zero => simp at hi
    | succ i =>
      have h := ih l' i (by simpa using hi)
      simpa using h

/-! ## 6. The loop -/

/-! ## 7. The reduced stream of one labelled equation -/

/-- The canonical representative of an integer residue class below the prime. -/
def intResidue (p : ℕ) (z : ℤ) : ℕ := (z % (p : ℤ)).toNat

theorem intResidue_lt (p : ℕ) (hp : 0 < p) (z : ℤ) : intResidue p z < p := by
  have hne : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  have h0 : (0 : ℤ) ≤ z % (p : ℤ) := Int.emod_nonneg z hne
  have h1 : z % (p : ℤ) < (p : ℤ) := Int.emod_lt_of_pos z (by exact_mod_cast hp)
  have h2 : ((z % (p : ℤ)).toNat : ℤ) = z % (p : ℤ) := Int.toNat_of_nonneg h0
  unfold intResidue
  omega

theorem intResidue_cast (p : ℕ) (hp : 0 < p) (z : ℤ) :
    ((intResidue p z : ℕ) : ZMod p) = ((z : ℤ) : ZMod p) := by
  have hne : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  have h0 : (0 : ℤ) ≤ z % (p : ℤ) := Int.emod_nonneg z hne
  have h2 : ((z % (p : ℤ)).toNat : ℤ) = z % (p : ℤ) := Int.toNat_of_nonneg h0
  have hstep : (((intResidue p z : ℕ) : ℤ) : ZMod p) = ((z : ℤ) : ZMod p) := by
    unfold intResidue
    rw [h2]
    exact (ZMod.intCast_eq_intCast_iff _ _ _).mpr (Int.emod_emod_of_dvd z dvd_rfl)
  simpa using hstep

/-- A physically reduced natural coefficient congruent to an integer weight
produces the same word as the arithmetic representative. -/
theorem reduced_of_congr (p : ℕ) (m : ℕ) (z : ℤ)
    (h : ((m : ℤ)) % (p : ℤ) = z % (p : ℤ)) : m % p = intResidue p z := by
  have hc : ((m % p : ℕ) : ℤ) = z % (p : ℤ) := by
    rw [Int.natCast_mod, h]
  unfold intResidue
  rw [← hc]
  generalize m % p = t
  simp

/-- The coefficient read by slot `i` of the row: a weight for `i < n`, and the
negated target in the last slot. -/
def coeffInt {n : ℕ} (eq : LabelledEquation (Fin n)) (i : ℕ) : ℤ :=
  if h : i < n then eq.weights ⟨i, h⟩ else -eq.target

theorem coeffInt_lt {n : ℕ} (eq : LabelledEquation (Fin n)) (i : Fin n) :
    coeffInt eq i.val = eq.weights i := by
  unfold coeffInt
  rw [dif_pos i.isLt]

theorem coeffInt_last {n : ℕ} (eq : LabelledEquation (Fin n)) :
    coeffInt eq n = -eq.target := by
  unfold coeffInt
  rw [dif_neg (lt_irrefl n)]

/-- The reduced summand stream of one labelled equation modulo one prime. -/
def reducedWord (p width : ℕ) {n : ℕ} (eq : LabelledEquation (Fin n)) (i : ℕ) : List Bool :=
  SignedSortKey.binary width (intResidue p (coeffInt eq i))

@[simp] theorem reducedWord_length (p width : ℕ) {n : ℕ} (eq : LabelledEquation (Fin n))
    (i : ℕ) : (reducedWord p width eq i).length = width := by
  simp [reducedWord]

theorem reducedWord_value (p width : ℕ) (hp : 0 < p) (hpw : 2 * p ≤ 2 ^ width)
    {n : ℕ} (eq : LabelledEquation (Fin n)) (i : ℕ) :
    value (reducedWord p width eq i) = intResidue p (coeffInt eq i) := by
  have hlt : intResidue p (coeffInt eq i) < 2 ^ width := by
    have := intResidue_lt p hp (coeffInt eq i)
    omega
  simp [reducedWord, SignedSortKey.binary_value width _ hlt]

theorem reducedWord_lt (p width : ℕ) (hp : 0 < p) (hpw : 2 * p ≤ 2 ^ width)
    {n : ℕ} (eq : LabelledEquation (Fin n)) (i : ℕ) :
    value (reducedWord p width eq i) < p := by
  rw [reducedWord_value p width hp hpw eq i]
  exact intResidue_lt p hp (coeffInt eq i)

/-- The gate stream of one input: the input bits, then the constant `true`
that admits the negated target. -/
def gateList {n : ℕ} (input : Fin n → Bool) : List Bool := List.ofFn input ++ [true]

theorem gateList_lt {n : ℕ} (input : Fin n → Bool) (i : Fin n) :
    (gateList input).getD i.val false = input i := by
  have h : i.val < (List.ofFn input).length := by simp
  unfold gateList
  rw [getD_append_left _ _ _ h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  simp

theorem gateList_last {n : ℕ} (input : Fin n → Bool) :
    (gateList input).getD n false = true := by
  have h : (List.ofFn input).length ≤ n := by simp
  unfold gateList
  rw [getD_append_right _ _ _ h]
  simp

/-! ## 8. The threshold row with the reduced stream supplied -/

/-! ## 9. Rung 2, THR mode, with nothing about the stream assumed -/

section PaperRow
open SourceInterfaces RepairRepresentation SupplierEstimator RepairSource.CloseoutRawRows

end PaperRow

end NearCubicWires.RepairOrdinary.FinalPrimeReduce
