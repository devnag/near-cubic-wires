import Proof.Rows.FinalPrimeRowOut

/-! # The THR row producer: one ordinary run emitting the row's accept bit

This joins the two verified stages into a single machine on a nine-tape bank:

* `CloseoutRowsDegreeLoop.machine FinalPrimeModular.body` accumulates the gated
  summand stream modulo the prime (`FinalPrimeModular.accumulate_loop`);
* `FinalPrimeRowOut.machine`, docked by an injective slot map, materialises the
  residue and emits the zero verdict in the same pass.

`Composition` adds finite control states but no tapes and the row-output stage
needs no head reset, so the tape stack stays exactly
`pass -> MaskedReset -> RepeatMachine` plus one embedded result cell.

The bridge `accum_congr` says the accumulated residue is congruent to the
labelled equation's difference, so the emitted bit is literally
`SupplierPrime.modularEquationHolds`.  The paper's accuracy for that bit is
unchanged: it is exactly the quantity bounded by
`CloseoutRawRows.threshold_prime_error` and `threshold_union_error`.
-/
namespace NearCubicWires.RepairOrdinary.FinalPrimeThresholdRow
open LocalBitMultitape RecoveryExecution RadixSemantics ExtDecompositionBatch
open RepairSource.VerifierDecoding RecoveryRootRound
open SupplierPipeline SupplierPrime
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## 1. The nine-tape bank -/

def portT : Fin (6 + 1 + 1 + 1) := Fin.castAdd 1 (Fin.castAdd 1 (Fin.castAdd 1 0))
def portU : Fin (6 + 1 + 1 + 1) := Fin.castAdd 1 (Fin.castAdd 1 (Fin.castAdd 1 1))
def portF : Fin (6 + 1 + 1 + 1) := Fin.castAdd 1 (Fin.castAdd 1 (Fin.castAdd 1 3))
def portR : Fin (6 + 1 + 1 + 1) := Fin.natAdd (6 + 1 + 1) 0

def slots : Fin 4 → Fin (6 + 1 + 1 + 1) := ![portT, portU, portF, portR]

theorem slots_injective : Function.Injective slots := by
  intro a b h
  have hv := congrArg (fun k : Fin (6 + 1 + 1 + 1) => k.val) h
  fin_cases a <;> fin_cases b <;> simp [slots, portT, portU, portF, portR] at hv ⊢

noncomputable def loopStart (prime width cap Q : ℕ) (w : ℕ → List Bool) (gates : List Bool) :=
  RepeatMachine.cfg 0 (FinalPrimeModular.sourceCfg prime width cap Q w gates 0) Q 1

noncomputable def loopEnd (prime width cap Q : ℕ) (w : ℕ → List Bool) (gates : List Bool) :=
  RepeatMachine.cfg 3 (FinalPrimeModular.sourceCfg prime width cap Q w gates Q) Q 1

noncomputable def whole :=
  Composition.machine
    (TapeEmbedding.machine 1 (CloseoutRowsDegreeLoop.machine FinalPrimeModular.body))
    (RecoveryFocus.machine slots FinalPrimeRowOut.machine)

def rowFuel (width Q : ℕ) : ℕ :=
  Q * (FinalPrimeModular.cost width + 3) + 3 + 1 + (2 * width + 2)

/-! ## 2. The port equalities, hoisted out of the tape stack -/

theorem ambientHeads_port (prime width cap Q : ℕ) (w : ℕ → List Bool) (gates : List Bool)
    (j : Fin 4) :
    Fin.addCases (motive := fun _ => ℕ) (loopEnd prime width cap Q w gates).heads
      (fun _ : Fin 1 => 0) (slots j) = (![0, 0, 0, 0] : Fin 4 → ℕ) j := by
  fin_cases j <;> rfl

theorem ambientTapes_port (prime width cap Q : ℕ) (w : ℕ → List Bool) (gates : List Bool)
    (j : Fin 4) :
    Fin.addCases (motive := fun _ => List Bool) (loopEnd prime width cap Q w gates).tapes
      (fun _ : Fin 1 => ([false] : List Bool)) (slots j) =
      (![frame (FinalPrimeModular.stateAt prime width w gates Q).1,
        frame (FinalPrimeModular.stateAt prime width w gates Q).2.1,
        [(FinalPrimeModular.stateAt prime width w gates Q).2.2],
        [false]] : Fin 4 → List Bool) j := by
  fin_cases j <;> rfl

/-! ## 3. One run of the joined machine -/

theorem row_step (prime width cap Q : ℕ) (w : ℕ → List Bool) (gates : List Bool)
    (hwlen : ∀ i, (w i).length = width) (hwval : ∀ i, value (w i) < prime)
    (hp0 : 0 < prime) (hp : 2 * prime ≤ 2 ^ width) (hcap : 2 * width + 2 ≤ cap) :
    Step whole (rowFuel width Q)
      (Fin.addCases (motive := fun _ => ℕ) (loopStart prime width cap Q w gates).heads
        (fun _ : Fin 1 => 0))
      (Fin.addCases (motive := fun _ => List Bool) (loopStart prime width cap Q w gates).tapes
        (fun _ : Fin 1 => ([false] : List Bool)))
      (dockH slots
        (Fin.addCases (motive := fun _ => ℕ) (loopEnd prime width cap Q w gates).heads
          (fun _ : Fin 1 => 0))
        (![2 * width + 1, 2 * width + 1, 0, 0] : Fin 4 → ℕ))
      (install slots
        (Fin.addCases (motive := fun _ => List Bool) (loopEnd prime width cap Q w gates).tapes
          (fun _ : Fin 1 => ([false] : List Bool)))
        (![frame (FinalPrimeRow.residueWord (FinalPrimeModular.stateAt prime width w gates Q)),
          frame (FinalPrimeModular.stateAt prime width w gates Q).2.1,
          [(FinalPrimeModular.stateAt prime width w gates Q).2.2],
          [decide (value (FinalPrimeRow.residueWord
            (FinalPrimeModular.stateAt prime width w gates Q)) = 0)]] : Fin 4 → List Bool)) := by
  obtain ⟨r, hr, hf, hs, _hres⟩ := FinalPrimeModular.accumulate_loop prime width cap Q w gates
    hwlen hwval hp0 hp hcap
  have hcfg : (⟨(CloseoutRowsDegreeLoop.machine FinalPrimeModular.body).start,
      (loopStart prime width cap Q w gates).heads,
      (loopStart prime width cap Q w gates).tapes⟩ : Configuration (6 + 1 + 1) _) =
      RepeatMachine.cfg 0 (FinalPrimeModular.sourceCfg prime width cap Q w gates 0) Q 1 := by
    apply configuration_ext
    · rfl
    · rfl
    · rfl
  rw [← hcfg] at hr
  have hloop : Step (CloseoutRowsDegreeLoop.machine FinalPrimeModular.body)
      (Q * (FinalPrimeModular.cost width + 3) + 3)
      (loopStart prime width cap Q w gates).heads (loopStart prime width cap Q w gates).tapes
      (loopEnd prime width cap Q w gates).heads (loopEnd prime width cap Q w gates).tapes :=
    Step.of_run hr (by rw [hf]; rfl) (by rw [hf]; rfl)
  have hemb := hloop.embed (fun _ : Fin 1 => 0) (fun _ : Fin 1 => ([false] : List Bool))
  obtain ⟨hT, hU⟩ := FinalPrimeModular.stateAt_length prime width w gates hwlen Q
  have hF : readTapeBit [(FinalPrimeModular.stateAt prime width w gates Q).2.2] 0 =
      (FinalPrimeModular.stateAt prime width w gates Q).2.2 := rfl
  have hrow := FinalPrimeRowOut.rowOut_step
    (FinalPrimeModular.stateAt prime width w gates Q).2.2
    (FinalPrimeModular.stateAt prime width w gates Q).1
    (FinalPrimeModular.stateAt prime width w gates Q).2.1
    [(FinalPrimeModular.stateAt prime width w gates Q).2.2] [false] (by rw [hU, hT]) hF
  rw [hT] at hrow
  have hfoc := hrow.focus slots slots_injective
    (Fin.addCases (motive := fun _ => ℕ) (loopEnd prime width cap Q w gates).heads
      (fun _ : Fin 1 => 0))
    (Fin.addCases (motive := fun _ => List Bool) (loopEnd prime width cap Q w gates).tapes
      (fun _ : Fin 1 => ([false] : List Bool)))
  rw [FinalPrimeResidue.dockH_existing slots _ _ (ambientHeads_port prime width cap Q w gates),
    install_existing slots _ _ (ambientTapes_port prime width cap Q w gates)] at hfoc
  have hres : (if (FinalPrimeModular.stateAt prime width w gates Q).2.2 then
      (FinalPrimeModular.stateAt prime width w gates Q).2.1
    else (FinalPrimeModular.stateAt prime width w gates Q).1) =
      FinalPrimeRow.residueWord (FinalPrimeModular.stateAt prime width w gates Q) := rfl
  rw [hres] at hfoc
  exact hemb.seq hfoc

/-! ## 4. The accumulation is the equation's difference -/

theorem partialSum_cast (p : ℕ) (w : ℕ → List Bool) (gates : List Bool) (j : ℕ) :
    ((FinalPrimeModular.partialSum w gates j : ℕ) : ZMod p) =
      ∑ i ∈ Finset.range j, (if gates.getD i false then ((value (w i) : ℕ) : ZMod p) else 0) := by
  induction j with
  | zero => simp [FinalPrimeModular.partialSum]
  | succ j ih =>
    rw [FinalPrimeModular.partialSum_succ, Finset.sum_range_succ, ← ih, Nat.cast_add]
    congr 1
    split <;> simp

theorem accum_congr (p n : ℕ) (eq : LabelledEquation (Fin n)) (input : Fin n → Bool)
    (w : ℕ → List Bool) (gates : List Bool)
    (hgate : ∀ i : Fin n, gates.getD i.val false = input i)
    (hgateLast : gates.getD n false = true)
    (hw : ∀ i : Fin n, ((value (w i.val) : ℕ) : ZMod p) = ((eq.weights i : ℤ) : ZMod p))
    (hwLast : ((value (w n) : ℕ) : ZMod p) = ((-eq.target : ℤ) : ZMod p)) :
    ((FinalPrimeModular.partialSum w gates (n + 1) : ℕ) : ZMod p) =
      ((eq.difference input : ℤ) : ZMod p) := by
  rw [partialSum_cast, Finset.sum_range_succ, hgateLast, if_pos rfl, hwLast]
  have hterms : ∑ i ∈ Finset.range n,
      (if gates.getD i false then ((value (w i) : ℕ) : ZMod p) else 0) =
      ((eq.score input : ℤ) : ZMod p) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun i => if gates.getD i false then ((value (w i) : ℕ) : ZMod p) else 0) n]
    unfold LabelledEquation.score
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hgate i, hw i]
    cases h : input i <;> simp [ThresholdCompiler.bitInt]
  rw [hterms]
  unfold LabelledEquation.difference
  push_cast
  ring

/-! ## 5. The emitted bit is `modularEquationHolds` -/

theorem emitted_bit {n cutoff : ℕ} (prime : PrimeIndex cutoff) (eq : LabelledEquation (Fin n))
    (input : Fin n → Bool) (w : ℕ → List Bool) (gates : List Bool)
    (hgate : ∀ i : Fin n, gates.getD i.val false = input i)
    (hgateLast : gates.getD n false = true)
    (hw : ∀ i : Fin n, ((value (w i.val) : ℕ) : ZMod prime.val) = ((eq.weights i : ℤ) : ZMod prime.val))
    (hwLast : ((value (w n) : ℕ) : ZMod prime.val) = ((-eq.target : ℤ) : ZMod prime.val)) :
    decide (FinalPrimeModular.partialSum w gates (n + 1) % prime.val = 0) =
      modularEquationHolds eq prime input := by
  have hp0 : 0 < prime.val := (mem_primesUpTo.mp prime.property).1.pos
  haveI : NeZero prime.val := ⟨by omega⟩
  have hcong := accum_congr prime.val n eq input w gates hgate hgateLast hw hwLast
  have hnat : (FinalPrimeModular.partialSum w gates (n + 1) % prime.val = 0) ↔
      ((FinalPrimeModular.partialSum w gates (n + 1) : ℕ) : ZMod prime.val) = 0 := by
    constructor
    · intro h
      have : ((FinalPrimeModular.partialSum w gates (n + 1) : ℕ) : ZMod prime.val) =
          ((0 : ℕ) : ZMod prime.val) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr (by unfold Nat.ModEq; simp [h])
      simpa using this
    · intro h
      have hmod : FinalPrimeModular.partialSum w gates (n + 1) ≡ 0 [MOD prime.val] := by
        refine (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_
        simpa using h
      unfold Nat.ModEq at hmod
      simpa using hmod
  have hint : (eq.difference input % (prime.val : ℤ) = 0) ↔
      ((eq.difference input : ℤ) : ZMod prime.val) = 0 := by
    constructor
    · intro h
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (Int.dvd_of_emod_eq_zero h)
    · intro h
      exact Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  unfold modularEquationHolds LabelledEquation.HoldsModulo
  refine decide_eq_decide.mpr ?_
  rw [hnat, hint, hcong]

end NearCubicWires.RepairOrdinary.FinalPrimeThresholdRow
