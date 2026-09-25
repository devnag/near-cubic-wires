import Proof.Rows.FinalNativeResiduePrepare
import Proof.Rows.FinalNativeSignedResidue
import Proof.CaseAnalysis.RowsEstimatorParityAlternating

/-! One original native signed coefficient yields its actual framed residue.
Prime/width fields, zero residue words, repetition template, blank workspace
and reset logs are physical inputs. Stream assembly and per-coefficient
workspace clearing remain enclosing program obligations. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10NativeResidue
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open RepairRepresentation VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def signFlipSlot : Fin 1 → Fin 10 := ![8]
noncomputable def flipSign := RecoveryFocus.machine signFlipSlot
  (CloseoutRowsEstimatorParity.Alternating.flip 0)
private def stateCount {s : ℕ} (_ : Machine 10 s) := s
noncomputable def signedMachine : (negate : Bool) → Machine 10
    (if negate then 2+stateCount C10NativeSignedResidue.machine else stateCount C10NativeSignedResidue.machine)
  | false => C10NativeSignedResidue.machine
  | true => Composition.machine flipSign C10NativeSignedResidue.machine

def signedBit (negate negative : Bool) := if negate then !negative else negative

private theorem vector8_other (a b c d e f g h x y j : List Bool) (i : Fin 10) (hi : i≠8) :
    (![a,b,c,d,e,f,g,h,x,j] : Fin 10 → List Bool) i = ![a,b,c,d,e,f,g,h,y,j] i := by
  rcases i with ⟨i,hi'⟩
  interval_cases i <;> simp_all only [Matrix.cons_val_succ', Matrix.cons_val_zero']
  exact False.elim (hi rfl)

theorem signed_run (negate : Bool) (p w cap Q D : ℕ) (bits : List Bool) (negative : Bool)
    (hc : 2*w+2≤cap) (hD : FinalPrimeResidue.fuel w Q≤D) (hs : 2*w+2≤D) :
    let st := FinalPrimeRow.stateAt p w bits Q
    let r := FinalPrimeRow.residueWord st
    let nr := FinalPrimeRow.residueWord (FinalPrimeNegate.negState p w r)
    ∃ output : Fin 10 → List Bool,
      Step (signedMachine negate) ((if negate then 2 else 0)+C10NativeSignedResidue.budget w Q)
        C10NativeSignedResidue.head
        (C10NativeSignedResidue.data p w cap Q D bits negative
          (SignedSortKey.binary w 0) (SignedSortKey.binary w 0) (SignedSortKey.binary w 0) false)
        C10NativeSignedResidue.head output ∧
      output 0=frame (if signedBit negate negative then nr else r) := by
  dsimp only
  obtain ⟨out,hr,ho,_,_⟩ := C10NativeSignedResidue.run p w cap Q D bits
    (signedBit negate negative) hc hD hs
  cases negate
  · simp only [signedMachine, signedBit, Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hr ho ⊢
    exact ⟨out,hr,ho⟩
  · simp only [signedMachine, signedBit, ↓reduceIte] at hr ho ⊢
    let A := C10NativeSignedResidue.data p w cap Q D bits negative
      (SignedSortKey.binary w 0) (SignedSortKey.binary w 0) (SignedSortKey.binary w 0) false
    let B := C10NativeSignedResidue.data p w cap Q D bits (!negative)
      (SignedSortKey.binary w 0) (SignedSortKey.binary w 0) (SignedSortKey.binary w 0) false
    have flip := CloseoutRowsEstimatorParity.Alternating.flip_run negative [] (fun i : Fin 0=>i.elim0)
    have firstStep := (flip.dock signFlipSlot (by decide) C10NativeSignedResidue.head A
      (by intro i; fin_cases i; rfl) (by intro i; fin_cases i; rfl)).congr
      (dockH_existing signFlipSlot _ _ (by intro i; fin_cases i; rfl))
      (HierarchyAllocation.install_eq signFlipSlot (by decide) A B _
        (by intro i; fin_cases i; rfl)
        (by intro i hi; exact vector8_other _ _ _ _ _ _ _ _ _ _ _ i (fun h=>hi 0 h.symm)))
    exact ⟨out,firstStep.seq hr,ho⟩

theorem selected_sign (negate negative : Bool) (n : ℕ) :
    (if signedBit negate negative then -(n : ℤ) else n) =
    (if negate then -(if negative then -(n : ℤ) else n) else
      (if negative then -(n : ℤ) else n)) := by
  cases negate <;> cases negative <;> simp [signedBit]

def slots : Fin 10 → Fin 22 := ![14,15,16,17,12,18,19,20,6,21]

def budget (negate : Bool) (z : ℤ) (w : ℕ) := 22*natBitLength z.natAbs+19+1+
  ((if negate then 2 else 0)+C10NativeSignedResidue.budget w (2*natBitLength z.natAbs))

/-- Actual weight slots consume the same native signed weight. -/
theorem weight_word (p w : ℕ) {n : ℕ} (eq : SupplierPipeline.LabelledEquation (Fin n)) (i : Fin n) :
    SignedSortKey.binary w (FinalPrimeReduce.intResidue p (eq.weights i)) =
      FinalPrimeReduce.reducedWord p w eq i.val := by
  simp only [FinalPrimeReduce.reducedWord, FinalPrimeReduce.coeffInt_lt]

end NearCubicWires.RepairSource.CloseoutFinal.C10NativeResidue
