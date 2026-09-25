import Proof.Rows.ThresholdStreams

/-! Actual nine-tape comparator Step on the physically emitted coefficient
and flag codecs. The final bank is explicit for paid verdict copy and cleanup. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_ThresholdCompare
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding RadixSemantics SignedSortKey
noncomputable section

def bank (p w cap Q :Nat) (flags coefficients A B :List Bool) (f verdict :Bool):Fin 9→List Bool:=
 ![frame A,frame B,frame (binary w p),[f],flags,coefficients,List.replicate cap false,
  CompareMachine.word Q,[verdict]]
def startHeads:Fin 9→Nat:=![0,0,0,0,0,0,0,1,0]
def finalHeads (w Q :Nat):Fin 9→Nat:=![2*w+1,2*w+1,0,0,Q,Q*(2*w+1),0,1,0]
def state (p w :Nat) {n :Nat} (eq :LabelledEquation (Fin n)) (input :Fin n→Bool):=
 FinalPrimeModular.stateAt p w (FinalPrimeReduce.reducedWord p w eq) (FinalPrimeReduce.gateList input) (n+1)

theorem verdict {n cutoff :Nat} (prime :PrimeIndex cutoff) (w :Nat) (eq :LabelledEquation (Fin n))
 (input :Fin n→Bool) (hpw :2*prime.val ≤ 2^w):
 decide (value (FinalPrimeRow.residueWord (state prime.val w eq input))=0)=modularEquationHolds eq prime input :=by
 have hp:0<prime.val:=(mem_primesUpTo.mp prime.property).1.pos
 have val:value (FinalPrimeRow.residueWord (state prime.val w eq input))=
  FinalPrimeModular.partialSum (FinalPrimeReduce.reducedWord prime.val w eq)
   (FinalPrimeReduce.gateList input) (n+1)%prime.val:=by
   rw [←FinalPrimeRow.residueOf_word]
   exact FinalPrimeModular.stateAt_residue prime.val w _ _
    (FinalPrimeReduce.reducedWord_length prime.val w eq)
    (FinalPrimeReduce.reducedWord_lt prime.val w hp hpw eq) hp hpw (n+1)
 rw [val]
 apply FinalPrimeThresholdRow.emitted_bit prime eq input
  (FinalPrimeReduce.reducedWord prime.val w eq) (FinalPrimeReduce.gateList input)
  (FinalPrimeReduce.gateList_lt input) (FinalPrimeReduce.gateList_last input)
 · intro i
   rw [FinalPrimeReduce.reducedWord_value prime.val w hp hpw eq i.val,FinalPrimeReduce.coeffInt_lt]
   exact FinalPrimeReduce.intResidue_cast prime.val hp (eq.weights i)
 · rw [FinalPrimeReduce.reducedWord_value prime.val w hp hpw eq n,FinalPrimeReduce.coeffInt_last]
   exact FinalPrimeReduce.intResidue_cast prime.val hp (-eq.target)

theorem run {n cutoff :Nat} (prime :PrimeIndex cutoff) (w cap :Nat)
 (eq :LabelledEquation (Fin n)) (input :Fin n→Bool) (hpw :2*prime.val ≤ 2^w) (hcap :2*w+2 ≤ cap):
 Step FinalPrimeThresholdRow.whole (FinalPrimeThresholdRow.rowFuel w (n+1)) startHeads
  (bank prime.val w cap (n+1) (FinalPrimeReduce.gateList input)
   (FinalPrimeModular.blocks (FinalPrimeReduce.reducedWord prime.val w eq) 0 (n+1))
   (binary w 0) (binary w 0) false false)
  (finalHeads w (n+1))
  (bank prime.val w cap (n+1) (FinalPrimeReduce.gateList input)
   (FinalPrimeModular.blocks (FinalPrimeReduce.reducedWord prime.val w eq) 0 (n+1))
   (FinalPrimeRow.residueWord (state prime.val w eq input)) (state prime.val w eq input).2.1
   (state prime.val w eq input).2.2 (modularEquationHolds eq prime input)) :=by
 have hp:0<prime.val:=(mem_primesUpTo.mp prime.property).1.pos
 have s:=FinalPrimeThresholdRow.row_step prime.val w cap (n+1)
  (FinalPrimeReduce.reducedWord prime.val w eq) (FinalPrimeReduce.gateList input)
  (FinalPrimeReduce.reducedWord_length prime.val w eq)
  (FinalPrimeReduce.reducedWord_lt prime.val w hp hpw eq) hp hpw hcap
 refine (s.congr_in ?_ ?_).congr ?_ ?_
 · funext i;fin_cases i
   all_goals first
    | rfl
    | change 0*(2*w+1)=0;omega
 · funext i;fin_cases i <;>rfl
 · funext i;fin_cases i
   all_goals first
    | rfl
    | exact dockH_slot FinalPrimeThresholdRow.slots FinalPrimeThresholdRow.slots_injective _ _ 0
    | exact dockH_slot FinalPrimeThresholdRow.slots FinalPrimeThresholdRow.slots_injective _ _ 1
    | exact dockH_slot FinalPrimeThresholdRow.slots FinalPrimeThresholdRow.slots_injective _ _ 2
    | exact dockH_slot FinalPrimeThresholdRow.slots FinalPrimeThresholdRow.slots_injective _ _ 3
 · funext i;fin_cases i
   all_goals first
    | rfl
    | exact RecoveryRootRound.install_slot FinalPrimeThresholdRow.slots FinalPrimeThresholdRow.slots_injective _ _ 0
    | exact RecoveryRootRound.install_slot FinalPrimeThresholdRow.slots FinalPrimeThresholdRow.slots_injective _ _ 1
    | exact RecoveryRootRound.install_slot FinalPrimeThresholdRow.slots FinalPrimeThresholdRow.slots_injective _ _ 2
    | exact (RecoveryRootRound.install_slot FinalPrimeThresholdRow.slots FinalPrimeThresholdRow.slots_injective _ _ 3).trans
       (congrArg (fun b=>[b]) (verdict prime w eq input hpw))
end
end PCJ45bee56da9f34d5a_ThresholdCompare
