import Proof.Rows.ClosureOffsetSourceGate

/-! Exact reusable native gate evaluator. The retained masters contain only
the original native source, assignment, dimensions and zero workspace; the
computed gate bit is appended and all other tapes are restored literally. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.OffsetSourceGate
open LocalBitMultitape RepairOrdinary RecoveryRootRound ExtDecompositionBatch
open RepairRepresentation RepairSource.CloseoutFinal RepairSource.VerifierDecoding
open CloseoutRowsPoolWeight

def extra : Fin 4→List Bool := ![[],[],CompareMachine.word 0,[]]
def entry (xs : List Item) (z : Int) (tail mtail : List Bool) (w C D : Nat)
    (out : List Bool) : Fin 48→List Bool :=
  Fin.addCases (motive:=fun _=>List Bool)
    (C10NaturalHardwireScoreInputs.data (word xs++intWord z++tail) (mask xs++mtail)
      out w C D xs.length 0 0) extra
noncomputable def worker := TapeEmbedding.machine 4 core
noncomputable def machine := Reusable48.machine worker
noncomputable def input (xs : List Item) (z : Int) (tail mtail : List Bool) (w C D R : Nat)
    (out : List Bool) := Reusable48.input (entry xs z tail mtail w C D) out R

def capacity (xs : List Item) (z : Int) (tail mtail : List Bool) (w C D : Nat) :=
  (word xs++intWord z++tail).length+(mask xs++mtail).length+D+C+2*w+xs.length+
    budget xs z w C+10

theorem masters_fit (xs : List Item) (z : Int) (tail mtail : List Bool) (w C D : Nat) :
    ∀ j,(Reusable48.masters (entry xs z tail mtail w C D) j).length ≤
      capacity xs z tail mtail w C D := by
  intro j
  fin_cases j <;>
    simp [Reusable48.masters,HardwireReusable.work,entry,extra,
      C10NaturalHardwireScoreInputs.data,C10NaturalHardwireScoreInputs.extra,
      C10NaturalHardwireTarget.input,C10NaturalHardwireTarget.pairInput,
      C10NaturalHardwireTarget.pairExtra,C10NaturalHardwireTarget.extra,
      CloseoutRowsPoolMagnitude.input,Fin.addCases,MatrixScoreWeight.scalar,
      ZeroPadding.pad_length,RepairOrdinary.frame_length,SignedSortKey.binary_length,
      CompareMachine.word,capacity] <;>omega

end NearCubicWires.P1Closure.OffsetSourceGate
