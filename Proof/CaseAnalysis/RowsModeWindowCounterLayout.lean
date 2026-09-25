import Proof.CaseAnalysis.RowsModeWindowScalar

/-! Exact retained-bank identities for the physical inner counters. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowCounter
open LocalBitMultitape RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open CloseoutRowsModeWindowLayout
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem degree_tape (v u M a offset b scratch degree target C : Nat)
    (nonzero guard : Bool) (out : List Bool) :
    data v u M a offset b scratch degree target C nonzero guard out 48=
      ZeroPadding.pad C (CompareMachine.word a):=by
  change CloseoutRowsModeElementaryReusable.paddedBlank v a M C out 48=_
  rw [CloseoutRowsModeElementaryReusable.paddedBlank,CloseoutRowsModeElementaryLayout.blank_eq]
  rfl

theorem core_degree_other (v a a' M C : Nat) (out : List Bool) (i : Fin 52) (hi : i≠48) :
    CloseoutRowsModeElementaryReusable.paddedBlank v a M C out i=
      CloseoutRowsModeElementaryReusable.paddedBlank v a' M C out i:=by
  unfold CloseoutRowsModeElementaryReusable.paddedBlank
  rw [CloseoutRowsModeElementaryLayout.blank_eq,CloseoutRowsModeElementaryLayout.blank_eq]
  apply congrArg
  fin_cases i <;> first | rfl | exact False.elim (hi rfl)

theorem degree_other (v u M a a' offset b scratch degree target C : Nat)
    (nonzero guard : Bool) (out : List Bool) (i : Fin 60) (hi : i≠48) :
    data v u M a offset b scratch degree target C nonzero guard out i=
      data v u M a' offset b scratch degree target C nonzero guard out i:=by
  unfold data
  simp only [Fin.addCases]
  split
  · apply core_degree_other
    intro e
    exact hi (Fin.ext (congrArg (fun x : Fin 52=>x.val) e))
  · rfl


end NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowCounter
