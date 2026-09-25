import Proof.Packets.PacketsXWalkLiteralMastersCanonical
import Proof.Packets.SourceGradedRank

/-! The palette's rank and depth are actual outputs of the original graded
rank computation. Entry supplies population and active count, no rank/depth words. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralMasters
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed.Materializer
open Completion
noncomputable section

def gradedExtra (C R root : Nat) (mask : List Bool) (i : Fin 55) : List Bool :=
  if i=0 then List.replicate C true else if i=1 then List.replicate R true else
  if i=2 then List.replicate root true else if i=6 then mask else []
def gradedInput (C R root population active : Nat) (mask : List Bool) : Fin 95→List Bool :=
  Fin.addCases (m:=40) (n:=55) (motive:=fun _=>List Bool)
    (SourceGradedRank.input population active) (gradedExtra C R root mask)
def gradedSlots (i : Fin 55) : Fin 95 :=
  if i=3 then 36 else if i=4 then 38 else if i=5 then 11 else i.natAdd 40
def gradedMachine := Composition.machine (TapeEmbedding.machine 55 SourceGradedRank.machine)
  (RecoveryFocus.machine gradedSlots machine)
def gradedBudget (C R root population active : Nat) (mask : List Bool) :=
  SourceGradedRank.budget population active+1+
    budget C R root (SourceGradedRank.rank population active) (SourceGradedRank.depth active) population mask
attribute [local irreducible] machine SourceGradedRank.machine

theorem graded_slots_injective : Function.Injective gradedSlots := by decide

theorem graded_join (C R root population active : Nat) (mask : List Bool) (rankData : Fin 40→List Bool)
    (hr : rankData 36=List.replicate (SourceGradedRank.rank population active) true)
    (hd : rankData 38=List.replicate (SourceGradedRank.depth active) true)
    (hp : rankData 11=List.replicate population true) :
    ∀i,Fin.addCases (m:=40) (n:=55) (motive:=fun _=>List Bool)
      rankData (gradedExtra C R root mask) (gradedSlots i)=
      input C R root (SourceGradedRank.rank population active) (SourceGradedRank.depth active) population mask i := by
  intro i
  by_cases h3 : i=3
  · subst i;exact hr
  by_cases h4 : i=4
  · subst i;exact hd
  by_cases h5 : i=5
  · subst i;exact hp
  simp [gradedSlots,gradedExtra,input,h3,h4,h5,Fin.addCases_right]

end
end Theorem25Completion.WalkLiteralMasters
