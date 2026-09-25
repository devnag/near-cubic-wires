import Proof.Packets.PacketsXVectorCoordinateCollect
import Proof.Packets.PacketsXVectorWorkerReset

/-! The candidate counter is physically zeroed after vector construction,
then the already resident population-plus-one driver enumerates coordinates. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section
attribute [local irreducible] resetChild coordinateCollect

def collectedCandidates {s : Nat} (callback : Machine 296 s):=
  Composition.machine (TapeEmbedding.machine 1 resetChild) (coordinateCollect callback)

theorem collected_candidates_run {s : Nat} (callback : Machine 296 s) (C R N ci pi li fuel : Nat)
    (left right acc : PacketVector.Packet) (previous next : List Bool)
    (fields : Fin 222→List Bool) (extra : Fin 32→List Bool) (output : Fin 297→List Bool)
    (hc : ci+1≤R)
    (hloop : Step (coordinateCollect callback) fuel
      (Fin.addCases (H (fun _ : Fin 222=>0)) (fun _ : Fin 1=>1))
      (Fin.addCases (A C R 0 pi li left right acc previous next fields extra)
        (fun _ : Fin 1=>ZeroPadding.pad R (CompareMachine.word N)))
      (Fin.addCases (H (fun _ : Fin 222=>0)) (fun _ : Fin 1=>1)) output) :
    Step (collectedCandidates callback) (2*R+7+fuel)
      (Fin.addCases (H (fun _ : Fin 222=>0)) (fun _ : Fin 1=>1))
      (Fin.addCases (A C R ci pi li left right acc previous next fields extra)
        (fun _ : Fin 1=>ZeroPadding.pad R (CompareMachine.word N)))
      (Fin.addCases (H (fun _ : Fin 222=>0)) (fun _ : Fin 1=>1)) output := by
  have first:=(reset_child_run C R ci pi li left right acc previous next (fun _=>0) fields extra hc).embed
    (fun _ : Fin 1=>1) (fun _ : Fin 1=>ZeroPadding.pad R (CompareMachine.word N))
  have joined:=first.seq hloop
  have fuelEq:(2*R+6)+1+fuel=2*R+7+fuel := by omega
  rw [fuelEq] at joined
  exact joined

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
