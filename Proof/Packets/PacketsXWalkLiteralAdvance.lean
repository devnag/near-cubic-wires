import Proof.Packets.PacketsXWalkLiteralVisit
import Proof.Packets.PacketsXWalkTimeLoop

/-! The resident walk advances while retaining the palette, its bounded
workspace, and the transcript at its current cursor. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralAdvance
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces NearCubicWires.SupplierWalkBridge
open NearCubicWires.SupplierWalk
open PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
noncomputable section

def machine := TapeEmbedding.machine 317 (TapeEmbedding.machine 7 WalkPoweredRun.machine)
def budget (rank R : Nat) := 160*toeplitzWalkSideBits rank+160*R+1160

theorem run {rank n : Nat} (R L S dest : Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits rank) (n+1)) (tail : List Bool)
    (palette : Fin 15 → List Bool) (work : Fin 299 → List Bool) (transcript : List Bool)
    (i : Nat) (hi : i<n) (hR : 2*toeplitzWalkSideBits rank+1 ≤ R)
    (hL : 2*toeplitzWalkSideBits rank+1 ≤ L) :
    Step machine (budget rank R) (WalkLiteralVisit.H (160*i) dest)
      (WalkLiteralVisit.A rank R L S (WalkTimeLoop.vertex sample i)
        (WalkSampleWord.labelsWord (sampleTransitionLabels sample)++tail) palette work transcript)
      (WalkLiteralVisit.H (160*(i+1)) dest)
      (WalkLiteralVisit.A rank R L S (WalkTimeLoop.vertex sample (i+1))
        (WalkSampleWord.labelsWord (sampleTransitionLabels sample)++tail) palette work transcript) := by
  have first:=WalkTimeLoop.iteration R L sample tail i hi hR hL
  have second:=first.embed (fun _ : Fin 7=>0) (WalkSeedResident.extras rank R)
  have third:=second.embed (collectHeads dest) (collectData palette S work transcript)
  simpa only [machine,budget,WalkLiteralVisit.H,WalkLiteralVisit.A,WalkTimeLoop.H,WalkTimeLoop.A,
    WalkSeedResident.heads,WalkSeedResident.input,Nat.min_eq_left (by omega : i≤n),
    Nat.min_eq_left (by omega : i+1≤n)] using third

end
end Theorem25Completion.WalkLiteralAdvance
