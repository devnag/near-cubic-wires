import Proof.CaseAnalysis.FinalThresholdEstimateRowJoin
import Proof.MachineModel.TopDownPaidReusableFamily

/-! Apply the completed physical hrow to both existing family consumers.
The list-to-payload equality is the explicit upstream semantic contract;
it does not supply an execution receipt or a row-loader callback. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDownPaidReusable
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open SupplierPipeline SupplierEstimator SourceInterfaces CanonicalFourfoldRowProgram
open RepairSource.CloseoutFinal.C10ExternalRowLoop
open RepairSource.CloseoutFinal.C10ThresholdEstimateRowJoin
open RepairSource.CloseoutFinal.C10ThresholdNaturalSum
open CloseoutFinalC10RowAnswerWord
open CloseoutFinalC10SupplierAccuracy (rowAnswer)
open P1TopDownPaidPayload (tapes)
attribute [local irreducible] machine CompetitorCrossScheduler.producer

noncomputable def outputSlot (a : WilliamsAlgorithm) : Fin (tapes a+1+2+4) :=
  ((0 : Fin 2).natAdd (tapes a+1)).castAdd 4

theorem source_output (a : WilliamsAlgorithm) (ds : List Datum) (S R B k : Nat) (out : List Bool) :
    (source a ds S R B k out).tapes (outputSlot a)=out := by
  simp [source,bank,outputSlot,P1TopDownPaidReusableBody.bank,P1Closure.RawRowJoin.bank]

set_option maxHeartbeats 1000000 in
theorem hrow_words (a : WilliamsAlgorithm) (ds : List Datum) (dflt : Datum)
    (S R B cost : Nat) (wanted : List (List Bool))
    (hv : ∀ k (hk : k<ds.length),Valid a B R S ds[k])
    (hb : ∀ k (hk : k<ds.length),(ds[k]).budget a B S≤cost)
    (hwords : ds.map Datum.emit=wanted) (k : Nat) (hk : k<wanted.length) (out : List Bool) :
    ∃ r,runFrom (machine a) cost (source a ds S R B k out)=some r ∧
      r.final.heads=(source a ds S R B (k+1) (out++wanted.getD k [])).heads ∧
      r.final.tapes=(source a ds S R B (k+1) (out++wanted.getD k [])).tapes ∧ r.steps≤cost := by
  have hk' : k<ds.length := by simpa only [←hwords,List.length_map] using hk
  have he : wanted.getD k []=(ds.getD k dflt).emit := by
    rw [←hwords]
    exact C10RowFrameJoin.getD_map Datum.emit ds k dflt [] hk'
  rw [he]
  exact hrow a ds dflt S R B cost hv hb k hk' out

end NearCubicWires.P1TopDownPaidReusable
