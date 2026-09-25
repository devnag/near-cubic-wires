import Proof.Packets.NormalizedAdditionData

/-! One actual fixed addition pipeline: reverse-frame the left bank and frame the right bank,
produce their count, then compute exact ordered parity normalization. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NormalizedAddition
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding

theorem run (B : Nat) (left right : List (List Bool))
    (hl : ∀ bits∈left,bits.length=B) (hr : ∀ bits∈right,bits.length=B) :
    ∃ r,runFrom machine (budget B left right) (entry B left right)=some r ∧
      r.steps≤budget B left right ∧
      r.final.tapes 20=(NormalizerOrder.ordered (left.reverse++right)).flatten ∧
      r.final.heads 20=0 ∧
      r.final.tapes 21=CompareMachine.word (NormalizerOrder.ordered (left.reverse++right)).length ∧
      r.final.heads 21=1 := by
  obtain ⟨a,ha,ah,adata,has⟩ := addition_step B left right hl hr
  obtain ⟨b,hb,hbs,bout,bhead,bcount,bcountHead⟩ :=
    NormalizeCold.run B (left.reverse++right) (sum_width B left right hl hr)
  have h := TapeEmbedding.run_embed NormalizeCold.machine extraHeads (extras B left right) _ _ b hb
  have join : Composition.restart a.final normalizeMachine.start=
      TapeEmbedding.config extraHeads (extras B left right) (NormalizeCold.entry B (left.reverse++right)) := by
    apply configuration_ext
    · rfl
    · exact ah
    · exact adata
  rw [←join] at h
  have result := Composition.run_join additionMachine normalizeMachine _ _ _ a _ ha h
  refine ⟨_,result,?_,?_,?_,?_,?_⟩
  · change a.steps+1+b.steps≤budget B left right
    unfold budget
    omega
  · change (TapeEmbedding.receipt extraHeads (extras B left right) b).final.tapes 20=_
    simpa [TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases] using bout
  · change (TapeEmbedding.receipt extraHeads (extras B left right) b).final.heads 20=0
    simpa [TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases] using bhead
  · change (TapeEmbedding.receipt extraHeads (extras B left right) b).final.tapes 21=_
    simpa [TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases] using bcount
  · change (TapeEmbedding.receipt extraHeads (extras B left right) b).final.heads 21=1
    simpa [TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases] using bcountHead

end PCJ9eff70d512234a4c_Fixed.Materializer.NormalizedAddition
