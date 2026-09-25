import Proof.Packets.NormalizedMultiplyData
import Proof.Packets.NormalizerRetention

/-! One actual fixed multiplication pipeline: enumerate all support unions,
produce their count, then compute exact ordered parity normalization. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NormalizedMultiply
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding

theorem run_retained (B : Nat) (left right : List (List Bool))
    (hl : ∀ bits∈left,bits.length=B) (hr : ∀ bits∈right,bits.length=B) :
    ∃ r,runFrom machine (budget B left right) (entry B left right)=some r ∧
      r.steps≤budget B left right ∧
      r.final.tapes 20=(NormalizerOrder.ordered (MaskProduct.unions left right)).flatten ∧
      r.final.heads 20=0 ∧
      r.final.tapes 21=CompareMachine.word (NormalizerOrder.ordered (MaskProduct.unions left right)).length ∧
      r.final.heads 21=1 ∧
      r.final.tapes 13=UnaryTemplate.tape (2*B+3) ∧
      r.final.tapes 24=UnaryTemplate.tape B ∧
      r.final.tapes 25=left.flatten ∧
      r.final.tapes 28=CompareMachine.word left.length := by
  obtain ⟨a,ha,ah,adata,has⟩ := product_step B left right hl hr
  obtain ⟨b,hb,hbs,bout,bhead,bcount,bcountHead,bWidth⟩ :=
    NormalizeCold.run_width B (MaskProduct.unions left right) (unions_width B left right hl hr)
  have h := TapeEmbedding.run_embed NormalizeCold.machine extraHeads (extras B left right) _ _ b hb
  have join : Composition.restart a.final normalizeMachine.start=
      TapeEmbedding.config extraHeads (extras B left right) (NormalizeCold.entry B (MaskProduct.unions left right)) := by
    apply configuration_ext
    · rfl
    · exact ah
    · exact adata
  rw [←join] at h
  have result := Composition.run_join productMachine normalizeMachine _ _ _ a _ ha h
  refine ⟨_,result,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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

  · change (TapeEmbedding.receipt extraHeads (extras B left right) b).final.tapes 13=_
    simpa [TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases] using bWidth
  · change (TapeEmbedding.receipt extraHeads (extras B left right) b).final.tapes 24=_
    simp [TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,extras]
  · change (TapeEmbedding.receipt extraHeads (extras B left right) b).final.tapes 25=_
    simp [TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,extras]
  · change (TapeEmbedding.receipt extraHeads (extras B left right) b).final.tapes 28=_
    simp [TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,extras]

end PCJ9eff70d512234a4c_Fixed.Materializer.NormalizedMultiply
