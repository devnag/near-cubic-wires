import Proof.Packets.NativeNormalized
import Proof.Packets.NormalizedAdditionRetained

/-! Retained actual width and native source at the normalized converter's
exit. These are consequences of the executed component receipts. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NativeNormalized
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.RecoveryExecution

theorem run_retained (C : Nat) (P : List (List Nat)) (hp : ∀m∈P,∀code∈m,code<C) :
    ∃ r,runFrom machine (budget C P) (input C P)=some r ∧ r.steps≤budget C P ∧
      r.final.tapes 20=(NormalizerOrder.ordered (masks C P)).flatten ∧ r.final.heads 20=0 ∧
      r.final.tapes 21=CompareMachine.word (NormalizerOrder.ordered (masks C P)).length ∧
      r.final.heads 21=1 ∧
      r.final.tapes 13=UnaryTemplate.tape (2*C+3) ∧
      r.final.tapes 24=UnaryTemplate.tape C ∧
      r.final.tapes 30=ExtIncidence.stream P ∧
      r.final.tapes 31=List.replicate C false := by
  obtain ⟨a,ha,ah,aTapes,aSteps⟩:=prepare_step C P hp
  obtain ⟨b,hb,bs,b20,bh20,b21,bh21,b13,b24,_,_⟩:=NormalizedAddition.run_retained C [] (masks C P)
    (by simp) (masks_width C P)
  have normal:=TapeEmbedding.run_embed NormalizedAddition.machine
    (![ (ExtIncidence.stream P).length,0] : Fin 2→Nat) (extra C P) _ _ b hb
  have join : Composition.restart a.final normalize.start=
      TapeEmbedding.config (![(ExtIncidence.stream P).length,0] : Fin 2→Nat) (extra C P)
        (NormalizedAddition.entry C [] (masks C P)) := by
    apply configuration_ext
    · rfl
    · rw [Composition.restart,ah]
      funext i;fin_cases i <;> rfl
    · rw [Composition.restart,aTapes]
      rfl
  rw [←join] at normal
  have all:=Composition.run_join prepare normalize _ _ _ a _ ha normal
  refine ⟨_,all,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change a.steps+1+b.steps≤budget C P
    unfold budget
    omega
  · change (TapeEmbedding.receipt (![ (ExtIncidence.stream P).length,0] : Fin 2→Nat) (extra C P) b).final.tapes 20=_
    simpa [TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases] using b20
  · change (TapeEmbedding.receipt (![ (ExtIncidence.stream P).length,0] : Fin 2→Nat) (extra C P) b).final.heads 20=0
    simpa [TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases] using bh20
  · change (TapeEmbedding.receipt (![ (ExtIncidence.stream P).length,0] : Fin 2→Nat) (extra C P) b).final.tapes 21=_
    simpa [TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases] using b21
  · change (TapeEmbedding.receipt (![ (ExtIncidence.stream P).length,0] : Fin 2→Nat) (extra C P) b).final.heads 21=1
    simpa [TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases] using bh21

  · change (TapeEmbedding.receipt (![(ExtIncidence.stream P).length,0] : Fin 2→Nat) (extra C P) b).final.tapes 13=_
    simpa [TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases] using b13
  · change (TapeEmbedding.receipt (![(ExtIncidence.stream P).length,0] : Fin 2→Nat) (extra C P) b).final.tapes 24=_
    simpa [TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases] using b24
  · change (TapeEmbedding.receipt (![(ExtIncidence.stream P).length,0] : Fin 2→Nat) (extra C P) b).final.tapes 30=_
    rfl
  · change (TapeEmbedding.receipt (![(ExtIncidence.stream P).length,0] : Fin 2→Nat) (extra C P) b).final.tapes 31=_
    rfl

end PCJ9eff70d512234a4c_Fixed.Materializer.NativeNormalized
