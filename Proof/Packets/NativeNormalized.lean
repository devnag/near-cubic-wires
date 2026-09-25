import Proof.Packets.NativeNormalizedData

/-! Complete native-stream to normalized support-bank execution. The same
fixed32-tape machine parses all raw rows, generates their count, returns its
operand cursors, then performs the verified exact ordered normalization. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NativeNormalized
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.RecoveryExecution

noncomputable abbrev normalize := TapeEmbedding.machine 2 NormalizedAddition.machine
noncomputable abbrev machine := Composition.machine prepare normalize
def budget (C : Nat) (P : List (List Nat)) := prepareBudget C P+1+NormalizedAddition.budget C [] (masks C P)
noncomputable def input (C : Nat) (P : List (List Nat)) := Normalize.started machine (H 0 0 1) (A C P [])

theorem run (C : Nat) (P : List (List Nat)) (hp : ∀m∈P,∀code∈m,code<C) :
    ∃ r,runFrom machine (budget C P) (input C P)=some r ∧ r.steps≤budget C P ∧
      r.final.tapes 20=(NormalizerOrder.ordered (masks C P)).flatten ∧ r.final.heads 20=0 ∧
      r.final.tapes 21=CompareMachine.word (NormalizerOrder.ordered (masks C P)).length ∧
      r.final.heads 21=1 := by
  obtain ⟨a,ha,ah,aTapes,aSteps⟩:=prepare_step C P hp
  obtain ⟨b,hb,bs,b20,bh20,b21,bh21⟩:=NormalizedAddition.run C [] (masks C P)
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
  refine ⟨_,all,?_,?_,?_,?_,?_⟩
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

end PCJ9eff70d512234a4c_Fixed.Materializer.NativeNormalized
