import Proof.MachineModel.TopDownWorkspaceSelectedProgram
import Proof.CaseAnalysis.FinalOriginalFrame

/-! The actual admitted parser exit retains the original input, witness and
mode words. This enriches the same selected physical admission run by
receipt determinism; it does not execute the source a second time. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.WorkspaceSelectedOriginals
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal RepairSource.SelectedRecoveryIntegration
open WorkspaceGuardedWorker (input entry reference)
open WorkspaceSelectedAdmission (originalTapes coldCutoff preFuel capacity)
open WorkspaceSelectedProgram (finalBank lengthFlag)
noncomputable section
attribute [local irreducible] BoundedFamilySupport.actualMachine ColdFamilySupport.actualMachine
  CloseoutFinalC10ColdCacheRewind.machine WorkspaceSelectedProgram.admission
  WorkspaceSelectedAdmission.admission

def headerPort (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) (i : Fin 150) : Fin (originalTapes sources p k) :=
  (HeaderDock.old (BoundedFamily.workspace (fixedProjection sources)
    (CloseoutLanguage.selectedPCPP sources) k p.clauseDegree p.degree (capacity sources p).E) i).castAdd 1

def Originals (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) {n : Nat} (x : BitInput n) (bits : List Bool)
    (A : Fin (originalTapes sources p k) → List Bool) : Prop :=
  A (headerPort sources p k 0)=RepairOrdinary.frame (List.ofFn x) ∧
  A (headerPort sources p k 1)=RepairOrdinary.frame bits ∧
  A (headerPort sources p k 142)=[BoundedFields.symmetric bits]

theorem headerPort_val (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) (i : Fin 150) : (headerPort sources p k i).val=i.val := rfl

private theorem tapes_unique {t s : Nat} {m : Machine t s} {fuel : Nat}
    {H J J' : Fin t → Nat} {A B B' : Fin t → List Bool}
    (h : Step m fuel H A J B) (h' : Step m fuel H A J' B') : B=B' := by
  obtain ⟨r,hr,_hh,ht,_hs⟩ := h
  obtain ⟨r',hr',_hh',ht',_hs'⟩ := h'
  have same : r=r' := Option.some.inj (hr.symm.trans hr')
  exact ht.symm.trans ((congrArg (fun e => e.final.tapes) same).trans ht')

end
end NearCubicWires.P1TopDown.WorkspaceSelectedOriginals
