import Proof.Packets.PacketsXWalkLiteralProducedMajorityData

/-! The column may be filled between the scalar and arithmetic stages:
its bank is outside the scalar producer's entire physical footprint. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralProducedMajority
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer Completion
noncomputable section

theorem update_install_other {t u : Nat} (slots : Fin t→Fin u) (A : Fin u→List Bool)
    (localData : Fin t→List Bool) (k : Fin u) (word : List Bool) (away : ∀j,slots j≠k) :
    Function.update (install slots A localData) k word=
      install slots (Function.update A k word) localData := by
  funext i
  by_cases hi:i=k
  · subst i
    rw [Function.update_self,install_other _ _ _ _ away,Function.update_self]
  · rw [Function.update_of_ne hi]
    unfold install
    cases hp:RecoveryFocus.pick slots i with
    | none=>exact (Function.update_of_ne hi word A).symm
    | some j=>rfl

theorem cold_input_update (C R n : Nat) (before after : List Bool) :
    Function.update (MajorityComplete.Cold.input C R n before) 44 after=
      MajorityComplete.Cold.input C R n after := by
  unfold MajorityComplete.Cold.input Fin.append
  change Function.update (Fin.addCases (m:=137) (n:=41) (motive:=fun _=>List Bool)
    (fun i=>if i=44 then before else []) _) ((44 : Fin 137).castAdd 41) after=_
  rw [PhysicalAppendUpdate.left]
  congr 1
  funext i
  by_cases hi:i=44
  · subst i;simp
  · simp [hi]

theorem cold_scalar_update (C R n : Nat) (before after : List Bool) :
    Function.update (MajorityComplete.Cold.afterScalar C R n before) 44 after=
      MajorityComplete.Cold.afterScalar C R n after := by
  rw [MajorityComplete.Cold.afterScalar,update_install_other _ _ _ _ _ (by decide),cold_input_update]
  rfl

theorem cold_scalar_source (C R n : Nat) (source : List Bool) :
    MajorityComplete.Cold.afterScalar C R n source 44=source := by
  rw [MajorityComplete.Cold.afterScalar,install_other _ _ _ _ (by decide)]
  rfl

theorem zero_cold_disjoint : ∀i j,zeroSlots i≠coldSlots j := by decide

theorem column_cold_overlap : ∀i j,columnSlots i=coldSlots j→
    (i=6 ∧ j=44) ∨ (i=7 ∧ j=146) := by decide

theorem cold_majority (i : Fin 137) : coldSlots (MajorityComplete.Cold.arenaSlots i)=majoritySlots i := by
  simp only [coldSlots,MajorityComplete.Cold.arenaSlots,Fin.addCases_left]

end
end Theorem25Completion.WalkLiteralProducedMajority
