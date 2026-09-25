import Proof.Packets.WindowSeedBody

/-! The actual raw level is derived from the retained successor tag.
Both old private allocations are cleared; the original tag survives and the
temporary counter is erased after conversion. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ModeLevelRaw
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open WindowSeed (source)

def A (R level : Nat) (raw temp : List Bool) : Fin 5→List Bool :=
  ![source R (level+1),raw,temp,List.replicate R true,List.replicate (R+3) false]
def zero (R : Nat) := List.replicate R false
def clearSlots : Fin 4→Fin 5 := ![1,2,3,4]
def copySlots : Fin 4→Fin 5 := ![0,2,3,4]
def predSlots : Fin 1→Fin 5 := ![2]
def rawSlots : Fin 3→Fin 5 := ![2,1,4]
def lastSlots : Fin 3→Fin 5 := ![2,3,4]
noncomputable def clear := RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 2)
noncomputable def copy := RecoveryFocus.machine copySlots WindowSeed.copy
noncomputable def pred := RecoveryFocus.machine predSlots WindowSeed.countPred
noncomputable def raw := RecoveryFocus.machine rawSlots WindowSeed.raw
noncomputable def last := RecoveryFocus.machine lastSlots (RecoveryScratchErase.resetMachine 1)
noncomputable def machine := Composition.machine clear (Composition.machine copy
  (Composition.machine pred (Composition.machine raw last)))
def budget (R level : Nat) := 6*R+4*level+31

theorem clear_run (R level : Nat) (oldRaw oldTemp : List Bool)
    (hr : oldRaw.length≤R) (ht : oldTemp.length≤R) :
    Step clear (2*R+4) (fun _=>0) (A R level oldRaw oldTemp)
      (fun _=>0) (A R level (zero R) (zero R)) := by
  have h:=Step.of_ready (RecoveryScratchErase.erase_ready R (R+3)
    (![oldRaw,oldTemp] : Fin 2→List Bool) (by intro i;fin_cases i <;>assumption))
  have hm:max (R+3) (R+1)=R+3:=by omega
  rw [hm] at h
  apply PhysicalFocusBoundary.focus h clearSlots (by decide) (fun _=>0) (fun _=>0) _ _
  · intro i;rfl
  · intro i;fin_cases i <;>rfl
  · intro i;rfl
  · intro i;fin_cases i <;>rfl
  · intro i away;fin_cases i <;>first | exact ⟨rfl,rfl⟩ | exact False.elim (away 0 rfl) | exact False.elim (away 1 rfl)

theorem copy_run (R level : Nat) (hcap : level+2≤R) :
    Step copy (2*R+4) (fun _=>0) (A R level (zero R) (zero R))
      (fun _=>0) (A R level (zero R) (source R (level+1))) := by
  have h:=WindowSeed.copy_run R (source R (level+1))
    (by simp [source,ZeroPadding.pad_length,CompareMachine.word,hcap])
  apply PhysicalFocusBoundary.focus h copySlots (by decide) (fun _=>0) (fun _=>0) _ _
  · intro i;rfl
  · intro i;fin_cases i <;>rfl
  · intro i;rfl
  · intro i;fin_cases i <;>simp [WindowSeed.copyData,A,copySlots,source,WindowSeed.pad_idem]
  · intro i away;fin_cases i <;>first | exact ⟨rfl,rfl⟩ | exact False.elim (away 1 rfl)

theorem pred_run (R level : Nat) (hcap : level+2≤R) :
    Step pred (2*(level+1)+7) (fun _=>0) (A R level (zero R) (source R (level+1)))
      (fun _=>0) (A R level (zero R) (source R level)) := by
  apply PhysicalFocusBoundary.focus (WindowSeed.count_pred_run R (level+1) hcap)
    predSlots (by decide) (fun _=>0) (fun _=>0) _ _
  · intro i;rfl
  · intro i;fin_cases i;rfl
  · intro i;rfl
  · intro i;fin_cases i;simp [A,predSlots]
  · intro i away;fin_cases i <;>first | exact ⟨rfl,rfl⟩ | exact False.elim (away 0 rfl)

theorem raw_run (R level : Nat) (hcap : level+2≤R) :
    Step raw (2*level+6) (fun _=>0) (A R level (zero R) (source R level))
      (fun _=>0) (A R level (ZeroPadding.pad R (List.replicate level true)) (source R level)) := by
  apply PhysicalFocusBoundary.focus (WindowSeed.raw_run R level (by omega))
    rawSlots (by decide) (fun _=>0) (fun _=>0) _ _
  · intro i;rfl
  · intro i;fin_cases i <;>simp [A,rawSlots,WindowSeed.rawData,ZeroPadding.pad,zero]
  · intro i;rfl
  · intro i;fin_cases i <;>rfl
  · intro i away;fin_cases i <;>first | exact ⟨rfl,rfl⟩ | exact False.elim (away 1 rfl)

theorem last_run (R level : Nat) (hcap : level+2≤R) :
    Step last (2*R+4) (fun _=>0) (A R level (ZeroPadding.pad R (List.replicate level true)) (source R level))
      (fun _=>0) (A R level (ZeroPadding.pad R (List.replicate level true)) (zero R)) := by
  have h:=Step.of_ready (RecoveryScratchErase.erase_ready R (R+3)
    (fun _ : Fin 1=>source R level)
    (by intro i;simp [source,ZeroPadding.pad_length,CompareMachine.word];omega))
  have hm:max (R+3) (R+1)=R+3:=by omega
  rw [hm] at h
  apply PhysicalFocusBoundary.focus h lastSlots (by decide) (fun _=>0) (fun _=>0) _ _
  · intro i;rfl
  · intro i;fin_cases i <;>rfl
  · intro i;rfl
  · intro i;fin_cases i <;>rfl
  · intro i away;fin_cases i <;>first | exact ⟨rfl,rfl⟩ | exact False.elim (away 0 rfl)

theorem run (R level : Nat) (oldRaw oldTemp : List Bool)
    (hr : oldRaw.length≤R) (ht : oldTemp.length≤R) (hcap : level+2≤R) :
    Step machine (budget R level) (fun _=>0) (A R level oldRaw oldTemp)
      (fun _=>0) (A R level (ZeroPadding.pad R (List.replicate level true)) (zero R)) := by
  have h:=(clear_run R level oldRaw oldTemp hr ht).seq ((copy_run R level hcap).seq
    ((pred_run R level hcap).seq ((raw_run R level hcap).seq (last_run R level hcap))))
  have hf : (2*R+4)+1+((2*R+4)+1+((2*(level+1)+7)+1+((2*level+6)+1+(2*R+4))))=
      budget R level := by unfold budget;omega
  simpa only [machine,hf] using h

end PCJ9eff70d512234a4c_Fixed.Materializer.ModeLevelRaw
