import Proof.Rows.Plan

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ45bee56da9f34d5a_HeaderField
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimator
open NearCubicWires.RepairSource.ProjectionNormalization
noncomputable section

def rewindSlots : Fin 3 → Fin 9 := ![0,1,2]
def scanSlots : Fin 5 → Fin 9 := ![0,3,4,5,6]
def frameSlots : Fin 4 → Fin 9 := ![0,5,7,8]
theorem rewind_injective : Function.Injective rewindSlots := by decide
theorem scan_injective : Function.Injective scanSlots := by decide
theorem frame_injective : Function.Injective frameSlots := by decide

theorem pick_rewind (i : Fin 9) : RecoveryFocus.pick rewindSlots i =
    if i=0 then some 0 else if i=1 then some 1 else if i=2 then some 2 else none := by
  fin_cases i <;> first
    | exact RecoveryFocus.pick_slot _ rewind_injective 0
    | exact RecoveryFocus.pick_slot _ rewind_injective 1
    | exact RecoveryFocus.pick_slot _ rewind_injective 2
    | decide

theorem pick_scan (i : Fin 9) : RecoveryFocus.pick scanSlots i =
    if i=0 then some 0 else if i=3 then some 1 else if i=4 then some 2
    else if i=5 then some 3 else if i=6 then some 4 else none := by
  fin_cases i <;> first
    | exact RecoveryFocus.pick_slot _ scan_injective 0
    | exact RecoveryFocus.pick_slot _ scan_injective 1
    | exact RecoveryFocus.pick_slot _ scan_injective 2
    | exact RecoveryFocus.pick_slot _ scan_injective 3
    | exact RecoveryFocus.pick_slot _ scan_injective 4
    | decide

theorem pick_frame (i : Fin 9) : RecoveryFocus.pick frameSlots i =
    if i=0 then some 0 else if i=5 then some 1 else if i=7 then some 2
    else if i=8 then some 3 else none := by
  fin_cases i <;> first
    | exact RecoveryFocus.pick_slot _ frame_injective 0
    | exact RecoveryFocus.pick_slot _ frame_injective 1
    | exact RecoveryFocus.pick_slot _ frame_injective 2
    | exact RecoveryFocus.pick_slot _ frame_injective 3
    | decide

def rewind := RecoveryFocus.machine rewindSlots CompetitorRecordRewind.machine
def scan := RecoveryFocus.machine scanSlots Scan.readyMachine
def framing := RecoveryFocus.machine frameSlots RawFrame.machine
def machine := Composition.machine rewind (Composition.machine scan framing)

def heads (row : EquationRow.Input) : Fin 9 → Nat :=
  ![(Header.stream row).length,0,0,0,0,0,0,0,0]
def input (row : EquationRow.Input) (K : Nat) : Fin 9 → List Bool :=
  ![Header.stream row,List.replicate K true,[],UnaryTemplate.tape (Scan.countFields row),
    [],[],[],[],[]]
def afterRewind (row : EquationRow.Input) (K : Nat) : Fin 9 → List Bool :=
  ![Header.stream row,List.replicate K true,List.replicate K false,
    UnaryTemplate.tape (Scan.countFields row),[],[],[],[],[]]
def afterScan (row : EquationRow.Input) (K : Nat) : Fin 9 → List Bool :=
  ![Header.stream row,List.replicate K true,List.replicate K false,
    UnaryTemplate.tape (Scan.countFields row),List.replicate row.cuts.length true,
    List.replicate (Header.stream row).length true,List.replicate (Scan.ticks row) false,[],[]]
def output (row : EquationRow.Input) (K : Nat) : Fin 9 → List Bool :=
  ![Header.stream row,List.replicate K true,List.replicate K false,
    UnaryTemplate.tape (Scan.countFields row),List.replicate row.cuts.length true,
    List.replicate (Header.stream row).length true,List.replicate (Scan.ticks row) false,
    frame (Header.stream row),List.replicate (2*(Header.stream row).length+1) false]
def budget (row : EquationRow.Input) (K : Nat) :=
  2*K+2*Scan.ticks row+4*(Header.stream row).length+10

theorem rewind_run (row : EquationRow.Input) (K : Nat) (fits : (Header.stream row).length ≤ K) :
    Step rewind (2*K+2) (heads row) (input row K) (fun _ => 0) (afterRewind row K) := by
  obtain ⟨r,run,final,_⟩:=CompetitorRecordRewind.rewind_run
    (Header.stream row) K (Header.stream row).length fits
  have base:=Step.of_run run (congrArg Configuration.heads final) (congrArg Configuration.tapes final)
  have focused:=base.dock rewindSlots rewind_injective (heads row) (input row K)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
  apply focused.congr
  · funext i;fin_cases i <;> simp [dockH,pick_rewind,CompetitorRecordRewind.cfg,heads]
  · funext i;fin_cases i <;>
      simp [install,pick_rewind,CompetitorRecordRewind.cfg,input,afterRewind]

theorem scan_run (row : EquationRow.Input) (K : Nat) :
    Step scan (2*Scan.ticks row+2) (fun _ => 0) (afterRewind row K)
      (fun _ => 0) (afterScan row K) := by
  obtain ⟨r,run,tapes,hs,_⟩:=Scan.ready row
  have base:=Step.of_run run (funext hs) tapes
  have focused:=base.dock scanSlots scan_injective (fun _ => 0) (afterRewind row K)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
  apply focused.congr
  · funext i;fin_cases i <;> simp [dockH,pick_scan]
  · funext i;fin_cases i <;>
      simp [install,pick_scan,Scan.output,afterRewind,afterScan,Header.stream]

theorem frame_run (row : EquationRow.Input) (K : Nat) :
    Step framing (4*(Header.stream row).length+4) (fun _ => 0) (afterScan row K)
      (fun _ => 0) (output row K) := by
  obtain ⟨r,run,tapes,hs,_⟩:=RawFrame.ready (Header.stream row)
  have base:=Step.of_run run (funext hs) tapes
  have focused:=base.dock frameSlots frame_injective (fun _ => 0) (afterScan row K)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
  apply focused.congr
  · funext i;fin_cases i <;> simp [dockH,pick_frame]
  · funext i;fin_cases i <;>
      simp [install,pick_frame,RawFrame.output,afterScan,output]

theorem run (row : EquationRow.Input) (K : Nat) (fits : (Header.stream row).length ≤ K) :
    Step machine (budget row K) (heads row) (input row K) (fun _ => 0) (output row K) := by
  have h:=(rewind_run row K fits).seq ((scan_run row K).seq (frame_run row K))
  have fuel:(2*K+2)+1+((2*Scan.ticks row+2)+1+(4*(Header.stream row).length+4))=budget row K := by
    unfold budget;omega
  rw [fuel] at h
  exact h

/-- One fixed outer reserve carries through the entire executed chain. -/
theorem padded_run (row : EquationRow.Input) (K : Nat)
    (fits : (Header.stream row).length ≤ K) (reserve : Fin 9 → Nat) :
    Step machine (budget row K) (heads row) (fun i => ZeroPadding.pad (reserve i) (input row K i))
      (fun _ => 0) (fun i => ZeroPadding.pad (reserve i) (output row K i)) :=
  (run row K fits).pad reserve

end
end PCJ45bee56da9f34d5a_HeaderField
