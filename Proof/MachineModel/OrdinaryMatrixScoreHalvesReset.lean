import Proof.MachineModel.OrdinaryMatrixScoreLeftEnumeration

/-! Paid left-to-right boundary: copy the retained native zero assignment
and U template over the final left assignment/id. The output cursor and
both loop sentinels stay in place. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreHalvesReset
open LocalBitMultitape RecoveryRootRound SignedSortKey
open MatrixScoreWeight (zeros)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (outlen : ℕ) : Fin 29 → ℕ :=
  Fin.addCases (m := 28) (n := 1) (motive := fun _ => ℕ)
    (MatrixScoreLeftEnumeration.heads (MatrixScoreLeftCycle.heads outlen) 1) (fun _ => 0)
def tapes (source : List Bool) (d n c w x m id template U returnCap : ℕ)
    (work : Fin 12 → List Bool) (driver counter out : List Bool) : Fin 29 → List Bool :=
  Fin.addCases (m := 28) (n := 1) (motive := fun _ => List Bool)
    (MatrixScoreLeftEnumeration.tapes
      (MatrixScoreLeftCycle.tapes source (frame (binary d n)) d c (c+1) w x m id template work driver counter out returnCap) U)
    (fun _ => frame (binary d 0))
def slots (idMode : Bool) : Fin 4 → Fin 29 := ![if idMode then 23 else 28,if idMode then 22 else 1,25,16]
theorem injective (mode : Bool) : Function.Injective (slots mode) := by cases mode <;> decide
def picked (mode : Bool) : Fin 29 → Option (Fin 4) := if mode then
  ![none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,some 3,none,none,none,none,none,some 1,some 0,none,some 2,none,none,none]
  else ![none,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,some 3,none,none,none,none,none,none,none,none,some 2,none,none,some 0]
theorem pick_slots (mode : Bool) (i : Fin 29) : RecoveryFocus.pick (slots mode) i=picked mode i := by
  cases mode <;> fin_cases i
  all_goals first
    | decide
    | exact RecoveryFocus.pick_slot (slots false) (injective false) 0
    | exact RecoveryFocus.pick_slot (slots false) (injective false) 1
    | exact RecoveryFocus.pick_slot (slots false) (injective false) 2
    | exact RecoveryFocus.pick_slot (slots false) (injective false) 3
    | exact RecoveryFocus.pick_slot (slots true) (injective true) 0
    | exact RecoveryFocus.pick_slot (slots true) (injective true) 1
    | exact RecoveryFocus.pick_slot (slots true) (injective true) 2
    | exact RecoveryFocus.pick_slot (slots true) (injective true) 3
noncomputable def copy (mode : Bool) := RecoveryFocus.machine (slots mode) copyMachine
noncomputable def machine := Composition.machine (copy false) (copy true)
def budget (d m : ℕ) := (8*d+8)+1+(8*m+8)

theorem ready (w a b c : ℕ) (hc : 4*w+2≤c) :
    ClockJoin.ReadyRun copyMachine (8*w+8)
      ![frame (binary w a),frame (binary w b),zeros c,zeros (c+1)]
      ![frame (binary w a),frame (binary w a),zeros c,zeros (c+1)] := by
  have base := copy_ready (binary w a) (frame (binary w b)) c (c+1) (by simp [frame_length,binary_length])
  simp only [binary_length] at base
  rw [max_eq_left (by omega : 2*w+1≤c),max_eq_left (by omega : 4*w+3≤c+1)] at base
  obtain ⟨actual,hr,ht,hh,hs⟩ := base
  exact ⟨actual,hr,ht,hh,hs.le⟩

theorem reset_run (source : List Bool) (d n c w x m id template U returnCap : ℕ)
    (work : Fin 12 → List Bool) (driver counter out : List Bool)
    (hd : 4*d+2≤c) (hm : 4*m+2≤c) :
    ∃ actual,runFrom machine (budget d m)
      (RecoveryCalls.restarted machine (heads out.length)
        (tapes source d n c w x m id template U returnCap work driver counter out))=some actual ∧
      actual.final.heads=heads out.length ∧
      actual.final.tapes=tapes source d 0 c w x m template template U returnCap work driver counter out ∧
      actual.steps≤budget d m := by
  let ambient := tapes source d n c w x m id template U returnCap work driver counter out
  let afterAssignment := tapes source d 0 c w x m id template U returnCap work driver counter out
  obtain ⟨first,hf,fh,ft,fs⟩ := CompetitorReusableDecision.bounded_focused_run (slots false) (injective false)
    copyMachine _ _ (ready d 0 n c hd) (heads out.length) ambient
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  have firstTapes : first.final.tapes=afterAssignment := by
    rw [ft]
    funext i
    fin_cases i <;> simp [install,pick_slots,picked,ambient,afterAssignment,tapes,MatrixScoreLeftEnumeration.tapes,
      MatrixScoreLeftCycle.tapes,MatrixScoreRecordDock.tapes,MatrixScoreLeftFields.tapes,MatrixScoreFoldEntry.tapes,Fin.addCases]
  obtain ⟨last,hl,lh,lt,ls⟩ := CompetitorReusableDecision.bounded_focused_run (slots true) (injective true)
    copyMachine _ _ (ready m template id c hm) (heads out.length) afterAssignment
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  have hi : Composition.restart first.final (copy true).start=
      RecoveryCalls.restarted (copy true) (heads out.length) afterAssignment := by
    apply configuration_ext
    · rfl
    · exact fh
    · exact firstTapes
  change runFrom (copy true) (8*m+8) (RecoveryCalls.restarted (copy true) (heads out.length) afterAssignment)=some last at hl
  rw [← hi] at hl
  have joined := Composition.run_join (copy false) (copy true) _ _ _ first last hf hl
  refine ⟨Composition.joinedReceipt first last,joined,lh,?_,?_⟩
  · change last.final.tapes=_
    rw [lt]
    funext i
    fin_cases i <;> simp [install,pick_slots,picked,afterAssignment,tapes,MatrixScoreLeftEnumeration.tapes,
      MatrixScoreLeftCycle.tapes,MatrixScoreRecordDock.tapes,MatrixScoreLeftFields.tapes,MatrixScoreFoldEntry.tapes,Fin.addCases]
  · change first.steps+1+last.steps≤_
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixScoreHalvesReset
