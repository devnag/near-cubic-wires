import Proof.MachineModel.OrdinaryMatrixScoreLeftCycle

/-! Physical assignment and stable-id increments between remaining records.
The caller must exhibit a remaining assignment, so neither word overflows. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreAdvance
open LocalBitMultitape RecoveryRootRound SignedSortKey MatrixScoreLeftCycle
open MatrixScoreWeight (zeros)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (idMode : Bool) : Fin 2 → Fin 27 := ![if idMode then 22 else 1,25]
theorem injective (mode : Bool) : Function.Injective (slots mode) := by cases mode <;> decide
def picked (mode : Bool) : Fin 27 → Option (Fin 2) := if mode then
  ![none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,some 0,none,none,some 1,none]
  else ![none,some 0,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,some 1,none]
theorem pick_slots (mode : Bool) (i : Fin 27) : RecoveryFocus.pick (slots mode) i=picked mode i := by
  cases mode <;> fin_cases i
  all_goals first
    | decide
    | exact RecoveryFocus.pick_slot (slots false) (injective false) 0
    | exact RecoveryFocus.pick_slot (slots false) (injective false) 1
    | exact RecoveryFocus.pick_slot (slots true) (injective true) 0
    | exact RecoveryFocus.pick_slot (slots true) (injective true) 1
noncomputable def bump (mode : Bool) := RecoveryFocus.machine (slots mode) FramedIncrement.machine
noncomputable def machine := Composition.machine (bump false) (bump true)
def budget (d m : ℕ) := (4*d+2)+1+(4*m+2)

theorem ready (w n c : ℕ) (hn : n+1<2^w) (hc : 2*w≤c) :
    ClockJoin.ReadyRun FramedIncrement.machine (4*w+2)
      ![frame (binary w n),zeros c] ![frame (binary w (n+1)),zeros c] := by
  obtain ⟨base,hb,h0,h1,hh,hs,_⟩ := FramedIncrement.increment_run w n c hn hc
  have hi : (Fin.addCases (m := 1) (n := 1) (motive := fun _ => List Bool)
      (fun _ => frame (binary w n)) (fun _ => List.replicate c false))=![frame (binary w n),zeros c] := by
    funext i; fin_cases i <;> rfl
  rw [hi] at hb
  refine ⟨base,hb,?_,hh,hs⟩
  funext i
  fin_cases i
  · exact h0
  · exact h1

theorem advance_run (source : List Bool) (d n c cap w x m id template returnCap : ℕ)
    (work : Fin 12 → List Bool) (driver counter out : List Bool)
    (hn : n+1<2^d) (hi : id+1<2^m) (hd : 2*d≤c) (hm : 2*m≤c) :
    ∃ actual,runFrom machine (budget d m)
      (RecoveryCalls.restarted machine (heads out.length)
        (tapes source (frame (binary d n)) d c cap w x m id template work driver counter out returnCap))=some actual ∧
      actual.final.heads=heads out.length ∧
      actual.final.tapes=tapes source (frame (binary d (n+1))) d c cap w x m (id+1) template work driver counter out returnCap ∧
      actual.steps≤budget d m := by
  let ambient := tapes source (frame (binary d n)) d c cap w x m id template work driver counter out returnCap
  let afterAssignment := tapes source (frame (binary d (n+1))) d c cap w x m id template work driver counter out returnCap
  obtain ⟨first,hf,fh,ft,fs⟩ := CompetitorReusableDecision.bounded_focused_run (slots false) (injective false)
    FramedIncrement.machine _ _ (ready d n c hn hd) (heads out.length) ambient
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  have firstTapes : first.final.tapes=afterAssignment := by
    rw [ft]
    funext i
    fin_cases i <;> simp [install,pick_slots,picked,ambient,afterAssignment,tapes,MatrixScoreRecordDock.tapes,
      MatrixScoreLeftFields.tapes,MatrixScoreFoldEntry.tapes,Fin.addCases]
  obtain ⟨last,hl,lh,lt,ls⟩ := CompetitorReusableDecision.bounded_focused_run (slots true) (injective true)
    FramedIncrement.machine _ _ (ready m id c hi hm) (heads out.length) afterAssignment
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  have hiRun : Composition.restart first.final (bump true).start=
      RecoveryCalls.restarted (bump true) (heads out.length) afterAssignment := by
    apply configuration_ext
    · rfl
    · exact fh
    · exact firstTapes
  change runFrom (bump true) (4*m+2) (RecoveryCalls.restarted (bump true) (heads out.length) afterAssignment)=some last at hl
  rw [← hiRun] at hl
  have joined := Composition.run_join (bump false) (bump true) (4*d+2) (4*m+2) _ first last hf hl
  refine ⟨Composition.joinedReceipt first last,joined,lh,?_,?_⟩
  · change last.final.tapes=_
    rw [lt]
    funext i
    fin_cases i <;> simp [install,pick_slots,picked,afterAssignment,tapes,MatrixScoreRecordDock.tapes,
      MatrixScoreLeftFields.tapes,MatrixScoreFoldEntry.tapes,Fin.addCases]
  · change first.steps+1+last.steps≤_
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixScoreAdvance
