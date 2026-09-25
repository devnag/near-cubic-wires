import Proof.MachineModel.OrdinaryMatrixBatchGateClear

/-! Paid assignment/id restoration after the simultaneous gate-work clear.
The independent retained M-zero word is the actual source of the id reset. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchGateReset
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey MatrixScoreBatch
open MatrixScoreLeftLoop (C)
open MatrixScoreReusableRanks (D)
open MatrixBatchGateClear (tapes heads)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (idMode : Bool) : Fin 4 → Fin 48 := ![if idMode then 43 else 28,if idMode then 22 else 1,25,16]
theorem slots_injective (mode : Bool) : Function.Injective (slots mode) := by cases mode <;> decide
def picked (idMode : Bool) : Fin 48 → Option (Fin 4) := if idMode then
  ![none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,some 3,none,none,none,none,none,some 1,
    none,none,some 2,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,some 0,none,none,none,none]
  else ![none,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,some 3,none,none,none,none,none,none,
    none,none,some 2,none,none,some 0,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem pick_slots (mode : Bool) (i : Fin 48) : RecoveryFocus.pick (slots mode) i=picked mode i := by
  cases mode <;> fin_cases i
  all_goals first
    | decide
    | exact RecoveryFocus.pick_slot (slots false) (slots_injective false) 0
    | exact RecoveryFocus.pick_slot (slots false) (slots_injective false) 1
    | exact RecoveryFocus.pick_slot (slots false) (slots_injective false) 2
    | exact RecoveryFocus.pick_slot (slots false) (slots_injective false) 3
    | exact RecoveryFocus.pick_slot (slots true) (slots_injective true) 0
    | exact RecoveryFocus.pick_slot (slots true) (slots_injective true) 1
    | exact RecoveryFocus.pick_slot (slots true) (slots_injective true) 2
    | exact RecoveryFocus.pick_slot (slots true) (slots_injective true) 3
noncomputable def copy (mode : Bool) := RecoveryFocus.machine (slots mode) copyMachine
def width (r : Request) (mode : Bool) := if mode then r.M else r.d
def nextAssignment (mode : Bool) (assignment : ℕ) := if mode then assignment else 0
def nextId (mode : Bool) (id : ℕ) := if mode then 0 else id
def copyOutput (r : Request) (mode : Bool) : Fin 4 → List Bool :=
  ![frame (binary (width r mode) 0),frame (binary (width r mode) 0),
    List.replicate (C r) false,List.replicate (C r+1) false]

theorem install_copy (r : Request) (mode : Bool) (assignment id cap : ℕ) (source out : List Bool)
    (backing : Fin 31 → List Bool) :
    install (slots mode) (tapes r assignment id cap source out backing) (copyOutput r mode)=
      tapes r (nextAssignment mode assignment) (nextId mode id) cap source out backing := by
  funext i
  cases mode <;> fin_cases i <;>
    simp [install,pick_slots,picked,copyOutput,width,nextAssignment,nextId,tapes,
      MatrixBatchGateClear.pick_scratch,MatrixBatchGateClear.scratchPick,MatrixBatchGateClear.stable]

theorem copy_run (r : Request) (mode : Bool) (assignment id cap pos : ℕ) (source out : List Bool)
    (backing : Fin 31 → List Bool) :
    ∃ actual,runFrom (copy mode) (8*width r mode+8)
      (RecoveryCalls.restarted (copy mode) (heads pos out.length) (tapes r assignment id cap source out backing))=some actual ∧
      actual.final.heads=heads pos out.length ∧
      actual.final.tapes=tapes r (nextAssignment mode assignment) (nextId mode id) cap source out backing ∧
      actual.steps≤8*width r mode+8 := by
  have hc : 4*width r mode+2≤C r := by
    cases mode
    · have hm := common_width r
      simp only [width,Bool.false_eq_true,ite_false,C]
      omega
    · simp only [width,ite_true,C]
      omega
  have ready := MatrixScoreHalvesReset.ready (width r mode) 0 (if mode then id else assignment) (C r) hc
  obtain ⟨actual,ha,ah,atapes,as⟩ := CompetitorReusableDecision.bounded_focused_run (slots mode) (slots_injective mode)
    copyMachine _ _ ready (heads pos out.length) (tapes r assignment id cap source out backing)
    (by intro i; cases mode <;> fin_cases i <;> rfl)
    (by intro i; cases mode <;> fin_cases i <;>
      simp [slots,width,tapes,install,MatrixBatchGateClear.pick_scratch,MatrixBatchGateClear.scratchPick,MatrixBatchGateClear.stable,
        MatrixScoreWeight.zeros])
  exact ⟨actual,ha,ah,atapes.trans (install_copy r mode assignment id cap source out backing),as⟩

noncomputable def resets := Composition.machine (copy false) (copy true)
noncomputable def machine := Composition.machine MatrixBatchGateClear.machine resets
def budget (r : Request) := (2*D r+4)+1+((8*r.d+8)+1+(8*r.M+8))
noncomputable def input (r : Request) (assignment id cap pos : ℕ) (source out : List Bool)
    (backing : Fin 31 → List Bool) :=
  Composition.leftConfig 12 (MatrixBatchGateClear.input r assignment id cap pos source out backing)

theorem prepare_run (r : Request) (assignment id cap pos : ℕ) (source out : List Bool)
    (backing : Fin 31 → List Bool) (hb : ∀ i,(backing i).length≤D r) :
    ∃ actual,runFrom machine (budget r) (input r assignment id cap pos source out backing)=some actual ∧
      actual.final.heads=heads pos out.length ∧
      actual.final.tapes=tapes r 0 0 (max cap (D r+1)) source out (fun _ => List.replicate (D r) false) ∧
      actual.steps≤budget r := by
  obtain ⟨cleared,hc,ch,ct,cs⟩ := MatrixBatchGateClear.clear_run r assignment id cap pos source out backing hb
  obtain ⟨left,hl,lh,lt,ls⟩ := copy_run r false assignment id (max cap (D r+1)) pos source out (fun _ => List.replicate (D r) false)
  obtain ⟨right,hr,rh,rt,rs⟩ := copy_run r true 0 id (max cap (D r+1)) pos source out (fun _ => List.replicate (D r) false)
  have hi : Composition.restart left.final (copy true).start=
      RecoveryCalls.restarted (copy true) (heads pos out.length)
        (tapes r 0 id (max cap (D r+1)) source out (fun _ => List.replicate (D r) false)) := by
    apply configuration_ext
    · rfl
    · exact lh
    · exact lt
  rw [←hi] at hr
  have htail := Composition.run_join (copy false) (copy true) _ _ _ left right hl hr
  have he : Composition.restart cleared.final resets.start=
      Composition.leftConfig 6 (RecoveryCalls.restarted (copy false) (heads pos out.length)
        (tapes r assignment id (max cap (D r+1)) source out (fun _ => List.replicate (D r) false))) := by
    apply configuration_ext
    · rfl
    · exact ch
    · exact ct
  rw [←he] at htail
  have joined := Composition.run_join MatrixBatchGateClear.machine resets _ _ _ cleared (Composition.joinedReceipt left right) hc htail
  refine ⟨Composition.joinedReceipt cleared (Composition.joinedReceipt left right),joined,rh,rt,?_⟩
  change cleared.steps+1+(left.steps+1+right.steps)≤_
  unfold budget
  simp only [width,Bool.false_eq_true,ite_false,ite_true] at ls rs
  omega

end NearCubicWires.RepairOrdinary.MatrixBatchGateReset
