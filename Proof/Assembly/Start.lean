import Proof.Assembly.Loop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ93d4cfe17dc847a3.Start
open NearCubicWires LocalBitMultitape RepairOrdinary RecoveryExecution ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
open RepairRepresentation RecoveryRootRound PCJc4297ab269d8423a_Source

def picked : Fin 14 → Option (Fin 8) :=
  ![none,some 0,some 1,some 7,some 3,some 2,some 4,some 5,none,none,none,none,none,some 6]
theorem pick_slots (i : Fin 14) : RecoveryFocus.pick Program.initSlots i = picked i := by
  fin_cases i
  all_goals first
    | decide
    | exact RecoveryFocus.pick_slot Program.initSlots Program.initSlots_injective 0
    | exact RecoveryFocus.pick_slot Program.initSlots Program.initSlots_injective 1
    | exact RecoveryFocus.pick_slot Program.initSlots Program.initSlots_injective 2
    | exact RecoveryFocus.pick_slot Program.initSlots Program.initSlots_injective 3
    | exact RecoveryFocus.pick_slot Program.initSlots Program.initSlots_injective 4
    | exact RecoveryFocus.pick_slot Program.initSlots Program.initSlots_injective 5
    | exact RecoveryFocus.pick_slot Program.initSlots Program.initSlots_injective 6
    | exact RecoveryFocus.pick_slot Program.initSlots Program.initSlots_injective 7

noncomputable def midH (d : MaskData) := dockH Program.initSlots (fun _ => 0)
  (Init.finished d.q d.K (CompareMachine.word d.m)).heads
noncomputable def midA (d : MaskData) := install Program.initSlots (d.input 9)
  (Init.finished d.q d.K (CompareMachine.word d.m)).tapes

theorem initial_heads (d : MaskData) :
    dockH Program.initSlots (fun _ => 0) (Init.initial d.q d.K (CompareMachine.word d.m)).heads =
      fun _ => 0 := by
  funext i
  unfold dockH
  split <;> rfl

theorem initial_bank (d : MaskData) :
    install Program.initSlots (d.input 9) (Init.initial d.q d.K (CompareMachine.word d.m)).tapes = d.input 9 := by
  funext i
  fin_cases i <;> simp [install,pick_slots,picked,Init.initial,MaskData.input]

theorem init_step (d : MaskData) :
    Step (RecoveryFocus.machine Program.initSlots Init.machine) (4*d.q+5)
      (fun _ => 0) (d.input 9) (midH d) (midA d) := by
  obtain ⟨r,hr,hf,_⟩ := Init.initializer_run d.q d.K (CompareMachine.word d.m)
  have h := (Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)).focus
    Program.initSlots Program.initSlots_injective (fun _ => 0) (d.input 9)
  have hh : dockH Program.initSlots (fun _ => 0) (fun _ => 0) = (fun _ => 0) := initial_heads d
  rw [hh,initial_bank] at h
  exact h

theorem setup_heads (d : MaskData) :
    (applyAction (⟨0,midH d,midA d⟩ : Configuration 14 2)
      ⟨1,(fun i => if i.val=8 ∨ i.val=9 ∨ i.val=10 ∨ i.val=11 then some false else none),
        (fun i => if i.val=1 ∨ i.val=8 ∨ i.val=11 then .right else .stay)⟩).heads =
      (RepeatMachine.cfg 0 (Loop.state d 0 []) d.q 1).heads := by
  funext i
  fin_cases i <;> simp [applyAction,midH,dockH,pick_slots,picked,Init.finished,
    RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Loop.state,State.heads,HeadMove.apply,Fin.addCases]

theorem setup_bank (d : MaskData) :
    (applyAction (⟨0,midH d,midA d⟩ : Configuration 14 2)
      ⟨1,(fun i => if i.val=8 ∨ i.val=9 ∨ i.val=10 ∨ i.val=11 then some false else none),
        (fun i => if i.val=1 ∨ i.val=8 ∨ i.val=11 then .right else .stay)⟩).tapes =
      (RepeatMachine.cfg 0 (Loop.state d 0 []) d.q 1).tapes := by
  funext i
  fin_cases i <;> simp [applyAction,midH,midA,dockH,install,pick_slots,picked,Init.finished,
    RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Loop.state,State.bank,State.double,
    Winner.scan,State.logCapacity,MaskData.input,writeTapeBit,CompareMachine.word,Fin.addCases]

theorem setup_step (d : MaskData) :
    Step Program.setup 1 (midH d) (midA d)
      (RepeatMachine.cfg 0 (Loop.state d 0 []) d.q 1).heads
      (RepeatMachine.cfg 0 (Loop.state d 0 []) d.q 1).tapes := by
  obtain ⟨r,hr,hf,_⟩ := Program.single_run (t := 14)
    (fun i => if i.val=8 ∨ i.val=9 ∨ i.val=10 ∨ i.val=11 then some false else none)
    (fun i => if i.val=1 ∨ i.val=8 ∨ i.val=11 then .right else .stay) (midH d) (midA d)
  apply Step.of_run hr
  · rw [hf]; exact setup_heads d
  · rw [hf]; exact setup_bank d

end PCJ93d4cfe17dc847a3.Start
