import Proof.MachineModel.OrdinaryMatrixBatchGateLayout

/-! Full raw Request plus blank work physically prepares every native field
of the reusable all-gates loop. No gate bank, zero word or driver is supplied
as an external premise. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchGateColdEntry
open LocalBitMultitape SignedSortKey MatrixScoreBatch
open MatrixBatchGateLayout (slots heads tapes)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first := TapeEmbedding.machine 34 MatrixBatchWorkspace.machine
noncomputable def machine := Composition.machine first MatrixBatchGateColdCopy.machine
def input (r : Request) : Fin 166 → List Bool := fun i => if i=0 then physicalInput r else []
def budget (r : Request) := MatrixBatchWorkspace.budget r+1+MatrixBatchGateColdCopy.budget r

theorem entry_run (r : Request) :
    ∃ actual,run machine (budget r) (input r)=some actual ∧
      (∀ i,actual.final.heads (slots i)=heads r i) ∧
      (∀ i,actual.final.tapes (slots i)=tapes r i) ∧
      actual.final.tapes 0=physicalInput r ∧ actual.final.heads 0=0 ∧
      actual.final.tapes 40=List.replicate r.p true ∧ actual.final.heads 40=0 ∧
      actual.final.tapes 80=List.replicate (natBitLength r.Gates) true ∧ actual.final.heads 80=0 ∧
      actual.final.tapes 83=frame (binary (natBitLength r.Gates) r.Gates) ∧ actual.final.heads 83=0 ∧
      actual.steps≤budget r := by
  obtain ⟨base,hb,b0,h0,b1,h1,b32,h32,b39,h39,b40,h40,b49,h49,b61,h61,b65,h65,b77,h77,
    b80,h80,b83,h83,b89,h89,b92,h92,b95,h95,b99,h99,b103,h103,b106,h106,b107,h107,bs⟩ :=
    MatrixBatchNativeFields.setup_run r
  obtain ⟨workspace,hw,wt,wh,w130,wh130,ws⟩ := MatrixBatchWorkspace.workspace_run r base hb b77 h77 b39 h39 bs
  have he := TapeEmbedding.run_embed MatrixBatchWorkspace.machine
    (fun _ : Fin 34 => 0) (fun _ : Fin 34 => []) _ _ workspace hw
  let prepared := TapeEmbedding.receipt (fun _ : Fin 34 => 0) (fun _ : Fin 34 => []) workspace
  obtain ⟨moved,hm,mh,mt,ms⟩ := MatrixBatchGateColdCopy.prepare_run r prepared.final.heads prepared.final.tapes
    (by intro i; fin_cases i; exact (wh 103).trans h103; rfl; exact (wh 106).trans h106; exact (wh 107).trans h107)
    ((wt 103).trans b103) (by rfl) ((wt 106).trans b106) ((wt 107).trans b107)
  have joined := Composition.run_join first MatrixBatchGateColdCopy.machine _ _ _ prepared moved he hm
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 34 => 0) (fun _ : Fin 34 => [])
      (initialConfiguration MatrixBatchWorkspace.machine (MatrixBatchWorkspace.input r)))=
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at joined
  refine ⟨Composition.joinedReceipt prepared moved,joined,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    change moved.final.heads (slots i)=_
    rw [mh]
    fin_cases i
    · rfl
    · exact (wh 95).trans h95
    · rfl
    · rfl
    · rfl
    · rfl
    · exact (wh 49).trans h49
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact (wh 77).trans h77
    · exact (wh 107).trans h107
    · change workspace.final.heads 92+1=1
      exact congrArg (fun n => n+1) ((wh 92).trans h92)
    · exact (wh 61).trans h61
    · exact (wh 65).trans h65
    · rfl
    · rfl
    · rfl
    · exact (wh 32).trans h32
    · rfl
    · exact (wh 106).trans h106
    · rfl
    · change workspace.final.heads 39+1=1
      exact congrArg (fun n => n+1) (wh 39)
    · exact (wh 99).trans h99
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact (wh 103).trans h103
    · exact wh130
    · rfl
    · exact (wh 1).trans h1
    · rfl
    · exact (wh 89).trans h89
  · intro i
    change moved.final.tapes (slots i)=_
    rw [mt]
    fin_cases i
    · rfl
    · exact (wt 95).trans b95
    · rfl
    · rfl
    · rfl
    · rfl
    · exact (wt 49).trans b49
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact (wt 77).trans b77
    · exact (wt 107).trans b107
    · exact (wt 92).trans b92
    · exact (wt 61).trans b61
    · exact (wt 65).trans b65
    · rfl
    · rfl
    · rfl
    · exact (wt 32).trans b32
    · rfl
    · exact (wt 106).trans b106
    · rfl
    · exact (wt 39).trans b39
    · exact (wt 99).trans b99
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact (wt 103).trans b103
    · exact w130
    · rfl
    · exact (wt 1).trans b1
    · rfl
    · exact (wt 89).trans b89
  · change moved.final.tapes 0=_
    rw [mt]
    exact (wt 0).trans b0
  · change moved.final.heads 0=_
    rw [mh]
    exact (wh 0).trans h0
  · change moved.final.tapes 40=_
    rw [mt]
    exact (wt 40).trans b40
  · change moved.final.heads 40=_
    rw [mh]
    exact (wh 40).trans h40
  · change moved.final.tapes 80=_
    rw [mt]
    exact (wt 80).trans b80
  · change moved.final.heads 80=_
    rw [mh]
    exact (wh 80).trans h80
  · change moved.final.tapes 83=_
    rw [mt]
    exact (wt 83).trans b83
  · change moved.final.heads 83=_
    rw [mh]
    exact (wh 83).trans h83
  · change prepared.steps+1+moved.steps≤_
    rw [ms]
    change workspace.steps+1+MatrixBatchGateColdCopy.budget r≤budget r
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixBatchGateColdEntry
