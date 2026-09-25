import Proof.Packets.WalkSeedSlice

/-! Actual seed slicing with paid restoration of every cursor. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 12000
set_option warningAsError true
namespace Theorem25Completion.WalkSeedReady
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open WalkSeedSlice

noncomputable def machine:=MaskedReset.machine WalkSeedSlice.machine (fun _=>true)
def input (rank : Nat) (word : List Bool) : Fin 6→List Bool:=
  Fin.addCases (m:=5) (n:=1) (motive:=fun _=>List Bool) (bank rank word [] [] []) (fun _ : Fin 1=>[])
def output (rank : Nat) (word low up tr log : List Bool) : Fin 6→List Bool:=
  Fin.addCases (m:=5) (n:=1) (motive:=fun _=>List Bool) (bank rank word low up tr) (fun _ : Fin 1=>log)

theorem run (rank : Nat) (hr : 0<rank) (pad low up tr : List Bool)
    (hp : pad.length=WalkSeedPadding.padding rank) (hl : low.length=rank)
    (hu : up.length=rank-1) (ht : tr.length=rank) : ∃log,
    Step machine (16*rank+30) (fun _=>0) (input rank (source pad low up tr))
      (fun _=>0) (output rank (source pad low up tr) low up tr log) ∧ log.length≤8*rank+14 := by
  obtain ⟨base,br,bh,bt,bs⟩:=WalkSeedSlice.run rank hr pad low up tr hp hl hu ht
  have bound : ∀i,base.final.heads i≤base.steps := by
    intro i
    have h:=SelectiveReset.prefix_head (prefix_of_run WalkSeedSlice.machine (8*rank+14)
      (⟨WalkSeedSlice.machine.start,fun _=>0,bank rank (source pad low up tr) [] [] []⟩) base br).1 i
    simpa using h
  obtain ⟨r,rr,rf,rs,_⟩:=MaskedReset.reset_run WalkSeedSlice.machine (fun _=>true) (8*rank+14)
    (⟨WalkSeedSlice.machine.start,fun _=>0,bank rank (source pad low up tr) [] [] []⟩)
      base br (by intro i _;exact bound i)
  refine ⟨List.replicate base.steps false,?_,by simpa using bs⟩
  have fuel:2*base.steps+2≤16*rank+30:=by omega
  have h:=runFrom_moreFuel machine _ (16*rank+30-(2*base.steps+2)) _ r rr
  rw [Nat.add_sub_of_le fuel] at h
  have he : Rewind.recording
      (⟨WalkSeedSlice.machine.start,fun _=>0,bank rank (source pad low up tr) [] [] []⟩) 0=
      (⟨machine.start,fun _=>0,input rank (source pad low up tr)⟩ : Configuration 6 _) := by
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;>rfl
    · rfl
  rw [he] at h
  refine ⟨r,h,?_,?_,by omega⟩
  · rw [rf]
    funext i;fin_cases i <;>rfl
  · rw [rf]
    change Fin.addCases (m:=5) (n:=1) (motive:=fun _=>List Bool) base.final.tapes (fun _ : Fin 1=>List.replicate base.steps false)=_
    rw [bt]
    rfl

end Theorem25Completion.WalkSeedReady
