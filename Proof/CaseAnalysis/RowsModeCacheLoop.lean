import Proof.CaseAnalysis.RowsModeCacheBody

/-! The retained original population driver repeats the whole physical
cache body, preserving pair order, including an empty population. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
open LocalBitMultitape ExtDecompositionBatch RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def track (mode : Fin 3) (p : Parameters) (initial : State) : Nat→State
  | 0=>{initial with out:=[]}
  | j+1=>{next mode p (track mode p initial j) with out:=[]}
def atState (mode : Fin 3) (p : Parameters) (initial : State) (j : Nat) (out : List Bool):=
  {track mode p initial j with out:=out}
def piece (mode : Fin 3) (p : Parameters) (initial : State) (j : Nat):=
  pairWord (selected mode p (guarded p (track mode p initial j)))
noncomputable def entry (mode : Fin 3) (p : Parameters) (initial : State) (j : Nat) (out : List Bool):=
  (⟨(body mode).start,heads (atState mode p initial j out),data p (atState mode p initial j out) false⟩ : Configuration 24 _)
noncomputable def machine (mode : Fin 3):=CloseoutRowsDegreeLoop.machine (body mode)
def budget (p : Parameters) (initial : State) (count : Nat):=count*(bodyBudget p (initial.index+count)+3)+3

theorem track_index (mode : Fin 3) (p : Parameters) (initial : State) (j : Nat) :
    (track mode p initial j).index=initial.index+j:=by
  induction j with
  | zero=>rfl
  | succ j ih=>
    change (track mode p initial j).index+1=initial.index+(j+1)
    rw [ih,Nat.add_assoc]

theorem round_run (mode : Fin 3) (p : Parameters) (initial : State) (j count : Nat) (out : List Bool)
    (hl : p.level≤p.rank) (hC : p.rank+2≤p.C) (hb : CloseoutRowsModeHashLoop.budget p.rank p.rank+2≤p.C)
    (hj : j<count) (hi : initial.index+count≤2^p.rank) :
    Step (body mode) (bodyBudget p (initial.index+count))
      (entry mode p initial j out).heads (entry mode p initial j out).tapes
      (entry mode p initial (j+1) (out++piece mode p initial j)).heads
      (entry mode p initial (j+1) (out++piece mode p initial j)).tapes:=by
  have hx:(atState mode p initial j out).index=initial.index+j:=track_index mode p initial j
  have r:=body_run mode p (atState mode p initial j out) hl hC hb (by omega)
  have hmono:bodyBudget p (atState mode p initial j out).index≤bodyBudget p (initial.index+count):=by
    unfold bodyBudget;omega
  exact r.enlarge hmono

theorem loop_run (mode : Fin 3) (p : Parameters) (initial : State) (count : Nat) (out : List Bool)
    (hl : p.level≤p.rank) (hC : p.rank+2≤p.C) (hb : CloseoutRowsModeHashLoop.budget p.rank p.rank+2≤p.C)
    (hi : initial.index+count≤2^p.rank) :
    ∃ r,runFrom (machine mode) (budget p initial count)
      (RepeatMachine.cfg 0 (entry mode p initial 0 out) count 1)=some r ∧
      r.final=RepeatMachine.cfg 3 (entry mode p initial count (out++(List.range count).flatMap (piece mode p initial))) count 1 ∧
      r.steps≤budget p initial count:=by
  apply CloseoutRowsDegreeLoop.loop_run (body mode) (entry mode p initial) (piece mode p initial)
    (bodyBudget p (initial.index+count)) count (by intro j hj pre;rfl) _ out
  intro j hj pre
  exact round_run mode p initial j count pre hl hC hb hj hi

end NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
