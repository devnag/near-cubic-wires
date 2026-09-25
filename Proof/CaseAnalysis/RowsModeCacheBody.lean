import Proof.CaseAnalysis.RowsModeCacheNext

/-! One whole actual original-seed occurrence pass computes the hash, reads
the same original mask, appends its exact literal pair, and returns its bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
open LocalBitMultitape ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first:=Composition.machine hashMachine guardMachine
noncomputable def second (mode : Fin 3):=Composition.machine first (selectMachine mode)
noncomputable def third (mode : Fin 3):=Composition.machine (second mode) pairMachine
noncomputable def fourth (mode : Fin 3):=Composition.machine (third mode) cursorMachine
noncomputable def fifth (mode : Fin 3):=Composition.machine (fourth mode) labelMachine
noncomputable def body (mode : Fin 3):=Composition.machine (fifth mode) eraseMachine

def next (mode : Fin 3) (p : Parameters) (s : State):=emitted (selected mode p (guarded p s))
def bodyBudget (p : Parameters) (index : Nat):=
  CloseoutRowsModeHashReady.budget p.rank p.rank+2*p.level+4*index+2*p.rank+2*p.C+55

theorem body_run (mode : Fin 3) (p : Parameters) (s : State) (hl : p.level≤p.rank)
    (hC : p.rank+2≤p.C) (hb : CloseoutRowsModeHashLoop.budget p.rank p.rank+2≤p.C)
    (hi : s.index<2^p.rank) :
    Step (body mode) (bodyBudget p s.index) (heads s) (data p s false)
      (heads (next mode p s)) (data p (next mode p s) false):=by
  have a:=hash_run p s hC hb
  have b:=guard_run p s hl hC
  have c:=select_run mode p (guarded p s)
  have d:=pair_run p (selected mode p (guarded p s))
  have e:=cursor_run p (selected mode p (guarded p s))
  have f:=label_run p (selected mode p (guarded p s)) hi (by omega)
  have g:=erase_run p (selected mode p (guarded p s)) hC
  have r:=(((((a.seq b).seq c).seq d).seq e).seq f).seq g
  have ht:(((((CloseoutRowsModeHashReady.budget p.rank p.rank+1+(2*p.level+6))+1+1)+1+
      CloseoutRowsModeLiteralPair.budget (selected mode p (guarded p s)).index)+1+1)+1+(2*p.rank+4))+1+(2*p.C+4)=
      bodyBudget p s.index:=by
    simp only [CloseoutRowsModeLiteralPair.budget,selected,guarded,bodyBudget]
    omega
  rw [ht] at r
  exact r

end NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
