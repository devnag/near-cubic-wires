import Proof.Packets.PacketsXSelectedFactorStep

/-! Manufacture the paired-bank index and assignment end cursor from the
retained actual truth-assignment length driver. Two physical increments are
paid per bit; no doubled-index or cursor advice is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.BooleanSelectorSeek
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open SelectedPairFetch
noncomputable def advance:=PhysicalIndexedAt.advance (35 : Fin 38)
noncomputable def move:=RecoveryFocus.machine (fun _ : Fin 1=>(37 : Fin 38))
  (Completion.PhysicalDriverMoves.machine 1 .right)
noncomputable def body:=Composition.machine advance (Composition.machine advance move)
noncomputable def machine:=RepeatMachine.machine body (fun _ _=>true)
def budget (N : Nat):=N*(8*N+12)+3

theorem advance_run (C R index pos : Nat) (left acc : Poly) (ps : List Poly) (bits : List Bool) :
    Step advance (2*index+2) (H pos) (A C R index left acc ps bits)
      (H pos) (A C R (index+1) left acc ps bits) := by
  have h:=PhysicalIndexedAt.advance_run (35 : Fin 38) R index (H pos) (A C R index left acc ps bits)
  have hh : PhysicalIndexedAt.H (35 : Fin 38) (H pos)=H pos:=by
    apply Function.update_eq_self_iff.mpr
    rfl
  rw [hh,update_index,update_index] at h
  exact h

theorem move_run (C R index pos : Nat) (left acc : Poly) (ps : List Poly) (bits : List Bool) :
    Step move 1 (H pos) (A C R index left acc ps bits)
      (H (pos+1)) (A C R index left acc ps bits) := by
  apply PhysicalFocusBoundary.focus
    (Completion.PhysicalDriverMoves.run .right (fun _ : Fin 1=>pos) (fun _=>bits))
    (fun _ : Fin 1=>(37 : Fin 38)) (by intro i j _;exact Subsingleton.elim i j)
    (H pos) (H (pos+1)) _ _
  · intro i;rfl
  · intro i;rfl
  · intro i;rfl
  · intro i;rfl
  · intro i hi
    have h37 : i≠37:=by intro he;exact hi 0 he.symm
    fin_cases i <;>simp_all [H,Fin.addCases]

theorem body_run (C R i N : Nat) (left acc : Poly) (ps : List Poly) (bits : List Bool) (hi : i<N) :
    Step body (8*N+9) (H i) (A C R (2*i) left acc ps bits)
      (H (i+1)) (A C R (2*(i+1)) left acc ps bits) := by
  have h:=(advance_run C R (2*i) i left acc ps bits).seq
    ((advance_run C R (2*i+1) i left acc ps bits).seq
      (move_run C R (2*i+1+1) i left acc ps bits))
  rw [show 2*i+1+1=2*(i+1) by omega] at h
  exact h.enlarge (by omega)

theorem run (C R N : Nat) (left acc : Poly) (ps : List Poly) (bits : List Bool) :
    Step machine (budget N)
      (Fin.addCases (m:=38) (n:=1) (motive:=fun _=>Nat) (H 0) (fun _=>1))
      (Fin.addCases (m:=38) (n:=1) (motive:=fun _=>List Bool)
        (A C R 0 left acc ps bits) (fun _=>CompareMachine.word N))
      (Fin.addCases (m:=38) (n:=1) (motive:=fun _=>Nat) (H N) (fun _=>1))
      (Fin.addCases (m:=38) (n:=1) (motive:=fun _=>List Bool)
        (A C R (2*N) left acc ps bits) (fun _=>CompareMachine.word N)) := by
  have h:=PhysicalRepeatStep.run body N (8*N+9) (fun i=>H i)
    (fun i=>A C R (2*i) left acc ps bits) (fun i hi=>body_run C R i N left acc ps bits hi)
  simpa only [machine,budget,Nat.mul_zero,show 8*N+9+3=8*N+12 by omega] using h

end PCJ9eff70d512234a4c_Fixed.Materializer.BooleanSelectorSeek
