import Proof.Packets.IdentityCodeRecord
import Proof.Packets.VectorCounterDecrement
import Proof.Packets.PhysicalRepeatStep

/-! Runtime-counted descending identity-address cache, generated from a
retained count and a physical unary index. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.IdentityCodeLoop
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

def output (N j : Nat) (out : List Bool) := out++
  (List.range j).flatMap (fun i=>NativeLiteralCode.word (N-1-i))
def stream (N : Nat) := (List.range N).flatMap (fun i=>NativeLiteralCode.word (N-1-i))
def H (out : List Bool) : Fin 2→Nat := ![1,out.length]
def A (R n : Nat) (out : List Bool) : Fin 2→List Bool := ![ZeroPadding.pad R (CompareMachine.word n),out]
def indexSlot : Fin 1→Fin 2 := ![0]
noncomputable def decrement := RecoveryFocus.machine indexSlot VectorCounter.decrement
noncomputable def body := Composition.machine decrement IdentityCodeRecord.machine
noncomputable def machine := RepeatMachine.machine body (fun _ _=>true)
def budget (N : Nat) := N*(4*N+16)+3

theorem output_succ (N j : Nat) (out : List Bool) :
    output N (j+1) out=output N j out++NativeLiteralCode.word (N-(j+1)) := by
  have he : N-1-j=N-(j+1) := by omega
  simp [output,List.range_succ,List.flatMap_append,List.append_assoc,he]

theorem decrement_run (R n : Nat) (out : List Bool) (hcap : n+2≤R) :
    Step decrement (2*n+4) (H out) (A R (n+1) out) (H out) (A R n out) := by
  apply PhysicalFocusBoundary.focus (VectorCounter.decrement_padded n R hcap)
    indexSlot (by decide) (H out) (H out) (A R (n+1) out) (A R n out)
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;rfl
  · intro i away;fin_cases i
    · exact False.elim (away 0 rfl)
    · exact ⟨rfl,rfl⟩

theorem record_run (R n : Nat) (out : List Bool) :
    Step IdentityCodeRecord.machine (2*n+8) (H out) (A R n out)
      (H (out++NativeLiteralCode.word n)) (A R n (out++NativeLiteralCode.word n)) := by
  have h:=(IdentityCodeRecord.run n out).pad (![R,0] : Fin 2→Nat)
  convert h using 1 <;>first | rfl | (funext i;fin_cases i <;>simp [A,ZeroPadding.pad_zero])

theorem body_run (R N j : Nat) (out : List Bool) (hj : j<N) (hcap : N+1≤R) :
    Step body (4*N+13) (H (output N j out)) (A R (N-j) (output N j out))
      (H (output N (j+1) out)) (A R (N-(j+1)) (output N (j+1) out)) := by
  have first:=decrement_run R (N-(j+1)) (output N j out) (by omega)
  have he : N-(j+1)+1=N-j := by omega
  rw [he] at first
  have h:=first.seq (record_run R (N-(j+1)) (output N j out))
  rw [←output_succ] at h
  exact h.enlarge (by omega)

theorem run (R N : Nat) (out : List Bool) (hcap : N+1≤R) :
    Step machine (budget N)
      (Fin.addCases (m:=2) (n:=1) (H out) (fun _=>1))
      (Fin.addCases (m:=2) (n:=1) (A R N out) (fun _=>CompareMachine.word N))
      (Fin.addCases (m:=2) (n:=1) (H (out++stream N)) (fun _=>1))
      (Fin.addCases (m:=2) (n:=1) (A R 0 (out++stream N)) (fun _=>CompareMachine.word N)) := by
  have h:=PhysicalRepeatStep.run body N (4*N+13)
    (fun j=>H (output N j out)) (fun j=>A R (N-j) (output N j out))
    (fun j hj=>body_run R N j out hj hcap)
  simpa [machine,budget,output,stream,Nat.add_assoc] using h

end PCJ9eff70d512234a4c_Fixed.Materializer.IdentityCodeLoop
