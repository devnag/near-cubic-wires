import Proof.Packets.ArithmeticPacketLookup
import Proof.Packets.PacketBankZeroHeads

/-! Actual indexed child lookup into the reusable right operand. The bank,
physical index, current left operand, and reserve resources are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorChildLookup
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def heads : Fin 37→Nat := Fin.addCases (m:=34) (n:=3) (motive:=fun _=>Nat)
  ReusableArithmetic.heads (![0,1,0])
def tapes (B R index : Nat) (left right : List (List Bool)) (source : List Bool) : Fin 37→List Bool :=
  Fin.addCases (m:=34) (n:=3) (motive:=fun _=>List Bool) (ReusableArithmetic.state B R left right)
    (![source,ZeroPadding.pad R (CompareMachine.word index),List.replicate R false])
def slots : Fin 6→Fin 37 := ![31,34,26,27,35,36]
def machine := RecoveryFocus.machine slots PacketBank.lookupZero

theorem tapes_outside (B R index : Nat) (left right selected : List (List Bool))
    (source : List Bool) (i : Fin 37) (h26 : i≠26) (h27 : i≠27) :
    tapes B R index left right source i=tapes B R index left selected source i := by
  change ArithmeticLookup.A B R index left right source i=ArithmeticLookup.A B R index left selected source i
  revert h26 h27
  refine Fin.addCases (m:=34) (n:=3) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=30) (n:=4) (fun k=>?_) (fun k=>?_) j
    · refine Fin.addCases (m:=24) (n:=6) (fun l=>?_) (fun l=>?_) k
      · intro _ _
        rw [ArithmeticLookup.A_worker,ArithmeticLookup.A_worker,ArithmeticLookup.data_core,ArithmeticLookup.data_core]
      · intro hn26 hn27
        rw [ArithmeticLookup.A_worker,ArithmeticLookup.A_worker,ArithmeticLookup.data_extra,ArithmeticLookup.data_extra]
        fin_cases l
        · rfl
        · rfl
        · exact False.elim (hn26 rfl)
        · exact False.elim (hn27 rfl)
        · rfl
        · rfl
    · intro _ _;rw [ArithmeticLookup.A_reserved,ArithmeticLookup.A_reserved]
  · intro _ _;rw [ArithmeticLookup.A_extra,ArithmeticLookup.A_extra]

attribute [local irreducible] PacketBank.lookupZero PacketBank.lookup

theorem run (B R index : Nat) (left right selected : List (List Bool))
    (pre post : List Bool) (hpre : pre.length=2*index*R)
    (hr : right.flatten.length≤R) (hrc : right.length+1≤R)
    (hs : selected.flatten.length≤R) (hsc : selected.length+1≤R) :
    let payload:=ZeroPadding.pad R selected.flatten
    let count:=ZeroPadding.pad R (CompareMachine.word selected.length)
    Step machine (PacketBank.lookupBudget R index+4)
      heads (tapes B R index left right (pre++payload++count++post))
      heads (tapes B R index left selected (pre++payload++count++post)) := by
  dsimp only
  have hsl : (ZeroPadding.pad R selected.flatten).length=R := by rw [ZeroPadding.pad_length,Nat.max_eq_left hs]
  have hscl : (ZeroPadding.pad R (CompareMachine.word selected.length)).length=R := by
    simp [CompareMachine.word,Nat.max_eq_left hsc]
  have hrl : (ZeroPadding.pad R right.flatten).length=R := by rw [ZeroPadding.pad_length,Nat.max_eq_left hr]
  have hrcl : (ZeroPadding.pad R (CompareMachine.word right.length)).length=R := by
    simp [CompareMachine.word,Nat.max_eq_left hrc]
  have h := (PacketBank.lookup_zero_run R index pre (ZeroPadding.pad R selected.flatten)
    (ZeroPadding.pad R (CompareMachine.word selected.length)) post
    (ZeroPadding.pad R right.flatten) (ZeroPadding.pad R (CompareMachine.word right.length))
    hpre hsl hscl hrl hrcl).pad (![0,0,0,0,R,R] : Fin 6→Nat)
  apply PhysicalFocusBoundary.focus h slots (by decide) heads heads _ _
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>simp [slots,tapes,PacketBank.A,Fin.addCases,ReusableArithmetic.state,ReusableArithmetic.bank,
      ReusableArithmetic.padded,ReusableArithmetic.data,NormalizedMultiply.data,NormalizedMultiply.extras,ZeroPadding.pad_zero]
    simp [ZeroPadding.pad]
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>simp [slots,tapes,PacketBank.A,Fin.addCases,ReusableArithmetic.state,ReusableArithmetic.bank,
      ReusableArithmetic.padded,ReusableArithmetic.data,NormalizedMultiply.data,NormalizedMultiply.extras,ZeroPadding.pad_zero]
    simp [ZeroPadding.pad]
  · intro i away
    refine ⟨rfl,?_⟩
    exact tapes_outside B R index left right selected _ i
      (by intro he;subst i;exact away 2 rfl) (by intro he;subst i;exact away 3 rfl)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorChildLookup
