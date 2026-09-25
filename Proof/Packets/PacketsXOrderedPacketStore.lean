import Proof.Packets.PacketsXOrderedPacketReset
import Proof.Packets.PacketBankZeroHeads

/-! Append the resident normalized accumulator packet to a physical output bank,
retaining the arbitrary left operand, source bank and index. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.OrderedPacketStore
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport Theorem25Completion.CycleBounds
abbrev Poly:=Ring.Poly Nat

def H (out : List Bool) : Fin 38→Nat:=Fin.addCases (m:=37) (n:=1) (motive:=fun _=>Nat)
  (ArithmeticLookup.H 0) (fun _=>out.length)
def A (C R index : Nat) (left right : Poly) (ps : List Poly) (out : List Bool) : Fin 38→List Bool:=
  Fin.addCases (m:=37) (n:=1) (motive:=fun _=>List Bool)
    (OrderedPacketStep.A C R index left right ps) (fun _=>out)
def entry (C R : Nat) (P : Poly) :=PacketVector.entry R (P.map (maskNat C))
def slots : Fin 6→Fin 38:=![31,37,26,27,35,36]
noncomputable def store:=RecoveryFocus.machine slots PacketBank.storeZero

theorem store_run (C R index : Nat) (left P : Poly) (ps : List Poly) (out : List Bool)
    (hp : PacketVector.Fits R (P.map (maskNat C))) :
    Step store (PacketBank.storeBudget R+4)
      (H out) (A C R index left P ps out)
      (H (out++entry C R P)) (A C R index left P ps (out++entry C R P)) := by
  have h:=(PacketBank.store_zero_run R index out
    (PacketVector.payload R (P.map (maskNat C))) (PacketVector.count R (P.map (maskNat C)))
    (PacketVector.payload_length hp) (PacketVector.count_length hp)).pad (![0,0,0,0,R,R] : Fin 6→Nat)
  apply PhysicalFocusBoundary.focus h slots (by decide) (H out) (H (out++entry C R P)) _ _
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>simp [slots,A,OrderedPacketStep.A,ArithmeticLookup.A,PacketBank.A,
      Fin.addCases,ReusableArithmetic.state,ReusableArithmetic.bank,ReusableArithmetic.padded,
      ReusableArithmetic.data,NormalizedMultiply.data,NormalizedMultiply.extras,
      PacketVector.payload,PacketVector.count,ZeroPadding.pad_zero]
    simp [ZeroPadding.pad]
  · intro i;fin_cases i <;>simp [slots,H,PacketBank.H,ArithmeticLookup.H,Fin.addCases,entry,PacketVector.entry,List.append_assoc]
  · intro i;fin_cases i <;>simp [slots,A,OrderedPacketStep.A,ArithmeticLookup.A,PacketBank.A,
      Fin.addCases,ReusableArithmetic.state,ReusableArithmetic.bank,ReusableArithmetic.padded,
      ReusableArithmetic.data,NormalizedMultiply.data,NormalizedMultiply.extras,
      PacketVector.payload,PacketVector.count,ZeroPadding.pad_zero,entry,PacketVector.entry,List.append_assoc]
    simp [ZeroPadding.pad]
  · intro i away
    have hi : i≠37:=by intro he;subst i;exact away 1 rfl
    fin_cases i <;>simp_all [H,A,Fin.addCases]

end PCJ9eff70d512234a4c_Fixed.Materializer.OrderedPacketStore
