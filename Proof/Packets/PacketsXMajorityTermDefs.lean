import Proof.Packets.MajorityAccept
import Proof.Packets.PacketsXBooleanSelectorResident

/-! Concrete shared arena for one reusable majority truth-table callback. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityTermArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport Theorem25Completion.CycleBounds PairedPacketMeaning

def H (out : List Bool) : Fin 46→Nat:=Fin.addCases (m:=37) (n:=9) (motive:=fun _=>Nat)
  (ArithmeticLookup.H 0) ![0,1,0,0,0,0,out.length,0,0]
def extras (R N count : Nat) (bits out binary : List Bool) (flag : Bool) : Fin 9→List Bool:=
  ![ZeroPadding.pad R bits,ZeroPadding.pad R (CompareMachine.word N),
    ZeroPadding.pad R (CompareMachine.word ((N+1)/2)),ZeroPadding.pad R (CompareMachine.word count),
    ZeroPadding.pad R [flag],List.replicate R false,out,binary,List.replicate R false]
def A (C R : Nat) (ps : List Poly) (left right : Poly) (bits : List Bool) (count : Nat)
    (flag : Bool) (out binary : List Bool) : Fin 46→List Bool:=
  Fin.addCases (m:=37) (n:=9) (motive:=fun _=>List Bool)
    (OrderedPacketStep.A C R 0 left right (ComplementPacketBank.pairs ps))
    (extras R ps.length count bits out binary flag)
def scratch : Fin 7→Fin 46:=![25,26,27,28,37,40,41]
def clearSlots : Fin 9→Fin 46:=Fin.addCases (m:=7) (n:=2) (motive:=fun _=>Fin 46) scratch ![32,33]
noncomputable def clear:=RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 7)


end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityTermArena
