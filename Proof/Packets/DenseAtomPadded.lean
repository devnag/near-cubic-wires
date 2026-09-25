import Proof.Packets.DenseAtom
import Proof.Packets.DenseAtomMeaning

/-! Native atom and generated-code caches retain actual common-R backing
on first entry and every reentry. No logical padding is used as a tape write:
these are executions from the already backed producer outputs. -/
set_option autoImplicit false
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DenseAtomMaterialize
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open CloseoutRowsRawPairSeek (Pair cacheWord)
open DenseAtomProgram (table codes)
open PacketVector (Packet)

def cacheCaps (R : Nat) (i : Fin 46) : Nat := if i=36 ∨ i=40 then R else 0
def paddedA (C R tag : Nat) (cs : List Pair) (ps : List Packet) (index : Nat) (i : Fin 46) :=
  ZeroPadding.pad (cacheCaps R i) (A C R tag cs ps index i)

end PCJ9eff70d512234a4c_Fixed.Materializer.DenseAtomMaterialize
