import Proof.Packets.PacketsXMajorityCompletePacketAtomsBounds
import Proof.Packets.PacketsXMajorityCompletePacketRewind

/-! The physical atom table's terminal arena contains the packet arithmetic
masters. These literal projections dock it without another arithmetic boot. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.PacketAtoms
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsRawPairSeek (Pair)
open NormalizedFiniteTransport Theorem25Completion.CycleBounds
noncomputable section

def arithmeticSlots (i : Fin 34) : Fin 46 :=
  if i.val<30 then ⟨i.val,by omega⟩ else ⟨i.val+2,by have h:=i.isLt;omega⟩

theorem arithmetic_words (C R : Nat) (coding : Nat→Nat) (cs : List Pair)
    (ps : List PacketVector.Packet) (hR : 1≤R) (i : Fin 34) :
    AddressedAtomMaterialize.paddedA C R coding cs ps 0 (arithmeticSlots i)=
      ReusableArithmetic.natState C R [] [] i := by
  have hz : ZeroPadding.pad R [false]=List.replicate R false := by
    change ZeroPadding.pad R (List.replicate 1 false)=_
    rw [Rewind.Workspace.pad_zeros,Nat.max_eq_left hR]
  have hc : ZeroPadding.pad R (CompareMachine.word 0)=List.replicate R false := hz
  fin_cases i <;>simp [arithmeticSlots,AddressedAtomMaterialize.paddedA,
    AddressedAtomMaterialize.cacheCaps,AddressedAtomMaterialize.A,NativeIndexedAtom.data,
    NativeAtomStore.data,NativePairNormalize.result,ReusableNative.ready,ReusableNative.bank,
    ReusableNative.readyData,ReusableArithmetic.natState,ReusableArithmetic.state,
    ReusableArithmetic.bank,ReusableArithmetic.padded,ReusableArithmetic.data,
    NormalizedMultiply.data,NormalizedMultiply.extras,NormalizeCold.data,Normalize.records,
    Fin.addCases,ZeroPadding.pad_zero,hc,
    show ZeroPadding.pad R []=List.replicate R false from by simp [ZeroPadding.pad]]

theorem dense_source (C R : Nat) (coding : Nat→Nat) (cs : List Pair)
    (ps : List PacketVector.Packet) :
    AddressedAtomMaterialize.paddedA C R coding cs ps 0 42=PacketVector.bank R ps := by
  exact ZeroPadding.pad_zero _

end
end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.PacketAtoms
