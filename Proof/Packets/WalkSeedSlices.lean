import Proof.Packets.WalkSeedReady
import Proof.Supplier.SupplierWalkBridge

/-! The slice boundaries are computed from the actual rank; no decomposition
of the input word is an execution premise. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option warningAsError true
namespace Theorem25Completion.WalkSeedSlices
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.SupplierWalkBridge

def pad (rank : Nat) (word : List Bool):=word.take (WalkSeedPadding.padding rank)
def rest (rank : Nat) (word : List Bool):=word.drop (WalkSeedPadding.padding rank)
def lower (rank : Nat) (word : List Bool):=(rest rank word).take rank
def afterLower (rank : Nat) (word : List Bool):=(rest rank word).drop rank
def upper (rank : Nat) (word : List Bool):=(afterLower rank word).take (rank-1)
def translation (rank : Nat) (word : List Bool):=(afterLower rank word).drop (rank-1)

theorem decompose (rank : Nat) (word : List Bool) :
    WalkSeedSlice.source (pad rank word) (lower rank word) (upper rank word) (translation rank word)=word := by
  unfold WalkSeedSlice.source upper translation
  rw [List.append_assoc, List.append_assoc,List.take_append_drop]
  unfold lower afterLower
  rw [List.take_append_drop]
  exact List.take_append_drop _ _

theorem padding_eq (rank : Nat) (hr : 0<rank) :
    WalkSeedPadding.padding rank=2*toeplitzWalkSideBits rank-toeplitzSeedBits rank := by
  unfold WalkSeedPadding.padding toeplitzWalkSideBits toeplitzSeedBits
  split <;>omega

theorem extent (rank : Nat) (hr : 0<rank) :
    WalkSeedPadding.padding rank+rank+(rank-1)+rank=2*toeplitzWalkSideBits rank := by
  unfold WalkSeedPadding.padding toeplitzWalkSideBits toeplitzSeedBits
  split <;>omega

theorem lengths (rank : Nat) (hr : 0<rank) (word : List Bool)
    (hw : word.length=2*toeplitzWalkSideBits rank) :
    (pad rank word).length=WalkSeedPadding.padding rank ∧ (lower rank word).length=rank ∧
    (upper rank word).length=rank-1 ∧ (translation rank word).length=rank := by
  have he:=extent rank hr
  simp only [pad,lower,rest,upper,translation,afterLower,List.length_take,List.length_drop,hw]
  omega

end Theorem25Completion.WalkSeedSlices
