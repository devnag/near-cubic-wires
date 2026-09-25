import Proof.Packets.WalkSeedBinary
import Proof.Packets.WalkSeedSlices

/-! The physically selected seed fields are the original Toeplitz fields. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true
namespace Theorem25Completion.WalkSeedMeaning
open NearCubicWires NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.ExtDecompositionBatch Completion.ToeplitzSeedBits WalkSeedBinary

theorem rest_binary (rank : Nat) (hr : 0<rank)
    (v : MargulisVertex (2^toeplitzWalkSideBits rank)) :
    WalkSeedSlices.rest rank (vertexWord rank v)=
      binary (rank+((rank-1)+rank)) (seedCode rank v) := by
  have he : 2*toeplitzWalkSideBits rank=
      WalkSeedPadding.padding rank+(rank+((rank-1)+rank)) := by
    have h:=WalkSeedSlices.extent rank hr
    omega
  rw [WalkSeedSlices.rest,vertexWord_binary,he,binary_split]
  rw [List.drop_left' (binary_length (WalkSeedPadding.padding rank) (vertexCode rank v))]
  rw [WalkSeedSlices.padding_eq rank hr]
  rfl

theorem lower_binary (rank : Nat) (hr : 0<rank)
    (v : MargulisVertex (2^toeplitzWalkSideBits rank)) :
    WalkSeedSlices.lower rank (vertexWord rank v)=binary rank (seedCode rank v) := by
  rw [WalkSeedSlices.lower,rest_binary rank hr,binary_split]
  exact List.take_left' (binary_length rank (seedCode rank v))

theorem afterLower_binary (rank : Nat) (hr : 0<rank)
    (v : MargulisVertex (2^toeplitzWalkSideBits rank)) :
    WalkSeedSlices.afterLower rank (vertexWord rank v)=
      binary ((rank-1)+rank) (seedCode rank v/2^rank) := by
  rw [WalkSeedSlices.afterLower,rest_binary rank hr,binary_split]
  exact List.drop_left' (binary_length rank (seedCode rank v))

theorem upper_binary (rank : Nat) (hr : 0<rank)
    (v : MargulisVertex (2^toeplitzWalkSideBits rank)) :
    WalkSeedSlices.upper rank (vertexWord rank v)=binary (rank-1) (seedCode rank v/2^rank) := by
  rw [WalkSeedSlices.upper,afterLower_binary rank hr,binary_split]
  exact List.take_left' (binary_length (rank-1) (seedCode rank v/2^rank))

theorem translation_binary (rank : Nat) (hr : 0<rank)
    (v : MargulisVertex (2^toeplitzWalkSideBits rank)) :
    WalkSeedSlices.translation rank (vertexWord rank v)=
      binary rank (seedCode rank v/2^(rank+(rank-1))) := by
  rw [WalkSeedSlices.translation,afterLower_binary rank hr,binary_split]
  rw [List.drop_left' (binary_length (rank-1) (seedCode rank v/2^rank)),
    Nat.div_div_eq_div_mul,←pow_add]

theorem lower_eq (rank : Nat) (hr : 0<rank)
    (v : MargulisVertex (2^toeplitzWalkSideBits rank)) :
    WalkSeedSlices.lower rank (vertexWord rank v)=
      List.ofFn (fun i : Fin rank=>decide ((toeplitzWalkEncoding rank v).1.1.1 i=1)) :=
  (lower_binary rank hr v).trans (lower_word rank v).symm

theorem upper_eq (rank : Nat) (hr : 0<rank)
    (v : MargulisVertex (2^toeplitzWalkSideBits rank)) :
    WalkSeedSlices.upper rank (vertexWord rank v)=
      List.ofFn (fun i : Fin (rank-1)=>decide ((toeplitzWalkEncoding rank v).1.1.2 i=1)) :=
  (upper_binary rank hr v).trans (upper_word rank v).symm

theorem translation_eq (rank : Nat) (hr : 0<rank)
    (v : MargulisVertex (2^toeplitzWalkSideBits rank)) :
    WalkSeedSlices.translation rank (vertexWord rank v)=
      List.ofFn (fun i : Fin rank=>decide ((toeplitzWalkEncoding rank v).1.2 i=1)) :=
  (translation_binary rank hr v).trans (translation_word rank v).symm

end Theorem25Completion.WalkSeedMeaning
