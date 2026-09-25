import Proof.Packets.WalkSeedDecode
import Proof.Packets.WalkSeedMeaning

/-! Actual framed vertex coordinates are decoded to the frozen seed fields.
No supplied seed decomposition or seed-field execution premise is needed. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true
namespace Theorem25Completion.WalkSeedTyped
open NearCubicWires NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.ExtDecompositionBatch WalkSeedBinary

theorem run (rank : Nat) (hr : 0<rank)
    (v : MargulisVertex (2^toeplitzWalkSideBits rank)) : ∃a b,
    Step WalkSeedDecode.machine (28*rank+43) (fun _=>0)
      (WalkSeedDecode.input rank (binary (toeplitzWalkSideBits rank) v.1.val)
        (binary (toeplitzWalkSideBits rank) v.2.val)) (fun _=>0)
      (WalkSeedDecode.output rank (binary (toeplitzWalkSideBits rank) v.1.val)
        (binary (toeplitzWalkSideBits rank) v.2.val)
        (List.ofFn (fun i : Fin rank=>decide ((toeplitzWalkEncoding rank v).1.1.1 i=1)))
        (List.ofFn (fun i : Fin (rank-1)=>decide ((toeplitzWalkEncoding rank v).1.1.2 i=1)))
        (List.ofFn (fun i : Fin rank=>decide ((toeplitzWalkEncoding rank v).1.2 i=1))) a b) ∧
      a.length≤6*rank+5 ∧ b.length≤8*rank+14 := by
  obtain ⟨hp,hl,hu,ht⟩:=WalkSeedSlices.lengths rank hr (vertexWord rank v)
    (vertexWord_length rank v)
  obtain ⟨a,b,h,ha,hb⟩:=WalkSeedDecode.run rank hr
    (binary (toeplitzWalkSideBits rank) v.1.val)
    (binary (toeplitzWalkSideBits rank) v.2.val)
    (WalkSeedSlices.pad rank (vertexWord rank v))
    (WalkSeedSlices.lower rank (vertexWord rank v))
    (WalkSeedSlices.upper rank (vertexWord rank v))
    (WalkSeedSlices.translation rank (vertexWord rank v))
    (WalkSeedSlices.decompose rank (vertexWord rank v)).symm hp hl hu ht
  rw [WalkSeedMeaning.lower_eq rank hr,WalkSeedMeaning.upper_eq rank hr,
    WalkSeedMeaning.translation_eq rank hr] at h
  have hs : 2*toeplitzWalkSideBits rank≤3*rank+1 :=
    (twice_toeplitzWalkSideBits_le rank).trans (by
      have h:=toeplitzSeedBits_le_three_mul rank
      omega)
  have hf : WalkSeedDecode.budget rank
      (binary (toeplitzWalkSideBits rank) v.1.val)
      (binary (toeplitzWalkSideBits rank) v.2.val)≤28*rank+43 := by
    simp only [WalkSeedDecode.budget,WalkVertexBits.budget,binary_length]
    omega
  refine ⟨a,b,h.enlarge hf,?_,hb⟩
  simp only [WalkVertexBits.budget,binary_length] at ha
  omega

end Theorem25Completion.WalkSeedTyped
