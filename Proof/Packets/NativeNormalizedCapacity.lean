import Proof.Packets.ReusableNativeNormalize
import Proof.Packets.PacketVector

/-! The actual executed normalizer's paid reserve also bounds its delivered
payload/count blocks. No additional output-capacity premise is required. -/
set_option autoImplicit false
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NativeNormalized
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

theorem output_fits (C R : Nat) (P : List (List Nat)) (hp : ∀m∈P,∀i∈m,i<C)
    (hdata : ∀i,(A C P [] i).length≤R) (hfuel : budget C P+3≤R) :
    PacketVector.Fits R (NormalizerOrder.ordered (masks C P)) := by
  obtain ⟨r,rr,hs,h20,_,h21,_⟩:=run C P hp
  have actual : Step machine (budget C P) (H 0 0 1) (A C P []) r.final.heads r.final.tapes :=
    ⟨r,rr,rfl,rfl,hs⟩
  have actual':=actual.congr_in ReusableNative.local_heads.symm rfl
  have a:=ReusableNative.output_fits actual' hdata hfuel (20 : Fin 32)
  have b:=ReusableNative.output_fits actual' hdata hfuel (21 : Fin 32)
  simp only [ReusableNative.padded,h20,h21,ZeroPadding.pad_length] at a b
  exact ⟨(Nat.le_max_right _ _).trans_eq a,(Nat.le_max_right _ _).trans_eq b⟩

end PCJ9eff70d512234a4c_Fixed.Materializer.NativeNormalized
