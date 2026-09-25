import Proof.Packets.PacketsXWindowRawMeaning
import Proof.Packets.WindowSourceClose

/-! The executed reflected-cache renaming and native normalizer return the
literal frozen window polynomial on the arithmetic operand ports. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.CanonicalFourfoldRowProgram
open CloseoutRowsRawPairSeek (Pair cacheWord)
open NormalizedFiniteTransport WindowNativeOrder

def renamed (codes : List Nat) (v offset width target : Nat) :=
  structuralGF2Substitute (CloseoutRowsEstimator.SubstitutionMonomial.atom (literalPairs codes))
    (positionalWindow v codes.length offset width target)

theorem window_run (C R : Nat) (codes : List Nat) (hc : codes.Pairwise (·<·))
    (hcodes : ∀ c∈codes,c<C) (v offset width target : Nat) (hM : codes.length≤2^v)
    (hR : 1≤R) (hC : C≤R)
    (hspace : CloseoutRowsEstimator.SubstitutionBounds.space (literalPairs codes) 1 width
      (cacheWord (literalPairs codes)).length≤R)
    (hcost : CloseoutRowsEstimator.SubstitutionBounds.fuel (literalPairs codes) 1 width
      (positionalWindow v codes.length offset width target).length≤R+3)
    (H : Fin 256→Nat) (A : Fin 256→List Bool)
    (hh : ∀ i,H (rawPorts i)=0)
    (ha : ∀ i,A (rawPorts i)=RawSingletonSubstitution.bank R
      (ExtIncidence.stream (positionalWindow v codes.length offset width target))
      (ZeroPadding.pad R (cacheWord (literalPairs codes))) [] i)
    (hn : ∀ i,ReusableNative.heads i=H (nativePorts i))
    (an : ∀ i,A (nativePorts i)=ReusableNative.ready C R [] i)
    (hdata : ∀ i,(NativeNormalized.A C (renamed codes v offset width target) [] i).length≤R)
    (hfuel : NativeNormalized.budget C (renamed codes v offset width target)+3≤R) :
    Step renameNormalize
      (RawSingletonSubstitution.budget (literalPairs codes) width
        (positionalWindow v codes.length offset width target).length+1+
        ReusableNative.budget (NativeNormalized.budget C (renamed codes v offset width target)) R)
      H A H (completed R
        ((Normalized.structuralGF2ConsecutiveWindowIndicator codes offset width target).map (maskNat C)) A) := by
  have hp:=renamed_fits C codes hc hcodes v offset width target hM
  have run:=rename_normalize_run C R width (literalPairs codes) (literalPairs_count codes)
    (positionalWindow v codes.length offset width target) (literal_valid codes v offset width target hM)
    (fun m hm=>(window_bounds v codes.length offset width target hM m hm).1) hR hC hspace hcost
    H A hh ha hn an hp hdata hfuel
  have he : NormalizerOrder.ordered (NativeNormalized.masks C (renamed codes v offset width target))=
      (Ring.norm (renamed codes v offset width target)).map (maskNat C) := normalized_masks_nat C _ hp
  change NormalizerOrder.ordered (NativeNormalized.masks C
      (structuralGF2Substitute (CloseoutRowsEstimator.SubstitutionMonomial.atom (literalPairs codes))
        (positionalWindow v codes.length offset width target)))=_ at he
  rw [he] at run
  simp only [renamed,normalized_literal_window codes hc v offset width target hM] at run
  exact run

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
