import Proof.Packets.PacketsXNormalizedFiniteTransport
import Proof.Packets.PacketsXWindowPositionalBounds
import Proof.Packets.PacketsXWindowRawDock
import Proof.Packets.ReflectedLiteralCache

/-! The actual reflected singleton-cache lookup has exactly the frozen
literal-window meaning, including both polynomial and monomial list order. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.CanonicalFourfoldRowProgram
open CloseoutRowsRawPairSeek (Pair cacheWord)
open NormalizedFiniteTransport WindowNativeOrder

def literalPairs (codes : List Nat) : List Pair := codes.reverse.map (fun c=>([[c]],[]))

theorem literalPairs_length (codes : List Nat) : (literalPairs codes).length=codes.length := by
  simp [literalPairs]

theorem literalPairs_count (codes : List Nat) (i : Nat) (hi : i<(literalPairs codes).length) :
    ((literalPairs codes)[i].1++(literalPairs codes)[i].2).length≤1 := by
  simp [literalPairs,List.getElem_map]

theorem literal_atom (codes : List Nat) (i : Nat) (hi : i<codes.length) :
    CloseoutRowsEstimator.SubstitutionMonomial.atom (literalPairs codes) i=[[SubsetOrder.lookup codes.reverse i]] := by
  rw [CloseoutRowsEstimator.SubstitutionMonomial.atom_eq _ i (by simpa [literalPairs] using hi)]
  simp [literalPairs,SubsetOrder.lookup,List.getElem?_eq_getElem (by simpa using hi : i<codes.reverse.length)]

theorem literal_valid (codes : List Nat) (v offset width target : Nat) (hM : codes.length≤2^v) :
    CloseoutRowsEstimator.SubstitutionOuter.Valid (literalPairs codes)
      (positionalWindow v codes.length offset width target) := by
  intro m hm i hi
  rw [literalPairs_length]
  exact (window_bounds v codes.length offset width target hM m hm).2 i hi

theorem renamed_window (codes : List Nat) (v offset width target : Nat) (hM : codes.length≤2^v) :
    structuralGF2Substitute (CloseoutRowsEstimator.SubstitutionMonomial.atom (literalPairs codes))
      (positionalWindow v codes.length offset width target)=
      WindowHomogeneousOrder.nativeWindow codes v offset width target := by
  rw [SingletonSubstitution.substitute_congr_on (SubsetOrder.lookup codes.reverse) _ _ (by
    intro m hm i hi
    exact literal_atom codes i ((window_bounds v codes.length offset width target hM m hm).2 i hi))]
  exact reflected_window codes v offset width target

theorem renamed_fits (C : Nat) (codes : List Nat) (hc : codes.Pairwise (·<·)) (hcodes : ∀ c∈codes,c<C)
    (v offset width target : Nat) (hM : codes.length≤2^v) :
    Fits C (structuralGF2Substitute (CloseoutRowsEstimator.SubstitutionMonomial.atom (literalPairs codes))
      (positionalWindow v codes.length offset width target)) := by
  rw [renamed_window codes v offset width target hM]
  intro m hm c hcm
  exact hcodes c (WindowHomogeneousOrder.nativeWindow_support codes hc v offset width target hM m hm c hcm)

theorem normalized_literal_window (codes : List Nat) (hc : codes.Pairwise (·<·))
    (v offset width target : Nat) (hM : codes.length≤2^v) :
    Ring.norm (structuralGF2Substitute (CloseoutRowsEstimator.SubstitutionMonomial.atom (literalPairs codes))
      (positionalWindow v codes.length offset width target))=
      Normalized.structuralGF2ConsecutiveWindowIndicator codes offset width target := by
  rw [renamed_window codes v offset width target hM]
  exact WindowHomogeneousOrder.nativeWindow_exact codes hc v offset width target hM

theorem cache_source (tag count : Nat) :
    cacheWord (literalPairs (ReflectedLiteralCache.codes tag count))=ReflectedLiteralCache.stream tag count := by
  rw [ReflectedLiteralCache.stream_eq]
  rfl

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
