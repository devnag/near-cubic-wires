import Proof.Packets.WindowNativeDock
import Proof.Packets.PacketsXRawSingletonPaddedCache

/-! Actual singleton-cache renaming in the fixed provider arena. Only native
source122 changes; all source, cache and reusable scratch words are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.CanonicalFourfoldRowProgram
open CloseoutRowsRawPairSeek (Pair cacheWord)

noncomputable def rename := RecoveryFocus.machine rawPorts RawSingletonSubstitution.machine

theorem raw_bank_outside (R : Nat) (source cache out : List Bool) (i : Fin 12) (hi : i≠10) :
    RawSingletonSubstitution.bank R source cache out i=RawSingletonSubstitution.bank R source cache [] i := by
  fin_cases i <;>simp_all [RawSingletonSubstitution.bank,RawSingletonSubstitution.words,Fin.addCases]

theorem rename_run (R d : Nat) (cs : List Pair)
    (hc : ∀ i (hi : i<cs.length),(cs[i].1++cs[i].2).length≤1)
    (P : StructuralGF2Polynomial) (hv : CloseoutRowsEstimator.SubstitutionOuter.Valid cs P)
    (hd : ∀ m∈P,m.length≤d) (hR : 1≤R)
    (hspace : CloseoutRowsEstimator.SubstitutionBounds.space cs 1 d (cacheWord cs).length≤R)
    (hcost : CloseoutRowsEstimator.SubstitutionBounds.fuel cs 1 d P.length≤R+3)
    (H : Fin 256→Nat) (A : Fin 256→List Bool)
    (hh : ∀ i,H (rawPorts i)=0)
    (ha : ∀ i,A (rawPorts i)=RawSingletonSubstitution.bank R (ExtIncidence.stream P) (ZeroPadding.pad R (cacheWord cs)) [] i) :
    Step rename (RawSingletonSubstitution.budget cs d P.length) H A H
      (withSource R (ExtIncidence.stream (structuralGF2Substitute
        (CloseoutRowsEstimator.SubstitutionMonomial.atom cs) P)) A) := by
  apply PhysicalFocusBoundary.focus (RawSingletonSubstitution.run_cache_pad R R d cs hc P hv hd hR hspace hcost)
    rawPorts raw_injective H H A _ (fun i=>(hh i).symm) (fun i=>(ha i).symm) (fun i=>(hh i).symm)
  · intro i
    by_cases hi : i=10
    · subst i;rfl
    have hn : rawPorts i≠122 := by intro he;apply hi;apply raw_injective;exact he
    simp only [withSource,Function.update_of_ne hn]
    exact (raw_bank_outside R _ _ _ i hi).trans (ha i).symm
  · intro i away
    have hn : i≠122 := by intro he;subst i;exact away 10 rfl
    exact ⟨rfl,by simp only [withSource,Function.update_of_ne hn]⟩

noncomputable def renameNormalize := Composition.machine rename normalize

theorem rename_normalize_run (C R d : Nat) (cs : List Pair)
    (hc : ∀ i (hi : i<cs.length),(cs[i].1++cs[i].2).length≤1)
    (P : StructuralGF2Polynomial) (hv : CloseoutRowsEstimator.SubstitutionOuter.Valid cs P)
    (hd : ∀ m∈P,m.length≤d) (hR : 1≤R) (hC : C≤R)
    (hspace : CloseoutRowsEstimator.SubstitutionBounds.space cs 1 d (cacheWord cs).length≤R)
    (hcost : CloseoutRowsEstimator.SubstitutionBounds.fuel cs 1 d P.length≤R+3)
    (H : Fin 256→Nat) (A : Fin 256→List Bool)
    (hh : ∀ i,H (rawPorts i)=0)
    (ha : ∀ i,A (rawPorts i)=RawSingletonSubstitution.bank R (ExtIncidence.stream P) (ZeroPadding.pad R (cacheWord cs)) [] i)
    (hn : ∀ i,ReusableNative.heads i=H (nativePorts i))
    (an : ∀ i,A (nativePorts i)=ReusableNative.ready C R [] i)
    (hp : ∀ m∈structuralGF2Substitute (CloseoutRowsEstimator.SubstitutionMonomial.atom cs) P,∀code∈m,code<C)
    (hdata : ∀ i,(NativeNormalized.A C (structuralGF2Substitute (CloseoutRowsEstimator.SubstitutionMonomial.atom cs) P) [] i).length≤R)
    (hfuel : NativeNormalized.budget C (structuralGF2Substitute (CloseoutRowsEstimator.SubstitutionMonomial.atom cs) P)+3≤R) :
    Step renameNormalize
      (RawSingletonSubstitution.budget cs d P.length+1+
        ReusableNative.budget (NativeNormalized.budget C (structuralGF2Substitute (CloseoutRowsEstimator.SubstitutionMonomial.atom cs) P)) R)
      H A H (completed R (NormalizerOrder.ordered (NativeNormalized.masks C
        (structuralGF2Substitute (CloseoutRowsEstimator.SubstitutionMonomial.atom cs) P))) A) :=
  (rename_run R d cs hc P hv hd hR hspace hcost H A hh ha).seq
    (normalize_run C R _ H A hC hR hn an hp hdata hfuel)

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
