import Proof.Packets.PacketsXRawSingletonSubstitution

/-! The same executed raw substitution retains the physically generated
zero backing of the reflected cache, as required between provider calls. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.RawSingletonSubstitution
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.CanonicalFourfoldRowProgram
open CloseoutRowsRawPairSeek (Pair cacheWord)

theorem cache_padding (R B : Nat) (source cache out : List Bool) :
    (fun i : Fin 12=>ZeroPadding.pad (if i=1 then B else 0) (bank R source cache out i))=
      bank R source (ZeroPadding.pad B cache) out := by
  funext i
  fin_cases i <;>simp [bank,words,Fin.addCases,ZeroPadding.pad_zero]

theorem run_cache_pad (R B d : Nat) (cs : List Pair)
    (hc : ∀ i (hi : i<cs.length),(cs[i].1++cs[i].2).length≤1)
    (P : StructuralGF2Polynomial) (hv : CloseoutRowsEstimator.SubstitutionOuter.Valid cs P)
    (hd : ∀ m∈P,m.length≤d) (hR : 1≤R)
    (hspace : CloseoutRowsEstimator.SubstitutionBounds.space cs 1 d (cacheWord cs).length≤R)
    (hcost : CloseoutRowsEstimator.SubstitutionBounds.fuel cs 1 d P.length≤R+3) :
    Step machine (budget cs d P.length) (fun _=>0)
      (bank R (ExtIncidence.stream P) (ZeroPadding.pad B (cacheWord cs)) [])
      (fun _=>0) (bank R (ExtIncidence.stream P) (ZeroPadding.pad B (cacheWord cs))
        (ExtIncidence.stream (structuralGF2Substitute (CloseoutRowsEstimator.SubstitutionMonomial.atom cs) P))) := by
  have h:=(run R d cs hc P hv hd hR hspace hcost).pad (fun i : Fin 12=>if i=1 then B else 0)
  simpa only [cache_padding] using h

end PCJ9eff70d512234a4c_Fixed.Materializer.RawSingletonSubstitution
