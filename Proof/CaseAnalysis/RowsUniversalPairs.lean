import Proof.CaseAnalysis.RowsUniversalLowering
import Proof.CaseAnalysis.RowsRawPairSeekBody

/-! The paired reader views the existing source cache; it does not manufacture
a second cache or change the absolute child indices. -/
namespace NearCubicWires.RepairSource.CloseoutRowsUniversal
open SupplierPipeline RepairRepresentation CanonicalFourfoldRowProgram
open RepairOrdinary ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable {q : ℕ}

def pairs (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) : List CloseoutRowsRawPairSeek.Pair:=
  List.ofFn (fun i : Fin occ.length=>
    (cacheAtom a (pool live occ) (originalIndex live occ i),
      cacheAtom a (pool live occ) (constantIndex live occ i)))

theorem pairs_length (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) : (pairs a live occ).length=occ.length:=by
  simp only [pairs,List.length_ofFn]

theorem pairs_getElem (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (i : Fin occ.length) :
    (pairs a live occ)[i.val]'(by rw [pairs_length];exact i.isLt)=
      (cacheAtom a (pool live occ) (originalIndex live occ i),
       cacheAtom a (pool live occ) (constantIndex live occ i)):=by
  simp only [pairs,List.getElem_ofFn]

theorem pairs_flat (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) :
    (pairs a live occ).flatMap (fun p=>[p.1,p.2])=
      CloseoutRowsRawAtomCache.sourceCache a (pool live occ):=by
  let f : Fin (occ.length*2)→StructuralGF2Polynomial:=fun i=>
    cacheAtom a (pool live occ) ⟨i.val,by rw [pool_length];omega⟩
  have same:List.ofFn f=CloseoutRowsRawAtomCache.sourceCache a (pool live occ):=by
    apply List.ext_getElem
    · simp only [List.length_ofFn,CloseoutRowsRawAtomCache.source_length,pool_length]
      omega
    · intro i hi hj
      simp only [List.getElem_ofFn,f,cacheAtom]
  rw [←same,List.ofFn_mul]
  simp only [pairs,List.flatMap_def,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  simp [List.ofFn_succ,f,originalIndex,constantIndex,Nat.mul_comm]

theorem pairs_word (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) :
    CloseoutRowsRawPairSeek.cacheWord (pairs a live occ)=
      CloseoutRowsRawAtomSeek.cacheWord (CloseoutRowsRawAtomCache.sourceCache a (pool live occ)):=by
  rw [←pairs_flat a live occ]
  simp only [CloseoutRowsRawAtomSeek.cacheWord,List.flatMap_assoc,
    List.flatMap_cons,List.flatMap_nil,List.append_nil,
    CloseoutRowsRawPairSeek.cacheWord]
  rfl

theorem pairs_residual (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (i : Fin occ.length) :
    let p:=(pairs a live occ)[i.val]'(by rw [pairs_length];exact i.isLt)
    p.1++p.2=residualAtom a live occ i:=by
  simp only [pairs_getElem,residualAtom,structuralGF2Add]

end
end NearCubicWires.RepairSource.CloseoutRowsUniversal
