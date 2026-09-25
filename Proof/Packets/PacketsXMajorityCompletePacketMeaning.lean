import Proof.Assembly.Packets
import Proof.Packets.PacketsXNormalizedSubstitutionExt
import Proof.Packets.PacketsXSubstitutionNat

/-! Exact specialization to the real packet parent. Lowering keeps its
tail-first normalized substitution, and the final normalization is performed
once before the increasing live-assignment relabelling loop. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.PacketMeaning
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.CanonicalFourfoldRowProgram
open NormalizedFiniteTransport NormalizedIntermediate
noncomputable section
variable {q L : Nat}

def childCount (a : DecompositionAlgorithm) (F : Packets.Family q L) :=
  (C10SupplierRowInput.childList a (Packets.live F) F.occurrences).length
def atom (a : DecompositionAlgorithm) (F : Packets.Family q L) (code : Nat) :=
  Ring.norm (CloseoutRowsUniversal.atomOfCode a (Packets.live F) F.occurrences code)
def atoms (C : Nat) (a : DecompositionAlgorithm) (F : Packets.Family q L) :=
  List.ofFn (fun i : Fin C=>atom a F i.val)

private theorem cache_valid (a : DecompositionAlgorithm)
    (gs : List (NearCubicWires.SupplierPipeline.SupportedNormalizedGate q)) (i : Fin gs.length) :
    ∀m∈CloseoutRowsUniversal.cacheAtom a gs i, ∀c∈m,c<(ExtDecompositionBatch.GS a gs).length := by
  unfold CloseoutRowsUniversal.cacheAtom
  rw [CloseoutRowsRawAtomCache.source_getElem]
  exact CloseoutRowsRawAtomMeaning.indices_valid a gs i

theorem atom_bounded (a : DecompositionAlgorithm) (F : Packets.Family q L) (code : Nat) :
    Bounded (Finset.range (childCount a F)) 1 (atom a F code) := by
  refine ⟨LiteralAlphabet.good_norm _ _ ?_,Ring.degree_norm (CloseoutRowsUniversal.atom_degree _ _ _ _)⟩
  unfold CloseoutRowsUniversal.atomOfCode
  split
  · intro m hm c hc
    rcases List.mem_append.mp hm with hm|hm
    · exact Finset.mem_range.mpr (cache_valid a _ _ m hm c hc)
    · exact Finset.mem_range.mpr (cache_valid a _ _ m hm c hc)
  · intro m hm
    cases hm

theorem atoms_length (C : Nat) (a : DecompositionAlgorithm) (F : Packets.Family q L) :
    (atoms C a F).length=C := List.length_ofFn

theorem atoms_get (C : Nat) (a : DecompositionAlgorithm) (F : Packets.Family q L)
    (code : Nat) (hc : code<C) : (atoms C a F).getD code []=atom a F code := by
  rw [List.getD_eq_getElem _ _ (by rw [atoms_length];exact hc)]
  simp only [atoms,List.getElem_ofFn]

theorem atoms_bounded (C : Nat) (a : DecompositionAlgorithm) (F : Packets.Family q L) :
    ∀P∈atoms C a F,Bounded (Finset.range (childCount a F)) 1 P := by
  intro P hP
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hP
  exact atom_bounded a F i.val

theorem lowered_exact (C : Nat) (a : DecompositionAlgorithm) (F : Packets.Family q L)
    (r : Packets.Row F.occurrences L) (hP : Fits C r.polynomial) :
    Normalized.structuralGF2Substitute (fun code=>(atoms C a F).getD code []) r.polynomial=
      Packets.lowered a F r := by
  apply NormalizedSubstitutionExt.on_support
  intro m hm code hc
  exact atoms_get C a F code (hP m hm code hc)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.PacketMeaning
