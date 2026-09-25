import Proof.Packets.PacketsXWalkLiteralMastersFanout
import Proof.Packets.PacketsXWalkLiteralLoopData

/-! The initially generated zero seed is an original Toeplitz seed.
Its three words are overwritten by the actual vertex before each visit. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralMasters
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.CanonicalFourfoldRowProgram
open PCJ9eff70d512234a4c_Fixed.Materializer VectorBottomUp CloseoutRowsModeCache
open Theorem25Completion.CycleBounds
noncomputable section

def zeroSeed (rank : Nat) : ToeplitzSeed rank := ((fun _=>0,fun _=>0),fun _=>0)

theorem zero_bits (n R : Nat) (hn : n≤R) :
    ZeroPadding.pad R (CloseoutRowsModeHashMeaning.bits (fun _ : Fin n=>(0 : ZMod 2)))=
      List.replicate R false := by
  have bits : CloseoutRowsModeHashMeaning.bits (fun _ : Fin n=>(0 : ZMod 2))=List.replicate n false := by
    simp [CloseoutRowsModeHashMeaning.bits,List.ofFn_const]
  rw [bits,Rewind.Workspace.pad_zeros,Nat.max_eq_left hn]

theorem palette_eq_original (C R population active root depth : Nat) (mask : Finset (Fin population))
    (hr : canonicalGradedRank population active≤R) :
    palette C R root (canonicalGradedRank population active) depth population
      (List.ofFn (fun i=>decide (i∈mask)))=
    paddedPalette C R population root depth
      (parameters population active 0 (C+9) mask (zeroSeed (canonicalGradedRank population active))) := by
  have upper : canonicalGradedRank population active-1≤R := by omega
  have hz:=zero_bits (canonicalGradedRank population active) R hr
  have hu:=zero_bits (canonicalGradedRank population active-1) R upper
  funext i;fin_cases i <;>
    simp [palette,paddedPalette,coldPalette,parameters,zeroSeed,hz,hu,ZeroPadding.pad,
      UnaryTemplate.tape,CloseoutRowsModeHashMeaning.bits,List.ofFn_const,
      ←List.replicate_add,Nat.add_sub_of_le hr,Nat.add_sub_of_le upper]
  omega

theorem original_bounds {population active depth : Nat} (C w d root S L : Nat)
    (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (h : WalkLiteralLoop.Bounds C w d population active depth root S L wins) :
    Bounds C (commonReserve C w) root (canonicalGradedRank population active) depth population
      (List.ofFn (fun i=>decide (i∈mask))) := by
  have small : 258*population+2≤C :=
    (show 258*population+2≤(258*population+2)^2 from Nat.le_self_pow (by decide) _).trans h.populationCapacity
  have dsmall : depth+2*population+2≤C :=
    (show depth+2*population+2≤(depth+2*population+2)^2 from Nat.le_self_pow (by decide) _).trans h.codeCapacity
  have rank:=h.rankPopulation
  have root:=h.rootBound
  have reserve : 2*C+11≤commonReserve C w := by
    have he : 1≤2^(8*w):=Nat.one_le_pow _ _ (by decide)
    have hp : C+1≤(C+1)^4:=Nat.le_self_pow (by decide) _
    have hh:=Nat.mul_le_mul_left (65536*(C+1)^4) he
    unfold commonReserve
    nlinarith
  constructor
  all_goals first | (simp only [List.length_ofFn];omega) | omega

end
end Theorem25Completion.WalkLiteralMasters
