import Proof.Packets.PacketsXVectorLiteralPalette
import Proof.Packets.PhysicalStepSupport

/-! Original Toeplitz and occurrence words discharge every cold-word bound. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairSource.VerifierDecoding CloseoutRowsModeCache
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.CanonicalFourfoldRowProgram Theorem25Completion.CycleBounds
noncomputable section

theorem cold_original_word_bounds (C w population active root depth : Nat)
    (mask : Finset (Fin population)) (seed : ToeplitzSeed (canonicalGradedRank population active))
    (hrank : canonicalGradedRank population active ≤ C) (hpop : population ≤ C)
    (hd : depth ≤ C) (hroot : root ≤ commonReserve C w) :
    ColdWordBounds C (commonReserve C w) population root depth
      (parameters population active 0 (C+9) mask seed) := by
  have reserve : C+10 ≤ commonReserve C w := by
    have he : 1≤2^(8*w):=Nat.one_le_pow _ _ (by decide)
    have hp : C+1≤(C+1)^4:=Nat.le_self_pow (by decide) _
    unfold commonReserve
    nlinarith [Nat.mul_le_mul_left (65536*(C+1)^4) he]
  refine ⟨reserve,by omega,hroot,by omega,?_,?_,?_,?_,?_,?_⟩
  all_goals simp only [parameters,CloseoutRowsModeHashMeaning.bits,List.length_ofFn]
  all_goals omega

theorem cold_data_length (C R M root depth S : Nat) (p : Parameters)
    (h : ColdWordBounds C R M root depth p) (hRS : R+3 ≤ S) (hCS : 2*C+5 ≤ S) :
    ∀i,(coldData C R (coldFields C R M root depth p) (coldExtra R) i).length ≤ S := by
  have hpalette:=cold_palette_length C R M root depth S p h hRS hCS
  have he:=cold_palette_data C R M root depth S p hRS
  intro i
  have hf : (NativeFanout.word coldSelect (coldPalette C R M root depth p) i).length ≤ S := by
    unfold NativeFanout.word
    cases hi : coldSelect i with
    | none => simp
    | some j => exact hpalette j
  have hh:=congrArg List.length (congrFun he i)
  simp only [ZeroPadding.pad_length,Nat.max_eq_left hf] at hh
  omega

theorem cold_run_output_length {s fuel : Nat} (machine : Machine 299 s)
    (C R M root depth S : Nat) (p : Parameters) (out : Fin 299 → List Bool)
    (h : ColdWordBounds C R M root depth p) (hRS : R+3 ≤ S) (hCS : 2*C+5 ≤ S)
    (hf : fuel+2 ≤ S)
    (run : Step machine fuel VectorNumericArena.heads
      (coldData C R (coldFields C R M root depth p) (coldExtra R)) VectorNumericArena.heads out) :
    ∀i,(out i).length ≤ S := by
  apply run.tapes_bounded S 1 S
  · have all : ∀i,VectorNumericArena.heads i ≤ 1 := by decide
    exact all
  · exact cold_data_length C R M root depth S p h hRS hCS
  · exact le_rfl
  · omega

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
