import Proof.Packets.PacketsXVectorLiteralPaletteProgram
import Proof.Packets.PacketsXVectorLiteralPalettePadding

/-! Physical palette distribution, initialization, bottom-up vector loop,
and every masked coordinate in one fixed 316-tape ordinary machine. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.RepairSource.CloseoutRawRows
open NearCubicWires.ExtIncidence
open CloseoutRowsModeCache NormalizedFiniteTransport Theorem25Completion.CycleBounds SubstitutionCensus
noncomputable section

theorem literal_padded_palette_program_run (C w d population active depth root S : Nat)
    (mask : Finset (Fin population)) (seed : ToeplitzSeed (canonicalGradedRank population active))
    (wins : Fin depth → Nat)
    (hd : depth≤canonicalGradedRank population active)
    (hrank : canonicalGradedRank population active≤9*population)
    (hC : (258*population+2)^2≤C) (hcodesC : (depth+2*population+2)^2≤C)
    (hpop : 1≤population) (hi : population≤2^(canonicalGradedRank population active))
    (hw : 3≤w) (hdegree : structuralListCoordinateRawDegree depth wins 0≤d)
    (hfit : (population*(2*depth+1)+2)^d≤2^w)
    (hsourcefit : (population+1)^d≤2^w) (hatomfit : population+1≤2^w)
    (hwin : ∀level,wins level=GradedWindow.window root level.val)
    (hW : ∀level,wins level≤64*(C+2)) (hroot : root+67≤commonReserve C w)
    (hRS : commonReserve C w+3 ≤ S) (hCS : 2*C+5 ≤ S)
    (hspace : literalInitializedFuel C w population root depth+2 ≤ S) :
    ∃output : Fin 299 → List Bool,
      Step literalPaletteProgram (literalPaletteFuel C w population root depth S) (fun _=>0)
        (NativeFanout.input (m:=299)
          (paddedPalette C (commonReserve C w) population root depth
            (parameters population active 0 (C+9) mask seed)) S)
        (paletteHeads VectorNumericArena.heads)
        (paletteData (paddedPalette C (commonReserve C w) population root depth
          (parameters population active 0 (C+9) mask seed)) S
          (fun i=>ZeroPadding.pad S (output i))) ∧
      (∀i,(output i).length ≤ S) ∧
      output 256=vectorBank C (commonReserve C w)
        (NormalizedVector.table (canonicalGradedLabel population active) seed wins 0 depth) ∧
      output 257=PacketVector.bank (commonReserve C w) (List.ofFn (fun candidate : Fin (population+1)=>
        (Normalized.structuralMaskedListCoordinate mask (canonicalGradedLabel population active) seed wins 0 candidate).map (maskNat C))) ∧
      output 31=UnaryTemplate.tape (commonReserve C w) ∧
      output 297=ZeroPadding.pad (commonReserve C w) (CompareMachine.word (population+1)) ∧
      output 261=ZeroPadding.pad (commonReserve C w) [] ∧
      output 263=List.replicate (commonReserve C w) false := by
  obtain ⟨output,run,hout,hvector,hcoordinates,hwidth,hcount,hscratch,hzero⟩:=literal_palette_program_run
    C w d population active depth root S mask seed wins hd hrank hC hcodesC
    hpop hi hw hdegree hfit hsourcefit hatomfit hwin hW hroot hRS hCS hspace
  have padded:=run.pad (paletteMasterCaps (commonReserve C w))
  rw [palette_pad_input,palette_pad_data] at padded
  exact ⟨output,padded,hout,hvector,hcoordinates,hwidth,hcount,hscratch,hzero⟩

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
