import Proof.Packets.PacketsXVectorLiteralInitializedProgram
import Proof.Packets.PacketsXVectorLiteralPaletteBounds
import Proof.Packets.PacketsXVectorLiteralPaletteDock

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

def literalPaletteProgram := Composition.machine coldPaletteBoot
  (RecoveryFocus.machine paletteArenaSlots literalInitializedProgram)
def literalPaletteFuel (C w M root depth S : Nat) := 2*S+7+literalInitializedFuel C w M root depth
attribute [local irreducible] coldPaletteBoot literalInitializedProgram

theorem literal_palette_program_run (C w d population active depth root S : Nat)
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
          (coldPalette C (commonReserve C w) population root depth
            (parameters population active 0 (C+9) mask seed)) S)
        (paletteHeads VectorNumericArena.heads)
        (paletteData (coldPalette C (commonReserve C w) population root depth
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
  let R:=commonReserve C w
  let p:=parameters population active 0 (C+9) mask seed
  have hsmall : 258*population+2 ≤ C :=
    (show 258*population+2 ≤ (258*population+2)^2 from Nat.le_self_pow (by decide) _).trans hC
  have hdepth : depth+2*population+2 ≤ C :=
    (show depth+2*population+2 ≤ (depth+2*population+2)^2 from Nat.le_self_pow (by decide) _).trans hcodesC
  have bounds : ColdWordBounds C R population root depth p :=
    cold_original_word_bounds C w population active root depth mask seed (by omega) (by omega) (by omega) (by omega)
  have hcold:=cold_words_state C R population root depth p bounds
  obtain ⟨left,right,pi,outFields,outExtra,body,_,_,_⟩:=literal_initialized_program_run
    C w d population active depth root mask seed wins
    (coldFields C R population root depth p) (coldExtra R)
    hd hrank hC hcodesC hpop hi hw hdegree hfit hsourcefit hatomfit hwin hW hroot hcold
  let output : Fin 299 → List Bool :=
    Fin.addCases (m:=298) (n:=1) (motive:=fun _=>List Bool)
      (levelData C R (population+1) (population+1) pi 0 left right
        (vectorBank C R (NormalizedVector.table (canonicalGradedLabel population active) seed wins 0 depth))
        (PacketVector.bank R (List.ofFn (fun candidate : Fin (population+1)=>
          (Normalized.structuralMaskedListCoordinate mask (canonicalGradedLabel population active) seed wins 0 candidate).map (maskNat C))))
        outFields outExtra) (fun _ : Fin 1=>WindowSeed.source R depth)
  rw [←initialized_heads] at body
  change Step literalInitializedProgram (literalInitializedFuel C w population root depth)
    VectorNumericArena.heads (coldData C R (coldFields C R population root depth p) (coldExtra R))
    VectorNumericArena.heads output at body
  have hout:=cold_run_output_length literalInitializedProgram C R population root depth S p output
    bounds hRS hCS hspace body
  have lifted:=palette_dock_run literalInitializedProgram (coldPalette C R population root depth p)
    S _ _ _ _ (body.pad (fun _=>S))
  have boot:=cold_palette_boot_run C R population root depth S p bounds hRS hCS
  have run:=boot.seq lifted
  refine ⟨output,?_,hout,rfl,rfl,rfl,rfl,rfl,rfl⟩
  simpa only [literalPaletteProgram,literalPaletteFuel,
    show 2*S+6+1=2*S+7 by omega] using run

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
