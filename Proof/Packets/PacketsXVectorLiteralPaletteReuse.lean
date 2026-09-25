import Proof.Packets.PacketsXVectorLiteralPaddedPaletteProgram
import Proof.Packets.PacketsXVectorLiteralPaletteReset

/-! Repeated literal-vector execution uses the same paid program and the
resident reset reserve. Every working tape is erased before fanout. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairSource.VerifierDecoding CloseoutRowsModeCache
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.RepairSource.CloseoutRawRows
open NormalizedFiniteTransport Theorem25Completion.CycleBounds SubstitutionCensus
noncomputable section

theorem palette_reuse_input (palette : Fin 15 → List Bool) (S : Nat) :
    (fun i=>ZeroPadding.pad (NativeFanout.caps 15 299 S i)
      (NativeFanout.input (m:=299) palette S i)) =
      paletteData palette S (fun _=>List.replicate S false) := by
  funext i
  refine Fin.addCases (m:=315) (n:=1) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=15) (n:=300) (fun j=>?_) (fun j=>?_) j
    · simp only [NativeFanout.caps,NativeFanout.input,paletteData,
        Fin.addCases_left,ZeroPadding.pad_zero]
    · refine Fin.addCases (m:=299) (n:=1) (fun j=>?_) (fun j=>?_) j <;>
        simp [NativeFanout.caps,NativeFanout.input,paletteData,ZeroPadding.pad]
  · simp [NativeFanout.caps,NativeFanout.input,paletteData,ZeroPadding.pad]

theorem palette_reuse_output (palette : Fin 15 → List Bool) (S : Nat)
    (output : Fin 299 → List Bool) :
    (fun i=>ZeroPadding.pad (NativeFanout.caps 15 299 S i)
      (paletteData palette S (fun j=>ZeroPadding.pad S (output j)) i)) =
      paletteData palette S (fun j=>ZeroPadding.pad S (output j)) := by
  funext i
  refine Fin.addCases (m:=315) (n:=1) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=15) (n:=300) (fun j=>?_) (fun j=>?_) j
    · simp only [NativeFanout.caps,paletteData,Fin.addCases_left,ZeroPadding.pad_zero]
    · refine Fin.addCases (m:=299) (n:=1) (fun j=>?_) (fun j=>?_) j
      · simp only [NativeFanout.caps,paletteData,Fin.addCases_left,Fin.addCases_right]
        exact MatrixBucketRootPower.pad_pad S S _ le_rfl
      · simp only [NativeFanout.caps,paletteData,Fin.addCases_left,Fin.addCases_right,
          ZeroPadding.pad_zero]
  · simp [NativeFanout.caps,paletteData,ZeroPadding.pad]

def literalPaletteRefreshProgram := Composition.machine paletteReset literalPaletteProgram
def literalPaletteRefreshFuel (C w M root depth S : Nat) :=
  2*S+7+literalPaletteFuel C w M root depth S

theorem palette_program_reuse {states fuel : Nat} (program : Machine 316 states)
    (palette : Fin 15 → List Bool) (S : Nat) (output : Fin 299 → List Bool)
    (run : Step program fuel (fun _=>0) (NativeFanout.input (m:=299) palette S)
      (paletteHeads VectorNumericArena.heads)
      (paletteData palette S (fun i=>ZeroPadding.pad S (output i)))) :
    Step program fuel (fun _=>0) (paletteData palette S (fun _=>List.replicate S false))
      (paletteHeads VectorNumericArena.heads)
      (paletteData palette S (fun i=>ZeroPadding.pad S (output i))) := by
  have padded:=run.pad (NativeFanout.caps 15 299 S)
  rw [palette_reuse_input,palette_reuse_output] at padded
  exact padded

theorem literal_padded_palette_refresh_run (C w d population active depth root S : Nat)
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
    (hspace : literalInitializedFuel C w population root depth+2 ≤ S)
    (work : Fin 299 → List Bool) (hwork : ∀i,(work i).length ≤ S) :
    ∃output : Fin 299 → List Bool,
      Step literalPaletteRefreshProgram (literalPaletteRefreshFuel C w population root depth S) (paletteHeads VectorNumericArena.heads)
        (paletteData
          (paddedPalette C (commonReserve C w) population root depth
            (parameters population active 0 (C+9) mask seed)) S work)
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
  obtain ⟨output,run,hout,hvector,hcoordinates,hwidth,hcount,hscratch,hzero⟩:=literal_padded_palette_program_run
    C w d population active depth root S mask seed wins hd hrank hC hcodesC
    hpop hi hw hdegree hfit hsourcefit hatomfit hwin hW hroot hRS hCS hspace
  have reused:=palette_program_reuse literalPaletteProgram _ S output run
  have reset:=palette_reset_run
    (paddedPalette C (commonReserve C w) population root depth
      (parameters population active 0 (C+9) mask seed)) S work hwork
  have joined:=reset.seq reused
  refine ⟨output,?_,hout,hvector,hcoordinates,hwidth,hcount,hscratch,hzero⟩
  simpa only [literalPaletteRefreshProgram,literalPaletteRefreshFuel,
    show 2*S+6+1=2*S+7 by omega] using joined

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
