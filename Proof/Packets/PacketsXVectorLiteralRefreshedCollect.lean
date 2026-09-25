import Proof.Packets.PacketsXVectorLiteralCollectedProgram
import Proof.Packets.PacketsXVectorLiteralPaletteReuse

/-! Complete literal-vector construction followed by paid append of every
coordinate, preserving its exact ordinal and polynomial list ordering. -/
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


def literalPaletteRefreshCollectProgram := Composition.machine
  (TapeEmbedding.machine 1 literalPaletteRefreshProgram) collectMachine
def literalPaletteRefreshCollectFuel (C w M root depth S : Nat) :=
  literalPaletteRefreshFuel C w M root depth S+1+PacketVectorAppend.budget (commonReserve C w) (M+1)
attribute [local irreducible] literalPaletteRefreshProgram collectMachine

theorem literal_palette_refresh_collect_run (C w d population active depth root S : Nat)
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
    (work : Fin 299 → List Bool) (hwork : ∀i,(work i).length ≤ S)
    (pre rest : List Bool) :
    ∃output : Fin 299 → List Bool,
      Step literalPaletteRefreshCollectProgram (literalPaletteRefreshCollectFuel C w population root depth S)
        (collectHeads pre.length)
        (collectData (paddedPalette C (commonReserve C w) population root depth
          (parameters population active 0 (C+9) mask seed)) S work
          (pre++List.replicate ((population+1)*(2*commonReserve C w)) false++rest))
        (collectHeads (pre.length+(population+1)*(2*commonReserve C w)))
        (collectData (paddedPalette C (commonReserve C w) population root depth
          (parameters population active 0 (C+9) mask seed)) S output
          (pre++PacketVector.bank (commonReserve C w)
            (literalCoordinatePackets C population active depth mask seed wins)++rest)) ∧
      (∀i,(output i).length ≤ S) ∧ output 257=List.replicate S false ∧
      TranscriptRewindReady (commonReserve C w) S (population+1) output := by
  let R:=commonReserve C w
  let packets:=literalCoordinatePackets C population active depth mask seed wins
  let palette:=paddedPalette C R population root depth (parameters population active 0 (C+9) mask seed)
  obtain ⟨raw,build,hout,hvector,hcoordinates,hwidth,hcount,hscratch,hzero⟩:=literal_padded_palette_refresh_run
    C w d population active depth root S mask seed wins hd hrank hC hcodesC
    hpop hi hw hdegree hfit hsourcefit hatomfit hwin hW hroot hRS hCS hspace work hwork
  have plen : packets.length=population+1 := List.length_ofFn
  have reserve : C+2 ≤ R:=LiteralCacheReuse.reserve_width C w
  have fits : ∀P∈packets,PacketVector.Fits R P := by
    intro P hP
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hP
    exact packet_fits R _ (literal_coordinate_guards C w d population active depth mask seed wins j
      hd hcodesC hdegree hsourcefit hfit).2.2.2
  change raw 257=PacketVector.bank R packets at hcoordinates
  have hbank : (PacketVector.bank R packets).length ≤ S := by
    rw [←hcoordinates]
    exact hout 257
  have copied:=collect_palette_run R S packets pre rest palette raw (by omega) (by omega) fits hbank
    hcoordinates hwidth (by simpa only [plen] using hcount) hscratch hzero
  rw [plen] at copied
  have built:=build.embed (fun _ : Fin 1=>pre.length)
    (fun _ : Fin 1=>pre++List.replicate ((population+1)*(2*R)) false++rest)
  have joined:=built.seq copied
  let output:=Function.update (fun i=>ZeroPadding.pad S (raw i)) 257 (List.replicate S false)
  refine ⟨output,joined,?_,Function.update_self _ _ _,?_⟩
  · intro i
    by_cases hi:i=257
    · subst i;simp [output]
    · dsimp only [output]
      rw [Function.update_of_ne hi,ZeroPadding.pad_length]
      exact max_le le_rfl (hout i)
  · exact collect_ready R S (population+1) raw (by omega) hwidth hcount hscratch hzero

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
