import Proof.Packets.PacketsXVectorLiteralRefreshedCollect
import Proof.Packets.PacketsXWalkPaletteAssociativity

/-! One complete paid walk visit: decode the resident vertex, overwrite
its three Toeplitz seed words, rebuild all literal coordinates, and append
the resulting vector to the ordered transcript. No execution is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralVisit
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.RepairSource.CloseoutRawRows
open PCJ9eff70d512234a4c_Fixed.Materializer
open CloseoutRowsModeCache NormalizedFiniteTransport Theorem25Completion.CycleBounds
open VectorBottomUp SubstitutionCensus
noncomputable section

def H (position dest : Nat) : Fin 332 → Nat :=
  Fin.addCases (m:=15) (n:=317) (motive:=fun _=>Nat)
    (WalkSeedResident.heads position) (collectHeads dest)
def A (rank R L S : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank)) (code : List Bool)
    (palette : Fin 15 → List Bool) (work : Fin 299 → List Bool) (transcript : List Bool) : Fin 332 → List Bool :=
  Fin.addCases (m:=15) (n:=317) (motive:=fun _=>List Bool)
    (WalkSeedResident.input rank R L v code) (collectData palette S work transcript)
def machine := Composition.machine (TapeEmbedding.machine 1 WalkPaletteSeedReady.machine)
  (PhysicalPrepend.machine 15 literalPaletteRefreshCollectProgram)
def budget (rank C w M root depth S : Nat) :=
  WalkPaletteSeedReady.budget rank (commonReserve C w)+1+
    literalPaletteRefreshCollectFuel C w M root depth S
attribute [local irreducible] WalkPaletteSeedReady.machine literalPaletteRefreshCollectProgram

theorem run (C w d population active depth root S L position : Nat)
    (mask : Finset (Fin population)) (old : ToeplitzSeed (canonicalGradedRank population active))
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
    (pre rest : List Bool)
    (hr : 0<canonicalGradedRank population active)
    (hdecode : 8*canonicalGradedRank population active+14 ≤ commonReserve C w)
    (v : MargulisVertex (2^toeplitzWalkSideBits (canonicalGradedRank population active))) (code : List Bool) :
    ∃output : Fin 299 → List Bool,
      Step machine (budget (canonicalGradedRank population active) C w population root depth S)
        (H position pre.length)
        (A (canonicalGradedRank population active) (commonReserve C w) L S v code
          (paddedPalette C (commonReserve C w) population root depth
            (parameters population active 0 (C+9) mask old)) work
          (pre++List.replicate ((population+1)*(2*commonReserve C w)) false++rest))
        (H position (pre.length+(population+1)*(2*commonReserve C w)))
        (A (canonicalGradedRank population active) (commonReserve C w) L S v code
          (paddedPalette C (commonReserve C w) population root depth
            (parameters population active 0 (C+9) mask
              ((toeplitzWalkEncoding (canonicalGradedRank population active) v).1))) output
          (pre++PacketVector.bank (commonReserve C w)
            (literalCoordinatePackets C population active depth mask
              ((toeplitzWalkEncoding (canonicalGradedRank population active) v).1) wins)++rest)) ∧
      (∀i,(output i).length ≤ S) ∧ output 257=List.replicate S false ∧
      TranscriptRewindReady (commonReserve C w) S (population+1) output := by
  let rank:=canonicalGradedRank population active
  let R:=commonReserve C w
  let seed:=(toeplitzWalkEncoding rank v).1
  have decode:=WalkLiteralSeedReady.run C R L S population active root depth position mask old hr hdecode
    v code VectorNumericArena.heads work
  have first:=decode.embed (fun _ : Fin 1=>pre.length)
    (fun _ : Fin 1=>pre++List.replicate ((population+1)*(2*R)) false++rest)
  simp only [WalkPaletteSeedReady.H,WalkPaletteSeedReady.A,WalkPaletteAssociativity.append] at first
  obtain ⟨output,collect,hlen,hzero,hready⟩:=literal_palette_refresh_collect_run
    C w d population active depth root S mask seed wins hd hrank hC hcodesC hpop hi hw
    hdegree hfit hsourcefit hatomfit hwin hW hroot hRS hCS hspace work hwork pre rest
  have second:=PhysicalPrepend.run collect (WalkSeedResident.heads position)
    (WalkSeedResident.input rank R L v code)
  have joined:=first.seq second
  exact ⟨output,joined,hlen,hzero,hready⟩

end
end Theorem25Completion.WalkLiteralVisit
