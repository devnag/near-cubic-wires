import Proof.Packets.PacketsXVectorLiteralCoordinates
import Proof.Packets.PhysicalDriverAssociativity

/-! One fixed ordinary 299-tape program builds the literal vector and then
materializes every normalized masked coordinate by whole-coordinate
substitution. All three nested vector loops and the coordinate loop use
concrete machines with proved executions. -/
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
open CloseoutRowsModeCache NormalizedFiniteTransport Theorem25Completion.CycleBounds SubstitutionCensus
noncomputable section

def literalProgram:=Composition.machine (machine WindowProvider.literalProvider WindowProvider.levelProvider)
  (TapeEmbedding.machine 2 (collectedCandidates literalCoordinateCallback))
attribute [local irreducible] machine collectedCandidates literalCoordinateCallback

def literalProgramFuel (C w M root depth : Nat):=
  depth*(literalLevelFuel C w M root depth+2*depth+6)+4+literalCoordinatesFuel C w M

theorem literal_program_run (C w d population active depth root : Nat)
    (mask : Finset (Fin population)) (seed : ToeplitzSeed (canonicalGradedRank population active))
    (wins : Fin depth → Nat) (input : Fin 298 → List Bool)
    (hd : depth≤canonicalGradedRank population active)
    (hrank : canonicalGradedRank population active≤9*population)
    (hC : (258*population+2)^2≤C) (hcodesC : (depth+2*population+2)^2≤C)
    (hpop : 1≤population) (hi : population≤2^(canonicalGradedRank population active))
    (hw : 3≤w) (hdegree : structuralListCoordinateRawDegree depth wins 0≤d)
    (hfit : (population*(2*depth+1)+2)^d≤2^w)
    (hsourcefit : (population+1)^d≤2^w) (hatomfit : population+1≤2^w)
    (hwin : ∀level,wins level=GradedWindow.window root level.val)
    (hW : ∀level,wins level≤64*(C+2)) (hroot : root+67≤commonReserve C w)
    (hinput : LevelReady C (commonReserve C w) (population+1) depth
      (NormalizedVector.table (canonicalGradedLabel population active) seed wins 0)
      (literalLoopState C (commonReserve C w) population root depth
        (parameters population active 0 (C+9) mask seed) (List.replicate C [])) 0 input) :
    ∃left right pi fields extra,
      Step literalProgram (literalProgramFuel C w population root depth)
        (Fin.addCases (levelH (fun _ : Fin 222=>0)) (fun _ : Fin 1=>1))
        (Fin.addCases input (fun _ : Fin 1=>WindowSeed.source (commonReserve C w) depth))
        (Fin.addCases (levelH (fun _ : Fin 222=>0)) (fun _ : Fin 1=>1))
        (Fin.addCases (levelData C (commonReserve C w) (population+1) (population+1) pi 0 left right
          (vectorBank C (commonReserve C w) (NormalizedVector.table (canonicalGradedLabel population active) seed wins 0 depth))
          (PacketVector.bank (commonReserve C w) (List.ofFn (fun candidate : Fin (population+1)=>
            (Normalized.structuralMaskedListCoordinate mask (canonicalGradedLabel population active) seed wins 0 candidate).map (maskNat C))))
          fields extra) (fun _ : Fin 1=>WindowSeed.source (commonReserve C w) depth)) ∧
      VectorAccumulator.Fits (commonReserve C w) left ∧ VectorAccumulator.Fits (commonReserve C w) right ∧
      LiteralLevelState C (commonReserve C w) population root (parameters population active 0 (C+9) mask seed)
        (denseLevels C population depth (parameters population active 0 (C+9) mask seed) (List.replicate C []) depth) fields extra := by
  let R:=commonReserve C w
  obtain ⟨middle,build,ci,pi,left,right,fields,extra,hci,_hpi,hq,rfl⟩:=literal_complete_loop C w d population active depth root
    mask seed wins (List.replicate C []) input hd hrank hC hcodesC hpop hi hw hdegree hfit hwin hW hroot hinput
  obtain ⟨hl,hr,hs⟩:=hq
  simp only [Nat.sub_self] at build
  obtain ⟨left',right',fields',coordinates,hl',hr',hs'⟩:=literal_coordinates_run C w d population active depth root ci pi 0
    mask seed wins hd hcodesC (by omega) hdegree hsourcefit hatomfit hfit left right [] fields extra hl hr hci hs
  have embedded:=coordinates.embed (fun _ : Fin 2=>1)
    (![WindowSeed.source R (population+1),WindowSeed.source R depth] : Fin 2 → List Bool)
  have pairOne : (![1,1] : Fin 2 → Nat)=(fun _=>1) := by funext i;fin_cases i <;>rfl
  have joinedHead : Fin.addCases (m:=297) (n:=2) (motive:=fun _=>Nat)
      (Fin.addCases (m:=296) (n:=1) (motive:=fun _=>Nat) (H (fun _=>0)) (fun _=>1)) (fun _=>1)=
      Fin.addCases (m:=298) (n:=1) (motive:=fun _=>Nat) (levelH (fun _ : Fin 222=>0)) (fun _ : Fin 1=>1) := by
    rw [←pairOne,←PhysicalDriverAssociativity.reassociate]
    rfl
  simp only [joinedHead,WindowSeed.source,R] at embedded
  simp only [levelData,WindowSeed.source,PhysicalDriverAssociativity.reassociate] at build
  have all:=build.seq embedded
  have fuelEq : depth*(literalLevelFuel C w population root depth+2*depth+6)+3+1+literalCoordinatesFuel C w population=
      literalProgramFuel C w population root depth := by unfold literalProgramFuel;omega
  rw [fuelEq] at all
  refine ⟨left',right',pi,fields',extra,?_,hl',hr',hs'⟩
  simpa only [literalProgram,levelData,WindowSeed.source,
    PhysicalDriverAssociativity.reassociate] using all

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
