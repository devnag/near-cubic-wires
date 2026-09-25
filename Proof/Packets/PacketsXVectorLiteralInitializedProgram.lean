import Proof.Packets.PacketsXVectorLiteralBankEntry
import Proof.Packets.PacketsXVectorLiteralProgram

/-! Initialization, the vector loop, and all coordinates in one fixed program.
All three banks are empty at entry. -/
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

def literalInitializedProgram := Composition.machine initializeLiteral literalProgram
def literalInitializedFuel (C w M root depth : Nat) :=
  initializeLiteralFuel C (commonReserve C w) M+1+literalProgramFuel C w M root depth
attribute [local irreducible] initializeLiteral literalProgram

theorem literal_initialized_program_run (C w d population active depth root : Nat)
    (mask : Finset (Fin population)) (seed : ToeplitzSeed (canonicalGradedRank population active))
    (wins : Fin depth → Nat) (fields : Fin 222 → List Bool) (extra : Fin 32 → List Bool)
    (hd : depth≤canonicalGradedRank population active)
    (hrank : canonicalGradedRank population active≤9*population)
    (hC : (258*population+2)^2≤C) (hcodesC : (depth+2*population+2)^2≤C)
    (hpop : 1≤population) (hi : population≤2^(canonicalGradedRank population active))
    (hw : 3≤w) (hdegree : structuralListCoordinateRawDegree depth wins 0≤d)
    (hfit : (population*(2*depth+1)+2)^d≤2^w)
    (hsourcefit : (population+1)^d≤2^w) (hatomfit : population+1≤2^w)
    (hwin : ∀level,wins level=GradedWindow.window root level.val)
    (hW : ∀level,wins level≤64*(C+2)) (hroot : root+67≤commonReserve C w)
    (hcold : LiteralColdState C (commonReserve C w) population root depth
      (parameters population active 0 (C+9) mask seed) fields extra []) :
    ∃left right pi outFields outExtra,
      Step literalInitializedProgram (literalInitializedFuel C w population root depth)
        (Fin.addCases (m:=298) (n:=1) (motive:=fun _=>Nat) (levelH (fun _ : Fin 222=>0)) (fun _ : Fin 1=>1))
        (coldData C (commonReserve C w) fields extra)
        (Fin.addCases (m:=298) (n:=1) (motive:=fun _=>Nat) (levelH (fun _ : Fin 222=>0)) (fun _ : Fin 1=>1))
        (Fin.addCases (m:=298) (n:=1) (motive:=fun _=>List Bool) (levelData C (commonReserve C w) (population+1) (population+1) pi 0 left right
          (vectorBank C (commonReserve C w) (NormalizedVector.table (canonicalGradedLabel population active) seed wins 0 depth))
          (PacketVector.bank (commonReserve C w) (List.ofFn (fun candidate : Fin (population+1)=>
            (Normalized.structuralMaskedListCoordinate mask (canonicalGradedLabel population active) seed wins 0 candidate).map (maskNat C))))
          outFields outExtra) (fun _ : Fin 1=>WindowSeed.source (commonReserve C w) depth)) ∧
      VectorAccumulator.Fits (commonReserve C w) left ∧ VectorAccumulator.Fits (commonReserve C w) right ∧
      LiteralLevelState C (commonReserve C w) population root (parameters population active 0 (C+9) mask seed)
        (denseLevels C population depth (parameters population active 0 (C+9) mask seed) (List.replicate C []) depth) outFields outExtra := by
  let R:=commonReserve C w
  let p:=parameters population active 0 (C+9) mask seed
  let fs:=Function.update fields 106 (PacketVector.bank R (List.replicate C []))
  have reserve : C+2≤R := LiteralCacheReuse.reserve_width C w
  have small : depth+2*population+2≤C := by
    nlinarith only [hcodesC,Nat.zero_le ((depth+2*population+2-1)^2)]
  have cap : Completion.SourceDigitWidth.capacity (2*population)≤R :=
    Theorem25Completion.CycleDeltaMetadataCost.phase_width_reserve C w population (by omega)
  have hs : LiteralColdState C R population root depth p fs extra :=
    cold_state_bank C R population root depth p fields extra [] _ hcold
  let input:=levelData C R (population+1) 0 0 depth [List.replicate C false] []
    (PacketVector.bank R ([List.replicate C false]::List.replicate population []))
    (PacketVector.bank R (List.replicate (population+1) [])) (bootFields R population fs) (bootExtra R population extra)
  have entry:=initialized_level_ready C R population root depth (canonicalGradedRank population active) p
    (canonicalGradedLabel population active) seed wins fs extra hs (by omega) (by omega)
  have init:=initialize_literal_run C R population root depth p fields extra hcold reserve (by omega) cap
  obtain ⟨left,right,pi,fields',extra',run,hl,hr,hs'⟩:=literal_program_run C w d population active depth root
    mask seed wins input hd hrank hC hcodesC hpop hi hw hdegree hfit hsourcefit hatomfit hwin hW hroot entry
  have all:=init.seq run
  exact ⟨left,right,pi,fields',extra',all,hl,hr,hs'⟩

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
