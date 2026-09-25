import Proof.Packets.PacketsXWalkPaletteSeedReady

/-! The decoded vertex supplies exactly the original Toeplitz parameters
used by the literal-vector theorem, with all static masters retained. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 18000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralSeedReady
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces NearCubicWires.SupplierWalkBridge
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore
open NearCubicWires.CanonicalFourfoldRowProgram CloseoutRowsModeCache
open PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
noncomputable section

theorem seeded_palette (C R population active root depth : Nat) (mask : Finset (Fin population))
    (old : ToeplitzSeed (canonicalGradedRank population active))
    (v : MargulisVertex (2^toeplitzWalkSideBits (canonicalGradedRank population active))) :
    seedPalette R (paddedPalette C R population root depth (parameters population active 0 (C+9) mask old))
      (WalkSeedResident.fields (canonicalGradedRank population active) v) =
      paddedPalette C R population root depth
        (parameters population active 0 (C+9) mask ((toeplitzWalkEncoding (canonicalGradedRank population active) v).1)) := by
  funext i;fin_cases i <;>
    simp [seedPalette,paddedPalette,coldPalette,parameters,WalkSeedResident.fields,
      CloseoutRowsModeHashMeaning.bits,Function.update]

theorem palette_width (C R M root depth : Nat) (p : Parameters) :
    paddedPalette C R M root depth p 2=UnaryTemplate.tape R := by
  simp [paddedPalette,coldPalette,ZeroPadding.pad,UnaryTemplate.tape]
  omega

theorem palette_seed_lengths (C R population active root depth : Nat)
    (mask : Finset (Fin population)) (old : ToeplitzSeed (canonicalGradedRank population active))
    (hr : canonicalGradedRank population active ≤ R) :
    ∀j : Fin 3,(paddedPalette C R population root depth
      (parameters population active 0 (C+9) mask old) ⟨6+j.val,by omega⟩).length=R := by
  have hu : canonicalGradedRank population active-1 ≤ R := by omega
  intro j;fin_cases j <;>
    simp [paddedPalette,coldPalette,parameters,CloseoutRowsModeHashMeaning.bits,
      ZeroPadding.pad_length,Nat.max_eq_left hr,Nat.max_eq_left hu]

theorem run (C R L S population active root depth position : Nat)
    (mask : Finset (Fin population)) (old : ToeplitzSeed (canonicalGradedRank population active))
    (hr : 0<canonicalGradedRank population active)
    (hR : 8*canonicalGradedRank population active+14 ≤ R)
    (v : MargulisVertex (2^toeplitzWalkSideBits (canonicalGradedRank population active)))
    (code : List Bool) (workHeads : Fin 299 → Nat) (work : Fin 299 → List Bool) :
    Step WalkPaletteSeedReady.machine (WalkPaletteSeedReady.budget (canonicalGradedRank population active) R)
      (WalkPaletteSeedReady.H position workHeads)
      (WalkPaletteSeedReady.A (canonicalGradedRank population active) R L S v code
        (paddedPalette C R population root depth (parameters population active 0 (C+9) mask old)) work)
      (WalkPaletteSeedReady.H position workHeads)
      (WalkPaletteSeedReady.A (canonicalGradedRank population active) R L S v code
        (paddedPalette C R population root depth
          (parameters population active 0 (C+9) mask ((toeplitzWalkEncoding (canonicalGradedRank population active) v).1))) work) := by
  have h:=WalkPaletteSeedReady.run (canonicalGradedRank population active) R L S position hr hR
    v code (paddedPalette C R population root depth (parameters population active 0 (C+9) mask old))
    workHeads work (palette_width C R population root depth _)
    (palette_seed_lengths C R population active root depth mask old (by omega))
  rw [seeded_palette] at h
  exact h

end
end Theorem25Completion.WalkLiteralSeedReady
