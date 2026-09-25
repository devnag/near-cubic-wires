import Proof.Rows.PowerBank

/-! The real product uses an isolated bounded destination. It cannot scan the
coefficient output at64; that tape is outside the product focus. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_PowerProduct
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open SignedSortKey PCJ45bee56da9f34d5a_PowerBank
noncomputable section

def machine := RecoveryFocus.machine productSlots PCJ45bee56da9f34d5a_ResidueScaleCell.machine

theorem heads_away (pos len t t' : Nat) (i : Fin 94) (hi : i≠93) :
    heads pos len t i=heads pos len t' i := by
  fin_cases i <;>first |rfl |contradiction

theorem run (a B p w F U q pos : Nat) (source out : List Bool)
    (hp : 0 < p) (hpw : 2*p ≤ 2^w) (ha : a < 2^w) (hB : B < 2^w)
    (hU : 1024*(w+1)^2+2 ≤ U) :
    Step machine (1024*(w+1)^2+6*U+2*w+19) (heads pos out.length 0)
      (bank a B p w F U q source out (ZeroPadding.pad U (frame (binary w B))) [])
      (heads pos out.length (2*w+1))
      (bank a B p w F U q source out (ZeroPadding.pad U (frame (binary w B))) (frame (binary w ((a*B)%p)))) := by
  have h := ((PCJ45bee56da9f34d5a_ResidueScaleBounds.run a B p w U [] hp hpw ha hB hU).pad (productCaps U)).dock
    productSlots product_injective (heads pos out.length 0)
      (bank a B p w F U q source out (ZeroPadding.pad U (frame (binary w B))) [])
      (product_head pos out []) (product_bank a B B p w F U q source out [])
  simp only [List.nil_append] at h
  apply h.congr
  · funext i
    by_cases hi:∃j,productSlots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [dockH_slot _ product_injective]
      have he := product_head pos out (frame (binary w ((a*B)%p))) j
      simpa only [frame_length,binary_length] using he.symm
    · rw [dockH_other _ _ _ _ (by simpa using hi)]
      exact heads_away pos out.length 0 (2*w+1) i (fun he=>hi ⟨64,he.symm⟩)
  · apply HierarchyAllocation.install_eq productSlots product_injective
    · intro j;exact product_bank a B B p w F U q source out _ j
    · intro i hi
      exact (bank_away a B p w F U q source out _ _ [] _ i (fun he=>hi 0 he.symm) (fun he=>hi 64 he.symm)).symm
end
end PCJ45bee56da9f34d5a_PowerProduct
