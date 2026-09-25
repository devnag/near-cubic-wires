import Proof.Rows.PowerProduct

/-! Rewind only the isolated scalar result, then clear the two short temporary
operands after replacing the factor. All coefficient/native cursors survive. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_PowerCleanup
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open SignedSortKey PCJ45bee56da9f34d5a_PowerBank
noncomputable section

def rewind := RecoveryFocus.machine (![93,62,63] : Fin 3→Fin 94) CompetitorRecordRewind.machine
def eraseSlots : Fin 4→Fin 94 := ![0,93,62,63]
def erase := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 2)

theorem rewind_run (a B p w F U q pos : Nat) (source out coefficient temp : List Bool)
    (hpos : temp.length ≤ U) :
    Step rewind (2*U+2) (heads pos out.length temp.length)
      (bank a B p w F U q source out coefficient temp)
      (heads pos out.length 0) (bank a B p w F U q source out coefficient temp) := by
  have h := CloseoutRowsTupleSeek.rewind_at (93 : Fin 94) 62 63 (by decide) (by decide) (by decide)
    U (heads pos out.length temp.length) (bank a B p w F U q source out coefficient temp)
    hpos rfl rfl (ZeroPadding.pad_zero _) (ZeroPadding.pad_zero _)
  apply h.congr
  · funext i
    by_cases hi:i=93
    · subst i;rfl
    · rw [Function.update_of_ne hi]
      exact PCJ45bee56da9f34d5a_PowerProduct.heads_away pos out.length temp.length 0 i hi
  · rfl

theorem erase_run (a B p w F U q pos : Nat) (source out coefficient temp : List Bool)
    (hc : coefficient.length ≤ U) (ht : temp.length ≤ U) :
    Step erase (2*U+4) (heads pos out.length 0) (bank a B p w F U q source out coefficient temp)
      (heads pos out.length 0) (bank a B p w F U q source out (List.replicate U false) []) := by
  have hd : ∀i : Fin 2,((![coefficient,ZeroPadding.pad U temp] : Fin 2→List Bool) i).length ≤ U := by
    intro i;fin_cases i
    · exact hc
    · change (ZeroPadding.pad U temp).length ≤ U
      rw [ZeroPadding.pad_length]
      exact max_le le_rfl ht
  have h := (Step.of_ready (RecoveryScratchErase.erase_ready U (U+1)
    (![coefficient,ZeroPadding.pad U temp] : Fin 2→List Bool) hd)).dock eraseSlots (by decide)
      (heads pos out.length 0) (bank a B p w F U q source out coefficient temp)
      (by intro i;fin_cases i <;>rfl)
      (by intro i;fin_cases i <;>first |rfl |exact ZeroPadding.pad_zero _)
  apply h.congr
  · exact dockH_existing _ _ _ (by intro i;fin_cases i <;>rfl)
  · apply HierarchyAllocation.install_eq eraseSlots (by decide)
    · intro i;fin_cases i <;>simp only [Nat.max_self] <;>first |rfl |exact ZeroPadding.pad_zero _
    · intro i hi
      exact (bank_away a B p w F U q source out coefficient (List.replicate U false) temp [] i
        (fun he=>hi 0 he.symm) (fun he=>hi 1 he.symm)).symm
end
end PCJ45bee56da9f34d5a_PowerCleanup
