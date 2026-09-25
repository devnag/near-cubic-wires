import Proof.Packets.PacketsXWindowLiteralCacheDock

/-! Retained provider fields and exact private-space reentry invariant for
the physically generated reflected literal cache. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open Theorem25Completion.CycleLiteralPairCost

theorem cache_at (R tag count : Nat) (A : Fin 256→List Bool) (i : Fin 68) :
    cacheOutput R tag count A (literalPorts i)=LiteralCacheTransaction.output R tag count i := by
  simp only [cacheOutput,PhysicalFocusBoundary.dock,RecoveryFocus.pick_slot literalPorts literal_injective]

theorem cache_private_lengths (C w tag count : Nat) (ht : tag≤C) (hc : count≤C)
    (hcode : ∀i,i<count→Nat.pair tag i≤C) (A : Fin 256→List Bool) :
    ∀i,i≠59→i≠60→i≠62→i≠64→i≠65→
      (cacheOutput (commonReserve C w) tag count A (literalPorts i)).length=commonReserve C w := by
  intro i h59 h60 h62 h64 h65
  rw [cache_at]
  simp only [LiteralCacheTransaction.output,LiteralCacheTransaction.padMetadata,
    if_neg h64,if_neg h65,ZeroPadding.pad_zero]
  exact LiteralCacheReuse.output_private_lengths C w tag count ht hc hcode i h59 h60 h62 h64 h65

theorem cache_retained (R tag count : Nat) (A : Fin 256→List Bool)
    (hraw : A 32=List.replicate R true) (hlog : A 33=List.replicate (R+3) false)
    (hR : A 31=UnaryTemplate.tape R)
    (ht : A 187=ZeroPadding.pad R (CompareMachine.word tag))
    (hc : A 184=ZeroPadding.pad R (CompareMachine.word count))
    (htR : tag+2≤R) (hcR : count+2≤R)
    (i : Fin 256) (hi : i.val<188) (h186 : i≠186) :
    cacheOutput R tag count A i=A i := by
  cases hp : RecoveryFocus.pick literalPorts i with
  | none=>simp only [cacheOutput,PhysicalFocusBoundary.dock,hp]
  | some j=>
    have he:=RecoveryFocus.slot_of_pick literalPorts hp
    rw [←he,cache_at]
    by_cases h2 : j=2
    · subst j;exact False.elim (h186 he.symm)
    by_cases h59 : j=59
    · subst j
      simpa [literalPorts,LiteralCacheTransaction.output,LiteralCacheTransaction.padMetadata,
        LiteralCacheReuse.output,LiteralCacheReload.ready,LiteralCacheReload.bank4,
        LiteralCacheReload.bank3,LiteralCacheReload.cleared,LiteralCacheReload.input,
        ZeroPadding.pad_zero] using hraw.symm
    by_cases h60 : j=60
    · subst j
      simpa [literalPorts,LiteralCacheTransaction.output,LiteralCacheTransaction.padMetadata,
        LiteralCacheReuse.output,LiteralCacheReload.ready,LiteralCacheReload.bank4,
        LiteralCacheReload.bank3,LiteralCacheReload.cleared,LiteralCacheReload.input,
        ZeroPadding.pad_zero] using hlog.symm
    by_cases h62 : j=62
    · subst j
      simpa [literalPorts,LiteralCacheTransaction.output,LiteralCacheTransaction.padMetadata,
        LiteralCacheReuse.output,LiteralCacheReload.ready,LiteralCacheReload.bank4,
        LiteralCacheReload.bank3,LiteralCacheReload.cleared,LiteralCacheReload.input,
        ZeroPadding.pad_zero] using hR.symm
    by_cases h64 : j=64
    · subst j
      simpa [literalPorts,LiteralCacheTransaction.output,LiteralCacheTransaction.padMetadata,
        LiteralCacheReuse.output,LiteralCacheReload.ready,LiteralCacheReload.bank4,
        LiteralCacheReload.bank3,LiteralCacheReload.cleared,LiteralCacheReload.input,
        VectorCounter.padded_template_word tag R htR] using ht.symm
    by_cases h65 : j=65
    · subst j
      simpa [literalPorts,LiteralCacheTransaction.output,LiteralCacheTransaction.padMetadata,
        LiteralCacheReuse.output,LiteralCacheReload.ready,LiteralCacheReload.bank4,
        LiteralCacheReload.bank3,LiteralCacheReload.cleared,LiteralCacheReload.input,
        VectorCounter.padded_template_word count R hcR] using hc.symm
    have hv:=congrArg (fun k : Fin 256=>k.val) he
    simp only [literalPorts,if_neg h2,if_neg h59,if_neg h60,if_neg h62,if_neg h64,if_neg h65] at hv
    omega

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
