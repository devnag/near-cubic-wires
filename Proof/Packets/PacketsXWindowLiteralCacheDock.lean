import Proof.Packets.PacketsXLiteralCacheTransaction
import Proof.Packets.WindowProviderPorts

/-! Physical reflected-code cache production from the retained actual tag,
population, and reserve masters in the fixed provider arena. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open Theorem25Completion.CycleLiteralPairCost

def literalPorts (i : Fin 68) : Fin 256 :=
  if i=2 then 186 else if i=59 then 32 else if i=60 then 33 else if i=62 then 31
  else if i=64 then 187 else if i=65 then 184 else ⟨i.val+188,by have h:=i.isLt;omega⟩
theorem literal_injective : Function.Injective literalPorts := by decide
noncomputable def buildLiteralCache := RecoveryFocus.machine literalPorts LiteralCacheTransaction.machine
noncomputable def cacheOutput (R tag count : Nat) (A : Fin 256→List Bool) :=
  PhysicalFocusBoundary.dock literalPorts A (LiteralCacheTransaction.output R tag count)

theorem cache_input (R tag count : Nat) (A : Fin 256→List Bool)
    (hraw : A 32=List.replicate R true) (hlog : A 33=List.replicate (R+3) false)
    (hR : A 31=UnaryTemplate.tape R)
    (ht : A 187=ZeroPadding.pad R (CompareMachine.word tag))
    (hc : A 184=ZeroPadding.pad R (CompareMachine.word count))
    (htR : tag+2≤R) (hcR : count+2≤R) :
    ∀i,LiteralCacheTransaction.input R tag count (fun j=>A (literalPorts j)) i=A (literalPorts i) := by
  intro i
  by_cases h59 : i=59
  · subst i;simpa [LiteralCacheTransaction.input,LiteralCacheTransaction.padMetadata,LiteralCacheReload.input,
      literalPorts,ZeroPadding.pad_zero] using hraw.symm
  by_cases h60 : i=60
  · subst i;simpa [LiteralCacheTransaction.input,LiteralCacheTransaction.padMetadata,LiteralCacheReload.input,
      literalPorts,ZeroPadding.pad_zero] using hlog.symm
  by_cases h62 : i=62
  · subst i;simpa [LiteralCacheTransaction.input,LiteralCacheTransaction.padMetadata,LiteralCacheReload.input,
      literalPorts,ZeroPadding.pad_zero] using hR.symm
  by_cases h64 : i=64
  · subst i
    simpa [LiteralCacheTransaction.input,LiteralCacheTransaction.padMetadata,LiteralCacheReload.input,
      literalPorts,VectorCounter.padded_template_word tag R htR] using ht.symm
  by_cases h65 : i=65
  · subst i
    simpa [LiteralCacheTransaction.input,LiteralCacheTransaction.padMetadata,LiteralCacheReload.input,
      literalPorts,VectorCounter.padded_template_word count R hcR] using hc.symm
  simp only [LiteralCacheTransaction.input,LiteralCacheTransaction.padMetadata,LiteralCacheReload.input,
    if_neg h59,if_neg h60,if_neg h62,if_neg h64,if_neg h65,ZeroPadding.pad_zero]

theorem build_literal_cache_run (C w tag count : Nat) (ht : tag≤C) (hc : count≤C)
    (hcode : ∀i,i<count→Nat.pair tag i≤C) (H : Fin 256→Nat) (A : Fin 256→List Bool)
    (hH : ∀i,LiteralCacheTransaction.heads i=H (literalPorts i))
    (hraw : A 32=List.replicate (commonReserve C w) true)
    (hlog : A 33=List.replicate (commonReserve C w+3) false)
    (hR : A 31=UnaryTemplate.tape (commonReserve C w))
    (htag : A 187=ZeroPadding.pad (commonReserve C w) (CompareMachine.word tag))
    (hcount : A 184=ZeroPadding.pad (commonReserve C w) (CompareMachine.word count))
    (hfit : ∀i,i≠59→i≠60→i≠62→i≠64→i≠65→(A (literalPorts i)).length≤commonReserve C w) :
    Step buildLiteralCache (LiteralCacheTransaction.budget (commonReserve C w) tag count)
      H A H (cacheOutput (commonReserve C w) tag count A) := by
  have hcap:=LiteralCacheReuse.reserve_width C w
  apply PhysicalFocusBoundary.focus
    (LiteralCacheTransaction.run C w tag count (fun i=>A (literalPorts i)) ht hc hcode hfit)
    literalPorts literal_injective H H A _ hH
    (cache_input _ tag count A hraw hlog hR htag hcount (by omega) (by omega)) hH
  · intro i
    simp only [cacheOutput,PhysicalFocusBoundary.dock,RecoveryFocus.pick_slot literalPorts literal_injective]
  · intro i away
    refine ⟨rfl,?_⟩
    cases hp : RecoveryFocus.pick literalPorts i with
    | none=>simp only [cacheOutput,PhysicalFocusBoundary.dock,hp]
    | some j=>exact False.elim (away j (RecoveryFocus.slot_of_pick literalPorts hp))

theorem produced_cache (R tag count : Nat) (A : Fin 256→List Bool) :
    cacheOutput R tag count A 186=ZeroPadding.pad R (ReflectedLiteralCache.stream tag count) := by
  change cacheOutput R tag count A (literalPorts 2)=_
  simp only [cacheOutput,PhysicalFocusBoundary.dock,RecoveryFocus.pick_slot literalPorts literal_injective]
  exact LiteralCacheTransaction.output_cache R tag count

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
