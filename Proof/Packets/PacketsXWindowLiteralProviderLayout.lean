import Proof.Packets.PacketsXWindowLiteralProvider
import Proof.Packets.PacketsXWindowLiteralState

/-! Full reusable boundary of the literal provider: exact arithmetic result,
retained masters/cache, and finite lengths of every private word on reentry. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.CanonicalFourfoldRowProgram
open NormalizedFiniteTransport

theorem literal_output_engine (C R v u offset W target : Nat) (codes : List Nat)
    (left : List (List Bool)) (A : Fin 256→ List Bool)
    (ha : ∀i : Fin 34,A (i.castAdd 222)=ReusableArithmetic.state C R left [] i) :
    ∀i : Fin 34,literalProviderOutput C R v u offset W target codes A (i.castAdd 222)=
      ReusableArithmetic.state C R left
        ((Normalized.structuralGF2ConsecutiveWindowIndicator codes offset (2*W) target).map (maskNat C)) i := by
  apply completed_core
  intro i
  rw [emitted_core R v u codes.length offset W target (Workspace.cleared R A)
    ((Workspace.core_retained R A 32).trans (ha 32))
    ((Workspace.core_retained R A 33).trans (ha 33)) _ (by simp only [Fin.val_castAdd];exact i.isLt)]
  exact (Workspace.core_retained R A i).trans (ha i)

theorem literal_output_middle (C R v u offset W target : Nat) (codes : List Nat)
    (A : Fin 256→ List Bool) (i : Fin 256) (hlo : 96≤ i.val) (hhi : i.val<150) :
    literalProviderOutput C R v u offset W target codes A i=Workspace.cleared R A i := by
  have h26:i≠26:=by intro he;subst i;norm_num at hlo
  have h27:i≠27:=by intro he;subst i;norm_num at hlo
  simp only [literalProviderOutput,completed,Function.update_of_ne h26,Function.update_of_ne h27]
  exact seed_emitted_preserved _ _ _ _ _ _ _ _ i (seed_away_middle i hlo hhi)

theorem literal_output_work (C R v u offset W target : Nat) (codes : List Nat)
    (A : Fin 256→ List Bool) :
    ∀i,Workspace.selected i→ literalProviderOutput C R v u offset W target codes A i=List.replicate R false := by
  intro i hi
  have range : 96≤ i.val ∧ i.val<150:=by unfold Workspace.selected at hi;omega
  rw [literal_output_middle _ _ _ _ _ _ _ _ _ i range.1 range.2,Workspace.cleared,if_pos hi]

theorem emitted_masters (R v u M offset W target : Nat) (A : Fin 256→ List Bool) (j : Fin 7) :
    emittedOutput R v u M offset W target A (seedPorts (j.natAdd 62))=
      WindowSeed.metadata R v u M offset W target j := by
  simp only [emittedOutput,PhysicalFocusBoundary.dock,RecoveryFocus.pick_slot seedPorts seed_injective,
    WindowSeed.after,Fin.addCases_right]

theorem emitted_large (R v u M offset W target : Nat) (A : Fin 256→ List Bool)
    (hmeta : ∀j : Fin 7,A (seedPorts (j.natAdd 62))=WindowSeed.metadata R v u M offset W target j)
    (i : Fin 256) (hi : 150≤ i.val) : emittedOutput R v u M offset W target A i=A i := by
  cases hp:RecoveryFocus.pick seedPorts i with
  | none=>simp only [emittedOutput,PhysicalFocusBoundary.dock,hp]
  | some j=>
    have he:=RecoveryFocus.slot_of_pick seedPorts hp
    rw [←he] at hi ⊢
    revert hi
    refine Fin.addCases (m:=62) (n:=7) (fun k=>?_) (fun k=>?_) j
    · intro hi
      have hsmall : ∀k : Fin 62,(seedPorts (k.castAdd 7)).val<96:=by decide
      have h:=hsmall k
      omega
    · intro _
      exact (emitted_masters R v u M offset W target A k).trans (hmeta k).symm

theorem literal_output_large (C R v u offset W target : Nat) (codes : List Nat)
    (A : Fin 256→ List Bool)
    (hmeta : ∀j : Fin 7,A (seedPorts (j.natAdd 62))=WindowSeed.metadata R v u codes.length offset W target j)
    (i : Fin 256) (hi : 150≤ i.val) : literalProviderOutput C R v u offset W target codes A i=A i := by
  have h26:i≠26:=by intro he;subst i;norm_num at hi
  have h27:i≠27:=by intro he;subst i;norm_num at hi
  have hn : ¬Workspace.selected i:=by unfold Workspace.selected;omega
  simp only [literalProviderOutput,completed,Function.update_of_ne h26,Function.update_of_ne h27]
  rw [emitted_large R v u codes.length offset W target (Workspace.cleared R A)
    (fun j=>by rw [Workspace.cleared,if_neg (seed_workspace_away _)];exact hmeta j) i hi,
    Workspace.cleared,if_neg hn]

theorem literal_output_private (C R v u offset W target : Nat) (codes : List Nat)
    (A : Fin 256→ List Bool) (hu : 2*u+1≤ R) (hv : 2*v+1≤ R) (hM : codes.length≤ R)
    (hW : 2*W+2≤ R) (hout : (WindowSeed.emitted v codes.length offset W target).length≤ R) :
    ∀j,(literalProviderOutput C R v u offset W target codes A
      (seedPorts (WindowSeed.privateSlot j))).length=R := by
  intro j
  have hneq : ∀j,seedPorts (WindowSeed.privateSlot j)≠26 ∧ seedPorts (WindowSeed.privateSlot j)≠27 := by decide
  simp only [literalProviderOutput,completed,Function.update_of_ne (hneq j).1,
    Function.update_of_ne (hneq j).2,emittedOutput,PhysicalFocusBoundary.dock,
    RecoveryFocus.pick_slot seedPorts seed_injective]
  exact WindowSeed.after_private_lengths R v u codes.length offset W target hu hv hM hW hout j

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
