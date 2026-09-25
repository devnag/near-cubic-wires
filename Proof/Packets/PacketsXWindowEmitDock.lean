import Proof.Packets.PacketsXWindowSeedEmit
import Proof.Packets.WindowProviderPorts

/-! The actual cold/reentry seed and nested window emitter in the fixed
256-tape provider. All metadata comes from its retained numeric masters. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch

def seedPorts : Fin 69→Fin 256 := Fin.addCases (m:=62) (n:=7) windowPorts ![180,181,182,183,184,185,152]
theorem seed_injective : Function.Injective seedPorts := by decide
theorem seed_range : ∀j,(seedPorts j).val<96 ∨ (seedPorts j).val=152 ∨
    (180≤(seedPorts j).val ∧ (seedPorts j).val≤185) := by decide
theorem seed_small : ∀j,(seedPorts j).val<34→j=50 ∨ j=51 := by decide

theorem seed_away_small (i : Fin 256) (hi : i.val<34) (h32 : i≠32) (h33 : i≠33) :
    ∀j,seedPorts j≠i := by
  intro j he
  have hj : (seedPorts j).val<34 := by rw [he];exact hi
  rcases seed_small j hj with rfl|rfl
  · exact h32 he.symm
  · exact h33 he.symm

theorem seed_away_middle (i : Fin 256) (hlo : 96≤ i.val) (hhi : i.val<150) :
    ∀j,seedPorts j≠i := by
  intro j he
  have hs:=seed_range j
  rw [he] at hs
  omega

theorem seed_away_cache : ∀j,seedPorts j≠186 := by decide

attribute [local irreducible] WindowSeed.complete
noncomputable def seedEmit := RecoveryFocus.machine seedPorts WindowSeed.complete
def emittedHeads (v M offset W target : Nat) (H : Fin 256→Nat) :=
  Function.update (Function.update H 78 (WindowSeed.emitted v M offset W target).length) 95 1
noncomputable def emittedOutput (R v u M offset W target : Nat) (A : Fin 256→List Bool) :=
  PhysicalFocusBoundary.dock seedPorts A (WindowSeed.after R v u M offset W target (2*W+1))

theorem seed_emitted_run (R v u M offset W target : Nat) (H : Fin 256→Nat) (A : Fin 256→List Bool)
    (hH : ∀i,H (seedPorts i)=0)
    (hu : 2*u+1≤ R) (hv : 2*v+1≤ R) (hM : M+1≤ R) (hMv : M≤2^v)
    (hraw : A 32=List.replicate R true) (hlog : A 33=List.replicate (R+3) false)
    (hmeta : ∀j : Fin 7,A (seedPorts (Fin.natAdd 62 j))=WindowSeed.metadata R v u M offset W target j)
    (hprivate : ∀j,(A (seedPorts (WindowSeed.privateSlot j))).length≤ R)
    (hfit : offset+2*W<2^u) (hd : 2*W+1<2^u) (ht : target<2^u)
    (hfields : 2*v+2*W+3≤ R)
    (hC : ∀k≤2*W,CloseoutRowsModeElementary.budget v k M+1≤ R) :
    Step seedEmit (WindowSeed.completeBudget R v u M W) H A
      (emittedHeads v M offset W target H) (emittedOutput R v u M offset W target A) := by
  have actual:=WindowSeed.complete_run R v u M offset W target 0 (fun i=>A (seedPorts i))
    (by omega) hu hv hM hMv hraw hlog hmeta hprivate hfit hd ht hfields hC
  apply PhysicalFocusBoundary.focus actual seedPorts seed_injective H _ A _
  · intro i
    simpa only [WindowSeed.H,ite_self] using (hH i).symm
  · intro i;rfl
  · intro i
    rw [WindowSeed.after_heads]
    by_cases h44 : i=44
    · subst i;simp [emittedHeads,seedPorts,windowPorts,Fin.addCases]
    by_cases h61 : i=61
    · subst i;simp [emittedHeads,seedPorts,windowPorts,Fin.addCases]
    have hp78 : seedPorts i≠78 := fun he=>h44 (seed_injective (show seedPorts i=seedPorts 44 from he))
    have hp95 : seedPorts i≠95 := fun he=>h61 (seed_injective (show seedPorts i=seedPorts 61 from he))
    simp only [if_neg h44,if_neg h61,emittedHeads,Function.update_of_ne hp78,Function.update_of_ne hp95]
    exact (hH i).symm
  · intro i
    simp only [emittedOutput,PhysicalFocusBoundary.dock,RecoveryFocus.pick_slot seedPorts seed_injective]
  · intro i away
    have h78 : i≠78 := by intro he;subst i;exact away 44 rfl
    have h95 : i≠95 := by intro he;subst i;exact away 61 rfl
    refine ⟨by simp only [emittedHeads,Function.update_of_ne h78,Function.update_of_ne h95],?_⟩
    cases hp : RecoveryFocus.pick seedPorts i with
    | none=>simp only [emittedOutput,PhysicalFocusBoundary.dock,hp]
    | some j=>exact False.elim (away j (RecoveryFocus.slot_of_pick seedPorts hp))

theorem seed_emitted_source (R v u M offset W target : Nat) (A : Fin 256→List Bool) :
    emittedOutput R v u M offset W target A 78=
      ZeroPadding.pad R ((WindowNativeOrder.positionalWindow v M offset (2*W) target).flatMap ExtIncidence.monomialWord) := by
  change emittedOutput R v u M offset W target A (seedPorts 44)=_
  simp only [emittedOutput,PhysicalFocusBoundary.dock,RecoveryFocus.pick_slot seedPorts seed_injective,
    WindowSeed.after_output,WindowSeed.emitted_word]

theorem seed_emitted_preserved (R v u M offset W target : Nat) (A : Fin 256→List Bool)
    (i : Fin 256) (hi : ∀j,seedPorts j≠i) : emittedOutput R v u M offset W target A i=A i := by
  cases hp : RecoveryFocus.pick seedPorts i with
  | none=>simp only [emittedOutput,PhysicalFocusBoundary.dock,hp]
  | some j=>exact False.elim (hi j (RecoveryFocus.slot_of_pick seedPorts hp))

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
