import Proof.Packets.PacketsXModeCacheReady
import Proof.Packets.WindowProviderPorts

/-! The actual original-seed delta cache in the fixed provider arena.
Both source halves are emitted into125; the actually counted child cell is
retained at150. All remaining provider state lies outside the fixed ports. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsModeCache
attribute [local irreducible] ModeCacheReady.machine

def modePorts : Fin 29→Fin 256 :=
  ![153,162,154,155,163,156,164,165,166,157,167,158,159,168,169,
    170,171,172,173,174,125,160,175,150,161,30,32,33,31]
theorem mode_injective : Function.Injective modePorts := by decide
noncomputable def buildModeCache := RecoveryFocus.machine modePorts ModeCacheReady.machine
noncomputable def modeOutput (p : Parameters) (M R : Nat) (A : Fin 256→List Bool) :=
  PhysicalFocusBoundary.dock modePorts A
    (ModeCacheReady.A p M R (ModeCacheReady.word p M) (reuseFinal 2 p M R))

theorem build_mode_cache_run (p : Parameters) (M R : Nat) (out : List Bool) (priv : Fin 15→List Bool)
    (hl : p.level≤p.rank) (hC : p.rank+2≤p.C)
    (hb : CloseoutRowsModeHashLoop.budget p.rank p.rank+2≤p.C)
    (hi : M≤2^p.rank) (hlog : sourceBudget p M≤R+3)
    (hD : reuseCapacity p M≤R) (hpriv : ∀i,(priv i).length≤R)
    (hout : out.length≤R) (hword : (ModeCacheReady.word p M).length≤R)
    (H : Fin 256→Nat) (A : Fin 256→List Bool)
    (hH : ∀i,ModeCacheReady.H 0 i=H (modePorts i))
    (hA : ∀i,ModeCacheReady.A p M R out priv i=A (modePorts i)) :
    Step buildModeCache (ModeCacheReady.budget p M R) H A H (modeOutput p M R A) := by
  apply PhysicalFocusBoundary.focus (ModeCacheReady.run p M R out priv hl hC hb hi hlog hD hpriv hout hword)
    modePorts mode_injective H H A _ hH hA hH
  · intro i
    simp only [modeOutput,PhysicalFocusBoundary.dock,RecoveryFocus.pick_slot modePorts mode_injective]
  · intro i away
    refine ⟨rfl,?_⟩
    cases hp : RecoveryFocus.pick modePorts i with
    | none=>simp only [modeOutput,PhysicalFocusBoundary.dock,hp]
    | some j=>exact False.elim (away j (RecoveryFocus.slot_of_pick modePorts hp))

theorem mode_source (p : Parameters) (M R : Nat) (A : Fin 256→List Bool) :
    modeOutput p M R A 125=ZeroPadding.pad R
      (CloseoutRowsRawPairSeek.cacheWord (pairs 1 p M++pairs 2 p M)) := by
  change modeOutput p M R A (modePorts 20)=_
  simp only [modeOutput,PhysicalFocusBoundary.dock,RecoveryFocus.pick_slot modePorts mode_injective]
  rfl

theorem mode_child_count (p : Parameters) (M R : Nat) (A : Fin 256→List Bool) :
    modeOutput p M R A 150=ZeroPadding.pad R
      (CompareMachine.word (track 2 p (initialState []) M).children) := by
  change modeOutput p M R A (modePorts 23)=_
  simp only [modeOutput,PhysicalFocusBoundary.dock,RecoveryFocus.pick_slot modePorts mode_injective]
  simp [ModeCacheReady.A,ModeCacheReady.caps,reuseData,reuseFinal,loopData,
    privateSlots,atState,Fin.addCases,ZeroPadding.pad_zero]
  rfl

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
