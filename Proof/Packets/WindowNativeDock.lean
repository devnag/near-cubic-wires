import Proof.Packets.WindowProviderPorts
import Proof.Packets.ReusableNativeLayout

/-! The concrete native-normalizer dock in the256-tape provider. It consumes
its physically produced source on122, returns the normalized operand on26/27,
and restores all native private backing without changing other provider data. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

noncomputable def normalize := RecoveryFocus.machine nativePorts ReusableNative.normalize
def withSource (R : Nat) (source : List Bool) (A : Fin 256→List Bool) :=
  Function.update A 122 (ZeroPadding.pad R source)
def completed (R : Nat) (raw : List (List Bool)) (A : Fin 256→List Bool) :=
  Function.update (Function.update A 26 (ZeroPadding.pad R raw.flatten)) 27
    (ZeroPadding.pad R (CompareMachine.word raw.length))

theorem ready_outside (C R : Nat) (raw : List (List Bool)) (i : Fin 36) (h26 : i≠26) (h27 : i≠27) :
    ReusableNative.ready C R raw i=ReusableNative.ready C R [] i := by
  revert h26 h27
  refine Fin.addCases (m:=32) (n:=4) (fun j=>?_) (fun j=>?_) i
  · intro h26 h27
    unfold ReusableNative.ready ReusableNative.bank
    rw [Fin.addCases_left,Fin.addCases_left]
    have hj26 : j≠26 := by intro he;subst j;exact h26 rfl
    have hj27 : j≠27 := by intro he;subst j;exact h27 rfl
    simp only [ReusableNative.readyData,if_neg hj26,if_neg hj27]
  · intro _ _
    unfold ReusableNative.ready ReusableNative.bank
    rw [Fin.addCases_right,Fin.addCases_right]

theorem native_source (C R : Nat) (P : List (List Nat)) (A : Fin 256→List Bool)
    (hC : C≤R) (hR : 1≤R) (ha : ∀ i,A (nativePorts i)=ReusableNative.ready C R [] i) :
    ∀ i,ReusableNative.input C R P i=withSource R (ExtIncidence.stream P) A (nativePorts i) := by
  intro i
  rw [ReusableNative.input_layout C R P hC hR]
  by_cases hi : i=30
  · subst i;rfl
  have hn : nativePorts i≠122 := by intro he;apply hi;apply native_injective;exact he
  simp only [withSource,Function.update_of_ne hi,Function.update_of_ne hn]
  exact (ha i).symm

theorem native_result (C R : Nat) (raw : List (List Bool)) (A : Fin 256→List Bool)
    (ha : ∀ i,A (nativePorts i)=ReusableNative.ready C R [] i) :
    ∀ i,ReusableNative.ready C R raw i=completed R raw A (nativePorts i) := by
  intro i
  by_cases h26 : i=26
  · subst i;rfl
  by_cases h27 : i=27
  · subst i;rfl
  have hn26 : nativePorts i≠26 := by intro he;apply h26;apply native_injective;exact he
  have hn27 : nativePorts i≠27 := by intro he;apply h27;apply native_injective;exact he
  simp only [completed,Function.update_of_ne hn26,Function.update_of_ne hn27]
  exact (ready_outside C R raw i h26 h27).trans (ha i).symm

theorem normalize_run (C R : Nat) (P : List (List Nat)) (H : Fin 256→Nat) (A : Fin 256→List Bool)
    (hC : C≤R) (hR : 1≤R)
    (hh : ∀ i,ReusableNative.heads i=H (nativePorts i))
    (ha : ∀ i,A (nativePorts i)=ReusableNative.ready C R [] i)
    (hp : ∀m∈P,∀code∈m,code<C)
    (hdata : ∀i,(NativeNormalized.A C P [] i).length≤R)
    (hfuel : NativeNormalized.budget C P+3≤R) :
    Step normalize (ReusableNative.budget (NativeNormalized.budget C P) R) H
      (withSource R (ExtIncidence.stream P) A) H
      (completed R (NormalizerOrder.ordered (NativeNormalized.masks C P)) A) := by
  apply PhysicalFocusBoundary.focus (ReusableNative.normalize_run C R P hp hdata hfuel)
    nativePorts native_injective H H _ _ hh (native_source C R P A hC hR ha) hh
    (native_result C R _ A ha)
  intro i away
  have h122 : i≠122 := by intro he;subst i;exact away 30 rfl
  have h26 : i≠26 := by intro he;subst i;exact away 26 rfl
  have h27 : i≠27 := by intro he;subst i;exact away 27 rfl
  exact ⟨rfl,by simp only [withSource,completed,Function.update_of_ne h122,
    Function.update_of_ne h26,Function.update_of_ne h27]⟩

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
