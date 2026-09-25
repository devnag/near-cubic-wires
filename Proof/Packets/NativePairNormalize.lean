import Proof.Packets.NativePairCapture
import Proof.Packets.ReusableNativeLayout

/-! An actual resident atom pair is copied, normalized, and retained as a
ready packet. The cache cursor advances while the reusable normalizer's
source and private work are physically cleared. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NativePairNormalize
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open CloseoutRowsRawPairSeek (Pair word)

def heads (pos : Nat) (i : Fin 40) : Nat := Fin.addCases (m:=36) (n:=4) (motive:=fun _=>Nat) ReusableNative.heads (![pos,0,0,0] : Fin 4→Nat) i
def extras (R : Nat) (source : List Bool) : Fin 4→List Bool :=
  ![source,List.replicate R false,List.replicate R false,List.replicate R false]
def data (C R : Nat) (source native : List Bool) (i : Fin 40) : List Bool :=
  Fin.addCases (m:=36) (n:=4) (motive:=fun _=>List Bool) (Function.update (ReusableNative.ready C R []) 30 (ZeroPadding.pad R native)) (extras R source) i
def result (C R : Nat) (source : List Bool) (raw : List (List Bool)) (i : Fin 40) : List Bool :=
  Fin.addCases (m:=36) (n:=4) (motive:=fun _=>List Bool) (ReusableNative.ready C R raw) (extras R source) i
def captureSlots : Fin 6→Fin 40 := ![37,36,30,38,39,32]
noncomputable def capture := RecoveryFocus.machine captureSlots NativePairCapture.machine
noncomputable def machine := Composition.machine capture (TapeEmbedding.machine 4 ReusableNative.normalize)
def budget (C R : Nat) (p : Pair) := NativePairCapture.budget p+1+
  ReusableNative.budget (NativeNormalized.budget C (p.1++p.2)) R

theorem capture_run (C R : Nat) (pre post : List Bool) (p : Pair) (hR : 1≤R)
    (hcost : CloseoutRowsRawPairCopy.budget p≤R+3) :
    Step capture (NativePairCapture.budget p)
      (heads pre.length) (data C R (pre++word p++post) [])
      (heads (pre.length+(word p).length))
      (data C R (pre++word p++post) (ExtIncidence.stream (p.1++p.2))) := by
  have h:=NativePairCapture.run R pre post p hR hcost
  apply PhysicalFocusBoundary.focus h captureSlots (by decide)
    (heads pre.length) (heads (pre.length+(word p).length))
    (data C R (pre++word p++post) [])
    (data C R (pre++word p++post) (ExtIncidence.stream (p.1++p.2)))
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i away
    fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 1 rfl) | exact False.elim (away 2 rfl)

theorem run (C R : Nat) (pre post : List Bool) (p : Pair) (hC : C≤R) (hR : 1≤R)
    (hcost : CloseoutRowsRawPairCopy.budget p≤R+3)
    (hp : ∀m∈p.1++p.2,∀code∈m,code<C)
    (hdata : ∀i,(NativeNormalized.A C (p.1++p.2) [] i).length≤R)
    (hfuel : NativeNormalized.budget C (p.1++p.2)+3≤R) :
    Step machine (budget C R p)
      (heads pre.length) (data C R (pre++word p++post) [])
      (heads (pre.length+(word p).length))
      (result C R (pre++word p++post)
        (NormalizerOrder.ordered (NativeNormalized.masks C (p.1++p.2)))) := by
  have first:=capture_run C R pre post p hR hcost
  have next:=(ReusableNative.normalize_run C R (p.1++p.2) hp hdata hfuel).embed
    (![pre.length+(word p).length,0,0,0] : Fin 4→Nat) (extras R (pre++word p++post))
  have next' : Step (TapeEmbedding.machine 4 ReusableNative.normalize)
      (ReusableNative.budget (NativeNormalized.budget C (p.1++p.2)) R)
      (heads (pre.length+(word p).length))
      (data C R (pre++word p++post) (ExtIncidence.stream (p.1++p.2)))
      (heads (pre.length+(word p).length))
      (result C R (pre++word p++post)
        (NormalizerOrder.ordered (NativeNormalized.masks C (p.1++p.2)))) := by
    apply next.congr_in rfl
    rw [ReusableNative.input_layout C R (p.1++p.2) hC hR]
    rfl
  exact first.seq next'

end PCJ9eff70d512234a4c_Fixed.Materializer.NativePairNormalize
