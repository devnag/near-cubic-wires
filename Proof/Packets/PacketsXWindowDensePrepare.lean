import Proof.Packets.PacketsXWindowDenseDock
import Proof.Packets.PhysicalEraseInto
import Proof.Packets.WindowWorkspaceLayout

/-! Dense-table input preparation from resident sources and arithmetic
masters. The population is physically copied to the counted-loop master. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsRawPairSeek (Pair cacheWord)

def denseReady (R : Nat) (A : Fin 256→List Bool) := Function.update (Workspace.cleared R A) 129 (A 184)
noncomputable def prepareDense := Composition.machine Workspace.machine
  (Composition.machine (PhysicalEraseInto.machine (129 : Fin 256) 32 33)
    (PhysicalCopyInto.machine (31 : Fin 256) 184 129))

theorem prepare_dense_run (R : Nat) (H : Fin 256→Nat) (A : Fin 256→List Bool)
    (hH : ∀j,H (Workspace.slots j)=0) (h31 : H 31=1) (h184 : H 184=0) (h129 : H 129=0)
    (hraw : A 32=List.replicate R true) (hlog : A 33=List.replicate (R+3) false)
    (hR : A 31=UnaryTemplate.tape R) (hcount : (A 184).length=R)
    (hfit : ∀i,Workspace.selected i→(A i).length≤R) (h129fit : (A 129).length≤R) :
    Step prepareDense (6*R+12) H A H (denseReady R A) := by
  have h32 : H 32=0 := hH 51
  have h33 : H 33=0 := hH 52
  have first:=Workspace.run R H A hH hraw hlog hfit
  have second:=PhysicalEraseInto.run R (129 : Fin 256) 32 33 (by decide) (by decide) (by decide)
    H (Workspace.cleared R A) h129 h32 h33 hraw hlog h129fit
  have third:=PhysicalCopyInto.run R (31 : Fin 256) 184 129 (by decide) (by decide) (by decide)
    H (Function.update (Workspace.cleared R A) 129 (List.replicate R false)) h31 h184 h129
    hR hcount (by simp)
  have final : Function.update
      (Function.update (Workspace.cleared R A) 129 (List.replicate R false)) 129
      (Function.update (Workspace.cleared R A) 129 (List.replicate R false) 184)=denseReady R A := by
    simp only [Function.update_of_ne (by decide : (184 : Fin 256)≠129),Function.update_idem]
    rfl
  have whole:=first.seq (second.seq (third.congr rfl final))
  have fuel : (2*R+4)+1+((2*R+4)+1+(2*R+2))=6*R+12 := by omega
  simpa only [prepareDense,fuel] using whole

theorem padded_dense_native (C R tag : Nat) (cs : List Pair) (initial : List PacketVector.Packet)
    (j : Fin 36) :
    DenseAtomMaterialize.paddedA C R tag cs initial 0 (j.castAdd 10)=ReusableNative.ready C R [] j := by
  fin_cases j <;>exact ZeroPadding.pad_zero _

theorem dense_ready_layout (C R tag : Nat) (cs : List Pair) (initial : List PacketVector.Packet)
    (left : PacketVector.Packet) (A : Fin 256→List Bool) (hR : 1≤R)
    (hengine : ∀i : Fin 34,A (i.castAdd 222)=ReusableArithmetic.state C R left [] i)
    (hcache : A 125=ZeroPadding.pad R (cacheWord cs))
    (hcodes : A 186=ZeroPadding.pad R (DenseAtomProgram.codes tag cs))
    (hcount : A 184=ZeroPadding.pad R (CompareMachine.word cs.length))
    (hbank : A 140=PacketVector.bank R initial) :
    ∀i,denseReady R A (densePorts i)=DenseAtomMaterialize.paddedA C R tag cs initial 0 i := by
  have hz : ZeroPadding.pad R (CompareMachine.word 0)=List.replicate R false := by
    change ZeroPadding.pad R (List.replicate 1 false)=_
    rw [Rewind.Workspace.pad_zeros,Nat.max_eq_left hR]
  intro i
  refine Fin.addCases (m:=36) (n:=10) (fun j=>?_) (fun j=>?_) i
  · rw [padded_dense_native,densePorts,Fin.addCases_left]
    have hn : nativePorts j≠129 := by fin_cases j <;>decide
    rw [denseReady,Function.update_of_ne hn]
    exact Workspace.native_ready C R left [] A hengine j
  · fin_cases j <;>
      simp [denseReady,densePorts,Workspace.cleared,Workspace.selected,
        DenseAtomMaterialize.paddedA,DenseAtomMaterialize.cacheCaps,DenseAtomMaterialize.A,
        NativeIndexedAtom.data,NativeAtomStore.data,NativePairNormalize.result,NativePairNormalize.extras,
        Fin.addCases,ZeroPadding.pad_zero,hcache,hcodes,hcount,hbank,hz]

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
