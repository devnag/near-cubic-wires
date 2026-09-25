import Proof.Packets.PhysicalCounterCopy

/-! Physical M+1 driver generation from a retained zero-head master. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalCounterCopy
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def zeroSuccessor {t : Nat} (width source target : Fin t) :=
  Composition.machine (PhysicalIndexReload.machine width source target)
    (RecoveryFocus.machine (fun _ : Fin 1=>target) VectorCounter.increment)

theorem zero_successor_run {t : Nat} (R n : Nat) (width source target : Fin t)
    (hws : width≠source) (hwt : width≠target) (hst : source≠target)
    (H : Fin t→Nat) (A : Fin t→List Bool)
    (hw : H width=1) (hs : H source=0) (ht : H target=1)
    (hword : A width=UnaryTemplate.tape R) (hsource : A source=ZeroPadding.pad R (CompareMachine.word n))
    (hr : n+1≤R) (htl : (A target).length=R) :
    Step (zeroSuccessor width source target) (2*R+2*n+9) H A H
      (Function.update A target (ZeroPadding.pad R (CompareMachine.word (n+1)))) := by
  have hsl : (A source).length=R := by
    rw [hsource,ZeroPadding.pad_length]
    simp only [CompareMachine.word,List.length_cons,List.length_replicate]
    omega
  have first:=PhysicalIndexReload.run R width source target hws hwt hst H A hw hs ht hword hsl htl
  have last:=PhysicalFocusBoundary.focus (VectorCounter.increment_padded n R)
    (fun _ : Fin 1=>target) (by intro i j _;exact Subsingleton.elim i j)
    H H (Function.update A target (A source))
    (Function.update A target (ZeroPadding.pad R (CompareMachine.word (n+1))))
    (by intro i;exact ht.symm) (by intro i;simp only [Function.update_self,hsource])
    (by intro i;exact ht.symm) (by intro i;simp only [Function.update_self])
    (by intro i away
        have hi:i≠target := by intro he;exact away 0 he.symm
        exact ⟨rfl,by simp only [Function.update_of_ne hi]⟩)
  have h:=first.seq last
  have hf : (2*R+6)+1+(2*n+2)=2*R+2*n+9 := by omega
  rw [hf] at h
  exact h

end
end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalCounterCopy
