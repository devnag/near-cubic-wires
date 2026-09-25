import Proof.Packets.PhysicalIndexReload

/-! Retained unary masters are copied with both endpoint cursors at one.
The successor variant physically supplies the M+1 child/parent driver. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalCounterCopy
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def machine {t : Nat} (width source target : Fin t) :=
  Composition.machine (PhysicalIndexReload.move source .left)
    (Composition.machine (PhysicalIndexReload.machine width source target) (PhysicalIndexReload.move source .right))
def successor {t : Nat} (width source target : Fin t) :=
  Composition.machine (machine width source target)
    (RecoveryFocus.machine (fun _ : Fin 1=>target) VectorCounter.increment)

theorem run {t : Nat} (R : Nat) (width source target : Fin t)
    (hws : width≠source) (hwt : width≠target) (hst : source≠target)
    (H : Fin t→Nat) (A : Fin t→List Bool)
    (hw : H width=1) (hs : H source=1) (ht : H target=1)
    (hword : A width=UnaryTemplate.tape R) (hsl : (A source).length=R) (htl : (A target).length=R) :
    Step (machine width source target) (2*R+10) H A H (Function.update A target (A source)) := by
  have first:=PhysicalIndexReload.move_run source .left H A
  simp only [hs,HeadMove.apply] at first
  have middle:=PhysicalIndexReload.run R width source target hws hwt hst
    (Function.update H source 0) A
    (by simpa [Function.update,hws] using hw) (by simp)
    (by simpa [Function.update,Ne.symm hst] using ht) hword hsl htl
  have last:=PhysicalIndexReload.move_run source .right (Function.update H source 0)
    (Function.update A target (A source))
  simp only [Function.update_self,HeadMove.apply] at last
  have he : Function.update (Function.update H source 0) source 1=H := by
    funext i;by_cases hi:i=source
    · subst i;simp [hs]
    · simp [Function.update,hi]
  have h:=first.seq (middle.seq (last.congr he rfl))
  have hf : 1+1+((2*R+6)+1+1)=2*R+10 := by omega
  rw [hf] at h
  exact h

theorem successor_run {t : Nat} (R n : Nat) (width source target : Fin t)
    (hws : width≠source) (hwt : width≠target) (hst : source≠target)
    (H : Fin t→Nat) (A : Fin t→List Bool)
    (hw : H width=1) (hs : H source=1) (ht : H target=1)
    (hword : A width=UnaryTemplate.tape R) (hsource : A source=ZeroPadding.pad R (CompareMachine.word n))
    (hr : n+1≤R) (htl : (A target).length=R) :
    Step (successor width source target) (2*R+2*n+13) H A H
      (Function.update A target (ZeroPadding.pad R (CompareMachine.word (n+1)))) := by
  have hsl : (A source).length=R := by
    rw [hsource,ZeroPadding.pad_length]
    simp only [CompareMachine.word,List.length_cons,List.length_replicate]
    omega
  have first:=run R width source target hws hwt hst H A hw hs ht hword hsl htl
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
  have hf : (2*R+10)+1+(2*n+2)=2*R+2*n+13 := by omega
  rw [hf] at h
  exact h

end
end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalCounterCopy
