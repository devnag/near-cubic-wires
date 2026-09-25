import Proof.Packets.ScalarCounterSeed
import Proof.Packets.PhysicalIndexReload

/-! Canonical ambient-bank adapters for actual scalar production. Only the
selected scalar word changes; the count source and rewind allocation survive. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ScalarCounterInto
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def slots {t : Nat} (scalar log counter : Fin t) : Fin 3→Fin t := ![scalar,log,counter]
def machine {t : Nat} (scalar log counter : Fin t) := RecoveryFocus.machine (slots scalar log counter) ScalarFromCounter.machine
def zeroMachine {t : Nat} (scalar log counter : Fin t) :=
  Composition.machine (PhysicalIndexReload.move counter .right)
    (Composition.machine (machine scalar log counter) (PhysicalIndexReload.move counter .left))

theorem run {t : Nat} (u old R N : Nat) (scalar log counter : Fin t)
    (hinj : Function.Injective (slots scalar log counter)) (H : Fin t→Nat) (A : Fin t→List Bool)
    (hs : H scalar=0) (hl : H log=0) (hc : H counter=1)
    (as : A scalar=ZeroPadding.pad R (frame (SignedSortKey.binary u old)))
    (al : A log=List.replicate R false) (ac : A counter=ZeroPadding.pad R (CompareMachine.word N))
    (hn : N<2^u) (hr : 2*u+1≤R) :
    Step (machine scalar log counter) (ScalarFromCounter.budget u N) H A H
      (Function.update A scalar (ZeroPadding.pad R (frame (SignedSortKey.binary u N)))) := by
  have hsl : log≠scalar := by intro he;have h:=hinj (show slots scalar log counter 1=slots scalar log counter 0 from he);exact (by decide : (1 : Fin 3)≠0) h
  have hsc : counter≠scalar := by intro he;have h:=hinj (show slots scalar log counter 2=slots scalar log counter 0 from he);exact (by decide : (2 : Fin 3)≠0) h
  apply PhysicalFocusBoundary.focus (ScalarFromCounter.padded_run u old R N hn hr)
    (slots scalar log counter) hinj H H A _
  · intro i;fin_cases i <;> first | exact hs.symm | exact hl.symm | exact hc.symm
  · intro i;fin_cases i
    · exact as.symm
    · change ZeroPadding.pad 0 (List.replicate R false)=A log
      simpa only [ZeroPadding.pad_zero] using al.symm
    · exact ac.symm
  · intro i;fin_cases i <;> first | exact hs.symm | exact hl.symm | exact hc.symm
  · intro i;fin_cases i
    · change ZeroPadding.pad R (frame (SignedSortKey.binary u N))=
        Function.update A scalar (ZeroPadding.pad R (frame (SignedSortKey.binary u N))) scalar
      simp only [Function.update_self]
    · change ZeroPadding.pad 0 (List.replicate R false)=
        Function.update A scalar (ZeroPadding.pad R (frame (SignedSortKey.binary u N))) log
      simpa only [ZeroPadding.pad_zero,Function.update_of_ne hsl] using al.symm
    · change ZeroPadding.pad R (CompareMachine.word N)=
        Function.update A scalar (ZeroPadding.pad R (frame (SignedSortKey.binary u N))) counter
      simpa only [Function.update_of_ne hsc] using ac.symm
  · intro i away
    have hi : i≠scalar := by intro he;exact away 0 he.symm
    exact ⟨rfl,(Function.update_of_ne hi _ _).symm⟩

theorem zero_run {t : Nat} (u old R N : Nat) (scalar log counter : Fin t)
    (hinj : Function.Injective (slots scalar log counter)) (H : Fin t→Nat) (A : Fin t→List Bool)
    (hs : H scalar=0) (hl : H log=0) (hc : H counter=0)
    (as : A scalar=ZeroPadding.pad R (frame (SignedSortKey.binary u old)))
    (al : A log=List.replicate R false) (ac : A counter=ZeroPadding.pad R (CompareMachine.word N))
    (hn : N<2^u) (hr : 2*u+1≤R) :
    Step (zeroMachine scalar log counter) (ScalarFromCounter.budget u N+4) H A H
      (Function.update A scalar (ZeroPadding.pad R (frame (SignedSortKey.binary u N)))) := by
  have hsc : scalar≠counter := by intro he;have h:=hinj (show slots scalar log counter 0=slots scalar log counter 2 from he);exact (by decide : (0 : Fin 3)≠2) h
  have hlc : log≠counter := by intro he;have h:=hinj (show slots scalar log counter 1=slots scalar log counter 2 from he);exact (by decide : (1 : Fin 3)≠2) h
  have first:=PhysicalIndexReload.move_run counter .right H A
  simp only [hc,HeadMove.apply] at first
  have middle:=run u old R N scalar log counter hinj (Function.update H counter 1) A
    (by simpa only [Function.update_of_ne hsc] using hs)
    (by simpa only [Function.update_of_ne hlc] using hl) (by simp) as al ac hn hr
  have last:=PhysicalIndexReload.move_run counter .left (Function.update H counter 1)
    (Function.update A scalar (ZeroPadding.pad R (frame (SignedSortKey.binary u N))))
  simp only [Function.update_self,HeadMove.apply] at last
  have he : Function.update (Function.update H counter 1) counter 0=H := by
    funext i;by_cases hi:i=counter
    · subst i;simp [hc]
    · simp [Function.update,hi]
  have h:=first.seq (middle.seq (last.congr he rfl))
  have hf : 1+1+(ScalarFromCounter.budget u N+1+1)=ScalarFromCounter.budget u N+4 := by omega
  rw [hf] at h
  exact h

end
end PCJ9eff70d512234a4c_Fixed.Materializer.ScalarCounterInto
