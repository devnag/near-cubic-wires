import Proof.Packets.ScalarCounterSeed
import Proof.Packets.PhysicalIndexReload

/-! Place the physically initialized binary-zero scalar in any ambient bank.
The all-zero-head variant pays both width-driver head moves. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ScalarSeedInto
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def slots {t : Nat} (scalar log width : Fin t) : Fin 3→Fin t := ![width,scalar,log]
def machine {t : Nat} (scalar log width : Fin t) := RecoveryFocus.machine (slots scalar log width) ScalarCounterSeed.machine
def zeroMachine {t : Nat} (scalar log width : Fin t) :=
  Composition.machine (PhysicalIndexReload.move width .right)
    (Composition.machine (machine scalar log width) (PhysicalIndexReload.move width .left))

theorem run {t : Nat} (u R : Nat) (scalar log width : Fin t)
    (hinj : Function.Injective (slots scalar log width)) (H : Fin t→Nat) (A : Fin t→List Bool)
    (hs : H scalar=0) (hl : H log=0) (hw : H width=1)
    (as : A scalar=List.replicate R false) (al : A log=List.replicate R false)
    (aw : A width=ZeroPadding.pad R (CompareMachine.word u)) (hr : 2*u+1≤R) :
    Step (machine scalar log width) (ScalarCounterSeed.budget u) H A H
      (Function.update A scalar (ZeroPadding.pad R (frame (SignedSortKey.binary u 0)))) := by
  have hsl : log≠scalar := by intro he;have h:=hinj (show slots scalar log width 2=slots scalar log width 1 from he);exact (by decide : (2 : Fin 3)≠1) h
  have hsw : width≠scalar := by intro he;have h:=hinj (show slots scalar log width 0=slots scalar log width 1 from he);exact (by decide : (0 : Fin 3)≠1) h
  apply PhysicalFocusBoundary.focus (ScalarCounterSeed.padded_run u R hr) (slots scalar log width) hinj H H A _
  · intro i;fin_cases i <;>first | exact hw.symm | exact hs.symm | exact hl.symm
  · intro i;fin_cases i
    · exact aw.symm
    · change ZeroPadding.pad R []=A scalar
      exact as.symm
    · change ZeroPadding.pad 0 (List.replicate R false)=A log
      simpa only [ZeroPadding.pad_zero] using al.symm
  · intro i;fin_cases i <;>first | exact hw.symm | exact hs.symm | exact hl.symm
  · intro i;fin_cases i
    · change ZeroPadding.pad R (CompareMachine.word u)=
        Function.update A scalar (ZeroPadding.pad R (frame (SignedSortKey.binary u 0))) width
      simpa only [Function.update_of_ne hsw] using aw.symm
    · change ZeroPadding.pad R (frame (SignedSortKey.binary u 0))=
        Function.update A scalar (ZeroPadding.pad R (frame (SignedSortKey.binary u 0))) scalar
      simp only [Function.update_self]
    · change ZeroPadding.pad 0 (List.replicate R false)=
        Function.update A scalar (ZeroPadding.pad R (frame (SignedSortKey.binary u 0))) log
      simpa only [ZeroPadding.pad_zero,Function.update_of_ne hsl] using al.symm
  · intro i away
    have hi : i≠scalar := by intro he;exact away 1 he.symm
    exact ⟨rfl,(Function.update_of_ne hi _ _).symm⟩

theorem zero_run {t : Nat} (u R : Nat) (scalar log width : Fin t)
    (hinj : Function.Injective (slots scalar log width)) (H : Fin t→Nat) (A : Fin t→List Bool)
    (hs : H scalar=0) (hl : H log=0) (hw : H width=0)
    (as : A scalar=List.replicate R false) (al : A log=List.replicate R false)
    (aw : A width=ZeroPadding.pad R (CompareMachine.word u)) (hr : 2*u+1≤R) :
    Step (zeroMachine scalar log width) (ScalarCounterSeed.budget u+4) H A H
      (Function.update A scalar (ZeroPadding.pad R (frame (SignedSortKey.binary u 0)))) := by
  have hsw : scalar≠width := by intro he;have h:=hinj (show slots scalar log width 1=slots scalar log width 0 from he);exact (by decide : (1 : Fin 3)≠0) h
  have hlw : log≠width := by intro he;have h:=hinj (show slots scalar log width 2=slots scalar log width 0 from he);exact (by decide : (2 : Fin 3)≠0) h
  have first:=PhysicalIndexReload.move_run width .right H A
  simp only [hw,HeadMove.apply] at first
  have middle:=run u R scalar log width hinj (Function.update H width 1) A
    (by simpa only [Function.update_of_ne hsw] using hs)
    (by simpa only [Function.update_of_ne hlw] using hl) (by simp) as al aw hr
  have last:=PhysicalIndexReload.move_run width .left (Function.update H width 1)
    (Function.update A scalar (ZeroPadding.pad R (frame (SignedSortKey.binary u 0))))
  simp only [Function.update_self,HeadMove.apply] at last
  have he : Function.update (Function.update H width 1) width 0=H := by
    funext i;by_cases hi:i=width
    · subst i;simp [hw]
    · simp [Function.update,hi]
  have h:=first.seq (middle.seq (last.congr he rfl))
  have hf : 1+1+(ScalarCounterSeed.budget u+1+1)=ScalarCounterSeed.budget u+4 := by omega
  rw [hf] at h
  exact h

end
end PCJ9eff70d512234a4c_Fixed.Materializer.ScalarSeedInto
