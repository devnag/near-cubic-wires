import Proof.Packets.WindowSeedScalar
import Proof.Packets.PhysicalOneOutput

/-! The actual seed workers overwrite only their named destination in the
69-tape window/metadata arena. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option warningAsError true
set_option linter.unnecessarySeqFocus false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open SignedSortKey
noncomputable section

def copySlots (s d : Fin 69) : Fin 4→Fin 69 := ![s,d,50,51]
def rawSlots (s d : Fin 69) : Fin 3→Fin 69 := ![s,d,51]
def valueSlots (s d : Fin 69) : Fin 3→Fin 69 := ![d,51,s]
def copyAt (s d : Fin 69) := RecoveryFocus.machine (copySlots s d) copy
def rawAt (s d : Fin 69) := RecoveryFocus.machine (rawSlots s d) raw
def zeroAt (s d : Fin 69) := RecoveryFocus.machine (rawSlots s d) scalarZero
def valueAt (s d : Fin 69) := RecoveryFocus.machine (valueSlots s d) scalarValue
def predAt (d : Fin 69) := RecoveryFocus.machine (fun _ : Fin 1=>d) countPred

theorem copy_at (R : Nat) (s d : Fin 69) (A : Fin 69→List Bool)
    (hinj : Function.Injective (copySlots s d)) (hsrc : (A s).length≤R)
    (hd : A d=List.replicate R false) (hr : A 50=List.replicate R true)
    (hl : A 51=List.replicate (R+3) false) :
    Step (copyAt s d) (2*R+4) (fun _=>0) A (fun _=>0)
      (Function.update A d (ZeroPadding.pad R (A s))) := by
  have h:=copy_run R (A s) hsrc
  have h' : Step copy (2*R+4) (fun _=>0) (copyData R (A s) (List.replicate R false))
      (fun _=>0) (Function.update (copyData R (A s) (List.replicate R false)) 1 (ZeroPadding.pad R (A s))) := by
    convert h using 1 <;>first | rfl | (funext i;fin_cases i <;>rfl)
  exact PhysicalOneOutput.focus copy _ _ 1 _ h' (copySlots s d) hinj (fun _=>0) A
    (fun _=>rfl) (by intro i;fin_cases i <;>first | rfl | exact hd | exact hr | exact hl)

theorem raw_at (R n : Nat) (s d : Fin 69) (A : Fin 69→List Bool)
    (hinj : Function.Injective (rawSlots s d)) (hn : n≤R+1)
    (hs : A s=source R n) (hd : A d=List.replicate R false)
    (hl : A 51=List.replicate (R+3) false) :
    Step (rawAt s d) (2*n+6) (fun _=>0) A (fun _=>0)
      (Function.update A d (ZeroPadding.pad R (List.replicate n true))) := by
  have h:=raw_run R n hn
  have h' : Step raw (2*n+6) (fun _=>0) (rawData R n [])
      (fun _=>0) (Function.update (rawData R n []) 1 (ZeroPadding.pad R (List.replicate n true))) := by
    convert h using 1 <;>first | rfl | (funext i;fin_cases i <;>rfl)
  apply PhysicalOneOutput.focus raw _ _ 1 _ h' (rawSlots s d) hinj (fun _=>0) A (fun _=>rfl)
  intro i;fin_cases i
  · exact hs
  · simpa [rawSlots,rawData,ZeroPadding.pad] using hd
  · exact hl

theorem zero_at (R u : Nat) (s d : Fin 69) (A : Fin 69→List Bool)
    (hinj : Function.Injective (rawSlots s d)) (hu : 2*u+1≤R+3)
    (hs : A s=source R u) (hd : A d=List.replicate R false)
    (hl : A 51=List.replicate (R+3) false) :
    Step (zeroAt s d) (8*u+11) (fun _=>0) A (fun _=>0)
      (Function.update A d (ZeroPadding.pad R (frame (binary u 0)))) := by
  have h:=scalar_zero_run R u hu
  have h' : Step scalarZero (8*u+11) (fun _=>0) (scalarData R u [])
      (fun _=>0) (Function.update (scalarData R u []) 1 (ZeroPadding.pad R (frame (binary u 0)))) := by
    convert h using 1 <;>first | rfl | (funext i;fin_cases i <;>rfl)
  apply PhysicalOneOutput.focus scalarZero _ _ 1 _ h' (rawSlots s d) hinj (fun _=>0) A (fun _=>rfl)
  intro i;fin_cases i
  · exact hs
  · simpa [rawSlots,scalarData,ZeroPadding.pad] using hd
  · exact hl

theorem value_at (R u old n : Nat) (s d : Fin 69) (A : Fin 69→List Bool)
    (hinj : Function.Injective (valueSlots s d)) (hn : n<2^u) (hu : 2*u+1≤R+3)
    (hs : A s=source R n) (hd : A d=ZeroPadding.pad R (frame (binary u old)))
    (hl : A 51=List.replicate (R+3) false) :
    Step (valueAt s d) (ScalarFromCounter.budget u n+4) (fun _=>0) A (fun _=>0)
      (Function.update A d (ZeroPadding.pad R (frame (binary u n)))) := by
  have h:=scalar_value_run R u old n hn hu
  have h' : Step scalarValue (ScalarFromCounter.budget u n+4) (fun _=>0) (valueData R u old n)
      (fun _=>0) (Function.update (valueData R u old n) 0 (ZeroPadding.pad R (frame (binary u n)))) := by
    convert h using 1 <;>first | rfl | (funext i;fin_cases i <;>rfl)
  exact PhysicalOneOutput.focus scalarValue _ _ 0 _ h' (valueSlots s d) hinj (fun _=>0) A
    (fun _=>rfl) (by intro i;fin_cases i <;>first | exact hd | exact hl | exact hs)

theorem pred_at (R n : Nat) (d : Fin 69) (A : Fin 69→List Bool)
    (hn : n+1≤R) (hd : A d=source R n) :
    Step (predAt d) (2*n+7) (fun _=>0) A (fun _=>0)
      (Function.update A d (source R (n-1))) := by
  have h:=count_pred_run R n hn
  have h' : Step countPred (2*n+7) (fun _=>0) (fun _=>source R n)
      (fun _=>0) (Function.update (fun _=>source R n) (0 : Fin 1) (source R (n-1))) := by
    convert h using 1 <;>first | rfl | (funext i;fin_cases i;rfl)
  exact PhysicalOneOutput.focus countPred _ _ 0 _ h' (fun _ : Fin 1=>d)
    (fun _ _ _=>Subsingleton.elim _ _) (fun _=>0) A (fun _=>rfl) (fun _=>hd)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
