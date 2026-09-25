import Proof.Rows.NativeScaleInput

/-! One native signed coefficient is read, reduced, multiplied by the resident
scale, and appended to the modular summand stream. Both consumers return the
same next bank; only the native source and append cursors advance. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_NativeScaleRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairRepresentation
open SignedSortKey PCJ45bee56da9f34d5a_NativeScaleInput
noncomputable section

def rewind:=RecoveryFocus.machine (![0,62,63] : Fin 3→Fin 91) CompetitorRecordRewind.machine
def scale:=TapeEmbedding.machine 26 PCJ45bee56da9f34d5a_ResidueScaleCell.machine
def erase:=RecoveryFocus.machine (![0,62,63] : Fin 3→Fin 91) (RecoveryScratchErase.resetMachine 1)
def machine (negate : Bool):=Composition.machine (Composition.machine (Composition.machine (read negate) rewind) scale) erase

theorem rewind_run (a p w F U pos len cursor : Nat) (source out coefficient : List Bool)
    (hc : cursor≤U) :
    Step rewind (2*U+2) (heads pos len cursor) (bank a p w F U source out coefficient)
      (heads pos len 0) (bank a p w F U source out coefficient):=by
  have h:=CloseoutRowsTupleSeek.rewind_at (0 : Fin 91) 62 63 (by decide) (by decide) (by decide)
    U (heads pos len cursor) (bank a p w F U source out coefficient) hc rfl rfl rfl rfl
  apply h.congr
  · funext i;by_cases hi:i=0 <;>simp [heads,Function.update,hi]
  · rfl

theorem scale_run (a b p w F U pos : Nat) (source out : List Bool)
    (hp : 0<p) (hpw : 2*p≤2^w) (ha : a<2^w) (hb : b<2^w)
    (hU : 1024*(w+1)^2+2≤U) :
    Step scale (1024*(w+1)^2+6*U+2*w+19)
      (heads pos out.length 0) (bank a p w F U source out (ZeroPadding.pad U (frame (binary w b))))
      (heads pos (out++frame (binary w ((a*b)%p))).length 0)
      (bank a p w F U source (out++frame (binary w ((a*b)%p))) (ZeroPadding.pad U (frame (binary w b)))):=by
  have body:=(PCJ45bee56da9f34d5a_ResidueScaleBounds.run a b p w U out hp hpw ha hb hU).pad
    (fun i : Fin 65=>if i=0 then U else 0)
  rw [main_eq,main_eq] at body
  have h:=body.embed (fun i : Fin 26=>if i=0 then pos else 0) (extras F w p source)
  refine (h.congr_in ?_ rfl).congr ?_ rfl
  all_goals funext i;fin_cases i <;>rfl

theorem erase_run (a p w F U pos : Nat) (source out coefficient : List Bool) (hc : coefficient.length≤U) :
    Step erase (2*U+4) (heads pos out.length 0) (bank a p w F U source out coefficient)
      (heads pos out.length 0) (bank a p w F U source out (List.replicate U false)):=by
  have h:=(Step.of_ready (RecoveryScratchErase.erase_ready U (U+1)
    (fun _ : Fin 1=>coefficient) (fun _=>hc))).dock (![0,62,63] : Fin 3→Fin 91) (by decide)
    (heads pos out.length 0) (bank a p w F U source out coefficient)
    (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
  apply h.congr
  · exact dockH_existing _ _ _ (by intro i;fin_cases i <;>rfl)
  · apply HierarchyAllocation.install_eq (![0,62,63] : Fin 3→Fin 91) (by decide)
    · intro i;fin_cases i <;>simp only [Nat.max_self] <;>rfl
    · intro i hi;fin_cases i
      all_goals first
        | rfl
        | exact False.elim (hi 0 rfl)

def budget (negate : Bool) (z : Int) (w F U : Nat):=
  2*C10NativeResidueCallback.coreBudget negate z w+2*F+1024*(w+1)^2+10*U+18*w+55

theorem run (negate : Bool) (pre tail out : List Bool) (z : Int) (a p w F U : Nat)
    (hp : 0<p) (hpw : 2*p≤2^w) (ha : a<2^w)
    (hF : C10NativeResidueCallback.coreBudget negate z w+1≤F)
    (hU : 1024*(w+1)^2+2≤U) :
    Step (machine negate) (budget negate z w F U)
      (heads pre.length out.length 0) (bank a p w F U (pre++intWord z++tail) out (List.replicate U false))
      (heads (pre.length+(intWord z).length)
        (out++frame (binary w ((a*FinalPrimeReduce.intResidue p (if negate then -z else z))%p))).length 0)
      (bank a p w F U (pre++intWord z++tail)
        (out++frame (binary w ((a*FinalPrimeReduce.intResidue p (if negate then -z else z))%p)))
        (List.replicate U false)):=by
  let b:=FinalPrimeReduce.intResidue p (if negate then -z else z)
  have hb:b<2^w:=by have hh:=FinalPrimeReduce.intResidue_lt p hp (if negate then -z else z);dsimp only [b];omega
  have hwu:2*w+1≤U:=by nlinarith
  have first:=read_run negate pre tail out z a p w F U hp hpw hF
  have second:=rewind_run a p w F U (pre.length+(intWord z).length) out.length (2*w+1)
    (pre++intWord z++tail) out (ZeroPadding.pad U (frame (binary w b))) hwu
  have third:=scale_run a b p w F U (pre.length+(intWord z).length) (pre++intWord z++tail) out hp hpw ha hb hU
  have last:=erase_run a p w F U (pre.length+(intWord z).length) (pre++intWord z++tail)
    (out++frame (binary w ((a*b)%p))) (ZeroPadding.pad U (frame (binary w b)))
    (by simp [ZeroPadding.pad_length,frame_length,binary_length];omega)
  have all:=((first.seq second).seq third).seq last
  unfold machine
  convert all using 1
  unfold budget
  omega
end
end PCJ45bee56da9f34d5a_NativeScaleRun
