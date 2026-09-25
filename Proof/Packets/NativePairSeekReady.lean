import Proof.CaseAnalysis.RowsRawPairSeek
import Proof.Packets.MaskProductReady

/-! The actual unary occurrence index seeks through resident native pairs;
its cursor is paid back to head one. This permits a descending literal-code
stream to access the original ascending atom cache without reordering data. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NativePairSeekReady
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsRawPairSeek (Pair cacheWord)

def slot : Fin 1→Fin 2 := ![0]
noncomputable def machine := Composition.machine CloseoutRowsRawPairSeek.loop
  (RecoveryFocus.machine slot PairCountReady.machine)
def budget (ps : List Pair) := CloseoutRowsRawPairSeek.budget ps+1+(ps.length+2)

theorem pad_append_false (R : Nat) (bits : List Bool) (h : bits.length<R) :
    ZeroPadding.pad R (bits++[false])=ZeroPadding.pad R bits := by
  simp only [ZeroPadding.pad,List.length_append,List.length_singleton,List.append_assoc]
  apply congrArg (bits++·)
  change List.replicate 1 false++List.replicate (R-(bits.length+1)) false=List.replicate (R-bits.length) false
  rw [←List.replicate_add]
  congr 1
  omega

theorem run (R : Nat) (pre : List Pair) (tail : List Bool) (hR : pre.length+2≤R) :
    Step machine (budget pre) (![1,0])
      (![ZeroPadding.pad R (CompareMachine.word pre.length),cacheWord pre++tail])
      (![1,(cacheWord pre).length])
      (![ZeroPadding.pad R (CompareMachine.word pre.length),cacheWord pre++tail]) := by
  have first:=(CloseoutRowsRawPairSeek.loop_run pre [false] [] [] tail).pad (![R,0] : Fin 2→Nat)
  have eqword : ZeroPadding.pad R ([false]++List.replicate pre.length true++[false])=
      ZeroPadding.pad R (CompareMachine.word pre.length) := by
    apply pad_append_false
    simp only [List.length_append,List.length_singleton,List.length_replicate]
    omega
  simp only [List.singleton_append,List.cons_append,List.nil_append] at eqword
  have first' : Step CloseoutRowsRawPairSeek.loop (CloseoutRowsRawPairSeek.budget pre)
      (![1,0]) (![ZeroPadding.pad R (CompareMachine.word pre.length),cacheWord pre++tail])
      (![pre.length+1,(cacheWord pre).length])
      (![ZeroPadding.pad R (CompareMachine.word pre.length),cacheWord pre++tail]) := by
    convert first using 1 <;>
      (funext i;fin_cases i <;>simp [CloseoutRowsRawAtomSeek.heads,CloseoutRowsRawAtomSeek.data,
        eqword,ZeroPadding.pad_zero,Nat.add_comm])
  obtain ⟨r,rr,rf,_⟩:=PairCountReady.run pre.length
  have small:=(Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)).pad (fun _=>R)
  have last : Step (RecoveryFocus.machine slot PairCountReady.machine) (pre.length+2)
      (![pre.length+1,(cacheWord pre).length])
      (![ZeroPadding.pad R (CompareMachine.word pre.length),cacheWord pre++tail])
      (![1,(cacheWord pre).length])
      (![ZeroPadding.pad R (CompareMachine.word pre.length),cacheWord pre++tail]) := by
    apply PhysicalFocusBoundary.focus small slot (by decide)
      (![pre.length+1,(cacheWord pre).length]) (![1,(cacheWord pre).length])
      (![ZeroPadding.pad R (CompareMachine.word pre.length),cacheWord pre++tail])
      (![ZeroPadding.pad R (CompareMachine.word pre.length),cacheWord pre++tail])
    · intro i;fin_cases i;rfl
    · intro i;fin_cases i;rfl
    · intro i;fin_cases i;rfl
    · intro i;fin_cases i;rfl
    · intro i away;fin_cases i
      · exact False.elim (away 0 rfl)
      · exact ⟨rfl,rfl⟩
  exact first'.seq last

end PCJ9eff70d512234a4c_Fixed.Materializer.NativePairSeekReady
