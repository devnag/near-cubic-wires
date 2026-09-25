import Proof.CaseAnalysis.RowsModeHashFields

/-! The same physical selector reads the original mask at its live cursor;
no singleton copy or supplied per-occurrence mask bit is needed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeLiteralScan
open LocalBitMultitape ExtDecompositionBatch RepairSource.VerifierDecoding CloseoutRowsModeLiteralSelect
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (pos count : Nat) : Fin 7→Nat:=![0,0,0,pos,0,0,count+1]
def data (z s c : Bool) (mask : List Bool) (v n : Bool) (count : Nat) : Fin 7→List Bool:=
  ![[z],[s],[c],mask,[v],[n],CompareMachine.word count]

theorem write_marks_litscan (position : Nat) :
    writeTapeBit (List.replicate position true) position true = List.replicate (position + 1) true := by
  simpa only [List.length_replicate, List.replicate_add, List.replicate_one] using
    Streaming.write_append (List.replicate position true) true

theorem scan_run (mode : Fin 3) (z s c v n : Bool) (mask : List Bool) (pos count : Nat) :
    Step (machine mode) 1 (heads pos count) (data z s c mask v n count)
      (heads pos (count+c.toNat)) (data z s c mask (varFlag mode z s c (readTapeBit mask pos)) (negative mode z s c) (count+c.toNat)):=by
  have hs:step (machine mode) ⟨0,heads pos count,data z s c mask v n count⟩=
      some ⟨1,heads pos (count+c.toNat),data z s c mask (varFlag mode z s c (readTapeBit mask pos)) (negative mode z s c) (count+c.toNat)⟩:=by
    have hsel:(⟨0,heads pos count,data z s c mask v n count⟩ : Configuration 7 2).scanned (mode.castAdd 4)=chosen mode z s c:=by
      fin_cases mode <;> rfl
    have hm:(⟨0,heads pos count,data z s c mask v n count⟩ : Configuration 7 2).scanned 3=readTapeBit mask pos:=rfl
    have hc:(⟨0,heads pos count,data z s c mask v n count⟩ : Configuration 7 2).scanned 2=c:=rfl
    simp only [step,machine,if_true,hsel,hm,hc]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> cases c <;> simp only [Bool.false_eq_true, Bool.if_false_right, Bool.toNat, Fin.isValue, Fin.mk_one, Fin.reduceEq, Fin.reduceFinMk, Fin.zero_eta, HeadMove.apply, Matrix.cons_val, Matrix.cons_val_one, Matrix.cons_val_zero, Nat.add_assoc, Nat.reduceAdd, add_zero, and_false, and_true, applyAction, cond_false, cond_true, heads, ↓reduceIte]
    · funext i;fin_cases i <;> cases c <;> simp only [Bool.false_eq_true, Bool.if_false_right, Bool.toNat, CompareMachine.word, Fin.isValue, Fin.mk_one, Fin.reduceEq, Fin.reduceFinMk, Fin.zero_eta, List.replicate_add, List.replicate_one, Matrix.cons_val, Matrix.cons_val_one, Matrix.cons_val_zero, Nat.reduceAdd, add_zero, and_false, and_true, applyAction, cond_false, cond_true, data, heads, negative, varFlag, writeTapeBit, ↓reduceIte, write_marks_litscan]
  obtain ⟨r,hr,rf,_⟩:=(RecoveryExecution.Timed.single (by rfl) hs).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeLiteralScan
