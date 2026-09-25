import Proof.CaseAnalysis.RowsModeElementaryMasterPadding

/-! A two-transition selector reads the actual coefficient, original M,
and elementary degree. It preserves the constant monomial when M=a=0. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowSelect
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def result (guard live positiveDegree : Bool) : Fin 5:=
  if !guard then 2 else if live then 3 else if !positiveDegree then 4 else 2
def machine : Machine 60 5 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (2≤q.val)
  rule:=fun q bits=>if q=0 then some ⟨1,fun _=>none,fun i=>if i=48 then .right else .stay⟩
    else if q=1 then some ⟨result (bits 56) (bits 59) (bits 48),fun _=>none,
      fun i=>if i=48 then .left else .stay⟩ else none

theorem selected_run (H : Fin 60→Nat) (A : Fin 60→List Bool) (guard live positiveDegree : Bool)
    (h48 : H 48=0) (h56 : H 56=0) (h59 : H 59=0)
    (a48 : readTapeBit (A 48) 1=positiveDegree) (a56 : readTapeBit (A 56) 0=guard)
    (a59 : readTapeBit (A 59) 0=live) :
    ∃ r,runFrom machine 2 ⟨machine.start,H,A⟩=some r ∧
      r.final=⟨result guard live positiveDegree,H,A⟩ ∧ r.steps=2:=by
  have first:step machine ⟨0,H,A⟩=some ⟨1,Function.update H 48 1,A⟩:=by
    simp [step,machine]
    apply configuration_ext
    · rfl
    · funext i
      by_cases hi:i=48
      · subst i;simp [applyAction,HeadMove.apply,h48]
      · simp [applyAction,HeadMove.apply,hi]
    · rfl
  have second:step machine ⟨1,Function.update H 48 1,A⟩=
      some ⟨result guard live positiveDegree,H,A⟩:=by
    simp [step,machine,Configuration.scanned,h56,h59,a48,a56,a59]
    apply configuration_ext
    · rfl
    · funext i
      by_cases hi:i=48
      · subst i;simp [applyAction,HeadMove.apply,h48]
      · simp [applyAction,HeadMove.apply,hi]
    · rfl
  have last:machine.halted (result guard live positiveDegree)=true:=by
    cases guard <;> cases live <;> cases positiveDegree <;> decide
  exact ((Timed.single (by rfl) first).trans (Timed.single (by rfl) second)).run last

end NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowSelect
