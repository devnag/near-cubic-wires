import Proof.CaseAnalysis.RowsModeHashLoop

/-! The actual hash-prefix scan returns all three literal cell flags:
zero prefix, its one-bit sibling, and its zero child. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeHashCell
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 5 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=2)
  rule:=fun q bits=>if q=0 then some ⟨1,fun i=>if i=2 then some true else none,fun _=>.stay⟩
    else if q=1 then some (if bits 1 then ⟨1,fun i=>if i=2 then some (bits 2&&!bits 0) else none,
      ![.right,.right,.stay,.stay,.stay]⟩ else ⟨2,![none,none,none,some (bits 2&&bits 0),some (bits 2&&!bits 0)],fun _=>.stay⟩)
    else none

def data (level : Nat) (bits : List Bool) (zero sibling child : Bool) : Fin 5→List Bool:=
  ![bits,List.replicate level true,[zero],[sibling],[child]]
def cfg (q : Fin 3) (level pos : Nat) (bits : List Bool) (zero sibling child : Bool) : Configuration 5 3:=
  ⟨q,![pos,pos,0,0,0],data level bits zero sibling child⟩
def zeroFlag (pre : List Bool):=pre.all (! ·)

theorem scan (pre tail rest : List Bool) (z s c : Bool) :
    Timed machine tail.length
      (cfg 1 (pre.length+tail.length) pre.length (pre++tail++rest) z s c)
      (cfg 1 (pre.length+tail.length) (pre.length+tail.length) (pre++tail++rest) (z&&zeroFlag tail) s c):=by
  induction tail generalizing pre z with
  | nil=>simpa [zeroFlag] using Timed.refl machine (cfg 1 pre.length pre.length (pre++rest) z s c)
  | cons bit tail ih=>
    have head:Timed machine 1
        (cfg 1 (pre.length+(bit::tail).length) pre.length (pre++(bit::tail)++rest) z s c)
        (cfg 1 (pre.length+(bit::tail).length) (pre.length+1) (pre++(bit::tail)++rest) (z&&!bit) s c):=by
      have hb:readTapeBit (pre++(bit::tail)++rest) pre.length=bit:=by simpa using Streaming.read_append pre (tail++rest) bit
      have hd:readTapeBit (List.replicate (pre.length+(bit::tail).length) true) pre.length=true:=by rw [ClockUnaryProduct.read_unary];simp
      apply Timed.single (by rfl)
      simp only [step,machine,cfg,Configuration.scanned,data,Matrix.cons_val_zero,Matrix.cons_val_one,hb,hd,if_true]
      apply congrArg some
      apply configuration_ext
      · rfl
      · funext i;fin_cases i <;> rfl
      · funext i;fin_cases i <;> simp [applyAction,writeTapeBit,readTapeBit,List.getD]
    have ht:=ih (pre++[bit]) (z&&!bit)
    have time:1+tail.length=(bit::tail).length:=by simp;omega
    have whole:=head.trans (by simpa [List.length_append,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht)
    rw [time] at whole
    simpa [zeroFlag,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Bool.and_assoc] using whole

theorem finish_step (bits : List Bool) (level : Nat) (z s c : Bool) :
    step machine (cfg 1 level level bits z s c)=
      some (cfg 2 level level bits z (z&&readTapeBit bits level) (z&&!readTapeBit bits level)):=by
  have hd:readTapeBit (List.replicate level true) level=false:=by rw [ClockUnaryProduct.read_unary];simp
  simp only [step,machine,cfg,Configuration.scanned,data,Matrix.cons_val_zero,Matrix.cons_val_one,hd,if_true,Bool.false_eq_true,if_false]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> simp [applyAction,writeTapeBit,readTapeBit,List.getD]

theorem cell_run (pre rest : List Bool) (z s c : Bool) :
    ∃ r,runFrom machine (pre.length+2) (cfg 0 pre.length 0 (pre++rest) z s c)=some r ∧
      r.final=cfg 2 pre.length pre.length (pre++rest) (zeroFlag pre)
        (zeroFlag pre&&readTapeBit (pre++rest) pre.length)
        (zeroFlag pre&&!readTapeBit (pre++rest) pre.length) ∧r.steps=pre.length+2:=by
  have start:step machine (cfg 0 pre.length 0 (pre++rest) z s c)=
      some (cfg 1 pre.length 0 (pre++rest) true s c):=by
    simp only [step,machine,cfg,if_true]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> simp [applyAction,data,writeTapeBit]
  have middle:=scan [] pre rest true s c
  simp only [List.length_nil,List.nil_append,Nat.zero_add,Bool.true_and] at middle
  have whole:=((Timed.single (by rfl) start).trans middle).trans
    (Timed.single (by rfl) (finish_step (pre++rest) pre.length (zeroFlag pre) s c))
  have time:(1+pre.length)+1=pre.length+2:=by omega
  rw [time] at whole
  exact whole.run (by rfl)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeHashCell
