import Proof.PCP.ProjectionNormalizationUnaryCore
import Proof.CaseAnalysis.RowsModeParity
import Proof.MachineModel.Encoding

/-! A real binary tuple/literal index emits its exact ordinary raw index
block. The existing predecessor loop appends the unary marks and consumes
the private binary copy; original tuple/cache tapes remain outside it. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeIndexBlock
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch RadixSemantics SignedSortKey
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def mark (bit : Bool) : Machine 4 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q _=>if q=0 then
    some ⟨1,![none,none,none,some bit],![.stay,.stay,.stay,.right]⟩ else none

theorem mark_run (bit : Bool) (bits out : List Bool) (flag : Bool) (C : Nat) :
    ∃ r,runFrom (mark bit) 1 (UnaryCore.cfg 0 bits flag C out)=some r ∧
      r.final=UnaryCore.cfg 1 bits flag C (out++[bit]) ∧ r.steps=1 := by
  have hs:step (mark bit) (UnaryCore.cfg 0 bits flag C out)=
      some (UnaryCore.cfg 1 bits flag C (out++[bit])):=by
    simp [step,mark,UnaryCore.cfg]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
    · funext i;fin_cases i <;> simp [applyAction,Streaming.write_append]
  exact (Timed.single (by rfl) hs).run (by rfl)

noncomputable def machine:=Composition.machine (Composition.machine (mark true) UnaryCore.machine) (mark false)
def budget (w n : Nat):=n*(4*w+7)+4*w+9

theorem block_run (w n C : Nat) (out : List Bool) (flag : Bool) (hn : n<2^w) (hc : 2*w+1≤C) :
    ∃ residue : List Bool,residue.length=w ∧
      Step machine (budget w n) ![0,0,0,out.length]
        ![frame (binary w n),[flag],List.replicate C false,out]
        ![0,0,0,(out++ExtIncidence.block n).length]
        ![frame residue,[false],List.replicate C false,out++ExtIncidence.block n] := by
  obtain ⟨a,ha,af,_⟩:=mark_run true (binary w n) out flag C
  obtain ⟨residue,hres,ht⟩:=UnaryCore.loop n (binary w n) (out++[true]) flag C (binary_value w n hn)
  obtain ⟨b,hb,bf,_⟩:=ht.run (by simp [UnaryCore.machine,UnaryCore.stopped,UnaryCore.cfg,
    RecoveryCalls.machine,RecoveryCalls.controlCode])
  have hi : Composition.restart a.final UnaryCore.machine.start=
      UnaryCore.nodeCfg 0 (binary w n) flag C (out++[true]):=by rw [af];rfl
  rw [←hi] at hb
  have first:=Composition.run_join (mark true) UnaryCore.machine _ _ _ a b ha hb
  have hc' : max C (2*(binary w n).length+1)=C:=by simp only [binary_length];omega
  obtain ⟨c,hcRun,cf,_⟩:=mark_run false residue
    ((out++[true])++List.replicate n true) false C
  have hj : Composition.restart (Composition.joinedReceipt a b).final (mark false).start=
      UnaryCore.cfg 0 residue false C ((out++[true])++List.replicate n true):=by
    change Composition.restart b.final _=_
    rw [bf,hc'];rfl
  rw [←hj] at hcRun
  have whole:=Composition.run_join (Composition.machine (mark true) UnaryCore.machine)
    (mark false) _ _ _ (Composition.joinedReceipt a b) c first hcRun
  have time : 1+1+(n*(4*(binary w n).length+7)+4*(binary w n).length+5)+1+1=budget w n:=by
    simp only [binary_length,budget];omega
  rw [time] at whole
  have output : (((out++[true])++List.replicate n true)++[false])=out++ExtIncidence.block n:=by
    simp [ExtIncidence.block,List.replicate_succ,List.append_assoc]
  refine ⟨residue,hres.trans (binary_length w n),Step.of_run whole ?_ ?_⟩
  · change c.final.heads=_
    rw [cf,output];rfl
  · change c.final.tapes=_
    rw [cf,output];rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsModeIndexBlock
