import Proof.CaseAnalysis.RowsModeShift

/-! Both window coefficients are computed by actual scalar scans. The
accumulator is initialized by a real write, and every scalar cursor returns. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowGuard
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extra (w degree target : Nat) : Fin 2→List Bool:=![frame (binary w degree),frame (binary w target)]
def data (w offset b scratch degree target C : Nat) (nonzero guard : Bool) : Fin 8→List Bool:=
  Fin.addCases (m:=6) (n:=2) (motive:=fun _=>List Bool)
    (CloseoutRowsModeShift.data w offset b scratch C nonzero guard) (extra w degree target)
def init : Machine 8 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q _=>if q=0 then some ⟨1,fun i=>if i=4 then some true else none,fun _=>.stay⟩ else none
def paritySlots : Fin 4→Fin 8:=![6,7,4,5]
noncomputable def parity:=RecoveryFocus.machine paritySlots CloseoutRowsModeParityReusable.machine
noncomputable def shift:=TapeEmbedding.machine 2 CloseoutRowsModeShift.machine
noncomputable def machine:=Composition.machine (Composition.machine init parity) shift

theorem init_run (w offset b scratch degree target C : Nat) (nonzero guard : Bool) :
    Step init 1 (fun _=>0) (data w offset b scratch degree target C nonzero guard)
      (fun _=>0) (data w offset b scratch degree target C nonzero true):=by
  have hs:step init ⟨0,fun _=>0,data w offset b scratch degree target C nonzero guard⟩=
      some ⟨1,fun _=>0,data w offset b scratch degree target C nonzero true⟩:=by
    simp [step,init]
    apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i <;> rfl
  obtain ⟨r,hr,rf,_⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

theorem parity_run (w offset b scratch degree target C : Nat) (nonzero : Bool)
    (hd : degree<2^w) (ht : target<2^w) (hC : 2*w+1≤C) :
    Step parity (4*w+4) (fun _=>0) (data w offset b scratch degree target C nonzero true)
      (fun _=>0) (data w offset b scratch degree target C nonzero (degree.choose target%2==1)):=by
  have localRun:=CloseoutRowsModeParityReusable.parity_ready w degree target C true hd ht hC
  simp only [Bool.true_and] at localRun
  have focused:=localRun.focus paritySlots (by decide) (data w offset b scratch degree target C nonzero true)
    (by intro i;fin_cases i <;> rfl)
  apply (Step.of_ready focused).congr rfl
  funext i;fin_cases i
  all_goals first
    | exact install_slot _ (by decide) _ _ 0
    | exact install_slot _ (by decide) _ _ 1
    | exact install_slot _ (by decide) _ _ 2
    | exact install_slot _ (by decide) _ _ 3
    | exact install_other _ _ _ _ (by decide)

theorem shift_run (w offset b scratch degree target C : Nat) (nonzero guard : Bool)
    (hfit : offset+b<2^w) (hC : 2*w+1≤C) :
    Step shift (12*w+14) (fun _=>0) (data w offset b scratch degree target C nonzero guard)
      (fun _=>0) (data w offset b (CloseoutRowsModeShift.top w offset b) degree target C
        (decide (offset+b≠0)) (guard&&((offset+b-1).choose b%2==1))):=by
  have h:=(CloseoutRowsModeShift.shift_run w offset b scratch C nonzero guard hfit hC).embed
    (fun _ : Fin 2=>0) (extra w degree target)
  exact (h.congr_in (by funext i;fin_cases i <;> rfl) rfl).congr
    (by funext i;fin_cases i <;> rfl) rfl

theorem guard_run (w offset b scratch degree target C : Nat) (nonzero guard : Bool)
    (hfit : offset+b<2^w) (hd : degree<2^w) (ht : target<2^w) (hC : 2*w+1≤C) :
    Step machine (16*w+21) (fun _=>0) (data w offset b scratch degree target C nonzero guard)
      (fun _=>0) (data w offset b (CloseoutRowsModeShift.top w offset b) degree target C
        (decide (offset+b≠0)) ((degree.choose target%2==1)&&((offset+b-1).choose b%2==1))):=by
  have whole:=((init_run w offset b scratch degree target C nonzero guard).seq
    (parity_run w offset b scratch degree target C nonzero hd ht hC)).seq
    (shift_run w offset b scratch degree target C nonzero (degree.choose target%2==1) hfit hC)
  have time:(1+1+(4*w+4))+1+(12*w+14)=16*w+21:=by omega
  rw [time] at whole
  exact whole

end NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowGuard
