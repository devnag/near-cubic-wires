import Proof.Rows.VerdictAppend

/-! Copy the actual verdict to the external table and erase the bounded
private bank. The table's existing prefix is outside every cleanup bound. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_VerdictFinish
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.P1Closure
noncomputable section

def bank (A :Fin 254→List Bool) (R :Nat) (out :List Bool):Fin 257→List Bool:=
 Fin.addCases (m:=254) (n:=3) (motive:=fun _=>List Bool) A
  ![List.replicate R true,List.replicate (R+1) false,out]
def heads (H :Fin 254→Nat) (len :Nat):Fin 257→Nat:=
 Fin.addCases (m:=254) (n:=3) (motive:=fun _=>Nat) H ![0,0,len]
def appendSlots:Fin 2→Fin 257:=![253,256]
def append:=RecoveryFocus.machine appendSlots PCJ45bee56da9f34d5a_VerdictAppend.machine
def clear:=TapeEmbedding.machine 1 (PCJ45bee56da9f34d5a_HeaderRewind.clear 254)
def machine:=Composition.machine append clear

theorem out_away (A :Fin 254→List Bool) (R :Nat) (out out' :List Bool) (i :Fin 257) (hi :i≠256):
 bank A R out i=bank A R out' i :=by
 revert hi
 refine Fin.addCases (m:=254) (n:=3) (fun j _=>?_) (fun j hj=>?_) i
 · simp only [bank,Fin.addCases_left]
 · fin_cases j <;>first |rfl |exact False.elim (hj rfl)
theorem head_away (H :Fin 254→Nat) (len len' :Nat) (i :Fin 257) (hi :i≠256):
 heads H len i=heads H len' i :=by
 revert hi
 refine Fin.addCases (m:=254) (n:=3) (fun j _=>?_) (fun j hj=>?_) i
 · simp only [heads,Fin.addCases_left]
 · fin_cases j <;>first |rfl |exact False.elim (hj rfl)

theorem append_run (H :Fin 254→Nat) (A :Fin 254→List Bool) (R :Nat) (out :List Bool) (b :Bool)
 (hhead :H 253=0) (hbit :readTapeBit (A 253) 0=b):
 Step append 1 (heads H out.length) (bank A R out)
  (heads H (out.length+1)) (bank A R (out++[b])) :=by
 have h:=(PCJ45bee56da9f34d5a_VerdictAppend.run (A 253) out b hbit).dock appendSlots (by decide)
  (heads H out.length) (bank A R out)
  (by intro i;fin_cases i;exact hhead;rfl) (by intro i;fin_cases i <;>rfl)
 apply h.congr
 · apply PCJ45bee56da9f34d5a_NativeCircuitCount.dock_heads appendSlots (by decide)
   · intro i;fin_cases i;exact hhead.symm;rfl
   · intro i hi;exact head_away H _ _ i (fun he=>hi 1 he.symm)
 · apply HierarchyAllocation.install_eq appendSlots (by decide)
   · intro i;fin_cases i <;>rfl
   · intro i hi;exact out_away A R _ _ i (fun he=>hi 1 he.symm)

theorem bank_nested (A :Fin 254→List Bool) (R :Nat) (out :List Bool):
 bank A R out=Fin.addCases (m:=256) (n:=1) (motive:=fun _=>List Bool)
  (PCJ45bee56da9f34d5a_Plan.clearInput R (R+1) A) (fun _=>out) :=by
 funext i
 refine Fin.addCases (m:=254) (n:=3) (fun j=>?_) (fun j=>?_) i
 · simp only [bank,Fin.addCases_left]
   change A j=Fin.addCases (m:=256) (n:=1) (motive:=fun _=>List Bool)
    (PCJ45bee56da9f34d5a_Plan.clearInput R (R+1) A) (fun _=>out) (((j.castAdd 1).castAdd 1).castAdd 1)
   simp only [PCJ45bee56da9f34d5a_Plan.clearInput,Fin.addCases_left]
 · fin_cases j <;>rfl

theorem heads_nested (H :Fin 254→Nat) (len :Nat):
 heads H len=Fin.addCases (m:=256) (n:=1) (motive:=fun _=>Nat)
  (Fin.addCases (m:=255) (n:=1) (motive:=fun _=>Nat)
   (Fin.addCases (m:=254) (n:=1) (motive:=fun _=>Nat) H (fun _=>0)) (fun _=>0)) (fun _=>len) :=by
 funext i
 refine Fin.addCases (m:=254) (n:=3) (fun j=>?_) (fun j=>?_) i
 · simp only [heads,Fin.addCases_left]
   change H j=Fin.addCases (m:=256) (n:=1) (motive:=fun _=>Nat)
    (Fin.addCases (m:=255) (n:=1) (motive:=fun _=>Nat)
     (Fin.addCases (m:=254) (n:=1) (motive:=fun _=>Nat) H (fun _=>0)) (fun _=>0)) (fun _=>len)
    (((j.castAdd 1).castAdd 1).castAdd 1)
   simp only [Fin.addCases_left]
 · fin_cases j <;>rfl

theorem clear_run (H :Fin 254→Nat) (A :Fin 254→List Bool) (R :Nat) (out :List Bool)
 (hH :∀i,H i≤R) (hA :∀i,(A i).length≤R):
 Step clear (4*R+9) (heads H out.length) (bank A R out)
  (heads (fun _=>0) out.length) (bank (fun _=>List.replicate R false) R out) :=by
 have h:=(PCJ45bee56da9f34d5a_HeaderRewind.clear_run 254 H A R hH hA).embed
  (fun _ :Fin 1=>out.length) (fun _=>out)
 refine (h.congr_in (heads_nested H out.length).symm (bank_nested A R out).symm).congr ?_ ?_
 · rw [heads_nested]
   funext i
   refine Fin.addCases (m:=256) (n:=1) (fun j=>?_) (fun j=>?_) i
   · simp only [Fin.addCases_left]
     refine Fin.addCases (m:=255) (n:=1) (fun k=>?_) (fun k=>?_) j
     · simp only [Fin.addCases_left]
       refine Fin.addCases (m:=254) (n:=1) (fun _=>?_) (fun _=>?_) k <;>simp only [Fin.addCases_left,Fin.addCases_right]
     · simp only [Fin.addCases_right]
   · simp only [Fin.addCases_right]
 · exact (bank_nested (fun _=>List.replicate R false) R out).symm

theorem run (H :Fin 254→Nat) (A :Fin 254→List Bool) (R :Nat) (out :List Bool) (b :Bool)
 (hhead :H 253=0) (hbit :readTapeBit (A 253) 0=b) (hH :∀i,H i≤R) (hA :∀i,(A i).length≤R):
 Step machine (4*R+11) (heads H out.length) (bank A R out)
  (heads (fun _=>0) (out++[b]).length) (bank (fun _=>List.replicate R false) R (out++[b])) :=by
 have one:=append_run H A R out b hhead hbit
 have two:=clear_run H A R (out++[b]) hH hA
 have len:(out++[b]).length=out.length+1:=by simp
 rw [len] at two
 have all:=one.seq two
 simpa only [machine,len,show 1+1+(4*R+9)=4*R+11 by omega] using all

theorem bounds {s n :Nat} {M :Machine 254 s} {H J :Fin 254→Nat} {A B :Fin 254→List Bool}
 (h:Step M n H A J B) (R :Nat) (hH :∀i,H i≤1) (hA :∀i,(A i).length≤R) (hn :n+2≤R):
 (∀i,J i≤R) ∧ (∀i,(B i).length≤R) :=by
 constructor
 · intro i
   obtain ⟨rec,hr,hh,_,hs⟩:=h
   have hi:=SelectiveReset.prefix_head (prefix_of_run M n _ rec hr).1 i
   rw [hh] at hi
   change J i≤H i+rec.steps at hi
   have h0:=hH i
   omega
 · intro i
   exact LocalSupport.step_fits h i R (hA i) (by have h0:=hH i;omega)
end
end PCJ45bee56da9f34d5a_VerdictFinish
