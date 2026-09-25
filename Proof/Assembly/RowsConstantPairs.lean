import Proof.Assembly.RowsConstantLoops

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ45bee56da9f34d5a_Constants
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary RecoveryExecution

def nShift (H : Fin 4 → Nat) (k : Nat) := fun i=>H i+if i=1 then k else 0

theorem n_first (source : Fin 4 → List Bool) (H : Fin 4 → Nat)
    (out : Fin 11 → List Bool) (b : Bool) (hb : readTapeBit (source 1) (H 1)=b) :
    step raw (cfg 171 source H out)=some (cfg (if b then 228 else 342) source H out) := by
  have key : ∀ bits : Fin 15 → Bool, raw.rule 171 bits=
      some (jump (if bits (Fin.castAdd 11 1) then 228 else 342)) := by
    intro bits
    rfl
  have hs : (cfg 171 source H out).scanned (Fin.castAdd 11 1)=b := by
    simp only [Configuration.scanned,cfg,Fin.addCases_left]
    exact hb
  change (raw.rule 171 _).map _=_
  rw [key,hs,Option.map_some]
  congr 1
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (m:=4) (n:=11) (fun j=>?_) (fun j=>?_) i <;>
      simp [applyAction,cfg,jump,HeadMove.apply]
  · rfl

theorem n_second (source : Fin 4 → List Bool) (H : Fin 4 → Nat)
    (out : Fin 11 → List Bool) (b : Bool) (hb : readTapeBit (source 1) (H 1)=b) :
    step raw (cfg 285 source H out)=
      some (cfg (if b then 171 else 399) source (if b then nShift H 1 else H) out) := by
  have key : ∀ bits : Fin 15 → Bool, raw.rule 285 bits=
      some (if bits (Fin.castAdd 11 1) then jump 171 ![.stay,.right,.stay,.stay] else jump 399) := by
    intro bits
    rfl
  have hs : (cfg 285 source H out).scanned (Fin.castAdd 11 1)=b := by
    simp only [Configuration.scanned,cfg,Fin.addCases_left]
    exact hb
  change (raw.rule 285 _).map _=_
  rw [key,hs,Option.map_some]
  congr 1
  cases b
  · apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=4) (n:=11) (fun j=>?_) (fun j=>?_) i <;>
        simp [applyAction,cfg,jump,HeadMove.apply]
    · rfl
  · apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=4) (n:=11) (fun j=>?_) (fun j=>?_) i
      · simp only [↓reduceIte,applyAction,cfg,jump,Fin.addCases_left]
        fin_cases j <;> simp [nShift,HeadMove.apply]
      · simp [applyAction,cfg,jump,HeadMove.apply]
    · rfl

theorem n_chunk (source : Fin 4 → List Bool) (H : Fin 4 → Nat)
    (out : Fin 11 → List Bool) :
    Timed raw 16 (cfg 228 source H out)
      (cfg 285 source (nShift H 1) (fun i=>out i++blocks 4 i)) := by
  have path:=chunk (4 : Fin 13) (by simp [Emits]) source H out
  have hm : moved H (4 : Fin 13).val true=nShift H 1 := by
    funext i;fin_cases i <;> simp [moved,sourceMove,nShift,HeadMove.apply]
  rw [hm] at path
  exact path

theorem nShift_add (H : Fin 4 → Nat) (a b : Nat) : nShift (nShift H a) b=nShift H (a+b) := by
  funext i
  by_cases h : i=1 <;> simp [nShift,h,Nat.add_assoc]

theorem n_pair (source : Fin 4 → List Bool) (H : Fin 4 → Nat)
    (out : Fin 11 → List Bool)
    (h0 : readTapeBit (source 1) (H 1)=true)
    (h1 : readTapeBit (source 1) (H 1+1)=true) :
    Timed raw 18 (cfg 171 source H out)
      (cfg 171 source (nShift H 2) (fun i=>out i++blocks 4 i)) := by
  have hfirst:=n_first source H out true h0
  have hchunk:=n_chunk source H out
  have hsecond:=n_second source (nShift H 1) (fun i=>out i++blocks 4 i) true
    (by simpa only [nShift,↓reduceIte] using h1)
  simp only [↓reduceIte] at hfirst hsecond
  rw [nShift_add] at hsecond
  exact ((Timed.single (by rfl) hfirst).trans hchunk).trans (Timed.single (by rfl) hsecond)

theorem n_pairs (source : Fin 4 → List Bool) (H : Fin 4 → Nat)
    (out : Fin 11 → List Bool) (pairs remaining k : Nat)
    (read : ∀ j<2*pairs,readTapeBit (source 1) (H 1+j)=true) (hk : k+remaining=pairs) :
    Timed raw (18*remaining)
      (cfg 171 source (nShift H (2*k)) (appendedMany out 4 k))
      (cfg 171 source (nShift H (2*pairs)) (appendedMany out 4 pairs)) := by
  induction remaining generalizing k with
  | zero =>
    have he : k=pairs := by omega
    subst k
    exact Timed.refl _ _
  | succ remaining ih =>
    have hp:=n_pair source (nShift H (2*k)) (appendedMany out 4 k)
      (by simpa only [nShift,↓reduceIte] using read (2*k) (by omega))
      (by simpa only [nShift,↓reduceIte,Nat.add_assoc] using read (2*k+1) (by omega))
    rw [nShift_add,show 2*k+2=2*(k+1) by omega,appendedMany_next] at hp
    have path:=hp.trans (ih (k+1) (by omega))
    have ht : 18+18*remaining=18*(remaining+1) := by omega
    rw [ht] at path
    exact path

def parityPhase (b : Bool) : Fin 13 := if b then 7 else 6

theorem parity_chunk (source : Fin 4 → List Bool) (H : Fin 4 → Nat)
    (out : Fin 11 → List Bool) (b : Bool) :
    Timed raw 3 (cfg (if b then 399 else 342) source H out)
      (cfg 456 source (shift H 1 1) (fun i=>out i++blocks (parityPhase b).val i)) := by
  have he : Emits (parityPhase b) := by cases b <;> simp [parityPhase,Emits]
  have path:=chunk (parityPhase b) he source H out
  have hm : moved H (parityPhase b).val true=shift H 1 1 := by
    funext i;cases b <;> fin_cases i <;>
      simp [parityPhase,moved,sourceMove,shift,passDriver,HeadMove.apply]
  rw [hm] at path
  cases b <;> exact path

theorem n_tail (source : Fin 4 → List Bool) (H : Fin 4 → Nat)
    (out : Fin 11 → List Bool) (b : Bool)
    (read : ∀ j≤b.toNat,readTapeBit (source 1) (H 1+j)=decide (j<b.toNat)) :
    Timed raw (17*b.toNat+4) (cfg 171 source H out)
      (cfg 456 source (shift (nShift H b.toNat) 1 1)
        (fun i=>appendedMany out 4 b.toNat i++blocks (parityPhase b).val i)) := by
  cases b with
  | false =>
    have hr : readTapeBit (source 1) (H 1)=false := by simpa using read 0 (by decide)
    have hfirst:=n_first source H out false hr
    have hp:=parity_chunk source H out false
    have path:=(Timed.single (by rfl) hfirst).trans hp
    have head0 : nShift H 0=H := by funext i;simp [nShift]
    have out0 : appendedMany out 4 0=out := by funext i;simp [appendedMany]
    simp only [Bool.toNat_false,head0,out0,Nat.mul_zero,Nat.zero_add]
    exact path
  | true =>
    have hr0 : readTapeBit (source 1) (H 1)=true := by simpa using read 0 (by decide)
    have hr1 : readTapeBit (source 1) (H 1+1)=false := by simpa using read 1 (by decide)
    have hfirst:=n_first source H out true hr0
    have hchunk:=n_chunk source H out
    have hsecond:=n_second source (nShift H 1) (fun i=>out i++blocks 4 i) false
      (by simpa only [nShift,↓reduceIte] using hr1)
    have hp:=parity_chunk source (nShift H 1) (fun i=>out i++blocks 4 i) true
    have path:=(((Timed.single (by rfl) hfirst).trans hchunk).trans
      (Timed.single (by rfl) hsecond)).trans hp
    simpa only [Bool.toNat_true,appendedMany,repeatWord_succ,repeatWord_zero,List.append_nil] using path

theorem appendedMany_add (out : Fin 11 → List Bool) (phase a b : Nat) :
    appendedMany (appendedMany out phase a) phase b=appendedMany out phase (a+b) := by
  funext i
  simp only [appendedMany,repeatWord,List.replicate_add,List.flatten_append,List.append_assoc]

theorem n_run (source : Fin 4 → List Bool) (H : Fin 4 → Nat)
    (out : Fin 11 → List Bool) (n : Nat)
    (read : ∀ j≤n,readTapeBit (source 1) (H 1+j)=decide (j<n)) :
    Timed raw (n+16*((n+1)/2)+4) (cfg 171 source H out)
      (cfg 456 source (shift (nShift H n) 1 1)
        (fun i=>appendedMany out 4 ((n+1)/2) i++
          blocks (if n%2=1 then 7 else 6) i)) := by
  let b : Bool := decide (n%2=1)
  have hb : b.toNat=n%2 := by
    dsimp [b]
    by_cases h : n%2=1
    · simp [h]
    · simp [h]
      omega
  have hn : 2*(n/2)+b.toNat=n := by omega
  have hd : n/2+b.toNat=(n+1)/2 := by omega
  have head0 : nShift H 0=H := by funext i;simp [nShift]
  have out0 : appendedMany out 4 0=out := by funext i;simp [appendedMany]
  have pairs:=n_pairs source H out (n/2) (n/2) 0
    (by intro j hj;have hr:=read j (by omega);simpa [show j<n by omega] using hr) (by omega)
  simp only [Nat.mul_zero,head0,out0] at pairs
  have tail:=n_tail source (nShift H (2*(n/2))) (appendedMany out 4 (n/2)) b (by
    intro j hj
    have hr:=read (2*(n/2)+j) (by omega)
    have he : (2*(n/2)+j<n) ↔ j<b.toNat := by omega
    simpa only [nShift,↓reduceIte,Nat.add_assoc,he] using hr)
  have path:=pairs.trans tail
  rw [nShift_add,hn] at path
  have outEq : (fun i=>appendedMany (appendedMany out 4 (n/2)) 4 b.toNat i++
      blocks (parityPhase b).val i)=
      (fun i=>appendedMany out 4 ((n+1)/2) i++blocks (if n%2=1 then 7 else 6) i) := by
    rw [appendedMany_add,hd]
    funext i
    by_cases h : n%2=1 <;> simp [parityPhase,b,h]
  rw [outEq] at path
  have ht : 18*(n/2)+(17*b.toNat+4)=n+16*((n+1)/2)+4 := by omega
  rw [ht] at path
  exact path


end PCJ45bee56da9f34d5a_Constants
