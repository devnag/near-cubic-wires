import Proof.Rows.ResidueProductBounds
import Proof.Rows.TopFrameReentry

/-! A reusable physical modular-product emitter. Resident short masters are
copied into the product worker, the computed residue is appended in framed
stream order, and all worker tapes are rewound and erased. The append prefix
is never rescanned and never enters the scratch reserve. -/
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_ResidueScaleCell
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.P1Closure NearCubicWires.ExtIncidence SignedSortKey
noncomputable section

def palette (a b p w : Nat):=PCJ45bee56da9f34d5a_ResidueProductReady.input (2*w+1) a p w (2*w+2)
  (PCJ45bee56da9f34d5a_ResidueProductBounds.resetCap w) (binary w b)
def slot (i : Fin 31) : Fin 65:=(((i.castAdd 1).natAdd 31).castAdd 1).castAdd 1
def clearSlots (i : Fin 33) : Fin 65:=(i.natAdd 31).castAdd 1
theorem slot_inj : Function.Injective slot:=by
  intro i j h;apply Fin.ext;have hv:=congrArg Fin.val h
  simp [slot] at hv;omega
theorem clear_inj : Function.Injective clearSlots:=by
  intro i j h;apply Fin.ext;have hv:=congrArg Fin.val h
  simp [clearSlots] at hv;omega
def choice (i : Fin 31) : Option (Fin 31):=some i
def cold (P : Fin 31→List Bool) (U : Nat) (out : List Bool) : Fin 65→List Bool:=
  Fin.addCases (m:=64) (n:=1) (motive:=fun _=>List Bool) (NativeFanout.reusableInput (m:=31) P U) (fun _=>out)
def warm (P : Fin 31→List Bool) (U : Nat) (out : List Bool) : Fin 65→List Bool:=
  Fin.addCases (m:=64) (n:=1) (motive:=fun _=>List Bool) (NativeFanout.output choice P U) (fun _=>out)
def heads (out : List Bool) (up : Nat) (i : Fin 65):=if i=64 then out.length else if i=55 then up else 0
def fanout:=TapeEmbedding.machine 1 (NativeFanout.machine choice)
def advance:=DecompositionCountPosition.move (fun i : Fin 65=>if i=55 then .right else .stay)
def evaluate:=RecoveryFocus.machine slot PCJ45bee56da9f34d5a_ResidueProductReady.machine
def copySlots : Fin 2→Fin 65:=![50,64]
def append:=RecoveryFocus.machine copySlots CloseoutRowsTouching.FrameStream.machine
def clear:=RecoveryFocus.machine clearSlots (PCJ45bee56da9f34d5a_HeaderRewind.clear 31)
def machine:=Composition.machine (Composition.machine (Composition.machine (Composition.machine fanout advance) evaluate) append) clear

theorem entry (P : Fin 31→List Bool) (U : Nat) (out : List Bool) (i : Fin 31) :
    warm P U out (slot i)=ZeroPadding.pad U (P i):=by
  simp only [warm,slot,NativeFanout.output,Fin.addCases_left,Fin.addCases_right,NativeFanout.word,choice,Option.elim_some]

theorem run (a b p w U : Nat) (out : List Bool) (hp : 0<p) (hpw : 2*p≤2^w)
    (ha : a<2^w) (hb : b<2^w) (hU : 1024*(w+1)^2+2≤U)
    (hP : ∀i,(palette a b p w i).length≤U) :
    Step machine (1024*(w+1)^2+6*U+2*w+19) (heads out 0) (cold (palette a b p w) U out)
      (heads (out++frame (binary w ((a*b)%p))) 0)
      (cold (palette a b p w) U (out++frame (binary w ((a*b)%p)))):=by
  let P:=palette a b p w
  let bits:=binary w ((a*b)%p)
  have bl:bits.length=w:=binary_length _ _
  have hu1:1≤U:=by omega
  have hwu:2*w+1≤U:=by nlinarith
  have first:=(NativeFanout.reusable choice P U hP).embed (fun _ : Fin 1=>out.length) (fun _=>out)
  have first':Step fanout (2*U+4) (heads out 0) (cold P U out) (heads out 0) (warm P U out):=by
    refine (first.congr_in ?_ rfl).congr ?_ rfl
    all_goals funext i;fin_cases i <;>rfl
  obtain ⟨r,hr,hf,_⟩:=DecompositionCountPosition.move_run
    (fun i : Fin 65=>if i=55 then .right else .stay) (heads out 0) (warm P U out)
  have up:=(Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)).congr
    (show _=heads out 1 by funext i;by_cases h55:i=55 <;>by_cases h64:i=64 <;>simp [heads,h55,h64,HeadMove.apply]) rfl
  obtain ⟨result,pr,pword⟩:=PCJ45bee56da9f34d5a_ResidueProductBounds.run_fits a b p w hp hpw ha hb
  have body:=(pr.pad (fun _=>U)).dock slot slot_inj (heads out 1) (warm P U out)
    (by intro i;fin_cases i <;>rfl) (entry P U out)
  let H:=dockH slot (heads out 1) PCJ45bee56da9f34d5a_ResidueProductReady.heads
  let A:=install slot (warm P U out) (fun i=>ZeroPadding.pad U (result i))
  have bhead:H 50=0:=dockH_slot slot slot_inj _ _ 19
  have bout:H 64=out.length:=(dockH_other slot _ _ _ (by
    intro i hi;have hv:=congrArg Fin.val hi;simp [slot] at hv;have:=i.isLt;omega)).trans rfl
  have bword:A 50=ZeroPadding.pad U (frame bits):=
    (install_slot slot slot_inj _ _ 19).trans (congrArg (ZeroPadding.pad U) pword)
  have outword:A 64=out:=(install_other slot _ _ _ (by
    intro i hi;have hv:=congrArg Fin.val hi;simp [slot] at hv;have:=i.isLt;omega)).trans rfl
  obtain ⟨copied,cr,cf,_⟩:=CloseoutRowsTouching.FrameStream.copy_run [] bits [] out
  have cp:Step CloseoutRowsTouching.FrameStream.machine (2*w+1)
      (![0,out.length] : Fin 2→Nat) ![frame bits,out]
      (![2*w+1,out.length+(2*w+1)] : Fin 2→Nat) ![frame bits,out++frame bits]:=by
    have base:=Step.of_run cr (congrArg Configuration.heads cf) (congrArg Configuration.tapes cf)
    simpa only [CloseoutRowsTouching.FrameStream.cfg,List.nil_append,List.append_nil,List.length_nil,
      Nat.zero_add,List.length_append,frame_length,bl] using base
  have emit:=(cp.pad (![U,0] : Fin 2→Nat)).dock copySlots (by decide) H A
    (by intro i;fin_cases i <;>assumption)
    (by intro i;fin_cases i;exact bword;exact outword.trans (ZeroPadding.pad_zero _).symm)
  let H':=dockH copySlots H (![2*w+1,out.length+(2*w+1)] : Fin 2→Nat)
  let A':=install copySlots A (fun i=>ZeroPadding.pad ((![U,0] : Fin 2→Nat) i) ((![frame bits,out++frame bits] : Fin 2→List Bool) i))
  have workHeads:∀i : Fin 31,H' (slot i)≤U:=by
    intro i
    by_cases hi:i=19
    · subst i;exact (dockH_slot copySlots (by decide) _ _ 0).le.trans hwu
    · have hother:∀j,copySlots j≠slot i:=by
        intro j;fin_cases j
        · intro he;apply hi;apply slot_inj;exact he.symm
        · intro he;have hv:=congrArg Fin.val he;simp [slot,copySlots] at hv;have:=i.isLt;omega
      dsimp only [H'];rw [dockH_other copySlots _ _ _ hother]
      dsimp only [H];rw [dockH_slot slot slot_inj]
      fin_cases i <;>simp [PCJ45bee56da9f34d5a_ResidueProductReady.heads,
        PCJ45bee56da9f34d5a_ResidueProduct.heads,Fin.addCases]
      omega
  have workLength:∀i : Fin 31,(A' (slot i)).length≤U:=by
    intro i
    by_cases hi:i=19
    · subst i
      dsimp only [A'];rw [show slot 19=copySlots 0 from rfl,install_slot copySlots (by decide)]
      simp only [Matrix.cons_val_zero,ZeroPadding.pad_length,frame_length,bl];omega
    · have hother:∀j,copySlots j≠slot i:=by
        intro j;fin_cases j
        · intro he;apply hi;apply slot_inj;exact he.symm
        · intro he;have hv:=congrArg Fin.val he;simp [slot,copySlots] at hv;have:=i.isLt;omega
      dsimp only [A'];rw [install_other copySlots _ _ _ hother]
      dsimp only [A];rw [install_slot slot slot_inj,ZeroPadding.pad_length]
      apply max_le le_rfl
      apply LocalSupport.step_fits pr i U (hP i)
      have hh:PCJ45bee56da9f34d5a_ResidueProductReady.heads i≤1:=by
        fin_cases i <;>simp [PCJ45bee56da9f34d5a_ResidueProductReady.heads,
          PCJ45bee56da9f34d5a_ResidueProduct.heads,Fin.addCases]
      omega
  have fresh:=(PCJ45bee56da9f34d5a_HeaderRewind.clear_run 31
    (fun i=>H' (slot i)) (fun i=>A' (slot i)) U workHeads workLength).dock
    clearSlots clear_inj H' A'
    (by intro i;fin_cases i <;>rfl)
    (by intro i;fin_cases i <;>rfl)
  have finished:Step clear (4*U+9) H' A' (heads (out++frame bits) 0) (cold P U (out++frame bits)):=by
    apply fresh.congr
    · funext i
      by_cases hit : (31 ≤ i.val ∧ i.val < 64)
      · let j : Fin 33:=⟨i.val-31,by omega⟩
        have he:clearSlots j=i:=Fin.ext (by simp only [clearSlots,Fin.val_castAdd,Fin.val_natAdd,j];omega)
        rw [←he,dockH_slot clearSlots clear_inj]
        have hi64:i≠64:=by intro h;have hv:=congrArg Fin.val h;change i.val=64 at hv;omega
        simp only [heads,he,hi64,if_false];split <;>rfl
      · rw [dockH_other clearSlots _ _ _ (by
          intro j hj;have hv:=congrArg Fin.val hj;simp [clearSlots] at hv;have:=j.isLt;omega)]
        by_cases hi64:i=64
        · subst i;dsimp only [H'];rw [show (64 : Fin 65)=copySlots 1 from rfl,dockH_slot copySlots (by decide)]
          simp [heads,copySlots,List.length_append,frame_length,bl]
        · have hi31:i.val<31:=by have:=i.isLt;omega
          dsimp only [H'];rw [dockH_other copySlots _ _ _ (by intro j;fin_cases j <;>intro he <;>have:=congrArg Fin.val he <;>simp [copySlots] at this <;>omega)]
          dsimp only [H];rw [dockH_other slot _ _ _ (by intro j hj;have hv:=congrArg Fin.val hj;simp [slot] at hv;omega)]
          have hi55:i≠55:=by intro he;have:=congrArg Fin.val he;simp at this;omega
          simp [heads,hi64,hi55]
    · apply HierarchyAllocation.install_eq clearSlots clear_inj
      · intro i;fin_cases i <;>rfl
      · intro i hi
        have hit:i.val<31 ∨ i=64:=by
          by_contra h;push Not at h
          have hh:i.val<64:=by have:=i.isLt;omega
          exact hi ⟨i.val-31,by omega⟩ (Fin.ext (by simp only [clearSlots,Fin.val_castAdd,Fin.val_natAdd];omega))
        rcases hit with hit|rfl
        · dsimp only [A'];rw [install_other copySlots _ _ _ (by intro j;fin_cases j <;>intro he <;>have:=congrArg Fin.val he <;>simp [copySlots] at this <;>omega)]
          dsimp only [A];rw [install_other slot _ _ _ (by intro j hj;have hv:=congrArg Fin.val hj;simp [slot] at hv;omega)]
          fin_cases i <;>first | rfl | norm_num at hit
        · dsimp only [A'];rw [show (64 : Fin 65)=copySlots 1 from rfl,install_slot copySlots (by decide)]
          change out++frame bits=ZeroPadding.pad 0 (out++frame bits)
          exact (ZeroPadding.pad_zero _).symm
  have total:=(((first'.seq up).seq body).seq emit).seq finished
  unfold machine
  convert total using 1 <;>first | rfl | omega
end
end PCJ45bee56da9f34d5a_ResidueScaleCell
