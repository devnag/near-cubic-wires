import Proof.Assembly.RowsConstantWords
import Proof.MachineModel.BlockUnaryCalc
import Proof.Rows.CapReader

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace RowsInit
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
noncomputable section

/-! ## 1. A masked reset from an EMPTY log (every selected head ends at `0`) -/

theorem mask_empty {t s : Nat} {p : Machine t s} {n : Nat} {hin hout : Fin t → Nat}
    {tin tout : Fin t → List Bool} (h : Step p n hin tin hout tout) (selected : Fin t → Bool)
    (hstart : ∀ i,selected i=true → hin i=0) :
    ∃ k,k ≤ n ∧ Step (MaskedReset.machine p selected) (2*n+2)
      (Fin.addCases hin (fun _ : Fin 1=>0)) (Fin.addCases tin (fun _ : Fin 1=>[]))
      (Fin.addCases (fun i=>if selected i then 0 else hout i) (fun _ : Fin 1=>0))
      (Fin.addCases tout (fun _ : Fin 1=>List.replicate k false)) := by
  obtain ⟨r,hr,hh,ht,hs⟩ := h
  have hhead : ∀ i,selected i=true → r.final.heads i ≤ r.steps := by
    intro i hi
    have h := SelectiveReset.prefix_head (prefix_of_run p n _ r hr).1 i
    change r.final.heads i ≤ hin i+r.steps at h
    rw [hstart i hi,Nat.zero_add] at h
    exact h
  obtain ⟨res,hres,hfinal,hsteps,_⟩ := MaskedReset.reset_run p selected n _ r hr hhead
  have hentry : Rewind.recording (⟨p.start,hin,tin⟩ : Configuration t s) 0=
      (⟨(MaskedReset.machine p selected).start,Fin.addCases hin (fun _ : Fin 1=>0),
        Fin.addCases tin (fun _ : Fin 1=>[])⟩ : Configuration (t+1) (s+2)) := by
    apply configuration_ext
    · rfl
    · rfl
    · rfl
  rw [hentry] at hres
  have hfuel : 2*r.steps+2 ≤ 2*n+2 := by omega
  have hmore := runFrom_moreFuel (MaskedReset.machine p selected) (2*r.steps+2)
    (2*n+2-(2*r.steps+2)) _ res hres
  rw [Nat.add_sub_of_le hfuel] at hmore
  refine ⟨r.steps,hs,res,hmore,?_,?_,by omega⟩
  · rw [hfinal]
    funext i
    refine Fin.addCases (m:=t) (n:=1) (fun j=>?_) (fun j=>?_) i
    · simp only [SelectiveReset.finished,Rewind.config,Fin.addCases_left,hh]
    · simp only [SelectiveReset.finished,Rewind.config,Fin.addCases_right]
  · rw [hfinal]
    funext i
    refine Fin.addCases (m:=t) (n:=1) (fun j=>?_) (fun j=>?_) i
    · simp only [SelectiveReset.finished,Rewind.config,Fin.addCases_left,ht]
    · simp only [SelectiveReset.finished,Rewind.config,Fin.addCases_right]

/-! ## 2. Skipping one natural field (its value is never expanded) -/

/-- Skip `natWord n` at the source cursor `pre.length`; scratch `backing` receives the width
template (overlaid), the output tape is untouched. -/
theorem skip_step (pre tail backing : List Bool) (n : Nat) :
    Step (PCPPQueryField.machine false) (2*natBitLength n+3)
      ![pre.length,0,0] ![pre++natWord n++tail,backing,[]]
      ![pre.length+2*natBitLength n+1,0,0]
      ![pre++natWord n++tail,StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength n)) backing,[]] := by
  obtain ⟨r,hr,hf,hs⟩ := PCPPQueryField.nat_run false pre tail backing [] n
  refine Step.of_run hr ?_ ?_
  · rw [hf]
    rfl
  · rw [hf]
    rfl

/-! ## 3. Reading one natural field into unary -/

/-- The compiled cap reader, with its outputs named: `1^n` on local ports 8 and 9, the template
`UnaryTemplate.tape n` on port 10 (head 1), the source kept with its cursor after the field. -/
theorem read_step (pre suffix : List Bool) (n : Nat) :
    ∃ H A,Step PCJ45bee56da9f34d5a_CapReader.machine (8*n+20*natBitLength n+17)
      (PCJ45bee56da9f34d5a_CapReader.initialHeads pre.length)
      (PCJ45bee56da9f34d5a_CapReader.initialBank (pre++natWord n++suffix)) H A ∧
      A 0=pre++natWord n++suffix ∧ H 0=pre.length+2*natBitLength n+1 ∧
      A 8=List.replicate n true ∧ H 8=0 ∧ A 9=List.replicate n true ∧ H 9=0 ∧
      A 10=UnaryTemplate.tape n ∧ H 10=1 := by
  obtain ⟨H,A,h,f⟩ := PCJ45bee56da9f34d5a_CapReader.natural_run pre suffix n
  exact ⟨H,A,h,f⟩

/-! ## 4. The stages docked on the 61-port local caps bank -/

def skipSlots : Fin 3 → Fin 61 := ![0,1,2]
def readSlots (b : Fin 52) : Fin 11 → Fin 61 :=
  fun i=>if h : i.val=0 then 0 else ⟨b.val+i.val-1,by have := b.isLt; have := i.isLt; omega⟩
def sumSlots (a b c d : Fin 61) : Fin 4 → Fin 61 := ![a,b,c,d]
def eraseSlots (d l : Fin 61) : Fin (0+1+1) → Fin 61 := ![d,l]

theorem skipSlots_injective : Function.Injective skipSlots := by decide

theorem readSlots_val (b : Fin 52) (i : Fin 11) :
    (readSlots b i).val=if i.val=0 then 0 else b.val+i.val-1 := by
  unfold readSlots
  split_ifs <;> rfl

theorem readSlots_injective (b : Fin 52) (hb : 1 ≤ b.val) : Function.Injective (readSlots b) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [readSlots_val,readSlots_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem sumSlots_injective (a b c d : Fin 61) (hab : a≠b) (hac : a≠c) (had : a≠d) (hbc : b≠c)
    (hbd : b≠d) (hcd : c≠d) : Function.Injective (sumSlots a b c d) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp [sumSlots] at h; tauto)

theorem eraseSlots_injective (d l : Fin 61) (hdl : d≠l) : Function.Injective (eraseSlots d l) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp [eraseSlots] at h; tauto)

theorem natWord_length (n : Nat) : (natWord n).length=2*natBitLength n+1 := by
  rw [WilliamsInputHeader.natWord_eq]
  simp [SignedSortKey.binary_length]
  omega

theorem pos_eq (pre : List Bool) (n : Nat) :
    pre.length+2*natBitLength n+1=(pre++natWord n).length := by
  rw [List.length_append,natWord_length]
  omega

def skipStage := RecoveryFocus.machine skipSlots (PCPPQueryField.machine false)
def readStage (b : Fin 52) := RecoveryFocus.machine (readSlots b) PCJ45bee56da9f34d5a_CapReader.machine
def sumStage (a b c d : Fin 61) := RecoveryFocus.machine (sumSlots a b c d) ClockUnarySum.machine
def eraseStage (d l : Fin 61) := RecoveryFocus.machine (eraseSlots d l) (RecoveryScratchErase.resetMachine 0)

theorem skip_dock (pre tail backing : List Bool) (n : Nat) (H : Fin 61 → Nat) (A : Fin 61 → List Bool)
    (h0 : H 0=pre.length) (h1 : H 1=0) (h2 : H 2=0)
    (a0 : A 0=pre++natWord n++tail) (a1 : A 1=backing) (a2 : A 2=[]) :
    Step skipStage (2*natBitLength n+3) H A (Function.update H 0 (pre++natWord n).length)
      (Function.update A 1
        (StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength n)) backing)) := by
  classical
  rw [←pos_eq]
  have d := (skip_step pre tail backing n).dock skipSlots skipSlots_injective H A
    (fun i=>by fin_cases i; exacts [h0,h1,h2]) (fun i=>by fin_cases i; exacts [a0,a1,a2])
  have hout : ∀ x : Fin 61,x≠0 → x≠1 → x≠2 → ∀ i,skipSlots i≠x := by
    intro x h0' h1' h2' i he
    fin_cases i
    · exact h0' he.symm
    · exact h1' he.symm
    · exact h2' he.symm
  refine d.congr ?_ ?_
  · funext x
    by_cases hx0 : x=0
    · subst hx0
      rw [Function.update_self]
      exact dockH_slot _ skipSlots_injective _ _ 0
    · rw [Function.update_of_ne hx0]
      by_cases hx1 : x=1
      · subst hx1
        exact (dockH_slot _ skipSlots_injective _ _ 1).trans h1.symm
      · by_cases hx2 : x=2
        · subst hx2
          exact (dockH_slot _ skipSlots_injective _ _ 2).trans h2.symm
        · exact dockH_other _ _ _ _ (hout x hx0 hx1 hx2)
  · funext x
    by_cases hx1 : x=1
    · subst hx1
      rw [Function.update_self]
      exact install_slot _ skipSlots_injective _ _ 1
    · rw [Function.update_of_ne hx1]
      by_cases hx0 : x=0
      · subst hx0
        exact (install_slot _ skipSlots_injective _ _ 0).trans a0.symm
      · by_cases hx2 : x=2
        · subst hx2
          exact (install_slot _ skipSlots_injective _ _ 2).trans a2.symm
        · exact install_other _ _ _ _ (hout x hx0 hx1 hx2)

theorem read_dock (b : Fin 52) (hb : 1 ≤ b.val) (pre suffix : List Bool) (n : Nat)
    (H : Fin 61 → Nat) (A : Fin 61 → List Bool)
    (h0 : H 0=pre.length) (hz : ∀ i : Fin 11,i≠0 → H (readSlots b i)=0)
    (a0 : A 0=pre++natWord n++suffix) (ae : ∀ i : Fin 11,i≠0 → A (readSlots b i)=[]) :
    ∃ H' A',Step (readStage b) (8*n+20*natBitLength n+17) H A H' A' ∧
      (∀ x,(∀ i,readSlots b i≠x) → H' x=H x ∧ A' x=A x) ∧
      A' 0=pre++natWord n++suffix ∧ H' 0=(pre++natWord n).length ∧
      A' (readSlots b 8)=List.replicate n true ∧ H' (readSlots b 8)=0 ∧
      A' (readSlots b 9)=List.replicate n true ∧ H' (readSlots b 9)=0 ∧
      A' (readSlots b 10)=UnaryTemplate.tape n ∧ H' (readSlots b 10)=1 := by
  classical
  have hi := readSlots_injective b hb
  obtain ⟨Hl,Al,h,f0,g0,f8,g8,f9,g9,f10,g10⟩ := read_step pre suffix n
  have d := h.dock (readSlots b) hi H A
    (by
      intro i
      by_cases h : i=0
      · subst h
        exact h0
      · rw [hz i h]
        simp only [PCJ45bee56da9f34d5a_CapReader.initialHeads]
        fin_cases i <;> first | exact absurd rfl h | rfl)
    (by
      intro i
      by_cases h : i=0
      · subst h
        exact a0
      · rw [ae i h]
        simp only [PCJ45bee56da9f34d5a_CapReader.initialBank]
        fin_cases i <;> first | exact absurd rfl h | rfl)
  have r0 : readSlots b 0=0 := rfl
  refine ⟨_,_,d,fun x hx=>⟨dockH_other _ _ _ _ hx,install_other _ _ _ _ hx⟩,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [←r0,install_slot _ hi,f0]
  · rw [←r0,dockH_slot _ hi,g0,pos_eq]
  · rw [install_slot _ hi,f8]
  · rw [dockH_slot _ hi,g8]
  · rw [install_slot _ hi,f9]
  · rw [dockH_slot _ hi,g9]
  · rw [install_slot _ hi,f10]
  · rw [dockH_slot _ hi,g10]

theorem sum_dock (a b c d : Fin 61) (hinj : Function.Injective (sumSlots a b c d)) (r s : Nat)
    (H : Fin 61 → Nat) (A : Fin 61 → List Bool)
    (ha : H a=0) (hb : H b=0) (hc : H c=0) (hd : H d=0)
    (xa : A a=List.replicate r true) (xb : A b=List.replicate s true) (xc : A c=[]) (xd : A d=[]) :
    Step (sumStage a b c d) (2*(r+s)+6) H A H
      (Function.update (Function.update A c (List.replicate (r+s) true)) d
        (List.replicate (r+s+2) false)) := by
  classical
  have e01 : a≠b := fun h=>absurd (hinj (show sumSlots a b c d 0=sumSlots a b c d 1 from h)) (by decide)
  have e02 : a≠c := fun h=>absurd (hinj (show sumSlots a b c d 0=sumSlots a b c d 2 from h)) (by decide)
  have e03 : a≠d := fun h=>absurd (hinj (show sumSlots a b c d 0=sumSlots a b c d 3 from h)) (by decide)
  have e12 : b≠c := fun h=>absurd (hinj (show sumSlots a b c d 1=sumSlots a b c d 2 from h)) (by decide)
  have e13 : b≠d := fun h=>absurd (hinj (show sumSlots a b c d 1=sumSlots a b c d 3 from h)) (by decide)
  have e23 : c≠d := fun h=>absurd (hinj (show sumSlots a b c d 2=sumSlots a b c d 3 from h)) (by decide)
  have dk := (BlockPlatform.UnaryCalc.sum_step r s).dock (sumSlots a b c d) hinj H A
    (fun i=>by fin_cases i; exacts [ha,hb,hc,hd]) (fun i=>by fin_cases i; exacts [xa,xb,xc,xd])
  refine dk.congr (dockH_existing _ _ _ (fun i=>by fin_cases i; exacts [ha,hb,hc,hd])) ?_
  funext x
  by_cases hxd : x=d
  · subst hxd
    rw [Function.update_self]
    exact install_slot _ hinj _ _ 3
  · rw [Function.update_of_ne hxd]
    by_cases hxc : x=c
    · subst hxc
      rw [Function.update_self]
      exact install_slot _ hinj _ _ 2
    · rw [Function.update_of_ne hxc]
      by_cases hxa : x=a
      · subst hxa
        exact (install_slot _ hinj _ _ 0).trans xa.symm
      · by_cases hxb : x=b
        · subst hxb
          exact (install_slot _ hinj _ _ 1).trans xb.symm
        · refine install_other _ _ _ _ (fun i he=>?_)
          fin_cases i
          · exact hxa he.symm
          · exact hxb he.symm
          · exact hxc he.symm
          · exact hxd he.symm

theorem erase_dock (d l : Fin 61) (hdl : d≠l) (total : Nat) (H : Fin 61 → Nat) (A : Fin 61 → List Bool)
    (hd : H d=0) (hl : H l=0) (xd : A d=List.replicate total true) (xl : A l=[]) :
    Step (eraseStage d l) (2*total+4) H A H (Function.update A l (List.replicate (total+1) false)) := by
  classical
  have hinj := eraseSlots_injective d l hdl
  have ready := Step.of_ready (RecoveryScratchErase.erase_ready (t:=0) total 0 Fin.elim0 (fun i=>Fin.elim0 i))
  have dk := ready.dock (eraseSlots d l) hinj H A
    (fun i=>by fin_cases i; exacts [hd,hl]) (fun i=>by fin_cases i; exacts [xd,xl])
  refine dk.congr (dockH_existing _ _ _ (fun i=>by fin_cases i; exacts [hd,hl])) ?_
  funext x
  by_cases hxl : x=l
  · subst hxl
    rw [Function.update_self]
    refine (install_slot _ hinj _ _ 1).trans ?_
    show List.replicate (max 0 (total+1)) false=_
    rw [Nat.zero_max]
  · rw [Function.update_of_ne hxl]
    by_cases hxd : x=d
    · subst hxd
      exact (install_slot _ hinj _ _ 0).trans xd.symm
    · refine install_other _ _ _ _ (fun i he=>?_)
      fin_cases i
      · exact hxd he.symm
      · exact hxl he.symm

/-! ## 5. The reads phase: three skips, read `C`, skip, read `headerFuel`, `copyCap`, `descriptorReserve` -/

/-- The metadata word of the row public input (as `Entry` unwraps it). -/
def metaWord (w deg C hF cC dR rR : Nat) : List Bool :=
  natListWord [w,deg,C]++natListWord [hF,cC,dR,rR]

theorem metaWord_eq (w deg C hF cC dR rR : Nat) :
    metaWord w deg C hF cC dR rR=natWord 3++natWord w++natWord deg++natWord C++natWord 4++
      natWord hF++natWord cC++natWord dR++natWord rR := by
  simp [metaWord,natListWord,List.append_assoc]

/-- The local entry bank: the metadata word on port 0, all else blank. -/
def capsIn (m : List Bool) : Fin 61 → List Bool := fun i=>if i=0 then m else []

/-- The machine of the reads phase. -/
def readsMachine :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine (Composition.machine (Composition.machine skipStage skipStage) skipStage)
      (readStage 3)) skipStage) (readStage 13)) (readStage 23)) (readStage 33)

def readsCost (w deg C hF cC dR : Nat) : Nat :=
  (2*natBitLength 3+3)+1+(2*natBitLength w+3)+1+(2*natBitLength deg+3)+1+
    (8*C+20*natBitLength C+17)+1+(2*natBitLength 4+3)+1+(8*hF+20*natBitLength hF+17)+1+
    (8*cC+20*natBitLength cC+17)+1+(8*dR+20*natBitLength dR+17)

def Ready8 (m : List Bool) (C hF cC dR : Nat) (K : Fin 61 → Nat) (B : Fin 61 → List Bool) : Prop :=
  B 0=m ∧ (∀ x : Fin 61,43 ≤ x.val → B x=[] ∧ K x=0) ∧
  B 10=List.replicate C true ∧ K 10=0 ∧
  B 20=List.replicate hF true ∧ K 20=0 ∧ B 21=List.replicate hF true ∧ K 21=0 ∧
  B 30=List.replicate cC true ∧ K 30=0 ∧ B 31=List.replicate cC true ∧ K 31=0 ∧
  B 40=List.replicate dR true ∧ K 40=0

theorem readSlots_range (b : Fin 52) (i : Fin 11) (hi : i≠0) :
    b.val ≤ (readSlots b i).val ∧ (readSlots b i).val ≤ b.val+9 := by
  have hv : i.val≠0 := fun h=>hi (Fin.ext h)
  rw [readSlots_val,if_neg hv]
  have := i.isLt
  omega

theorem notin_read (b : Fin 52) (x : Fin 61) (hx0 : x≠0) (hx : x.val<b.val ∨ b.val+9<x.val) :
    ∀ i,readSlots b i≠x := by
  intro i he
  by_cases hi : i=0
  · subst hi
    exact hx0 he.symm
  · have := readSlots_range b i hi
    rw [he] at this
    omega

theorem reads_phase (w deg C hF cC dR rR : Nat) :
    ∃ K B,Step readsMachine (readsCost w deg C hF cC dR) (fun _=>0)
      (capsIn (metaWord w deg C hF cC dR rR)) K B ∧ Ready8 (metaWord w deg C hF cC dR rR) C hF cC dR K B := by
  classical
  have hm := metaWord_eq w deg C hF cC dR rR
  set m := metaWord w deg C hF cC dR rR with hmdef
  have nw := natWord_length
  have hsrc : ∀ (pre tail : List Bool) (x : Nat),m=pre++natWord x++tail → capsIn m 0=pre++natWord x++tail :=
    fun pre tail x h=>by simp [capsIn,h]
  -- skip `natWord 3`
  have s1 := skip_dock [] (natWord w++natWord deg++natWord C++natWord 4++natWord hF++natWord cC++
      natWord dR++natWord rR) [] 3 (fun _=>0) (capsIn m) rfl rfl rfl
    (hsrc _ _ _ (by simp [hm])) rfl rfl
  -- skip `natWord w`
  have s2 := skip_dock (natWord 3) (natWord deg++natWord C++natWord 4++natWord hF++natWord cC++
      natWord dR++natWord rR) (StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength 3)) []) w
    (Function.update (fun _ : Fin 61=>(0:Nat)) 0 ([]++natWord 3).length) (Function.update (capsIn m) 1 (StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength 3)) []))
    (by simp [Function.update_apply]) (by simp [Function.update_apply])
    (by simp [Function.update_apply])
    (by simp [Function.update_apply,capsIn,hm]) (by simp [Function.update_apply])
    (by simp [Function.update_apply,capsIn])
  -- skip `natWord deg`
  have s3 := skip_dock (natWord 3++natWord w) (natWord C++natWord 4++natWord hF++natWord cC++
      natWord dR++natWord rR) (StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength w)) (StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength 3)) [])) deg
    (Function.update (Function.update (fun _ : Fin 61=>(0:Nat)) 0 ([]++natWord 3).length) 0 (natWord 3++natWord w).length) (Function.update (Function.update (capsIn m) 1 (StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength 3)) [])) 1 (StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength w)) (StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength 3)) [])))
    (by simp [Function.update_apply]) (by simp [Function.update_apply])
    (by simp [Function.update_apply])
    (by simp [Function.update_apply,capsIn,hm]) (by simp [Function.update_apply])
    (by simp [Function.update_apply,capsIn])
  -- read `C`
  obtain ⟨K4,B4,r4,f4,a4,h4,o4a,o4b,o4c,o4d,-,-⟩ := read_dock 3 (by decide) (natWord 3++natWord w++natWord deg)
    (natWord 4++natWord hF++natWord cC++natWord dR++natWord rR) C (Function.update (Function.update (Function.update (fun _ : Fin 61=>(0:Nat)) 0 ([]++natWord 3).length) 0 (natWord 3++natWord w).length) 0 (natWord 3++natWord w++natWord deg).length) (Function.update (Function.update (Function.update (capsIn m) 1 (StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength 3)) [])) 1 (StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength w)) (StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength 3)) []))) 1 (StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength deg)) (StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength w)) (StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength 3)) []))))
    (by simp [Function.update_apply])
    (by
      intro i hi
      have := readSlots_range 3 i hi
      have h0 : readSlots 3 i≠0 := fun h=>by rw [h] at this; simp at this
      simp [Function.update_apply,h0])
    (by simp [Function.update_apply,capsIn,hm])
    (by
      intro i hi
      have := readSlots_range 3 i hi
      have h0 : readSlots 3 i≠0 := fun h=>by rw [h] at this; simp at this
      have h1 : readSlots 3 i≠1 := fun h=>by rw [h] at this; simp at this
      simp [Function.update_apply,h0,h1,capsIn])
  -- facts about the first four banks
  have k3z : ∀ x : Fin 61,x≠0 → (Function.update (Function.update (Function.update (fun _ : Fin 61=>(0:Nat)) 0 ([]++natWord 3).length) 0 (natWord 3++natWord w).length) 0 (natWord 3++natWord w++natWord deg).length) x=0 := by
    intro x hx
    simp [Function.update_apply,hx]
  have b3z : ∀ x : Fin 61,x≠0 → x≠1 → (Function.update (Function.update (Function.update (capsIn m) 1 (StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength 3)) [])) 1 (StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength w)) (StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength 3)) []))) 1 (StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength deg)) (StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength w)) (StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength 3)) [])))) x=[] := by
    intro x hx0 hx1
    simp [Function.update_apply,hx0,hx1,capsIn]
  -- skip `natWord 4`
  have s5 := skip_dock (natWord 3++natWord w++natWord deg++natWord C) (natWord hF++natWord cC++natWord dR++natWord rR) (StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength deg)) (StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength w)) (StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength 3)) []))) 4 K4 B4
    (by simp [h4])
    (by rw [(f4 1 (notin_read 3 1 (by decide) (Or.inl (by decide)))).1]; exact k3z 1 (by decide))
    (by rw [(f4 2 (notin_read 3 2 (by decide) (Or.inl (by decide)))).1]; exact k3z 2 (by decide))
    (by rw [a4]; simp)
    (by rw [(f4 1 (notin_read 3 1 (by decide) (Or.inl (by decide)))).2]; simp [Function.update_apply])
    (by rw [(f4 2 (notin_read 3 2 (by decide) (Or.inl (by decide)))).2]; exact b3z 2 (by decide) (by decide))
  -- facts about the banks after skip 4, off the Prepare/skip ports
  have k5 : ∀ x : Fin 61,x≠0 → 12<x.val → (Function.update K4 0 ((natWord 3++natWord w++natWord deg++natWord C)++natWord 4).length) x=0 := by
    intro x hx0 hx
    rw [Function.update_of_ne hx0,(f4 x (notin_read 3 x hx0 (Or.inr hx))).1]
    exact k3z x hx0
  have b5 : ∀ x : Fin 61,x≠0 → 12<x.val → (Function.update B4 1 (StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength 4)) (StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength deg)) (StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength w)) (StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength 3)) []))))) x=[] := by
    intro x hx0 hx
    have hx1 : x≠1 := fun h=>by rw [h] at hx; simp at hx
    rw [Function.update_of_ne hx1,(f4 x (notin_read 3 x hx0 (Or.inr hx))).2]
    exact b3z x hx0 hx1
  -- read `headerFuel`
  obtain ⟨K6,B6,r6,f6,a6,h6,o6a,o6b,o6c,o6d,-,-⟩ := read_dock 13 (by decide) (natWord 3++natWord w++natWord deg++natWord C++natWord 4)
    (natWord cC++natWord dR++natWord rR) hF (Function.update K4 0 ((natWord 3++natWord w++natWord deg++natWord C)++natWord 4).length) (Function.update B4 1 (StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength 4)) (StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength deg)) (StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength w)) (StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength 3)) [])))))
    (by simp)
    (by
      intro i hi
      have := readSlots_range 13 i hi
      have h0 : readSlots 13 i≠0 := fun h=>by rw [h] at this; simp at this
      exact k5 _ h0 (by simp at this; omega))
    (by rw [Function.update_of_ne (by decide),a4]; simp)
    (by
      intro i hi
      have := readSlots_range 13 i hi
      have h0 : readSlots 13 i≠0 := fun h=>by rw [h] at this; simp at this
      exact b5 _ h0 (by simp at this; omega))
  -- read `copyCap`
  obtain ⟨K7,B7,r7,f7,a7,h7,o7a,o7b,o7c,o7d,-,-⟩ := read_dock 23 (by decide) (natWord 3++natWord w++natWord deg++natWord C++natWord 4++natWord hF)
    (natWord dR++natWord rR) cC K6 B6
    (by simp [h6])
    (by
      intro i hi
      have := readSlots_range 23 i hi
      have h0 : readSlots 23 i≠0 := fun h=>by rw [h] at this; simp at this
      rw [(f6 _ (notin_read 13 _ h0 (Or.inr (by simp at this; omega)))).1]
      exact k5 _ h0 (by simp at this; omega))
    (by rw [a6]; simp)
    (by
      intro i hi
      have := readSlots_range 23 i hi
      have h0 : readSlots 23 i≠0 := fun h=>by rw [h] at this; simp at this
      rw [(f6 _ (notin_read 13 _ h0 (Or.inr (by simp at this; omega)))).2]
      exact b5 _ h0 (by simp at this; omega))
  -- read `descriptorReserve`
  obtain ⟨K8,B8,r8,f8,a8,h8,o8a,o8b,-,-,-,-⟩ := read_dock 33 (by decide) (natWord 3++natWord w++natWord deg++natWord C++natWord 4++natWord hF++natWord cC)
    (natWord rR) dR K7 B7
    (by simp [h7])
    (by
      intro i hi
      have := readSlots_range 33 i hi
      have h0 : readSlots 33 i≠0 := fun h=>by rw [h] at this; simp at this
      rw [(f7 _ (notin_read 23 _ h0 (Or.inr (by simp at this; omega)))).1,
        (f6 _ (notin_read 13 _ h0 (Or.inr (by simp at this; omega)))).1]
      exact k5 _ h0 (by simp at this; omega))
    (by rw [a7]; simp)
    (by
      intro i hi
      have := readSlots_range 33 i hi
      have h0 : readSlots 33 i≠0 := fun h=>by rw [h] at this; simp at this
      rw [(f7 _ (notin_read 23 _ h0 (Or.inr (by simp at this; omega)))).2,
        (f6 _ (notin_read 13 _ h0 (Or.inr (by simp at this; omega)))).2]
      exact b5 _ h0 (by simp at this; omega))
  refine ⟨K8,B8,(((((((s1.seq s2).seq s3).seq r4).seq s5).seq r6).seq r7).seq r8),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [a8]
    simp [hm]
  · intro x hx
    have hx0 : x≠0 := fun h=>by rw [h] at hx; simp at hx
    have n8 := notin_read 33 x hx0 (Or.inr (by simp; omega))
    have n7 := notin_read 23 x hx0 (Or.inr (by simp; omega))
    have n6 := notin_read 13 x hx0 (Or.inr (by simp; omega))
    constructor
    · rw [(f8 x n8).2,(f7 x n7).2,(f6 x n6).2]
      exact b5 x hx0 (by omega)
    · rw [(f8 x n8).1,(f7 x n7).1,(f6 x n6).1]
      exact k5 x hx0 (by omega)
  · rw [(f8 10 (notin_read 33 10 (by decide) (Or.inl (by decide)))).2,
      (f7 10 (notin_read 23 10 (by decide) (Or.inl (by decide)))).2,
      (f6 10 (notin_read 13 10 (by decide) (Or.inl (by decide)))).2,Function.update_of_ne (by decide)]
    exact o4a
  · rw [(f8 10 (notin_read 33 10 (by decide) (Or.inl (by decide)))).1,
      (f7 10 (notin_read 23 10 (by decide) (Or.inl (by decide)))).1,
      (f6 10 (notin_read 13 10 (by decide) (Or.inl (by decide)))).1,Function.update_of_ne (by decide)]
    exact o4b
  · rw [(f8 20 (notin_read 33 20 (by decide) (Or.inl (by decide)))).2,
      (f7 20 (notin_read 23 20 (by decide) (Or.inl (by decide)))).2]
    exact o6a
  · rw [(f8 20 (notin_read 33 20 (by decide) (Or.inl (by decide)))).1,
      (f7 20 (notin_read 23 20 (by decide) (Or.inl (by decide)))).1]
    exact o6b
  · rw [(f8 21 (notin_read 33 21 (by decide) (Or.inl (by decide)))).2,
      (f7 21 (notin_read 23 21 (by decide) (Or.inl (by decide)))).2]
    exact o6c
  · rw [(f8 21 (notin_read 33 21 (by decide) (Or.inl (by decide)))).1,
      (f7 21 (notin_read 23 21 (by decide) (Or.inl (by decide)))).1]
    exact o6d
  · rw [(f8 30 (notin_read 33 30 (by decide) (Or.inl (by decide)))).2]
    exact o7a
  · rw [(f8 30 (notin_read 33 30 (by decide) (Or.inl (by decide)))).1]
    exact o7b
  · rw [(f8 31 (notin_read 33 31 (by decide) (Or.inl (by decide)))).2]
    exact o7c
  · rw [(f8 31 (notin_read 33 31 (by decide) (Or.inl (by decide)))).1]
    exact o7d
  · exact o8a
  · exact o8b

/-! ## 6. The sums phase: doublings and Fibonacci sums of the read unaries, two erase logs -/

def sumsMachine := (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (sumStage 20 21 43 44) (eraseStage 43 45)) (sumStage 30 31 46 47)) (sumStage 30 46 48 49)) (sumStage 48 46 50 51)) (sumStage 50 48 52 53)) (sumStage 52 50 54 55)) (sumStage 54 52 56 57)) (sumStage 56 54 58 59)) (eraseStage 30 60))

def sumsCost (hF cC : Nat) : Nat := (2*(hF+hF)+6)+1+(2*(hF+hF)+4)+1+(2*(cC+cC)+6)+1+(2*(cC+(cC+cC))+6)+1+(2*((cC+(cC+cC))+(cC+cC))+6)+1+(2*(((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+6)+1+(2*((((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+((cC+(cC+cC))+(cC+cC)))+6)+1+(2*(((((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+((cC+(cC+cC))+(cC+cC)))+(((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC))))+6)+1+(2*((((((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+((cC+(cC+cC))+(cC+cC)))+(((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC))))+((((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+((cC+(cC+cC))+(cC+cC))))+6)+1+(2*cC+4)

def sumsOut (hF cC : Nat) (B : Fin 61 → List Bool) : Fin 61 → List Bool := (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update B 43 (List.replicate (hF+hF) true)) 44 (List.replicate (hF+hF+2) false)) 45 (List.replicate ((hF+hF)+1) false)) 46 (List.replicate (cC+cC) true)) 47 (List.replicate (cC+cC+2) false)) 48 (List.replicate (cC+(cC+cC)) true)) 49 (List.replicate (cC+(cC+cC)+2) false)) 50 (List.replicate ((cC+(cC+cC))+(cC+cC)) true)) 51 (List.replicate ((cC+(cC+cC))+(cC+cC)+2) false)) 52 (List.replicate (((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC))) true)) 53 (List.replicate (((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC))+2) false)) 54 (List.replicate ((((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+((cC+(cC+cC))+(cC+cC))) true)) 55 (List.replicate ((((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+((cC+(cC+cC))+(cC+cC))+2) false)) 56 (List.replicate (((((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+((cC+(cC+cC))+(cC+cC)))+(((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))) true)) 57 (List.replicate (((((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+((cC+(cC+cC))+(cC+cC)))+(((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+2) false)) 58 (List.replicate ((((((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+((cC+(cC+cC))+(cC+cC)))+(((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC))))+((((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+((cC+(cC+cC))+(cC+cC)))) true)) 59 (List.replicate ((((((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+((cC+(cC+cC))+(cC+cC)))+(((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC))))+((((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+((cC+(cC+cC))+(cC+cC)))+2) false)) 60 (List.replicate (cC+1) false))

theorem sums_phase (m : List Bool) (C hF cC dR : Nat) (K : Fin 61 → Nat) (B : Fin 61 → List Bool)
    (h : Ready8 m C hF cC dR K B) :
    Step sumsMachine (sumsCost hF cC) K B K (sumsOut hF cC B) := by
  obtain ⟨_,hz,_,_,b20,k20,b21,k21,b30,k30,b31,k31,_,_⟩ := h
  have e43 := (hz 43 (by decide)).1
  have z43 := (hz 43 (by decide)).2
  have e44 := (hz 44 (by decide)).1
  have z44 := (hz 44 (by decide)).2
  have e45 := (hz 45 (by decide)).1
  have z45 := (hz 45 (by decide)).2
  have e46 := (hz 46 (by decide)).1
  have z46 := (hz 46 (by decide)).2
  have e47 := (hz 47 (by decide)).1
  have z47 := (hz 47 (by decide)).2
  have e48 := (hz 48 (by decide)).1
  have z48 := (hz 48 (by decide)).2
  have e49 := (hz 49 (by decide)).1
  have z49 := (hz 49 (by decide)).2
  have e50 := (hz 50 (by decide)).1
  have z50 := (hz 50 (by decide)).2
  have e51 := (hz 51 (by decide)).1
  have z51 := (hz 51 (by decide)).2
  have e52 := (hz 52 (by decide)).1
  have z52 := (hz 52 (by decide)).2
  have e53 := (hz 53 (by decide)).1
  have z53 := (hz 53 (by decide)).2
  have e54 := (hz 54 (by decide)).1
  have z54 := (hz 54 (by decide)).2
  have e55 := (hz 55 (by decide)).1
  have z55 := (hz 55 (by decide)).2
  have e56 := (hz 56 (by decide)).1
  have z56 := (hz 56 (by decide)).2
  have e57 := (hz 57 (by decide)).1
  have z57 := (hz 57 (by decide)).2
  have e58 := (hz 58 (by decide)).1
  have z58 := (hz 58 (by decide)).2
  have e59 := (hz 59 (by decide)).1
  have z59 := (hz 59 (by decide)).2
  have e60 := (hz 60 (by decide)).1
  have z60 := (hz 60 (by decide)).2
  have t0 := sum_dock 20 21 43 44 (sumSlots_injective _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hF hF K B
    k20 k21 z43 z44
    (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60]) (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60])
    (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60]) (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60])
  have t1 := erase_dock 43 45 (by decide) (hF+hF) K (Function.update (Function.update B 43 (List.replicate (hF+hF) true)) 44 (List.replicate (hF+hF+2) false)) z43 z45
    (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60]) (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60])
  have t2 := sum_dock 30 31 46 47 (sumSlots_injective _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) cC cC K (Function.update (Function.update (Function.update B 43 (List.replicate (hF+hF) true)) 44 (List.replicate (hF+hF+2) false)) 45 (List.replicate ((hF+hF)+1) false))
    k30 k31 z46 z47
    (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60]) (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60])
    (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60]) (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60])
  have t3 := sum_dock 30 46 48 49 (sumSlots_injective _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) cC (cC+cC) K (Function.update (Function.update (Function.update (Function.update (Function.update B 43 (List.replicate (hF+hF) true)) 44 (List.replicate (hF+hF+2) false)) 45 (List.replicate ((hF+hF)+1) false)) 46 (List.replicate (cC+cC) true)) 47 (List.replicate (cC+cC+2) false))
    k30 z46 z48 z49
    (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60]) (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60])
    (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60]) (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60])
  have t4 := sum_dock 48 46 50 51 (sumSlots_injective _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (cC+(cC+cC)) (cC+cC) K (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update B 43 (List.replicate (hF+hF) true)) 44 (List.replicate (hF+hF+2) false)) 45 (List.replicate ((hF+hF)+1) false)) 46 (List.replicate (cC+cC) true)) 47 (List.replicate (cC+cC+2) false)) 48 (List.replicate (cC+(cC+cC)) true)) 49 (List.replicate (cC+(cC+cC)+2) false))
    z48 z46 z50 z51
    (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60]) (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60])
    (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60]) (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60])
  have t5 := sum_dock 50 48 52 53 (sumSlots_injective _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) ((cC+(cC+cC))+(cC+cC)) (cC+(cC+cC)) K (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update B 43 (List.replicate (hF+hF) true)) 44 (List.replicate (hF+hF+2) false)) 45 (List.replicate ((hF+hF)+1) false)) 46 (List.replicate (cC+cC) true)) 47 (List.replicate (cC+cC+2) false)) 48 (List.replicate (cC+(cC+cC)) true)) 49 (List.replicate (cC+(cC+cC)+2) false)) 50 (List.replicate ((cC+(cC+cC))+(cC+cC)) true)) 51 (List.replicate ((cC+(cC+cC))+(cC+cC)+2) false))
    z50 z48 z52 z53
    (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60]) (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60])
    (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60]) (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60])
  have t6 := sum_dock 52 50 54 55 (sumSlots_injective _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC))) ((cC+(cC+cC))+(cC+cC)) K (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update B 43 (List.replicate (hF+hF) true)) 44 (List.replicate (hF+hF+2) false)) 45 (List.replicate ((hF+hF)+1) false)) 46 (List.replicate (cC+cC) true)) 47 (List.replicate (cC+cC+2) false)) 48 (List.replicate (cC+(cC+cC)) true)) 49 (List.replicate (cC+(cC+cC)+2) false)) 50 (List.replicate ((cC+(cC+cC))+(cC+cC)) true)) 51 (List.replicate ((cC+(cC+cC))+(cC+cC)+2) false)) 52 (List.replicate (((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC))) true)) 53 (List.replicate (((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC))+2) false))
    z52 z50 z54 z55
    (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60]) (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60])
    (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60]) (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60])
  have t7 := sum_dock 54 52 56 57 (sumSlots_injective _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) ((((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+((cC+(cC+cC))+(cC+cC))) (((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC))) K (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update B 43 (List.replicate (hF+hF) true)) 44 (List.replicate (hF+hF+2) false)) 45 (List.replicate ((hF+hF)+1) false)) 46 (List.replicate (cC+cC) true)) 47 (List.replicate (cC+cC+2) false)) 48 (List.replicate (cC+(cC+cC)) true)) 49 (List.replicate (cC+(cC+cC)+2) false)) 50 (List.replicate ((cC+(cC+cC))+(cC+cC)) true)) 51 (List.replicate ((cC+(cC+cC))+(cC+cC)+2) false)) 52 (List.replicate (((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC))) true)) 53 (List.replicate (((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC))+2) false)) 54 (List.replicate ((((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+((cC+(cC+cC))+(cC+cC))) true)) 55 (List.replicate ((((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+((cC+(cC+cC))+(cC+cC))+2) false))
    z54 z52 z56 z57
    (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60]) (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60])
    (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60]) (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60])
  have t8 := sum_dock 56 54 58 59 (sumSlots_injective _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (((((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+((cC+(cC+cC))+(cC+cC)))+(((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))) ((((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+((cC+(cC+cC))+(cC+cC))) K (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update B 43 (List.replicate (hF+hF) true)) 44 (List.replicate (hF+hF+2) false)) 45 (List.replicate ((hF+hF)+1) false)) 46 (List.replicate (cC+cC) true)) 47 (List.replicate (cC+cC+2) false)) 48 (List.replicate (cC+(cC+cC)) true)) 49 (List.replicate (cC+(cC+cC)+2) false)) 50 (List.replicate ((cC+(cC+cC))+(cC+cC)) true)) 51 (List.replicate ((cC+(cC+cC))+(cC+cC)+2) false)) 52 (List.replicate (((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC))) true)) 53 (List.replicate (((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC))+2) false)) 54 (List.replicate ((((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+((cC+(cC+cC))+(cC+cC))) true)) 55 (List.replicate ((((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+((cC+(cC+cC))+(cC+cC))+2) false)) 56 (List.replicate (((((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+((cC+(cC+cC))+(cC+cC)))+(((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))) true)) 57 (List.replicate (((((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+((cC+(cC+cC))+(cC+cC)))+(((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+2) false))
    z56 z54 z58 z59
    (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60]) (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60])
    (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60]) (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60])
  have t9 := erase_dock 30 60 (by decide) cC K (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update B 43 (List.replicate (hF+hF) true)) 44 (List.replicate (hF+hF+2) false)) 45 (List.replicate ((hF+hF)+1) false)) 46 (List.replicate (cC+cC) true)) 47 (List.replicate (cC+cC+2) false)) 48 (List.replicate (cC+(cC+cC)) true)) 49 (List.replicate (cC+(cC+cC)+2) false)) 50 (List.replicate ((cC+(cC+cC))+(cC+cC)) true)) 51 (List.replicate ((cC+(cC+cC))+(cC+cC)+2) false)) 52 (List.replicate (((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC))) true)) 53 (List.replicate (((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC))+2) false)) 54 (List.replicate ((((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+((cC+(cC+cC))+(cC+cC))) true)) 55 (List.replicate ((((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+((cC+(cC+cC))+(cC+cC))+2) false)) 56 (List.replicate (((((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+((cC+(cC+cC))+(cC+cC)))+(((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))) true)) 57 (List.replicate (((((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+((cC+(cC+cC))+(cC+cC)))+(((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+2) false)) 58 (List.replicate ((((((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+((cC+(cC+cC))+(cC+cC)))+(((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC))))+((((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+((cC+(cC+cC))+(cC+cC)))) true)) 59 (List.replicate ((((((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+((cC+(cC+cC))+(cC+cC)))+(((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC))))+((((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+((cC+(cC+cC))+(cC+cC)))+2) false)) k30 z60
    (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60]) (by simp [Function.update_apply,b20,b21,b30,b31,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60])
  exact (((((((((t0.seq t1).seq t2).seq t3).seq t4).seq t5).seq t6).seq t7).seq t8).seq t9)

/-! ## 7. The whole caps pass, all heads returned to `0` -/

def capsChain := Composition.machine readsMachine sumsMachine
/-- **The ONE fixed caps machine** (62 local ports: 61 plus its reset log). -/
def capsMachine := MaskedReset.machine capsChain (fun _=>true)
def capsCost (w deg C hF cC dR : Nat) : Nat := 2*(readsCost w deg C hF cC dR+1+sumsCost hF cC)+2

/-- The counter blank's length `34*copyCap+2`, written as the sums compute it. -/
abbrev ctrLen (cC : Nat) : Nat := ((((((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+((cC+(cC+cC))+(cC+cC)))+(((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC))))+((((cC+(cC+cC))+(cC+cC))+(cC+(cC+cC)))+((cC+(cC+cC))+(cC+cC)))+2)

theorem ctrLen_eq (cC : Nat) : ctrLen cC=34*cC+2 := by
  unfold ctrLen
  omega

/-- **The caps pass.** From the metadata word alone (all other local ports blank, heads `0`), the
fixed `capsMachine` reaches a bank whose named ports hold exactly the resident words, every head
at `0`; the remaining local ports hold the pass's own scratch (existential). -/
theorem caps_run (w deg C hF cC dR rR : Nat) :
    ∃ A : Fin 62 → List Bool,Step capsMachine (capsCost w deg C hF cC dR) (fun _=>0)
        (Fin.addCases (capsIn (metaWord w deg C hF cC dR rR)) (fun _ : Fin 1=>[])) (fun _=>0) A ∧
      A 0=metaWord w deg C hF cC dR rR ∧ A 10=List.replicate C true ∧
      A 30=List.replicate cC true ∧ A 40=List.replicate dR true ∧
      A 43=List.replicate (hF+hF) true ∧ A 45=List.replicate (hF+hF+1) false ∧
      A 49=List.replicate (cC+(cC+cC)+2) false ∧ A 59=List.replicate (ctrLen cC) false ∧
      A 60=List.replicate (cC+1) false := by
  obtain ⟨K,B,hr,hready⟩ := reads_phase w deg C hF cC dR rR
  have hs := sums_phase _ C hF cC dR K B hready
  obtain ⟨b0,hz,b10,-,-,-,-,-,b30,-,-,-,b40,-⟩ := hready
  obtain ⟨k,-,hm⟩ := mask_empty (hr.seq hs) (fun _=>true) (fun _ _=>rfl)
  have hH : Fin.addCases (m:=61) (n:=1) (motive:=fun _=>Nat) (fun _ : Fin 61=>(0:Nat)) (fun _ : Fin 1=>0)=fun _=>0 := by
    funext i
    refine Fin.addCases (m:=61) (n:=1) (fun j=>?_) (fun j=>?_) i
    · simp only [Fin.addCases_left]
    · simp only [Fin.addCases_right]
  have hH' : Fin.addCases (m:=61) (n:=1) (motive:=fun _=>Nat)
      (fun i : Fin 61=>if (fun _ : Fin 61=>true) i then 0 else K i) (fun _ : Fin 1=>0)=fun _=>0 := by
    funext i
    refine Fin.addCases (m:=61) (n:=1) (fun j=>?_) (fun j=>?_) i
    · simp only [Fin.addCases_left,if_true]
    · simp only [Fin.addCases_right]
  rw [hH,hH'] at hm
  refine ⟨_,hm,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · show Fin.addCases (m:=61) (n:=1) (motive:=fun _=>List Bool) (sumsOut hF cC B)
      (fun _ : Fin 1=>List.replicate k false) (Fin.castAdd 1 (0 : Fin 61))=_
    rw [Fin.addCases_left]
    simp [sumsOut,Function.update_apply,b0,b10,b30,b40,(hz 43 (by decide)).1,(hz 45 (by decide)).1,
      (hz 49 (by decide)).1,(hz 59 (by decide)).1,(hz 60 (by decide)).1]
  · show Fin.addCases (m:=61) (n:=1) (motive:=fun _=>List Bool) (sumsOut hF cC B)
      (fun _ : Fin 1=>List.replicate k false) (Fin.castAdd 1 (10 : Fin 61))=_
    rw [Fin.addCases_left]
    simp [sumsOut,Function.update_apply,b0,b10,b30,b40,(hz 43 (by decide)).1,(hz 45 (by decide)).1,
      (hz 49 (by decide)).1,(hz 59 (by decide)).1,(hz 60 (by decide)).1]
  · show Fin.addCases (m:=61) (n:=1) (motive:=fun _=>List Bool) (sumsOut hF cC B)
      (fun _ : Fin 1=>List.replicate k false) (Fin.castAdd 1 (30 : Fin 61))=_
    rw [Fin.addCases_left]
    simp [sumsOut,Function.update_apply,b0,b10,b30,b40,(hz 43 (by decide)).1,(hz 45 (by decide)).1,
      (hz 49 (by decide)).1,(hz 59 (by decide)).1,(hz 60 (by decide)).1]
  · show Fin.addCases (m:=61) (n:=1) (motive:=fun _=>List Bool) (sumsOut hF cC B)
      (fun _ : Fin 1=>List.replicate k false) (Fin.castAdd 1 (40 : Fin 61))=_
    rw [Fin.addCases_left]
    simp [sumsOut,Function.update_apply,b0,b10,b30,b40,(hz 43 (by decide)).1,(hz 45 (by decide)).1,
      (hz 49 (by decide)).1,(hz 59 (by decide)).1,(hz 60 (by decide)).1]
  · show Fin.addCases (m:=61) (n:=1) (motive:=fun _=>List Bool) (sumsOut hF cC B)
      (fun _ : Fin 1=>List.replicate k false) (Fin.castAdd 1 (43 : Fin 61))=_
    rw [Fin.addCases_left]
    simp [sumsOut,Function.update_apply,b0,b10,b30,b40,(hz 43 (by decide)).1,(hz 45 (by decide)).1,
      (hz 49 (by decide)).1,(hz 59 (by decide)).1,(hz 60 (by decide)).1]
  · show Fin.addCases (m:=61) (n:=1) (motive:=fun _=>List Bool) (sumsOut hF cC B)
      (fun _ : Fin 1=>List.replicate k false) (Fin.castAdd 1 (45 : Fin 61))=_
    rw [Fin.addCases_left]
    simp [sumsOut,Function.update_apply,b0,b10,b30,b40,(hz 43 (by decide)).1,(hz 45 (by decide)).1,
      (hz 49 (by decide)).1,(hz 59 (by decide)).1,(hz 60 (by decide)).1]
  · show Fin.addCases (m:=61) (n:=1) (motive:=fun _=>List Bool) (sumsOut hF cC B)
      (fun _ : Fin 1=>List.replicate k false) (Fin.castAdd 1 (49 : Fin 61))=_
    rw [Fin.addCases_left]
    simp [sumsOut,Function.update_apply,b0,b10,b30,b40,(hz 43 (by decide)).1,(hz 45 (by decide)).1,
      (hz 49 (by decide)).1,(hz 59 (by decide)).1,(hz 60 (by decide)).1]
  · show Fin.addCases (m:=61) (n:=1) (motive:=fun _=>List Bool) (sumsOut hF cC B)
      (fun _ : Fin 1=>List.replicate k false) (Fin.castAdd 1 (59 : Fin 61))=_
    rw [Fin.addCases_left]
    simp [sumsOut,Function.update_apply,b0,b10,b30,b40,(hz 43 (by decide)).1,(hz 45 (by decide)).1,
      (hz 49 (by decide)).1,(hz 59 (by decide)).1,(hz 60 (by decide)).1]
  · show Fin.addCases (m:=61) (n:=1) (motive:=fun _=>List Bool) (sumsOut hF cC B)
      (fun _ : Fin 1=>List.replicate k false) (Fin.castAdd 1 (60 : Fin 61))=_
    rw [Fin.addCases_left]
    simp [sumsOut,Function.update_apply,b0,b10,b30,b40,(hz 43 (by decide)).1,(hz 45 (by decide)).1,
      (hz 49 (by decide)).1,(hz 59 (by decide)).1,(hz 60 (by decide)).1]

/-! ## 8. What the words are good for: the row-level capacity premises -/

/-- The caps pass costs linearly in the four expanded caps and the metadata length. -/
theorem capsCost_le (w deg C hF cC dR rR : Nat) :
    capsCost w deg C hF cC dR ≤ 400*(C+hF+cC+dR+(metaWord w deg C hF cC dR rR).length+1) := by
  have hm := congrArg List.length (metaWord_eq w deg C hF cC dR rR)
  simp only [List.length_append,natWord_length] at hm
  unfold capsCost readsCost sumsCost
  omega

/-! ## 9. The caps pass docked at arbitrary ports of a larger bank -/

/-- Docked at an injective port map `slots` of any bank whose `slots` heads are `0`, whose
`slots 0` holds the metadata word and whose other `slots` are blank: exit heads unchanged, and
the named ports hold the resident words. -/
theorem caps_dock {T : Nat} (slots : Fin 62 → Fin T) (hinj : Function.Injective slots)
    (w deg C hF cC dR rR : Nat) (H : Fin T → Nat) (A : Fin T → List Bool)
    (hH : ∀ i,H (slots i)=0) (h0 : A (slots 0)=metaWord w deg C hF cC dR rR)
    (hA : ∀ i,i≠0 → A (slots i)=[]) :
    ∃ B : Fin 62 → List Bool,Step (RecoveryFocus.machine slots capsMachine) (capsCost w deg C hF cC dR)
        H A H (install slots A B) ∧
      B 10=List.replicate C true ∧ B 30=List.replicate cC true ∧ B 40=List.replicate dR true ∧
      B 43=List.replicate (hF+hF) true ∧ B 45=List.replicate (hF+hF+1) false ∧
      B 49=List.replicate (cC+(cC+cC)+2) false ∧ B 59=List.replicate (ctrLen cC) false ∧
      B 60=List.replicate (cC+1) false := by
  obtain ⟨B,run,_,b10,b30,b40,b43,b45,b49,b59,b60⟩ := caps_run w deg C hF cC dR rR
  refine ⟨B,?_,b10,b30,b40,b43,b45,b49,b59,b60⟩
  have d := run.dock slots hinj H A hH (by
    intro i
    refine Fin.addCases (m:=61) (n:=1) (fun j=>?_) (fun j=>?_) i
    · by_cases hj : j=0
      · subst hj
        rw [Fin.addCases_left]
        exact h0
      · rw [Fin.addCases_left,hA _ (fun he=>hj (Fin.castAdd_injective _ _ he))]
        simp [capsIn,hj]
    · rw [Fin.addCases_right,hA _ (fun he=>by
        have hv := congrArg Fin.val he
        simp at hv)])
  exact d.congr (dockH_existing _ _ _ hH) rfl

/-! ## 10. Blank backing: one paid erase over any port family (I7's Frame block, I2's Header reserves) -/

/-- The erase slot map: `t` target ports, then the driver, then the log. -/
def eraseAll {T t : Nat} (ports : Fin t → Fin T) (drvP logP : Fin T) : Fin (t+1+1) → Fin T :=
  Fin.addCases (m:=t+1) (n:=1) (Fin.addCases (m:=t) (n:=1) ports (fun _ : Fin 1=>drvP)) (fun _ : Fin 1=>logP)

theorem eraseAll_injective {T t : Nat} (ports : Fin t → Fin T) (drvP logP : Fin T)
    (hp : Function.Injective ports) (hd : ∀ i,ports i≠drvP) (hl : ∀ i,ports i≠logP) (hdl : drvP≠logP) :
    Function.Injective (eraseAll ports drvP logP) := by
  intro i j h
  revert h
  refine Fin.addCases (m:=t+1) (n:=1) (fun i=>?_) (fun e=>?_) i <;>
    refine Fin.addCases (m:=t+1) (n:=1) (fun j=>?_) (fun f=>?_) j
  · revert i j
    intro i j
    refine Fin.addCases (m:=t) (n:=1) (fun a=>?_) (fun e=>?_) i <;>
      refine Fin.addCases (m:=t) (n:=1) (fun b=>?_) (fun f=>?_) j
    · intro h
      simp only [eraseAll,Fin.addCases_left] at h
      rw [hp h]
    · intro h
      simp only [eraseAll,Fin.addCases_left,Fin.addCases_right] at h
      exact absurd h (hd a)
    · intro h
      simp only [eraseAll,Fin.addCases_left,Fin.addCases_right] at h
      exact absurd h.symm (hd b)
    · intro _
      rw [Subsingleton.elim e f]
  · intro h
    revert h
    refine Fin.addCases (m:=t) (n:=1) (fun a=>?_) (fun e'=>?_) i
    · intro h
      simp only [eraseAll,Fin.addCases_left,Fin.addCases_right] at h
      exact absurd h (hl a)
    · intro h
      simp only [eraseAll,Fin.addCases_left,Fin.addCases_right] at h
      exact absurd h hdl
  · intro h
    revert h
    refine Fin.addCases (m:=t) (n:=1) (fun b=>?_) (fun f'=>?_) j
    · intro h
      simp only [eraseAll,Fin.addCases_left,Fin.addCases_right] at h
      exact absurd h.symm (hl b)
    · intro h
      simp only [eraseAll,Fin.addCases_left,Fin.addCases_right] at h
      exact absurd h.symm hdl
  · intro _
    rw [Subsingleton.elim e f]

/-- **Blank backing.** With a resident driver `1^K` and a log `0^cap`, one fixed erase turns every
target port of length `≤ K` into `0^K`, keeps the driver, and leaves the log `0^(max cap (K+1))`;
every head and every other port is unchanged. -/
theorem backing_step {T t : Nat} (ports : Fin t → Fin T) (drvP logP : Fin T)
    (hinj : Function.Injective (eraseAll ports drvP logP)) (K cap : Nat)
    (H : Fin T → Nat) (A : Fin T → List Bool)
    (hH : ∀ i,H (eraseAll ports drvP logP i)=0) (hlen : ∀ i,(A (ports i)).length ≤ K)
    (hd : A drvP=List.replicate K true) (hl : A logP=List.replicate cap false) :
    Step (RecoveryFocus.machine (eraseAll ports drvP logP) (RecoveryScratchErase.resetMachine t))
      (2*K+4) H A H
      (Function.update (install ports A (fun _=>List.replicate K false)) logP
        (List.replicate (max cap (K+1)) false)) := by
  classical
  have ready := Step.of_ready (RecoveryScratchErase.erase_ready K cap (fun i=>A (ports i)) hlen)
  have dk := ready.dock (eraseAll ports drvP logP) hinj H A hH (by
    intro i
    refine Fin.addCases (m:=t+1) (n:=1) (fun j=>?_) (fun e=>?_) i
    · refine Fin.addCases (m:=t) (n:=1) (fun a=>?_) (fun e=>?_) j
      · simp only [eraseAll,Fin.addCases_left]
      · simp only [eraseAll,Fin.addCases_left,Fin.addCases_right]
        exact hd
    · simp only [eraseAll,Fin.addCases_right]
      exact hl)
  refine dk.congr (dockH_existing _ _ _ hH) ?_
  have hpd : ∀ i,ports i≠logP := by
    intro i he
    have := hinj (show eraseAll ports drvP logP ((i.castAdd 1).castAdd 1)=
      eraseAll ports drvP logP ((0 : Fin 1).natAdd (t+1)) by
        simp only [eraseAll,Fin.addCases_left,Fin.addCases_right]
        exact he)
    have hv := congrArg Fin.val this
    simp at hv
    omega
  have hdl : drvP≠logP := by
    intro he
    have := hinj (show eraseAll ports drvP logP (((0 : Fin 1).natAdd t).castAdd 1)=
      eraseAll ports drvP logP ((0 : Fin 1).natAdd (t+1)) by
        simp only [eraseAll,Fin.addCases_left,Fin.addCases_right]
        exact he)
    have hv := congrArg Fin.val this
    simp at hv
  have hpinj : Function.Injective ports := by
    intro a b he
    have := hinj (show eraseAll ports drvP logP ((a.castAdd 1).castAdd 1)=
      eraseAll ports drvP logP ((b.castAdd 1).castAdd 1) by
        simp only [eraseAll,Fin.addCases_left]
        exact he)
    have hv := congrArg Fin.val this
    simp at hv
    exact Fin.ext hv
  have sl : eraseAll ports drvP logP ((0 : Fin 1).natAdd (t+1))=logP := by
    simp only [eraseAll,Fin.addCases_right]
  have sd : eraseAll ports drvP logP (((0 : Fin 1).natAdd t).castAdd 1)=drvP := by
    simp only [eraseAll,Fin.addCases_left,Fin.addCases_right]
  have sp : ∀ i,eraseAll ports drvP logP ((i.castAdd 1).castAdd 1)=ports i := by
    intro i
    simp only [eraseAll,Fin.addCases_left]
  have il := install_slot _ hinj A (fun i=>Fin.addCases (m:=t+1) (n:=1) (motive:=fun _=>List Bool)
    (fun i=>Fin.addCases (m:=t) (n:=1) (motive:=fun _=>List Bool) (fun _ : Fin t=>List.replicate K false)
      (fun _ : Fin 1=>List.replicate K true) i) (fun _ : Fin 1=>List.replicate (max cap (K+1)) false) i)
  funext x
  by_cases hxl : x=logP
  · rw [hxl,Function.update_self]
    have h := il ((0 : Fin 1).natAdd (t+1))
    rw [sl] at h
    rw [h]
    simp only [Fin.addCases_right]
  · rw [Function.update_of_ne hxl]
    by_cases hxp : ∃ i,ports i=x
    · obtain ⟨i,rfl⟩ := hxp
      rw [install_slot _ hpinj]
      have h := il ((i.castAdd 1).castAdd 1)
      rw [sp i] at h
      rw [h]
      simp only [Fin.addCases_left]
    · rw [install_other _ _ _ _ (fun i he=>hxp ⟨i,he⟩)]
      by_cases hxd : x=drvP
      · rw [hxd]
        have h := il (((0 : Fin 1).natAdd t).castAdd 1)
        rw [sd] at h
        rw [h,hd]
        simp only [Fin.addCases_left,Fin.addCases_right]
      · refine install_other _ _ _ _ (fun i he=>?_)
        revert he
        refine Fin.addCases (m:=t+1) (n:=1) (fun j=>?_) (fun e=>?_) i
        · refine Fin.addCases (m:=t) (n:=1) (fun a=>?_) (fun e=>?_) j
          · intro he
            simp only [eraseAll,Fin.addCases_left] at he
            exact hxp ⟨a,he⟩
          · intro he
            simp only [eraseAll,Fin.addCases_left,Fin.addCases_right] at he
            exact hxd he.symm
        · intro he
          simp only [eraseAll,Fin.addCases_right] at he
          exact hxl he.symm

/-! ## 11. I7: the Frame block backing -/

/-- Payload ports then the copier counter, inside a Frame block of `P` payload ports
(descriptor `P`, counter `P+1`, as `FramingSpec.target/counter`). -/
def pcPorts (P : Nat) : Fin (P+1) → Fin (P+2) :=
  Fin.addCases (m:=P) (n:=1) (fun k=>k.castAdd 2) (fun _ : Fin 1=>(1 : Fin 2).natAdd P)

theorem pcPorts_val (P : Nat) (i : Fin (P+1)) : (pcPorts P i).val=if i.val<P then i.val else P+1 := by
  refine Fin.addCases (m:=P) (n:=1) (fun k=>?_) (fun e=>?_) i
  · simp [pcPorts,Fin.addCases_left,k.isLt]
  · simp [pcPorts,Fin.addCases_right]

theorem pcPorts_injective (P : Nat) : Function.Injective (pcPorts P) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [pcPorts_val,pcPorts_val] at hv
  have := i.isLt
  have := j.isLt
  apply Fin.ext
  split_ifs at hv <;> omega

/-- **I7, the Frame block.** From blank Frame ports (heads `0`), with the resident `copyCap`
pair `drv`/`lg` and a resident `1^descriptorReserve` (plus a blank log port for it), two fixed
erases leave every payload port and the copier counter at `0^copyCap` and the descriptor at
`0^descriptorReserve` (= `pad descriptorReserve []`, the RowState Frame block of row `0`); `drv`
and `lg` are kept, the descriptor log becomes `0^(descriptorReserve+1)`. -/
theorem frame_backing {T P : Nat} (fr : Fin (P+2) → Fin T) (drvP lgP dRP dlogP : Fin T)
    (h1 : Function.Injective (eraseAll (fr ∘ pcPorts P) drvP lgP))
    (h2 : Function.Injective (eraseAll (fun _ : Fin 1=>fr ((0 : Fin 2).natAdd P)) dRP dlogP))
    (hfr : Function.Injective fr) (hdl : ∀ k,fr k≠dlogP) (hlg : ∀ k,fr k≠lgP) (hdr : ∀ k,fr k≠dRP)
    (hdlg : dlogP≠lgP) (hdrv : dRP≠lgP)
    (cC dR : Nat) (H : Fin T → Nat) (A : Fin T → List Bool)
    (hH1 : ∀ i,H (eraseAll (fr ∘ pcPorts P) drvP lgP i)=0)
    (hH2 : ∀ i,H (eraseAll (fun _ : Fin 1=>fr ((0 : Fin 2).natAdd P)) dRP dlogP i)=0)
    (hA : ∀ k,A (fr k)=[]) (hd : A drvP=List.replicate cC true)
    (hl : A lgP=List.replicate (cC+1) false) (hr : A dRP=List.replicate dR true) (hlog : A dlogP=[]) :
    ∃ A',Step (Composition.machine
        (RecoveryFocus.machine (eraseAll (fr ∘ pcPorts P) drvP lgP) (RecoveryScratchErase.resetMachine (P+1)))
        (RecoveryFocus.machine (eraseAll (fun _ : Fin 1=>fr ((0 : Fin 2).natAdd P)) dRP dlogP)
          (RecoveryScratchErase.resetMachine 1)))
      (2*cC+4+1+(2*dR+4)) H A H A' ∧
      (∀ k,A' (fr k)=if k.val=P then List.replicate dR false else List.replicate cC false) ∧
      A' dlogP=List.replicate (dR+1) false ∧
      (∀ x,(∀ k,fr k≠x) → x≠dlogP → A' x=A x) := by
  classical
  have s1 := backing_step (fr ∘ pcPorts P) drvP lgP h1 cC (cC+1) H A hH1
    (fun i=>by simp only [Function.comp_apply,hA,List.length_nil,Nat.zero_le]) hd hl
  set A1 := Function.update (install (fr ∘ pcPorts P) A (fun _=>List.replicate cC false)) lgP
    (List.replicate (max (cC+1) (cC+1)) false) with hA1
  have hpc : Function.Injective (fr ∘ pcPorts P) := hfr.comp (pcPorts_injective P)
  have s2 := backing_step (fun _ : Fin 1=>fr ((0 : Fin 2).natAdd P)) dRP dlogP h2 dR 0 H A1 hH2
    (fun _=>by
      rw [hA1,Function.update_of_ne (hlg _),install_other _ _ _ _ (fun i he=>by
        have := hfr he
        have hv := congrArg Fin.val this
        rw [pcPorts_val] at hv
        simp at hv
        split_ifs at hv <;> omega),hA]
      simp)
    (by
      rw [hA1,Function.update_of_ne hdrv,install_other (fr ∘ pcPorts P) _ _ _ (fun i he=>hdr _ he),hr])
    (by
      rw [hA1,Function.update_of_ne hdlg,install_other (fr ∘ pcPorts P) _ _ _ (fun i he=>hdl _ he),hlog]
      rfl)
  refine ⟨_,s1.seq s2,?_,?_,?_⟩
  · intro k
    rw [Function.update_of_ne (hdl k)]
    refine Fin.addCases (m:=P) (n:=2) (motive:=fun k=>install (fun _ : Fin 1=>fr ((0 : Fin 2).natAdd P)) A1
        (fun _=>List.replicate dR false) (fr k)=if k.val=P then List.replicate dR false
          else List.replicate cC false) (fun j=>?_) (fun e=>?_) k
    · have hj : (Fin.castAdd 2 j).val≠P := by simp; omega
      rw [if_neg hj,install_other _ _ _ _ (fun _ he=>by
          have := hfr he
          have hv := congrArg Fin.val this
          simp at hv
          omega),hA1,Function.update_of_ne (hlg _)]
      have h := install_slot (fr ∘ pcPorts P) hpc A (fun _=>List.replicate cC false) (j.castAdd 1)
      simp only [Function.comp_apply,pcPorts,Fin.addCases_left] at h
      exact h
    · obtain rfl | rfl : e=0 ∨ e=1 := by
        rcases e with ⟨v,hv⟩
        rcases v with _ | _ | v
        · exact Or.inl rfl
        · exact Or.inr rfl
        · omega
      · have h := install_slot (fun _ : Fin 1=>fr ((0 : Fin 2).natAdd P))
          (fun a b _=>Subsingleton.elim a b) A1 (fun _=>List.replicate dR false) 0
        rw [if_pos (by simp)]
        exact h
      · rw [if_neg (by simp),install_other _ _ _ _ (fun _ he=>by
            have := hfr he
            have hv := congrArg Fin.val this
            simp at hv),hA1,Function.update_of_ne (hlg _)]
        have h := install_slot (fr ∘ pcPorts P) hpc A (fun _=>List.replicate cC false) ((0 : Fin 1).natAdd P)
        simp only [Function.comp_apply,pcPorts,Fin.addCases_right] at h
        exact h
  · rw [Function.update_self,Nat.zero_max]
  · intro x hx hxd
    rw [Function.update_of_ne hxd,install_other _ _ _ _ (fun _ he=>hx _ he),hA1]
    by_cases hxl : x=lgP
    · rw [hxl,Function.update_self,hl,Nat.max_self]
    · rw [Function.update_of_ne hxl,install_other (fr ∘ pcPorts P) _ _ _ (fun i he=>hx _ he)]



end
end RowsInit
