import Proof.Rows.HeaderErase
import Proof.Rows.RowsInitCaps

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace RowsInit
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.P1Closure
noncomputable section

/-! ## 1. A one-step head bump -/

/-- Move the single head one cell right, write nothing. -/
def bump : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun s=>decide (s=1)
  rule := fun s _=>if s=0 then some ⟨1,fun _=>none,fun _=>.right⟩ else none

theorem bump_run (h : Nat) (t : List Bool) :
    Step bump 1 (fun _=>h) (fun _=>t) (fun _=>h+1) (fun _=>t) := by
  have hs : step bump (⟨bump.start,fun _=>h,fun _=>t⟩ : Configuration 1 2)=
      some ⟨1,fun _=>h+1,fun _=>t⟩ := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i
      rfl
    · rfl
  obtain ⟨r,hr,hf,_⟩ := (Timed.single (by rfl) hs).run rfl
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

/-! ## 2. The 29-port Header-word chain -/

/-- Local entry bank: pool word (0), arity template (1), metadata word (2), all else blank. -/
def hdrIn {k : Nat} (gs : List (ExactThresholdGate k)) (m : List Bool) : Fin 29 → List Bool :=
  fun i=>if i=0 then exactListWord gs else if i=1 then UnaryTemplate.tape k else if i=2 then m else []

theorem hdrIn_blank {k : Nat} (gs : List (ExactThresholdGate k)) (m : List Bool) (x : Fin 29)
    (hx : 3 ≤ x.val) : hdrIn gs m x=[] := by
  have h0 : x≠0 := fun h=>by rw [h] at hx; exact absurd hx (by decide)
  have h1 : x≠1 := fun h=>by rw [h] at hx; exact absurd hx (by decide)
  have h2 : x≠2 := fun h=>by rw [h] at hx; exact absurd hx (by decide)
  simp only [hdrIn,if_neg h0,if_neg h1,if_neg h2]

/-- A: count `N` from the pool word's header (source head rewound to `0`, `tape N` at head `1`). -/
def slotsA : Fin (11+1) → Fin 29 := ![0,3,4,5,6,7,8,9,10,11,12,13]
/-- B: bump the arity template to its sentinel head `1`. -/
def slotsB : Fin 1 → Fin 29 := ![1]
/-- C: the counted scanner: pool, two scratch, arity, `tape N`, the recorded length `1^B` (16). -/
def slotsC : Fin 6 → Fin 29 := ![0,14,15,1,12,16]
/-- D: skip the metadata word's list count. -/
def slotsD : Fin 3 → Fin 29 := ![2,17,18]
/-- E: read `w` into unary (`1^w` on 26). -/
def slotsE : Fin 11 → Fin 29 := ![2,19,20,21,22,23,24,25,26,27,28]
def selA : Fin 11 → Bool := fun i=>decide (i=0)

theorem slotsA_injective : Function.Injective slotsA := by decide
theorem slotsB_injective : Function.Injective slotsB := by decide
theorem slotsC_injective : Function.Injective slotsC := by decide
theorem slotsD_injective : Function.Injective slotsD := by decide
theorem slotsE_injective : Function.Injective slotsE := by decide

def stageA := RecoveryFocus.machine slotsA (MaskedReset.machine PCJ45bee56da9f34d5a_CapReader.machine selA)
def stageB := RecoveryFocus.machine slotsB bump
def stageC := RecoveryFocus.machine slotsC BinaryCacheColdMeasure.scanner
def stageD := RecoveryFocus.machine slotsD (PCPPQueryField.machine false)
def stageE := RecoveryFocus.machine slotsE PCJ45bee56da9f34d5a_CapReader.machine
def hdrChain := Composition.machine (Composition.machine (Composition.machine
  (Composition.machine stageA stageB) stageC) stageD) stageE
/-- **The Header-word pass**: the chain under one masked reset of every head. -/
def hdrMachine := MaskedReset.machine hdrChain (fun _=>true)

def readCost (x : Nat) : Nat := 8*x+20*natBitLength x+17
def chainCost {k : Nat} (gs : List (ExactThresholdGate k)) (w : Nat) : Nat :=
  ((((2*readCost gs.length+2)+1+1)+1+DecompositionCachedChild.budget gs gs.length)+1+
    (2*natBitLength 3+3))+1+readCost w
def hdrCost {k : Nat} (gs : List (ExactThresholdGate k)) (w : Nat) : Nat := 2*chainCost gs w+2

theorem hdr_chain {k : Nat} (gs : List (ExactThresholdGate k)) (w deg C hF cC dR rR : Nat) :
    ∃ H A,Step hdrChain (chainCost gs w) (fun _=>0) (hdrIn gs (metaWord w deg C hF cC dR rR)) H A ∧
      A 0=exactListWord gs ∧ A 1=UnaryTemplate.tape k ∧ A 2=metaWord w deg C hF cC dR rR ∧
      A 12=UnaryTemplate.tape gs.length ∧ A 16=List.replicate (exactListWord gs).length true ∧
      A 26=List.replicate w true := by
  classical
  have hm := metaWord_eq w deg C hF cC dR rR
  set m := metaWord w deg C hF cC dR rR with hmdef
  set H0 : Fin 29 → Nat := fun _=>0 with hH0
  set A0 := hdrIn gs m with hA0
  have e1 : A0 1=UnaryTemplate.tape k := by simp [hA0,hdrIn]
  have e2 : A0 2=m := by simp [hA0,hdrIn]
  -- A: the count
  obtain ⟨HA,AA,rA,fA0,-,-,-,-,-,fA10,gA10⟩ := read_step [] (gs.flatMap exactWord) gs.length
  obtain ⟨kA,-,mA⟩ := mask_empty rA selA (fun i hi=>by
    have hi0 : i=0 := by simpa [selA] using hi
    subst hi0
    rfl)
  have dA := mA.dock slotsA slotsA_injective H0 A0
    (by
      intro j
      refine Fin.addCases (m:=11) (n:=1) (fun i=>?_) (fun i=>?_) j
      · rw [Fin.addCases_left]
        fin_cases i <;> rfl
      · rw [Fin.addCases_right])
    (by
      intro j
      refine Fin.addCases (m:=11) (n:=1) (fun i=>?_) (fun i=>?_) j
      · rw [Fin.addCases_left]
        by_cases hi : i=0
        · subst hi
          show exactListWord gs=_
          rfl
        · have hge : 3 ≤ (slotsA (Fin.castAdd 1 i)).val := by
            revert i
            decide
          rw [hA0,hdrIn_blank gs m _ hge]
          fin_cases i <;> first | exact absurd rfl hi | rfl
      · rw [Fin.addCases_right,hA0,hdrIn_blank gs m _ (by fin_cases i; decide)])
  set HA1 := dockH slotsA H0 (Fin.addCases (fun i=>if selA i then 0 else HA i) (fun _ : Fin 1=>0)) with hHA1
  set AA1 := install slotsA A0 (Fin.addCases AA (fun _ : Fin 1=>List.replicate kA false)) with hAA1
  have oA : ∀ x,(∀ j,slotsA j≠x) → HA1 x=0 ∧ AA1 x=A0 x :=
    fun x hx=>⟨dockH_other _ _ _ _ hx,install_other _ _ _ _ hx⟩
  have a0 : AA1 0=exactListWord gs := by
    show AA1 (slotsA (Fin.castAdd 1 0))=_
    rw [hAA1,install_slot _ slotsA_injective,Fin.addCases_left,fA0]
    rfl
  have h0 : HA1 0=0 := by
    show HA1 (slotsA (Fin.castAdd 1 0))=_
    rw [hHA1,dockH_slot _ slotsA_injective,Fin.addCases_left]
    rfl
  have a12 : AA1 12=UnaryTemplate.tape gs.length := by
    show AA1 (slotsA (Fin.castAdd 1 10))=_
    rw [hAA1,install_slot _ slotsA_injective,Fin.addCases_left,fA10]
  have h12 : HA1 12=1 := by
    show HA1 (slotsA (Fin.castAdd 1 10))=_
    rw [hHA1,dockH_slot _ slotsA_injective,Fin.addCases_left]
    simp [selA,gA10]
  -- B: the arity sentinel
  have dB := (bump_run 0 (UnaryTemplate.tape k)).dock slotsB slotsB_injective HA1 AA1
    (fun j=>by fin_cases j; exact (oA 1 (by decide)).1)
    (fun j=>by fin_cases j; exact (oA 1 (by decide)).2.trans e1)
  set HB := dockH slotsB HA1 (fun _=>0+1) with hHB
  set AB := install slotsB AA1 (fun _=>UnaryTemplate.tape k) with hAB
  have oB : ∀ x,x≠1 → HB x=HA1 x ∧ AB x=AA1 x := by
    intro x hx
    have hs : ∀ j,slotsB j≠x := by
      intro j he
      fin_cases j
      exact hx he.symm
    exact ⟨dockH_other _ _ _ _ hs,install_other _ _ _ _ hs⟩
  have b1 : AB 1=UnaryTemplate.tape k := by
    show AB (slotsB 0)=_
    rw [hAB,install_slot _ slotsB_injective]
  have g1 : HB 1=1 := by
    show HB (slotsB 0)=_
    rw [hHB,dockH_slot _ slotsB_injective]
  have blank : ∀ x : Fin 29,(∀ j,slotsA j≠x) → x≠1 → 3 ≤ x.val → HB x=0 ∧ AB x=[] := by
    intro x hA h1 h3
    rw [(oB x h1).1,(oB x h1).2,(oA x hA).1,(oA x hA).2,hA0,hdrIn_blank gs m x h3]
    exact ⟨rfl,rfl⟩
  -- C: the counted scanner
  obtain ⟨HC0,TC0,rC,c0,c3,c4,c5⟩ := BinaryCacheColdMeasure.scan_run gs
  have dC := rC.dock slotsC slotsC_injective HB AB
    (by
      intro j
      fin_cases j
      · show HB 0=0
        rw [(oB 0 (by decide)).1,h0]
      · exact (blank 14 (by decide) (by decide) (by decide)).1
      · exact (blank 15 (by decide) (by decide) (by decide)).1
      · exact g1
      · show HB 12=1
        rw [(oB 12 (by decide)).1,h12]
      · exact (blank 16 (by decide) (by decide) (by decide)).1)
    (by
      intro j
      fin_cases j
      · show AB 0=exactListWord gs
        rw [(oB 0 (by decide)).2,a0]
      · exact (blank 14 (by decide) (by decide) (by decide)).2
      · exact (blank 15 (by decide) (by decide) (by decide)).2
      · exact b1
      · show AB 12=UnaryTemplate.tape gs.length
        rw [(oB 12 (by decide)).2,a12]
      · exact (blank 16 (by decide) (by decide) (by decide)).2)
  set HC := dockH slotsC HB HC0 with hHC
  set AC := install slotsC AB TC0 with hAC
  have oC : ∀ x,(∀ j,slotsC j≠x) → HC x=HB x ∧ AC x=AB x :=
    fun x hx=>⟨dockH_other _ _ _ _ hx,install_other _ _ _ _ hx⟩
  have cc0 : AC 0=exactListWord gs := by
    show AC (slotsC 0)=_
    rw [hAC,install_slot _ slotsC_injective,c0]
  have cc1 : AC 1=UnaryTemplate.tape k := by
    show AC (slotsC 3)=_
    rw [hAC,install_slot _ slotsC_injective,c3]
  have cc12 : AC 12=UnaryTemplate.tape gs.length := by
    show AC (slotsC 4)=_
    rw [hAC,install_slot _ slotsC_injective,c4]
  have cc16 : AC 16=List.replicate (exactListWord gs).length true := by
    show AC (slotsC 5)=_
    rw [hAC,install_slot _ slotsC_injective,c5]
  have blankC : ∀ x : Fin 29,17 ≤ x.val → HC x=0 ∧ AC x=[] := by
    intro x hx
    have hC : ∀ j,slotsC j≠x := by
      have hs : ∀ j,(slotsC j).val<17 := by decide
      intro j he
      have := hs j
      rw [he] at this
      omega
    have hA : ∀ j,slotsA j≠x := by
      have hs : ∀ j,(slotsA j).val<17 := by decide
      intro j he
      have := hs j
      rw [he] at this
      omega
    have h1 : x≠1 := fun he=>by rw [he] at hx; exact absurd hx (by decide)
    rw [(oC x hC).1,(oC x hC).2]
    exact blank x hA h1 (by omega)
  have c2 : HC 2=0 ∧ AC 2=m := by
    have hC : ∀ j,slotsC j≠2 := by decide
    rw [(oC 2 hC).1,(oC 2 hC).2,(oB 2 (by decide)).1,(oB 2 (by decide)).2,
      (oA 2 (by decide)).1,(oA 2 (by decide)).2,e2]
    exact ⟨rfl,rfl⟩
  -- D: skip the list count `natWord 3`
  have rD := skip_step [] (natWord w++natWord deg++natWord C++natWord 4++natWord hF++natWord cC++
    natWord dR++natWord rR) [] 3
  have dD := rD.dock slotsD slotsD_injective HC AC
    (by
      intro j
      fin_cases j
      · exact c2.1
      · exact (blankC 17 (by decide)).1
      · exact (blankC 18 (by decide)).1)
    (by
      intro j
      fin_cases j
      · show AC 2=[]++natWord 3++(natWord w++natWord deg++natWord C++natWord 4++natWord hF++
          natWord cC++natWord dR++natWord rR)
        rw [c2.2,hm]
        simp only [List.nil_append,List.append_assoc]
      · exact (blankC 17 (by decide)).2
      · exact (blankC 18 (by decide)).2)
  set HD := dockH slotsD HC ![([] : List Bool).length+2*natBitLength 3+1,0,0] with hHD
  set AD := install slotsD AC ![[]++natWord 3++(natWord w++natWord deg++natWord C++natWord 4++
    natWord hF++natWord cC++natWord dR++natWord rR),
    StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength 3)) [],[]] with hAD
  have oD : ∀ x,(∀ j,slotsD j≠x) → HD x=HC x ∧ AD x=AC x :=
    fun x hx=>⟨dockH_other _ _ _ _ hx,install_other _ _ _ _ hx⟩
  have blankD : ∀ x : Fin 29,19 ≤ x.val → HD x=0 ∧ AD x=[] := by
    intro x hx
    have hD : ∀ j,slotsD j≠x := by
      have hs : ∀ j,(slotsD j).val<19 := by decide
      intro j he
      have := hs j
      rw [he] at this
      omega
    rw [(oD x hD).1,(oD x hD).2]
    exact blankC x (by omega)
  -- E: read `w`
  obtain ⟨HE0,AE0,rE,e0,-,e8,-,-,-,-,-⟩ := read_step (natWord 3) (natWord deg++natWord C++natWord 4++
    natWord hF++natWord cC++natWord dR++natWord rR) w
  have dE := rE.dock slotsE slotsE_injective HD AD
    (by
      intro j
      by_cases hj : j=0
      · subst hj
        show HD (slotsD 0)=_
        rw [hHD,dockH_slot _ slotsD_injective]
        show ([] : List Bool).length+2*natBitLength 3+1=(natWord 3).length
        rw [natWord_length]
        rfl
      · have hge : 19 ≤ (slotsE j).val := by
          revert j
          decide
        rw [(blankD _ hge).1]
        fin_cases j <;> first | exact absurd rfl hj | rfl)
    (by
      intro j
      by_cases hj : j=0
      · subst hj
        show AD (slotsD 0)=_
        rw [hAD,install_slot _ slotsD_injective]
        show []++natWord 3++(natWord w++natWord deg++natWord C++natWord 4++natWord hF++natWord cC++
          natWord dR++natWord rR)=natWord 3++natWord w++(natWord deg++natWord C++natWord 4++natWord hF++
          natWord cC++natWord dR++natWord rR)
        simp only [List.nil_append,List.append_assoc]
      · have hge : 19 ≤ (slotsE j).val := by
          revert j
          decide
        rw [(blankD _ hge).2]
        fin_cases j <;> first | exact absurd rfl hj | rfl)
  set AE := install slotsE AD AE0 with hAE
  have oE : ∀ x,(∀ j,slotsE j≠x) → AE x=AD x := fun x hx=>install_other _ _ _ _ hx
  have hmE : natWord 3++natWord w++(natWord deg++natWord C++natWord 4++natWord hF++natWord cC++
      natWord dR++natWord rR)=m := by
    rw [hm]
    simp only [List.append_assoc]
  refine ⟨_,AE,(((dA.seq dB).seq dC).seq dD).seq dE,?_,?_,?_,?_,?_,?_⟩
  · rw [oE 0 (by decide),(oD 0 (by decide)).2,cc0]
  · rw [oE 1 (by decide),(oD 1 (by decide)).2,cc1]
  · show AE (slotsE 0)=_
    rw [hAE,install_slot _ slotsE_injective,e0,hmE]
  · rw [oE 12 (by decide),(oD 12 (by decide)).2,cc12]
  · rw [oE 16 (by decide),(oD 16 (by decide)).2,cc16]
  · show AE (slotsE 8)=_
    rw [hAE,install_slot _ slotsE_injective,e8]

/-- **I2a, local form.** One fixed machine from the pool word (0), the arity template (1) and the
metadata word (2), everything else blank and every head `0`, to every head `0` and:
`tape N` on 12, `1^|exactListWord gs|` on 16, `1^w` on 26; the three inputs kept. -/
theorem hdr_run {k : Nat} (gs : List (ExactThresholdGate k)) (w deg C hF cC dR rR : Nat) :
    ∃ A : Fin 30 → List Bool,Step hdrMachine (hdrCost gs w) (fun _=>0)
        (Fin.addCases (hdrIn gs (metaWord w deg C hF cC dR rR)) (fun _ : Fin 1=>[])) (fun _=>0) A ∧
      A 0=exactListWord gs ∧ A 1=UnaryTemplate.tape k ∧ A 2=metaWord w deg C hF cC dR rR ∧
      A 12=UnaryTemplate.tape gs.length ∧ A 16=List.replicate (exactListWord gs).length true ∧
      A 26=List.replicate w true := by
  obtain ⟨H,A,run,a0,a1,a2,a12,a16,a26⟩ := hdr_chain gs w deg C hF cC dR rR
  obtain ⟨kk,-,mR⟩ := mask_empty run (fun _=>true) (fun _ _=>rfl)
  have hin : Fin.addCases (m:=29) (n:=1) (fun _ : Fin 29=>(0:Nat)) (fun _ : Fin 1=>0)=fun _=>0 := by
    funext i
    refine Fin.addCases (m:=29) (n:=1) (fun j=>?_) (fun j=>?_) i
    · rw [Fin.addCases_left]
    · rw [Fin.addCases_right]
  have hout : Fin.addCases (m:=29) (n:=1) (fun i=>if (fun _ : Fin 29=>true) i then 0 else H i)
      (fun _ : Fin 1=>0)=fun _=>0 := by
    funext i
    refine Fin.addCases (m:=29) (n:=1) (fun j=>?_) (fun j=>?_) i
    · rw [Fin.addCases_left]
      rfl
    · rw [Fin.addCases_right]
  let R : Fin 30 → List Bool :=
    Fin.addCases (m:=29) (n:=1) (motive:=fun _=>List Bool) A (fun _=>List.replicate kk false)
  have hR : ∀ x : Fin 29,R (Fin.castAdd 1 x)=A x := fun x=>Fin.addCases_left x
  exact ⟨R,(mR.congr_in hin rfl).congr hout rfl,(hR 0).trans a0,(hR 1).trans a1,(hR 2).trans a2,
    (hR 12).trans a12,(hR 16).trans a16,(hR 26).trans a26⟩

/-- **I2a, docked** at any injective 30-port map of a larger bank whose mapped heads are `0`, whose
ports `slots 0/1/2` hold the pool word, the arity template and the metadata word, and whose other
mapped ports are blank: exit heads unchanged, the named outputs in place. -/
theorem hdr_dock {T k : Nat} (slots : Fin 30 → Fin T) (hinj : Function.Injective slots)
    (gs : List (ExactThresholdGate k)) (w deg C hF cC dR rR : Nat) (H : Fin T → Nat) (A : Fin T → List Bool)
    (hH : ∀ i,H (slots i)=0) (h0 : A (slots 0)=exactListWord gs) (h1 : A (slots 1)=UnaryTemplate.tape k)
    (h2 : A (slots 2)=metaWord w deg C hF cC dR rR) (hA : ∀ i,3 ≤ i.val → A (slots i)=[]) :
    ∃ B : Fin 30 → List Bool,Step (RecoveryFocus.machine slots hdrMachine) (hdrCost gs w)
        H A H (install slots A B) ∧
      B 0=exactListWord gs ∧ B 1=UnaryTemplate.tape k ∧ B 2=metaWord w deg C hF cC dR rR ∧
      B 12=UnaryTemplate.tape gs.length ∧ B 16=List.replicate (exactListWord gs).length true ∧
      B 26=List.replicate w true := by
  obtain ⟨B,run,b0,b1,b2,b12,b16,b26⟩ := hdr_run gs w deg C hF cC dR rR
  refine ⟨B,?_,b0,b1,b2,b12,b16,b26⟩
  have d := run.dock slots hinj H A hH (by
    intro i
    refine Fin.addCases (m:=29) (n:=1) (fun j=>?_) (fun j=>?_) i
    · rw [Fin.addCases_left]
      by_cases hj0 : j=0
      · subst hj0
        exact h0.trans (by simp [hdrIn])
      · by_cases hj1 : j=1
        · subst hj1
          exact h1.trans (by simp [hdrIn])
        · by_cases hj2 : j=2
          · subst hj2
            exact h2.trans (by simp [hdrIn])
          · have hv : 3 ≤ j.val := by
              have a : j.val≠0 := fun h=>hj0 (Fin.ext h)
              have b : j.val≠1 := fun h=>hj1 (Fin.ext h)
              have c : j.val≠2 := fun h=>hj2 (Fin.ext h)
              omega
            rw [hA _ (by simpa using hv),hdrIn_blank gs _ j hv]
    · rw [Fin.addCases_right,hA _ (by simp)])
  exact d.congr (dockH_existing _ _ _ hH) rfl

/-! ## 3. Cost: dominated by the Header's own budget -/

theorem bits_le (x : Nat) : natBitLength x ≤ x+1 := by
  unfold natBitLength
  have := Nat.log_le_self 2 x
  omega

/-- The pass is linear in the pool word's bytes, `(arity+1)·(count+1)` and `w`. -/
theorem hdrCost_le {k : Nat} (gs : List (ExactThresholdGate k)) (w : Nat) :
    hdrCost gs w ≤ 300*((exactListWord gs).length+(k+1)*(gs.length+1)+w+1) := by
  have b1 := bits_le gs.length
  have b2 := bits_le w
  have b3 := bits_le 3
  have ht : gs.take gs.length=gs := List.take_of_length_le (le_refl _)
  have hB : (exactListWord gs).length=(natWord gs.length).length+(gs.flatMap exactWord).length := by
    simp [exactListWord]
  have hmul : (6*k+10)*gs.length ≤ 10*((k+1)*(gs.length+1)) := by nlinarith
  have hN : gs.length ≤ (k+1)*(gs.length+1) := by nlinarith
  unfold hdrCost chainCost readCost DecompositionCachedChild.budget
  rw [ht]
  omega

/-- The compact metadata pass alone pays `2·(B+(n+1)(N+1))+8w`. -/
theorem meta_ge (B n N b D Q w : Nat) :
    2*(B+(n+1)*(N+1))+8*w ≤ CompactMetadata.budget B n N b D Q w := by
  unfold CompactMetadata.budget CompactMetadata.budget8 CompactMetadata.budget7 CompactMetadata.budget6
    CompactMetadata.budget5 CompactMetadata.budget4 CompactMetadata.budget3 CompactMetadata.budget2
    CompactMetadata.budget1 CompactSize.budget CompactSize.value NearCubicWires.ExtIncidence.NativeShort.budget
  omega

/-- **Budget class.** The Header-word pass of a family costs at most `300·(Header.budget+1)` for
ANY row of the family; with a row present, `RowCaps.Good` bounds this by `300·(headerFuel+1)`. -/
theorem hdrCost_header {q L : Nat} (a : DecompositionAlgorithm) (F : PCJ9eff70d512234a4c_Fixed.Packets.Family q L)
    (g : PCJ9eff70d512234a4c_Fixed.Packets.Geometry F) (layout : PCJ9eff70d512234a4c_Fixed.Packets.Layout a F g)
    (r : PCJ9eff70d512234a4c_Fixed.Packets.Row F.occurrences L) :
    hdrCost (PCJ9eff70d512234a4c_Fixed.Packets.pool a F g) layout.w ≤
      300*(PCJcc051fd4c1bd4540_Header.budget a F g layout r+1) := by
  letI := PCJ9eff70d512234a4c_Fixed.Packets.radix a F g layout
  have h1 := hdrCost_le (PCJ9eff70d512234a4c_Fixed.Packets.pool a F g) layout.w
  have h2 := meta_ge (exactListWord (PCJ9eff70d512234a4c_Fixed.Packets.pool a F g)).length
    ((PCJ9eff70d512234a4c_Fixed.Packets.residual F+1)/2+PCJ9eff70d512234a4c_Fixed.Packets.residual F/2)
    (PCJ9eff70d512234a4c_Fixed.Packets.pool a F g).length
    (P1Radix.bits (PCJ9eff70d512234a4c_Fixed.Packets.pool a F g))
    (P1Radix.effectiveDegree (PCJ9eff70d512234a4c_Fixed.Packets.pool a F g))
    ((PCJ9eff70d512234a4c_Fixed.Packets.live F).card+1) layout.w
  have h3 : CompactMetadata.budget (exactListWord (PCJ9eff70d512234a4c_Fixed.Packets.pool a F g)).length
      ((PCJ9eff70d512234a4c_Fixed.Packets.residual F+1)/2+PCJ9eff70d512234a4c_Fixed.Packets.residual F/2)
      (PCJ9eff70d512234a4c_Fixed.Packets.pool a F g).length
      (P1Radix.bits (PCJ9eff70d512234a4c_Fixed.Packets.pool a F g))
      (P1Radix.effectiveDegree (PCJ9eff70d512234a4c_Fixed.Packets.pool a F g))
      ((PCJ9eff70d512234a4c_Fixed.Packets.live F).card+1) layout.w ≤
      PCJcc051fd4c1bd4540_Header.budget a F g layout r := by
    unfold PCJcc051fd4c1bd4540_Header.budget CompactColdFamily.budget CompactNativeInitialize.budget
    omega
  omega

/-! ## 4. The 430 mutable Header reserves `pad U []` -/

theorem pad_blank (K : Nat) : ZeroPadding.pad K []=List.replicate K false := by
  simp [ZeroPadding.pad]

/-- **Mutable reserves.** With the resident Header-erase pair (`1^U`, `0^(U+1)`) and every mutable
Header port blank, one paid erase leaves every mutable Header port at `pad U [] = 0^U` (the entry
value `pad (reserve k) (commonHeader k)` for `reserve k = U`, `HeaderErase.commonHeader_mutable`),
driver, log, heads and every other port unchanged. -/
theorem reserves_step {T : Nat} (hdr : Fin 440 → Fin T) (drvP logP : Fin T)
    (hinj : Function.Injective (eraseAll (fun i=>hdr (PCJ45bee56da9f34d5a_HeaderErase.mutable i)) drvP logP))
    (U : Nat) (H : Fin T → Nat) (A : Fin T → List Bool)
    (hH : ∀ i,H (eraseAll (fun i=>hdr (PCJ45bee56da9f34d5a_HeaderErase.mutable i)) drvP logP i)=0)
    (hblank : ∀ i,A (hdr (PCJ45bee56da9f34d5a_HeaderErase.mutable i))=[])
    (hd : A drvP=List.replicate U true) (hl : A logP=List.replicate (U+1) false) :
    Step (RecoveryFocus.machine (eraseAll (fun i=>hdr (PCJ45bee56da9f34d5a_HeaderErase.mutable i)) drvP logP)
        (RecoveryScratchErase.resetMachine 430)) (2*U+4) H A H
      (install (fun i=>hdr (PCJ45bee56da9f34d5a_HeaderErase.mutable i)) A (fun _=>ZeroPadding.pad U [])) := by
  classical
  have h := backing_step (fun i=>hdr (PCJ45bee56da9f34d5a_HeaderErase.mutable i)) drvP logP hinj U (U+1) H A hH
    (fun i=>by rw [hblank]; exact Nat.zero_le _) hd hl
  refine h.congr rfl ?_
  have hlog : ∀ i,hdr (PCJ45bee56da9f34d5a_HeaderErase.mutable i)≠logP := by
    intro i he
    have := hinj (show eraseAll (fun i=>hdr (PCJ45bee56da9f34d5a_HeaderErase.mutable i)) drvP logP
        (Fin.castAdd 1 (Fin.castAdd 1 i))=eraseAll (fun i=>hdr (PCJ45bee56da9f34d5a_HeaderErase.mutable i)) drvP logP
        (Fin.natAdd (430+1) 0) by simp only [eraseAll,Fin.addCases_left,Fin.addCases_right]; exact he)
    have hv := congrArg Fin.val this
    simp at hv
    omega
  funext x
  by_cases hx : x=logP
  · subst hx
    rw [Function.update_self,install_other _ _ _ _ hlog,hl,Nat.max_self]
  · rw [Function.update_of_ne hx]
    simp only [pad_blank]

/-! ## 5. The consumer's words at the I2a ports -/

/-- `commonHeader` (the entry Header bank before padding) at the pool port and the three I2a ports. -/
theorem common_words {q L : Nat} (a : DecompositionAlgorithm) (F : PCJ9eff70d512234a4c_Fixed.Packets.Family q L)
    (g : PCJ9eff70d512234a4c_Fixed.Packets.Geometry F) (layout : PCJ9eff70d512234a4c_Fixed.Packets.Layout a F g) :
    PCJ45bee56da9f34d5a_RowState.commonHeader a F g layout 0=exactListWord (PCJ9eff70d512234a4c_Fixed.Packets.pool a F g) ∧
    PCJ45bee56da9f34d5a_RowState.commonHeader a F g layout 278=
      List.replicate (exactListWord (PCJ9eff70d512234a4c_Fixed.Packets.pool a F g)).length true ∧
    PCJ45bee56da9f34d5a_RowState.commonHeader a F g layout 4=
      UnaryTemplate.tape (PCJ9eff70d512234a4c_Fixed.Packets.pool a F g).length ∧
    PCJ45bee56da9f34d5a_RowState.commonHeader a F g layout 88=List.replicate layout.w true := by
  unfold PCJ45bee56da9f34d5a_RowState.commonHeader CompactNativeInitialize.input
  refine ⟨?_,?_,?_,?_⟩
  · rw [show (0 : Fin 440)=CompactNativeInitialize.metadataSlots 7 from rfl,
      install_slot _ CompactNativeInitialize.meta_injective]
    rfl
  · rw [show (278 : Fin 440)=CompactNativeInitialize.metadataSlots 0 from rfl,
      install_slot _ CompactNativeInitialize.meta_injective]
    rfl
  · rw [show (4 : Fin 440)=CompactNativeInitialize.metadataSlots 2 from rfl,
      install_slot _ CompactNativeInitialize.meta_injective]
    rfl
  · rw [show (88 : Fin 440)=CompactNativeInitialize.metadataSlots 6 from rfl,
      install_slot _ CompactNativeInitialize.meta_injective]
    rfl

end
end RowsInit
