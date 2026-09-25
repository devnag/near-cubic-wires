import Proof.SourceAssembly.SourceFirstCore3
import Proof.SourceAssembly.SourceRefillSeam3

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
namespace NearCubicWires.SourceConstruction.Rest
noncomputable section

/-- The first prologue's second clear: the cursor template `rsT 2` and the loop counter `cnt`, then the resident
driver `scr 11` and log `scr 12`. -/
def clrCur {d : SourceConstruction.Dims} {eX pX gW : Nat} (e : d.RestExt eX pX gW) {V : Nat} (hV : d.U ≤ V)
    (cnt : Fin V) : Fin (2+1+1) → Fin V :=
  ![d.rsT e hV 2, cnt, d.scr hV 11, d.scr hV 12]

/-- **The first prologue's front**: the refill clear on `clr2`, the second clear on `clrCur`, then E6 (query copy to
`q284`, cache tape `c15` erased) on the cache's own driver/log `c17/c18`. -/
def firstFront {a : DecompositionAlgorithm} {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage a vE) (sp : PacketsGlue.RequestMeta.UnaryStage a vP)
    {d : SourceConstruction.Dims} {gW : Nat} (e : d.RestExt2 se.extra sp.extra gW) {V : Nat} (hV : d.U ≤ V)
    (cnt c15 q284 c17 c18 : Fin V) :=
  Composition.machine
    (RecoveryFocus.machine (Dims.clr2 e.ext1 hV) (PCJ6e421fabe2aa4155_SourceClear.machine (d.tcl2 se.extra sp.extra gW)))
    (Composition.machine (RecoveryFocus.machine (clrCur e.ext1 hV cnt) (PCJ6e421fabe2aa4155_SourceClear.machine 2))
      (Prologue.restoreMachine c15 q284 c17 c18))

def firstPro3 {a : DecompositionAlgorithm} {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage a vE) (sp : PacketsGlue.RequestMeta.UnaryStage a vP)
    {d : SourceConstruction.Dims} {gW : Nat} (e : d.RestExt3 se.extra sp.extra gW) {V : Nat} (hV : d.U ≤ V)
    {si : Nat} (initM : Machine V si) {s7 : Nat} (g7M : Machine V s7) (cnt c15 q284 c17 c18 : Fin V) :=
  Composition.machine initM
    (Composition.machine
      (RecoveryFocus.machine (Dims.clrZ e hV) (PCJ6e421fabe2aa4155_SourceClear.machine (71 + se.extra + sp.extra)))
      (Composition.machine (firstFront se sp e.ext2 hV cnt c15 q284 c17 c18) (firstCore se sp e.ext2 hV g7M cnt)))

structure InvC {d : SourceConstruction.Dims} {eX pX gW : Nat} (e : d.RestExt3 eX pX gW) {V : Nat} (hV : d.U ≤ V)
    (Rc Rk : Nat) (Kc : Fin V → Prop) (K0 : Fin V → List Bool) (KH0 : Fin V → Nat) (cnt : Fin V)
    (w q Mb Ms cW cQ cB cS S Rw B v U0 : Nat) (H : Fin V → Nat) (A : Fin V → List Bool) : Prop where
  kept : ∀ x, Kc x → A x = K0 x ∧ H x = KH0 x
  big : A (d.rsT e.ext2.ext1 hV 0) = ZeroPadding.pad cB (List.replicate Mb true)
  small : A (d.rsT e.ext2.ext1 hV 1) = ZeroPadding.pad cS (List.replicate Ms true)
  wv : A (d.rsT e.ext2.ext1 hV 3) = ZeroPadding.pad cW (List.replicate w true)
  qv : A (d.rsT e.ext2.ext1 hV 4) = ZeroPadding.pad cQ (List.replicate q true)
  rsH : ∀ i : Fin 5, i ≠ 2 → H (d.rsT e.ext2.ext1 hV i) = 0
  mU : A (Dims.mT e.ext2 hV 0) = ZeroPadding.pad Rc (List.replicate U0 true)
  mS : A (Dims.mT e.ext2 hV 1) = ZeroPadding.pad Rc (UnaryTemplate.tape S)
  mR : A (Dims.mT e.ext2 hV 2) = ZeroPadding.pad Rc (UnaryTemplate.tape Rw)
  mB : A (Dims.mT e.ext2 hV 3) = ZeroPadding.pad Rc (UnaryTemplate.tape B)
  mv : A (Dims.mT e.ext2 hV 4) = ZeroPadding.pad Rc (UnaryTemplate.tape v)
  mH : ∀ i, H (Dims.mT e.ext2 hV i) = 0
  drv : A (d.scr hV 11) = List.replicate Rc true
  drvH : H (d.scr hV 11) = 0
  lg : A (d.scr hV 12) = List.replicate (Rc+2) false
  lgH : H (d.scr hV 12) = 0
  zD : A (Dims.hrT e hV 10) = List.replicate Rk true
  zDH : H (Dims.hrT e hV 10) = 0
  zL : A (Dims.hrT e hV 11) = List.replicate (Rk+2) false
  zLH : H (Dims.hrT e hV 11) = 0
  dirtA : ∀ x : Fin V, d.InDirt eX pX gW x.val → ¬ d.InZ eX pX x.val → (A x).length ≤ Rc
  dirtH : ∀ x : Fin V, d.InDirt eX pX gW x.val → ¬ d.InZ eX pX x.val → H x ≤ Rc
  zA : ∀ x : Fin V, d.InZ eX pX x.val → (A x).length ≤ Rk
  zH : ∀ x : Fin V, d.InZ eX pX x.val → H x ≤ Rk
  curA : (A (d.rsT e.ext2.ext1 hV 2)).length ≤ Rc
  curH : H (d.rsT e.ext2.ext1 hV 2) ≤ Rc
  cntA : (A cnt).length ≤ Rc
  cntH : H cnt ≤ Rc
  encA : ∀ kk : Fin 13, (kk.val < 3 ∨ kk.val = 4) → (A (Dims.encT (d := d) hV kk)).length ≤ Rc
  encH : ∀ kk : Fin 13, (kk.val < 3 ∨ kk.val = 4) → H (Dims.encT (d := d) hV kk) = 0

section front
variable {d : SourceConstruction.Dims} {eX pX gW : Nat} (e : d.RestExt eX pX gW) {V : Nat} (hV : d.U ≤ V)

theorem clrCur_val (cnt : Fin V) (k : Fin (2+1+1)) :
    (clrCur e hV cnt k).val = if k.val = 0 then d.B + 19 + restPc eX pX gW + 2 else if k.val = 1 then cnt.val
      else if k.val = 2 then d.G + d.R1 + 397 + d.w + d.tc + 11 else d.G + d.R1 + 397 + d.w + d.tc + 12 := by
  fin_cases k <;> rfl

theorem clrCur_injective (cnt : Fin V) (hcnt : cnt.val = d.U) : Function.Injective (clrCur e hV cnt) := by
  have hB : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  have hU : d.U = d.G + d.prepT := rfl
  have hprep : d.prepT = d.R1 + 410 + d.w + d.tc + d.res := rfl
  have := e.hres
  intro a b h
  have hv := congrArg Fin.val h
  rw [clrCur_val, clrCur_val, hcnt] at hv
  have ha := a.isLt; have hb := b.isLt
  apply Fin.ext
  split_ifs at hv <;> omega

/-- **The first prologue's front run.** From a bank whose refill clear set, cursor template and counter are
dirt-bounded by `Rc`, with the resident driver/log, the cache's query word/driver/log and the copy tape as E6 needs:
the clear set, the cursor template and the counter are blank at `Rc` with head 0, the copy tape holds the query word,
cache tape 15 is erased, and every other tape (word and head) is kept. -/
theorem first_front_run {a : DecompositionAlgorithm} {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage a vE) (sp : PacketsGlue.RequestMeta.UnaryStage a vP)
    (e2 : d.RestExt2 se.extra sp.extra gW) (cnt c15 q284 c17 c18 : Fin V) (hcnt : cnt.val = d.U)
    (hlow : c15.val < d.F ∧ q284.val < d.F ∧ c17.val < d.F ∧ c18.val < d.F)
    (h1 : c15 ≠ q284) (h2 : c15 ≠ c17) (h3 : c15 ≠ c18) (h4 : q284 ≠ c17) (h5 : q284 ≠ c18) (h6 : c17 ≠ c18)
    (Rc C : Nat) (wq : List Bool) (hwq : wq.length = C) (H : Fin V → Nat) (A : Fin V → List Bool)
    (hclrA : ∀ x : Fin V, d.InClear se.extra sp.extra gW x.val → (A x).length ≤ Rc)
    (hclrH : ∀ x : Fin V, d.InClear se.extra sp.extra gW x.val → H x ≤ Rc)
    (hcT : (A (d.rsT e2.ext1 hV 2)).length ≤ Rc) (hcTH : H (d.rsT e2.ext1 hV 2) ≤ Rc)
    (hcA : (A cnt).length ≤ Rc) (hcH : H cnt ≤ Rc)
    (hdrv : A (d.scr hV 11) = List.replicate Rc true) (hdrvH : H (d.scr hV 11) = 0)
    (hlg : A (d.scr hV 12) = List.replicate (Rc+2) false) (hlgH : H (d.scr hV 12) = 0)
    (hq : A c15 = wq) (hq17 : A c17 = List.replicate C true) (hq18 : A c18 = List.replicate (C+1) false)
    (h284 : (A q284).length ≤ C)
    (hH15 : H c15 = 0) (hH284 : H q284 = 0) (hH17 : H c17 = 0) (hH18 : H c18 = 0) :
    ∃ (Hf : Fin V → Nat) (Af : Fin V → List Bool),
      Step (firstFront se sp e2 hV cnt c15 q284 c17 c18)
        ((4*Rc+7) + 1 + ((4*Rc+7) + 1 + ((2*C+4) + 1 + (2*C+4) + 1 + (2*C+4)))) H A Hf Af ∧
      (∀ x : Fin V, d.InClear se.extra sp.extra gW x.val → Af x = List.replicate Rc false ∧ Hf x = 0) ∧
      Af (d.rsT e2.ext1 hV 2) = List.replicate Rc false ∧ Hf (d.rsT e2.ext1 hV 2) = 0 ∧
      Af cnt = List.replicate Rc false ∧ Hf cnt = 0 ∧
      Af (d.scr hV 11) = List.replicate Rc true ∧ Hf (d.scr hV 11) = 0 ∧
      Af (d.scr hV 12) = List.replicate (Rc+2) false ∧ Hf (d.scr hV 12) = 0 ∧
      Af q284 = wq ∧ Hf q284 = 0 ∧ Af c15 = List.replicate C false ∧ Hf c15 = 0 ∧
      (∀ x : Fin V, ¬ d.InClear se.extra sp.extra gW x.val → x ≠ d.scr hV 11 → x ≠ d.scr hV 12 →
        x ≠ d.rsT e2.ext1 hV 2 → x ≠ cnt → x ≠ c15 → x ≠ q284 → Af x = A x ∧ Hf x = H x) := by
  classical
  have hB : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  have hG : d.G = d.F + d.rt + 13 := rfl
  have hU : d.U = d.G + d.prepT := rfl
  have hprep : d.prepT = d.R1 + 410 + d.w + d.tc + d.res := rfl
  have hp : d.pscr = d.R1 + 408 + d.w + d.tc := rfl
  have hres2 := e2.hres2
  have vscr : ∀ m : Fin 13, (d.scr hV m).val = d.G + d.R1 + 397 + d.w + d.tc + m.val := fun _ => rfl
  have vrs2 : (d.rsT e2.ext1 hV 2).val = d.B + 19 + restPc se.extra sp.extra gW + 2 := rfl
  have vPc : restPc se.extra sp.extra gW = 71 + se.extra + sp.extra + gW := rfl
  -- 1. the clear on `clr2`
  have sC := Refill.clear_on (Dims.clr2 e2.ext1 hV) (Dims.clr2_injective e2.ext1 hV) Rc H A
    (fun k => hclrH _ (Dims.clr2_in e2.ext1 hV k)) (fun k => hclrA _ (Dims.clr2_in e2.ext1 hV k))
    (by rw [Dims.clr2_driver]; exact hdrvH) (by rw [Dims.clr2_log]; exact hlgH)
    (by rw [Dims.clr2_driver]; exact hdrv) (by rw [Dims.clr2_log]; exact hlg)
  obtain ⟨cA, cH, cD, cDH, cL, cLH, cOA, cOH⟩ := clear_facts e2.ext1 hV Rc H A
  obtain ⟨H1, hH1⟩ : ∃ H1 : Fin V → Nat, H1 = dockH (Dims.clr2 e2.ext1 hV) H (fun _ => 0) := ⟨_, rfl⟩
  obtain ⟨A1, hA1⟩ : ∃ A1 : Fin V → List Bool, A1 = install (Dims.clr2 e2.ext1 hV) A
      (PCJ6e421fabe2aa4155_SourceClear.join (fun _ => List.replicate Rc false) (List.replicate Rc true)
        (List.replicate (Rc+2) false)) := ⟨_, rfl⟩
  rw [← hH1, ← hA1] at sC
  rw [← hA1] at cA cD cL cOA
  rw [← hH1] at cH cDH cLH cOH
  have nclT : ¬ d.InClear se.extra sp.extra gW (d.rsT e2.ext1 hV 2).val := by
    unfold SourceConstruction.Dims.InClear; rw [vrs2]; omega
  have nclC : ¬ d.InClear se.extra sp.extra gW cnt.val := by
    unfold SourceConstruction.Dims.InClear; rw [hcnt, hU, hprep]; omega
  have tS11 : d.rsT e2.ext1 hV 2 ≠ d.scr hV 11 := ne_val (by rw [vrs2, vscr]; omega)
  have tS12 : d.rsT e2.ext1 hV 2 ≠ d.scr hV 12 := ne_val (by rw [vrs2, vscr]; omega)
  have cS11 : cnt ≠ d.scr hV 11 := ne_val (by rw [hcnt, vscr, hU, hprep]; omega)
  have cS12 : cnt ≠ d.scr hV 12 := ne_val (by rw [hcnt, vscr, hU, hprep]; omega)
  -- 2. the clear on `clrCur`
  have inj3 := clrCur_injective e2.ext1 hV cnt hcnt
  have k0 : clrCur e2.ext1 hV cnt (Fin.castAdd 1 (Fin.castAdd 1 (0 : Fin 2))) = d.rsT e2.ext1 hV 2 := rfl
  have k1 : clrCur e2.ext1 hV cnt (Fin.castAdd 1 (Fin.castAdd 1 (1 : Fin 2))) = cnt := rfl
  have k3d : clrCur e2.ext1 hV cnt (Fin.castAdd 1 ((0 : Fin 1).natAdd 2)) = d.scr hV 11 := rfl
  have k3l : clrCur e2.ext1 hV cnt ((0 : Fin 1).natAdd (2 + 1)) = d.scr hV 12 := rfl
  have kst : ∀ kk : Fin 2, clrCur e2.ext1 hV cnt (Fin.castAdd 1 (Fin.castAdd 1 kk)) = d.rsT e2.ext1 hV 2 ∨
      clrCur e2.ext1 hV cnt (Fin.castAdd 1 (Fin.castAdd 1 kk)) = cnt := by
    intro kk; fin_cases kk
    · exact Or.inl k0
    · exact Or.inr k1
  have sC3 := Refill.clear_on (clrCur e2.ext1 hV cnt) inj3 Rc H1 A1
    (fun kk => by
      rcases kst kk with h | h <;> rw [h]
      · rw [cOH _ nclT tS11 tS12]; exact hcTH
      · rw [cOH _ nclC cS11 cS12]; exact hcH)
    (fun kk => by
      rcases kst kk with h | h <;> rw [h]
      · rw [cOA _ nclT tS11 tS12]; exact hcT
      · rw [cOA _ nclC cS11 cS12]; exact hcA)
    (by rw [k3d]; exact cDH) (by rw [k3l]; exact cLH) (by rw [k3d]; exact cD) (by rw [k3l]; exact cL)
  obtain ⟨H2, hH2⟩ : ∃ H2 : Fin V → Nat, H2 = dockH (clrCur e2.ext1 hV cnt) H1 (fun _ => 0) := ⟨_, rfl⟩
  obtain ⟨A2, hA2⟩ : ∃ A2 : Fin V → List Bool, A2 = install (clrCur e2.ext1 hV cnt) A1
      (PCJ6e421fabe2aa4155_SourceClear.join (fun _ => List.replicate Rc false) (List.replicate Rc true)
        (List.replicate (Rc+2) false)) := ⟨_, rfl⟩
  rw [← hH2, ← hA2] at sC3
  have off3 : ∀ x : Fin V, x ≠ d.rsT e2.ext1 hV 2 → x ≠ cnt → x ≠ d.scr hV 11 → x ≠ d.scr hV 12 →
      ∀ kk, clrCur e2.ext1 hV cnt kk ≠ x := by
    intro x a1 a2 a3 a4 kk hk
    fin_cases kk
    · exact a1 hk.symm
    · exact a2 hk.symm
    · exact a3 hk.symm
    · exact a4 hk.symm
  have A2o : ∀ x, x ≠ d.rsT e2.ext1 hV 2 → x ≠ cnt → x ≠ d.scr hV 11 → x ≠ d.scr hV 12 → A2 x = A1 x :=
    fun x a1 a2 a3 a4 => by rw [hA2]; exact install_other _ A1 _ x (off3 x a1 a2 a3 a4)
  have H2o : ∀ x, x ≠ d.rsT e2.ext1 hV 2 → x ≠ cnt → x ≠ d.scr hV 11 → x ≠ d.scr hV 12 → H2 x = H1 x :=
    fun x a1 a2 a3 a4 => by rw [hH2]; exact dockH_other _ H1 _ x (off3 x a1 a2 a3 a4)
  have jst : ∀ kk : Fin 2, (PCJ6e421fabe2aa4155_SourceClear.join (fun _ => List.replicate Rc false)
      (List.replicate Rc true) (List.replicate (Rc+2) false)) (Fin.castAdd 1 (Fin.castAdd 1 kk)) =
      List.replicate Rc false := by
    intro kk; rw [PCJ6e421fabe2aa4155_SourceClear.join, Fin.addCases_left, Fin.addCases_left]
  have A2t : A2 (d.rsT e2.ext1 hV 2) = List.replicate Rc false := by
    rw [hA2]
    exact (congrArg (install (clrCur e2.ext1 hV cnt) A1 _) k0.symm).trans
      ((install_slot _ inj3 _ _ _).trans (jst 0))
  have A2c : A2 cnt = List.replicate Rc false := by
    rw [hA2]
    exact (congrArg (install (clrCur e2.ext1 hV cnt) A1 _) k1.symm).trans
      ((install_slot _ inj3 _ _ _).trans (jst 1))
  have H2t : H2 (d.rsT e2.ext1 hV 2) = 0 := by
    rw [hH2]
    exact (congrArg (dockH (clrCur e2.ext1 hV cnt) H1 (fun _ => 0)) k0.symm).trans (dockH_slot _ inj3 _ _ _)
  have H2c : H2 cnt = 0 := by
    rw [hH2]
    exact (congrArg (dockH (clrCur e2.ext1 hV cnt) H1 (fun _ => 0)) k1.symm).trans (dockH_slot _ inj3 _ _ _)
  have A2d : A2 (d.scr hV 11) = List.replicate Rc true := by
    rw [hA2, ← k3d, install_slot _ inj3, PCJ6e421fabe2aa4155_SourceClear.join, Fin.addCases_left, Fin.addCases_right]
  have A2l : A2 (d.scr hV 12) = List.replicate (Rc+2) false := by
    rw [hA2, ← k3l, install_slot _ inj3, PCJ6e421fabe2aa4155_SourceClear.join, Fin.addCases_right]
  have H2d : H2 (d.scr hV 11) = 0 := by rw [hH2, ← k3d, dockH_slot _ inj3]
  have H2l : H2 (d.scr hV 12) = 0 := by rw [hH2, ← k3l, dockH_slot _ inj3]
  -- the E6 tapes are below `F`: untouched by both clears
  have lowK : ∀ x : Fin V, x.val < d.F → A2 x = A x ∧ H2 x = H x := by
    intro x hx
    have n1 : ¬ d.InClear se.extra sp.extra gW x.val := by unfold SourceConstruction.Dims.InClear; omega
    have n2 : x ≠ d.scr hV 11 := ne_val (by rw [vscr]; omega)
    have n3 : x ≠ d.scr hV 12 := ne_val (by rw [vscr]; omega)
    have n4 : x ≠ d.rsT e2.ext1 hV 2 := ne_val (by rw [vrs2]; omega)
    have n5 : x ≠ cnt := ne_val (by rw [hcnt, hU, hprep]; omega)
    exact ⟨(A2o x n4 n5 n2 n3).trans (cOA x n1 n2 n3), (H2o x n4 n5 n2 n3).trans (cOH x n1 n2 n3)⟩
  -- 3. E6
  obtain ⟨A3, s6, e15, e284, e17, e18, eo⟩ := Prologue.query_restore c15 q284 c17 c18 h1 h2 h3 h4 h5 h6 C wq hwq
    H2 A2 (by rw [(lowK _ hlow.1).1]; exact hq) (by rw [(lowK _ hlow.2.2.1).1]; exact hq17)
    (by rw [(lowK _ hlow.2.2.2).1]; exact hq18) (by rw [(lowK _ hlow.2.1).1]; exact h284)
    (by rw [(lowK _ hlow.1).2]; exact hH15) (by rw [(lowK _ hlow.2.1).2]; exact hH284)
    (by rw [(lowK _ hlow.2.2.1).2]; exact hH17) (by rw [(lowK _ hlow.2.2.2).2]; exact hH18)
  have lowNe : ∀ x : Fin V, d.F ≤ x.val → x ≠ c15 ∧ x ≠ q284 ∧ x ≠ c17 ∧ x ≠ c18 := by
    intro x hx
    exact ⟨ne_val (by omega), ne_val (by omega), ne_val (by omega), ne_val (by omega)⟩
  have e3 : ∀ x : Fin V, d.F ≤ x.val → A3 x = A2 x := by
    intro x hx
    obtain ⟨a1, a2, a3, a4⟩ := lowNe x hx
    exact eo x a1 a2 a3 a4
  refine ⟨H2, A3, sC.seq (sC3.seq s6), ?_, ?_, H2t, ?_, H2c, ?_, H2d, ?_, H2l, e284, ?_, e15, ?_, ?_⟩
  · intro x hx
    have hxF : d.F ≤ x.val := by unfold SourceConstruction.Dims.InClear at hx; omega
    have n4 : x ≠ d.rsT e2.ext1 hV 2 := fun h => nclT (h ▸ hx)
    have n5 : x ≠ cnt := fun h => nclC (h ▸ hx)
    have n2 : x ≠ d.scr hV 11 := ne_val (by
      rw [vscr]; unfold SourceConstruction.Dims.InClear at hx; omega)
    have n3 : x ≠ d.scr hV 12 := ne_val (by
      rw [vscr]; unfold SourceConstruction.Dims.InClear at hx; omega)
    rw [e3 x hxF, A2o x n4 n5 n2 n3, H2o x n4 n5 n2 n3]
    exact ⟨cA x hx, cH x hx⟩
  · rw [e3 _ (by rw [vrs2]; omega)]; exact A2t
  · rw [e3 _ (by rw [hcnt, hU, hprep]; omega)]; exact A2c
  · rw [e3 _ (by rw [vscr]; omega)]; exact A2d
  · rw [e3 _ (by rw [vscr]; omega)]; exact A2l
  · rw [(lowK _ hlow.2.1).2]; exact hH284
  · rw [(lowK _ hlow.1).2]; exact hH15
  · intro x a1 a2 a3 a4 a5 a6 a7
    by_cases hxF : d.F ≤ x.val
    · rw [e3 x hxF, A2o x a4 a5 a2 a3, H2o x a4 a5 a2 a3]
      exact ⟨cOA x a1 a2 a3, cOH x a1 a2 a3⟩
    · have hx' : x.val < d.F := by omega
      by_cases h17 : x = c17
      · subst h17
        rw [e17, (lowK _ hx').2]; exact ⟨hq17.symm, rfl⟩
      by_cases h18 : x = c18
      · subst h18
        rw [e18, (lowK _ hx').2]; exact ⟨hq18.symm, rfl⟩
      rw [eo x a6 a7 h17 h18]
      exact lowK x hx'

end front

end
end NearCubicWires.SourceConstruction.Rest
end
