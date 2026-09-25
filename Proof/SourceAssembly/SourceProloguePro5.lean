import Proof.SourceAssembly.SourceRestRunD5

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

section concrete
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources) (res : Nat)
  {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources res p k r

theorem prologue_rest5 {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) vE)
    (sp : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) vP) {gW : Nat}
    (e : (𝔇).RestExt2 se.extra sp.extra gW) {V : Nat} (hV : (𝔇).U ≤ V)
    {s7 : Nat} (g7M : Machine V s7) (g7cost : Nat → Nat)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits))
    (L target : Nat) (mode : Bool) (Rc b : Nat)
    (layoutAt : ∀ m : Nat, Packets.Layout (decompositionOf sources)
      ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources))
      (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode m)))
    (capsAt : Nat → RowCaps)
    (K : Fin V → Prop) (K0 : Fin V → List Bool) (KH0 : Fin V → Nat)
    (hG7 : ResidentRunH g7M g7cost mask (packets (decompositionOf sources))
      (rows (decompositionOf sources) (printerOf sources))
      ((𝔇).maskSlots hV) ((𝔇).pslots hV) ((𝔇).slot hV) ((𝔇).ret hV) ((𝔇).scr hV 0) ((𝔇).scr hV 1)
      ((𝔇).familySlots hV) ((𝔇).poolSlots hV) (Dims.rewind2Slots e.ext1.ext hV)
      ((𝔇).scr hV 5) ((𝔇).scr hV 6) ((𝔇).scr hV 7) ((𝔇).scr hV 8) ((𝔇).scr hV 9) ((𝔇).scr hV 10)
      (Dims.lenTape e.ext1.ext hV) coordinate ph ci L target mode Rc b
      ((𝔇).pcT e.ext1 hV ⟨70, by unfold restPc; omega⟩)
      (fun i => (𝔇).pcT e.ext1 hV ⟨61 + i.val, by have := i.isLt; unfold restPc; omega⟩) layoutAt capsAt
      (Dims.Rpad (d := 𝔇) (eX := se.extra) (pX := sp.extra) (gW := gW) (V := V) Rc)
      (RestIn4 (𝔇) se.extra sp.extra gW Rc ((𝔇).pcT e.ext1 hV ⟨64, by unfold restPc; omega⟩) K K0 KH0)
      (fun x => OutV (𝔇) se.extra sp.extra gW x.val))
    (j : Nat) (hj : j + 1 ≤ (monomials coordinate ph ci).length) (hRc : j + 1 + 3 ≤ Rc)
    (w cW cQ Mb Ms cB cS : Nat)
    (Hout : Fin V → Nat) (amb : Fin V → List Bool)
    (hK : ∀ x, K x → amb x = K0 x ∧ Hout x = KH0 x) (hKpos : ∀ x, K x → x.val < (𝔇).F ∨ (𝔇).B + 19 + restPc se.extra sp.extra gW + 10 ≤ x.val)
    (hMb : Mb ≤ Rc) (hMs : Ms ≤ Rc)
    (hcurT : amb ((𝔇).rsT e.ext1 hV 2) = ZeroPadding.pad Rc (UnaryTemplate.tape j))
    (hcurTH : Hout ((𝔇).rsT e.ext1 hV 2) = 0)
    (henc : ∀ kk : Fin 13, (kk.val < 3 ∨ kk.val = 4) → (amb (Dims.encT (d := 𝔇) hV kk)).length ≤ Rc)
    (hencH : ∀ kk : Fin 13, (kk.val < 3 ∨ kk.val = 4) → Hout (Dims.encT (d := 𝔇) hV kk) = 0)
    (hW : amb ((𝔇).rsT e.ext1 hV 3) = ZeroPadding.pad cW (List.replicate w true))
    (hWH : Hout ((𝔇).rsT e.ext1 hV 3) = 0)
    (hQ : amb ((𝔇).rsT e.ext1 hV 4) = ZeroPadding.pad cQ (List.replicate q true))
    (hQH : Hout ((𝔇).rsT e.ext1 hV 4) = 0)
    (hbig : amb ((𝔇).rsT e.ext1 hV 0) = ZeroPadding.pad cB (List.replicate Mb true))
    (hbigH : Hout ((𝔇).rsT e.ext1 hV 0) = 0)
    (hsmall : amb ((𝔇).rsT e.ext1 hV 1) = ZeroPadding.pad cS (List.replicate Ms true))
    (hsmallH : Hout ((𝔇).rsT e.ext1 hV 1) = 0)
    (hlog : 2 * ((requestAt coordinate ph ci L target mode (j+1)).input (decompositionOf sources)).length + 1 ≤ Rc)
    (he1 : 1 ≤ vE (requestAt coordinate ph ci L target mode (j+1)))
    (hpw : (CloseoutRowsCountBinary.bits (vP (requestAt coordinate ph ci L target mode (j+1)))).length ≤ w)
    (hfirst : vP (requestAt coordinate ph ci L target mode (j+1)) * 2^(natBitLength (vE (requestAt coordinate ph ci L target mode (j+1)))) < 2^w)
    (hsecond : vP (requestAt coordinate ph ci L target mode (j+1)) * vE (requestAt coordinate ph ci L target mode (j+1)) * 2^(q+1) < 2^w) :
    ∃ (H2 : Fin V → Nat) (A2 : Fin V → List Bool) (Av2 : Fin V → List Bool),
      Step (restMachine se sp e.ext1 hV g7M) (cursorCost j + 1 + (g7cost (j+1) + 1 + backCost se sp (requestAt coordinate ph ci L target mode (j+1)) Rc w q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length Mb Ms))
        (dockH (Dims.clr2 e.ext1 hV) Hout (fun _ => 0))
        (install (Dims.clr2 e.ext1 hV) amb (PCJ6e421fabe2aa4155_SourceClear.join (fun _ => List.replicate Rc false)
          (List.replicate Rc true) (List.replicate (Rc+2) false))) H2 A2 ∧
      (∀ x, A2 x = ZeroPadding.pad (Dims.Rpad (d := 𝔇) (eX := se.extra) (pX := sp.extra) (gW := gW) (V := V) Rc x)
        (Av2 x)) ∧
      Nonempty (Resident mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources))
        ((𝔇).maskSlots hV) ((𝔇).pslots hV) ((𝔇).slot hV) ((𝔇).ret hV) ((𝔇).scr hV 0) ((𝔇).scr hV 1)
        ((𝔇).familySlots hV) ((𝔇).poolSlots hV) (Dims.rewind2Slots e.ext1.ext hV)
        ((𝔇).scr hV 5) ((𝔇).scr hV 6) ((𝔇).scr hV 7) ((𝔇).scr hV 8) ((𝔇).scr hV 9) ((𝔇).scr hV 10)
        (Dims.lenTape e.ext1.ext hV) (requestAt coordinate ph ci L target mode (j+1)) (layoutAt (j+1)) (capsAt (j+1))
        H2 Av2) ∧
      A2 (Dims.encT (d := 𝔇) hV 4) = ZeroPadding.pad Rc (RepairOrdinary.frame (SignedSortKey.binary w
        (vP (requestAt coordinate ph ci L target mode (j+1)) * vE (requestAt coordinate ph ci L target mode (j+1)) * 2^q))) ∧
      (∀ hm : j + 1 < (monomials coordinate ph ci).length, ∀ i : Fin 3, A2 (Dims.encT (d := 𝔇) hV ⟨i.val, by omega⟩) =
        ZeroPadding.pad Rc (RepairOrdinary.frame (CloseoutRowsEstimatorCoefficients.Stream.recordFields b
          (CloseoutFinalC10SupplierCalls.coefficientEstimate ((monomials coordinate ph ci)[j+1]).coefficient)
          0 0 ⟨i.val, by omega⟩))) ∧
      A2 (Dims.csSlots e.ext1.ext hV 1) = ZeroPadding.pad Rc (List.replicate (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length then Mb else Ms) true) ∧
      H2 (Dims.csSlots e.ext1.ext hV 1) = 0 ∧
      A2 ((𝔇).rsT e.ext1 hV 2) = ZeroPadding.pad Rc (UnaryTemplate.tape (j+1)) ∧ H2 ((𝔇).rsT e.ext1 hV 2) = 0 ∧
      (∀ x : Fin V, (((𝔇).F ≤ x.val ∧ x.val < (𝔇).F + (𝔇).rt) ∨ ((𝔇).B + 1 ≤ x.val ∧ x.val ≤ (𝔇).B + 12)) →
        A2 x = List.replicate Rc false ∧ H2 x = 0) ∧
      A2 ((𝔇).scr hV 11) = List.replicate Rc true ∧ H2 ((𝔇).scr hV 11) = 0 ∧
      A2 ((𝔇).scr hV 12) = List.replicate (Rc+2) false ∧ H2 ((𝔇).scr hV 12) = 0 ∧
      (∀ x : Fin V, ¬ (𝔇).InClear se.extra sp.extra gW x.val → x ≠ (𝔇).scr hV 11 → x ≠ (𝔇).scr hV 12 →
        ¬ OutV (𝔇) se.extra sp.extra gW x.val → x ≠ (𝔇).rsT e.ext1 hV 2 →
        ¬ ((𝔇).F + (𝔇).rt ≤ x.val ∧ x.val ≤ (𝔇).F + (𝔇).rt + 4 ∧ x.val ≠ (𝔇).F + (𝔇).rt + 3) →
        A2 x = amb x ∧ H2 x = Hout x) ∧
      (∀ x : Fin V, (𝔇).InClear se.extra sp.extra gW x.val → ¬ (𝔇).InZ se.extra sp.extra x.val →
        (A2 x).length ≤ Rc ∧ H2 x ≤ cursorCost j + 1 + g7cost (j+1)) ∧
      (∀ x : Fin V, (𝔇).InZ se.extra sp.extra x.val → (A2 x).length ≤ max Rc ((cursorCost j + 1 + (g7cost (j+1) + 1 + backCost se sp (requestAt coordinate ph ci L target mode (j+1)) Rc w q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length Mb Ms)) + 1) ∧ H2 x ≤ (cursorCost j + 1 + (g7cost (j+1) + 1 + backCost se sp (requestAt coordinate ph ci L target mode (j+1)) Rc w q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length Mb Ms))) ∧
      (∀ kk : Fin 13, H2 (Dims.encT (d := 𝔇) hV kk) = Hout (Dims.encT (d := 𝔇) hV kk)) ∧
      (∀ i : Fin 3, (A2 (Dims.encT (d := 𝔇) hV ⟨i.val, by omega⟩)).length ≤ Rc) := by
  classical
  have vG : (𝔇).G = (𝔇).F + (𝔇).rt + 13 := rfl
  have vB : (𝔇).B = (𝔇).G + (𝔇).R1 + 410 + (𝔇).w + (𝔇).tc := rfl
  have vp : (𝔇).pscr = (𝔇).R1 + 408 + (𝔇).w + (𝔇).tc := rfl
  have vPc : restPc se.extra sp.extra gW = 71 + se.extra + sp.extra + gW := rfl
  have hres2 := e.hres2
  have hF := e.ext1.ext.hF
  -- 1. the clear's exit on `clr2`
  obtain ⟨cA, cH, cD, cDH, cL, cLH, cOA, cOH⟩ := clear_facts e.ext1 hV Rc Hout amb
  -- 2. `rest` from the clear's exit
  have lowF : ∀ x : Fin V, (x.val < (𝔇).F ∨ (𝔇).B + 19 + restPc se.extra sp.extra gW + 10 ≤ x.val) →
      ¬ (𝔇).InClear se.extra sp.extra gW x.val ∧ x ≠ (𝔇).scr hV 11 ∧ x ≠ (𝔇).scr hV 12 := by
    intro x hx
    refine ⟨?_, ?_, ?_⟩
    · unfold SourceConstruction.Dims.InClear; omega
    · intro h; have := congrArg Fin.val h; simp only [SourceConstruction.Dims.scr, SourceConstruction.Dims.scrV] at this; omega
    · intro h; have := congrArg Fin.val h; simp only [SourceConstruction.Dims.scr, SourceConstruction.Dims.scrV] at this; omega
  have kCur : ∀ x : Fin V, (x.val < (𝔇).F ∨ (𝔇).B + 19 + restPc se.extra sp.extra gW + 10 ≤ x.val) →
      ∀ i, curSlots e.ext1 hV i ≠ x := by
    intro x hx i h
    have hv := congrArg Fin.val h
    fin_cases i <;> simp [curSlots, SourceConstruction.Dims.pcT, SourceConstruction.Dims.rsT] at hv <;> omega
  have hiRes : ∀ i : Fin 5, ¬ (𝔇).InClear se.extra sp.extra gW ((𝔇).rsT e.ext1 hV i).val ∧
      (𝔇).rsT e.ext1 hV i ≠ (𝔇).scr hV 11 ∧ (𝔇).rsT e.ext1 hV i ≠ (𝔇).scr hV 12 := by
    intro i
    have := i.isLt
    refine ⟨?_, ?_, ?_⟩
    · unfold SourceConstruction.Dims.InClear; simp only [SourceConstruction.Dims.rsT]; omega
    · intro h; have := congrArg Fin.val h
      simp only [SourceConstruction.Dims.rsT, SourceConstruction.Dims.scr, SourceConstruction.Dims.scrV] at this; omega
    · intro h; have := congrArg Fin.val h
      simp only [SourceConstruction.Dims.rsT, SourceConstruction.Dims.scr, SourceConstruction.Dims.scrV] at this; omega
  have hiEnc : ∀ kk : Fin 13, ¬ (𝔇).InClear se.extra sp.extra gW (Dims.encT (d := 𝔇) hV kk).val ∧
      Dims.encT (d := 𝔇) hV kk ≠ (𝔇).scr hV 11 ∧ Dims.encT (d := 𝔇) hV kk ≠ (𝔇).scr hV 12 := by
    intro kk
    have := kk.isLt
    refine ⟨?_, ?_, ?_⟩
    · unfold SourceConstruction.Dims.InClear; simp only [Dims.encT]; omega
    · intro h; have := congrArg Fin.val h
      simp only [Dims.encT, SourceConstruction.Dims.scr, SourceConstruction.Dims.scrV] at this; omega
    · intro h; have := congrArg Fin.val h
      simp only [Dims.encT, SourceConstruction.Dims.scr, SourceConstruction.Dims.scrV] at this; omega
  have cs1_in : (𝔇).InClear se.extra sp.extra gW (Dims.csSlots e.ext1.ext hV 1).val := by
    unfold SourceConstruction.Dims.InClear; right; right; left
    show (𝔇).B ≤ (𝔇).B + 13 ∧ (𝔇).B + 13 < (𝔇).B + 14
    omega
  obtain ⟨H2, A2, Av2, sR, hM2, ⟨res2⟩, e4, e02, ecs1, ecurT, ecurTH, frR, frRH, dG, e02L⟩ :=
    rest_run_d5 mask packets rows sources res p k r se sp e.ext1 hV g7M g7cost coordinate ph ci L target mode Rc b layoutAt capsAt K K0 KH0 hG7 j hj hRc w cW cQ Mb Ms cB cS
      (dockH (Dims.clr2 e.ext1 hV) Hout (fun _ => 0))
      (install (Dims.clr2 e.ext1 hV) amb (PCJ6e421fabe2aa4155_SourceClear.join (fun _ => List.replicate Rc false)
        (List.replicate Rc true) (List.replicate (Rc+2) false)))
      (fun x hx => by rw [cA x hx, List.length_replicate])
      (fun i => ⟨cA _ (pcT_in e.ext1 hV i), cH _ (pcT_in e.ext1 hV i)⟩)
      (fun x hx => ⟨cA x (out_in hx), cH x (out_in hx)⟩)
      (fun x hx => by
        obtain ⟨n1, n2, n3⟩ := lowF x (hKpos x hx)
        rw [cOA x n1 n2 n3, cOH x n1 n2 n3]; exact hK x hx)
      (fun x hx i => kCur x (hKpos x hx) i)
      (fun x hx _ => ⟨cA x hx, cH x hx⟩)
      (by obtain ⟨n1, n2, n3⟩ := hiRes 2; rw [cOA _ n1 n2 n3]; exact hcurT)
      (by obtain ⟨n1, n2, n3⟩ := hiRes 2; rw [cOH _ n1 n2 n3]; exact hcurTH)
      (fun kk hk => by obtain ⟨n1, n2, n3⟩ := hiEnc kk; rw [cOA _ n1 n2 n3]; exact henc kk hk)
      (fun kk hk => by obtain ⟨n1, n2, n3⟩ := hiEnc kk; rw [cOH _ n1 n2 n3]; exact hencH kk hk)
      (by obtain ⟨n1, n2, n3⟩ := hiRes 3; rw [cOA _ n1 n2 n3]; exact hW)
      (by obtain ⟨n1, n2, n3⟩ := hiRes 3; rw [cOH _ n1 n2 n3]; exact hWH)
      (by obtain ⟨n1, n2, n3⟩ := hiRes 4; rw [cOA _ n1 n2 n3]; exact hQ)
      (by obtain ⟨n1, n2, n3⟩ := hiRes 4; rw [cOH _ n1 n2 n3]; exact hQH)
      cD cDH cL cLH
      (by obtain ⟨n1, n2, n3⟩ := hiRes 0; rw [cOA _ n1 n2 n3]; exact hbig)
      (by obtain ⟨n1, n2, n3⟩ := hiRes 0; rw [cOH _ n1 n2 n3]; exact hbigH)
      (by obtain ⟨n1, n2, n3⟩ := hiRes 1; rw [cOA _ n1 n2 n3]; exact hsmall)
      (by obtain ⟨n1, n2, n3⟩ := hiRes 1; rw [cOH _ n1 n2 n3]; exact hsmallH)
      (cA _ cs1_in) (cH _ cs1_in)
      hlog he1 hpw hfirst hsecond
  -- values
  have v11 : ((𝔇).scr hV 11).val = (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc + 11 := rfl
  have v12 : ((𝔇).scr hV 12).val = (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc + 12 := rfl
  have vrs : ∀ i : Fin 5, ((𝔇).rsT e.ext1 hV i).val = (𝔇).B + 19 + restPc se.extra sp.extra gW + i.val :=
    fun _ => rfl
  have vcs1 : (Dims.csSlots e.ext1.ext hV 1).val = (𝔇).B + 13 := rfl
  have vrf : ∀ i : Fin 5, (Dims.rfT e hV i).val = (𝔇).B + 14 + i.val := fun _ => rfl
  have vmT : ∀ i : Fin 5, (Dims.mT e hV i).val = (𝔇).B + 19 + restPc se.extra sp.extra gW + 5 + i.val :=
    fun _ => rfl
  have venc : ∀ kk : Fin 13, (Dims.encT (d := 𝔇) hV kk).val = (𝔇).F + (𝔇).rt + kk.val := fun _ => rfl
  
  have keep2 : ∀ x : Fin V, ¬ (𝔇).InClear se.extra sp.extra gW x.val → x ≠ (𝔇).scr hV 11 →
      x ≠ (𝔇).scr hV 12 → ¬ OutV (𝔇) se.extra sp.extra gW x.val → x ≠ (𝔇).rsT e.ext1 hV 2 →
      ¬ ((𝔇).F + (𝔇).rt ≤ x.val ∧ x.val ≤ (𝔇).F + (𝔇).rt + 4 ∧ x.val ≠ (𝔇).F + (𝔇).rt + 3) →
      A2 x = amb x ∧ H2 x = Hout x := by
    intro x h1 h2 h3 h4 h5 h6
    have hpc : ¬ ((𝔇).B + 19 ≤ x.val ∧ x.val < (𝔇).B + 19 + restPc se.extra sp.extra gW) := by
      intro h; apply h1; unfold SourceConstruction.Dims.InClear; omega
    have hcs : x ≠ Dims.csSlots e.ext1.ext hV 1 := by
      intro h; apply h1; rw [h]; exact cs1_in
    obtain ⟨a1, a2⟩ := frR x h4 hpc h5 hcs h6
    exact ⟨a1.trans (cOA x h1 h2 h3), a2.trans (cOH x h1 h2 h3)⟩
  have scrK : ∀ m : Fin 13, (m.val = 11 ∨ m.val = 12) →
      A2 ((𝔇).scr hV m) = install (Dims.clr2 e.ext1 hV) amb (PCJ6e421fabe2aa4155_SourceClear.join
        (fun _ => List.replicate Rc false) (List.replicate Rc true) (List.replicate (Rc+2) false)) ((𝔇).scr hV m) ∧
      H2 ((𝔇).scr hV m) = dockH (Dims.clr2 e.ext1 hV) Hout (fun _ => 0) ((𝔇).scr hV m) := by
    intro m hm
    have vm : ((𝔇).scr hV m).val = (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc + m.val := rfl
    apply frR
    · unfold OutV; rw [vm]; omega
    · rw [vm]; omega
    · exact ne_val (by rw [vm, vrs]; omega)
    · exact ne_val (by rw [vm, vcs1]; omega)
    · rw [vm]; omega
  have ecs1H : H2 (Dims.csSlots e.ext1.ext hV 1) = 0 := by
    rw [frRH _ (by unfold OutV; rw [vcs1]; omega) (by rw [vcs1]; omega)
      (curSlots_ne_below e.ext1 hV _ (by rw [vcs1]; omega))]
    exact cH _ cs1_in
  refine ⟨H2, A2, Av2, sR, hM2, ⟨res2⟩, e4, e02, ecs1, ecs1H, ecurT, ecurTH, ?_, ?_, ?_, ?_, ?_, keep2, ?_, ?_, ?_, e02L⟩
  · intro x hx
    have hin : (𝔇).InClear se.extra sp.extra gW x.val := by
      unfold SourceConstruction.Dims.InClear; omega
    obtain ⟨a1, a2⟩ := frR x (by unfold OutV; omega) (by omega) (ne_val (by rw [vrs]; omega))
      (ne_val (by rw [vcs1]; omega)) (by omega)
    rw [a1, a2]
    exact ⟨cA x hin, cH x hin⟩
  · rw [(scrK 11 (Or.inl rfl)).1]; exact cD
  · rw [(scrK 11 (Or.inl rfl)).2]; exact cDH
  · rw [(scrK 12 (Or.inr rfl)).1]; exact cL
  · rw [(scrK 12 (Or.inr rfl)).2]; exact cLH
  · intro x hin hz
    by_cases hO : OutV (𝔇) se.extra sp.extra gW x.val
    · obtain ⟨g1, g2⟩ := dG x hO hz
      rw [cH x hin] at g1
      exact ⟨g2, by omega⟩
    · by_cases hc1 : x = Dims.csSlots e.ext1.ext hV 1
      · rw [hc1, ecs1, ecs1H, ZeroPadding.pad_length, List.length_replicate]
        refine ⟨?_, by omega⟩
        split_ifs <;> omega
      · have hpc : ¬ ((𝔇).B + 19 ≤ x.val ∧ x.val < (𝔇).B + 19 + restPc se.extra sp.extra gW) := by
          unfold SourceConstruction.Dims.InZ at hz; unfold OutV at hO; unfold restPc at *; omega
        have hr2 : x ≠ (𝔇).rsT e.ext1 hV 2 := ne_val (by
          unfold SourceConstruction.Dims.InClear at hin; rw [vrs]; omega)
        have hen : ¬ ((𝔇).F + (𝔇).rt ≤ x.val ∧ x.val ≤ (𝔇).F + (𝔇).rt + 4 ∧ x.val ≠ (𝔇).F + (𝔇).rt + 3) := by
          unfold SourceConstruction.Dims.InClear at hin; omega
        obtain ⟨a1, a2⟩ := frR x hO hpc hr2 hc1 hen
        rw [a1, a2, cA x hin, cH x hin, List.length_replicate]
        exact ⟨le_refl _, by omega⟩
  · intro x hz
    have hin : (𝔇).InClear se.extra sp.extra gW x.val := Dims.InZ_clear hz
    obtain ⟨b1, b2⟩ := dirty_bound sR x
    rw [cA x hin, List.length_replicate, cH x hin, Nat.zero_add] at b1
    rw [cH x hin] at b2
    exact ⟨b1, by omega⟩
  · intro kk
    obtain ⟨n1, n2, n3⟩ := hiEnc kk
    have := kk.isLt
    rw [frRH _ (notOut_enc (𝔇) se.extra sp.extra gW kk.val kk.isLt) (by rw [venc]; omega)
      (curSlots_ne_below e.ext1 hV _ (by rw [venc]; omega))]
    exact cOH _ n1 n2 n3

theorem prologue_run5 {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) vE)
    (sp : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) vP) {gW : Nat}
    (e : (𝔇).RestExt2 se.extra sp.extra gW) {V : Nat} (hV : (𝔇).U ≤ V)
    {s7 : Nat} (g7M : Machine V s7) (g7cost : Nat → Nat)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits))
    (L target : Nat) (mode : Bool) (Rc b : Nat)
    (layoutAt : ∀ m : Nat, Packets.Layout (decompositionOf sources)
      ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources))
      (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode m)))
    (capsAt : Nat → RowCaps)
    (K : Fin V → Prop) (K0 : Fin V → List Bool) (KH0 : Fin V → Nat)
    (hG7 : ResidentRunH g7M g7cost mask (packets (decompositionOf sources))
      (rows (decompositionOf sources) (printerOf sources))
      ((𝔇).maskSlots hV) ((𝔇).pslots hV) ((𝔇).slot hV) ((𝔇).ret hV) ((𝔇).scr hV 0) ((𝔇).scr hV 1)
      ((𝔇).familySlots hV) ((𝔇).poolSlots hV) (Dims.rewind2Slots e.ext1.ext hV)
      ((𝔇).scr hV 5) ((𝔇).scr hV 6) ((𝔇).scr hV 7) ((𝔇).scr hV 8) ((𝔇).scr hV 9) ((𝔇).scr hV 10)
      (Dims.lenTape e.ext1.ext hV) coordinate ph ci L target mode Rc b
      ((𝔇).pcT e.ext1 hV ⟨70, by unfold restPc; omega⟩)
      (fun i => (𝔇).pcT e.ext1 hV ⟨61 + i.val, by have := i.isLt; unfold restPc; omega⟩) layoutAt capsAt
      (Dims.Rpad (d := 𝔇) (eX := se.extra) (pX := sp.extra) (gW := gW) (V := V) Rc)
      (RestIn4 (𝔇) se.extra sp.extra gW Rc ((𝔇).pcT e.ext1 hV ⟨64, by unfold restPc; omega⟩) K K0 KH0)
      (fun x => OutV (𝔇) se.extra sp.extra gW x.val))
    (j : Nat) (hj : j + 1 ≤ (monomials coordinate ph ci).length) (hRc : j + 1 + 3 ≤ Rc)
    (w cW cQ Mb Ms cB cS : Nat) (M : Fin 5 → List Bool) (hMl : ∀ i, (M i).length = Rc)
    (Hout : Fin V → Nat) (amb : Fin V → List Bool)
    (hK : ∀ x, K x → amb x = K0 x ∧ Hout x = KH0 x) (hKpos : ∀ x, K x → x.val < (𝔇).F ∨ (𝔇).B + 19 + restPc se.extra sp.extra gW + 10 ≤ x.val)
    (hMb : Mb ≤ Rc) (hMs : Ms ≤ Rc)
    (hcurT : amb ((𝔇).rsT e.ext1 hV 2) = ZeroPadding.pad Rc (UnaryTemplate.tape j))
    (hcurTH : Hout ((𝔇).rsT e.ext1 hV 2) = 0)
    (henc : ∀ kk : Fin 13, (kk.val < 3 ∨ kk.val = 4) → (amb (Dims.encT (d := 𝔇) hV kk)).length ≤ Rc)
    (hencH : ∀ kk : Fin 13, (kk.val < 3 ∨ kk.val = 4) → Hout (Dims.encT (d := 𝔇) hV kk) = 0)
    (hW : amb ((𝔇).rsT e.ext1 hV 3) = ZeroPadding.pad cW (List.replicate w true))
    (hWH : Hout ((𝔇).rsT e.ext1 hV 3) = 0)
    (hQ : amb ((𝔇).rsT e.ext1 hV 4) = ZeroPadding.pad cQ (List.replicate q true))
    (hQH : Hout ((𝔇).rsT e.ext1 hV 4) = 0)
    (hbig : amb ((𝔇).rsT e.ext1 hV 0) = ZeroPadding.pad cB (List.replicate Mb true))
    (hbigH : Hout ((𝔇).rsT e.ext1 hV 0) = 0)
    (hsmall : amb ((𝔇).rsT e.ext1 hV 1) = ZeroPadding.pad cS (List.replicate Ms true))
    (hsmallH : Hout ((𝔇).rsT e.ext1 hV 1) = 0)
    (hm : ∀ i, amb (Dims.mT e hV i) = M i) (hmH : ∀ i, Hout (Dims.mT e hV i) = 0)
    (hrfA : ∀ i, (amb (Dims.rfT e hV i)).length ≤ Rc) (hrfH : ∀ i, Hout (Dims.rfT e hV i) ≤ Rc)
    (hlog : 2 * ((requestAt coordinate ph ci L target mode (j+1)).input (decompositionOf sources)).length + 1 ≤ Rc)
    (he1 : 1 ≤ vE (requestAt coordinate ph ci L target mode (j+1)))
    (hpw : (CloseoutRowsCountBinary.bits (vP (requestAt coordinate ph ci L target mode (j+1)))).length ≤ w)
    (hfirst : vP (requestAt coordinate ph ci L target mode (j+1)) * 2^(natBitLength (vE (requestAt coordinate ph ci L target mode (j+1)))) < 2^w)
    (hsecond : vP (requestAt coordinate ph ci L target mode (j+1)) * vE (requestAt coordinate ph ci L target mode (j+1)) * 2^(q+1) < 2^w) :
    ∃ (H3 : Fin V → Nat) (A3 : Fin V → List Bool) (Av3 : Fin V → List Bool),
      Step (Composition.machine (restMachine se sp e.ext1 hV g7M) (refreshMachine e hV)) ((cursorCost j + 1 + (g7cost (j+1) + 1 + backCost se sp (requestAt coordinate ph ci L target mode (j+1)) Rc w q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length Mb Ms)) + 1 + refreshCost Rc)
        (dockH (Dims.clr2 e.ext1 hV) Hout (fun _ => 0))
        (install (Dims.clr2 e.ext1 hV) amb (PCJ6e421fabe2aa4155_SourceClear.join (fun _ => List.replicate Rc false)
          (List.replicate Rc true) (List.replicate (Rc+2) false))) H3 A3 ∧
      (∀ x, A3 x = ZeroPadding.pad (Dims.Rpad (d := 𝔇) (eX := se.extra) (pX := sp.extra) (gW := gW) (V := V) Rc x)
        (Av3 x)) ∧
      Nonempty (Resident mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources))
        ((𝔇).maskSlots hV) ((𝔇).pslots hV) ((𝔇).slot hV) ((𝔇).ret hV) ((𝔇).scr hV 0) ((𝔇).scr hV 1)
        ((𝔇).familySlots hV) ((𝔇).poolSlots hV) (Dims.rewind2Slots e.ext1.ext hV)
        ((𝔇).scr hV 5) ((𝔇).scr hV 6) ((𝔇).scr hV 7) ((𝔇).scr hV 8) ((𝔇).scr hV 9) ((𝔇).scr hV 10)
        (Dims.lenTape e.ext1.ext hV) (requestAt coordinate ph ci L target mode (j+1)) (layoutAt (j+1)) (capsAt (j+1))
        H3 Av3) ∧
      A3 (Dims.encT (d := 𝔇) hV 4) = ZeroPadding.pad Rc (RepairOrdinary.frame (SignedSortKey.binary w
        (vP (requestAt coordinate ph ci L target mode (j+1)) * vE (requestAt coordinate ph ci L target mode (j+1)) * 2^q))) ∧
      (∀ hm : j + 1 < (monomials coordinate ph ci).length, ∀ i : Fin 3, A3 (Dims.encT (d := 𝔇) hV ⟨i.val, by omega⟩) =
        ZeroPadding.pad Rc (RepairOrdinary.frame (CloseoutRowsEstimatorCoefficients.Stream.recordFields b
          (CloseoutFinalC10SupplierCalls.coefficientEstimate ((monomials coordinate ph ci)[j+1]).coefficient)
          0 0 ⟨i.val, by omega⟩))) ∧
      A3 (Dims.csSlots e.ext1.ext hV 1) = ZeroPadding.pad Rc (List.replicate (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length then Mb else Ms) true) ∧
      H3 (Dims.csSlots e.ext1.ext hV 1) = 0 ∧
      A3 ((𝔇).rsT e.ext1 hV 2) = ZeroPadding.pad Rc (UnaryTemplate.tape (j+1)) ∧ H3 ((𝔇).rsT e.ext1 hV 2) = 0 ∧
      (∀ i, A3 (Dims.rfT e hV i) = M i) ∧ H3 (Dims.rfT e hV 0) = 0 ∧
      (∀ i : Fin 5, i.val ≠ 0 → H3 (Dims.rfT e hV i) = 1) ∧
      (∀ x : Fin V, (((𝔇).F ≤ x.val ∧ x.val < (𝔇).F + (𝔇).rt) ∨ ((𝔇).B + 1 ≤ x.val ∧ x.val ≤ (𝔇).B + 12)) →
        A3 x = List.replicate Rc false ∧ H3 x = 0) ∧
      A3 ((𝔇).scr hV 11) = List.replicate Rc true ∧ H3 ((𝔇).scr hV 11) = 0 ∧
      A3 ((𝔇).scr hV 12) = List.replicate (Rc+2) false ∧ H3 ((𝔇).scr hV 12) = 0 ∧
      (∀ x : Fin V, ¬ (𝔇).InClear se.extra sp.extra gW x.val → x ≠ (𝔇).scr hV 11 → x ≠ (𝔇).scr hV 12 →
        ¬ OutV (𝔇) se.extra sp.extra gW x.val → x ≠ (𝔇).rsT e.ext1 hV 2 →
        ¬ ((𝔇).F + (𝔇).rt ≤ x.val ∧ x.val ≤ (𝔇).F + (𝔇).rt + 4 ∧ x.val ≠ (𝔇).F + (𝔇).rt + 3) →
        (∀ i, Dims.rfT e hV i ≠ x) → A3 x = amb x ∧ H3 x = Hout x) ∧
      (∀ x : Fin V, (𝔇).InDirt se.extra sp.extra gW x.val → ¬ (𝔇).InZ se.extra sp.extra x.val →
        (A3 x).length ≤ Rc ∧ H3 x ≤ cursorCost j + 1 + g7cost (j+1) + 1) ∧
      (∀ x : Fin V, (𝔇).InZ se.extra sp.extra x.val → (A3 x).length ≤ max Rc ((cursorCost j + 1 + (g7cost (j+1) + 1 + backCost se sp (requestAt coordinate ph ci L target mode (j+1)) Rc w q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length Mb Ms)) + 1) ∧ H3 x ≤ (cursorCost j + 1 + (g7cost (j+1) + 1 + backCost se sp (requestAt coordinate ph ci L target mode (j+1)) Rc w q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length Mb Ms))) ∧
      (∀ kk : Fin 13, H3 (Dims.encT (d := 𝔇) hV kk) = Hout (Dims.encT (d := 𝔇) hV kk)) ∧
      (∀ i : Fin 3, (A3 (Dims.encT (d := 𝔇) hV ⟨i.val, by omega⟩)).length ≤ Rc) := by
  classical
  have vG : (𝔇).G = (𝔇).F + (𝔇).rt + 13 := rfl
  have vB : (𝔇).B = (𝔇).G + (𝔇).R1 + 410 + (𝔇).w + (𝔇).tc := rfl
  have vp : (𝔇).pscr = (𝔇).R1 + 408 + (𝔇).w + (𝔇).tc := rfl
  have vPc : restPc se.extra sp.extra gW = 71 + se.extra + sp.extra + gW := rfl
  have hres2 := e.hres2
  have hF := e.ext1.ext.hF
  obtain ⟨H2, A2, Av2, sCR, hM2, ⟨res2⟩, e4, e02, ecs1, ecs1H, ecurT, ecurTH, bl2, a11, h11, a12, h12, keep2, dirt2, dirtZ2, encH2, e02L⟩ :=
    prologue_rest5 mask packets rows sources res p k r se sp e hV g7M g7cost coordinate ph ci L target mode Rc b layoutAt capsAt K K0 KH0 hG7 j hj hRc w cW cQ Mb Ms cB cS Hout amb hK hKpos hMb hMs hcurT hcurTH henc hencH hW hWH hQ hQH hbig hbigH hsmall hsmallH hlog he1 hpw hfirst hsecond
  -- values
  have v11 : ((𝔇).scr hV 11).val = (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc + 11 := rfl
  have v12 : ((𝔇).scr hV 12).val = (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc + 12 := rfl
  have vrs : ∀ i : Fin 5, ((𝔇).rsT e.ext1 hV i).val = (𝔇).B + 19 + restPc se.extra sp.extra gW + i.val :=
    fun _ => rfl
  have vcs1 : (Dims.csSlots e.ext1.ext hV 1).val = (𝔇).B + 13 := rfl
  have vrf : ∀ i : Fin 5, (Dims.rfT e hV i).val = (𝔇).B + 14 + i.val := fun _ => rfl
  have vmT : ∀ i : Fin 5, (Dims.mT e hV i).val = (𝔇).B + 19 + restPc se.extra sp.extra gW + 5 + i.val :=
    fun _ => rfl
  have venc : ∀ kk : Fin 13, (Dims.encT (d := 𝔇) hV kk).val = (𝔇).F + (𝔇).rt + kk.val := fun _ => rfl
  have rfNotClear : ∀ i : Fin 5, ¬ (𝔇).InClear se.extra sp.extra gW (Dims.rfT e hV i).val := by
    intro i; have := i.isLt; unfold SourceConstruction.Dims.InClear; rw [vrf]; omega
  have rfK : ∀ i : Fin 5, A2 (Dims.rfT e hV i) = amb (Dims.rfT e hV i) ∧
      H2 (Dims.rfT e hV i) = Hout (Dims.rfT e hV i) := by
    intro i
    have := i.isLt
    apply keep2
    · exact rfNotClear i
    · exact ne_val (by rw [vrf, v11]; omega)
    · exact ne_val (by rw [vrf, v12]; omega)
    · unfold OutV; rw [vrf]; omega
    · exact ne_val (by rw [vrf, vrs]; omega)
    · rw [vrf]; omega
  have mK : ∀ i : Fin 5, A2 (Dims.mT e hV i) = amb (Dims.mT e hV i) ∧
      H2 (Dims.mT e hV i) = Hout (Dims.mT e hV i) := by
    intro i
    have := i.isLt
    apply keep2
    · exact mT_notClear e hV i
    · exact ne_val (by rw [vmT, v11]; omega)
    · exact ne_val (by rw [vmT, v12]; omega)
    · exact mT_notOut e hV i
    · exact ne_val (by rw [vmT, vrs]; omega)
    · rw [vmT]; omega
  -- 3. the refresh
  obtain ⟨H3, A3, sF, fv, f0, f14, frF⟩ := refresh_run e hV Rc M hMl H2 A2
    (fun i => by rw [(rfK i).1]; exact hrfA i) (fun i => by rw [(rfK i).2]; exact hrfH i)
    a11 h11 a12 h12
    (fun i => by rw [(mK i).1]; exact hm i) (fun i => by rw [(mK i).2]; exact hmH i)
  have rfNe : ∀ x : Fin V, (x.val < (𝔇).B + 14 ∨ (𝔇).B + 18 < x.val) → ∀ i, Dims.rfT e hV i ≠ x := by
    intro x hx i h
    have := i.isLt
    have hv := congrArg Fin.val h
    rw [vrf] at hv
    omega
  
  let Av3 : Fin V → List Bool := fun x => if (∃ i, Dims.rfT e hV i = x) then A3 x else Av2 x
  have hM3 : ∀ x, A3 x = ZeroPadding.pad (Dims.Rpad (d := 𝔇) (eX := se.extra) (pX := sp.extra) (gW := gW)
      (V := V) Rc x) (Av3 x) := by
    intro x
    by_cases hx : ∃ i, Dims.rfT e hV i = x
    · obtain ⟨i, hi⟩ := hx
      simp only [Av3, if_pos (⟨i, hi⟩ : ∃ i, Dims.rfT e hV i = x)]
      rw [← hi]
      simp only [Dims.Rpad, if_neg (rfNotClear i), ZeroPadding.pad_zero]
    · simp only [Av3, if_neg hx]
      rw [(frF x (fun i h => hx ⟨i, h⟩)).1]
      exact hM2 x
  have lowRf : ∀ x : Fin V, LowT (𝔇) x.val → ∀ i, Dims.rfT e hV i ≠ x := by
    intro x hx
    apply rfNe
    left
    unfold LowT at hx
    omega
  have avT : ∀ x : Fin V, LowT (𝔇) x.val → Av3 x = Av2 x := by
    intro x hx
    have hn : ¬ ∃ i, Dims.rfT e hV i = x := by
      intro hh
      obtain ⟨i, h⟩ := hh
      exact lowRf x hx i h
    simp only [Av3, if_neg hn]
  have hT : ∀ x : Fin V, LowT (𝔇) x.val → H3 x = H2 x := fun x hx => (frF x (lowRf x hx)).2
  obtain ⟨res3⟩ := resident_keep_low mask packets rows sources res p k r e.ext1.ext hV res2 avT hT
  -- 5. the exported facts
  have enc_off : ∀ kk : Fin 13, ∀ i, Dims.rfT e hV i ≠ Dims.encT (d := 𝔇) hV kk := by
    intro kk
    apply rfNe
    left; rw [venc]; have := kk.isLt; omega
  have cs1_off : ∀ i, Dims.rfT e hV i ≠ Dims.csSlots e.ext1.ext hV 1 := by
    apply rfNe; left; rw [vcs1]; omega
  have curT_off : ∀ i, Dims.rfT e hV i ≠ (𝔇).rsT e.ext1 hV 2 := by
    apply rfNe; right; rw [vrs]; omega
  refine ⟨H3, A3, Av3, sCR.seq sF, hM3, ⟨res3⟩, ?_, ?_, ?_, ?_, ?_, ?_, fv, f0, f14, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [(frF _ (enc_off 4)).1]; exact e4
  · intro hm i
    rw [(frF _ (enc_off _)).1]; exact e02 hm i
  · rw [(frF _ cs1_off).1]; exact ecs1
  · rw [(frF _ cs1_off).2]; exact ecs1H
  · rw [(frF _ curT_off).1]; exact ecurT
  · rw [(frF _ curT_off).2]; exact ecurTH
  · intro x hx
    have hoff : ∀ i, Dims.rfT e hV i ≠ x := rfNe x (by omega)
    rw [(frF x hoff).1, (frF x hoff).2]
    exact bl2 x hx
  · rw [(frF _ (fun i h => by have := congrArg Fin.val h; rw [vrf, v11] at this; omega)).1]; exact a11
  · rw [(frF _ (fun i h => by have := congrArg Fin.val h; rw [vrf, v11] at this; omega)).2]; exact h11
  · rw [(frF _ (fun i h => by have := congrArg Fin.val h; rw [vrf, v12] at this; omega)).1]; exact a12
  · rw [(frF _ (fun i h => by have := congrArg Fin.val h; rw [vrf, v12] at this; omega)).2]; exact h12
  · intro x h1 h2 h3 h4 h5 h6 h7
    obtain ⟨a1, a2⟩ := keep2 x h1 h2 h3 h4 h5 h6
    rw [(frF x h7).1, (frF x h7).2]
    exact ⟨a1, a2⟩
  · intro x hx hz
    unfold SourceConstruction.Dims.InDirt at hx
    by_cases hr : (𝔇).B + 14 ≤ x.val ∧ x.val ≤ (𝔇).B + 18
    · have hi : Dims.rfT e hV ⟨x.val - ((𝔇).B + 14), by omega⟩ = x := Fin.ext (by rw [vrf]; simp; omega)
      rw [← hi]
      refine ⟨by rw [fv, hMl], ?_⟩
      by_cases h0 : x.val - ((𝔇).B + 14) = 0
      · have e0 : (⟨x.val - ((𝔇).B + 14), by omega⟩ : Fin 5) = 0 := Fin.ext h0
        rw [e0, f0]; omega
      · rw [f14 _ h0]; omega
    · have hin : (𝔇).InClear se.extra sp.extra gW x.val := by
        rcases hx with h | h
        · exact h
        · exact absurd h hr
      have hoff : ∀ i, Dims.rfT e hV i ≠ x := rfNe x (by
        unfold SourceConstruction.Dims.InClear at hin; omega)
      rw [(frF x hoff).1, (frF x hoff).2]
      obtain ⟨b1, b2⟩ := dirt2 x hin hz
      exact ⟨b1, by omega⟩
  · intro x hz
    have hoff : ∀ i, Dims.rfT e hV i ≠ x := rfNe x (by unfold SourceConstruction.Dims.InZ at hz; omega)
    rw [(frF x hoff).1, (frF x hoff).2]
    exact dirtZ2 x hz
  · intro kk
    rw [(frF _ (enc_off kk)).2]
    exact encH2 kk
  · intro i
    rw [(frF _ (enc_off _)).1]; exact e02L i

end concrete

end
end NearCubicWires.SourceConstruction.Rest
end
