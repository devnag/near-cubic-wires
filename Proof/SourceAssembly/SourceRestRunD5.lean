import Proof.SourceAssembly.SourceRestRunD4

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

/-- **The refill prologue after the clear.** -/
theorem rest_run_d5 {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) vE)
    (sp : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) vP) {gW : Nat}
    (e : (𝔇).RestExt se.extra sp.extra gW) {V : Nat} (hV : (𝔇).U ≤ V)
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
      ((𝔇).familySlots hV) ((𝔇).poolSlots hV) (Dims.rewind2Slots e.ext hV)
      ((𝔇).scr hV 5) ((𝔇).scr hV 6) ((𝔇).scr hV 7) ((𝔇).scr hV 8) ((𝔇).scr hV 9) ((𝔇).scr hV 10)
      (Dims.lenTape e.ext hV) coordinate ph ci L target mode Rc b
      ((𝔇).pcT e hV ⟨70, by unfold restPc; omega⟩)
      (fun i => (𝔇).pcT e hV ⟨61 + i.val, by have := i.isLt; unfold restPc; omega⟩) layoutAt capsAt
      (Dims.Rpad (d := 𝔇) (eX := se.extra) (pX := sp.extra) (gW := gW) (V := V) Rc)
      (RestIn4 (𝔇) se.extra sp.extra gW Rc ((𝔇).pcT e hV ⟨64, by unfold restPc; omega⟩) K K0 KH0)
      (fun x => OutV (𝔇) se.extra sp.extra gW x.val))
    (j : Nat) (hj : j + 1 ≤ (monomials coordinate ph ci).length) (hRc : j + 1 + 3 ≤ Rc)
    (w cW cQ Mb Ms cB cS : Nat)
    (H : Fin V → Nat) (A : Fin V → List Bool)
    (hclr : ∀ x : Fin V, (𝔇).InClear se.extra sp.extra gW x.val → Rc ≤ (A x).length)
    (hpc : ∀ i : Fin (restPc se.extra sp.extra gW), A ((𝔇).pcT e hV i) = List.replicate Rc false ∧
      H ((𝔇).pcT e hV i) = 0)
    (hOut : ∀ x : Fin V, OutV (𝔇) se.extra sp.extra gW x.val → A x = List.replicate Rc false ∧ H x = 0)
    (hK : ∀ x, K x → A x = K0 x ∧ H x = KH0 x) (hKc : ∀ x, K x → ∀ i, curSlots e hV i ≠ x)
    (hclrB : ∀ x : Fin V, (𝔇).InClear se.extra sp.extra gW x.val → (∀ i, curSlots e hV i ≠ x) →
      A x = List.replicate Rc false ∧ H x = 0)
    (hcurT : A ((𝔇).rsT e hV 2) = ZeroPadding.pad Rc (UnaryTemplate.tape j)) (hcurTH : H ((𝔇).rsT e hV 2) = 0)
    (henc : ∀ kk : Fin 13, (kk.val < 3 ∨ kk.val = 4) → (A (Dims.encT (d := 𝔇) hV kk)).length ≤ Rc)
    (hencH : ∀ kk : Fin 13, (kk.val < 3 ∨ kk.val = 4) → H (Dims.encT (d := 𝔇) hV kk) = 0)
    (hW : A ((𝔇).rsT e hV 3) = ZeroPadding.pad cW (List.replicate w true)) (hWH : H ((𝔇).rsT e hV 3) = 0)
    (hQ : A ((𝔇).rsT e hV 4) = ZeroPadding.pad cQ (List.replicate q true)) (hQH : H ((𝔇).rsT e hV 4) = 0)
    (hdrv : A ((𝔇).scr hV 11) = List.replicate Rc true) (hdrvH : H ((𝔇).scr hV 11) = 0)
    (hlg : A ((𝔇).scr hV 12) = List.replicate (Rc+2) false) (hlgH : H ((𝔇).scr hV 12) = 0)
    (hbig : A ((𝔇).rsT e hV 0) = ZeroPadding.pad cB (List.replicate Mb true)) (hbigH : H ((𝔇).rsT e hV 0) = 0)
    (hsmall : A ((𝔇).rsT e hV 1) = ZeroPadding.pad cS (List.replicate Ms true))
    (hsmallH : H ((𝔇).rsT e hV 1) = 0)
    (hcs1 : A (Dims.csSlots e.ext hV 1) = List.replicate Rc false) (hcs1H : H (Dims.csSlots e.ext hV 1) = 0)
    (hlog : 2 * ((requestAt coordinate ph ci L target mode (j+1)).input (decompositionOf sources)).length + 1 ≤ Rc)
    (he1 : 1 ≤ vE (requestAt coordinate ph ci L target mode (j+1)))
    (hpw : (CloseoutRowsCountBinary.bits (vP (requestAt coordinate ph ci L target mode (j+1)))).length ≤ w)
    (hfirst : vP (requestAt coordinate ph ci L target mode (j+1)) *
      2^(natBitLength (vE (requestAt coordinate ph ci L target mode (j+1)))) < 2^w)
    (hsecond : vP (requestAt coordinate ph ci L target mode (j+1)) *
      vE (requestAt coordinate ph ci L target mode (j+1)) * 2^(q+1) < 2^w) :
    ∃ (H' : Fin V → Nat) (A' : Fin V → List Bool) (Av' : Fin V → List Bool),
      Step (restMachine se sp e hV g7M)
        (cursorCost j + 1 + (g7cost (j+1) + 1 + backCost se sp (requestAt coordinate ph ci L target mode (j+1))
          Rc w q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources)
            ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length
          Mb Ms)) H A H' A' ∧
      (∀ x, A' x = ZeroPadding.pad (Dims.Rpad (d := 𝔇) (eX := se.extra) (pX := sp.extra) (gW := gW) (V := V) Rc x)
        (Av' x)) ∧
      Nonempty (Resident mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources))
        ((𝔇).maskSlots hV) ((𝔇).pslots hV) ((𝔇).slot hV) ((𝔇).ret hV) ((𝔇).scr hV 0) ((𝔇).scr hV 1)
        ((𝔇).familySlots hV) ((𝔇).poolSlots hV) (Dims.rewind2Slots e.ext hV)
        ((𝔇).scr hV 5) ((𝔇).scr hV 6) ((𝔇).scr hV 7) ((𝔇).scr hV 8) ((𝔇).scr hV 9) ((𝔇).scr hV 10)
        (Dims.lenTape e.ext hV) (requestAt coordinate ph ci L target mode (j+1)) (layoutAt (j+1)) (capsAt (j+1))
        H' Av') ∧
      A' (Dims.encT (d := 𝔇) hV 4) = ZeroPadding.pad Rc (RepairOrdinary.frame (SignedSortKey.binary w
        (vP (requestAt coordinate ph ci L target mode (j+1)) * vE (requestAt coordinate ph ci L target mode (j+1)) *
          2^q))) ∧
      (∀ hm : j + 1 < (monomials coordinate ph ci).length, ∀ i : Fin 3, A' (Dims.encT (d := 𝔇) hV ⟨i.val, by omega⟩) =
        ZeroPadding.pad Rc (RepairOrdinary.frame (CloseoutRowsEstimatorCoefficients.Stream.recordFields b
          (CloseoutFinalC10SupplierCalls.coefficientEstimate ((monomials coordinate ph ci)[j+1]).coefficient)
          0 0 ⟨i.val, by omega⟩))) ∧
      A' (Dims.csSlots e.ext hV 1) = ZeroPadding.pad Rc (List.replicate
        (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources)
            ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length
          then Mb else Ms) true) ∧
      A' ((𝔇).rsT e hV 2) = ZeroPadding.pad Rc (UnaryTemplate.tape (j+1)) ∧ H' ((𝔇).rsT e hV 2) = 0 ∧
      (∀ x : Fin V, ¬ OutV (𝔇) se.extra sp.extra gW x.val →
        ¬ ((𝔇).B + 19 ≤ x.val ∧ x.val < (𝔇).B + 19 + restPc se.extra sp.extra gW) →
        x ≠ (𝔇).rsT e hV 2 → x ≠ Dims.csSlots e.ext hV 1 →
        ¬ ((𝔇).F + (𝔇).rt ≤ x.val ∧ x.val ≤ (𝔇).F + (𝔇).rt + 4 ∧ x.val ≠ (𝔇).F + (𝔇).rt + 3) →
        A' x = A x ∧ H' x = H x) ∧
      (∀ x : Fin V, ¬ OutV (𝔇) se.extra sp.extra gW x.val →
        ¬ ((𝔇).B + 19 + 71 ≤ x.val ∧ x.val < (𝔇).B + 19 + 71 + se.extra + sp.extra) →
        (∀ i, curSlots e hV i ≠ x) → H' x = H x) ∧
      (∀ x : Fin V, OutV (𝔇) se.extra sp.extra gW x.val → ¬ (𝔇).InZ se.extra sp.extra x.val →
        H' x ≤ H x + (cursorCost j + 1 + g7cost (j+1)) ∧ (A' x).length ≤ Rc) ∧
      (∀ i : Fin 3, (A' (Dims.encT (d := 𝔇) hV ⟨i.val, by omega⟩)).length ≤ Rc) := by
  classical

  have hres := e.hres
  have vPc : restPc se.extra sp.extra gW = 71 + se.extra + sp.extra + gW := rfl
  have vG : (𝔇).G = (𝔇).F + (𝔇).rt + 13 := rfl
  have vB : (𝔇).B = (𝔇).G + (𝔇).R1 + 410 + (𝔇).w + (𝔇).tc := rfl
  have vp : (𝔇).pscr = (𝔇).R1 + 408 + (𝔇).w + (𝔇).tc := rfl
  have vcur : ∀ i : Fin 3, (curSlots e hV i).val = (𝔇).B + 19 + restPc se.extra sp.extra gW + 2 ∨
      (curSlots e hV i).val = (𝔇).B + 19 + 64 ∨ (curSlots e hV i).val = (𝔇).B + 19 + 65 := by
    intro i; fin_cases i <;> simp [curSlots, SourceConstruction.Dims.pcT, SourceConstruction.Dims.rsT]
  have offCur : ∀ x : Fin V, x.val ≠ (𝔇).B + 19 + restPc se.extra sp.extra gW + 2 → x.val ≠ (𝔇).B + 19 + 64 →
      x.val ≠ (𝔇).B + 19 + 65 → ∀ i, curSlots e hV i ≠ x := by
    intro x a1 a2 a3 i h
    rcases vcur i with h' | h' | h' <;> rw [h] at h' <;> omega
  -- 1. the cursor
  have sC := cursor_run (curSlots e hV) (curSlots_injective e hV) j Rc (by omega) H A
    (by intro i; fin_cases i
        · exact hcurTH
        · exact (hpc _).2
        · exact (hpc _).2) hcurT (hpc _).1 (hpc _).1
  set Ac := install (curSlots e hV) A ![ZeroPadding.pad Rc (UnaryTemplate.tape (j+1)),
    ZeroPadding.pad Rc (List.replicate (j+1) true), List.replicate Rc false] with hAc
  have Aco : ∀ x, (∀ i, curSlots e hV i ≠ x) → Ac x = A x := fun x hx => install_other _ _ _ x hx
  have Ac_cur : Ac ((𝔇).pcT e hV ⟨64, by unfold restPc; omega⟩) = ZeroPadding.pad Rc (List.replicate (j+1) true) :=
    install_slot (curSlots e hV) (curSlots_injective e hV) A _ 1
  have Ac_curT : Ac ((𝔇).rsT e hV 2) = ZeroPadding.pad Rc (UnaryTemplate.tape (j+1)) :=
    install_slot (curSlots e hV) (curSlots_injective e hV) A _ 0
  have offCur_pc : ∀ i : Fin (restPc se.extra sp.extra gW), i.val ≠ 64 → i.val ≠ 65 →
      ∀ ii, curSlots e hV ii ≠ (𝔇).pcT e hV i := by
    intro i h1 h2
    have hi := i.isLt
    exact offCur _ (by show (𝔇).B + 19 + i.val ≠ _; omega) (by show (𝔇).B + 19 + i.val ≠ _; omega)
      (by show (𝔇).B + 19 + i.val ≠ _; omega)
  have offCur_low : ∀ x : Fin V, x.val < (𝔇).B + 19 → ∀ ii, curSlots e hV ii ≠ x := by
    intro x hx
    exact offCur x (by omega) (by omega) (by omega)
  
  have hin : RestIn (𝔇) se.extra sp.extra gW Rc ((𝔇).pcT e hV ⟨64, by unfold restPc; omega⟩) K K0 KH0 (j+1) H Ac := by
    refine ⟨fun x hx => ?_, Ac_cur, (hpc _).2, fun x hx => ?_⟩
    · rw [Aco x (offCur x (by unfold OutV at hx; omega) (by unfold OutV at hx; omega)
        (by unfold OutV at hx; omega))]
      exact hOut x hx
    · rw [Aco x (hKc x hx)]; exact hK x hx
  have hin4 : RestIn4 (𝔇) se.extra sp.extra gW Rc ((𝔇).pcT e hV ⟨64, by unfold restPc; omega⟩) K K0 KH0 (j+1) H Ac := by
    refine ⟨hin, fun x hx hc => ?_⟩
    by_cases h65 : x = (𝔇).pcT e hV ⟨65, by unfold restPc; omega⟩
    · subst h65
      exact ⟨install_slot (curSlots e hV) (curSlots_injective e hV) A _ 2, (hpc _).2⟩
    · have hoff : ∀ i, curSlots e hV i ≠ x := by
        intro i hi
        rcases vcur i with h | h | h
        · rw [hi] at h; unfold SourceConstruction.Dims.InClear at hx; rw [vPc] at h hx; omega
        · exact hc (by rw [← hi]; exact Fin.ext h)
        · exact h65 (by rw [← hi]; exact Fin.ext h)
      rw [Aco x hoff]; exact hclrB x hx hoff
  obtain ⟨H1, A1, Av, sG, hpad, ⟨res1⟩, hnTH, -, hcoefH, hcoefW, hfr, hOL⟩ := hG7 (j+1) hj H Ac hin4
  have fr1 : ∀ x : Fin V, ¬ OutV (𝔇) se.extra sp.extra gW x.val → (∀ i, curSlots e hV i ≠ x) →
      A1 x = A x ∧ H1 x = H x := by
    intro x h1 h2
    obtain ⟨a1, a2⟩ := hfr x h1
    exact ⟨a1.trans (Aco x h2), a2⟩
  have Rpad_clear : ∀ x : Fin V, (𝔇).InClear se.extra sp.extra gW x.val →
      Dims.Rpad (d := 𝔇) (eX := se.extra) (pX := sp.extra) (gW := gW) (V := V) Rc x = Rc := by
    intro x hx; simp only [Dims.Rpad, if_pos hx]
  have scr_clear : ∀ m : Fin 13, m.val ≤ 10 → (𝔇).InClear se.extra sp.extra gW ((𝔇).scr hV m).val := by
    intro m hm
    unfold SourceConstruction.Dims.InClear
    right; left
    show (𝔇).G ≤ (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc + m.val ∧ (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc + m.val < (𝔇).G + (𝔇).pscr
    omega
  
  have fr1_rs : ∀ i : Fin 5, i.val ≠ 2 → A1 ((𝔇).rsT e hV i) = A ((𝔇).rsT e hV i) ∧ H1 ((𝔇).rsT e hV i) = H ((𝔇).rsT e hV i) := by
    intro i hi
    have := i.isLt
    exact fr1 _ (notOut_rs (𝔇) se.extra sp.extra gW i.val)
      (offCur _ (by show (𝔇).B + 19 + restPc se.extra sp.extra gW + i.val ≠ _; omega)
        (by show (𝔇).B + 19 + restPc se.extra sp.extra gW + i.val ≠ _; omega)
        (by show (𝔇).B + 19 + restPc se.extra sp.extra gW + i.val ≠ _; omega))
  have fr1_enc : ∀ kk : Fin 13, A1 ((𝔇).encT hV kk) = A ((𝔇).encT hV kk) ∧ H1 ((𝔇).encT hV kk) = H ((𝔇).encT hV kk) := by
    intro kk
    have := kk.isLt
    exact fr1 _ (notOut_enc (𝔇) se.extra sp.extra gW kk.val kk.isLt)
      (offCur_low _ (by show (𝔇).F + (𝔇).rt + kk.val < _; omega))
  have fr1_scr : ∀ m : Fin 13, 11 ≤ m.val → A1 ((𝔇).scr hV m) = A ((𝔇).scr hV m) ∧ H1 ((𝔇).scr hV m) = H ((𝔇).scr hV m) := by
    intro m hm
    have := m.isLt
    exact fr1 _ (notOut_scr (𝔇) se.extra sp.extra gW m.val hm (by omega))
      (offCur_low _ (by show (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc + m.val < _; omega))
  have fr1_cs1 : A1 (Dims.csSlots e.ext hV 1) = A (Dims.csSlots e.ext hV 1) ∧
      H1 (Dims.csSlots e.ext hV 1) = H (Dims.csSlots e.ext hV 1) :=
    fr1 _ (notOut_cs1 (𝔇) se.extra sp.extra gW) (offCur_low _ (by show (𝔇).B + 13 < _; omega))
  
  obtain ⟨H', A', sB, bEnc4, bEnc, bCs1, bFr, bH⟩ := back_run se sp e hV
    (requestAt coordinate ph ci L target mode (j+1)) Rc (max Rc res1.capS1) (max Rc res1.capD1) w q cW cQ
    (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources)
      ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length
    (max Rc res1.capLen) Mb Ms cB cS H1 A1
    (by rw [hpad, Rpad_clear _ (scr_clear 5 (by decide)), res1.w_input, Uniform.pad_pad])
    (by rw [hpad, Rpad_clear _ (scr_clear 6 (by decide)), res1.w_inputLen, Uniform.pad_pad])
    res1.hH_s1 res1.hH_d1 hlog
    (by
      intro i hi
      rw [(fr1 _ (notOut_pcv (𝔇) se.extra sp.extra gW i.val (by omega)) (offCur_pc i (by omega) (by omega))).1]
      exact (hpc i).1)
    (by
      intro i hi
      by_cases hc : 61 ≤ i.val ∧ i.val < 64
      · have e1 : i = ⟨61 + (i.val - 61), by unfold restPc; omega⟩ := Fin.ext (by simp; omega)
        rw [e1]; exact hcoefH ⟨i.val - 61, by omega⟩
      by_cases h70 : i.val = 70
      · rw [show i = ⟨70, by unfold restPc; omega⟩ from Fin.ext h70]; exact hnTH
      by_cases h64 : i.val = 64 ∨ i.val = 65
      · rw [(hfr _ (notOut_pcv (𝔇) se.extra sp.extra gW i.val (by omega))).2]; exact (hpc i).2
      · rw [(fr1 _ (notOut_pcv (𝔇) se.extra sp.extra gW i.val (by omega)) (offCur_pc i (by omega) (by omega))).2]
        exact (hpc i).2)
    (by
      intro kk
      have hle := hOL ((𝔇).pcT e hV ⟨61 + kk.val, by unfold restPc; omega⟩)
        (isOut_coef (𝔇) se.extra sp.extra gW (61 + kk.val) (by omega))
      have h0 := CloseoutFinalC10WorkerEmitShape.Step_length_le sG ((𝔇).pcT e hV ⟨61 + kk.val, by unfold restPc; omega⟩)
      rw [Aco _ (offCur_pc _ (by simp; omega) (by simp; omega)), (hpc _).1, List.length_replicate] at h0
      omega)
    (fun kk hk => by rw [(fr1_enc kk).1]; exact henc kk hk)
    (fun kk hk => by rw [(fr1_enc kk).2]; exact hencH kk hk)
    (by rw [(fr1_rs 3 (by decide)).1]; exact hW) (by rw [(fr1_rs 3 (by decide)).2]; exact hWH)
    (by rw [(fr1_rs 4 (by decide)).1]; exact hQ) (by rw [(fr1_rs 4 (by decide)).2]; exact hQH)
    (by rw [(fr1_scr 11 (by decide)).1]; exact hdrv) (by rw [(fr1_scr 11 (by decide)).2]; exact hdrvH)
    (by rw [(fr1_scr 12 (by decide)).1]; exact hlg) (by rw [(fr1_scr 12 (by decide)).2]; exact hlgH)
    (by rw [(fr1_rs 0 (by decide)).1]; exact hbig) (by rw [(fr1_rs 0 (by decide)).2]; exact hbigH)
    (by rw [(fr1_rs 1 (by decide)).1]; exact hsmall) (by rw [(fr1_rs 1 (by decide)).2]; exact hsmallH)
    (by
      have hlc : (𝔇).InClear se.extra sp.extra gW (Dims.lenTape e.ext hV).val := by
        unfold SourceConstruction.Dims.InClear; right; right; left
        show (𝔇).B ≤ (𝔇).B ∧ (𝔇).B < (𝔇).B + 14
        omega
      rw [hpad, Rpad_clear _ hlc, res1.w_len, Uniform.pad_pad])
    res1.hH_len
    (by rw [fr1_cs1.1, hcs1]; exact (Finish.blank_is_padded Rc).symm)
    (by rw [fr1_cs1.2]; exact hcs1H)
    he1 hpw hfirst hsecond
  -- 4. the padded exit
  let Av' : Fin V → List Bool := fun x => if A' x = A1 x then Av x else A' x
  have hM' : ∀ x, A' x = ZeroPadding.pad (Dims.Rpad (d := 𝔇) (eX := se.extra) (pX := sp.extra) (gW := gW)
      (V := V) Rc x) (Av' x) := by
    intro x
    by_cases hx : A' x = A1 x
    · simp only [Av', if_pos hx]; rw [hx]; exact hpad x
    · simp only [Av', if_neg hx]
      by_cases hc : (𝔇).InClear se.extra sp.extra gW x.val
      · rw [Rpad_clear x hc]
        have hl : Rc ≤ (A' x).length := by
          have h0 := CloseoutFinalC10WorkerEmitShape.Step_length_le ((sC.seq sG).seq sB) x
          exact (hclr x hc).trans h0
        simp only [ZeroPadding.pad, Nat.sub_eq_zero_of_le hl, List.replicate_zero, List.append_nil]
      · simp only [Dims.Rpad, if_neg hc, ZeroPadding.pad_zero]
  have keepT : ∀ x : Fin V, LowT (𝔇) x.val → A' x = A1 x ∧ H' x = H1 x := by
    intro x hx
    obtain ⟨b1, b2, b3, b4⟩ := low_back hx se.extra sp.extra
    exact ⟨bFr x (ne_val (by show x.val ≠ (𝔇).B + 13; exact b1)) (by omega) b3, bH x b4⟩
  have avT : ∀ x : Fin V, LowT (𝔇) x.val → Av' x = Av x := by
    intro x hx
    simp only [Av', if_pos (keepT x hx).1]
  have res' := resident_transport res1 H' Av'
    (fun jj => avT _ (low_slot hV jj)) (fun ii => avT _ (low_mask hV ii)) (fun jj => avT _ (low_pslots hV jj))
    (fun ii => avT _ (low_pool hV ii)) (fun ii => avT _ (low_family hV ii)) (fun ii => avT _ (low_rewind e.ext hV ii))
    (fun ii => avT _ (low_ret hV ii)) (avT _ (low_scr hV 0 (by decide))) (avT _ (low_scr hV 1 (by decide)))
    (avT _ (low_scr hV 5 (by decide))) (avT _ (low_scr hV 6 (by decide))) (avT _ (low_scr hV 7 (by decide)))
    (avT _ (low_scr hV 8 (by decide))) (avT _ (low_scr hV 9 (by decide))) (avT _ (low_scr hV 10 (by decide)))
    (avT _ (low_len e.ext hV))
    (fun jj => (keepT _ (low_slot hV jj)).2) (fun ii => (keepT _ (low_mask hV ii)).2)
    (fun jj => (keepT _ (low_pslots hV jj)).2) (fun ii => (keepT _ (low_pool hV ii)).2)
    (fun ii => (keepT _ (low_family hV ii)).2) (fun ii => (keepT _ (low_rewind e.ext hV ii)).2)
    (fun ii => (keepT _ (low_ret hV ii)).2) (keepT _ (low_scr hV 0 (by decide))).2
    (keepT _ (low_scr hV 1 (by decide))).2 (keepT _ (low_scr hV 5 (by decide))).2
    (keepT _ (low_scr hV 6 (by decide))).2 (keepT _ (low_scr hV 7 (by decide))).2
    (keepT _ (low_scr hV 8 (by decide))).2 (keepT _ (low_scr hV 9 (by decide))).2
    (keepT _ (low_scr hV 10 (by decide))).2 (keepT _ (low_len e.ext hV)).2
  have curT_out : ¬ OutV (𝔇) se.extra sp.extra gW ((𝔇).rsT e hV 2).val := notOut_rs (𝔇) se.extra sp.extra gW 2
  have v_rs2 : ((𝔇).rsT e hV 2).val = (𝔇).B + 19 + restPc se.extra sp.extra gW + 2 := rfl
  have v_cs1 : (Dims.csSlots e.ext hV 1).val = (𝔇).B + 13 := rfl
  refine ⟨H', A', Av', sC.seq (sG.seq sB), hM', ⟨res'⟩, bEnc4, ?_, bCs1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hm i
    rw [bEnc i]
    exact (hcoefW hm) i
  · have c1 : ((𝔇).rsT e hV 2).val ≠ (Dims.csSlots e.ext hV 1).val := by rw [v_rs2, v_cs1]; omega
    have c2 : ¬ ((𝔇).B + 19 ≤ ((𝔇).rsT e hV 2).val ∧
        ((𝔇).rsT e hV 2).val < (𝔇).B + 19 + 71 + se.extra + sp.extra) := by rw [v_rs2]; omega
    have c3 : ¬ ((𝔇).F + (𝔇).rt ≤ ((𝔇).rsT e hV 2).val ∧ ((𝔇).rsT e hV 2).val ≤ (𝔇).F + (𝔇).rt + 4 ∧
        ((𝔇).rsT e hV 2).val ≠ (𝔇).F + (𝔇).rt + 3) := by rw [v_rs2]; omega
    rw [bFr ((𝔇).rsT e hV 2) (ne_val c1) c2 c3, (hfr _ curT_out).1]
    exact Ac_curT
  · have c4 : ¬ ((𝔇).B + 19 + 71 ≤ ((𝔇).rsT e hV 2).val ∧
        ((𝔇).rsT e hV 2).val < (𝔇).B + 19 + 71 + se.extra + sp.extra) := by rw [v_rs2]; omega
    rw [bH ((𝔇).rsT e hV 2) c4, (hfr _ curT_out).2]
    exact hcurTH
  · intro x h1 h2 h3 h4 h5
    have hcx : ∀ i, curSlots e hV i ≠ x := offCur x
      (fun h => h3 (Fin.ext (by rw [h]; rfl))) (by omega) (by omega)
    exact ⟨(bFr x h4 (by omega) h5).trans (fr1 x h1 hcx).1, (bH x (by omega)).trans (fr1 x h1 hcx).2⟩
  · intro x h1 h2 h3
    exact (bH x h2).trans (fr1 x h1 h3).2
  · intro x hO hZ
    have hZ' : ¬ ((𝔇).B + 19 ≤ x.val ∧ x.val < (𝔇).B + 19 + 71 + se.extra + sp.extra) := by
      unfold SourceConstruction.Dims.InZ at hZ; omega
    have hcx : ∀ i, curSlots e hV i ≠ x := by
      intro i h
      rcases vcur i with h' | h' | h'
      · exact curT_out (by rw [h] at h'; rw [v_rs2, ← h']; exact hO)
      · rw [h] at h'; omega
      · rw [h] at h'; omega
    have hc1 : x ≠ Dims.csSlots e.ext hV 1 := by
      intro h; apply notOut_cs1 (𝔇) se.extra sp.extra gW; rw [← v_cs1, ← h]; exact hO
    have hen : ¬ ((𝔇).F + (𝔇).rt ≤ x.val ∧ x.val ≤ (𝔇).F + (𝔇).rt + 4 ∧ x.val ≠ (𝔇).F + (𝔇).rt + 3) := by
      intro h
      apply notOut_enc (𝔇) se.extra sp.extra gW (x.val - ((𝔇).F + (𝔇).rt)) (by omega)
      rw [show (𝔇).F + (𝔇).rt + (x.val - ((𝔇).F + (𝔇).rt)) = x.val by omega]; exact hO
    have hdb := (dirty_bound (sC.seq sG) x).2
    have hH' : H' x = H1 x := bH x (by omega)
    have hA' : A' x = A1 x := bFr x hc1 hZ' hen
    refine ⟨by rw [hH']; exact hdb, by rw [hA']; exact hOL x hO⟩
  · intro i
    rw [bEnc i]
    exact hOL _ (isOut_coef (𝔇) se.extra sp.extra gW (61 + i.val) (by omega))

end concrete

end
end NearCubicWires.SourceConstruction.Rest
end
