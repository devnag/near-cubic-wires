import Proof.SourceAssembly.SourceFactorSelWordsHostWR
import Proof.SourceAssembly.SourceRestIn4

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.Rest
open NearCubicWires.SourceFactorSel.Words NearCubicWires.SourceFactorSel.WordsHost
namespace NearCubicWires.SourceFactorSel.AtS
noncomputable section
attribute [local irreducible] NearCubicWires.P1TopDownPaidPayload.tapes

section S
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources) (res : Nat)
  {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources res p k r

def layS {eX pX gW : Nat} (e : (𝔇).RestExt3 eX pX gW) {V : Nat} (hV : (𝔇).U ≤ V) (gG7 : Nat) :
    HostLay mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) V where
  maskSlots := (𝔇).maskSlots hV
  pslots := (𝔇).pslots hV
  slot := (𝔇).slot hV
  ret := (𝔇).ret hV
  retDrv := (𝔇).scr hV 0
  log := (𝔇).scr hV 1
  familySlots := (𝔇).familySlots hV
  poolSlots := (𝔇).poolSlots hV
  rewindSlots := Dims.rewind2Slots e.ext2.ext1.ext hV
  s1 := (𝔇).scr hV 5
  d1 := (𝔇).scr hV 6
  l1 := (𝔇).scr hV 7
  s2 := (𝔇).scr hV 8
  d2 := (𝔇).scr hV 9
  l2 := (𝔇).scr hV 10
  lenTape := Dims.lenTape e.ext2.ext1.ext hV
  F := (𝔇).F
  rt := (𝔇).rt
  sp := (𝔇).sp
  G := (𝔇).G
  R1 := (𝔇).R1
  descV := (𝔇).descV
  outV := (𝔇).outV
  Pc := restPc eX pX gW
  gB := (𝔇).B + 90 + eX + pX
  wB := (𝔇).B + 90 + eX + pX + gG7
  hG := rfl
  hsp := (𝔇).hsp
  hF := e.ext2.ext1.ext.hF
  hdesc := (𝔇).hdesc
  hdesc440 := (𝔇).hdesc440
  hout0 := (𝔇).hout0
  hslot := fun _ => rfl
  hmask := fun _ => rfl
  hpsl := fun _ => rfl
  hret := fun _ => rfl
  hretDrv := by show (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc + 0 = (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc; omega
  hlog := by show (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc + 1 = (𝔇).G + (𝔇).R1 + 398 + (𝔇).w + (𝔇).tc; omega
  hs1 := by show (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc + 5 = (𝔇).G + (𝔇).R1 + 402 + (𝔇).w + (𝔇).tc; omega
  hd1 := by show (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc + 6 = (𝔇).G + (𝔇).R1 + 403 + (𝔇).w + (𝔇).tc; omega
  hl1 := by show (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc + 7 = (𝔇).G + (𝔇).R1 + 404 + (𝔇).w + (𝔇).tc; omega
  hs2 := by show (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc + 8 = (𝔇).G + (𝔇).R1 + 405 + (𝔇).w + (𝔇).tc; omega
  hd2 := by show (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc + 9 = (𝔇).G + (𝔇).R1 + 406 + (𝔇).w + (𝔇).tc; omega
  hl2 := by show (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc + 10 = (𝔇).G + (𝔇).R1 + 407 + (𝔇).w + (𝔇).tc; omega
  hfam := fun _ => rfl
  hpool := fun _ => rfl
  hrw1 := rfl
  hrw2 := rfl
  hlen := rfl
  hgB := by show (𝔇).G + (𝔇).R1 + 410 + (𝔇).w + (𝔇).tc + 19 < (𝔇).B + 90 + eX + pX; unfold Dims.B; omega
  hwB := Nat.le_add_right _ _

/-- W's region fits below the high residents. -/
theorem layS_hN {eX pX gW : Nat} (e : (𝔇).RestExt3 eX pX gW) {V : Nat} (hV : (𝔇).U ≤ V) (gG7 : Nat) (kb : Nat)
    (hroom : gG7 + gwW mask.work (Cold.tapes (decompositionOf sources)) kb ≤ gW) :
    (layS mask packets rows sources res p k r e hV gG7).wB + (nW mask.work (Cold.tapes (decompositionOf sources)) kb - 29) ≤
      (layS mask packets rows sources res p k r e hV gG7).B + 43 + (layS mask packets rows sources res p k r e hV gG7).Pc := by
  have h := nW_eq mask.work (Cold.tapes (decompositionOf sources)) kb
  show (𝔇).B + 90 + eX + pX + gG7 + (nW mask.work (Cold.tapes (decompositionOf sources)) kb - 29) ≤
    (𝔇).B + 43 + restPc eX pX gW
  unfold restPc
  omega

/-- The high residents lie in the universe. -/
theorem layS_hVB {eX pX gW : Nat} (e : (𝔇).RestExt3 eX pX gW) {V : Nat} (hV : (𝔇).U ≤ V) (gG7 : Nat)
    (hres48 : 48 + restPc eX pX gW ≤ (𝔇).res) :
    (layS mask packets rows sources res p k r e hV gG7).B + 48 + (layS mask packets rows sources res p k r e hV gG7).Pc ≤ V := by
  show (𝔇).B + 48 + restPc eX pX gW ≤ V
  have hU : (𝔇).U = (𝔇).B + (𝔇).res := by unfold Dims.U Dims.prepT Dims.B; omega
  omega

/-- The value facts of `layS` in S's own terms (for `omega`). -/
theorem layS_vals {eX pX gW : Nat} (e : (𝔇).RestExt3 eX pX gW) {V : Nat} (hV : (𝔇).U ≤ V) (gG7 : Nat) :
    (layS mask packets rows sources res p k r e hV gG7).F = (𝔇).F ∧
    (layS mask packets rows sources res p k r e hV gG7).rt = (𝔇).rt ∧
    (layS mask packets rows sources res p k r e hV gG7).G = (𝔇).G ∧
    (layS mask packets rows sources res p k r e hV gG7).R1 = (𝔇).R1 ∧
    (layS mask packets rows sources res p k r e hV gG7).P0 = (𝔇).G + (𝔇).R1 ∧
    (layS mask packets rows sources res p k r e hV gG7).B = (𝔇).B ∧
    (layS mask packets rows sources res p k r e hV gG7).tc = (𝔇).tc ∧
    (layS mask packets rows sources res p k r e hV gG7).Pc = restPc eX pX gW ∧
    (layS mask packets rows sources res p k r e hV gG7).wB = (𝔇).B + 90 + eX + pX + gG7 ∧
    mask.work = (𝔇).w ∧ (packets (decompositionOf sources)).ordinary.program.tapeCount = (𝔇).tc :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `Rpad` is `Rc` on the loader scratch. -/
theorem layS_rpad {eX pX gW : Nat} (e : (𝔇).RestExt3 eX pX gW) {V : Nat} (hV : (𝔇).U ≤ V) (gG7 Rc : Nat) (x : Fin V)
    (h1 : (layS mask packets rows sources res p k r e hV gG7).G ≤ x.val)
    (h2 : x.val < (layS mask packets rows sources res p k r e hV gG7).P0 + 408 + mask.work +
      (layS mask packets rows sources res p k r e hV gG7).tc) :
    Dims.Rpad (d := 𝔇) (eX := eX) (pX := pX) (gW := gW) (V := V) Rc x = Rc := by
  obtain ⟨_, _, v3, v4, v5, _, v7, _, _, v10, _⟩ := layS_vals mask packets rows sources res p k r e hV gG7
  have hIC : (𝔇).InClear eX pX gW x.val := by
    have vp : (𝔇).pscr = (𝔇).R1 + 408 + (𝔇).w + (𝔇).tc := rfl
    unfold Dims.InClear
    rw [v3] at h1
    rw [v5, v7, v10] at h2
    omega
  unfold Dims.Rpad
  rw [if_pos hIC]

/-- The words stage's blank tapes are `InClear` and not the cursor, so `RestIn4` blanks them. -/
theorem layS_blank {eX pX gW : Nat} (e : (𝔇).RestExt3 eX pX gW) {V : Nat} (hV : (𝔇).U ≤ V) (gG7 kb Rc : Nat)
    (hroom : gG7 + gwW mask.work (Cold.tapes (decompositionOf sources)) kb ≤ gW)
    (K : Fin V → Prop) (K0 : Fin V → List Bool) (KH0 : Fin V → Nat) (m : Nat) (H : Fin V → Nat) (A : Fin V → List Bool)
    (hin : RestIn4 (𝔇) eX pX gW Rc ((𝔇).pcT e.ext2.ext1 hV ⟨64, by unfold restPc; omega⟩) K K0 KH0 m H A)
    (x : Fin V) (hx : (layS mask packets rows sources res p k r e hV gG7).Blank
      (gwW mask.work (Cold.tapes (decompositionOf sources)) kb) x.val) :
    A x = List.replicate Rc false ∧ H x = 0 := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11⟩ := layS_vals mask packets rows sources res p k r e hV gG7
  unfold HostLay.Blank at hx
  rw [v1, v2, v3, v5, v6, v7, v9, v10] at hx
  have vp : (𝔇).pscr = (𝔇).R1 + 408 + (𝔇).w + (𝔇).tc := rfl
  have vG : (𝔇).G = (𝔇).F + (𝔇).rt + 13 := rfl
  have vB : (𝔇).B = (𝔇).G + (𝔇).R1 + 410 + (𝔇).w + (𝔇).tc := rfl
  have vPc : restPc eX pX gW = 71 + eX + pX + gW := rfl
  have hIC : (𝔇).InClear eX pX gW x.val := by
    unfold Dims.InClear
    rw [vPc]
    rw [v10] at hroom
    omega
  have hc : x ≠ (𝔇).pcT e.ext2.ext1 hV ⟨64, by unfold restPc; omega⟩ := by
    intro h
    have hv : x.val = (𝔇).B + 19 + 64 := by rw [h]; rfl
    rw [v10] at hroom
    omega
  exact hin.2 x hIC hc

/-- Where the words stage writes: loader targets, `lenTape = B`, W's region. -/
theorem layS_wout {eX pX gW : Nat} (e : (𝔇).RestExt3 eX pX gW) {V : Nat} (hV : (𝔇).U ≤ V) (gG7 : Nat) (src : Fin 6 → Fin V)
    (N : Nat) (hN : ∀ pp, 6 ≤ pp → pp < N → hostV (layS mask packets rows sources res p k r e hV gG7).P0 mask.work
      (layS mask packets rows sources res p k r e hV gG7).tc (layS mask packets rows sources res p k r e hV gG7).B
      (layS mask packets rows sources res p k r e hV gG7).Pc (layS mask packets rows sources res p k r e hV gG7).wB pp < V)
    (pp : Fin N) (x : Fin V) (h11 : 11 ≤ pp.val)
    (hx : (layS mask packets rows sources res p k r e hV gG7).dock src N hN pp = x) :
    ((𝔇).G ≤ x.val ∧ x.val < (𝔇).G + (𝔇).R1 + 408 + (𝔇).w + (𝔇).tc) ∨ x.val = (𝔇).B ∨
      ((𝔇).B + 90 + eX + pX + gG7 ≤ x.val ∧ x.val < (𝔇).B + 90 + eX + pX + gG7 + (N - 29)) := by
  obtain ⟨_, _, _, _, v5, v6, v7, v8, v9, v10, _⟩ := layS_vals mask packets rows sources res p k r e hV gG7
  have hv := congrArg Fin.val hx
  unfold HostLay.dock at hv
  rw [wsl_val _ _ _ _ _ _ _ _ pp (by omega)] at hv
  have hc := hostV_cases (layS mask packets rows sources res p k r e hV gG7).P0 mask.work
    (layS mask packets rows sources res p k r e hV gG7).tc (layS mask packets rows sources res p k r e hV gG7).B
    (layS mask packets rows sources res p k r e hV gG7).Pc (layS mask packets rows sources res p k r e hV gG7).wB pp.val (by omega)
  have := pp.isLt
  have vB : (𝔇).B = (𝔇).G + (𝔇).R1 + 410 + (𝔇).w + (𝔇).tc := rfl
  omega

/-- **`hG7` at S's layout.** -/
theorem hG7_of {eX pX gW : Nat} (e : (𝔇).RestExt3 eX pX gW) {V : Nat} (hV : (𝔇).U ≤ V) (gG7 : Nat)
    {kb : Nat} (SB : Item4.StartBank (decompositionOf sources) kb) (hIn : ∀ j, (SB.inPort j).val = j.val)
    (hroom : gG7 + gwW mask.work (Cold.tapes (decompositionOf sources)) kb ≤ gW)
    (hres48 : 48 + restPc eX pX gW ≤ (𝔇).res)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits))
    (L target : Nat) (mode : Bool) (Rc b qCap : Nat)
    (layoutAt : ∀ m : Nat, Packets.Layout (decompositionOf sources)
      ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources))
      (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode m)))
    (capsAt : Nat → RowCaps) (MB : List Bool) (dR : Nat)
    (K : Fin V → Prop) (K0 : Fin V → List Bool) (KH0 : Fin V → Nat)
    {sS : Nat} (selM : Machine V sS) (costS : Nat → Nat) (P : FactorProducer mode (decompositionOf sources) pcpp)
    (reg : Fin (19 + 4 * P.t) → Fin V) (hreg : Function.Injective reg) (Scr : Fin V → Prop)
    (hsel : Item4.SelRun selM costS P coordinate ph ci L target Rc b qCap reg (Dims.queryCopy e.ext2.ext1.ext hV)
      ((𝔇).pcT e.ext2.ext1 hV ⟨70, by unfold restPc; omega⟩)
      (fun i => (𝔇).pcT e.ext2.ext1 hV ⟨61 + i.val, by have := i.isLt; unfold restPc; omega⟩) Scr
      (RestIn4 (𝔇) eX pX gW Rc ((𝔇).pcT e.ext2.ext1 hV ⟨64, by unfold restPc; omega⟩) K K0 KH0))
    (hregR : ∀ i, (𝔇).B + 90 + eX + pX ≤ (reg i).val ∧ (reg i).val < (𝔇).B + 90 + eX + pX + gG7)
    (hScr : ∀ x, Scr x → (𝔇).B + 90 + eX + pX ≤ x.val ∧ x.val < (𝔇).B + 90 + eX + pX + gG7)
    (hOk : ∀ m, m ≤ (monomials coordinate ph ci).length →
      ∀ i : Fin 4, P.Ok (factorsAt coordinate ph ci m)[i.val]?)
    (hneedP : ∀ m, m ≤ (monomials coordinate ph ci).length →
      ∀ i : Fin 4, P.need (factorsAt coordinate ph ci m)[i.val]? ≤ Rc)
    (hKq : K (Dims.queryCopy e.ext2.ext1.ext hV) ∧
      K0 (Dims.queryCopy e.ext2.ext1.ext hV) = ZeroPadding.pad qCap (natListWord
        [RepairRepresentation.literalIndex (pcpp.clauses ci).left,
         RepairRepresentation.literalIndex (pcpp.clauses ci).right]) ∧ KH0 (Dims.queryCopy e.ext2.ext1.ext hV) = 0)
    (hKres : ∀ m, m ≤ (monomials coordinate ph ci).length → ∀ x : Fin V,
      (𝔇).B + 43 + restPc eX pX gW ≤ x.val → x.val < (𝔇).B + 48 + restPc eX pX gW →
      K x ∧ K0 x = ZeroPadding.pad Rc (wd (decompositionOf sources) (requestAt coordinate ph ci L target mode m) MB
        (x.val - ((𝔇).B + 43 + restPc eX pX gW) + 6)) ∧ KH0 x = 0)
    (hKrw : K (Dims.rewind2Slots e.ext2.ext1.ext hV 1) ∧
      K0 (Dims.rewind2Slots e.ext2.ext1.ext hV 1) = List.replicate dR true ∧ KH0 (Dims.rewind2Slots e.ext2.ext1.ext hV 1) = 0 ∧
      K (Dims.rewind2Slots e.ext2.ext1.ext hV 2) ∧
      K0 (Dims.rewind2Slots e.ext2.ext1.ext hV 2) = List.replicate dR false ∧ KH0 (Dims.rewind2Slots e.ext2.ext1.ext hV 2) = 0)
    (hMB : ∀ m, SLoad.Setup.metaBits (layoutAt m).w (layoutAt m).degree (layoutAt m).C (capsAt m) = MB)
    (hdR : ∀ m, (capsAt m).descriptorReserve = dR)
    (hNw : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * (requestAt coordinate ph ci L target mode m).nativeWord.length + 1 ≤ Rc)
    (hS : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * ((requestAt coordinate ph ci L target mode m).supportWord (decompositionOf sources)).length + 1 ≤ Rc)
    (hT : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * ((requestAt coordinate ph ci L target mode m).topWord (decompositionOf sources)).length + 1 ≤ Rc)
    (cq : ∀ m, m ≤ (monomials coordinate ph ci).length → 4 * (requestAt coordinate ph ci L target mode m).q + 3 ≤ Rc)
    (ck : ∀ m, m ≤ (monomials coordinate ph ci).length →
      4 * normalizedLiveCount (requestAt coordinate ph ci L target mode m).q
        (requestAt coordinate ph ci L target mode m).liveScale + 3 ≤ Rc)
    (cm : ∀ m, m ≤ (monomials coordinate ph ci).length →
      4 * ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources)).occurrences.length + 3 ≤ Rc)
    (ci' : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * ((requestAt coordinate ph ci L target mode m).indexWord (decompositionOf sources)).length + 1 ≤ Rc)
    (hneed : ∀ m, m ≤ (monomials coordinate ph ci).length → SB.need (requestAt coordinate ph ci L target mode m) ≤ Rc)
    (cl1 : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * ((requestAt coordinate ph ci L target mode m).input (decompositionOf sources)).length + 1 ≤ Rc)
    (cl2 : 2 * MB.length + 1 ≤ Rc)
    (hwin : ∀ m, m ≤ (monomials coordinate ph ci).length →
      Item4.g7Cost costS (fun m => Words.wordsCost mask SB (requestAt coordinate ph ci L target mode m) MB) P coordinate ph ci
        L target m + 1 ≤ Rc) :
    ResidentRunH
      (Item4.g7Machine selM P reg (wordsHostM (layS mask packets rows sources res p k r e hV gG7) SB (srcOf P reg)
        ((layS mask packets rows sources res p k r e hV gG7).hostV_lt _
          (layS_hN mask packets rows sources res p k r e hV gG7 kb hroom)
          (layS_hVB mask packets rows sources res p k r e hV gG7 hres48))))
      (Item4.g7Cost costS (fun m => Words.wordsCost mask SB (requestAt coordinate ph ci L target mode m) MB) P coordinate ph ci
        L target)
      mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources))
      ((𝔇).maskSlots hV) ((𝔇).pslots hV) ((𝔇).slot hV) ((𝔇).ret hV) ((𝔇).scr hV 0) ((𝔇).scr hV 1)
      ((𝔇).familySlots hV) ((𝔇).poolSlots hV) (Dims.rewind2Slots e.ext2.ext1.ext hV)
      ((𝔇).scr hV 5) ((𝔇).scr hV 6) ((𝔇).scr hV 7) ((𝔇).scr hV 8) ((𝔇).scr hV 9) ((𝔇).scr hV 10)
      (Dims.lenTape e.ext2.ext1.ext hV) coordinate ph ci L target mode Rc b
      ((𝔇).pcT e.ext2.ext1 hV ⟨70, by unfold restPc; omega⟩)
      (fun i => (𝔇).pcT e.ext2.ext1 hV ⟨61 + i.val, by have := i.isLt; unfold restPc; omega⟩) layoutAt capsAt
      (Dims.Rpad (d := 𝔇) (eX := eX) (pX := pX) (gW := gW) (V := V) Rc)
      (RestIn4 (𝔇) eX pX gW Rc ((𝔇).pcT e.ext2.ext1 hV ⟨64, by unfold restPc; omega⟩) K K0 KH0)
      (fun x => OutV (𝔇) eX pX gW x.val) := by
  set LL := layS mask packets rows sources res p k r e hV gG7 with hLL
  have hN' := layS_hN mask packets rows sources res p k r e hV gG7 kb hroom
  have hVB' := layS_hVB mask packets rows sources res p k r e hV gG7 hres48
  set N := nW mask.work (Cold.tapes (decompositionOf sources)) kb with hNdef
  have hN29 : 29 ≤ N := by rw [hNdef]; unfold nW; omega
  have hgw : N - 29 = gwW mask.work (Cold.tapes (decompositionOf sources)) kb := by rw [hNdef, nW_eq]; omega
  have vB : (𝔇).B = (𝔇).G + (𝔇).R1 + 410 + (𝔇).w + (𝔇).tc := rfl
  have vG : (𝔇).G = (𝔇).F + (𝔇).rt + 13 := rfl
  have vp : (𝔇).pscr = (𝔇).R1 + 408 + (𝔇).w + (𝔇).tc := rfl
  have vPc : restPc eX pX gW = 71 + eX + pX + gW := rfl
  have hF := e.ext2.ext1.ext.hF
  have hsp := (𝔇).hsp
  have hWv : ∀ (pp : Fin N) (x : Fin V), 11 ≤ pp.val → LL.dock (srcOf P reg) N (LL.hostV_lt _ hN' hVB') pp = x →
      ((𝔇).G ≤ x.val ∧ x.val < (𝔇).G + (𝔇).R1 + 408 + (𝔇).w + (𝔇).tc) ∨ x.val = (𝔇).B ∨
        ((𝔇).B + 90 + eX + pX + gG7 ≤ x.val ∧ x.val < (𝔇).B + 90 + eX + pX + gG7 + (N - 29)) :=
    fun pp x h11 hx => layS_wout mask packets rows sources res p k r e hV gG7 (srcOf P reg) N _ pp x h11 hx
  have hW := wordsRun_host LL SB hIn coordinate ph ci L target Rc P reg hreg
    ((𝔇).pcT e.ext2.ext1 hV ⟨70, by unfold restPc; omega⟩)
    (fun i => (𝔇).pcT e.ext2.ext1 hV ⟨61 + i.val, by have := i.isLt; unfold restPc; omega⟩) Scr
    (RestIn4 (𝔇) eX pX gW Rc ((𝔇).pcT e.ext2.ext1 hV ⟨64, by unfold restPc; omega⟩) K K0 KH0)
    layoutAt capsAt MB dR (Dims.Rpad (d := 𝔇) (eX := eX) (pX := pX) (gW := gW) (V := V) Rc)
    hregR (by show (𝔇).B + 19 + 70 = (𝔇).B + 89; omega)
    (fun i => by show (𝔇).B + 19 + (61 + i.val) = (𝔇).B + 80 + i.val; omega) hScr
    (by show (𝔇).B + 90 ≤ (𝔇).B + 90 + eX + pX; omega) hN' hVB' rfl hMB hdR
    (fun x h1 h2 => layS_rpad mask packets rows sources res p k r e hV gG7 Rc x h1 h2)
    (by
      intro m hm H A hin x h1 h2
      obtain ⟨hK, h0, hk0⟩ := hKres m hm x h1 h2
      obtain ⟨e1, e2⟩ := hin.1.2.2.2 x hK
      exact ⟨e1.trans h0, e2.trans hk0⟩)
    (fun m H A hin x hx => layS_blank mask packets rows sources res p k r e hV gG7 kb Rc hroom K K0 KH0 m H A hin x hx)
    (by
      intro m H A hin
      obtain ⟨k1, k10, kh1, k2, k20, kh2⟩ := hKrw
      obtain ⟨a1, b1⟩ := hin.1.2.2.2 _ k1
      obtain ⟨a2, b2⟩ := hin.1.2.2.2 _ k2
      exact ⟨a1.trans k10, b1.trans kh1, a2.trans k20, b2.trans kh2⟩)
    hNw hS hT cq ck cm ci' hneed cl1 cl2
  refine Item4.residentRunH_of2 mask _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ coordinate ph ci L target mode Rc b qCap
    _ _ _ layoutAt capsAt _ _ _ selM costS P reg hreg Scr hsel _ _ _ hW ?_ hOk hneedP hNw hS hT ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hwin
  · intro m H A hin
    obtain ⟨e1, e2⟩ := hin.1.2.2.2 _ hKq.1
    exact ⟨e2.trans hKq.2.2, e1.trans hKq.2.1⟩
  · intro i he
    have := hregR i
    have hv := congrArg Fin.val he
    have : ((𝔇).pcT e.ext2.ext1 hV ⟨70, by unfold restPc; omega⟩).val = (𝔇).B + 19 + 70 := rfl
    omega
  · intro i j he
    have := hregR i
    have hv := congrArg Fin.val he
    have : ((𝔇).pcT e.ext2.ext1 hV ⟨61 + j.val, by have := j.isLt; unfold restPc; omega⟩).val = (𝔇).B + 19 + (61 + j.val) := rfl
    have := j.isLt
    omega
  · rintro ⟨pp, h11, hx⟩
    have hw := hWv pp _ h11 hx
    have : ((𝔇).pcT e.ext2.ext1 hV ⟨70, by unfold restPc; omega⟩).val = (𝔇).B + 19 + 70 := rfl
    omega
  · intro i ⟨pp, h11, hx⟩
    have hw := hWv pp _ h11 hx
    have : ((𝔇).pcT e.ext2.ext1 hV ⟨61 + i.val, by have := i.isLt; unfold restPc; omega⟩).val = (𝔇).B + 19 + (61 + i.val) := rfl
    have := i.isLt
    omega
  · intro i
    have := hregR i
    show OutV (𝔇) eX pX gW (reg i).val
    unfold OutV
    right; right; right; right
    constructor <;> omega
  · show OutV (𝔇) eX pX gW ((𝔇).B + 19 + 70)
    unfold OutV
    right; right; right; left; rfl
  · intro i
    show OutV (𝔇) eX pX gW ((𝔇).B + 19 + (61 + i.val))
    unfold OutV
    right; right; left
    have := i.isLt
    constructor <;> omega
  · intro x hx
    have := hScr x hx
    show OutV (𝔇) eX pX gW x.val
    unfold OutV
    right; right; right; right
    constructor <;> omega
  · rintro x ⟨pp, h11, hx⟩
    have hw := hWv pp _ h11 hx
    show OutV (𝔇) eX pX gW x.val
    unfold OutV
    omega
  · intro m H A hin x hx
    obtain ⟨e1, e2⟩ := hin.1.1 x hx
    exact ⟨by rw [e1, List.length_replicate], e2⟩
  · intro m H A hin x
    unfold Dims.Rpad
    split_ifs with h
    · exact hin.len x h
    · exact Nat.zero_le _

end S

end
end NearCubicWires.SourceFactorSel.AtS
end
