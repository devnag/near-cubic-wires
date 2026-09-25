import Proof.SourceAssembly.SourceSkelInitX
import Proof.SourceAssembly.SourceSkelInv

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open NearCubicWires.SupplierEstimator RepairRepresentation
open PCJ1fef9807c6954e94_Native
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
namespace NearCubicWires.SourceSkeleton.InitS
noncomputable section

/-! ## 1. The extended resident map -/

/-- **The whole init's resident map with the extension.** -/
def valAllX (mode : Bool) (L q Rc DD CD Dcw Ccw CL DL b : Nat) (MB : List Bool) : Nat → Option (List Bool) := fun i =>
  if i = 16 then some (ZeroPadding.pad Rc (UnaryTemplate.tape (normalizedLiveCount q L)))
  else if i = 17 then some (ZeroPadding.pad Rc (frame MB))
  else if i = 18 then some (ZeroPadding.pad Rc (frame (List.replicate MB.length true)))
  else if i = 19 then some (ZeroPadding.pad Rc (List.replicate b true))
  else valAll mode L q Rc DD CD Dcw Ccw CL DL i

theorem slotVal_longX (mode : Bool) (L q Rc DD CD Dcw Ccw CL DL b : Nat) (MB : List Bool) (i : Nat) :
    Rc ≤ (slotVal Rc (valAllX mode L q Rc DD CD Dcw Ccw CL DL b MB) i).length := by
  by_cases h16 : i = 16
  · subst h16; simp only [slotVal, valAllX, if_true]; exact pad_long _ _
  by_cases h17 : i = 17
  · subst h17; simp only [slotVal, valAllX, if_neg (show (17:Nat) ≠ 16 by decide), if_true]; exact pad_long _ _
  by_cases h18 : i = 18
  · subst h18
    simp only [slotVal, valAllX, if_neg (show (18:Nat) ≠ 16 by decide), if_neg (show (18:Nat) ≠ 17 by decide), if_true]
    exact pad_long _ _
  by_cases h19 : i = 19
  · subst h19
    simp only [slotVal, valAllX, if_neg (show (19:Nat) ≠ 16 by decide), if_neg (show (19:Nat) ≠ 17 by decide),
      if_neg (show (19:Nat) ≠ 18 by decide), if_true]
    exact pad_long _ _
  have e : slotVal Rc (valAllX mode L q Rc DD CD Dcw Ccw CL DL b MB) i = slotVal Rc (valAll mode L q Rc DD CD Dcw Ccw CL DL) i := by
    simp only [slotVal, valAllX, if_neg h16, if_neg h17, if_neg h18, if_neg h19]
  rw [e]
  exact slotVal_long mode L q Rc DD CD Dcw Ccw CL DL i

theorem valAllX_10 (mode : Bool) (L q Rc DD CD Dcw Ccw CL DL b : Nat) (MB : List Bool) :
    valAllX mode L q Rc DD CD Dcw Ccw CL DL b MB 10 = some (List.replicate (Rk Rc) true) := by
  simp [valAllX, valAll, valR]

theorem valAllX_11 (mode : Bool) (L q Rc DD CD Dcw Ccw CL DL b : Nat) (MB : List Bool) :
    valAllX mode L q Rc DD CD Dcw Ccw CL DL b MB 11 = some (List.replicate (Rk Rc + 2) false) := by
  simp [valAllX, valAll, valR]

variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T) {NS : Nat}
  (hh : HeadExt d eX pX gW X NS)

/-! ## 2. `hlong` and `InvC` at the init's exit, generic in the resident map -/

theorem inv_longG {NR NE : Nat} (hE : ResExt d eX pX gW X NS NE)
    {L cS cR q b Rc Vv CP CW CL DP DW DL : Nat} {mode : Bool} {tg : Nat} {val : Nat → Option (List Bool)} {u : Nat}
    {H H' : Fin T → ℕ} {A A' : Fin T → List Bool}
    (hi : InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg val u
      H A H' A')
    (hML : ∀ i, (masterW L cS cR q b Rc Vv i).length = Rc)
    (hv : ∀ i, Rc ≤ (slotVal Rc val i).length) :
    ∀ x : Fin T, d.F ≤ x.val → x.val < d.U → Rc ≤ (A' x).length := by
  obtain ⟨hF0, hB0, h11, h12, hU, hJB, hjk, hP⟩ := lay pl.ext
  have hres := hE.hres
  have hG : d.G = d.F + d.rt + 13 := rfl
  have hBG : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  have hsbB : sb d eX pX gW = d.B + 29 + restPc eX pX gW := rfl
  have hsb : sb d eX pX gW + 32 ≤ eb d eX pX gW X NS := by unfold sb eb; omega
  have heU : eb d eX pX gW X NS + NE ≤ d.U := by unfold eb; omega
  intro x h1 h2
  by_cases cs : sb d eX pX gW + 8 ≤ x.val ∧ x.val < sb d eX pX gW + NR
  · rw [(hi.strip x cs.1 cs.2).1]; exact hv _
  by_cases ce : eb d eX pX gW X NS ≤ x.val ∧ x.val < eb d eX pX gW X NS + NE
  · by_cases cu : x.val < eb d eX pX gW X NS + u
    · exact (hi.used x ce.1 cu).1
    · rw [(hi.fresh x (by omega) ce.2).1]; simp
  obtain ⟨H1, A1, ho, hag⟩ := hi.base
  rw [(hag x cs ce).1]
  have en : CloseoutRowsEstimatorCoefficients.Stream.Entry := ⟨CloseoutFinalC10SupplierCalls.coefficientEstimate 0, 0, 0⟩
  by_cases hk : KeptS d eX pX gW X NS NR x.val
  · unfold KeptS at hk
    rcases hk with k | k | k | k | k | k | k
    · rw [show x = d.scr pl.hT 11 from Fin.ext k, ho.drv.1]; simp
    · rw [show x = d.scr pl.hT 12 from Fin.ext k, ho.log.1]; simp
    · have e : x = Dims.rfT pl.ext2 pl.hT ⟨x.val - (d.B + 14), by omega⟩ :=
        Fin.ext (by rw [pl.rfT_val]; simp only; omega)
      rw [e, (ho.target _).1, hML]
    · -- `rsT 0..4`, `mT 0..4`, `hrT 0..7`
      by_cases c1 : x.val < d.B + 19 + restPc eX pX gW + 5
      · have e : x = Dims.rsT pl.ext.rest pl.hT ⟨x.val - (d.B + 19 + restPc eX pX gW), by omega⟩ :=
          Fin.ext (by show x.val = d.B + 19 + restPc eX pX gW + (x.val - (d.B + 19 + restPc eX pX gW)); omega)
        rw [e]
        generalize hj : (⟨x.val - (d.B + 19 + restPc eX pX gW), by omega⟩ : Fin 5) = j
        match j with
        | ⟨0, _⟩ => exact (show Rc ≤ (A1 (Dims.rsT pl.ext.rest pl.hT 0)).length from by rw [ho.big.1]; exact pad_long _ _)
        | ⟨1, _⟩ => exact (show Rc ≤ (A1 (Dims.rsT pl.ext.rest pl.hT 1)).length from by rw [ho.small.1]; exact pad_long _ _)
        | ⟨2, _⟩ => exact (show Rc ≤ (A1 (Dims.rsT pl.ext.rest pl.hT 2)).length from by rw [ho.curT.1]; exact pad_long _ _)
        | ⟨3, _⟩ => exact (show Rc ≤ (A1 (Dims.rsT pl.ext.rest pl.hT 3)).length from by rw [ho.wres.1]; exact pad_long _ _)
        | ⟨4, _⟩ => exact (show Rc ≤ (A1 (Dims.rsT pl.ext.rest pl.hT 4)).length from by rw [ho.qres.1]; exact pad_long _ _)
      by_cases c2 : x.val < d.B + 19 + restPc eX pX gW + 10
      · have e : x = Dims.mT pl.ext2 pl.hT ⟨x.val - (d.B + 19 + restPc eX pX gW + 5), by omega⟩ :=
          Fin.ext (by rw [pl.mT_val]; simp only; omega)
        rw [e, (ho.master _).1, hML]
      · have e : x = Dims.hrT (ext3 pl hh) pl.hT ⟨x.val - sb d eX pX gW, by omega⟩ :=
          Fin.ext (by rw [Dims.hrT_val]; simp only; omega)
        rw [e]
        generalize hj : (⟨x.val - sb d eX pX gW, by omega⟩ : Fin 12) = j
        have hj8 : j.val < 8 := by rw [← hj]; simp only; omega
        match j, hj8 with
        | ⟨0, _⟩, _ => exact (show Rc ≤ (A1 (Dims.hrT (ext3 pl hh) pl.hT 0)).length from by rw [ho.z0.1]; exact pad_long _ _)
        | ⟨1, _⟩, _ => exact (show Rc ≤ (A1 (Dims.hrT (ext3 pl hh) pl.hT 1)).length from by rw [ho.z1.1]; exact pad_long _ _)
        | ⟨2, _⟩, _ => exact (show Rc ≤ (A1 (Dims.hrT (ext3 pl hh) pl.hT 2)).length from by rw [ho.z2.1]; exact pad_long _ _)
        | ⟨3, _⟩, _ => exact (show Rc ≤ (A1 (Dims.hrT (ext3 pl hh) pl.hT 3)).length from by rw [ho.z3.1]; exact pad_long _ _)
        | ⟨4, _⟩, _ => exact (show Rc ≤ (A1 (Dims.hrT (ext3 pl hh) pl.hT 4)).length from by rw [ho.z4.1]; exact pad_long _ _)
        | ⟨5, _⟩, _ => exact (show Rc ≤ (A1 (Dims.hrT (ext3 pl hh) pl.hT 5)).length from by rw [ho.z5.1]; exact pad_long _ _)
        | ⟨6, _⟩, _ => exact (show Rc ≤ (A1 (Dims.hrT (ext3 pl hh) pl.hT 6)).length from by rw [ho.z6.1]; exact pad_long _ _)
        | ⟨7, _⟩, _ => exact (show Rc ≤ (A1 (Dims.hrT (ext3 pl hh) pl.hT 7)).length from by rw [ho.z7.1]; exact pad_long _ _)
    · -- `encT 3 .. 12`
      have e : x = Dims.encT (d := d) pl.hT ⟨x.val - (d.F + d.rt), by omega⟩ :=
        Fin.ext (by show x.val = d.F + d.rt + (x.val - (d.F + d.rt)); omega)
      rw [e]
      generalize hj : (⟨x.val - (d.F + d.rt), by omega⟩ : Fin 13) = j
      have hj3 : 3 ≤ j.val := by rw [← hj]; simp only; omega
      match j, hj3 with
      | ⟨3, _⟩, _ => exact (show Rc ≤ (A1 (Dims.encT (d := d) pl.hT 3)).length from by rw [(ho.enc3 en []).1]; exact pad_long _ _)
      | ⟨4, _⟩, _ => exact (show Rc ≤ (A1 (Dims.encT (d := d) pl.hT 4)).length from by rw [(ho.encOld 4 (Or.inl rfl)).1]; simp)
      | ⟨5, _⟩, _ => exact (show Rc ≤ (A1 (Dims.encT (d := d) pl.hT 5)).length from by rw [(ho.encOld 5 (Or.inr rfl)).1]; simp)
      | ⟨6, _⟩, _ => exact (show Rc ≤ (A1 (Dims.encT (d := d) pl.hT 6)).length from by rw [(ho.enc7 en []).1]; exact pad_long _ _)
      | ⟨7, _⟩, _ => exact (show Rc ≤ (A1 (Dims.encT (d := d) pl.hT 7)).length from by rw [(ho.enc8 en []).1]; exact pad_long _ _)
      | ⟨8, _⟩, _ => exact (show Rc ≤ (A1 (Dims.encT (d := d) pl.hT 8)).length from by rw [(ho.enc9 en []).1]; exact pad_long _ _)
      | ⟨9, _⟩, _ => exact (show Rc ≤ (A1 (Dims.encT (d := d) pl.hT 9)).length from by rw [(ho.enc10 en []).1]; exact pad_long _ _)
      | ⟨10, _⟩, _ => exact (show Rc ≤ (A1 (Dims.encT (d := d) pl.hT 10)).length from by rw [(ho.app2 en []).1]; exact pad_long _ _)
      | ⟨11, _⟩, _ => exact (show Rc ≤ (A1 (Dims.encT (d := d) pl.hT 11)).length from by rw [(ho.app4 en []).1]; exact pad_long _ _)
      | ⟨12, _⟩, _ => exact (show Rc ≤ (A1 (Dims.encT (d := d) pl.hT 12)).length from by rw [(ho.app5 en []).1]; exact pad_long _ _)
    · exact (ho.junk x k.1 k.2).1
    · exact (ho.scr x k.1 k.2).1
  · rw [(ho.blank x h1 h2 hk).1]; simp

theorem invC_of_initG (e : d.RestExt3 eX pX gW) {NR NE : Nat} (hNR16 : 16 ≤ NR) (hNR : NR ≤ 32)
    (hE : ResExt d eX pX gW X NS NE)
    {L cS cR q b Rc Vv CP CW CL DP DW DL : Nat} {mode : Bool} {tg : Nat} {val : Nat → Option (List Bool)} {u : Nat}
    {H H' : Fin T → ℕ} {A A' : Fin T → List Bool}
    (hi : InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg val u
      H A H' A')
    (Kc : Fin T → Prop) (K0 : Fin T → List Bool) (KH0 : Fin T → Nat) (cnt : Fin T) (hcnt : d.U ≤ cnt.val)
    (hKlow : ∀ x, Kc x → x.val < d.F → (x.val < 278 ∨ 284 ≤ x.val) ∧ A x = K0 x ∧ H x = KH0 x)
    (hKhigh : ∀ x, Kc x → d.F ≤ x.val → ∃ i, i < NR ∧ x.val = sb d eX pX gW + i ∧
      K0 x = initResVal Rc q L CP DP CW DW CL DL mode tg val i ∧ KH0 x = 0)
    (hcntA : (A cnt).length ≤ Rc) (hcntH : H cnt ≤ Rc)
    (hML : ∀ i, (masterW L cS cR q b Rc Vv i).length = Rc) (hRc2 : 2 ≤ Rc)
    (hv10 : val 10 = some (List.replicate (Rk Rc) true)) (hv11 : val 11 = some (List.replicate (Rk Rc + 2) false)) :
    Rest.InvC e pl.hT Rc (Rk Rc) Kc K0 KH0 cnt b q (Mb L q) (InitPost.Ms L q) Rc Rc Rc Rc (cS*(Vv+1)) (cR*(Vv+1))
      (Vv+1) b (U0 L q) H' A' := by
  obtain ⟨hF0, hB0, h11, h12, hU, hJB, hjk, hP⟩ := lay pl.ext
  have hres := hE.hres
  have hG : d.G = d.F + d.rt + 13 := rfl
  have hBG : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  have hsbB : sb d eX pX gW = d.B + 29 + restPc eX pX gW := rfl
  have hsb : sb d eX pX gW + 32 ≤ eb d eX pX gW X NS := by unfold sb eb; omega
  have heU : eb d eX pX gW X NS + NE ≤ d.U := by unfold eb; omega
  obtain ⟨H1, A1, ho, hag⟩ := hi.base
  have low : ∀ x : Fin T, x.val < sb d eX pX gW + 8 → A' x = A1 x ∧ H' x = H1 x := fun x hx =>
    hag x (by omega) (by omega)
  have high : ∀ x : Fin T, d.U ≤ x.val → A' x = A1 x ∧ H' x = H1 x := fun x hx =>
    hag x (by omega) (by omega)
  have vr : ∀ i : Fin 5, (Dims.rsT pl.ext.rest pl.hT i).val < sb d eX pX gW + 8 := fun i => by
    have := i.isLt; show d.B + 19 + restPc eX pX gW + i.val < _; omega
  have vm : ∀ i : Fin 5, (Dims.mT pl.ext2 pl.hT i).val < sb d eX pX gW + 8 := fun i => by
    rw [pl.mT_val]; have := i.isLt; omega
  have v11 : (d.scr pl.hT 11).val < sb d eX pX gW + 8 := by show d.scrV 11 < _; omega
  have v12 : (d.scr pl.hT 12).val < sb d eX pX gW + 8 := by show d.scrV 12 < _; omega
  have r10 := slot_of pl hh hi 10 (by decide) (by decide) (by omega) _ hv10
  have r11 := slot_of pl hh hi 11 (by decide) (by decide) (by omega) _ hv11
  have e10 : Dims.hrT e pl.hT 10 = stripT pl hh 10 (by decide) := Fin.ext rfl
  have e11 : Dims.hrT e pl.hT 11 = stripT pl hh 11 (by decide) := Fin.ext rfl
  have clr : ∀ x : Fin T, d.InClear eX pX gW x.val → A' x = List.replicate Rc false ∧ H' x = 0 := by
    intro x hx
    have hxlt : x.val < sb d eX pX gW + 8 := by
      have hp : d.pscr = d.R1 + 408 + d.w + d.tc := rfl
      unfold Dims.InClear at hx; rcases hx with h | h | h | h <;> omega
    rw [(low x hxlt).1, (low x hxlt).2]
    exact outS_clear pl hh NR hNR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho x hx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- kept
    intro x hx
    by_cases hxF : x.val < d.F
    · obtain ⟨hr, hA, hH⟩ := hKlow x hx hxF
      rw [(low x (by omega)).1, (low x (by omega)).2, (ho.below x hxF hr).1, (ho.below x hxF hr).2]
      exact ⟨hA, hH⟩
    · obtain ⟨i, hiN, hxv, hK, hKH⟩ := hKhigh x hx (by omega)
      have ex : x = stripT pl hh i (by omega) := Fin.ext hxv
      have r := inv_resident pl hh hNR hi i hiN
      rw [hK, hKH, ex]
      exact r
  · rw [(low _ (vr 0)).1]; exact ho.big.1
  · rw [(low _ (vr 1)).1]; exact ho.small.1
  · rw [(low _ (vr 3)).1]; exact ho.wres.1
  · rw [(low _ (vr 4)).1]; exact ho.qres.1
  · intro i hi2
    rw [(low _ (vr i)).2]
    fin_cases i
    · exact ho.big.2
    · exact ho.small.2
    · exact absurd rfl hi2
    · exact ho.wres.2
    · exact ho.qres.2
  · rw [(low _ (vm 0)).1, (ho.master 0).1]; rfl
  · rw [(low _ (vm 1)).1, (ho.master 1).1]; rfl
  · rw [(low _ (vm 2)).1, (ho.master 2).1]; rfl
  · rw [(low _ (vm 3)).1, (ho.master 3).1]; rfl
  · rw [(low _ (vm 4)).1, (ho.master 4).1]; rfl
  · intro i; rw [(low _ (vm i)).2]; exact (ho.master i).2
  · rw [(low _ v11).1]; exact ho.drv.1
  · rw [(low _ v11).2]; exact ho.drv.2
  · rw [(low _ v12).1]; exact ho.log.1
  · rw [(low _ v12).2]; exact ho.log.2
  · rw [e10]; exact r10.1
  · rw [e10]; exact r10.2
  · rw [e11]; exact r11.1
  · rw [e11]; exact r11.2
  · -- dirtA
    intro x hx _
    rcases hx with hc | ⟨h1, h2⟩
    · rw [(clr x hc).1]; simp
    · have ek : ∃ i : Fin 5, Dims.rfT pl.ext2 pl.hT i = x :=
        ⟨⟨x.val - (d.B + 14), by omega⟩, Fin.ext (by rw [pl.rfT_val]; simp only; omega)⟩
      obtain ⟨i, rfl⟩ := ek
      rw [(low _ (by rw [pl.rfT_val]; have := i.isLt; omega)).1, (ho.target i).1, hML i]
  · -- dirtH
    intro x hx _
    rcases hx with hc | ⟨h1, h2⟩
    · rw [(clr x hc).2]; omega
    · have ek : ∃ i : Fin 5, Dims.rfT pl.ext2 pl.hT i = x :=
        ⟨⟨x.val - (d.B + 14), by omega⟩, Fin.ext (by rw [pl.rfT_val]; simp only; omega)⟩
      obtain ⟨i, rfl⟩ := ek
      rw [(low _ (by rw [pl.rfT_val]; have := i.isLt; omega)).2, (ho.target i).2]; omega
  · intro x hz
    rw [(clr x (Dims.InZ_clear hz)).1]; simp [Rk]; omega
  · intro x hz
    rw [(clr x (Dims.InZ_clear hz)).2]; omega
  · rw [(low _ (vr 2)).1, ho.curT.1, ZeroPadding.pad_length]
    simp [UnaryTemplate.tape]; omega
  · rw [(low _ (vr 2)).2, ho.curT.2]; omega
  · rw [(high cnt hcnt).1, (ho.above cnt hcnt).1]; exact hcntA
  · rw [(high cnt hcnt).2, (ho.above cnt hcnt).2]; exact hcntH
  · -- encA
    intro kk hk
    have hkl : (Dims.encT (d := d) pl.hT kk).val < sb d eX pX gW + 8 := by
      have := kk.isLt; show d.F + d.rt + kk.val < _; omega
    rw [(low _ hkl).1]
    by_cases h4 : kk.val = 4
    · rw [(ho.encOld kk (Or.inl h4)).1]; simp
    · have hv : (Dims.encT (d := d) pl.hT kk).val = d.F + d.rt + kk.val := rfl
      have hnk : ¬ KeptS d eX pX gW X NS NR (Dims.encT (d := d) pl.hT kk).val := by
        rw [hv]; unfold KeptS; simp only [sb, Dims.scrV]; omega
      have hb := ho.blank (Dims.encT (d := d) pl.hT kk) (by rw [hv]; omega)
        (by have := kk.isLt; rw [hv]; omega) hnk
      rw [hb.1]; simp
  · -- encH
    intro kk hk
    have hkl : (Dims.encT (d := d) pl.hT kk).val < sb d eX pX gW + 8 := by
      have := kk.isLt; show d.F + d.rt + kk.val < _; omega
    rw [(low _ hkl).2]
    by_cases h4 : kk.val = 4
    · exact (ho.encOld kk (Or.inl h4)).2
    · have hv : (Dims.encT (d := d) pl.hT kk).val = d.F + d.rt + kk.val := rfl
      have hnk : ¬ KeptS d eX pX gW X NS NR (Dims.encT (d := d) pl.hT kk).val := by
        rw [hv]; unfold KeptS; simp only [sb, Dims.scrV]; omega
      exact (ho.blank (Dims.encT (d := d) pl.hT kk) (by rw [hv]; omega)
        (by have := kk.isLt; rw [hv]; omega) hnk).2

theorem invC_of_init_rwG (e : d.RestExt3 eX pX gW) {NR NE : Nat} (hNR16 : 16 ≤ NR) (hNR : NR ≤ 32)
    (hE : ResExt d eX pX gW X NS NE)
    {L cS cR q b Rc Vv CP CW CL DP DW DL : Nat} {mode : Bool} {tg : Nat} {val : Nat → Option (List Bool)} {u : Nat}
    {H H' : Fin T → ℕ} {A A' : Fin T → List Bool}
    (hi : InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg val u
      H A H' A')
    (Kc : Fin T → Prop) (K0 : Fin T → List Bool) (KH0 : Fin T → Nat) (cnt : Fin T) (hcnt : d.U ≤ cnt.val)
    (hKlow : ∀ x, Kc x → x.val < d.F → x.val ≠ 278 → x.val ≠ 279 → (x.val < 278 ∨ 284 ≤ x.val) ∧ A x = K0 x ∧ H x = KH0 x)
    (hK278 : ∀ x, Kc x → x.val = 278 → K0 x = List.replicate Vv true ∧ KH0 x = 0)
    (hK279 : ∀ x, Kc x → x.val = 279 → K0 x = List.replicate Vv false ∧ KH0 x = 0)
    (hKhigh : ∀ x, Kc x → d.F ≤ x.val → ∃ i, i < NR ∧ x.val = sb d eX pX gW + i ∧
      K0 x = initResVal Rc q L CP DP CW DW CL DL mode tg val i ∧ KH0 x = 0)
    (hcntA : (A cnt).length ≤ Rc) (hcntH : H cnt ≤ Rc)
    (hML : ∀ i, (masterW L cS cR q b Rc Vv i).length = Rc) (hRc2 : 2 ≤ Rc)
    (hv10 : val 10 = some (List.replicate (Rk Rc) true)) (hv11 : val 11 = some (List.replicate (Rk Rc + 2) false)) :
    Rest.InvC e pl.hT Rc (Rk Rc) Kc K0 KH0 cnt b q (Mb L q) (InitPost.Ms L q) Rc Rc Rc Rc (cS*(Vv+1)) (cR*(Vv+1))
      (Vv+1) b (U0 L q) H' A' := by
  obtain ⟨hF0, hB0, h11, h12, hU, hJB, hjk, hP⟩ := lay pl.ext
  have v1 := rw1_val pl
  have v2 := rw2_val pl
  have h := invC_of_initG pl hh e hNR16 hNR hE hi (fun x => Kc x ∧ x.val ≠ 278 ∧ x.val ≠ 279) K0 KH0 cnt hcnt
    (fun x hx hxF => hKlow x hx.1 hxF hx.2.1 hx.2.2) (fun x hx hxF => hKhigh x hx.1 hxF) hcntA hcntH hML hRc2 hv10 hv11
  obtain ⟨⟨r1, r1H⟩, ⟨r2, r2H⟩⟩ := init_rewinds pl hh hE hi
  have hk : ∀ x, Kc x → A' x = K0 x ∧ H' x = KH0 x := by
    intro x hx
    by_cases h8 : x.val = 278
    · have ex : x = Dims.rewind2Slots pl.ext.rest.ext pl.hT 1 := Fin.ext (by rw [h8, v1])
      obtain ⟨k1, k2⟩ := hK278 x hx h8
      rw [k1, k2, ex]
      exact ⟨r1, r1H⟩
    · by_cases h9 : x.val = 279
      · have ex : x = Dims.rewind2Slots pl.ext.rest.ext pl.hT 2 := Fin.ext (by rw [h9, v2])
        obtain ⟨k1, k2⟩ := hK279 x hx h9
        rw [k1, k2, ex]
        exact ⟨r2, r2H⟩
      · exact h.kept x ⟨hx, h8, h9⟩
  exact { h with kept := hk }

/-! ## 3. The meta stage's contract (POOL-9) and the extended init -/

def MetaRun (NR NE : Nat) (L cS cR q b Rc Vv CP CW CL DP DW DL : Nat) (mode : Bool) (tg : Nat) (MB : List Bool)
    (u : Nat) {sM : Nat} (M : Machine T sM) (mcost wM : Nat) : Prop :=
  u + wM ≤ NE ∧
  ∀ (val : Nat → Option (List Bool)) (H H' : Fin T → ℕ) (A A' : Fin T → List Bool),
    InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg val u H A H' A' →
    val 14 = some (ZeroPadding.pad Rc (frame (List.replicate q true))) →
    val 15 = some (ZeroPadding.pad Rc (frame (List.replicate (normalizedLiveCount q L) true))) →
    val 16 = some (ZeroPadding.pad Rc (UnaryTemplate.tape (normalizedLiveCount q L))) →
    val 17 = none → val 18 = none →
    ∃ A'', Step M mcost H' A' H' A'' ∧
      InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg
        (fun j => if j = 17 then some (ZeroPadding.pad Rc (frame MB))
          else if j = 18 then some (ZeroPadding.pad Rc (frame (List.replicate MB.length true))) else val j)
        (u + wM) H A H' A''

end
end NearCubicWires.SourceSkeleton.InitS
end

