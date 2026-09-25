import Proof.SourceAssembly.SourceSkelInitXA
import Proof.SourceAssembly.SourceSkelInitE

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

variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T) {NS : Nat}
  (hh : HeadExt d eX pX gW X NS)

/-! ## from `SourceSkelInitS` (E-copies) -/

/-- The composed init on SI's placement: SI's `init2Machine`, then SI's `headM`. -/
def initFME (L C cVc cS cR DP CP DW CW DL CL : Nat) (hN : nsOf DP DW DL ≤ NS) (mode : Bool) (target : Nat) :=
  Composition.machine (NearCubicWires.SourceSkeleton.InitE.init2MachineE pl L C cVc cS cR) (pl.headM hh DP CP DW CW DL CL hN mode L target)

/-- **The init on S's port map**: `initFME`, relocated (ONE fixed machine per layout, caps, mode, `L`, `target`, `NR`). -/
def initSMachineE (NR : Nat) (hNR : NR ≤ 32) (L C cVc cS cR DP CP DW CW DL CL : Nat) (hN : nsOf DP DW DL ≤ NS)
    (mode : Bool) (target : Nat) :=
  RecoveryFocus.machine (InitMove.piF (sb d eX pX gW) X NR T (room pl hh NR hNR))
    (initFME pl hh L C cVc cS cR DP CP DW CW DL CL hN mode target)

/-- Its cost (unchanged by the relocation). -/
def initSCostE (L C cVc cS cR DP CP DW CW DL CL : Nat) (mode : Bool) (target q b : Nat) : Nat :=
  NearCubicWires.SourceSkeleton.InitE.init2CostE pl L C cVc cS cR q b + 1 + Place.headCost DP CP DW CW DL CL mode L target q (Once.Rc eR L C q)

/-- **The init on S's port map.** From the first site entry (tapes of `[F, U)` and `278..283` blank at head 0, the arity template
and `1^b` at head 0), ONE fixed machine reaches `InitOutS`. Hypotheses: SI's `init2_run` fits and `head_run` bounds, at
`Rc = Once.Rc eR L C q`. -/
theorem initS_runE (NR : Nat) (hNR8 : 8 ≤ NR) (hNR : NR ≤ 32) (L C cVc cS cR DP CP DW CW DL CL : Nat)
    (hN : nsOf DP DW DL ≤ NS) (mode : Bool) (target q b : Nat) (H : Fin T → ℕ) (A : Fin T → List Bool)
    (hAr : A pl.ar = UnaryTemplate.tape q) (hHr : H pl.ar = 0)
    (hAw : A pl.wd = List.replicate b true) (hHw : H pl.wd = 0)
    (hlowE : ∀ x : Fin T, 278 ≤ x.val → x.val < 284 →
      (A x).length ≤ cVc * RuntimeShape.tableClass L eV q ∧ H x = 0)
    (hF : ∀ x : Fin T, d.F ≤ x.val → x.val < d.U → A x = [] ∧ H x = 0)
    (hfit : q + 3 + Dimension.prefixCost eR eV L C cVc q ≤ Once.Rc eR L C q)
    (hVR : cVc * RuntimeShape.tableClass L eV q ≤ Once.Rc eR L C q)
    (hVLR : VLog eV L cVc q ≤ Once.Rc eR L C q) (hRc : 2 ≤ Once.Rc eR L C q)
    (hU0 : U0 L q ≤ Once.Rc eR L C q)
    (hS : cS * (cVc * RuntimeShape.tableClass L eV q + 1) + 2 ≤ Once.Rc eR L C q)
    (hR : cR * (cVc * RuntimeShape.tableClass L eV q + 1) + 2 ≤ Once.Rc eR L C q)
    (hB : cVc * RuntimeShape.tableClass L eV q + 1 + 2 ≤ Once.Rc eR L C q)
    (hv : b + 2 ≤ Once.Rc eR L C q)
    (hcap : CloseoutRowsEstimatorParity.Capacity.value q ≤ Once.Rc eR L C q) (hqR : q ≤ Once.Rc eR L C q)
    (hLw : (frame (natWord L)).length ≤ Once.Rc eR L C q + 2)
    (hTw : (frame (natWord target)).length ≤ Once.Rc eR L C q + 2) (h5 : 5 ≤ Once.Rc eR L C q) :
    ∃ (H' : Fin T → ℕ) (A' : Fin T → List Bool),
      Step (initSMachineE pl hh NR hNR L C cVc cS cR DP CP DW CW DL CL hN mode target)
        (initSCostE pl L C cVc cS cR DP CP DW CW DL CL mode target q b) H A H' A' ∧
      InitOutS pl hh NR L cS cR q b (Once.Rc eR L C q) (cVc * RuntimeShape.tableClass L eV q) CP CW CL DP DW DL mode target
        H A H' A' := by
  obtain ⟨hF0, hB0, h11, h12, hU, hJB, hjk, hP⟩ := lay pl.ext
  obtain ⟨z1, z2, z3, z4, z5, z6⟩ := pl.zlay hh
  have hres := hh.hres
  have hG : d.G = d.F + d.rt + 13 := rfl
  have hBG : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  have hpc : restPc eX pX gW = 71 + eX + pX + gW := rfl
  have hroom := room pl hh NR hNR
  set bb := sb d eX pX gW with hbb
  have hbb' : bb = d.B + 29 + restPc eX pX gW := rfl
  set π := InitMove.piF bb X NR T hroom with hπ
  set ρ := InitMove.rhoF bb X NR T hroom with hρ
  have fixπ : ∀ x : Fin T, (x.val < bb ∨ bb + 3 + X + NR ≤ x.val) → π x = x := fun x hx =>
    Fin.ext (InitMove.piV_fix bb X NR x.val hx)
  have fixρ : ∀ x : Fin T, (x.val < bb ∨ bb + 3 + X + NR ≤ x.val) → ρ x = x := fun x hx =>
    Fin.ext (InitMove.rhoV_fix bb X NR x.val hx)
  have har := pl.har
  have hwd := pl.hwd
  -- SI's entry, on the bank read through `π`
  have hAr' : A (π pl.ar) = UnaryTemplate.tape q := by
    rw [fixπ pl.ar (Or.inl (by omega))]; exact hAr
  have hHr' : H (π pl.ar) = 0 := by rw [fixπ pl.ar (Or.inl (by omega))]; exact hHr
  have hAw' : A (π pl.wd) = List.replicate b true := by
    rw [fixπ pl.wd (Or.inl (by omega))]; exact hAw
  have hHw' : H (π pl.wd) = 0 := by rw [fixπ pl.wd (Or.inl (by omega))]; exact hHw
  have hlow' : ∀ x : Fin T, 278 ≤ x.val → x.val < 284 →
      (A (π x)).length ≤ cVc * RuntimeShape.tableClass L eV q ∧ H (π x) = 0 := by
    intro x h1 h2
    rw [fixπ x (Or.inl (by omega))]; exact hlowE x h1 h2
  have hF' : ∀ x : Fin T, d.F ≤ x.val → x.val < d.U → A (π x) = [] ∧ H (π x) = 0 := by
    intro x h1 h2
    have hm := InitMove.piV_mem bb X NR d.F d.U x.val (by omega) (by omega) h1 h2
    exact hF (π x) hm.1 hm.2
  obtain ⟨H1, A2, s1, ho⟩ := NearCubicWires.SourceSkeleton.InitE.init2_runE pl L C cVc cS cR q b (fun x => H (π x)) (fun x => A (π x))
    hAr' hHr' hAw' hHw' hlow' hF' hfit hVR hVLR hRc hU0 hS hR hB hv
  set Rc := Once.Rc eR L C q with hRcd
  -- the header region is blank after `init2`
  have hreg : ∀ x : Fin T, ZB d eX pX gW X ≤ x.val → x.val < ZB d eX pX gW X + 32 + NS →
      A2 x = List.replicate Rc false ∧ H1 x = 0 := by
    intro x h1 h2
    refine ho.blank x (by omega) (by omega) ?_
    unfold KeptM Kept; rw [hJB]; omega
  obtain ⟨A8, s2, hd⟩ := pl.head_run hh DP CP DW CW DL CL hN mode L target q Rc hcap hqR hLw hTw h5 H1 A2 hreg
    ho.qres.1 ho.qres.2 ho.drv.1 ho.drv.2 ho.log.1 ho.log.2
  have s := InitMove.relocate bb X NR T hroom (s1.seq s2)
  refine ⟨fun y => H1 (ρ y), fun y => A8 (ρ y), s, ?_⟩
  -- transport of the fixed tapes below the strip
  have lowF : ∀ y : Fin T, y.val < bb → A8 (ρ y) = A2 y ∧ H1 (ρ y) = H1 y := by
    intro y hy
    rw [fixρ y (Or.inl hy)]
    exact ⟨hd.frame y (by omega), rfl⟩
  have vr : ∀ i : Fin 5, (Dims.rsT pl.ext.rest pl.hT i).val < bb := fun i => by
    have := i.isLt; show d.B + 19 + restPc eX pX gW + i.val < bb; omega
  have vm : ∀ i : Fin 5, (Dims.mT pl.ext2 pl.hT i).val < bb := fun i => by
    rw [pl.mT_val]; have := i.isLt; omega
  have vt : ∀ i : Fin 5, (Dims.rfT pl.ext2 pl.hT i).val < bb := fun i => by
    rw [pl.rfT_val]; have := i.isLt; omega
  have ve : ∀ kk : Fin 13, (Dims.encT (d := d) pl.hT kk).val < bb := fun kk => by
    have := kk.isLt; show d.F + d.rt + kk.val < bb; omega
  have v11 : (d.scr pl.hT 11).val < bb := by show d.scrV 11 < bb; omega
  have v12 : (d.scr pl.hT 12).val < bb := by show d.scrV 12 < bb; omega
  have vw1 : (Dims.rewind2Slots pl.ext.rest.ext pl.hT 1).val < bb := by
    show d.rw2V 1 < bb; unfold Dims.rw2V; simp; omega
  have vw2 : (Dims.rewind2Slots pl.ext.rest.ext pl.hT 2).val < bb := by
    show d.rw2V 2 < bb; unfold Dims.rw2V; simp; omega
  -- the eight residents
  have zres : ∀ i : Fin 12, i.val < 8 → ∀ k : Fin 32, k.val = i.val →
      ρ (Dims.hrT (ext3 pl hh) pl.hT i) = pl.zT hh k := by
    intro i hi k hk
    apply Fin.ext
    rw [InitMove.rhoF_val, Dims.hrT_val, pl.zT_val, InitMove.rhoV_res bb X NR _ (by omega) (by omega)]
    unfold ZB; omega
  have zH : ∀ k : Fin 32, H1 (pl.zT hh k) = 0 := fun k =>
    (hreg _ (by rw [pl.zT_val]; omega) (by rw [pl.zT_val]; have := k.isLt; omega)).2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(lowF _ v11).1, (lowF _ v11).2]; exact ho.drv
  · rw [(lowF _ v12).1, (lowF _ v12).2]; exact ho.log
  · rw [(lowF _ vw1).1, (lowF _ vw1).2]; exact ho.rew1
  · rw [(lowF _ vw2).1, (lowF _ vw2).2]; exact ho.rew2
  · intro i; rw [(lowF _ (vm i)).1, (lowF _ (vm i)).2]; exact ho.master i
  · intro i; rw [(lowF _ (vt i)).1, (lowF _ (vt i)).2]; exact ho.target i
  · rw [(lowF _ (vr 0)).1, (lowF _ (vr 0)).2]; exact ho.big
  · rw [(lowF _ (vr 1)).1, (lowF _ (vr 1)).2]; exact ho.small
  · rw [(lowF _ (vr 2)).1, (lowF _ (vr 2)).2]; exact ho.curT
  · rw [(lowF _ (vr 3)).1, (lowF _ (vr 3)).2]; exact ho.wres
  · rw [(lowF _ (vr 4)).1, (lowF _ (vr 4)).2]; exact ho.qres
  · intro en old; rw [(lowF _ (ve 3)).1, (lowF _ (ve 3)).2]; exact ho.enc3 en old
  · intro en old; rw [(lowF _ (ve 6)).1, (lowF _ (ve 6)).2]; exact ho.enc7 en old
  · intro en old; rw [(lowF _ (ve 7)).1, (lowF _ (ve 7)).2]; exact ho.enc8 en old
  · intro en old; rw [(lowF _ (ve 8)).1, (lowF _ (ve 8)).2]; exact ho.enc9 en old
  · intro en old; rw [(lowF _ (ve 9)).1, (lowF _ (ve 9)).2]; exact ho.enc10 en old
  · intro en xs; rw [(lowF _ (ve 10)).1, (lowF _ (ve 10)).2]; exact ho.app2 en xs
  · intro en xs; rw [(lowF _ (ve 11)).1, (lowF _ (ve 11)).2]; exact ho.app4 en xs
  · intro en xs; rw [(lowF _ (ve 12)).1, (lowF _ (ve 12)).2]; exact ho.app5 en xs
  · intro kk hk; rw [(lowF _ (ve kk)).1, (lowF _ (ve kk)).2]; exact ho.encOld kk hk
  · show A8 (ρ _) = _ ∧ H1 (ρ _) = _
    rw [zres 0 (by decide) 0 rfl]; exact ⟨hd.z0, zH 0⟩
  · show A8 (ρ _) = _ ∧ H1 (ρ _) = _
    rw [zres 1 (by decide) 1 rfl]; exact ⟨hd.z1, zH 1⟩
  · show A8 (ρ _) = _ ∧ H1 (ρ _) = _
    rw [zres 2 (by decide) 2 rfl]; exact ⟨hd.z2, zH 2⟩
  · show A8 (ρ _) = _ ∧ H1 (ρ _) = _
    rw [zres 3 (by decide) 3 rfl]; exact ⟨hd.z3, zH 3⟩
  · show A8 (ρ _) = _ ∧ H1 (ρ _) = _
    rw [zres 4 (by decide) 4 rfl]; exact ⟨hd.z4, zH 4⟩
  · show A8 (ρ _) = _ ∧ H1 (ρ _) = _
    rw [zres 5 (by decide) 5 rfl]; exact ⟨hd.z5, zH 5⟩
  · show A8 (ρ _) = _ ∧ H1 (ρ _) = _
    rw [zres 6 (by decide) 6 rfl]; exact ⟨hd.z6, zH 6⟩
  · show A8 (ρ _) = _ ∧ H1 (ρ _) = _
    rw [zres 7 (by decide) 7 rfl]; exact ⟨hd.z7, zH 7⟩
  · -- blank
    intro y h1 h2 hk
    unfold KeptS at hk
    show A8 (ρ y) = _ ∧ H1 (ρ y) = _
    by_cases c1 : y.val < bb
    · rw [(lowF y c1).1, (lowF y c1).2]
      exact ho.blank y h1 h2 (by unfold KeptM Kept; rw [hJB]; omega)
    by_cases c2 : y.val < bb + NR
    · -- a strip tape `hrT i`, `8 ≤ i < NR`: SI's `zT i`, still blank
      have e : ρ y = pl.zT hh ⟨y.val - bb, by omega⟩ := by
        apply Fin.ext
        rw [InitMove.rhoF_val, pl.zT_val, InitMove.rhoV_res bb X NR _ (by omega) c2]
        unfold ZB; simp only; omega
      rw [e]
      exact ⟨hd.zrest _ (by simp only; omega), zH _⟩
    by_cases c3 : y.val < bb + NR + X
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, c3⟩)))))) hk
    by_cases c4 : y.val < bb + NR + X + 3
    · -- SI's three unused tapes `B+29+Pc .. B+31+Pc`
      have e : (ρ y).val = y.val - NR - X := by
        rw [InitMove.rhoF_val, InitMove.rhoV_u bb X NR _ (by omega) c4]
      have hlt : (ρ y).val < bb + 3 := by omega
      rw [hd.frame (ρ y) (by unfold ZB; omega)]
      exact ho.blank (ρ y) (by omega) (by omega) (by unfold KeptM Kept; rw [hJB]; omega)
    · rw [fixρ y (Or.inr (by omega))]
      by_cases c5 : y.val < ZB d eX pX gW X + 32
      · have e : y = pl.zT hh ⟨y.val - ZB d eX pX gW X, by omega⟩ := by
          apply Fin.ext; rw [pl.zT_val]; simp only; unfold ZB at *; omega
        rw [e]
        exact ⟨hd.zrest _ (by simp only; unfold ZB at *; omega), zH _⟩
      · rw [hd.frame y (by unfold ZB at *; omega)]
        exact ho.blank y h1 h2 (by unfold KeptM Kept; rw [hJB]; omega)
  · -- the moved workspace
    intro y h1 h2
    show Rc ≤ (A8 (ρ y)).length ∧ H1 (ρ y) = 0
    have e : (ρ y).val = y.val + 3 - NR := by
      rw [InitMove.rhoF_val, InitMove.rhoV_ws bb X NR _ h1 h2]
    rw [hd.frame (ρ y) (by unfold ZB; omega)]
    exact ho.junk (ρ y) (by rw [hJB]; omega) (by rw [hJB]; omega)
  · -- the header scratch
    intro y h1 h2
    show Rc ≤ (A8 (ρ y)).length ∧ H1 (ρ y) = 0
    rw [fixρ y (Or.inr (by omega))]
    exact ⟨hd.scr y (by unfold ZB; omega) (by unfold ZB; omega), (hreg y (by unfold ZB; omega) (by unfold ZB; omega)).2⟩
  · intro y h1 h2
    show A8 (ρ y) = A y ∧ H1 (ρ y) = H y
    rw [(lowF y (by omega)).1, (lowF y (by omega)).2]
    have hb := ho.below y h1 h2
    rw [fixπ y (Or.inl (by omega))] at hb
    exact hb
  · intro y h1 h2
    show H1 (ρ y) = 0
    rw [(lowF y (by omega)).2]
    exact ho.low y h1 h2
  · intro y h1
    show A8 (ρ y) = A y ∧ H1 (ρ y) = H y
    rw [fixρ y (Or.inr (by omega)), hd.frame y (by omega)]
    have ha := ho.above y h1
    rw [fixπ y (Or.inr (by omega))] at ha
    exact ha

/-! ## from `SourceSkelInitRes` (E-copies) -/

/-- **The init on S's port map with `1^Rk`, `0^(Rk+2)` and `1^D`**: `initS ; rk ; d` (ONE fixed machine). -/
def initRMachineE (NR : Nat) (hNR : NR ≤ 32) {NE : Nat} (hE : ResExt d eX pX gW X NS NE)
    (L C cVc cS cR DP CP DW CW DL CL : Nat) (hN : nsOf DP DW DL ≤ NS) (mode : Bool) (target DD CD : Nat)
    (hu : 18 + 14 + 2*DD ≤ NE) :=
  Composition.machine
    (Composition.machine (initSMachineE pl hh NR hNR L C cVc cS cR DP CP DW CW DL CL hN mode target)
      (rkM pl hh hE 0 (by omega)))
    (dM pl hh hE 18 DD CD hu)

def initRCostE (L C cVc cS cR DP CP DW CW DL CL : Nat) (mode : Bool) (target q b DD CD : Nat) : Nat :=
  initSCostE pl L C cVc cS cR DP CP DW CW DL CL mode target q b + 1 + rkCost (Once.Rc eR L C q) + 1 +
    PCPSerializerCapacity.Power.budget DD CD q

/-- **The init run with the three new residents.** Hypotheses: `initS_runE`'s, `13 ≤ NR ≤ 32`, the extension room `ResExt` with
`18 + 14 + 2·DD ≤ NE`. Exit: `InitInv` with `valR` (`hrT 10 = 1^Rk`, `hrT 11 = 0^(Rk+2)`, `hrD = pad Rc 1^(CD(q+1)^DD)`), the extension
scratch used up to `18 + 14 + 2·DD`. -/
theorem initR_runE (NR : Nat) (hNR13 : 13 ≤ NR) (hNR : NR ≤ 32) {NE : Nat} (hE : ResExt d eX pX gW X NS NE)
    (L C cVc cS cR DP CP DW CW DL CL : Nat) (hN : nsOf DP DW DL ≤ NS) (mode : Bool) (target q b DD CD : Nat)
    (hu : 18 + 14 + 2*DD ≤ NE) (H : Fin T → ℕ) (A : Fin T → List Bool)
    (hAr : A pl.ar = UnaryTemplate.tape q) (hHr : H pl.ar = 0)
    (hAw : A pl.wd = List.replicate b true) (hHw : H pl.wd = 0)
    (hlowE : ∀ x : Fin T, 278 ≤ x.val → x.val < 284 →
      (A x).length ≤ cVc * RuntimeShape.tableClass L eV q ∧ H x = 0)
    (hF : ∀ x : Fin T, d.F ≤ x.val → x.val < d.U → A x = [] ∧ H x = 0)
    (hfit : q + 3 + Dimension.prefixCost eR eV L C cVc q ≤ Once.Rc eR L C q)
    (hVR : cVc * RuntimeShape.tableClass L eV q ≤ Once.Rc eR L C q)
    (hVLR : VLog eV L cVc q ≤ Once.Rc eR L C q) (hRc : 2 ≤ Once.Rc eR L C q)
    (hU0 : U0 L q ≤ Once.Rc eR L C q)
    (hS : cS * (cVc * RuntimeShape.tableClass L eV q + 1) + 2 ≤ Once.Rc eR L C q)
    (hR : cR * (cVc * RuntimeShape.tableClass L eV q + 1) + 2 ≤ Once.Rc eR L C q)
    (hB : cVc * RuntimeShape.tableClass L eV q + 1 + 2 ≤ Once.Rc eR L C q)
    (hv : b + 2 ≤ Once.Rc eR L C q)
    (hcap : CloseoutRowsEstimatorParity.Capacity.value q ≤ Once.Rc eR L C q) (hqR : q ≤ Once.Rc eR L C q)
    (hLw : (frame (natWord L)).length ≤ Once.Rc eR L C q + 2)
    (hTw : (frame (natWord target)).length ≤ Once.Rc eR L C q + 2) (h5 : 5 ≤ Once.Rc eR L C q) :
    ∃ (H' : Fin T → ℕ) (A' : Fin T → List Bool),
      Step (initRMachineE pl hh NR hNR hE L C cVc cS cR DP CP DW CW DL CL hN mode target DD CD hu)
        (initRCostE pl L C cVc cS cR DP CP DW CW DL CL mode target q b DD CD) H A H' A' ∧
      InitInv pl hh NR NE L cS cR q b (Once.Rc eR L C q) (cVc * RuntimeShape.tableClass L eV q) CP CW CL DP DW DL
        mode target (valR (Once.Rc eR L C q) DD CD q) (18 + 14 + 2*DD) H A H' A' := by
  obtain ⟨H1, A1, s0, ho⟩ := initS_runE pl hh NR (by omega) hNR L C cVc cS cR DP CP DW CW DL CL hN mode target q b H A
    hAr hHr hAw hHw hlowE hF hfit hVR hVLR hRc hU0 hS hR hB hv hcap hqR hLw hTw h5
  have i0 := start pl hh NR NE (by omega) hNR hE L cS cR q b _ _ CP CW CL DP DW DL mode target H H1 A A1 ho
  obtain ⟨A2, s1, i1⟩ := rk_step pl hh hNR13 hNR hE (u := 0) (by omega) i0 rfl rfl
  obtain ⟨A3, s2, i2⟩ := d_step pl hh hNR13 hNR hE DD CD hu i1 (by simp)
  refine ⟨H1, A3, (s0.seq s1).seq s2, ?_⟩
  have e : (fun i => if i = 12 then some (ZeroPadding.pad (Once.Rc eR L C q) (List.replicate (CD*(q+1)^DD) true))
      else (fun i => if i = 10 then some (List.replicate (Rk (Once.Rc eR L C q)) true)
        else if i = 11 then some (List.replicate (Rk (Once.Rc eR L C q) + 2) false)
        else (fun _ => (none : Option (List Bool))) i) i) = valR (Once.Rc eR L C q) DD CD q := rfl
  rw [← e]
  exact i2

/-! ## from `SourceSkelInitAll` (E-copies) -/

/-- **The whole init** (ONE fixed machine). -/
def initAllMachineE (NR : Nat) (hNR : NR ≤ 32) {NE : Nat} (hE : ResExt d eX pX gW X NS NE)
    (L C cVc cS cR DP CP DW CW DL CL : Nat) (hN : nsOf DP DW DL ≤ NS) (mode : Bool) (target DD CD Dcw Ccw : Nat)
    (hNE : uAll DD Dcw ≤ NE) :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (initRMachineE pl hh NR hNR hE L C cVc cS cR DP CP DW CW DL CL hN mode target DD CD (by unfold uAll at hNE; omega))
    (cwM pl hh mode (18 + 14 + 2*DD)))
    (polyResM pl hh hE 9 (by decide) (18 + 14 + 2*DD + 81) Dcw Ccw (by unfold uAll at hNE; omega)))
    (g0M pl hh (18 + 14 + 2*DD + 81 + 14 + 2*Dcw)))
    (g1M pl hh (18 + 14 + 2*DD + 81 + 14 + 2*Dcw + 4))

def initAllCostE (L C cVc cS cR DP CP DW CW DL CL : Nat) (mode : Bool) (target q b DD CD Dcw Ccw : Nat) : Nat :=
  initRCostE pl L C cVc cS cR DP CP DW CW DL CL mode target q b DD CD + 1 + cwCost mode (CL*(q+1)^DL) + 1 +
    PCPSerializerCapacity.Power.budget Dcw Ccw q + 1 + ((2*q+6) + 1 + (2*(q+q)+6)) + 1 +
    ((2 * (List.replicate 2 true).length + 2) + 1 + SourceRequest.CurComp.subCost (InitPost.Ms L q))

/-- **The whole init, run.** From the first site entry, under SI's `init2_run`/`head_run` hypotheses at `Rc = Once.Rc eR L C q` and the
four resident bounds, ONE fixed machine reaches `InitInv … (valAll …) (uAll DD Dcw)`. -/
theorem initAll_runE (NR : Nat) (hNR16 : 16 ≤ NR) (hNR : NR ≤ 32) {NE : Nat} (hE : ResExt d eX pX gW X NS NE)
    (L C cVc cS cR DP CP DW CW DL CL : Nat) (hN : nsOf DP DW DL ≤ NS) (mode : Bool) (target q b DD CD Dcw Ccw : Nat)
    (hNE : uAll DD Dcw ≤ NE) (H : Fin T → ℕ) (A : Fin T → List Bool)
    (hAr : A pl.ar = UnaryTemplate.tape q) (hHr : H pl.ar = 0)
    (hAw : A pl.wd = List.replicate b true) (hHw : H pl.wd = 0)
    (hlowE : ∀ x : Fin T, 278 ≤ x.val → x.val < 284 →
      (A x).length ≤ cVc * RuntimeShape.tableClass L eV q ∧ H x = 0)
    (hF : ∀ x : Fin T, d.F ≤ x.val → x.val < d.U → A x = [] ∧ H x = 0)
    (hfit : q + 3 + Dimension.prefixCost eR eV L C cVc q ≤ Once.Rc eR L C q)
    (hVR : cVc * RuntimeShape.tableClass L eV q ≤ Once.Rc eR L C q)
    (hVLR : VLog eV L cVc q ≤ Once.Rc eR L C q) (hRc : 2 ≤ Once.Rc eR L C q)
    (hU0 : U0 L q ≤ Once.Rc eR L C q)
    (hS : cS * (cVc * RuntimeShape.tableClass L eV q + 1) + 2 ≤ Once.Rc eR L C q)
    (hR : cR * (cVc * RuntimeShape.tableClass L eV q + 1) + 2 ≤ Once.Rc eR L C q)
    (hB : cVc * RuntimeShape.tableClass L eV q + 1 + 2 ≤ Once.Rc eR L C q)
    (hv : b + 2 ≤ Once.Rc eR L C q)
    (hcap : CloseoutRowsEstimatorParity.Capacity.value q ≤ Once.Rc eR L C q) (hqR : q ≤ Once.Rc eR L C q)
    (hLw : (frame (natWord L)).length ≤ Once.Rc eR L C q + 2)
    (hTw : (frame (natWord target)).length ≤ Once.Rc eR L C q + 2) (h5 : 5 ≤ Once.Rc eR L C q)
    (hLd : CL*(q+1)^DL + 2 ≤ Once.Rc eR L C q) (hC82 : 82472 ≤ Once.Rc eR L C q)
    (hq2 : 2*q + 1 ≤ Once.Rc eR L C q) (hMs : 2 * InitPost.Ms L q + 5 ≤ Once.Rc eR L C q) :
    ∃ (H' : Fin T → ℕ) (A' : Fin T → List Bool),
      Step (initAllMachineE pl hh NR hNR hE L C cVc cS cR DP CP DW CW DL CL hN mode target DD CD Dcw Ccw hNE)
        (initAllCostE pl L C cVc cS cR DP CP DW CW DL CL mode target q b DD CD Dcw Ccw) H A H' A' ∧
      InitInv pl hh NR NE L cS cR q b (Once.Rc eR L C q) (cVc * RuntimeShape.tableClass L eV q) CP CW CL DP DW DL
        mode target (valAll mode L q (Once.Rc eR L C q) DD CD Dcw Ccw CL DL) (uAll DD Dcw) H A H' A' := by
  obtain ⟨H1, A1, s0, i0⟩ := initR_runE pl hh NR (by omega) hNR hE L C cVc cS cR DP CP DW CW DL CL hN mode target q b DD CD
    (by unfold uAll at hNE; omega) H A hAr hHr hAw hHw hlowE hF hfit hVR hVLR hRc hU0 hS hR hB hv hcap hqR hLw hTw h5
  obtain ⟨A2, s1, i1⟩ := cw_step pl hh (by omega) hNR hE (by unfold uAll at hNE; omega) i0 (by simp [valR]) hLd hC82
  obtain ⟨A3, s2, i2⟩ := polyRes_step pl hh hNR hE 9 (by decide) (by decide) (by omega) Dcw Ccw
    (by unfold uAll at hNE; omega) i1 (by simp [valR])
  obtain ⟨A4, s3, i3⟩ := g0_step pl hh hNR16 hNR hE (by unfold uAll at hNE; omega) i2 (by simp [valR]) hq2
  obtain ⟨A5, s4, i4⟩ := g1_step pl hh hNR16 hNR hE (by unfold uAll at hNE; omega) i3 (by simp [valR]) hMs
  exact ⟨H1, A5, (((s0.seq s1).seq s2).seq s3).seq s4, i4⟩

/-! ## from `SourceSkelInitXA` (E-copies) -/

def initAllXMachineE (NR : Nat) (hNR : NR ≤ 32) {NE : Nat} (hE : ResExt d eX pX gW X NS NE)
    (L C cVc cS cR DP CP DW CW DL CL : Nat) (hN : nsOf DP DW DL ≤ NS) (mode : Bool) (target DD CD Dcw Ccw : Nat)
    (hNE : uAll DD Dcw ≤ NE) {sM : Nat} (M : Machine T sM) :=
  Composition.machine (Composition.machine (Composition.machine
    (initAllMachineE pl hh NR hNR hE L C cVc cS cR DP CP DW CW DL CL hN mode target DD CD Dcw Ccw hNE)
    (tkM pl hh (uAll DD Dcw))) (bM pl hh (uAll DD Dcw + 5))) M

/-- The extended init's cost. -/
def initAllXCostE (L C cVc cS cR DP CP DW CW DL CL : Nat) (mode : Bool) (target q b DD CD Dcw Ccw mcost : Nat) : Nat :=
  initAllCostE pl L C cVc cS cR DP CP DW CW DL CL mode target q b DD CD Dcw Ccw + 1 + tkCost (normalizedLiveCount q L) + 1 +
    (2*b+6) + 1 + mcost

/-- **The extended init, run**: the four stages chained, ending in `InitInv … (valAllX …)`. -/
theorem initAllX_runE (NR : Nat) (hNR20 : 20 ≤ NR) (hNR : NR ≤ 32) {NE : Nat} (hE : ResExt d eX pX gW X NS NE)
    (L C cVc cS cR DP CP DW CW DL CL : Nat) (hN : nsOf DP DW DL ≤ NS) (mode : Bool) (target q b DD CD Dcw Ccw : Nat)
    (hNE : uAll DD Dcw ≤ NE) (MB : List Bool) {sM : Nat} (M : Machine T sM) (mcost wM : Nat)
    (hmeta : MetaRun pl hh NR NE L cS cR q b (Once.Rc eR L C q) (cVc * RuntimeShape.tableClass L eV q) CP CW CL DP DW DL mode target MB
      (uAll DD Dcw + 7) M mcost wM)
    (hK : 2 * normalizedLiveCount q L + 4 ≤ Once.Rc eR L C q)
    (H : Fin T → ℕ) (A : Fin T → List Bool)
    (hAr : A pl.ar = UnaryTemplate.tape q) (hHr : H pl.ar = 0)
    (hAw : A pl.wd = List.replicate b true) (hHw : H pl.wd = 0)
    (hlowE : ∀ x : Fin T, 278 ≤ x.val → x.val < 284 →
      (A x).length ≤ cVc * RuntimeShape.tableClass L eV q ∧ H x = 0)
    (hF : ∀ x : Fin T, d.F ≤ x.val → x.val < d.U → A x = [] ∧ H x = 0)
    (hfit : q + 3 + Dimension.prefixCost eR eV L C cVc q ≤ Once.Rc eR L C q)
    (hVR : cVc * RuntimeShape.tableClass L eV q ≤ Once.Rc eR L C q)
    (hVLR : VLog eV L cVc q ≤ Once.Rc eR L C q) (hRc : 2 ≤ Once.Rc eR L C q)
    (hU0 : U0 L q ≤ Once.Rc eR L C q)
    (hS : cS * (cVc * RuntimeShape.tableClass L eV q + 1) + 2 ≤ Once.Rc eR L C q)
    (hR : cR * (cVc * RuntimeShape.tableClass L eV q + 1) + 2 ≤ Once.Rc eR L C q)
    (hB : cVc * RuntimeShape.tableClass L eV q + 1 + 2 ≤ Once.Rc eR L C q)
    (hv : b + 2 ≤ Once.Rc eR L C q)
    (hcap : CloseoutRowsEstimatorParity.Capacity.value q ≤ Once.Rc eR L C q) (hqR : q ≤ Once.Rc eR L C q)
    (hLw : (frame (natWord L)).length ≤ Once.Rc eR L C q + 2)
    (hTw : (frame (natWord target)).length ≤ Once.Rc eR L C q + 2) (h5 : 5 ≤ Once.Rc eR L C q)
    (hLd : CL*(q+1)^DL + 2 ≤ Once.Rc eR L C q) (hC82 : 82472 ≤ Once.Rc eR L C q)
    (hq2 : 2*q + 1 ≤ Once.Rc eR L C q) (hMs : 2 * InitPost.Ms L q + 5 ≤ Once.Rc eR L C q) :
    ∃ (H' : Fin T → ℕ) (A' : Fin T → List Bool),
      Step (initAllXMachineE pl hh NR hNR hE L C cVc cS cR DP CP DW CW DL CL hN mode target DD CD Dcw Ccw hNE M)
        (initAllXCostE pl L C cVc cS cR DP CP DW CW DL CL mode target q b DD CD Dcw Ccw mcost) H A H' A' ∧
      InitInv pl hh NR NE L cS cR q b (Once.Rc eR L C q) (cVc * RuntimeShape.tableClass L eV q) CP CW CL DP DW DL
        mode target (valAllX mode L q (Once.Rc eR L C q) DD CD Dcw Ccw CL DL b MB) (uAll DD Dcw + 7 + wM) H A H' A' := by
  have hwM := hmeta.1
  obtain ⟨H1, A1, s0, i0⟩ := initAll_runE pl hh NR (by omega) hNR hE L C cVc cS cR DP CP DW CW DL CL hN mode target q b DD CD Dcw Ccw
    hNE H A hAr hHr hAw hHw hlowE hF hfit hVR hVLR hRc hU0 hS hR hB hv hcap hqR hLw hTw h5 hLd hC82 hq2 hMs
  obtain ⟨A2, s1, i1⟩ := tk_step pl hh (by omega) hNR hE (by omega) i0 (by simp [valAll]) (by simp [valAll, valR]) hK
  obtain ⟨A3, s2, i2⟩ := b_step pl hh hNR20 hNR hE (by omega) i1 (by simp [valAll, valR])
  obtain ⟨A4, s3, i3⟩ := hmeta.2 _ H H1 A A3 i2 (by simp [valAll]) (by simp [valAll]) (by simp) (by simp [valAll, valR])
    (by simp [valAll, valR])
  have hval : (fun j => if j = 17 then some (ZeroPadding.pad (Once.Rc eR L C q) (frame MB))
      else if j = 18 then some (ZeroPadding.pad (Once.Rc eR L C q) (frame (List.replicate MB.length true)))
      else (fun j => if j = 19 then some (ZeroPadding.pad (Once.Rc eR L C q) (List.replicate b true))
        else (fun j => if j = 16 then some (ZeroPadding.pad (Once.Rc eR L C q) (UnaryTemplate.tape (normalizedLiveCount q L)))
          else valAll mode L q (Once.Rc eR L C q) DD CD Dcw Ccw CL DL j) j) j) =
      valAllX mode L q (Once.Rc eR L C q) DD CD Dcw Ccw CL DL b MB := by
    funext j
    unfold valAllX
    by_cases h16 : j = 16
    · subst h16; simp
    by_cases h17 : j = 17
    · subst h17; simp
    by_cases h18 : j = 18
    · subst h18; simp
    by_cases h19 : j = 19
    · subst h19; simp
    simp [h16, h17, h18, h19]
  refine ⟨H1, A4, ((s0.seq s1).seq s2).seq s3, ?_⟩
  rw [← hval]
  exact i3

/-- **The guarded extended init** (S's guard on the clear driver's cell). -/
def guardAllXE (NR : Nat) (hNR : NR ≤ 32) {NE : Nat} (hE : ResExt d eX pX gW X NS NE)
    (L C cVc cS cR DP CP DW CW DL CL : Nat) (hN : nsOf DP DW DL ≤ NS) (mode : Bool) (target DD CD Dcw Ccw : Nat)
    (hNE : uAll DD Dcw ≤ NE) {sM : Nat} (M : Machine T sM) :=
  CloseoutRowsOriginalSwitch.machine (CloseoutRowsOriginalSwitch.stop T)
    (initAllXMachineE pl hh NR hNR hE L C cVc cS cR DP CP DW CW DL CL hN mode target DD CD Dcw Ccw hNE M) (d.scr pl.hT 11)

/-- **First site entry: produce.** -/
theorem guardAllXE_blank (NR : Nat) (hNR : NR ≤ 32) {NE : Nat} (hE : ResExt d eX pX gW X NS NE)
    (L C cVc cS cR DP CP DW CW DL CL : Nat) (hN : nsOf DP DW DL ≤ NS) (mode : Bool) (target q b DD CD Dcw Ccw : Nat)
    (hNE : uAll DD Dcw ≤ NE) {sM : Nat} (M : Machine T sM) (mcost : Nat) (H H' : Fin T → ℕ) (A A' : Fin T → List Bool)
    (hrun : Step (initAllXMachineE pl hh NR hNR hE L C cVc cS cR DP CP DW CW DL CL hN mode target DD CD Dcw Ccw hNE M)
      (initAllXCostE pl L C cVc cS cR DP CP DW CW DL CL mode target q b DD CD Dcw Ccw mcost) H A H' A')
    (hd : A (d.scr pl.hT 11) = []) :
    Step (guardAllXE pl hh NR hNR hE L C cVc cS cR DP CP DW CW DL CL hN mode target DD CD Dcw Ccw hNE M)
      (initAllXCostE pl L C cVc cS cR DP CP DW CW DL CL mode target q b DD CD Dcw Ccw mcost + 2) H A H' A' :=
  CloseoutRowsOriginalSwitch.false_run _ _ _ hrun (by rw [hd]; simp [readTapeBit])

/-- **Every later site entry**: the driver reads `true`, the guard skips at cost `2` and changes nothing. -/
theorem entry_skipXE (NR : Nat) (hNR : NR ≤ 32) {NE : Nat} (hE : ResExt d eX pX gW X NS NE)
    (L C cVc cS cR DP CP DW CW DL CL : Nat) (hN : nsOf DP DW DL ≤ NS) (mode : Bool) (target DD CD Dcw Ccw : Nat)
    (hNE : uAll DD Dcw ≤ NE) {sM : Nat} (M : Machine T sM) (Rc : Nat) (hRc : 1 ≤ Rc) (H0 : Fin T → ℕ) (A0 : Fin T → List Bool)
    (hdrv : A0 (d.scr pl.hT 11) = List.replicate Rc true) (hdrvH : H0 (d.scr pl.hT 11) = 0) :
    Step (guardAllXE pl hh NR hNR hE L C cVc cS cR DP CP DW CW DL CL hN mode target DD CD Dcw Ccw hNE M) (0 + 2)
      H0 A0 H0 A0 := by
  refine CloseoutRowsOriginalSwitch.true_run _ _ _ (SourceConstruction.stop_step H0 A0) ?_
  rw [hdrv, hdrvH]
  obtain ⟨k, rfl⟩ : ∃ k, Rc = k + 1 := ⟨Rc - 1, by omega⟩
  rfl

end
end NearCubicWires.SourceSkeleton.InitS
end

