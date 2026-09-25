import Proof.Packets.PacketsMetaSeedCount
import Proof.Rows.RowsPrimeReserve

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.CostBound
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.P1Closure
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.BlockPlatform NearCubicWires.ValidatorPolynomialDomination
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section

/-! ## 1. The fixed constants -/

/-- `Bf` (the THR traversal bound) as a polynomial of `q+|input|`. -/
def cF : Nat := Classical.choose BaseLayout.fns_poly
def dF : Nat := Classical.choose (Classical.choose_spec BaseLayout.fns_poly)
/-- `bF` (the base stage's bound) as a polynomial of `|input|`. -/
def cB : Nat := Classical.choose ThrSelBase.b_poly
def dB : Nat := Classical.choose (Classical.choose_spec ThrSelBase.b_poly)

/-- **The degree** (one fixed number: every exponent below is at most it). -/
def D : Nat := BaseLayout.thrRd + dF + BaseLayout.symRd + BaseLayout.symD + dB + 163 + 9 + 1

/-- The table coefficients (per cell, at measure `q+|input|`). -/
def tabT : Nat := 20 + 8*(BaseLayout.thrRc+1) + cF + 108
def tabS : Nat := 20 + 8*(BaseLayout.symRc+1) + BaseLayout.symC*5^BaseLayout.symD + 108

theorem Bf_le (q T : Nat) : BaseLayout.Bf q T ≤ cF*(q+T+1)^dF :=
  (Classical.choose_spec (Classical.choose_spec BaseLayout.fns_poly) q T).mono (by omega)

theorem bF_le (T : Nat) : ThrSelBase.bF T ≤ cB*(T+1)^dB :=
  (Classical.choose_spec (Classical.choose_spec ThrSelBase.b_poly) T).mono (by omega)

theorem pow_D (m d : Nat) (hd : d ≤ D) : (m+1)^d ≤ (m+1)^D := Nat.pow_le_pow_right (by omega) hd

theorem self_le_D (m : Nat) : m+1 ≤ (m+1)^D := by
  have h := pow_D m 1 (by unfold D; omega)
  rw [pow_one] at h
  exact h

/-! ## 2. The table term: `2^s` cells, each linear in `q`, `R`, `Bt` -/

theorem body_le (s q R Bt : Nat) (hs : s ≤ q) :
    ThrCell.bodyCost s q R Bt + 4*((s+1)/2) + 53 ≤ 20*q+8*R+Bt+108 := by
  unfold ThrCell.bodyCost
  omega

/-- **One mask pass plus the `O(2^s)` blanks is `2^s` cells**: `2^((s+1)/2)·2^(s/2) = 2^s`. -/
theorem mask_le (s q R Bt : Nat) (hs : s ≤ q) :
    1+1+((2^((s+1)/2)*(ThrMask.rowCost s q R Bt+3)+3)+1+(1+1+(2*2^s+2)))+6*2^s+21 ≤
      2^s*(20*q+8*R+Bt+108) := by
  have hB := body_le s q R Bt hs
  have hpow : 2^((s+1)/2)*2^(s/2) = 2^s := by rw [← pow_add, BaseLayout.half_sum]
  have hle : 2^((s+1)/2) ≤ 2^s := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hX : 1 ≤ 2^s := Nat.one_le_two_pow
  unfold ThrMask.rowCost
  generalize ThrCell.bodyCost s q R Bt = B at hB ⊢
  generalize (s+1)/2 = h at hB hpow hle ⊢
  generalize 2^h = Y at hpow hle ⊢
  generalize 2^(s/2) = Z at hpow ⊢
  generalize 2^s = X at hpow hle hX ⊢
  have e1 : Y*(Z*(B+3)+3+1+(4*h+4)+3) = X*(B+3)+Y*(4*h+11) := by
    rw [← hpow]
    ring
  have e2 : Y*(4*h+11) ≤ X*(4*h+11) := Nat.mul_le_mul_right _ hle
  have e3 : X*(B+3)+X*(4*h+11)+39*X = X*(B+4*h+53) := by ring
  have e4 : X*(B+4*h+53) ≤ X*(20*q+8*R+Bt+108) := Nat.mul_le_mul_left _ hB
  omega

theorem thr_cell_le (q T : Nat) :
    20*q+8*BaseLayout.thrRes q T+BaseLayout.Bf q T+108 ≤ tabT*(q+T+1)^D := by
  have hB := Bf_le q T
  have h1 := self_le_D (q+T)
  have h2 := pow_D (q+T) BaseLayout.thrRd (by unfold D; omega)
  have h3 := pow_D (q+T) dF (by unfold D; omega)
  have h0 : 1 ≤ (q+T+1)^D := Nat.one_le_pow _ _ (by omega)
  have hR : BaseLayout.thrRes q T = (BaseLayout.thrRc+1)*(q+T+1)^BaseLayout.thrRd := rfl
  have m2 := Nat.mul_le_mul_left (BaseLayout.thrRc+1) h2
  have m3 := Nat.mul_le_mul_left cF h3
  have e : tabT*(q+T+1)^D = 20*(q+T+1)^D+8*((BaseLayout.thrRc+1)*(q+T+1)^D)+cF*(q+T+1)^D+108*(q+T+1)^D := by
    unfold tabT
    ring
  rw [hR]
  omega

theorem sym_cell_le (q T Bt : Nat) (hBt : Bt ≤ BaseLayout.symCap q T) :
    20*q+8*BaseLayout.symRes q T+Bt+108 ≤ tabS*(q+T+1)^D := by
  have h1 := self_le_D (q+T)
  have h2 := pow_D (q+T) BaseLayout.symRd (by unfold D; omega)
  have h3 := pow_D (q+T) BaseLayout.symD (by unfold D; omega)
  have h0 : 1 ≤ (q+T+1)^D := Nat.one_le_pow _ _ (by omega)
  have hR : BaseLayout.symRes q T = (BaseLayout.symRc+1)*(q+T+1)^BaseLayout.symRd := rfl
  have hcap : BaseLayout.symCap q T ≤ BaseLayout.symC*5^BaseLayout.symD*(q+T+1)^BaseLayout.symD := by
    unfold BaseLayout.symCap
    calc BaseLayout.symC*(q+T+5)^BaseLayout.symD ≤ BaseLayout.symC*(5*(q+T+1))^BaseLayout.symD :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = BaseLayout.symC*5^BaseLayout.symD*(q+T+1)^BaseLayout.symD := by rw [mul_pow]; ring
  have m2 := Nat.mul_le_mul_left (BaseLayout.symRc+1) h2
  have m3 := Nat.mul_le_mul_left (BaseLayout.symC*5^BaseLayout.symD) h3
  have e : tabS*(q+T+1)^D = 20*(q+T+1)^D+8*((BaseLayout.symRc+1)*(q+T+1)^D)+
      BaseLayout.symC*5^BaseLayout.symD*(q+T+1)^D+108*(q+T+1)^D := by
    unfold tabS
    ring
  rw [hR]
  omega

/-- **THR table term.** -/
theorem thr_table (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : Nat) :
    CompleteWork.thrMaskCost a r four L target + 6*2^(BaseLayout.thrLive r L)ᶜ.card ≤
      tabT*(2^(BaseLayout.thrLive r L)ᶜ.card*
        ((Request.thr r four L target).q+((Request.thr r four L target).input a).length+1)^D) := by
  have hm := mask_le (BaseLayout.thrLive r L)ᶜ.card r.q (KeyTop.RT a r four L target)
    (BaseLayout.Bf r.q (ThrWidth.T a r four L target)) (BaseLayout.card_compl_le _)
  have hc := thr_cell_le r.q (ThrWidth.T a r four L target)
  have hc' := Nat.mul_le_mul_left (2^(BaseLayout.thrLive r L)ᶜ.card) hc
  change CompleteWork.thrMaskCost a r four L target + 6*2^(BaseLayout.thrLive r L)ᶜ.card ≤
    tabT*(2^(BaseLayout.thrLive r L)ᶜ.card*(r.q+ThrWidth.T a r four L target+1)^D)
  have e : 2^(BaseLayout.thrLive r L)ᶜ.card*(tabT*(r.q+ThrWidth.T a r four L target+1)^D) =
      tabT*(2^(BaseLayout.thrLive r L)ᶜ.card*(r.q+ThrWidth.T a r four L target+1)^D) := by ring
  have hm' : CompleteWork.thrMaskCost a r four L target + 6*2^(BaseLayout.thrLive r L)ᶜ.card + 21 ≤
      2^(BaseLayout.thrLive r L)ᶜ.card*(20*r.q+8*KeyTop.RT a r four L target+
        BaseLayout.Bf r.q (ThrWidth.T a r four L target)+108) := hm
  have hR : KeyTop.RT a r four L target = BaseLayout.thrRes r.q (ThrWidth.T a r four L target) := rfl
  rw [hR] at hm'
  omega

/-- **SYM table term.** -/
theorem sym_table (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : Nat) :
    CompleteRow.symMaskCost a r four L target + 6*2^(BaseLayout.symLive r L)ᶜ.card ≤
      tabS*(2^(BaseLayout.symLive r L)ᶜ.card*
        ((Request.sym r four L target).q+((Request.sym r four L target).input a).length+1)^D) := by
  have hBt : SymVerdict.cost r L target (BaseLayout.symT a r four L target) (BaseLayout.symT a r four L target+3) ≤
      BaseLayout.symCap r.q (BaseLayout.symT a r four L target) :=
    (BaseLayout.sym_spec a r four L target (fun _ => 0) (fun _ => Nat.zero_le _)).2.2.2.2.2.2.2.2
  have hm := mask_le (BaseLayout.symLive r L)ᶜ.card r.q (BaseLayout.symRes r.q (BaseLayout.symT a r four L target))
    (SymVerdict.cost r L target (BaseLayout.symT a r four L target) (BaseLayout.symT a r four L target+3))
    (BaseLayout.card_compl_le _)
  have hc := sym_cell_le r.q (BaseLayout.symT a r four L target) _ hBt
  have hc' := Nat.mul_le_mul_left (2^(BaseLayout.symLive r L)ᶜ.card) hc
  change CompleteRow.symMaskCost a r four L target + 6*2^(BaseLayout.symLive r L)ᶜ.card ≤
    tabS*(2^(BaseLayout.symLive r L)ᶜ.card*(r.q+BaseLayout.symT a r four L target+1)^D)
  have e : 2^(BaseLayout.symLive r L)ᶜ.card*(tabS*(r.q+BaseLayout.symT a r four L target+1)^D) =
      tabS*(2^(BaseLayout.symLive r L)ᶜ.card*(r.q+BaseLayout.symT a r four L target+1)^D) := by ring
  have hm' : CompleteRow.symMaskCost a r four L target + 6*2^(BaseLayout.symLive r L)ᶜ.card + 21 ≤
      2^(BaseLayout.symLive r L)ᶜ.card*(20*r.q+8*BaseLayout.symRes r.q (BaseLayout.symT a r four L target)+
        SymVerdict.cost r L target (BaseLayout.symT a r four L target) (BaseLayout.symT a r four L target+3)+108) := hm
  omega

/-! ## 3. The small term: C5 is linear in its arguments, each a fixed power of `smallSize` -/

theorem c5_le (wT RT wS SS Rp T F : Nat) :
    ThrC5.c5Cost wT RT wS SS Rp T F ≤ 256*(wT+RT+wS+SS+Rp+T+F+1) := by
  unfold ThrC5.c5Cost ThrC5.keyCostU ThrSelBase.selCost ThrSelCasc.cascCost ThrSelBase.baseCost KeyTop.carryCost
  omega

theorem symc5_le (w R wS S : Nat) : SymC5.symCost w R wS S ≤ 256*(w+R+wS+S+1) := by
  unfold SymC5.symCost SymC5.cascCost SymC5.recCost SymC5.tcost KeyTop.carryCost
  omega

theorem succ_pow_le (S : Nat) (hS : 1 ≤ S) : (S+1)^D ≤ 2^D*S^D := by
  rw [← mul_pow]
  exact Nat.pow_le_pow_left (by omega) D

/-- The seed-count word lengths (`natBitLength NS`, `seedScratch NS`) from `NS ≤ 8·S^163`. -/
theorem seed_words_le (S N : Nat) (hN : N ≤ 8*S^163) :
    natBitLength N ≤ 9*(S+1)^D ∧ BaseLayout.seedScratch N ≤ 19*(S+1)^D := by
  have hb := SymBounds.natBitLength_le N
  have h1 : S^163 ≤ (S+1)^163 := Nat.pow_le_pow_left (by omega) _
  have h2 := pow_D S 163 (by unfold D; omega)
  have h0 : 1 ≤ (S+1)^D := Nat.one_le_pow _ _ (by omega)
  unfold BaseLayout.seedScratch
  omega

/-- The prime reserve against `smallSize`: `rpK·(T+cut+1)^3 ≤ rpK·40002^3·(S+1)^9`. -/
theorem rp_le (T cut S : Nat) (hT : T ≤ S) (hcut : cut ≤ 40000*S^3) :
    PrimeReserve.rpK*(T+cut+1)^3 ≤ (PrimeReserve.rpK*40002^3)*(S+1)^D := by
  have h3 : S^3 ≤ (S+1)^3 := Nat.pow_le_pow_left (by omega) _
  have h31 : S+1 ≤ (S+1)^3 := by
    have := Nat.pow_le_pow_right (show 0 < S+1 by omega) (show 1 ≤ 3 by omega)
    rw [pow_one] at this
    exact this
  have hb : T+cut+1 ≤ 40002*(S+1)^3 := by omega
  have h9 : (S+1)^9 ≤ (S+1)^D := pow_D S 9 (by unfold D; omega)
  have e : (40002*(S+1)^3)^3 = 40002^3*(S+1)^9 := by ring
  calc PrimeReserve.rpK*(T+cut+1)^3 ≤ PrimeReserve.rpK*(40002*(S+1)^3)^3 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb 3)
    _ = PrimeReserve.rpK*40002^3*(S+1)^9 := by rw [e, Nat.mul_assoc]
    _ ≤ (PrimeReserve.rpK*40002^3)*(S+1)^D := Nat.mul_le_mul_left _ h9

/-- The THR request constants against `smallSize` (PM's `seedCount_le_small`, `cut_le_small`/`cut_eq`). -/
theorem thr_consts (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : Nat) :
    r.q + ThrWidth.T a r four L target ≤ Request.smallSize a (.thr r four L target) ∧
    KeyTop.NS a r L target ≤ 8*(Request.smallSize a (.thr r four L target))^163 ∧
    KeySucc.cut a r target ≤ 40000*(Request.smallSize a (.thr r four L target))^3 :=
  ⟨PolyBound.q_input_le_smallSize a (.thr r four L target),
   NearCubicWires.PacketsMeta.Seed.seedCount_le_small a (.thr r four L target),
   (NearCubicWires.PacketsMeta.Spec.cut_eq a r four target).symm.le.trans
      (NearCubicWires.PacketsMeta.Stage.cut_le_small a r four L target)⟩

/-- The seven-argument sum against one power `P`. -/
theorem arith7 (P wT RT wS SS Rp T F c1 c2 c3 : Nat)
    (h1 : wT ≤ 31*P) (h2 : RT ≤ c1*P) (h3 : wS ≤ 9*P) (h4 : SS ≤ 19*P) (h5 : Rp ≤ c2*P) (h6 : T+1 ≤ P)
    (h7 : F ≤ c3*P) :
    256*(wT+RT+wS+SS+Rp+T+F+1) ≤ 256*(31 + c1 + 9 + 19 + c2 + 1 + c3 + 1)*P := by
  have e : 256*(31 + c1 + 9 + 19 + c2 + 1 + c3 + 1)*P =
      256*(31*P + c1*P + 9*P + 19*P + c2*P + P + c3*P + P) := by ring
  rw [e]
  omega

/-- `c5Cost`'s seven arguments against `(S+1)^D`, as plain numbers. -/
theorem c5_args_le (q T NS cut S : Nat) (hq : q + T ≤ S) (hNS : NS ≤ 8*S^163) (hcut : cut ≤ 40000*S^3) :
    ThrC5.c5Cost (12*T+19) ((BaseLayout.thrRc+1)*(q+T+1)^BaseLayout.thrRd) (natBitLength NS)
      (BaseLayout.seedScratch NS) (PrimeReserve.rpK*(T+cut+1)^3) T (ThrSelBase.bF T) ≤
      256*(31 + (BaseLayout.thrRc+1) + 9 + 19 + PrimeReserve.rpK*40002^3 + 1 + cB + 1)*(S+1)^D := by
  have hw := seed_words_le S _ hNS
  have hP1 := self_le_D S
  have hRT : (BaseLayout.thrRc+1)*(q+T+1)^BaseLayout.thrRd ≤ (BaseLayout.thrRc+1)*(S+1)^D :=
    Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by omega) _).trans (pow_D S _ (by unfold D; omega)))
  have hF : ThrSelBase.bF T ≤ cB*(S+1)^D :=
    (bF_le _).trans (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by omega) _).trans (pow_D S _ (by unfold D; omega))))
  have hRp := rp_le T cut S (by omega) hcut
  have hwT : 12*T+19 ≤ 31*(S+1)^D := by omega
  have hT1 : T+1 ≤ (S+1)^D := by omega
  exact (c5_le _ _ _ _ _ _ _).trans
    (arith7 ((S+1)^D) _ _ _ _ _ _ _ (BaseLayout.thrRc+1) (PrimeReserve.rpK*40002^3) cB hwT hRT hw.1 hw.2 hRp hT1 hF)

/-- **THR small term**: one fixed coefficient for every THR request. -/
theorem thr_small : ∃ c, ∀ (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : Nat),
    ThrC5.c5Cost (KeyTop.wT a r four L target) (KeyTop.RT a r four L target)
      (natBitLength (KeyTop.NS a r L target)) (BaseLayout.seedScratch (KeyTop.NS a r L target))
      (PrimeReserve.rpOf a (.thr r four L target)) (ThrWidth.T a r four L target)
      (ThrSelBase.bF (ThrWidth.T a r four L target)) ≤
      c*(Request.smallSize a (.thr r four L target)+1)^D :=
  ⟨_, fun a r four L target =>
    c5_args_le r.q (ThrWidth.T a r four L target) (KeyTop.NS a r L target) (KeySucc.cut a r target) _
      (thr_consts a r four L target).1 (thr_consts a r four L target).2.1 (thr_consts a r four L target).2.2⟩

/-- The four-argument sum against one power `P`. -/
theorem arith4 (P w R wS SS c1 : Nat) (h1 : w ≤ 4*P) (h2 : R ≤ c1*P) (h3 : wS ≤ 9*P) (h4 : SS ≤ 19*P)
    (h5 : 1 ≤ P) : 256*(w+R+wS+SS+1) ≤ 256*(4 + c1 + 9 + 19 + 1)*P := by
  have e : 256*(4 + c1 + 9 + 19 + 1)*P = 256*(4*P + c1*P + 9*P + 19*P + P) := by ring
  rw [e]
  omega

/-- `symCost`'s four arguments against `(S+1)^D`. -/
theorem sym_args_le (q T NS S : Nat) (hq : q + T ≤ S) (hNS : NS ≤ 8*S^163) :
    SymC5.symCost (T+3) ((BaseLayout.symRc+1)*(q+T+1)^BaseLayout.symRd) (natBitLength NS)
      (BaseLayout.seedScratch NS) ≤ 256*(4 + (BaseLayout.symRc+1) + 9 + 19 + 1)*(S+1)^D := by
  have hw := seed_words_le S _ hNS
  have hP1 := self_le_D S
  have hR : (BaseLayout.symRc+1)*(q+T+1)^BaseLayout.symRd ≤ (BaseLayout.symRc+1)*(S+1)^D :=
    Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by omega) _).trans (pow_D S _ (by unfold D; omega)))
  have hw3 : T+3 ≤ 4*(S+1)^D := by omega
  have h1 : 1 ≤ (S+1)^D := by omega
  exact (symc5_le _ _ _ _).trans (arith4 ((S+1)^D) _ _ _ _ (BaseLayout.symRc+1) hw3 hR hw.1 hw.2 h1)

/-- **SYM small term**: one fixed coefficient for every SYM request. -/
theorem sym_small : ∃ c, ∀ (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : Nat),
    SymC5.symCost (SymC5.sw a r four L target) (BaseLayout.symRes r.q (BaseLayout.symT a r four L target))
      (natBitLength (SymC5.sNS r L target)) (BaseLayout.seedScratch (SymC5.sNS r L target)) ≤
      c*(Request.smallSize a (.sym r four L target)+1)^D :=
  ⟨_, fun a r four L target =>
    sym_args_le r.q (BaseLayout.symT a r four L target) (SymC5.sNS r L target) _
      (PolyBound.q_input_le_smallSize a (.sym r four L target))
      (NearCubicWires.PacketsMeta.Seed.seedCount_le_small a (.sym r four L target))⟩

/-- The two small coefficients. -/
def cST : Nat := Classical.choose thr_small
def cSS : Nat := Classical.choose sym_small

/-- **The coefficient**: linear part `4·T_printer+100`, table `tabT+tabS`, small `(cST+cSS)·2^D`. -/
def coefficientOf (printer : WilliamsAlgorithm) : Nat :=
  (4*P1TopDownPaidPayload.tapes printer+100) + (tabT+tabS) + (cST+cSS)*2^D

theorem coefficientOf_pos (printer : WilliamsAlgorithm) : 0 < coefficientOf printer := by
  unfold coefficientOf
  omega

/-! ## 4. Combining the three classes into `rowBudget` -/

theorem combine (a : DecompositionAlgorithm) (r : Request) (C : Nat) (caps : RowCaps)
    (coeff deg Tp Y Z W cT cS : Nat) (hK : 4*Tp+100 ≤ coeff) (hcT : cT ≤ coeff) (hcS : cS ≤ coeff)
    (hY : Y ≤ Tp*(4*caps.copyCap+4)+100*(caps.headerFuel+caps.copyCap+1))
    (hZ : Z ≤ cT*(2^(Packets.residual (r.family a))*(r.q+(r.input a).length+1)^deg))
    (hW : W ≤ cS*(r.smallSize a)^deg) :
    Y+Z+W ≤ rowBudget a coeff deg r C caps := by
  unfold rowBudget
  generalize (r.smallSize a)^deg = P at hW ⊢
  generalize 2^(Packets.residual (r.family a))*(r.q+(r.input a).length+1)^deg = Q at hZ ⊢
  generalize caps.headerFuel = hF at hY ⊢
  generalize caps.copyCap = cC at hY ⊢
  have e1 : (4*Tp+100)*(hF+cC+1) = 4*(Tp*hF)+4*(Tp*cC)+4*Tp+100*hF+100*cC+100 := by ring
  have e2 : Tp*(4*cC+4) = 4*(Tp*cC)+4*Tp := by ring
  have h1 : (4*Tp+100)*(hF+cC+1) ≤ coeff*(hF+cC+1) := Nat.mul_le_mul_right _ hK
  have h2 : cT*Q ≤ coeff*Q := Nat.mul_le_mul_right _ hcT
  have h3 : cS*P ≤ coeff*P := Nat.mul_le_mul_right _ hcS
  have e3 : coeff*(P+hF+C+cC+Q+1) = coeff*P+coeff*(hF+cC+1)+coeff*C+coeff*Q := by ring
  omega

theorem small_le (printer : WilliamsAlgorithm) (c : Nat) (hc : c ≤ cST+cSS) (a : DecompositionAlgorithm)
    (r : Request) {W : Nat} (hW : W ≤ c*(r.smallSize a+1)^D) :
    W ≤ (c*2^D)*(r.smallSize a)^D ∧ c*2^D ≤ coefficientOf printer := by
  have hs := succ_pow_le (r.smallSize a) (PolyBound.smallSize_pos a r)
  refine ⟨hW.trans ?_, ?_⟩
  · calc c*(r.smallSize a+1)^D ≤ c*(2^D*(r.smallSize a)^D) := Nat.mul_le_mul_left _ hs
      _ = (c*2^D)*(r.smallSize a)^D := by ring
  · have := Nat.mul_le_mul_right (2^D) hc
    unfold coefficientOf
    omega

theorem cost_le (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm)
    (r : Request) (C : Nat) (caps : RowCaps) :
    PartsFill.rowFuelOf printer a (PrimeReserve.rpOf a) r caps ≤ rowBudget a (coefficientOf printer) D r C caps := by
  have hK : 4*P1TopDownPaidPayload.tapes printer+100 ≤ coefficientOf printer := by
    unfold coefficientOf
    omega
  cases r with
  | terminal =>
    have hf : PartsStep.fuelOf a (PrimeReserve.rpOf a) .terminal caps = 0 := rfl
    refine le_trans ?_ (combine a .terminal C caps (coefficientOf printer) D (P1TopDownPaidPayload.tapes printer)
      (P1TopDownPaidPayload.tapes printer*(4*caps.copyCap+4)+100*(caps.headerFuel+caps.copyCap+1)) 0 0 0 0
      hK (Nat.zero_le _) (Nat.zero_le _) le_rfl (Nat.zero_le _) (Nat.zero_le _))
    unfold PartsFill.rowFuelOf
    rw [hf]
    omega
  | thr r four L target =>
    have hres : Packets.residual ((Request.thr r four L target).family a) = (BaseLayout.thrLive r L)ᶜ.card :=
      PartsStep.residual_eq _ (geometryOf selector a (.thr r four L target))
    have hf : PartsStep.fuelOf a (PrimeReserve.rpOf a) (.thr r four L target) caps =
        PartsStep.thrFuel a r four L target (PrimeReserve.rpOf a (.thr r four L target)) caps.copyCap
          caps.headerFuel := rfl
    obtain ⟨hW, hcS⟩ := small_le printer cST (by omega) a (.thr r four L target)
      (Classical.choose_spec thr_small a r four L target)
    have hZ : CompleteWork.thrMaskCost a r four L target + 6*2^(BaseLayout.thrLive r L)ᶜ.card ≤
        tabT*(2^(Packets.residual ((Request.thr r four L target).family a))*
          ((Request.thr r four L target).q+((Request.thr r four L target).input a).length+1)^D) := by
      rw [hres]
      exact thr_table a r four L target
    refine le_trans ?_ (combine a (.thr r four L target) C caps (coefficientOf printer) D
      (P1TopDownPaidPayload.tapes printer)
      (P1TopDownPaidPayload.tapes printer*(4*caps.copyCap+4)+100*(caps.headerFuel+caps.copyCap+1))
      (CompleteWork.thrMaskCost a r four L target + 6*2^(BaseLayout.thrLive r L)ᶜ.card) _ tabT (cST*2^D)
      hK (by unfold coefficientOf; omega) hcS le_rfl hZ hW)
    unfold PartsFill.rowFuelOf
    rw [hf]
    unfold PartsStep.thrFuel PartsStep.c1Bound
    omega
  | sym r four L target =>
    have hres : Packets.residual ((Request.sym r four L target).family a) = (BaseLayout.symLive r L)ᶜ.card :=
      PartsStep.residual_eq _ (geometryOf selector a (.sym r four L target))
    have hf : PartsStep.fuelOf a (PrimeReserve.rpOf a) (.sym r four L target) caps =
        PartsStep.symFuel a r four L target caps.copyCap caps.headerFuel := rfl
    obtain ⟨hW, hcS⟩ := small_le printer cSS (by omega) a (.sym r four L target)
      (Classical.choose_spec sym_small a r four L target)
    have hZ : CompleteRow.symMaskCost a r four L target + 6*2^(BaseLayout.symLive r L)ᶜ.card ≤
        tabS*(2^(Packets.residual ((Request.sym r four L target).family a))*
          ((Request.sym r four L target).q+((Request.sym r four L target).input a).length+1)^D) := by
      rw [hres]
      exact sym_table a r four L target
    refine le_trans ?_ (combine a (.sym r four L target) C caps (coefficientOf printer) D
      (P1TopDownPaidPayload.tapes printer)
      (P1TopDownPaidPayload.tapes printer*(4*caps.copyCap+4)+100*(caps.headerFuel+caps.copyCap+1))
      (CompleteRow.symMaskCost a r four L target + 6*2^(BaseLayout.symLive r L)ᶜ.card) _ tabS (cSS*2^D)
      hK (by unfold coefficientOf; omega) hcS le_rfl hZ hW)
    unfold PartsFill.rowFuelOf
    rw [hf]
    unfold PartsStep.symFuel PartsStep.c1Bound
    omega

end
end RowsConstruction.CostBound
