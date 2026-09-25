import Proof.Rows.RowsThrPrime

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.ThrKey
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierWalkBridge NearCubicWires.ExtDecompositionBatch
open NearCubicWires.PacketsGlue NearCubicWires.PacketsGlue.LexSucc NearCubicWires.RepairOrdinary.RecoveryRootRound
open RowsConstruction.BaseLayout RowsConstruction.KeyStep RowsConstruction.KeySucc RowsConstruction.KeyTop
noncomputable section

/-! ## 0. Ports of the prime stage (generic in `NI`) -/

section Ports
variable (NI : Nat)

theorem initPort_val (i : Fin NI) : (initPort NI i).val = 2 + i.val := by
  simp [initPort]

/-- The prime stage's slots: local 0 → master 240, 1 → C5 port 2 (the cutoff), 2–41 → `init` (via `ini`). -/
def psSlots (ini : Fin 40 → Fin NI) : Fin (RowsConstruction.ThrPrime.PT+1+1) → Fin (2+rowsWork NI) :=
  fun i => if i.val = 0 then masterPort NI 240 else if i.val = 1 then c5Port NI 2
    else initPort NI (ini ⟨i.val - 2, by have := i.isLt; simp only [RowsConstruction.ThrPrime.PT] at this; omega⟩)

theorem psSlots_hi (ini : Fin 40 → Fin NI) (i : Fin (RowsConstruction.ThrPrime.PT+1+1)) (hi : 2 ≤ i.val) :
    psSlots NI ini i = initPort NI (ini ⟨i.val - 2, by have := i.isLt; simp only [RowsConstruction.ThrPrime.PT] at this; omega⟩) := by
  unfold psSlots
  rw [if_neg (by omega), if_neg (by omega)]

theorem psSlots_injective (ini : Fin 40 → Fin NI) (hini : Function.Injective ini) :
    Function.Injective (psSlots NI ini) := by
  intro x y h
  have hv := congrArg Fin.val h
  have hx := x.isLt
  have hy := y.isLt
  simp only [RowsConstruction.ThrPrime.PT] at hx hy
  rcases Nat.lt_or_ge x.val 2 with hx2 | hx2 <;> rcases Nat.lt_or_ge y.val 2 with hy2 | hy2
  · apply Fin.ext
    unfold psSlots at hv
    rcases (show x.val = 0 ∨ x.val = 1 by omega) with e1 | e1 <;>
      rcases (show y.val = 0 ∨ y.val = 1 by omega) with e2 | e2 <;>
      simp only [e1, e2, if_true, if_false, one_ne_zero, masterPort_val, c5Port_val] at hv <;> omega
  · rw [psSlots_hi NI ini y hy2, initPort_val] at hv
    have := (ini ⟨y.val - 2, by omega⟩).isLt
    unfold psSlots at hv
    rcases (show x.val = 0 ∨ x.val = 1 by omega) with e1 | e1 <;>
      simp only [e1, if_true, if_false, one_ne_zero, masterPort_val, c5Port_val] at hv <;> omega
  · rw [psSlots_hi NI ini x hx2, initPort_val] at hv
    have := (ini ⟨x.val - 2, by omega⟩).isLt
    unfold psSlots at hv
    rcases (show y.val = 0 ∨ y.val = 1 by omega) with e2 | e2 <;>
      simp only [e2, if_true, if_false, one_ne_zero, masterPort_val, c5Port_val] at hv <;> omega
  · rw [psSlots_hi NI ini x hx2, psSlots_hi NI ini y hy2] at h
    have h' := hini (initPort_injective' h)
    apply Fin.ext
    have := congrArg Fin.val h'
    simp only at this
    omega
where
  initPort_injective' {i j : Fin NI} (h : initPort NI i = initPort NI j) : i = j := by
    apply Fin.ext
    have := congrArg Fin.val h
    rw [initPort_val, initPort_val] at this
    omega

/-- The `init` words the prime stage needs, at `ini m`. -/
def psInit (w R L : Nat) (m : Fin 40) : List Bool :=
  if m.val = 0 then List.replicate w true else if m.val = 1 then [true]
  else if m.val = 38 then List.replicate L false else if m.val = 39 then List.replicate R true
  else List.replicate R false

theorem initPort_ne_master (i : Fin NI) (k : Fin 254) : initPort NI i ≠ masterPort NI k := by
  intro h
  have := congrArg Fin.val h
  rw [initPort_val, masterPort_val] at this
  have := i.isLt
  omega

theorem initPort_ne_c5 (i : Fin NI) (k : Fin 16) : initPort NI i ≠ c5Port NI k := by
  intro h
  have := congrArg Fin.val h
  rw [initPort_val, c5Port_val] at this
  have := i.isLt
  omega

theorem master_ne (i k : Fin 254) (h : i ≠ k) : masterPort NI i ≠ masterPort NI k := by
  intro e
  have := congrArg Fin.val e
  rw [masterPort_val, masterPort_val] at this
  exact h (Fin.ext (by omega))

theorem cell_ne_master (c : Fin 257) (k : Fin 254) : cellPort NI c ≠ masterPort NI k := by
  intro h
  have := congrArg Fin.val h
  rw [cellPort_val, masterPort_val] at this
  have := c.isLt
  omega

theorem cell_ne_c5 (c : Fin 257) (k : Fin 16) : cellPort NI c ≠ c5Port NI k := by
  intro h
  have := congrArg Fin.val h
  rw [cellPort_val, c5Port_val] at this
  have := c.isLt
  omega

theorem cell_ne (c d : Fin 257) (h : c ≠ d) : cellPort NI c ≠ cellPort NI d := by
  intro e
  have := congrArg Fin.val e
  rw [cellPort_val, cellPort_val] at this
  exact h (Fin.ext (by omega))

/-- Compare slots: digit 149 (old `p`), bound 240 (new `p''`), flag/scratch cells 0–3, clock 254, log 255. -/
def slC : Fin 8 → Fin (2+rowsWork NI) :=
  ![masterPort NI 149, masterPort NI 240, cellPort NI 0, cellPort NI 1, cellPort NI 2, cellPort NI 3,
    cellPort NI 254, cellPort NI 255]

theorem slC_injective : Function.Injective (slC NI) := by
  intro x y h
  have hv := congrArg Fin.val h
  fin_cases x <;> fin_cases y <;> simp [slC, masterPort_val, cellPort_val] at hv ⊢

/-- Copy slots: source 240, zero word 242, destination, log cell 3. -/
def cpSlots (dst : Fin (2+rowsWork NI)) : Fin (3+1) → Fin (2+rowsWork NI) :=
  ![masterPort NI 240, masterPort NI 242, dst, cellPort NI 3]

theorem cpSlots_injective (k : Fin 254) (h240 : k ≠ 240) (h242 : k ≠ 242) :
    Function.Injective (cpSlots NI (masterPort NI k)) := by
  intro x y h
  have hv := congrArg Fin.val h
  have hk1 : k.val ≠ 240 := fun e => h240 (Fin.ext e)
  have hk2 : k.val ≠ 242 := fun e => h242 (Fin.ext e)
  fin_cases x <;> fin_cases y <;> simp [cpSlots, masterPort_val, cellPort_val] at hv ⊢ <;> omega

def cpM (dst : Fin (2+rowsWork NI)) := RecoveryFocus.machine (cpSlots NI dst)
  (MaskedReset.machine NearCubicWires.RepairOrdinary.Add.machine (fun _ => true))

def psW (ini : Fin 40 → Fin NI) := RecoveryFocus.machine (psSlots NI ini) RowsConstruction.ThrPrime.psMachine

/-- **The THR prime-level machine** (for a fixed continuation `K'`). -/
def thrKey (ini : Fin 40 → Fin NI) {sK : Nat} (K' : NearCubicWires.LocalBitMultitape.Machine (2+rowsWork NI) sK) :=
  Composition.machine (psW NI ini) (Composition.machine (cmpM (slC NI))
    (Composition.machine (cpM NI (masterPort NI 149)) (Composition.machine (cpM NI (masterPort NI 218))
      (Composition.machine (cpM NI (masterPort NI 209))
        (CloseoutRowsOriginalSwitch.machine (Composition.machine (rstM (slC NI)) K') (rstM (slC NI)) (slC NI 2))))))

theorem wdock {t s n : Nat} {p : NearCubicWires.LocalBitMultitape.Machine t s} {tin tout : Fin t → List Bool}
    (h : Step p n (fun _ => 0) tin (fun _ => 0) tout) (sl : Fin t → Fin (2+rowsWork NI)) (hi : Function.Injective sl)
    (A : Fin (2+rowsWork NI) → List Bool) (hA : ∀ j, A (sl j) = tin j) :
    Step (RecoveryFocus.machine sl p) n (fun _ => 0) A (fun _ => 0) (install sl A tout) :=
  (h.dock sl hi _ A (fun _ => rfl) hA).congr
    (NearCubicWires.ExtDecompositionBatch.dockH_existing _ _ _ (fun _ => rfl)) rfl

end Ports

/-- The copy, locally: `fb w a` from port 0 onto the (padded) framed word at port 2, zero word at port 1. -/
theorem copy_local (w a x F L : Nat) (ha : a < 2^w) (hL : 2*w+1 ≤ L) :
    Step (MaskedReset.machine NearCubicWires.RepairOrdinary.Add.machine (fun _ => true)) (2*(2*w+1)+2) (fun _ => 0)
      (Fin.addCases ![fb w a, fb w 0, ZeroPadding.pad F (fb w x)] (fun _ : Fin 1 => List.replicate L false))
      (fun _ => 0)
      (Fin.addCases ![fb w a, fb w 0, ZeroPadding.pad F (fb w a)] (fun _ : Fin 1 => List.replicate L false)) := by
  obtain ⟨r, hr, h0, h1, h2, _, _, _, hs, _⟩ :=
    NearCubicWires.RepairOrdinary.Add.add_run w a 0 (fb w x) (by simpa using ha) (by simp [KeyStep.fb])
  have st : Step NearCubicWires.RepairOrdinary.Add.machine (2*w+1) (fun _ => 0) ![fb w a, fb w 0, fb w x]
      r.final.heads ![fb w a, fb w 0, fb w a] := by
    refine ⟨r, ?_, rfl, ?_, by omega⟩
    · have e : (⟨NearCubicWires.RepairOrdinary.Add.machine.start, fun _ => 0, ![fb w a, fb w 0, fb w x]⟩ :
          Configuration 3 5) = NearCubicWires.RepairOrdinary.Add.config (NearCubicWires.RepairOrdinary.Add.scanState false)
            (fb w a) (fb w 0) 0 0 [] (fb w x) := by
        apply configuration_ext
        · rfl
        · funext i
          fin_cases i <;> rfl
        · funext i
          fin_cases i <;> rfl
      rw [e]
      exact hr
    · funext i
      fin_cases i
      · exact h0
      · exact h1
      · show r.final.tapes 2 = fb w a
        rw [h2, Nat.add_zero]
  have sp := st.pad ![0, 0, F]
  have sm := sp.mask (fun _ => true) (fun _ _ => rfl) (cap := L) hL
  have p0 : ∀ l : List Bool, ZeroPadding.pad 0 l = l := fun l => by simp [ZeroPadding.pad]
  refine (sm.congr_in (RowsConstruction.ThrPrime.addCases_zero _ (fun _ => rfl)) ?_).congr
    (RowsConstruction.ThrPrime.addCases_zero _ (fun _ => by simp)) ?_
  · funext i
    fin_cases i
    · exact p0 _
    · exact p0 _
    · rfl
    · rfl
  · funext i
    fin_cases i
    · exact p0 _
    · exact p0 _
    · rfl
    · rfl

theorem cp_at (NI : Nat) (k : Fin 254) (h240 : k ≠ 240) (h242 : k ≠ 242) (w a x F R : Nat)
    (A : Fin (2+rowsWork NI) → List Bool) (hs : A (masterPort NI 240) = fb w a) (hz : A (masterPort NI 242) = fb w 0)
    (hd : A (masterPort NI k) = ZeroPadding.pad F (fb w x)) (hl : A (cellPort NI 3) = List.replicate R false)
    (ha : a < 2^w) (hR : 2*w+1 ≤ R) :
    Step (cpM NI (masterPort NI k)) (2*(2*w+1)+2) (fun _ => 0) A (fun _ => 0)
      (Function.update A (masterPort NI k) (ZeroPadding.pad F (fb w a))) := by
  have hi := cpSlots_injective NI k h240 h242
  have d := wdock NI (copy_local w a x F R ha hR) (cpSlots NI (masterPort NI k)) hi A (fun j => by
    fin_cases j
    · exact hs
    · exact hz
    · exact hd
    · exact hl)
  rw [SymVerdict.install_update _ hi A _ 2 (fun j hj => by
    fin_cases j
    · exact hs.symm
    · exact hz.symm
    · exact absurd rfl hj
    · exact hl.symm)] at d
  exact d

section Thr
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)

/-! ## 1. The prime-index level of the key successor -/

theorem next_P (d : Fin 8 → ℕ) (hb : ¬ d 6 + 1 < primeAt (cut a r target) (d 4))
    (hs : ¬ d 5 + 1 < (thrSeeds a r L target).length)
    (hp : d 4 + 1 < Fintype.card (PrimeIndex (cut a r target))) :
    next (spec a r four L target) d =
      some (Function.update (Function.update (Function.update d 4 (d 4 + 1)) 5 0) 6 0) := by
  have hR : next [Rl a r target] d = none := by
    rw [next_cons_of_none _ _ _ rfl]
    simp only [Rl]
    rw [if_neg hb]
  have hS : next [Sl a r L target, Rl a r target] d = none := by
    rw [next_cons_of_none _ _ _ hR]
    simp only [Sl]
    rw [if_neg hs]
  have hP : next [Pl a r target, Sl a r L target, Rl a r target] d =
      some (Function.update (Function.update (Function.update d 4 (d 4 + 1)) 5 0) 6 0) := by
    rw [next_cons_of_none _ _ _ hS]
    simp only [Pl, Sl, Rl, zero]
    rw [if_pos hp]
  exact next_append_of_some (coords a r four) [Pl a r target, Sl a r L target, Rl a r target] _ _ hP

include four in
theorem dig_prime_lt (k : RCFive.RowKeys.ThrKey a r L target) :
    dig a r L target k 4 < NearCubicWires.PacketsGlue.PrimeCount.pc (cut a r target) := by
  rw [dig_prime a r four L target k, ← NearCubicWires.PacketsGlue.RequestMeta.card_primeIndex]
  exact Fin.isLt _

include four in
/-- **Case P**: residue and seed wrap, the prime index advances. -/
theorem thr_caseP (j : Nat) (hj : j+1 < (KeySucc.keys a r L target).length)
    (h1 : ¬ (KeySucc.keys a r L target)[j].residue.val + 1 < (KeySucc.keys a r L target)[j].prime.val)
    (h2 : ¬ thrSeedIdx a r L target (KeySucc.keys a r L target)[j] + 1 < (thrSeeds a r L target).length)
    (h3 : dig a r L target (KeySucc.keys a r L target)[j] 4 + 1 < NearCubicWires.PacketsGlue.PrimeCount.pc (cut a r target)) :
    dig a r L target (KeySucc.keys a r L target)[j+1] =
      Function.update (Function.update (Function.update (dig a r L target (KeySucc.keys a r L target)[j]) 4
        (dig a r L target (KeySucc.keys a r L target)[j] 4 + 1)) 5 0) 6 0 := by
  have hn := thr_next a r four L target j hj
  have e := next_P a r four L target (dig a r L target (KeySucc.keys a r L target)[j])
    (by rw [dig_res a r four, primeAt_dig a r four]; exact h1) (by rw [dig_seed a r four]; exact h2)
    (by rw [NearCubicWires.PacketsGlue.RequestMeta.card_primeIndex]; exact h3)
  rw [hn] at e
  exact Option.some.inj e

include four in
/-- On the last row the prime index cannot advance. -/
theorem last_prime (j : Nat) (hj : j < (KeySucc.keys a r L target).length)
    (hl : j+1 = (KeySucc.keys a r L target).length)
    (h1 : ¬ (KeySucc.keys a r L target)[j].residue.val + 1 < (KeySucc.keys a r L target)[j].prime.val)
    (h2 : ¬ thrSeedIdx a r L target (KeySucc.keys a r L target)[j] + 1 < (thrSeeds a r L target).length) :
    ¬ dig a r L target (KeySucc.keys a r L target)[j] 4 + 1 <
      NearCubicWires.PacketsGlue.PrimeCount.pc (cut a r target) := by
  intro h3
  have e := next_P a r four L target (dig a r L target (KeySucc.keys a r L target)[j])
    (by rw [dig_res a r four, primeAt_dig a r four]; exact h1) (by rw [dig_seed a r four]; exact h2)
    (by rw [NearCubicWires.PacketsGlue.RequestMeta.card_primeIndex]; exact h3)
  rw [last_none a r four L target j hj hl] at e
  exact Option.some_ne_none _ e.symm

include four in
/-- **Case P at key level.** -/
theorem thr_keyP (j : Nat) (hj : j+1 < (KeySucc.keys a r L target).length)
    (h1 : ¬ (KeySucc.keys a r L target)[j].residue.val + 1 < (KeySucc.keys a r L target)[j].prime.val)
    (h2 : ¬ thrSeedIdx a r L target (KeySucc.keys a r L target)[j] + 1 < (thrSeeds a r L target).length)
    (h3 : dig a r L target (KeySucc.keys a r L target)[j] 4 + 1 < NearCubicWires.PacketsGlue.PrimeCount.pc (cut a r target)) :
    (KeySucc.keys a r L target)[j+1].selection = (KeySucc.keys a r L target)[j].selection ∧
    (KeySucc.keys a r L target)[j+1].prime.val =
      primeAt (cut a r target) (dig a r L target (KeySucc.keys a r L target)[j] 4 + 1) ∧
    thrSeedIdx a r L target (KeySucc.keys a r L target)[j+1] = 0 ∧
    (KeySucc.keys a r L target)[j+1].residue.val = 0 := by
  have hd := thr_caseP a r four L target j hj h1 h2 h3
  refine ⟨sel_of_dig a r four L target _ _ (fun c => ?_), ?_, ?_, ?_⟩
  · rw [hd, Function.update_of_ne (by intro e; have := congrArg Fin.val e; simp at this; omega),
      Function.update_of_ne (by intro e; have := congrArg Fin.val e; simp at this; omega),
      Function.update_of_ne (by intro e; have := congrArg Fin.val e; simp at this; omega)]
  · rw [← primeAt_dig a r four L target (KeySucc.keys a r L target)[j+1], hd,
      Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]
  · rw [← dig_seed a r four, hd, Function.update_of_ne (by decide), Function.update_self]
  · rw [← dig_res a r four, hd, Function.update_self]

/-- The prime of row `j+1` in case P is `nextP c p`. -/
theorem nextP_caseP (u : Nat) (hu : u + 1 < NearCubicWires.PacketsGlue.PrimeCount.pc (cut a r target)) :
    RowsConstruction.ThrPrime.nextP (cut a r target) (primeAt (cut a r target) u) =
      primeAt (cut a r target) (u + 1) := by
  unfold RowsConstruction.ThrPrime.nextP
  rw [NearCubicWires.PacketsGlue.RequestMeta.nextPrime_succ _ _ hu]
  have := (NearCubicWires.PacketsGlue.RequestMeta.primeAt_spec _ _ hu).1.two_le
  omega

/-- Past the last prime, `nextP c p = 2`. -/
theorem nextP_caseSel (u : Nat) (hu : u + 1 = NearCubicWires.PacketsGlue.PrimeCount.pc (cut a r target)) :
    RowsConstruction.ThrPrime.nextP (cut a r target) (primeAt (cut a r target) u) = 2 := by
  unfold RowsConstruction.ThrPrime.nextP
  rw [NearCubicWires.PacketsGlue.RequestMeta.nextPrime_last _ _ hu]
  rfl

/-! ## 2. Masters of two keys with the same selection -/

set_option linter.unusedSectionVars false in
set_option linter.unnecessarySeqFocus false in
/-- Off the prime ports and 242, the traversal input does not depend on the prime or the residue. -/
theorem input_sameSel (sel : ThresholdRows.Selection a r) (I : Finset (Fin r.q)) (x : BitInput r.q)
    {cutoff : Nat} (prime prime' : PrimeIndex cutoff) (o : Fin prime.val) (o' : Fin prime'.val) (T w F U v : Nat)
    (i : Fin 254) (h149 : i ≠ 149) (h209 : i ≠ 209) (h218 : i ≠ 218) (h240 : i ≠ 240) (h242 : i ≠ 242) :
    PCJ45bee56da9f34d5a_ThresholdTraversal.input a r four sel I x prime o T L target w F U v i =
      PCJ45bee56da9f34d5a_ThresholdTraversal.input a r four sel I x prime' o' T L target w F U v i := by
  by_cases hk : i ∈ thrKeyPorts
  · simp only [thrKeyPorts, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h149
      | exact absurd rfl h209
      | exact absurd rfl h218
      | exact absurd rfl h240
      | exact absurd rfl h242
      | (bank_nf PCJ45bee56da9f34d5a_ThresholdTraversal.input <;>
          bank_nf PCJ45bee56da9f34d5a_ThresholdTraversal.input <;> rfl)
  · exact thr_other a r four I T L target w F U v sel sel x x prime prime' o o' i hk

theorem masters_at (R : Nat) (k : RCFive.RowKeys.ThrKey a r L target) (i : Fin 254) (hi : i ≠ 109) :
    thrMasters a r four L target R k i = keyPad thrKeySet R i
      (PCJ45bee56da9f34d5a_ThresholdTraversal.input a r four k.selection (thrLive r L) (fun _ => false)
        k.prime k.residue (RowsConstruction.ThrWidth.T a r four L target) L target (wT a r four L target)
        (Ff r.q (RowsConstruction.ThrWidth.T a r four L target)) (Uf r.q (RowsConstruction.ThrWidth.T a r four L target))
        (RowsConstruction.ThrWidth.T a r four L target) i) := by
  unfold thrMasters
  rw [if_neg hi]

/-- The width `F` of master 209's padding. -/
abbrev FT : Nat := Ff r.q (RowsConstruction.ThrWidth.T a r four L target)

/-- **Same selection**: the masters differ exactly at 242 (residue) and the four prime ports. -/
theorem masters_sameSel (R : Nat) (k k' : RCFive.RowKeys.ThrKey a r L target) (hs : k'.selection = k.selection) :
    thrMasters a r four L target R k' =
      Function.update (Function.update (Function.update (Function.update (Function.update
        (thrMasters a r four L target R k) 242 (fb (wT a r four L target) k'.residue.val))
        240 (fb (wT a r four L target) k'.prime.val)) 149 (fb (wT a r four L target) k'.prime.val))
        218 (fb (wT a r four L target) k'.prime.val))
        209 (ZeroPadding.pad (FT a r four L target) (fb (wT a r four L target) k'.prime.val)) := by
  funext i
  by_cases h209 : i = 209
  · subst h209
    rw [Function.update_self, masters_at a r four L target R k' 209 (by decide), keyPad_key _ (by decide)]
    exact thr_209 a r four _ _ L target _ _ _ _ _ _ _ _
  rw [Function.update_of_ne h209]
  by_cases h218 : i = 218
  · subst h218
    rw [Function.update_self, masters_at a r four L target R k' 218 (by decide), keyPad_key _ (by decide)]
    exact thr_prime_ports a r four _ _ L target _ _ _ _ _ _ _ _ 218 (Or.inr (Or.inl rfl))
  rw [Function.update_of_ne h218]
  by_cases h149 : i = 149
  · subst h149
    rw [Function.update_self, masters_at a r four L target R k' 149 (by decide), keyPad_key _ (by decide)]
    exact thr_prime_ports a r four _ _ L target _ _ _ _ _ _ _ _ 149 (Or.inl rfl)
  rw [Function.update_of_ne h149]
  by_cases h240 : i = 240
  · subst h240
    rw [Function.update_self]
    exact masters_240 a r four L target R k'
  rw [Function.update_of_ne h240]
  by_cases h242 : i = 242
  · subst h242
    rw [Function.update_self]
    exact masters_242 a r four L target R k'
  rw [Function.update_of_ne h242]
  by_cases h109 : i = 109
  · subst h109
    rw [thr_hm109, thr_hm109]
  rw [masters_at a r four L target R k' i h109, masters_at a r four L target R k i h109, hs]
  exact congrArg (keyPad thrKeySet R i)
    (input_sameSel a r four L target _ _ _ _ _ _ _ _ _ _ _ _ i h149 h209 h218 h240 h242)

/-! ## 3. Case P at the bank -/

theorem cut_lt : cut a r target < 2^(wT a r four L target) := by
  have h := RowsConstruction.ThrWidth.cutoff_le a r four L target
  have h2 : 2^(12*RowsConstruction.ThrWidth.T a r four L target+18) < 2^(12*RowsConstruction.ThrWidth.T a r four L target+19) :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  show cut a r target < 2^(12*RowsConstruction.ThrWidth.T a r four L target+19)
  exact lt_of_le_of_lt h h2

variable (NI : Nat) (pub : Fin 2 → List Bool) (init : Fin NI → List Bool) (rcp : Fin 64 → List Bool) (C cC hF : Nat)

/-- The both-carry bank (what `RowsKeyTop.thr_top` hands to its continuation). -/
abbrev B1 (j : Nat) : Fin (2+rowsWork NI) → List Bool :=
  Function.update (Function.update (thrBase a r four L target NI pub init rcp C cC hF j) (masterPort NI 242)
    (fb (wT a r four L target) 0)) (c5Port NI 0) (fb (natBitLength (NS a r L target)) 0)

theorem lp_ne_c5 (i : Fin 254) (k : Fin 16) :
    loopPort NI (((RowsConstruction.ThrCell.masterP i).castAdd 1).castAdd 1) ≠ c5Port NI k :=
  fun h => c5_ne_master NI k i h.symm

/-- **Case P at bank level.** -/
theorem base_succP (j : Nat) (hj : j+1 < (KeySucc.keys a r L target).length)
    (h1 : ¬ (KeySucc.keys a r L target)[j].residue.val + 1 < (KeySucc.keys a r L target)[j].prime.val)
    (h2 : ¬ thrSeedIdx a r L target (KeySucc.keys a r L target)[j] + 1 < (thrSeeds a r L target).length)
    (h3 : dig a r L target (KeySucc.keys a r L target)[j] 4 + 1 < NearCubicWires.PacketsGlue.PrimeCount.pc (cut a r target)) :
    thrBase a r four L target NI pub init rcp C cC hF (j+1) =
      Function.update (Function.update (Function.update (Function.update (B1 a r four L target NI pub init rcp C cC hF j)
        (masterPort NI 240) (fb (wT a r four L target)
          (primeAt (cut a r target) (dig a r L target (KeySucc.keys a r L target)[j] 4 + 1))))
        (masterPort NI 149) (fb (wT a r four L target)
          (primeAt (cut a r target) (dig a r L target (KeySucc.keys a r L target)[j] 4 + 1))))
        (masterPort NI 218) (fb (wT a r four L target)
          (primeAt (cut a r target) (dig a r L target (KeySucc.keys a r L target)[j] 4 + 1))))
        (masterPort NI 209) (ZeroPadding.pad (FT a r four L target) (fb (wT a r four L target)
          (primeAt (cut a r target) (dig a r L target (KeySucc.keys a r L target)[j] 4 + 1)))) := by
  obtain ⟨hs, hp, he, hr⟩ := thr_keyP a r four L target j hj h1 h2 h3
  unfold B1
  rw [base_eq a r four L target NI pub init rcp C cC hF j (by omega),
    base_eq a r four L target NI pub init rcp C cC hF (j+1) hj,
    masters_sameSel a r four L target _ _ _ hs, hr, hp, he,
    c5_seed_update (thrSeedIdx a r L target (KeySucc.keys a r L target)[j]) 0, wl_c5_update,
    loopBank_update, loopBank_update, loopBank_update, loopBank_update, loopBank_update,
    wl_loop_update, wl_loop_update, wl_loop_update, wl_loop_update, wl_loop_update,
    Function.update_comm (lp_ne_c5 NI 209 0), Function.update_comm (lp_ne_c5 NI 218 0),
    Function.update_comm (lp_ne_c5 NI 149 0), Function.update_comm (lp_ne_c5 NI 240 0)]
  rfl

/-! ## 4. The prime stage docked on the work block -/

theorem ps_entry (j : Nat) (hj : j < (KeySucc.keys a r L target).length) (ini : Fin 40 → Fin NI) (Rp Lp : Nat)
    (hinit : ∀ m, init (ini m) = psInit (wT a r four L target) Rp Lp m) :
    ∀ i, B1 a r four L target NI pub init rcp C cC hF j (psSlots NI ini i) =
      NearCubicWires.BlockPlatform.Scrub.bank (RowsConstruction.ThrPrime.psBank (wT a r four L target) (cut a r target)
        (KeySucc.keys a r L target)[j].prime.val Rp) Rp Lp i := by
  intro i
  obtain ⟨k, hk⟩ := i
  simp only [RowsConstruction.ThrPrime.PT] at hk
  rcases Nat.lt_or_ge k 2 with h2 | h2
  · rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · show B1 a r four L target NI pub init rcp C cC hF j (masterPort NI 240) = KeyStep.fb _ _
      unfold B1
      rw [Function.update_of_ne (fun h => c5_ne_master NI 0 240 h.symm),
        Function.update_of_ne (master_ne NI 240 242 (by decide)),
        base_eq a r four L target NI pub init rcp C cC hF j hj, wl_master, masters_240]
    · show B1 a r four L target NI pub init rcp C cC hF j (c5Port NI 2) = List.replicate (cut a r target) true
      unfold B1
      rw [Function.update_of_ne (fun h => by have := congrArg Fin.val h; rw [c5Port_val, c5Port_val] at this; simp at this),
        Function.update_of_ne (fun h => c5_ne_master NI 2 242 h),
        base_eq a r four L target NI pub init rcp C cC hF j hj, layout_c5]
      rfl
  · rw [psSlots_hi NI ini ⟨k, by simp only [RowsConstruction.ThrPrime.PT]; omega⟩ h2]
    unfold B1
    rw [Function.update_of_ne (initPort_ne_c5 NI _ 0), Function.update_of_ne (initPort_ne_master NI _ 242),
      base_eq a r four L target NI pub init rcp C cC hF j hj, layout_init, hinit]
    unfold psInit
    rcases Nat.lt_or_ge k 40 with h40 | h40
    · have e : NearCubicWires.BlockPlatform.Scrub.bank (RowsConstruction.ThrPrime.psBank (wT a r four L target)
          (cut a r target) (KeySucc.keys a r L target)[j].prime.val Rp) Rp Lp
          ⟨k, by simp only [RowsConstruction.ThrPrime.PT]; omega⟩ =
          RowsConstruction.ThrPrime.psBank (wT a r four L target) (cut a r target)
            (KeySucc.keys a r L target)[j].prime.val Rp ⟨k, h40⟩ :=
        NearCubicWires.BlockPlatform.Scrub.bank_inner _ _ _ ⟨k, h40⟩
      rw [e]
      simp only [RowsConstruction.ThrPrime.psBank]
      rcases (show k = 2 ∨ k = 3 ∨ 4 ≤ k by omega) with rfl | rfl | h4
      · rfl
      · rfl
      · simp only [show ¬ (k - 2 = 0) by omega, show ¬ (k - 2 = 1) by omega, show ¬ (k - 2 = 38) by omega,
          show ¬ (k - 2 = 39) by omega, show ¬ (k = 0) by omega, show ¬ (k = 1) by omega,
          show ¬ (k = 2) by omega, show ¬ (k = 3) by omega, if_false]
    · rcases (show k = 40 ∨ k = 41 by omega) with rfl | rfl
      · rfl
      · rfl

/-! ## 5. The prime-level machine on the both-carry bank -/

theorem cut_ge : 2 ≤ cut a r target := by
  have h : 563 ≤ CloseoutFinalC10ThresholdRows.primeCutoff a r target := by
    unfold CloseoutFinalC10ThresholdRows.primeCutoff
    exact canonicalPrimeCutoff_ge_563 _ _
  exact le_trans (by decide) h

theorem nextP_le (c p : Nat) (hc : 2 ≤ c) : RowsConstruction.ThrPrime.nextP c p ≤ c := by
  unfold RowsConstruction.ThrPrime.nextP NearCubicWires.PacketsGlue.RequestMeta.nextPrimeOf
  by_cases hu : NearCubicWires.PacketsGlue.PrimeCount.pc p < NearCubicWires.PacketsGlue.PrimeCount.pc c
  · have := (NearCubicWires.PacketsGlue.RequestMeta.primeAt_spec c _ hu).2.1
    omega
  · rw [NearCubicWires.PacketsGlue.RequestMeta.primeAt_off c _ (by omega)]
    omega

theorem psBank_off (w c d d' R L : Nat) (i : Fin (RowsConstruction.ThrPrime.PT+1+1)) (hi : i.val ≠ 0) :
    NearCubicWires.BlockPlatform.Scrub.bank (RowsConstruction.ThrPrime.psBank w c d' R) R L i =
      NearCubicWires.BlockPlatform.Scrub.bank (RowsConstruction.ThrPrime.psBank w c d R) R L i := by
  revert hi
  refine NearCubicWires.BlockPlatform.Scrub.cover (t := RowsConstruction.ThrPrime.PT)
    (motive := fun i => i.val ≠ 0 → NearCubicWires.BlockPlatform.Scrub.bank (RowsConstruction.ThrPrime.psBank w c d' R) R L i =
      NearCubicWires.BlockPlatform.Scrub.bank (RowsConstruction.ThrPrime.psBank w c d R) R L i)
    (fun k hk => ?_) (fun _ => by simp) (fun _ => by simp) i
  rw [NearCubicWires.BlockPlatform.Scrub.bank_inner, NearCubicWires.BlockPlatform.Scrub.bank_inner]
  have hk' : k.val ≠ 0 := by simpa [NearCubicWires.BlockPlatform.Scrub.inner_val] using hk
  simp [RowsConstruction.ThrPrime.psBank, hk']

variable (NI : Nat) (pub : Fin 2 → List Bool) (init : Fin NI → List Bool) (rcp : Fin 64 → List Bool) (C cC hF : Nat)

theorem B1_master (j : Nat) (hj : j < (KeySucc.keys a r L target).length) (k : Fin 254) (hk : k ≠ 242) :
    B1 a r four L target NI pub init rcp C cC hF j (masterPort NI k) =
      thrMasters a r four L target (RT a r four L target) (KeySucc.keys a r L target)[j] k := by
  unfold B1
  rw [Function.update_of_ne (fun h => c5_ne_master NI 0 k h.symm), Function.update_of_ne (master_ne NI k 242 hk),
    base_eq a r four L target NI pub init rcp C cC hF j hj, wl_master]

theorem B1_cell (j : Nat) (hj : j < (KeySucc.keys a r L target).length) (c : Fin 257) :
    B1 a r four L target NI pub init rcp C cC hF j (cellPort NI c) =
      PCJ45bee56da9f34d5a_VerdictFinish.bank (fun _ => List.replicate (RT a r four L target) false)
        (RT a r four L target) (List.replicate (2^(thrLive r L)ᶜ.card) false) c := by
  unfold B1
  rw [Function.update_of_ne (cell_ne_c5 NI c 0), Function.update_of_ne (cell_ne_master NI c 242),
    base_eq a r four L target NI pub init rcp C cC hF j hj, wl_cell]

/-- After the prime stage, the copies and the flag reset, with row `j+1`'s prime `v` on all four prime ports. -/
abbrev Bp (j v : Nat) : Fin (2+rowsWork NI) → List Bool :=
  Function.update (Function.update (Function.update (Function.update (B1 a r four L target NI pub init rcp C cC hF j)
    (masterPort NI 240) (fb (wT a r four L target) v)) (masterPort NI 149) (fb (wT a r four L target) v))
    (masterPort NI 218) (fb (wT a r four L target) v))
    (masterPort NI 209) (ZeroPadding.pad (FT a r four L target) (fb (wT a r four L target) v))

theorem shuffle (A : Fin (2+rowsWork NI) → List Bool) (x y z u f : List Bool) (R : Nat)
    (h0 : A (cellPort NI 0) = List.replicate R false) :
    Function.update (Function.update (Function.update (Function.update (Function.update (Function.update A
      (masterPort NI 240) x) (cellPort NI 0) f) (masterPort NI 149) y) (masterPort NI 218) z) (masterPort NI 209) u)
      (cellPort NI 0) (List.replicate R false) =
    Function.update (Function.update (Function.update (Function.update A (masterPort NI 240) x) (masterPort NI 149) y)
      (masterPort NI 218) z) (masterPort NI 209) u := by
  have hY : Function.update (Function.update A (masterPort NI 240) x) (cellPort NI 0) (List.replicate R false) =
      Function.update A (masterPort NI 240) x := by
    apply Function.update_eq_self_iff.mpr
    rw [Function.update_of_ne (cell_ne_master NI 0 240), h0]
  rw [Function.update_comm (fun h => cell_ne_master NI 0 209 h.symm),
    Function.update_comm (fun h => cell_ne_master NI 0 218 h.symm),
    Function.update_comm (fun h => cell_ne_master NI 0 149 h.symm), Function.update_idem, hY]

/-- The cost of the prime-level machine (both branches bounded by the carry branch). -/
def keyCost (w c p Rp R nK : Nat) : Nat :=
  (2*RowsConstruction.ThrPrime.psCost w c p+2+1+(2*Rp+4))+1+((4*w+4)+1+((2*(2*w+1)+2)+1+((2*(2*w+1)+2)+1+
    ((2*(2*w+1)+2)+1+(((2*R+4)+1+nK)+2)))))

theorem thr_key (j : Nat) (hj : j < (KeySucc.keys a r L target).length)
    (h1 : ¬ (KeySucc.keys a r L target)[j].residue.val + 1 < (KeySucc.keys a r L target)[j].prime.val)
    (h2 : ¬ thrSeedIdx a r L target (KeySucc.keys a r L target)[j] + 1 < (thrSeeds a r L target).length)
    (ini : Fin 40 → Fin NI) (hini : Function.Injective ini) (Rp Lp : Nat)
    (hinit : ∀ m, init (ini m) = psInit (wT a r four L target) Rp Lp m)
    (hR : RowsConstruction.ThrPrime.psCost (wT a r four L target) (cut a r target)
      (KeySucc.keys a r L target)[j].prime.val + 1 ≤ Rp) (hL : Rp + 1 ≤ Lp)
    {sK : Nat} (K' : NearCubicWires.LocalBitMultitape.Machine (2+rowsWork NI) sK) (nK : Nat)
    (hK : ¬ dig a r L target (KeySucc.keys a r L target)[j] 4 + 1 <
        NearCubicWires.PacketsGlue.PrimeCount.pc (cut a r target) →
      Step K' nK (fun _ => 0) (Bp a r four L target NI pub init rcp C cC hF j 2) (fun _ => 0)
        (thrBase a r four L target NI pub init rcp C cC hF (j+1))) :
    Step (thrKey NI ini K') (keyCost (wT a r four L target) (cut a r target) (KeySucc.keys a r L target)[j].prime.val
        Rp (RT a r four L target) nK) (fun _ => 0) (B1 a r four L target NI pub init rcp C cC hF j) (fun _ => 0)
      (thrBase a r four L target NI pub init rcp C cC hF (j+1)) := by
  set k := (KeySucc.keys a r L target)[j] with hkdef
  set B := B1 a r four L target NI pub init rcp C cC hF j with hBdef
  set w := wT a r four L target with hw
  set R := RT a r four L target with hRdef
  set c := cut a r target with hc
  have hpu : k.prime.val = primeAt c (dig a r L target k 4) := (primeAt_dig a r four L target k).symm
  have hu := dig_prime_lt a r four L target k
  have hRT : 2*w+1 ≤ R := wT_fits a r four L target k
  have hp := prime_lt a r four L target k
  have hq : RowsConstruction.ThrPrime.nextP c k.prime.val < 2^w :=
    lt_of_le_of_lt (nextP_le c _ (cut_ge a r target)) (cut_lt a r four L target)
  set p'' := RowsConstruction.ThrPrime.nextP c k.prime.val with hp''
  have p0 : ∀ l : List Bool, ZeroPadding.pad 0 l = l := fun l => by simp [ZeroPadding.pad]
  -- the prime stage
  have hsp := RowsConstruction.ThrPrime.ps_step w c k.prime.val Rp Lp hp hq hR hL
  have dps := wdock NI hsp (psSlots NI ini) (psSlots_injective NI ini hini) B
    (ps_entry a r four L target NI pub init rcp C cC hF j hj ini Rp Lp hinit)
  rw [SymVerdict.install_update _ (psSlots_injective NI ini hini) B _ ⟨0, by decide⟩ (fun i hi => by
    rw [psBank_off w c k.prime.val p'' Rp Lp i (fun e => hi (Fin.ext e))]
    exact (ps_entry a r four L target NI pub init rcp C cC hF j hj ini Rp Lp hinit i).symm)] at dps
  have e0 : psSlots NI ini ⟨0, by decide⟩ = masterPort NI 240 := rfl
  have e0' : NearCubicWires.BlockPlatform.Scrub.bank (RowsConstruction.ThrPrime.psBank w c p'' Rp) Rp Lp
      ⟨0, by decide⟩ = fb w p'' := rfl
  rw [e0, e0'] at dps
  set B2 := Function.update B (masterPort NI 240) (fb w p'') with hB2
  have b2c : ∀ c' : Fin 257, B2 (cellPort NI c') = B (cellPort NI c') := fun c' =>
    Function.update_of_ne (cell_ne_master NI c' 240) _ _
  -- the flag
  have b1_149 : B (masterPort NI 149) = fb w k.prime.val := by
    rw [hBdef, B1_master a r four L target NI pub init rcp C cC hF j hj 149 (by decide),
      masters_at a r four L target _ k 149 (by decide), keyPad_key _ (by decide)]
    exact thr_prime_ports a r four _ _ L target _ _ _ _ _ _ _ _ 149 (Or.inl rfl)
  have scmp := KeyStep.cmp_at (slC NI) (slC_injective NI) w p'' k.prime.val R (fun _ => 0) B2 (fun _ => rfl)
    (by show B2 (masterPort NI 240) = _; rw [hB2, Function.update_self])
    (by show B2 (masterPort NI 149) = _; rw [hB2, Function.update_of_ne (master_ne NI 149 240 (by decide)), b1_149])
    (by show B2 (cellPort NI 0) = _; rw [b2c, hBdef, B1_cell a r four L target NI pub init rcp C cC hF j hj]; rfl)
    (by show B2 (cellPort NI 2) = _; rw [b2c, hBdef, B1_cell a r four L target NI pub init rcp C cC hF j hj]; rfl)
    hq hp hRT
  set fl := decide (p'' ≤ k.prime.val) with hfl
  set B3 := Function.update B2 (slC NI 2) (ZeroPadding.pad R [fl]) with hB3
  have e2 : slC NI 2 = cellPort NI 0 := rfl
  have b3m : ∀ m : Fin 254, B3 (masterPort NI m) = B2 (masterPort NI m) := fun m =>
    Function.update_of_ne (by rw [e2]; exact fun h => cell_ne_master NI 0 m h.symm) _ _
  have b3c3 : B3 (cellPort NI 3) = List.replicate R false := by
    rw [hB3, e2, Function.update_of_ne (cell_ne NI 3 0 (by decide)), b2c, hBdef,
      B1_cell a r four L target NI pub init rcp C cC hF j hj]
    rfl
  have b242 : B (masterPort NI 242) = fb w 0 := by
    rw [hBdef]
    unfold B1
    rw [Function.update_of_ne (fun h => c5_ne_master NI 0 242 h.symm), Function.update_self]
  -- the three copies
  have s149 := cp_at NI 149 (by decide) (by decide) w p'' k.prime.val 0 R B3
    (by rw [b3m, hB2, Function.update_self])
    (by rw [b3m, hB2, Function.update_of_ne (master_ne NI 242 240 (by decide)), b242])
    (by rw [b3m, hB2, Function.update_of_ne (master_ne NI 149 240 (by decide)), b1_149, p0]) b3c3 hq hRT
  rw [p0] at s149
  set B4 := Function.update B3 (masterPort NI 149) (fb w p'') with hB4
  have b1_218 : B (masterPort NI 218) = fb w k.prime.val := by
    rw [hBdef, B1_master a r four L target NI pub init rcp C cC hF j hj 218 (by decide),
      masters_at a r four L target _ k 218 (by decide), keyPad_key _ (by decide)]
    exact thr_prime_ports a r four _ _ L target _ _ _ _ _ _ _ _ 218 (Or.inr (Or.inl rfl))
  have b1_209 : B (masterPort NI 209) = ZeroPadding.pad (FT a r four L target) (fb w k.prime.val) := by
    rw [hBdef, B1_master a r four L target NI pub init rcp C cC hF j hj 209 (by decide),
      masters_at a r four L target _ k 209 (by decide), keyPad_key _ (by decide)]
    exact thr_209 a r four _ _ L target _ _ _ _ _ _ _ _
  have s218 := cp_at NI 218 (by decide) (by decide) w p'' k.prime.val 0 R B4
    (by rw [hB4, Function.update_of_ne (master_ne NI 240 149 (by decide)), b3m, hB2, Function.update_self])
    (by rw [hB4, Function.update_of_ne (master_ne NI 242 149 (by decide)), b3m, hB2,
      Function.update_of_ne (master_ne NI 242 240 (by decide)), b242])
    (by rw [hB4, Function.update_of_ne (master_ne NI 218 149 (by decide)), b3m, hB2,
      Function.update_of_ne (master_ne NI 218 240 (by decide)), b1_218, p0])
    (by rw [hB4, Function.update_of_ne (cell_ne_master NI 3 149), b3c3]) hq hRT
  rw [p0] at s218
  set B5 := Function.update B4 (masterPort NI 218) (fb w p'') with hB5
  have s209 := cp_at NI 209 (by decide) (by decide) w p'' k.prime.val (FT a r four L target) R B5
    (by rw [hB5, Function.update_of_ne (master_ne NI 240 218 (by decide)), hB4,
      Function.update_of_ne (master_ne NI 240 149 (by decide)), b3m, hB2, Function.update_self])
    (by rw [hB5, Function.update_of_ne (master_ne NI 242 218 (by decide)), hB4,
      Function.update_of_ne (master_ne NI 242 149 (by decide)), b3m, hB2,
      Function.update_of_ne (master_ne NI 242 240 (by decide)), b242])
    (by rw [hB5, Function.update_of_ne (master_ne NI 209 218 (by decide)), hB4,
      Function.update_of_ne (master_ne NI 209 149 (by decide)), b3m, hB2,
      Function.update_of_ne (master_ne NI 209 240 (by decide)), b1_209])
    (by rw [hB5, Function.update_of_ne (cell_ne_master NI 3 218), hB4, Function.update_of_ne (cell_ne_master NI 3 149),
      b3c3]) hq hRT
  set B6 := Function.update B5 (masterPort NI 209) (ZeroPadding.pad (FT a r four L target) (fb w p'')) with hB6
  have b6c0 : B6 (slC NI 2) = ZeroPadding.pad R [fl] := by
    rw [e2, hB6, Function.update_of_ne (cell_ne_master NI 0 209), hB5, Function.update_of_ne (cell_ne_master NI 0 218),
      hB4, Function.update_of_ne (cell_ne_master NI 0 149), hB3, e2, Function.update_self]
  have b6c : ∀ c' : Fin 257, c' ≠ 0 → B6 (cellPort NI c') = B (cellPort NI c') := fun c' hc' => by
    rw [hB6, Function.update_of_ne (cell_ne_master NI c' 209), hB5, Function.update_of_ne (cell_ne_master NI c' 218),
      hB4, Function.update_of_ne (cell_ne_master NI c' 149), hB3, e2, Function.update_of_ne (cell_ne NI c' 0 hc'), b2c]
  have hrst := KeyStep.rst_at (slC NI) (slC_injective NI) fl R (by omega) (fun _ => 0) B6 (fun _ => rfl) b6c0
    (by show B6 (cellPort NI 254) = _; rw [b6c 254 (by decide), hBdef, B1_cell a r four L target NI pub init rcp C cC hF j hj]; rfl)
    (by show B6 (cellPort NI 255) = _; rw [b6c 255 (by decide), hBdef, B1_cell a r four L target NI pub init rcp C cC hF j hj]; rfl)
  have hb0 : B (cellPort NI 0) = List.replicate R false := by
    rw [hBdef, B1_cell a r four L target NI pub init rcp C cC hF j hj]; rfl
  have hshape : Function.update B6 (slC NI 2) (List.replicate R false) =
      Bp a r four L target NI pub init rcp C cC hF j p'' := by
    rw [e2, hB6, hB5, hB4, hB3, e2, hB2]
    exact shuffle NI B _ _ _ _ _ R hb0
  rw [hshape] at hrst
  have read1 : ∀ b : Bool, readTapeBit [b] 0 = b := fun b => by cases b <;> rfl
  have hread : readTapeBit (B6 (slC NI 2)) 0 = fl := by
    rw [b6c0, ZeroPadding.read_pad]
    exact read1 fl
  by_cases h3 : dig a r L target k 4 + 1 < NearCubicWires.PacketsGlue.PrimeCount.pc c
  · -- case P
    have hj1 : j+1 < (KeySucc.keys a r L target).length := by
      by_contra hn
      exact last_prime a r four L target j hj (by omega) h1 h2 h3
    have hv : p'' = primeAt c (dig a r L target k 4 + 1) := by
      rw [hp'', hpu]; exact nextP_caseP a r target _ h3
    have hflag : fl = false := by
      rw [hfl, decide_eq_false_iff_not, hv, hpu]
      intro hle
      have m := NearCubicWires.PacketsGlue.PrimeIdx.pc_mono hle
      rw [NearCubicWires.PacketsGlue.RequestMeta.pc_primeAt _ _ h3,
        NearCubicWires.PacketsGlue.RequestMeta.pc_primeAt _ _ hu] at m
      omega
    rw [hflag] at hread
    have sw := CloseoutRowsOriginalSwitch.false_run (Composition.machine (rstM (slC NI)) K') (rstM (slC NI)) (slC NI 2)
      hrst hread
    have tgt : Bp a r four L target NI pub init rcp C cC hF j p'' = thrBase a r four L target NI pub init rcp C cC hF (j+1) := by
      rw [base_succP a r four L target NI pub init rcp C cC hF j hj1 h1 h2 h3, ← hv]
    rw [tgt] at sw
    have sw' := sw.enlarge (show (2*R+4)+2 ≤ ((2*R+4)+1+nK)+2 by omega)
    exact dps.seq (scmp.seq (s149.seq (s218.seq (s209.seq sw'))))
  · -- case Sel
    have hv : p'' = 2 := by
      have hu' : dig a r L target k 4 < NearCubicWires.PacketsGlue.PrimeCount.pc c := hu
      rw [hp'', hpu]
      exact nextP_caseSel a r target _
        (show dig a r L target k 4 + 1 = NearCubicWires.PacketsGlue.PrimeCount.pc c by omega)
    have hflag : fl = true := by
      rw [hfl, decide_eq_true_eq, hv]
      exact (mem_primesUpTo.mp k.prime.property).1.two_le
    rw [hflag] at hread
    have hk := hK h3
    have hBp : Bp a r four L target NI pub init rcp C cC hF j p'' = Bp a r four L target NI pub init rcp C cC hF j 2 := by
      rw [hv]
    rw [hBp] at hrst
    have sw := CloseoutRowsOriginalSwitch.true_run (Composition.machine (rstM (slC NI)) K') (rstM (slC NI)) (slC NI 2)
      (hrst.seq hk) hread
    exact dps.seq (scmp.seq (s149.seq (s218.seq (s209.seq sw))))

end Thr

end
end RowsConstruction.ThrKey
