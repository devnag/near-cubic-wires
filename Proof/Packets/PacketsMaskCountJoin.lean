import Proof.Packets.PacketsKeysStageOn
import Proof.Packets.PacketsKeyWords

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsMaskCount
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.PacketsMeta NearCubicWires.PacketsSymBits NearCubicWires.PacketsConstruction
noncomputable section

/-! ## Slot maps: `m` main tapes, the flag tape `m`, then the mode stage's, the SYM half's and the THR half's blocks -/

section Slots
variable (m fe se te : ℕ)

/-- The mode stage: main tapes 0–8 stay, its output tape 9 is the flag tape `m`, private `10 + x ↦ m + 1 + x`. -/
def fslot (hm : 9 ≤ m) (i : Fin (10 + fe)) : Fin (m + (1 + fe + se + te)) :=
  ⟨if i.val < 9 then i.val else if i.val = 9 then m else m + 1 + (i.val - 10), by
    have := i.isLt; split_ifs <;> omega⟩

/-- The SYM half: main tapes stay, private `m + x ↦ m + 1 + fe + x`. -/
def sslot (i : Fin (m + se)) : Fin (m + (1 + fe + se + te)) :=
  ⟨if i.val < m then i.val else m + 1 + fe + (i.val - m), by have := i.isLt; split_ifs <;> omega⟩

def tslot (i : Fin (m + te)) : Fin (m + (1 + fe + se + te)) :=
  ⟨if i.val < m then i.val else m + 1 + fe + se + (i.val - m), by have := i.isLt; split_ifs <;> omega⟩

/-- The flag tape. -/
def flagT : Fin (m + (1 + fe + se + te)) := ⟨m, by omega⟩

theorem fslot_val (hm : 9 ≤ m) (i : Fin (10 + fe)) :
    (fslot m fe se te hm i).val = if i.val < 9 then i.val else if i.val = 9 then m else m + 1 + (i.val - 10) := rfl

theorem sslot_val (i : Fin (m + se)) :
    (sslot m fe se te i).val = if i.val < m then i.val else m + 1 + fe + (i.val - m) := rfl

theorem tslot_val (i : Fin (m + te)) :
    (tslot m fe se te i).val = if i.val < m then i.val else m + 1 + fe + se + (i.val - m) := rfl

theorem fslot_lo (hm : 9 ≤ m) (i : Fin (10 + fe)) (h : i.val < 9) : (fslot m fe se te hm i).val = i.val := by
  rw [fslot_val, if_pos h]

theorem fslot_ge (hm : 9 ≤ m) (i : Fin (10 + fe)) (h : 9 ≤ i.val) : m ≤ (fslot m fe se te hm i).val := by
  rw [fslot_val, if_neg (by omega)]
  split_ifs <;> omega

theorem sslot_lo (i : Fin (m + se)) (h : i.val < m) : (sslot m fe se te i).val = i.val := by
  rw [sslot_val, if_pos h]

theorem sslot_ge (i : Fin (m + se)) (h : m ≤ i.val) : m ≤ (sslot m fe se te i).val := by
  rw [sslot_val, if_neg (by omega)]
  omega

theorem tslot_lo (i : Fin (m + te)) (h : i.val < m) : (tslot m fe se te i).val = i.val := by
  rw [tslot_val, if_pos h]

theorem tslot_ge (i : Fin (m + te)) (h : m ≤ i.val) : m ≤ (tslot m fe se te i).val := by
  rw [tslot_val, if_neg (by omega)]
  omega

theorem fslot_inj (hm : 9 ≤ m) : Function.Injective (fslot m fe se te hm) := by
  intro i i' h
  have hv := congrArg Fin.val h
  rw [fslot_val, fslot_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem sslot_inj : Function.Injective (sslot m fe se te) := by
  intro i i' h
  have hv := congrArg Fin.val h
  rw [sslot_val, sslot_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem tslot_inj : Function.Injective (tslot m fe se te) := by
  intro i i' h
  have hv := congrArg Fin.val h
  rw [tslot_val, tslot_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

/-- The flag tape is the mode stage's output slot. -/
theorem flagT_eq (hm : 9 ≤ m) : flagT m fe se te = fslot m fe se te hm ⟨9, by omega⟩ :=
  Fin.ext (by rw [fslot_val]; rfl)

/-- A tape of neither the first nine, the flag, nor the mode stage's block is not a mode-stage slot. -/
theorem fslot_ne (hm : 9 ≤ m) (i : Fin (m + (1 + fe + se + te))) (h1 : 9 ≤ i.val)
    (h3 : i.val < m ∨ m + 1 + fe ≤ i.val) : ∀ l, fslot m fe se te hm l ≠ i := by
  intro l hl
  have hv := congrArg Fin.val hl
  rw [fslot_val] at hv
  have := l.isLt
  split_ifs at hv <;> omega

/-- Every SYM-half slot is one of the first nine tapes or outside the mode stage's slots. -/
theorem sslot_free (hm : 9 ≤ m) (l : Fin (m + se)) :
    (sslot m fe se te l).val < 9 ∨ ∀ l', fslot m fe se te hm l' ≠ sslot m fe se te l := by
  by_cases h : l.val < 9
  · left; rw [sslot_val, if_pos (by omega)]; exact h
  · right
    apply fslot_ne m fe se te hm
    · rw [sslot_val]; split_ifs <;> omega
    · rw [sslot_val]; split_ifs <;> omega

/-- Every THR-half slot is one of the first nine tapes or outside the mode stage's slots. -/
theorem tslot_free (hm : 9 ≤ m) (l : Fin (m + te)) :
    (tslot m fe se te l).val < 9 ∨ ∀ l', fslot m fe se te hm l' ≠ tslot m fe se te l := by
  by_cases h : l.val < 9
  · left; rw [tslot_val, if_pos (by omega)]; exact h
  · right
    apply fslot_ne m fe se te hm
    · rw [tslot_val]; split_ifs <;> omega
    · rw [tslot_val]; split_ifs <;> omega

end Slots

/-! ## The join machine and its two runs -/

section Run
variable {m fe se te : ℕ} (hm : 9 ≤ m) {sf ss st : ℕ} (F : Machine (10 + fe) sf) (S : Machine (m + se) ss)
  (T : Machine (m + te) st)

/-- **The join**: the mode stage, then the SYM half on a `true` flag, else the THR half. -/
def joinM :=
  Ite (RecoveryFocus.machine (fslot m fe se te hm) F) (RecoveryFocus.machine (sslot m fe se te) S)
    (RecoveryFocus.machine (tslot m fe se te) T) (flagT m fe se te)

/-- The docked mode stage: first nine tapes kept, every non-slot tape kept, the flag reads `b`. -/
theorem flag_run {nf : ℕ} (E : Fin (m + (1 + fe + se + te)) → List Bool) {EF : Fin (10 + fe) → List Bool}
    {HF : Fin (10 + fe) → ℕ} {AF : Fin (10 + fe) → List Bool} (b : Bool)
    (hF : Step F nf (fun _ => 0) EF HF AF) (hEF : ∀ i, E (fslot m fe se te hm i) = EF i)
    (hk : ∀ i : Fin (10 + fe), i.val < 9 → AF i = EF i ∧ HF i = 0)
    (h9 : AF ⟨9, by omega⟩ = [b]) (hh9 : HF ⟨9, by omega⟩ = 0) :
    ∃ (H1 : Fin (m + (1 + fe + se + te)) → ℕ) (A1 : Fin (m + (1 + fe + se + te)) → List Bool),
      Step (RecoveryFocus.machine (fslot m fe se te hm) F) nf (fun _ => 0) E H1 A1 ∧
      (∀ i, (i.val < 9 ∨ ∀ l, fslot m fe se te hm l ≠ i) → H1 i = 0 ∧ A1 i = E i) ∧
      readTapeBit (A1 (flagT m fe se te)) (H1 (flagT m fe se te)) = b := by
  obtain ⟨H1, A1, st, hs, ho⟩ := Dock.lift hF (fslot m fe se te hm) (fslot_inj m fe se te hm) (fun _ => 0)
    (fun _ => 0) E (fun j => ⟨rfl, by rw [ZeroPadding.pad_zero, hEF]⟩)
  refine ⟨H1, A1, st, ?_, ?_⟩
  · intro i hi
    rcases hi with hi | hi
    · have e : i = fslot m fe se te hm ⟨i.val, by omega⟩ :=
        Fin.ext (fslot_lo m fe se te hm ⟨i.val, by omega⟩ (show i.val < 9 from hi)).symm
      rw [e, (hs _).1, (hs _).2, ZeroPadding.pad_zero]
      obtain ⟨k1, k2⟩ := hk ⟨i.val, by omega⟩ hi
      exact ⟨k2, by rw [k1, hEF]⟩
    · exact ho i hi
  · have e1 : A1 (flagT m fe se te) = [b] := by rw [flagT_eq m fe se te hm, (hs _).2, ZeroPadding.pad_zero, h9]
    have e2 : H1 (flagT m fe se te) = 0 := by rw [flagT_eq m fe se te hm, (hs _).1, hh9]
    rw [e1, e2]
    rfl

/-- A docked half from the bank the mode stage left: its exit on its slots. -/
theorem half_run {u sh nh : ℕ} (slot : Fin u → Fin (m + (1 + fe + se + te))) (hinj : Function.Injective slot)
    (hfree : ∀ l, (slot l).val < 9 ∨ ∀ l', fslot m fe se te hm l' ≠ slot l) (M : Machine u sh)
    (E : Fin (m + (1 + fe + se + te)) → List Bool) (H1 : Fin (m + (1 + fe + se + te)) → ℕ)
    (A1 : Fin (m + (1 + fe + se + te)) → List Bool)
    (h1 : ∀ i, (i.val < 9 ∨ ∀ l, fslot m fe se te hm l ≠ i) → H1 i = 0 ∧ A1 i = E i)
    {HH : Fin u → ℕ} {AH : Fin u → List Bool} {EA : Fin u → List Bool}
    (hH : Step M nh (fun _ => 0) EA HH AH) (hE : ∀ l, E (slot l) = EA l) :
    ∃ (H2 : Fin (m + (1 + fe + se + te)) → ℕ) (A2 : Fin (m + (1 + fe + se + te)) → List Bool),
      Step (RecoveryFocus.machine slot M) nh H1 A1 H2 A2 ∧ ∀ l, H2 (slot l) = HH l ∧ A2 (slot l) = AH l := by
  obtain ⟨H2, A2, st, hs, _⟩ := Dock.lift hH slot hinj (fun _ => 0) H1 A1 (fun l => by
    obtain ⟨e1, e2⟩ := h1 _ (hfree l)
    exact ⟨e1, by rw [e2, ZeroPadding.pad_zero, hE]⟩)
  refine ⟨H2, A2, st, fun l => ⟨(hs l).1, ?_⟩⟩
  rw [(hs l).2, ZeroPadding.pad_zero]

/-- **The SYM run of the join** (flag `true`). -/
theorem join_sym {nf ns : ℕ} (nt : ℕ) (E : Fin (m + (1 + fe + se + te)) → List Bool)
    {EF : Fin (10 + fe) → List Bool} {HF : Fin (10 + fe) → ℕ} {AF : Fin (10 + fe) → List Bool}
    (hF : Step F nf (fun _ => 0) EF HF AF) (hEF : ∀ i, E (fslot m fe se te hm i) = EF i)
    (hk : ∀ i : Fin (10 + fe), i.val < 9 → AF i = EF i ∧ HF i = 0)
    (h9 : AF ⟨9, by omega⟩ = [true]) (hh9 : HF ⟨9, by omega⟩ = 0)
    {ES : Fin (m + se) → List Bool} {HS : Fin (m + se) → ℕ} {AS : Fin (m + se) → List Bool}
    (hS : Step S ns (fun _ => 0) ES HS AS) (hES : ∀ l, E (sslot m fe se te l) = ES l) :
    ∃ (H : Fin (m + (1 + fe + se + te)) → ℕ) (A : Fin (m + (1 + fe + se + te)) → List Bool),
      Step (joinM hm F S T) (nf + ns + nt + 2) (fun _ => 0) E H A ∧
      ∀ l, H (sslot m fe se te l) = HS l ∧ A (sslot m fe se te l) = AS l := by
  obtain ⟨H1, A1, st1, h1, hf⟩ := flag_run hm F E true hF hEF hk h9 hh9
  obtain ⟨H2, A2, st2, h2⟩ := half_run hm (sslot m fe se te) (sslot_inj m fe se te) (sslot_free m fe se te hm) S E H1
    A1 h1 hS hES
  exact ⟨H2, A2, iteT _ _ (RecoveryFocus.machine (tslot m fe se te) T) _ nt st1 hf st2, h2⟩

/-- **The THR run of the join** (flag `false`). -/
theorem join_thr {nf nt : ℕ} (ns : ℕ) (E : Fin (m + (1 + fe + se + te)) → List Bool)
    {EF : Fin (10 + fe) → List Bool} {HF : Fin (10 + fe) → ℕ} {AF : Fin (10 + fe) → List Bool}
    (hF : Step F nf (fun _ => 0) EF HF AF) (hEF : ∀ i, E (fslot m fe se te hm i) = EF i)
    (hk : ∀ i : Fin (10 + fe), i.val < 9 → AF i = EF i ∧ HF i = 0)
    (h9 : AF ⟨9, by omega⟩ = [false]) (hh9 : HF ⟨9, by omega⟩ = 0)
    {ET : Fin (m + te) → List Bool} {HT : Fin (m + te) → ℕ} {AT : Fin (m + te) → List Bool}
    (hT : Step T nt (fun _ => 0) ET HT AT) (hET : ∀ l, E (tslot m fe se te l) = ET l) :
    ∃ (H : Fin (m + (1 + fe + se + te)) → ℕ) (A : Fin (m + (1 + fe + se + te)) → List Bool),
      Step (joinM hm F S T) (nf + ns + nt + 2) (fun _ => 0) E H A ∧
      ∀ l, H (tslot m fe se te l) = HT l ∧ A (tslot m fe se te l) = AT l := by
  obtain ⟨H1, A1, st1, h1, hf⟩ := flag_run hm F E false hF hEF hk h9 hh9
  obtain ⟨H2, A2, st2, h2⟩ := half_run hm (tslot m fe se te) (tslot_inj m fe se te) (tslot_free m fe se te hm) T E H1
    A1 h1 hT hET
  exact ⟨H2, A2, iteF _ (RecoveryFocus.machine (sslot m fe se te) S) _ _ ns st1 hf st2, h2⟩

end Run

/-- Three stage costs and the branch overhead, as one power of `s ≥ 1`. -/
theorem cost3_le (s c1 d1 c2 d2 c3 d3 x y z : ℕ) (hs : 1 ≤ s) (hx : x ≤ c1 * s ^ d1) (hy : y ≤ c2 * s ^ d2)
    (hz : z ≤ c3 * s ^ d3) : x + y + z + 2 ≤ (c1 + c2 + c3 + 2) * s ^ (d1 + d2 + d3) := by
  have p1 : s ^ d1 ≤ s ^ (d1 + d2 + d3) := Nat.pow_le_pow_right hs (by omega)
  have p2 : s ^ d2 ≤ s ^ (d1 + d2 + d3) := Nat.pow_le_pow_right hs (by omega)
  have p3 : s ^ d3 ≤ s ^ (d1 + d2 + d3) := Nat.pow_le_pow_right hs (by omega)
  have p0 : 1 ≤ s ^ (d1 + d2 + d3) := Nat.one_le_pow _ _ hs
  have q1 := Nat.mul_le_mul_left c1 p1
  have q2 := Nat.mul_le_mul_left c2 p2
  have q3 := Nat.mul_le_mul_left c3 p3
  calc x + y + z + 2 ≤ c1 * s ^ (d1 + d2 + d3) + c2 * s ^ (d1 + d2 + d3) + c3 * s ^ (d1 + d2 + d3) +
        2 * s ^ (d1 + d2 + d3) := by omega
    _ = (c1 + c2 + c3 + 2) * s ^ (d1 + d2 + d3) := by ring

end
end NearCubicWires.PacketsMaskCount

namespace NearCubicWires.PacketsKeys.Stage
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction NearCubicWires.PacketsConstruction.Residual
open NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.PacketsMaskCount
open PCJd4d1d9d7d1fa4313_Production
noncomputable section

variable {a : DecompositionAlgorithm}

/-! ## Adapters -/

def KeyWordOn.ofKeyWord (p : Request → Prop) {w : ∀ r : Request, rcKey a r → List Bool} (s : KeyWord a w) :
    KeyWordOn a p w where
  extra := s.extra
  states := s.states
  machine := s.machine
  cost := s.cost
  costC := s.costC
  costD := s.costD
  cost_le := s.cost_le
  run := fun r _ k hk => s.run r k hk

/-- Transport a restricted key word along an equality of values on the requests satisfying `p`. -/
def KeyWordOn.congrOn {p : Request → Prop} {v w : ∀ r : Request, rcKey a r → List Bool} (s : KeyWordOn a p v)
    (h : ∀ r, p r → ∀ k, k ∈ rcKeys a r → v r k = w r k) : KeyWordOn a p w where
  extra := s.extra
  states := s.states
  machine := s.machine
  cost := s.cost
  costC := s.costC
  costD := s.costD
  cost_le := s.cost_le
  run := fun r hp k hk => by
    obtain ⟨H, A, st, keep, h9, hh9⟩ := s.run r hp k hk
    exact ⟨H, A, st, keep, h9.trans (h r hp k hk), hh9⟩

def KeyWordOn.ofThrWord {w : PacketsCombine.Asm.TVal a} (s : PacketsCombine.Asm.ThrWord a w)
    {v : ∀ r : Request, rcKey a r → List Bool}
    (hv : ∀ (r : PacketsCombine.Asm.TReq) (four : r.circuits.length ≤ 4) (L target : ℕ)
      (k : RCFive.RowKeys.ThrKey a r L target), v (.thr r four L target) k = w r four L target k) :
    KeyWordOn a IsThr v where
  extra := s.extra
  states := s.states
  machine := s.machine
  cost := s.cost
  costC := s.costC
  costD := s.costD
  cost_le := s.cost_le
  run := by
    intro r hp k hk
    cases r with
    | terminal => exact hp.elim
    | sym _ _ _ _ => exact hp.elim
    | thr r0 four L target =>
      obtain ⟨H, A, st, keep, h9, hh9⟩ := s.run r0 four L target k hk
      exact ⟨H, A, st, keep, h9.trans (hv r0 four L target k).symm, hh9⟩

/-! ## The kind test -/

def modeK (a : DecompositionAlgorithm) : KeyWord a (fun r _ => [symBit r]) := KeyWord.ofWord (modeWordStage a)

/-! ## The joins -/

section Stage
variable {v : ∀ r : Request, rcKey a r → ℕ → List Bool} (s : KeyStageOn a IsSym v) (t : KeyStageOn a IsThr v)

/-- The key-stage bank on the mode stage's slots is the mode stage's own entry. -/
theorem stage_fEntry (r : Request) (k : rcKey a r) (j : ℕ) (i : Fin (10 + (modeK a).extra)) :
    keyEntry a r k j (11 + (1 + (modeK a).extra + s.extra + t.extra))
        (fslot 11 (modeK a).extra s.extra t.extra (by omega) i) =
      PacketsCombine.metaEntry a r (some k) (10 + (modeK a).extra) i := by
  by_cases h : i.val < 9
  · have e := fslot_lo 11 (modeK a).extra s.extra t.extra (by omega) i h
    exact ke_meta r k j _ _ e (by rw [e]; exact h)
  · have e := fslot_ge 11 (modeK a).extra s.extra t.extra (by omega) i (by omega)
    rw [ke_high r k j (fslot 11 (modeK a).extra s.extra t.extra (by omega) i) (by omega),
      me_high r (some k) i (by omega)]

/-- The key-stage bank on a half's slots is the half's own entry. -/
theorem stage_hEntry {u : ℕ} (slot : Fin (11 + u) → Fin (11 + (1 + (modeK a).extra + s.extra + t.extra)))
    (hs : ∀ l, l.val < 11 → (slot l).val = l.val) (hl : ∀ l, 11 ≤ l.val → 11 ≤ (slot l).val)
    (r : Request) (k : rcKey a r) (j : ℕ) (l : Fin (11 + u)) :
    keyEntry a r k j (11 + (1 + (modeK a).extra + s.extra + t.extra)) (slot l) = keyEntry a r k j (11 + u) l := by
  by_cases h : l.val < 11
  · exact ke_val r k j _ _ (hs l h)
  · have e := hl l (by omega)
    rw [ke_high r k j (slot l) (by omega), ke_high r k j l (by omega)]

def KeyStageOn.join : KeyStage a v where
  extra := 1 + (modeK a).extra + s.extra + t.extra
  states := _
  machine := joinM (m := 11) (by omega) (modeK a).machine s.machine t.machine
  cost := fun r => (modeK a).cost r + s.cost r + t.cost r + 2
  costC := (modeK a).costC + s.costC + t.costC + 2
  costD := (modeK a).costD + s.costD + t.costD
  cost_le := fun r => cost3_le _ _ _ _ _ _ _ _ _ _ (one_le_small a r) ((modeK a).cost_le r) (s.cost_le r)
    (t.cost_le r)
  run := by
    intro r k hk j hj
    have hF := stage_fEntry s t r k j
    obtain ⟨HF, AF, stF, keepF, outF, houtF⟩ := (modeK a).run r k hk
    cases r with
    | terminal => exact PEmpty.elim k
    | sym r0 four L target =>
      obtain ⟨HS, AS, stS, keepS, outS, hhS⟩ := s.run (.sym r0 four L target) trivial k hk j hj
      obtain ⟨H, A, st, hsl⟩ := join_sym (m := 11) (by omega) (modeK a).machine s.machine t.machine
        (t.cost (.sym r0 four L target)) (keyEntry a (.sym r0 four L target) k j _) stF hF keepF outF houtF stS
        (stage_hEntry s t (sslot 11 (modeK a).extra s.extra t.extra)
          (fun l h => sslot_lo 11 (modeK a).extra s.extra t.extra l h)
          (fun l h => sslot_ge 11 (modeK a).extra s.extra t.extra l h) _ k j)
      have e10 : (⟨10, by omega⟩ : Fin (11 + (1 + (modeK a).extra + s.extra + t.extra))) =
          sslot 11 (modeK a).extra s.extra t.extra ⟨10, by omega⟩ :=
        Fin.ext (sslot_lo 11 (modeK a).extra s.extra t.extra ⟨10, by omega⟩ (show 10 < 11 by omega)).symm
      refine ⟨H, A, st, ?_, ?_, ?_⟩
      · intro i hi
        have e : sslot 11 (modeK a).extra s.extra t.extra ⟨i.val, by omega⟩ = i :=
          Fin.ext (sslot_lo 11 (modeK a).extra s.extra t.extra ⟨i.val, by omega⟩ (show i.val < 11 by omega))
        have h1 := (hsl ⟨i.val, by omega⟩).1
        have h2 := (hsl ⟨i.val, by omega⟩).2
        rw [e] at h1 h2
        obtain ⟨k1, k2⟩ := keepS ⟨i.val, by omega⟩ hi
        exact ⟨h2.trans (k1.trans (ke_val _ k j _ i rfl)), h1.trans k2⟩
      · rw [e10, (hsl _).2]
        exact outS
      · rw [e10, (hsl _).1]
        exact hhS
    | thr r0 four L target =>
      obtain ⟨HT, AT, stT, keepT, outT, hhT⟩ := t.run (.thr r0 four L target) trivial k hk j hj
      obtain ⟨H, A, st, hsl⟩ := join_thr (m := 11) (by omega) (modeK a).machine s.machine t.machine
        (s.cost (.thr r0 four L target)) (keyEntry a (.thr r0 four L target) k j _) stF hF keepF outF houtF stT
        (stage_hEntry s t (tslot 11 (modeK a).extra s.extra t.extra)
          (fun l h => tslot_lo 11 (modeK a).extra s.extra t.extra l h)
          (fun l h => tslot_ge 11 (modeK a).extra s.extra t.extra l h) _ k j)
      have e10 : (⟨10, by omega⟩ : Fin (11 + (1 + (modeK a).extra + s.extra + t.extra))) =
          tslot 11 (modeK a).extra s.extra t.extra ⟨10, by omega⟩ :=
        Fin.ext (tslot_lo 11 (modeK a).extra s.extra t.extra ⟨10, by omega⟩ (show 10 < 11 by omega)).symm
      refine ⟨H, A, st, ?_, ?_, ?_⟩
      · intro i hi
        have e : tslot 11 (modeK a).extra s.extra t.extra ⟨i.val, by omega⟩ = i :=
          Fin.ext (tslot_lo 11 (modeK a).extra s.extra t.extra ⟨i.val, by omega⟩ (show i.val < 11 by omega))
        have h1 := (hsl ⟨i.val, by omega⟩).1
        have h2 := (hsl ⟨i.val, by omega⟩).2
        rw [e] at h1 h2
        obtain ⟨k1, k2⟩ := keepT ⟨i.val, by omega⟩ hi
        exact ⟨h2.trans (k1.trans (ke_val _ k j _ i rfl)), h1.trans k2⟩
      · rw [e10, (hsl _).2]
        exact outT
      · rw [e10, (hsl _).1]
        exact hhT

end Stage

section Word
variable {v : ∀ r : Request, rcKey a r → List Bool} (s : KeyWordOn a IsSym v) (t : KeyWordOn a IsThr v)

/-- The key-word bank on the mode stage's slots is the mode stage's own entry. -/
theorem word_fEntry (r : Request) (k : rcKey a r) (i : Fin (10 + (modeK a).extra)) :
    PacketsCombine.metaEntry a r (some k) (10 + (1 + (modeK a).extra + s.extra + t.extra))
        (fslot 10 (modeK a).extra s.extra t.extra (by omega) i) =
      PacketsCombine.metaEntry a r (some k) (10 + (modeK a).extra) i := by
  by_cases h : i.val < 9
  · exact PacketsCombine.Asm.metaEntry_val a r _ _ _ (fslot_lo 10 (modeK a).extra s.extra t.extra (by omega) i h)
  · have e := fslot_ge 10 (modeK a).extra s.extra t.extra (by omega) i (by omega)
    rw [me_high r (some k) (fslot 10 (modeK a).extra s.extra t.extra (by omega) i) (by omega),
      me_high r (some k) i (by omega)]

/-- The key-word bank on a half's slots is the half's own entry. -/
theorem word_hEntry {u : ℕ} (slot : Fin (10 + u) → Fin (10 + (1 + (modeK a).extra + s.extra + t.extra)))
    (hs : ∀ l, l.val < 10 → (slot l).val = l.val) (hl : ∀ l, 10 ≤ l.val → 10 ≤ (slot l).val)
    (r : Request) (k : rcKey a r) (l : Fin (10 + u)) :
    PacketsCombine.metaEntry a r (some k) (10 + (1 + (modeK a).extra + s.extra + t.extra)) (slot l) =
      PacketsCombine.metaEntry a r (some k) (10 + u) l := by
  by_cases h : l.val < 10
  · exact PacketsCombine.Asm.metaEntry_val a r _ _ _ (hs l h)
  · have e := hl l (by omega)
    rw [me_high r (some k) (slot l) (by omega), me_high r (some k) l (by omega)]

def KeyWordOn.join : KeyWord a v where
  extra := 1 + (modeK a).extra + s.extra + t.extra
  states := _
  machine := joinM (m := 10) (by omega) (modeK a).machine s.machine t.machine
  cost := fun r => (modeK a).cost r + s.cost r + t.cost r + 2
  costC := (modeK a).costC + s.costC + t.costC + 2
  costD := (modeK a).costD + s.costD + t.costD
  cost_le := fun r => cost3_le _ _ _ _ _ _ _ _ _ _ (one_le_small a r) ((modeK a).cost_le r) (s.cost_le r)
    (t.cost_le r)
  run := by
    intro r k hk
    have hF := word_fEntry s t r k
    obtain ⟨HF, AF, stF, keepF, outF, houtF⟩ := (modeK a).run r k hk
    cases r with
    | terminal => exact PEmpty.elim k
    | sym r0 four L target =>
      obtain ⟨HS, AS, stS, keepS, outS, hhS⟩ := s.run (.sym r0 four L target) trivial k hk
      obtain ⟨H, A, st, hsl⟩ := join_sym (m := 10) (by omega) (modeK a).machine s.machine t.machine
        (t.cost (.sym r0 four L target)) (PacketsCombine.metaEntry a (.sym r0 four L target) (some k) _) stF hF keepF
        outF houtF stS
        (word_hEntry s t (sslot 10 (modeK a).extra s.extra t.extra)
          (fun l h => sslot_lo 10 (modeK a).extra s.extra t.extra l h)
          (fun l h => sslot_ge 10 (modeK a).extra s.extra t.extra l h) _ k)
      have e9 : (⟨9, by omega⟩ : Fin (10 + (1 + (modeK a).extra + s.extra + t.extra))) =
          sslot 10 (modeK a).extra s.extra t.extra ⟨9, by omega⟩ :=
        Fin.ext (sslot_lo 10 (modeK a).extra s.extra t.extra ⟨9, by omega⟩ (show 9 < 10 by omega)).symm
      refine ⟨H, A, st, ?_, ?_, ?_⟩
      · intro i hi
        have e : sslot 10 (modeK a).extra s.extra t.extra ⟨i.val, by omega⟩ = i :=
          Fin.ext (sslot_lo 10 (modeK a).extra s.extra t.extra ⟨i.val, by omega⟩ (show i.val < 10 by omega))
        have h1 := (hsl ⟨i.val, by omega⟩).1
        have h2 := (hsl ⟨i.val, by omega⟩).2
        rw [e] at h1 h2
        obtain ⟨k1, k2⟩ := keepS ⟨i.val, by omega⟩ hi
        exact ⟨h2.trans (k1.trans (PacketsCombine.Asm.metaEntry_val a _ _ _ i rfl)), h1.trans k2⟩
      · rw [e9, (hsl _).2]
        exact outS
      · rw [e9, (hsl _).1]
        exact hhS
    | thr r0 four L target =>
      obtain ⟨HT, AT, stT, keepT, outT, hhT⟩ := t.run (.thr r0 four L target) trivial k hk
      obtain ⟨H, A, st, hsl⟩ := join_thr (m := 10) (by omega) (modeK a).machine s.machine t.machine
        (s.cost (.thr r0 four L target)) (PacketsCombine.metaEntry a (.thr r0 four L target) (some k) _) stF hF keepF
        outF houtF stT
        (word_hEntry s t (tslot 10 (modeK a).extra s.extra t.extra)
          (fun l h => tslot_lo 10 (modeK a).extra s.extra t.extra l h)
          (fun l h => tslot_ge 10 (modeK a).extra s.extra t.extra l h) _ k)
      have e9 : (⟨9, by omega⟩ : Fin (10 + (1 + (modeK a).extra + s.extra + t.extra))) =
          tslot 10 (modeK a).extra s.extra t.extra ⟨9, by omega⟩ :=
        Fin.ext (tslot_lo 10 (modeK a).extra s.extra t.extra ⟨9, by omega⟩ (show 9 < 10 by omega)).symm
      refine ⟨H, A, st, ?_, ?_, ?_⟩
      · intro i hi
        have e : tslot 10 (modeK a).extra s.extra t.extra ⟨i.val, by omega⟩ = i :=
          Fin.ext (tslot_lo 10 (modeK a).extra s.extra t.extra ⟨i.val, by omega⟩ (show i.val < 10 by omega))
        have h1 := (hsl ⟨i.val, by omega⟩).1
        have h2 := (hsl ⟨i.val, by omega⟩).2
        rw [e] at h1 h2
        obtain ⟨k1, k2⟩ := keepT ⟨i.val, by omega⟩ hi
        exact ⟨h2.trans (k1.trans (PacketsCombine.Asm.metaEntry_val a _ _ _ i rfl)), h1.trans k2⟩
      · rw [e9, (hsl _).2]
        exact outT
      · rw [e9, (hsl _).1]
        exact hhT

end Word

end
end NearCubicWires.PacketsKeys.Stage

