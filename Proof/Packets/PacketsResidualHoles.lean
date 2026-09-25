import Proof.Packets.PacketFamilyScrubAdapter
import Proof.Packets.PacketsCombineStages
import Proof.Packets.PacketsLowerStage

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.Residual
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction NearCubicWires.PacketsCombine
open Theorem25Completion.CycleBounds
noncomputable section

variable {a : DecompositionAlgorithm}

/-! ## Polynomial bounds in `smallSize` -/

/-- `f` is bounded by a fixed power of `smallSize`. -/
def PB (a : DecompositionAlgorithm) (f : Request → ℕ) : Prop :=
  ∃ c d : ℕ, ∀ r, f r ≤ c * (r.smallSize a) ^ d

theorem PB.of_le {f : Request → ℕ} (c d : ℕ) (h : ∀ r, f r ≤ c * (r.smallSize a) ^ d) : PB a f := ⟨c, d, h⟩

theorem PB.mono {f g : Request → ℕ} (hg : PB a g) (h : ∀ r, f r ≤ g r) : PB a f := by
  obtain ⟨c, d, hc⟩ := hg
  exact ⟨c, d, fun r => (h r).trans (hc r)⟩

theorem PB.const (k : ℕ) : PB a (fun _ => k) := ⟨k, 0, fun r => by simp⟩

theorem PB.add {f g h : Request → ℕ} (hf : PB a f) (hg : PB a g) (e : ∀ r, h r ≤ f r + g r) : PB a h := by
  obtain ⟨c1, d1, h1⟩ := hf
  obtain ⟨c2, d2, h2⟩ := hg
  refine ⟨c1 + c2, d1 + d2, fun r => ?_⟩
  have hs := RCFive.PacketBounds.positive a r
  have p1 : (r.smallSize a) ^ d1 ≤ (r.smallSize a) ^ (d1 + d2) := Nat.pow_le_pow_right hs (by omega)
  have p2 : (r.smallSize a) ^ d2 ≤ (r.smallSize a) ^ (d1 + d2) := Nat.pow_le_pow_right hs (by omega)
  have q1 := (h1 r).trans (Nat.mul_le_mul_left c1 p1)
  have q2 := (h2 r).trans (Nat.mul_le_mul_left c2 p2)
  have e2 := e r
  rw [Nat.add_mul]
  omega

theorem PB.mul {f g h : Request → ℕ} (hf : PB a f) (hg : PB a g) (e : ∀ r, h r ≤ f r * g r) : PB a h := by
  obtain ⟨c1, d1, h1⟩ := hf
  obtain ⟨c2, d2, h2⟩ := hg
  refine ⟨c1 * c2, d1 + d2, fun r => (e r).trans ?_⟩
  calc f r * g r ≤ (c1 * (r.smallSize a) ^ d1) * (c2 * (r.smallSize a) ^ d2) := Nat.mul_le_mul (h1 r) (h2 r)
    _ = c1 * c2 * (r.smallSize a) ^ (d1 + d2) := by rw [pow_add]; ring

theorem PB.pow {f h : Request → ℕ} (hf : PB a f) (k : ℕ) (e : ∀ r, h r ≤ f r ^ k) : PB a h := by
  obtain ⟨c, d, h1⟩ := hf
  refine ⟨c ^ k, d * k, fun r => (e r).trans ?_⟩
  calc f r ^ k ≤ (c * (r.smallSize a) ^ d) ^ k := Nat.pow_le_pow_left (h1 r) k
    _ = c ^ k * (r.smallSize a) ^ (d * k) := by rw [mul_pow, ← pow_mul]

/-- A polynomial bound in `smallSize` is below `c·(b+1)^D` once `smallSize ≤ b`, `cT ≤ c`, `dT ≤ D`. -/
theorem lift_base (x cT dT c D s b : ℕ) (hx : x ≤ cT * s ^ dT) (hsb : s ≤ b) (hc : cT ≤ c) (hD : dT ≤ D) :
    x ≤ c * (b + 1) ^ D := by
  have h1 : s ^ dT ≤ (b + 1) ^ dT := Nat.pow_le_pow_left (by omega) dT
  have h2 : (b + 1) ^ dT ≤ (b + 1) ^ D := Nat.pow_le_pow_right (by omega) hD
  exact hx.trans (Nat.mul_le_mul hc (h1.trans h2))

structure CoordFam (a : DecompositionAlgorithm) (K : KitShape a) where
  u : ℕ
  need : Request → ℕ
  need_pb : PB a need
  costC : ℕ
  costD : ℕ
  stage : ∀ {X : WriterShape a} (Y : RowPolyShape X), u ≤ Y.u1 → (∀ r, need r ≤ X.R r) → CoordStageK Y K
  cost_le : ∀ {X : WriterShape a} (Y : RowPolyShape X) (hu : u ≤ Y.u1) (hn : ∀ r, need r ≤ X.R r) (r : Request),
    (stage Y hu hn).cost r ≤ costC * (r.smallSize a) ^ costD

/-- **Hole F3: the relabel drivers** (`RelabelPrepStage`, `Proof/Packets/PacketsWriterPlan.lean`), uniform in the shape: its
private tapes lie in `P3` (at least `u` of them), its cost bound does not depend on the shape. -/
structure PrepFam (a : DecompositionAlgorithm) where
  u : ℕ
  need : Request → ℕ
  need_pb : PB a need
  costC : ℕ
  costD : ℕ
  stage : ∀ (X : WriterShape a), u ≤ X.w3 → (∀ r, need r ≤ X.R r) → RelabelPrepStage X
  cost_le : ∀ (X : WriterShape a) (hu : u ≤ X.w3) (hn : ∀ r, need r ≤ X.R r) (r : Request),
    (stage X hu hn).cost r ≤ costC * (r.smallSize a) ^ costD

structure CursorFam (a : DecompositionAlgorithm) where
  u : ℕ
  need : Request → ℕ
  need_pb : PB a need
  cursor : ∀ (w : ℕ) (R : Request → ℕ) (cR dR : ℕ) (hR : ∀ r, R r ≤ cR * (r.smallSize a) ^ dR),
    u ≤ w → (∀ r, need r ≤ R r) → CursorAdvance (digitLayout a w R cR dR hR)

structure SetupFam (a : DecompositionAlgorithm) where
  base : Request → ℕ
  small_le_base : ∀ r, r.smallSize a ≤ base r
  baseC : ℕ
  baseD : ℕ
  base_le : ∀ r, base r ≤ baseC * (r.smallSize a) ^ baseD
  c0 : ℕ
  D0 : ℕ
  u : ℕ → ℕ → ℕ
  need : Request → ℕ
  need_pb : PB a need
  setup : ∀ (w c D cR dR : ℕ) (hR : ∀ r, c * (base r + 1) ^ D ≤ cR * (r.smallSize a) ^ dR),
    c0 ≤ c → D0 ≤ D → u c D ≤ w → (∀ r, need r ≤ c * (base r + 1) ^ D) →
    Setup (digitLayout a w (fun r => c * (base r + 1) ^ D) cR dR hR)
      (blockScrubForm (10 + w) (digitLayout a w (fun r => c * (base r + 1) ^ D) cR dR hR).scratch)

/-- **Every open piece of the packets residual.** -/
structure Holes (a : DecompositionAlgorithm) where
  K : KitShape a
  coord : CoordFam a K
  sym : SymMeta a K
  thr : ThrMeta a K
  lower : LowerKit.LowerMeta a K
  prep : PrepFam a
  cursor : CursorFam a
  setup : SetupFam a

/-! ## The shape-independent bounds -/

theorem pop_pb (K : KitShape a) : PB a (fun r => (r.family a).occurrences.length) :=
  PB.mono (PB.of_le K.cC K.dC K.C_le) (fun r => LowerFacts.pop_le K r)

theorem reserve_pb (K : KitShape a) : PB a (fun r => commonReserve (K.C r) (K.w r)) :=
  PB.of_le _ _ (reserve_poly K)

section Bounds
variable (K : KitShape a) (m : LowerKit.LowerMeta a K)

/-- F2's fuel inputs, one dominating value (the `Y` of `LowerCost.total_le`), without the writer shape. -/
def lowerY (r : Request) : ℕ :=
  m.cost r + K.C r + 2 ^ K.w r + CloseoutRowsRawAtomProducer.budget (m.cap r) (LowerKit.pool a r).length +
    2 * PolyKit.reserve (K.C r) (K.w r)

theorem lower_cost_le (r : Request) : LowerKit.cost K m r ≤ 2 ^ 46 * (lowerY K m r + 1) ^ 26 := by
  unfold LowerKit.cost
  exact LowerCost.total_le _ _ _ _ _ _ (by unfold lowerY; generalize (2:ℕ) ^ K.w r = W; omega)
    (by unfold lowerY; generalize (2:ℕ) ^ K.w r = W; omega) (by unfold lowerY; generalize (2:ℕ) ^ K.w r = W; omega)
    (by unfold lowerY; generalize (2:ℕ) ^ K.w r = W; omega) (by unfold lowerY; generalize (2:ℕ) ^ K.w r = W; omega)

theorem atomBudget_pb : PB a (fun r => CloseoutRowsRawAtomProducer.budget (m.cap r) (LowerKit.pool a r).length) := by
  have hcap : PB a m.cap := PB.of_le m.cK m.dK m.cap_le
  have hin : PB a (fun r => 4 * m.cap r + 7) :=
    PB.add (PB.mul (PB.const 4) hcap (fun _ => le_refl _)) (PB.const 7) (fun _ => le_refl _)
  have hprod : PB a (fun r => (2 * (r.family a).occurrences.length) * (4 * m.cap r + 7)) :=
    PB.mul (PB.mul (PB.const 2) (pop_pb K) (fun _ => le_refl _)) hin (fun _ => le_refl _)
  refine PB.add (PB.const 5) hprod (fun r => ?_)
  simp only [CloseoutRowsRawAtomProducer.budget, CloseoutRowsRawAtomBatch.budget, LowerKit.pool,
    CloseoutRowsUniversal.pool_length]
  omega

theorem lowerY_pb : PB a (lowerY K m) := by
  have h1 : PB a m.cost := PB.of_le m.cM m.dM m.cost_le
  have h2 : PB a K.C := PB.of_le K.cC K.dC K.C_le
  have h3 : PB a (fun r => 2 ^ K.w r) := PB.of_le K.cW K.dW K.w_le
  have h5 : PB a (fun r => 2 * PolyKit.reserve (K.C r) (K.w r)) :=
    PB.mul (PB.const 2) (reserve_pb K) (fun _ => le_refl _)
  exact PB.add (PB.add (PB.add (PB.add h1 h2 (fun _ => le_refl _)) h3 (fun _ => le_refl _))
    (atomBudget_pb K m) (fun _ => le_refl _)) h5 (fun _ => le_refl _)

theorem lowerCost_pb : PB a (fun r => 2 ^ 46 * (lowerY K m r + 1) ^ 26) :=
  PB.mul (PB.const _) (PB.pow (PB.add (lowerY_pb K m) (PB.const 1) (fun _ => le_refl _)) 26 (fun _ => le_refl _))
    (fun _ => le_refl _)

end Bounds

theorem relabelN_pb : PB a (relabelN a) := PB.of_le 1 1 (fun r => by simpa using relabelN_le (a := a) r)
theorem relabelY_pb : PB a (relabelY a) := PB.of_le 1 1 (fun r => by simpa using relabelY_le (a := a) r)
theorem streamCap_pb : PB a (streamCap a) := PB.of_le 4 3 (streamCap_le a)

/-- The relabel tapes' room (`RelabelFit.room`). -/
def relabelRoom (a : DecompositionAlgorithm) (r : Request) : ℕ :=
  P1Closure.RawRelabelUniform.logCapacity (relabelN a r) (relabelY a r) (streamCap a r) +
    (relabelN a r * relabelY a r + 3) + (relabelY a r + 1) + 1

theorem relabelRoom_pb : PB a (relabelRoom a) := by
  have hNY : PB a (fun r => relabelN a r * relabelY a r) := PB.mul relabelN_pb relabelY_pb (fun _ => le_refl _)
  have hA : PB a (fun r => (2 * (relabelN a r * relabelY a r + 1) + 4) * streamCap a r) :=
    PB.mul (PB.add (PB.mul (PB.const 2) (PB.add hNY (PB.const 1) (fun _ => le_refl _)) (fun _ => le_refl _))
      (PB.const 4) (fun _ => le_refl _)) streamCap_pb (fun _ => le_refl _)
  have hB : PB a (fun r => relabelN a r * (2 * relabelY a r + 3)) :=
    PB.mul relabelN_pb (PB.add (PB.mul (PB.const 2) relabelY_pb (fun _ => le_refl _)) (PB.const 3)
      (fun _ => le_refl _)) (fun _ => le_refl _)
  refine PB.add (PB.add (PB.add hA hB (fun _ => le_refl _)) hNY (fun _ => le_refl _)) (PB.add relabelY_pb (PB.const 10)
    (fun _ => le_refl _)) (fun r => ?_)
  simp only [relabelRoom, P1Closure.RawRelabelUniform.logCapacity, P1Closure.RawRelabelOffset.rawBudget]
  omega

/-- The relabel loop's fuel (`WriterStagesK.cost`'s last summand). -/
theorem relabelBudget_pb :
    PB a (fun r => P1Closure.RawRelabelFamily.budget (relabelN a r) (relabelY a r) (streamCap a r)) := by
  have hM : PB a (fun r => relabelN a r + relabelY a r + streamCap a r + 1) :=
    PB.add (PB.add (PB.add relabelN_pb relabelY_pb (fun _ => le_refl _)) streamCap_pb (fun _ => le_refl _))
      (PB.const 1) (fun _ => le_refl _)
  exact PB.mul (PB.const 128) (PB.mul (PB.mul (PB.mul hM hM (fun _ => le_refl _)) hM (fun _ => le_refl _)) hM
    (fun _ => le_refl _)) (fun r => relabel_budget_le _ _ _)

section Assembly
variable (h : Holes a)

/-- The writer's fuel, bounded without the writer shape. -/
def writerBound (r : Request) : ℕ :=
  h.coord.costC * (r.smallSize a) ^ h.coord.costD + 1 + (symStageCost h.K h.sym r + thrStageCost h.K h.thr r + 2) +
    1 + 2 ^ 46 * (lowerY h.K h.lower r + 1) ^ 26 + 1 + h.prep.costC * (r.smallSize a) ^ h.prep.costD + 1 +
    P1Closure.RawRelabelFamily.budget (relabelN a r) (relabelY a r) (streamCap a r)

/-- Every room the width must cover. -/
def rooms (r : Request) : ℕ :=
  h.coord.need r + h.prep.need r + h.cursor.need r + h.setup.need r + (h.lower.cap r + 1) +
    CloseoutRowsRawAtomProducer.budget (h.lower.cap r) (LowerKit.pool a r).length +
    2 * PolyKit.reserve (h.K.C r) (h.K.w r) + ((r.family a).occurrences.length + 2) +
    PacketBank.storeBudget (commonReserve (h.K.C r) (h.K.w r)) + relabelRoom a r

/-- What the scrub width must dominate. -/
def total (r : Request) : ℕ := writerBound h r + 1 + rooms h r

theorem writerBound_pb : PB a (writerBound h) := by
  have hc : PB a (fun r => h.coord.costC * (r.smallSize a) ^ h.coord.costD) := PB.of_le _ _ (fun _ => le_refl _)
  have hs : PB a (symStageCost h.K h.sym) := PB.of_le _ _ (sym_cost_le h.K h.sym)
  have ht : PB a (thrStageCost h.K h.thr) := PB.of_le _ _ (thr_cost_le h.K h.thr)
  have hp : PB a (fun r => h.prep.costC * (r.smallSize a) ^ h.prep.costD) := PB.of_le _ _ (fun _ => le_refl _)
  have h1 := PB.add hc (PB.add (PB.add hs ht (fun _ => le_refl _)) (PB.const 2) (fun _ => le_refl _))
    (fun _ => le_refl _)
  have h2 := PB.add h1 (lowerCost_pb h.K h.lower) (fun _ => le_refl _)
  have h3 := PB.add h2 hp (fun _ => le_refl _)
  refine PB.add (PB.add h3 relabelBudget_pb (fun _ => le_refl _)) (PB.const 4) (fun r => ?_)
  unfold writerBound
  omega

theorem rooms_pb : PB a (rooms h) := by
  have h1 := PB.add (PB.add (PB.add h.coord.need_pb h.prep.need_pb (fun _ => le_refl _)) h.cursor.need_pb
    (fun _ => le_refl _)) h.setup.need_pb (fun _ => le_refl _)
  have hcap : PB a (fun r => h.lower.cap r + 1) :=
    PB.add (PB.of_le h.lower.cK h.lower.dK h.lower.cap_le) (PB.const 1) (fun _ => le_refl _)
  have hres : PB a (fun r => 2 * PolyKit.reserve (h.K.C r) (h.K.w r)) :=
    PB.mul (PB.const 2) (reserve_pb h.K) (fun _ => le_refl _)
  have hpop : PB a (fun r => (r.family a).occurrences.length + 2) :=
    PB.add (pop_pb h.K) (PB.const 2) (fun _ => le_refl _)
  have hstore : PB a (fun r => PacketBank.storeBudget (commonReserve (h.K.C r) (h.K.w r))) :=
    PB.add (PB.mul (PB.const 8) (reserve_pb h.K) (fun _ => le_refl _)) (PB.const 15) (fun _ => le_refl _)
  have h2 := PB.add (PB.add (PB.add (PB.add h1 hcap (fun _ => le_refl _)) (atomBudget_pb h.K h.lower)
    (fun _ => le_refl _)) hres (fun _ => le_refl _)) hpop (fun _ => le_refl _)
  exact PB.add (PB.add h2 hstore (fun _ => le_refl _)) relabelRoom_pb (fun _ => le_refl _)

theorem total_pb : PB a (total h) :=
  PB.add (PB.add (writerBound_pb h) (PB.const 1) (fun _ => le_refl _)) (rooms_pb h) (fun _ => le_refl _)

/-! ## The shape, from the bound `total ≤ cT·smallSize^dT` -/

variable (cT dT : ℕ)

/-- The scrub width's constants. -/
def cW : ℕ := cT + h.setup.c0
def dW : ℕ := dT + h.setup.D0

/-- The scrub width `R r = c·(base r + 1)^D`. -/
def width (r : Request) : ℕ := cW h cT * (h.setup.base r + 1) ^ dW h dT

theorem width_le (r : Request) :
    width h cT dT r ≤ cW h cT * (h.setup.baseC + 1) ^ dW h dT * (r.smallSize a) ^ (h.setup.baseD * dW h dT) := by
  have hs := RCFive.PacketBounds.positive a r
  have hp : 1 ≤ (r.smallSize a) ^ h.setup.baseD := Nat.one_le_pow _ _ hs
  have hb : h.setup.base r + 1 ≤ (h.setup.baseC + 1) * (r.smallSize a) ^ h.setup.baseD := by
    have := h.setup.base_le r
    nlinarith
  have hp2 := Nat.pow_le_pow_left hb (dW h dT)
  unfold width
  rw [Nat.mul_pow, ← pow_mul] at hp2
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ hp2

/-- The writer's bank shape. -/
def shape : WriterShape a where
  w1 := 2 + h.coord.u + (106 + h.sym.extra) + (107 + h.thr.extra)
  w2 := 299 + (h.lower.tapes - 7)
  w3 := h.prep.u + h.cursor.u + h.setup.u (cW h cT) (dW h dT)
  R := fun r => cW h cT * (h.setup.base r + 1) ^ dW h dT
  cR := cW h cT * (h.setup.baseC + 1) ^ dW h dT
  dR := h.setup.baseD * dW h dT
  hR := width_le h cT dT

/-- F1's split shape. -/
def split : RowPolyShape (shape h cT dT) where
  u1 := h.coord.u
  u2 := 106 + h.sym.extra
  u3 := 107 + h.thr.extra
  hw1 := rfl

variable (hT : ∀ r, total h r ≤ cT * (r.smallSize a) ^ dT)
include hT

theorem total_le (r : Request) : total h r ≤ (shape h cT dT).R r :=
  lift_base _ cT dT _ _ _ _ (hT r) (h.setup.small_le_base r) (by unfold cW; omega) (by unfold dW; omega)

theorem room_le {f : Request → ℕ} (hf : ∀ r, f r ≤ rooms h r) (r : Request) : f r ≤ (shape h cT dT).R r := by
  have := total_le h cT dT hT r
  unfold total at this
  have := hf r
  omega

theorem symRoom : SymRoom (shape h cT dT) h.K := fun r =>
  room_le h cT dT hT (f := fun r => PacketBank.storeBudget (commonReserve (h.K.C r) (h.K.w r)))
    (fun r => by unfold rooms; omega) r

/-- F2's room. -/
theorem lowerFit : LowerKit.LowerFit (shape h cT dT) h.K h.lower where
  width := by simp only [shape]; omega
  cap := room_le h cT dT hT (f := fun r => h.lower.cap r + 1) (fun r => by unfold rooms; omega)
  log := room_le h cT dT hT (f := fun r => CloseoutRowsRawAtomProducer.budget (h.lower.cap r) (LowerKit.pool a r).length)
    (fun r => by unfold rooms; omega)
  reserve := room_le h cT dT hT (f := fun r => 2 * PolyKit.reserve (h.K.C r) (h.K.w r)) (fun r => by unfold rooms; omega)
  pop := room_le h cT dT hT (f := fun r => (r.family a).occurrences.length + 2) (fun r => by unfold rooms; omega)

/-- F1 = (i) ; switch ; (ii) | (iii). -/
def rowPolySplit : RowPolySplitK (split h cT dT) h.K where
  coord := h.coord.stage (split h cT dT) le_rfl (room_le h cT dT hT (f := h.coord.need) (fun r => by unfold rooms; omega))
  sym := symCombine (split h cT dT) h.K h.sym le_rfl (symRoom h cT dT hT)
  thr := thrCombine (split h cT dT) h.K h.thr le_rfl (symRoom h cT dT hT)

/-- The four writer stages. -/
def stages : WriterStagesK (shape h cT dT) h.K where
  rowPoly := RowPolySplitK.stage (rowPolySplit h cT dT hT)
  lower := LowerKit.stage (shape h cT dT) h.K h.lower (lowerFit h cT dT hT)
  prep := h.prep.stage (shape h cT dT) (by simp only [shape]; omega)
    (room_le h cT dT hT (f := h.prep.need) (fun r => by unfold rooms; omega))
  fit := relabelFit (shape h cT dT) (loweredDegree_holds a)
    (room_le h cT dT hT (f := relabelRoom a) (fun r => by unfold rooms; omega))

theorem stages_cost_le (r : Request) : (stages h cT dT hT).cost r ≤ writerBound h r := by
  have hc := h.coord.cost_le (split h cT dT) le_rfl
    (room_le h cT dT hT (f := h.coord.need) (fun r => by unfold rooms; omega)) r
  have hp := h.prep.cost_le (shape h cT dT) (by simp only [shape]; omega)
    (room_le h cT dT hT (f := h.prep.need) (fun r => by unfold rooms; omega)) r
  have hl := lower_cost_le h.K h.lower r
  change (rowPolySplit h cT dT hT).cost r + 1 + LowerKit.cost h.K h.lower r + 1 +
      (h.prep.stage (shape h cT dT) _ _).cost r + 1 +
      P1Closure.RawRelabelFamily.budget (relabelN a r) (relabelY a r) (streamCap a r) ≤ writerBound h r
  change (h.coord.stage (split h cT dT) le_rfl _).cost r + 1 +
      (symStageCost h.K h.sym r + thrStageCost h.K h.thr r + 2) + 1 + LowerKit.cost h.K h.lower r + 1 +
      (h.prep.stage (shape h cT dT) _ _).cost r + 1 +
      P1Closure.RawRelabelFamily.budget (relabelN a r) (relabelY a r) (streamCap a r) ≤ writerBound h r
  unfold writerBound
  omega

/-- **The residual, from the holes and the width's constants.** -/
def residualAt (selector : CyclicChoice.Laws) : SuppliedResidual selector a where
  layout := (shape h cT dT).layout
  writer := (stages h cT dT hT).rowWriter selector
  cursor := h.cursor.cursor (shape h cT dT).w (shape h cT dT).R (shape h cT dT).cR (shape h cT dT).dR
    (shape h cT dT).hR (by simp only [shape, WriterShape.w]; omega)
    (room_le h cT dT hT (f := h.cursor.need) (fun r => by unfold rooms; omega))
  setup := h.setup.setup (shape h cT dT).w (cW h cT) (dW h dT) (shape h cT dT).cR (shape h cT dT).dR
    (shape h cT dT).hR (by unfold cW; omega) (by unfold dW; omega) (by simp only [shape, WriterShape.w]; omega)
    (room_le h cT dT hT (f := h.setup.need) (fun r => by unfold rooms; omega))
  widthFits := fun r => by
    have h1 := stages_cost_le h cT dT hT r
    have h2 := total_le h cT dT hT r
    unfold total at h2
    change (stages h cT dT hT).cost r + 1 ≤ (shape h cT dT).R r
    omega

end Assembly

/-- **The packets residual from its holes.** -/
theorem residual (selector : CyclicChoice.Laws) (h : Holes a) : Nonempty (SuppliedResidual selector a) := by
  obtain ⟨cT, dT, hT⟩ := total_pb h
  exact ⟨residualAt h cT dT hT selector⟩

/-- **`packetsResidual`**, with every open piece a typed hole. -/
theorem packetsResidual (selector : CyclicChoice.Laws) (h : ∀ a, Holes a) :
    ∀ a, Nonempty (SuppliedResidual selector a) :=
  fun a => residual selector (h a)

theorem packetConstruction_of_holes (selector : CyclicChoice.Laws) (h : ∀ a, Holes a) :
    PacketConstruction selector :=
  packetConstruction_of_residual selector (packetsResidual selector h)

end
end NearCubicWires.PacketsConstruction.Residual
