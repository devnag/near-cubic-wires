import Proof.Packets.PacketsCursorKeyVec

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.Cursor
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime NearCubicWires.SupplierEstimator
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production NearCubicWires.PacketFamilyParent
open NearCubicWires.PacketsConstruction NearCubicWires.PacketsConstruction.Residual
open NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.PacketsMeta.Keys
open NearCubicWires.PacketsGlue.CursorKit NearCubicWires.PacketsGlue.CursorChain
noncomputable section

variable {a : DecompositionAlgorithm}

/-- Transport a key vector along a pointwise equality of its words. -/
def KeyVec.congr {n : ℕ} {outs outs' : ℕ → ∀ r : Request, rcKey a r → List Bool} (V : KeyVec a n outs)
    (h : ∀ j, j < n → ∀ r k, outs j r k = outs' j r k) : KeyVec a n outs' where
  extra := V.extra
  states := V.states
  machine := V.machine
  cost := V.cost
  costC := V.costC
  costD := V.costD
  cost_le := V.cost_le
  run := fun r k hk => (V.run r k hk).elim fun H e => e.elim fun A f =>
    ⟨H, A, f.1, f.2.1, fun j hj => by rw [← h j hj r k]; exact f.2.2 j hj⟩

/-- The nine words: the carry flags of fields 0–6, the kind, the driver source. -/
def cursorOuts (a : DecompositionAlgorithm) (base : Request → ℕ) (j : ℕ) (r : Request) (k : rcKey a r) : List Bool :=
  if h : j < 7 then
    List.replicate (carryV (lvlBound a r (keyDigits a r (some k)) ⟨j, by omega⟩) (keyDigits a r (some k) ⟨j, by omega⟩))
      true
  else if j = 7 then List.replicate (thrFlag r) true else List.replicate (base r + 1) true

theorem primeAt_le (c u : ℕ) : PacketsGlue.primeAt c u ≤ c + 1 := by
  unfold PacketsGlue.primeAt
  split_ifs with h
  · have := (mem_primesUpTo.mp ((primeIndexFinEquiv c).symm ⟨u, h⟩).property).2
    omega
  · omega

section Words
variable (a)

/-- The carry flag of coordinate field `i < 4`. -/
def flagC (cb : ∀ i : Fin 4, UnaryStage a (circBound a i.val)) (i : Fin 4) :=
  flagKW (v1 := fun r _ => circBound a i.val r) (KeyWord.ofWord (cb i).toWord) ⟨i.val, by omega⟩ (circBound a i.val)
    (fun _ _ _ => le_refl _) (KB.ofStage (cb i))

/-- The carry flag of field 4 (the prime index; bound `π(cutoff)`, at least 1). -/
def flag4 :=
  flagKW (v1 := fun r _ => primeCountOf a r) (KeyWord.ofWord (primeCountStage a (PacketsMeta.cutoffStage a)).toWord) 4
    (primeCountOf a) (fun _ _ _ => le_refl _) (KB.ofStage (primeCountStage a (PacketsMeta.cutoffStage a)))

/-- The carry flag of field 5 (the walk seed; bound `seedCount`). -/
def flag5 :=
  flagKW (v1 := fun r _ => seedCount a r) (KeyWord.ofWord (PacketsMeta.Seed.seedCountStage a).toWord) 5
    (seedCount a) (fun _ _ _ => le_refl _) (KB.ofStage (PacketsMeta.Seed.seedCountStage a))

def flag6 :=
  flagKW (v1 := fun r k => PacketsGlue.primeAt (cutoffOf a r) (keyDigits a r (some k) 4)) (primeW a) 6
    (fun r => cutoffOf a r + 1) (fun _ _ _ => primeAt_le _ _)
    (KB.add (KB.ofStage (PacketsMeta.cutoffStage a)) (KB.const 1) (fun _ => le_refl _))

/-- The kind bit `1^(thrFlag r)`. -/
def kindKW := KeyWord.ofWord (thrFlagStage a).toWord

/-- The driver source `1^(base r + 1)`. -/
def srcKW {base : Request → ℕ} (baseS : UnaryStage a base) :=
  KeyWord.ofWord (baseS.thenMapP (plusMap 1) 6 1 (plus_cost 1)).toWord

/-- The nine words, snoc by snoc. -/
def flagVec0 (cb : ∀ i : Fin 4, UnaryStage a (circBound a i.val)) {base : Request → ℕ} (baseS : UnaryStage a base) :=
  (((((((((KeyVec.nil a (cursorOuts a base)).snoc (flagC a cb 0)).snoc (flagC a cb 1)).snoc (flagC a cb 2)).snoc
    (flagC a cb 3)).snoc (flag4 a)).snoc (flag5 a)).snoc (flag6 a)).snoc (kindKW a)).snoc (srcKW a baseS)

end Words

theorem lvl_lt4 (r : Request) (d : PacketsGlue.Digits) (f : Fin 8) (hf : f.val < 4) :
    lvlBound a r d f = circBound a f.val r := by
  unfold lvlBound; rw [if_pos hf]

theorem lvl_4 (r : Request) (d : PacketsGlue.Digits) : lvlBound a r d 4 = primeCountOf a r := by
  unfold lvlBound; rw [if_neg (by decide), if_pos (by decide)]

theorem lvl_5 (r : Request) (d : PacketsGlue.Digits) : lvlBound a r d 5 = seedCount a r := by
  unfold lvlBound; rw [if_neg (by decide), if_neg (by decide), if_pos (by decide)]

theorem lvl_6 (r : Request) (d : PacketsGlue.Digits) : lvlBound a r d 6 = PacketsGlue.primeAt (cutoffOf a r) (d 4) := by
  unfold lvlBound; rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]

/-- **The cursor's nine key-level words, one fixed machine.** -/
def flagVec (cb : ∀ i : Fin 4, UnaryStage a (circBound a i.val)) {base : Request → ℕ} (baseS : UnaryStage a base) :
    KeyVec a 9 (cursorOuts a base) :=
  (flagVec0 a cb baseS).congr (by
    intro j hj r k
    interval_cases j
    · simp only [cursorOuts, if_neg (show ¬ ((0 : ℕ) = 8) by decide), if_neg (show ¬ ((0 : ℕ) = 7) by decide),
        if_neg (show ¬ ((0 : ℕ) = 6) by decide), if_neg (show ¬ ((0 : ℕ) = 5) by decide),
        if_neg (show ¬ ((0 : ℕ) = 4) by decide), if_neg (show ¬ ((0 : ℕ) = 3) by decide),
        if_neg (show ¬ ((0 : ℕ) = 2) by decide), if_neg (show ¬ ((0 : ℕ) = 1) by decide),
        dif_pos (show (0 : ℕ) < 7 by decide)]
      rw [lvl_lt4 r _ _ (by decide)]
      rfl
    · simp only [cursorOuts, if_neg (show ¬ ((1 : ℕ) = 8) by decide), if_neg (show ¬ ((1 : ℕ) = 7) by decide),
        if_neg (show ¬ ((1 : ℕ) = 6) by decide), if_neg (show ¬ ((1 : ℕ) = 5) by decide),
        if_neg (show ¬ ((1 : ℕ) = 4) by decide), if_neg (show ¬ ((1 : ℕ) = 3) by decide),
        if_neg (show ¬ ((1 : ℕ) = 2) by decide), dif_pos (show (1 : ℕ) < 7 by decide)]
      rw [lvl_lt4 r _ _ (by decide)]
      rfl
    · simp only [cursorOuts, if_neg (show ¬ ((2 : ℕ) = 8) by decide), if_neg (show ¬ ((2 : ℕ) = 7) by decide),
        if_neg (show ¬ ((2 : ℕ) = 6) by decide), if_neg (show ¬ ((2 : ℕ) = 5) by decide),
        if_neg (show ¬ ((2 : ℕ) = 4) by decide), if_neg (show ¬ ((2 : ℕ) = 3) by decide),
        dif_pos (show (2 : ℕ) < 7 by decide)]
      rw [lvl_lt4 r _ _ (by decide)]
      rfl
    · simp only [cursorOuts, if_neg (show ¬ ((3 : ℕ) = 8) by decide), if_neg (show ¬ ((3 : ℕ) = 7) by decide),
        if_neg (show ¬ ((3 : ℕ) = 6) by decide), if_neg (show ¬ ((3 : ℕ) = 5) by decide),
        if_neg (show ¬ ((3 : ℕ) = 4) by decide), dif_pos (show (3 : ℕ) < 7 by decide)]
      rw [lvl_lt4 r _ _ (by decide)]
      rfl
    · simp only [cursorOuts, if_neg (show ¬ ((4 : ℕ) = 8) by decide), if_neg (show ¬ ((4 : ℕ) = 7) by decide),
        if_neg (show ¬ ((4 : ℕ) = 6) by decide), if_neg (show ¬ ((4 : ℕ) = 5) by decide),
        dif_pos (show (4 : ℕ) < 7 by decide)]
      rw [show (⟨4, by decide⟩ : Fin 8) = 4 from rfl, lvl_4]
      rfl
    · simp only [cursorOuts, if_neg (show ¬ ((5 : ℕ) = 8) by decide), if_neg (show ¬ ((5 : ℕ) = 7) by decide),
        if_neg (show ¬ ((5 : ℕ) = 6) by decide), dif_pos (show (5 : ℕ) < 7 by decide)]
      rw [show (⟨5, by decide⟩ : Fin 8) = 5 from rfl, lvl_5]
      rfl
    · simp only [cursorOuts, if_neg (show ¬ ((6 : ℕ) = 8) by decide), if_neg (show ¬ ((6 : ℕ) = 7) by decide),
        dif_pos (show (6 : ℕ) < 7 by decide)]
      rw [show (⟨6, by decide⟩ : Fin 8) = 6 from rfl, lvl_6]
      rfl
    · simp only [cursorOuts, if_neg (show ¬ ((7 : ℕ) = 8) by decide),
        dif_neg (show ¬ ((7 : ℕ) < 7) by decide)]
      rfl
    · simp only [cursorOuts, dif_neg (show ¬ ((8 : ℕ) < 7) by decide),
        if_neg (show ¬ ((8 : ℕ) = 7) by decide)]
      rfl)

/-- The flag tape of field `f < 7` reads the carry flag on cell 0. -/
theorem cursorOuts_flag (base : Request → ℕ) (r : Request) (k : rcKey a r) (f : Fin 8) (hf : f.val < 7) :
    readTapeBit (cursorOuts a base f.val r k) 0 = flagsOf a r (keyDigits a r (some k)) f := by
  unfold cursorOuts
  rw [dif_pos hf, carryV_read]
  rfl

end
end NearCubicWires.PacketsConstruction.Cursor
