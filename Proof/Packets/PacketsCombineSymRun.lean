import Proof.Packets.PacketsCombineSymLocal

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsCombine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open NormalizedFiniteTransport Theorem25Completion.CycleBounds
noncomputable section

/-- The engine's 42-tape bank: the combine body plus the outer driver `word n`. -/
def engA (C R index m : ℕ) (left acc : Poly) (ps : List Poly) (bits : List Bool) (P : Poly) (n : ℕ) :
    Fin 42 → List Bool :=
  Fin.addCases (m := 41) (n := 1) (motive := fun _ => List Bool) (bodyA C R index m left acc ps bits P)
    (fun _ => CompareMachine.word n)

def engH (pos : ℕ) : Fin 42 → ℕ :=
  Fin.addCases (m := 41) (n := 1) (motive := fun _ => ℕ) (bodyH pos) (fun _ => 1)

noncomputable def symEngine := Composition.machine (TapeEmbedding.machine 1 (emb37 OrderedPacketReset.oneMachine))
  (Composition.machine (TapeEmbedding.machine 1 copyAccPark)
    (Composition.machine (TapeEmbedding.machine 1 (emb37 OrderedPacketReset.zeroMachine)) symLoop))

def symEngineCost (C w n m : ℕ) : ℕ :=
  (4 * commonReserve C w + 10) + 1 + ((4 * commonReserve C w + 5) + 1 + ((4 * commonReserve C w + 5) + 1 +
    (n * (symBodyBudget C w m + 3) + 3)))

/-- **The exact SYM engine.** From the arena with empty registers, cursor `n*m`, parked `[]`:
the parked register ends as `Product (blockPolys ps bits n m)`. -/
theorem symEngine_run (C w : ℕ) (S : Finset ℕ) (d : ℕ) (ps : List Poly) (bits : List Bool) (n m : ℕ)
    (hS : ∀ j ∈ S, j < C) (hps : ∀ P ∈ ps, NormalizedIntermediate.Bounded S d P)
    (hfit : (S.card + 1) ^ d ≤ 2 ^ w) (hfitn : (S.card + 1) ^ (d * n) ≤ 2 ^ w)
    (hlen : n * m ≤ ps.length) (hN : ps.length ≤ 2 ^ w) (hw : 1 ≤ w) :
    Step symEngine (symEngineCost C w n m) (engH (n * m))
      (engA C (commonReserve C w) (n * m) m [] [] ps bits [] n) (engH 0)
      (engA C (commonReserve C w) 0 m (leftAt ps bits n m [] n) [] ps bits
        (Normalized.structuralGF2Product (blockPolys ps bits n m)) n) := by
  set R := commonReserve C w with hRdef
  have h1 : ([[]] : Poly).length ≤ 2 ^ w := by
    simp only [List.length_singleton]
    exact Nat.one_le_two_pow
  have s1 := (emb37_run C R (n * m) m (n * m) [] [] [] [[]] ps bits []
    (OrderedPacketReset.one_run C w (n * m) [] [] ps (by simp))).embed
    (fun _ : Fin 1 => 1) (fun _ => CompareMachine.word n)
  have s2 := (by
    have h := copy_run' C R (n * m) m (n * m) [] [[]] ps bits [] 26 39 27 40 (by decide) (by decide)
      (by decide) (by decide) rfl rfl rfl rfl (reg_lengths C w _ h1).1 (reg_lengths C w [] (by simp)).1
      (reg_count_map C w _ h1) (reg_lengths C w [] (by simp)).2
    rw [bodyA_acc_to_park] at h
    exact h.embed (fun _ : Fin 1 => 1) (fun _ => CompareMachine.word n))
  have s3 := (emb37_run C R (n * m) m (n * m) [] [[]] [] [] ps bits [[]]
    (OrderedPacketReset.zero_run C w (n * m) [] [[]] ps h1)).embed
    (fun _ : Fin 1 => 1) (fun _ => CompareMachine.word n)
  have s4 := symLoop_run C w S d ps bits n m [] hS hps hfit hfitn hlen hN (by simp) hw
  exact s1.seq (s2.seq (s3.seq s4))

/-! ## The store of the parked register (masked) -/

/-- The store's 7-tape bank: `PacketBank`'s six tapes, then the mask log. -/
def stoA (R index cap : ℕ) (bank payload count : List Bool) : Fin 7 → List Bool :=
  Fin.addCases (m := 6) (n := 1) (motive := fun _ => List Bool) (PacketBank.A R index bank payload count)
    (fun _ => List.replicate cap false)

def stoSel (i : Fin 6) : Bool := decide (i.val = 1)

noncomputable def symStore := MaskedReset.machine PacketBank.store stoSel

/-- **The masked store.** An empty output tape receives `payload ++ count`; its head returns to `0`. -/
theorem symStore_run (R index : ℕ) (payload count : List Bool) (hp : payload.length = R)
    (hc : count.length = R) :
    Step symStore (2 * PacketBank.storeBudget R + 2)
      (Fin.addCases (m := 6) (n := 1) (motive := fun _ => ℕ) (PacketBank.H 0 1) (fun _ => 0))
      (stoA R index (PacketBank.storeBudget R) [] payload count)
      (Fin.addCases (m := 6) (n := 1) (motive := fun _ => ℕ)
        (fun i => if stoSel i then 0 else PacketBank.H (payload ++ count).length 1 i) (fun _ => 0))
      (stoA R index (PacketBank.storeBudget R) (payload ++ count) payload count) := by
  have h := PacketBank.store_run R index [] payload count hp hc
  simp only [List.nil_append, List.length_nil] at h
  have hm := h.mask stoSel (by
    intro i hi
    simp only [stoSel, decide_eq_true_eq] at hi
    have e : i = 1 := Fin.ext hi
    subst e
    rfl) (le_refl _)
  exact hm

end
end NearCubicWires.PacketsCombine
