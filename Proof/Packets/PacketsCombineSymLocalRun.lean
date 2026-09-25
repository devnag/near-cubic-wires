import Proof.Packets.PacketsCombineSymDock

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsCombine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open NearCubicWires.PacketsConstruction
open NormalizedFiniteTransport Theorem25Completion.CycleBounds
noncomputable section

/-- The SYM stage's local machine, fixed given the metadata machine. -/
noncomputable def symLocalM {e s : ℕ} (M : Machine (16 + e) s) :=
  Composition.machine (RecoveryFocus.machine (metaSlot e) M)
    (Composition.machine (RecoveryFocus.machine (kbSlot e) KitBoot.machine)
      (Composition.machine (moves3 e)
        (Composition.machine (RecoveryFocus.machine (engSlot e) symEngine)
          (Composition.machine (PhysicalIndexReload.move (t := 117 + e) ⟨114, by omega⟩ .right)
            (RecoveryFocus.machine (stoSlot e) symStore)))))

def symLocalCost (mcost C w n m : ℕ) : ℕ :=
  mcost + 1 + (KitBoot.cost C w + 1 + ((1 + 1 + (1 + 1 + 1)) + 1 + (symEngineCost C w n m + 1 +
    (1 + 1 + (2 * PacketBank.storeBudget (commonReserve C w) + 2)))))

/-- **The SYM local run.** -/
theorem symLocal_run {e s : ℕ} (M : Machine (16 + e) s) (mcost : ℕ) (mH : Fin (16 + e) → ℕ)
    (mA : Fin (16 + e) → List Bool) (Rb C w m n : ℕ) (input : List Bool) (keys : Fin 8 → List Bool)
    (coords bits : List Bool)
    (hm : Step M mcost (fun _ => 0) (metaIn e input keys) mH mA)
    (hk : ∀ i : Fin (16 + e), i.val ≤ 8 → mA i = metaIn e input keys i ∧ mH i = 0)
    (h9 : mA ⟨9, by omega⟩ = UnaryTemplate.tape C ∧ mH ⟨9, by omega⟩ = 0)
    (h10 : mA ⟨10, by omega⟩ = UnaryTemplate.tape C ∧ mH ⟨10, by omega⟩ = 0)
    (h11 : mA ⟨11, by omega⟩ = UnaryTemplate.tape w ∧ mH ⟨11, by omega⟩ = 0)
    (h12 : mA ⟨12, by omega⟩ = UnaryTemplate.tape m ∧ mH ⟨12, by omega⟩ = 0)
    (h13 : mA ⟨13, by omega⟩ = UnaryTemplate.tape n ∧ mH ⟨13, by omega⟩ = 0)
    (h14 : mA ⟨14, by omega⟩ = UnaryTemplate.tape (n * m) ∧ mH ⟨14, by omega⟩ = 0)
    (h15 : mA ⟨15, by omega⟩ = bits ∧ mH ⟨15, by omega⟩ = n * m)
    (S : Finset ℕ) (d : ℕ) (ps : List Poly)
    (hcoords : coords = OrderedPacketStep.bank C (commonReserve C w) ps)
    (hS : ∀ j ∈ S, j < C) (hps : ∀ P ∈ ps, NormalizedIntermediate.Bounded S d P)
    (hfit : (S.card + 1) ^ d ≤ 2 ^ w) (hfitn : (S.card + 1) ^ (d * n) ≤ 2 ^ w)
    (hlen : n * m ≤ ps.length) (hN : ps.length ≤ 2 ^ w) (hw : 1 ≤ w)
    (hR1 : 1 ≤ commonReserve C w) (hRb : PacketBank.storeBudget (commonReserve C w) ≤ Rb)
    (hnm : n * m + 2 ≤ commonReserve C w) (hm2 : m + 2 ≤ Rb) (hn2 : n + 2 ≤ Rb) :
    ∃ (H' : Fin (117 + e) → ℕ) (A' : Fin (117 + e) → List Bool),
      Step (symLocalM M) (symLocalCost mcost C w n m) (fun _ => 0) (lentry e Rb input keys coords) H' A' ∧
      (∀ i : Fin (117 + e), i.val ≤ 9 → A' i = lentry e Rb input keys coords i ∧ H' i = 0) ∧
      A' ⟨10, by omega⟩ = ZeroPadding.pad Rb
        (ZeroPadding.pad (commonReserve C w)
            ((Normalized.structuralGF2Product (blockPolys ps bits n m)).map (maskNat C)).flatten ++
          ZeroPadding.pad (commonReserve C w)
            (CompareMachine.word (Normalized.structuralGF2Product (blockPolys ps bits n m)).length)) ∧
      H' ⟨10, by omega⟩ = 0 := by
  have hRb' : commonReserve C w ≤ Rb := by unfold PacketBank.storeBudget at hRb; omega
  obtain ⟨H1, A1, s1, f1⟩ := stage1 e Rb C w m n input keys coords bits M mcost mH mA hm hk h9 h10 h11 h12 h13 h14 h15
  obtain ⟨H2, A2, s2, f2⟩ := stage2 e Rb C w m n input keys coords bits H1 A1 f1
  obtain ⟨H3, s3, f3⟩ := stage3 e Rb C w m n input keys coords bits H2 A2 f2
  obtain ⟨H4, A4, s4, o4, k4⟩ := stage4 e Rb C w m n input keys coords bits S d ps hcoords hS hps hfit hfitn
    hlen hN hw hR1 hRb' hnm hm2 hn2 H3 A2 f3
  have f4 := stage4_facts e Rb C w m n input keys coords bits ps hcoords H3 A2 f3 H4 A4 o4 k4
  have hPf : (Normalized.structuralGF2Product (blockPolys ps bits n m)).length ≤ 2 ^ w := by
    rw [← parkAt_full]
    exact (NormalizedIntermediate.census (parkAt_bounded S d ps bits n m n hps)).trans hfitn
  obtain ⟨H6, A6, s6, fb6, fa6, fh6⟩ := stage56 e Rb C w m input keys coords _ hPf hRb H4 A4 f4
  exact ⟨H6, A6, s1.seq (s2.seq (s3.seq (s4.seq s6))), fb6, fa6, fh6⟩

end
end NearCubicWires.PacketsCombine
