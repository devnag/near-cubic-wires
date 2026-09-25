import Proof.SourceAssembly.SourceFactorSelWordsRunB

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceFactorSel.Words
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source PCJ6fbdd6f776f6447d_Source
noncomputable section

/-- **The words stage's local machine** (fixed per `(mask, a, SB)`). -/
def wordsLoc (mask : MaskProducer) {a : DecompositionAlgorithm} {k : Nat} (SB : Item4.StartBank a k) :=
  Composition.machine (RecoveryFocus.machine (m1 mask.work (Cold.tapes a) k) SourceResident.copiesM)
  (Composition.machine (RecoveryFocus.machine (m2 mask.work (Cold.tapes a) k) SourceResident.occM)
  (Composition.machine (RecoveryFocus.machine (m3 mask.work (Cold.tapes a) k) (Item4.lmM mask))
  (Composition.machine (RecoveryFocus.machine (m4 mask.work (Cold.tapes a) k) (Item4.idxBlock SB))
  (Composition.machine (RecoveryFocus.machine (m5 mask.work (Cold.tapes a) k) (SourceRequest.InputPass.machine mask))
  (Composition.machine (RecoveryFocus.machine (m6 mask.work (Cold.tapes a) k) Item4.tkM)
  (Composition.machine (RecoveryFocus.machine (M7 mask.work a k) (Item4.poolBlock SB))
  (Composition.machine (RecoveryFocus.machine (m8 mask.work (Cold.tapes a) k) P1Closure.BinaryCacheColdMeasure.machine)
  (Composition.machine (RecoveryFocus.machine (m9 mask.work (Cold.tapes a) k) Streaming.machine)
    (RecoveryFocus.machine (m10 mask.work (Cold.tapes a) k) Streaming.machine)))))))))

/-- **Its per-request cost** (`Rc`-free). -/
def wordsCost (mask : MaskProducer) {a : DecompositionAlgorithm} {k : Nat} (SB : Item4.StartBank a k) (r : Request)
    (MB : List Bool) : Nat :=
  SourceResident.copiesCost (cw a r) + 1 +
  (SourceResident.occCost (r.supportWord a).length (r.family a).occurrences.length + 1 +
  (Item4.lmCost mask a r + 1 +
  (Item4.idxCost SB r + 1 +
  (SourceRequest.InputPass.cost mask a r + 1 +
  ((2 * (2 * (maskData a r).K + 5) + 2) + 1 +
  (Item4.poolCost SB r + 1 +
  (P1Closure.BinaryCacheColdMeasure.budget (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs + 1 +
  ((4 * MB.length + 2) + 1 + (4 * (List.replicate MB.length true).length + 2)))))))))

/-- **The words stage's local run.** -/
theorem words_run (selector : CyclicChoice.Laws) (mask : MaskProducer) {a : DecompositionAlgorithm} {k : Nat}
    (SB : Item4.StartBank a k) (hIn : ∀ j, (SB.inPort j).val = j.val) (r : Request) (MB : List Bool) (Rc : Nat)
    (E : Fin (nW mask.work (Cold.tapes a) k) → List Bool) (hE : ∀ x, E x = Gn a r MB Rc 0 x.val)
    (hN : 2 * r.nativeWord.length + 1 ≤ Rc) (hS : 2 * (r.supportWord a).length + 1 ≤ Rc)
    (hT : 2 * (r.topWord a).length + 1 ≤ Rc) (cq : 4 * r.q + 3 ≤ Rc)
    (ck : 4 * normalizedLiveCount r.q r.liveScale + 3 ≤ Rc) (cm : 4 * (r.family a).occurrences.length + 3 ≤ Rc)
    (ci : 2 * (r.indexWord a).length + 1 ≤ Rc) (hneed : SB.need r ≤ Rc) (hMB : MB.length ≤ Rc) :
    ∃ (H' : Fin (nW mask.work (Cold.tapes a) k) → Nat) (E' : Fin (nW mask.work (Cold.tapes a) k) → List Bool),
      Step (wordsLoc mask SB) (wordsCost mask SB r MB) (fun _ => 0) E H' E' ∧
      ∀ x : Fin (nW mask.work (Cold.tapes a) k), x.val < 30 →
        E' x = ZeroPadding.pad Rc (wd a r MB x.val) ∧ H' x = 0 := by
  have w0 := wi_zero a r MB Rc E hE
  obtain ⟨E1, s1, w1⟩ := st1 a r MB Rc E (fun _ => 0) w0 (by
    intro i
    fin_cases i
    · exact hN
    · exact hS
    · exact hT
    · show 2 * (List.replicate r.q true).length + 1 ≤ Rc
      rw [List.length_replicate]; omega
    · show 2 * (List.replicate (normalizedLiveCount r.q r.liveScale) true).length + 1 ≤ Rc
      rw [List.length_replicate]; omega)
  obtain ⟨E2, s2, w2⟩ := st2 a r MB Rc E1 (fun _ => 0) w1 hS
  obtain ⟨E3, s3, w3⟩ := st3 a r MB Rc mask E2 (fun _ => 0) w2 (by omega) cq ck cm
  obtain ⟨H4, E4, s4, w4⟩ := st4 a r MB Rc mask SB hIn E3 (fun _ => 0) w3 hneed
  obtain ⟨E5, s5, w5⟩ := st5 a r MB Rc mask E4 H4 w4 (by omega) cq ck cm hN hS ci hT
  obtain ⟨E6, s6, w6⟩ := st6 a r MB Rc E5 H4 w5
  obtain ⟨H7, E7, s7, w7⟩ := st7 a r MB Rc selector mask SB hIn E6 H4 w6 hneed
  obtain ⟨E8, s8, w8⟩ := st8 a r MB Rc E7 H7 w7
  obtain ⟨E9, s9, w9⟩ := st9 a r MB Rc E8 H7 w8 hMB
  obtain ⟨E10, s10, w10⟩ := st10 a r MB Rc E9 H7 w9 hMB
  refine ⟨H7, E10, s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq s10)))))))), ?_⟩
  intro x hx
  obtain ⟨e1, e2⟩ := w10 x (Or.inl hx)
  exact ⟨e1.trans (Gn_final a r MB Rc x.val), e2⟩

end
end NearCubicWires.SourceFactorSel.Words

