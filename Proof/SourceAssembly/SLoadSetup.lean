import Proof.SourceAssembly.SLoadRowInput

/-! Deliverable 2, the `setupLoad` machine.

`SLoad.RowInput` reduced the second conjunct of `MaskFamilyCode.Prepared` to
two produced words, two structure aliases and a zero backing. Both produced
words are `RepairOrdinary.frame` of a bare word:

* `rowPublicInput … rowRequestPort = frame (r.input a)`;
* `rowPublicInput … rowCapsPort = rowMetadataWord w degree C caps`, which is by
  definition `frame (natListWord [w,degree,C] ++ caps.word)`.

So `setupLoad` is TWO calls of the raw framer this loader family already uses
(`SLoad.MaskFrame.machine`, the docked `AppendFrameKernel`), each driven by a
retained unary length word onto a zero-backed destination slot. Ten states,
eight slots, no request in scope, and the exit bank differs from the entry bank
at exactly the two destination slots — so the two aliases and the 440-plus
blank header tapes are carried through untouched and no clearing scan is paid.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.Setup
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
noncomputable section

/-- The setup loader: two paid framings on one ambient layout. -/
noncomputable def machine {U : Nat} (s1 d1 t1 l1 s2 d2 t2 l2 : Fin U) :=
  Composition.machine (MaskFrame.machine s1 d1 t1 l1) (MaskFrame.machine s2 d2 t2 l2)

/-- Fuel for the setup loader, in the two physical word lengths. -/
def cost (n1 n2 : Nat) : Nat := (4 * n1 + 4) + 1 + (4 * n2 + 4)

/-- Two independent framings, sequenced. -/
theorem setup_frames {U : Nat} (s1 d1 t1 l1 s2 d2 t2 l2 : Fin U)
    (h1 : s1 ≠ d1) (h2 : s1 ≠ t1) (h3 : s1 ≠ l1)
    (h4 : d1 ≠ t1) (h5 : d1 ≠ l1) (h6 : t1 ≠ l1)
    (k1 : s2 ≠ d2) (k2 : s2 ≠ t2) (k3 : s2 ≠ l2)
    (k4 : d2 ≠ t2) (k5 : d2 ≠ l2) (k6 : t2 ≠ l2)
    (m1 : t1 ≠ s2) (m2 : t1 ≠ d2) (m3 : t1 ≠ t2) (m4 : t1 ≠ l2)
    (capS1 capD1 cap1 capL1 capS2 capD2 cap2 capL2 : Nat) (w1 w2 : List Bool)
    (hl1 : 2 * w1.length + 1 ≤ capL1) (hl2 : 2 * w2.length + 1 ≤ capL2)
    (H : Fin U → Nat) (A : Fin U → List Bool)
    (hH1s : H s1 = 0) (hH1d : H d1 = 0) (hH1t : H t1 = 0) (hH1l : H l1 = 0)
    (hH2s : H s2 = 0) (hH2d : H d2 = 0) (hH2t : H t2 = 0) (hH2l : H l2 = 0)
    (hA1s : A s1 = ZeroPadding.pad capS1 w1)
    (hA1d : A d1 = ZeroPadding.pad capD1 (List.replicate w1.length true))
    (hA1t : A t1 = List.replicate cap1 false) (hA1l : A l1 = List.replicate capL1 false)
    (hA2s : A s2 = ZeroPadding.pad capS2 w2)
    (hA2d : A d2 = ZeroPadding.pad capD2 (List.replicate w2.length true))
    (hA2t : A t2 = List.replicate cap2 false) (hA2l : A l2 = List.replicate capL2 false) :
    Step (machine s1 d1 t1 l1 s2 d2 t2 l2) (cost w1.length w2.length) H A H
      (Function.update (Function.update A t1 (ZeroPadding.pad cap1 (frame w1))) t2
        (ZeroPadding.pad cap2 (frame w2))) := by
  have e1 := MaskFrame.mask_frame_step s1 d1 t1 l1 h1 h2 h3 h4 h5 h6
    capS1 capD1 cap1 capL1 w1 hl1 H A hH1s hH1d hH1t hH1l hA1s hA1d hA1t hA1l
  have e2 := MaskFrame.mask_frame_step s2 d2 t2 l2 k1 k2 k3 k4 k5 k6
    capS2 capD2 cap2 capL2 w2 hl2 H
    (Function.update A t1 (ZeroPadding.pad cap1 (frame w1))) hH2s hH2d hH2t hH2l
    (by rw [Function.update_of_ne (Ne.symm m1)]; exact hA2s)
    (by rw [Function.update_of_ne (Ne.symm m2)]; exact hA2d)
    (by rw [Function.update_of_ne (Ne.symm m3)]; exact hA2t)
    (by rw [Function.update_of_ne (Ne.symm m4)]; exact hA2l)
  exact e1.seq e2

/-- The bare metadata bits the caps port's word frames. -/
def metaBits (w degree C : Nat) (caps : RowCaps) : List Bool :=
  natListWord [w, degree, C] ++ caps.word

theorem meta_frame (w degree C : Nat) (caps : RowCaps) :
    rowMetadataWord w degree C caps = frame (metaBits w degree C caps) := rfl


/-! ### Two of `Prepared`'s remaining obligations are already clauses of
`RowCaps.Good` — citations, not work. -/

/-- The third conjunct of `MaskFamilyCode.Prepared`, `pos ≤ rewindCap`, with
`rewindCap := caps.descriptorReserve`. -/
theorem descriptor_fits {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    {printer : WilliamsAlgorithm} {r : Request}
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (facts : ∀ row ∈ (r.family a).rows,
      Packets.PacketFacts a (r.family a) (geometryOf selector a r) row)
    (caps : RowCaps) (good : RowCaps.Good selector a printer r layout facts caps) :
    (PCJ38fbfed565f64139_Cached.descriptorWord printer
        (dataList a (r.family a) (geometryOf selector a r) layout facts)).length
      ≤ caps.descriptorReserve :=
  good.2.2.2



end
end SLoad.Setup
