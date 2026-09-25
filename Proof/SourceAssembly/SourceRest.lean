import Proof.SourceAssembly.SourceRestBackRun

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
namespace NearCubicWires.SourceConstruction.Rest
noncomputable section

def OutV (d : SourceConstruction.Dims) (eX pX gW v : Nat) : Prop :=
  (d.G ≤ v ∧ v < d.G + d.pscr) ∨ v = d.B ∨ (d.B + 19 + 61 ≤ v ∧ v < d.B + 19 + 64) ∨ v = d.B + 19 + 70 ∨
    (d.B + 19 + 71 + eX + pX ≤ v ∧ v < d.B + 19 + restPc eX pX gW)

def RestIn {V : Nat} (d : SourceConstruction.Dims) (eX pX gW Rc : Nat) (cur : Fin V) (K : Fin V → Prop)
    (K0 : Fin V → List Bool) (KH0 : Fin V → Nat) (m : Nat) (H : Fin V → Nat) (A : Fin V → List Bool) : Prop :=
  (∀ x : Fin V, OutV d eX pX gW x.val → A x = List.replicate Rc false ∧ H x = 0) ∧
  A cur = ZeroPadding.pad Rc (List.replicate m true) ∧ H cur = 0 ∧
  (∀ x, K x → A x = K0 x ∧ H x = KH0 x)

def ResidentRunH {U states : Nat} (machine : Machine U states) (cost : Nat → Nat)
    (mask : MaskProducer) {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} {printer : WilliamsAlgorithm}
    (packet : PacketWriter selector a) (rows : RowProducer selector a printer)
    (maskSlots : Fin (5 + mask.work) → Fin U)
    (pslots : Fin packet.ordinary.program.tapeCount → Fin U)
    (slot : Fin 13 → Fin U) (ret : Fin 4 → Fin U) (retDrv log : Fin U)
    (familySlots : Fin (rowTapes printer rows.privateWork + 1) → Fin U)
    (poolSlots : Fin 373 → Fin U) (rewindSlots : Fin 3 → Fin U)
    (s1 d1 l1 s2 d2 l2 lenTape : Fin U)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits))
    (L target : Nat) (mode : Bool) (Rc b : Nat) (nT : Fin U) (coefT : Fin 3 → Fin U)
    (layoutAt : ∀ m : Nat, Packets.Layout a ((requestAt coordinate ph ci L target mode m).family a)
      (geometryOf selector a (requestAt coordinate ph ci L target mode m)))
    (capsAt : Nat → RowCaps) (Rpad : Fin U → Nat)
    (In : Nat → (Fin U → Nat) → (Fin U → List Bool) → Prop) (Out : Fin U → Prop) : Prop :=
  ∀ (m : Nat), m ≤ (monomials coordinate ph ci).length →
    ∀ (H : Fin U → Nat) (A : Fin U → List Bool), In m H A →
    ∃ (H1 : Fin U → Nat) (A1 : Fin U → List Bool) (Av : Fin U → List Bool),
      Step machine (cost m) H A H1 A1 ∧
      (∀ x, A1 x = ZeroPadding.pad (Rpad x) (Av x)) ∧
      Nonempty (Resident mask packet rows maskSlots pslots slot ret retDrv log familySlots poolSlots
        rewindSlots s1 d1 l1 s2 d2 l2 lenTape (requestAt coordinate ph ci L target mode m) (layoutAt m)
        (capsAt m) H1 Av) ∧
      H1 nT = 0 ∧
      A1 nT = ZeroPadding.pad Rc (CompareMachine.word (monomials coordinate ph ci).length) ∧
      (∀ i, H1 (coefT i) = 0) ∧
      (∀ hm : m < (monomials coordinate ph ci).length,
        (∀ i : Fin 3, A1 (coefT i) = ZeroPadding.pad Rc (RepairOrdinary.frame
          (CloseoutRowsEstimatorCoefficients.Stream.recordFields b
            (CloseoutFinalC10SupplierCalls.coefficientEstimate ((monomials coordinate ph ci)[m]).coefficient)
            0 0 ⟨i.val, by omega⟩)))) ∧
      (∀ x, ¬ Out x → A1 x = A x ∧ H1 x = H x) ∧
      (∀ x, Out x → (A1 x).length ≤ Rc)

end
end NearCubicWires.SourceConstruction.Rest
end
