import Proof.SourceAssembly.SourceRest
import Proof.SourceAssembly.SourceFactorSelRunBound

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
namespace NearCubicWires.SourceFactorSel.Item4
noncomputable section

section defs
variable {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit} {mode : Bool} {a : DecompositionAlgorithm}

def SelRun {U s : Nat} (selM : Machine U s) (costS : Nat → Nat) (P : FactorProducer mode a pcpp)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits))
    (L target R b qCap : Nat) (reg : Fin (19 + 4 * P.t) → Fin U) (qTape nT : Fin U)
    (coefT : Fin 3 → Fin U) (Scr : Fin U → Prop)
    (Src : Nat → (Fin U → Nat) → (Fin U → List Bool) → Prop) : Prop :=
  ∀ (m : Nat), m ≤ (monomials coordinate ph ci).length →
    ∀ (H : Fin U → Nat) (A : Fin U → List Bool), Src m H A →
    H qTape = 0 →
    A qTape = ZeroPadding.pad qCap (natListWord
      [RepairRepresentation.literalIndex (pcpp.clauses ci).left,
       RepairRepresentation.literalIndex (pcpp.clauses ci).right]) →
    ∃ (H' : Fin U → Nat) (A' : Fin U → List Bool),
      Step selM (costS m) H A H' A' ∧
      H' nT = 0 ∧
      A' nT = ZeroPadding.pad R (RepairSource.VerifierDecoding.CompareMachine.word
        (monomials coordinate ph ci).length) ∧
      (∀ x, (∀ i, reg i ≠ x) → x ≠ nT → (∀ i, coefT i ≠ x) → ¬ Scr x →
        A' x = A x ∧ H' x = H x) ∧
      (∀ i, H' (reg i) = 0) ∧
      (∀ i, A' (reg i) = entry P
        (header mode q L target (factorsAt coordinate ph ci m).length)
        (fun k => P.Desc (factorsAt coordinate ph ci m)[k.val]?) R i) ∧
      (∀ i, H' (coefT i) = 0) ∧
      (∀ hm : m < (monomials coordinate ph ci).length,
        ∀ i : Fin 3, A' (coefT i) = ZeroPadding.pad R (RepairOrdinary.frame
          (CloseoutRowsEstimatorCoefficients.Stream.recordFields b
            (CloseoutFinalC10SupplierCalls.coefficientEstimate ((monomials coordinate ph ci)[m]).coefficient)
            0 0 ⟨i.val, by omega⟩)))

/-- **The bank after selection and loop** (the words stage's entry): some `In`-bank `(H0, A0)` off the selection's footprint, the
loop region's heads `0`, and the framed request fields of `requestAt m` (with their bare words and unary lengths) on the loop's
field ports. -/
def PostLoop {U : Nat} (P : FactorProducer mode a pcpp)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits))
    (L target R : Nat) (reg : Fin (19 + 4 * P.t) → Fin U) (nT : Fin U) (coefT : Fin 3 → Fin U)
    (Scr : Fin U → Prop) (In : Nat → (Fin U → Nat) → (Fin U → List Bool) → Prop)
    (m : Nat) (H : Fin U → Nat) (A : Fin U → List Bool) : Prop :=
  ∃ (H0 : Fin U → Nat) (A0 : Fin U → List Bool), In m H0 A0 ∧
    (∀ x, (∀ i, reg i ≠ x) → x ≠ nT → (∀ i, coefT i ≠ x) → ¬ Scr x → A x = A0 x ∧ H x = H0 x) ∧
    (∀ i, H (reg i) = 0) ∧
    A (reg (fslot P 17)) = ZeroPadding.pad R (RepairOrdinary.frame (requestAt coordinate ph ci L target mode m).nativeWord) ∧
    A (reg (fslot P 13)) = ZeroPadding.pad R (requestAt coordinate ph ci L target mode m).nativeWord ∧
    A (reg (fslot P 15)) = ZeroPadding.pad R
      (List.replicate (requestAt coordinate ph ci L target mode m).nativeWord.length true) ∧
    A (reg (fslot P 23)) = ZeroPadding.pad R
      (RepairOrdinary.frame ((requestAt coordinate ph ci L target mode m).supportWord a)) ∧
    A (reg (fslot P 19)) = ZeroPadding.pad R ((requestAt coordinate ph ci L target mode m).supportWord a) ∧
    A (reg (fslot P 21)) = ZeroPadding.pad R
      (List.replicate ((requestAt coordinate ph ci L target mode m).supportWord a).length true) ∧
    A (reg (fslot P 29)) = ZeroPadding.pad R
      (RepairOrdinary.frame ((requestAt coordinate ph ci L target mode m).topWord a)) ∧
    A (reg (fslot P 25)) = ZeroPadding.pad R ((requestAt coordinate ph ci L target mode m).topWord a) ∧
    A (reg (fslot P 27)) = ZeroPadding.pad R
      (List.replicate ((requestAt coordinate ph ci L target mode m).topWord a).length true)

end defs

/-- **The words stage's contract** (the consumer's `Resident` of `requestAt m`, fused with the padding and the frame): from every
`WIn`-bank at a cursor `m ≤ N`, one run of the fixed machine `W` reaches a bank whose unpadded view `Av` carries `Resident`, with
every tape outside `WOut` unchanged. -/
def WordsRun {U sW : Nat} (W : Machine U sW) (costW : Nat → Nat)
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
    (L target : Nat) (mode : Bool)
    (layoutAt : ∀ m : Nat, Packets.Layout a ((requestAt coordinate ph ci L target mode m).family a)
      (geometryOf selector a (requestAt coordinate ph ci L target mode m)))
    (capsAt : Nat → RowCaps) (Rpad : Fin U → Nat)
    (WIn : Nat → (Fin U → Nat) → (Fin U → List Bool) → Prop) (WOut : Fin U → Prop) : Prop :=
  ∀ (m : Nat), m ≤ (monomials coordinate ph ci).length →
    ∀ (H : Fin U → Nat) (A : Fin U → List Bool), WIn m H A →
    ∃ (H1 : Fin U → Nat) (A1 : Fin U → List Bool) (Av : Fin U → List Bool),
      Step W (costW m) H A H1 A1 ∧
      (∀ x, A1 x = ZeroPadding.pad (Rpad x) (Av x)) ∧
      Nonempty (Resident mask packet rows maskSlots pslots slot ret retDrv log familySlots poolSlots
        rewindSlots s1 d1 l1 s2 d2 l2 lenTape (requestAt coordinate ph ci L target mode m) (layoutAt m)
        (capsAt m) H1 Av) ∧
      (∀ x, ¬ WOut x → A1 x = A x ∧ H1 x = H x)

section main
variable {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit} {mode : Bool} {a : DecompositionAlgorithm}

/-- **The item-4 machine** (fixed before the input). -/
def g7Machine {U sS sW : Nat} (selM : Machine U sS) (P : FactorProducer mode a pcpp)
    (reg : Fin (19 + 4 * P.t) → Fin U) (W : Machine U sW) :=
  Composition.machine selM (Composition.machine (RecoveryFocus.machine reg (FactorLoop.machine P)) W)

/-- **Its per-call cost** (Rc-free whenever `costS`, `costW` are). -/
def g7Cost (costS costW : Nat → Nat) (P : FactorProducer mode a pcpp)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits)) (L target m : Nat) : Nat :=
  costS m + 1 + (FactorLoop.cost P L target (factorsAt coordinate ph ci m) + 1 + costW m)

end main

end
end NearCubicWires.SourceFactorSel.Item4
end

