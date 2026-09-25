import Proof.SourceAssembly.SourceFactorSelItem4Top
import Proof.SourceAssembly.SourceFactorSelWordsDocks

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

/-- The words stage's entry: `PostLoop` and the length floor. -/
def PostLoopL {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit} {mode : Bool} {a : DecompositionAlgorithm}
    {U : Nat} (P : FactorProducer mode a pcpp)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits))
    (L target R : Nat) (reg : Fin (19 + 4 * P.t) → Fin U) (nT : Fin U) (coefT : Fin 3 → Fin U)
    (Scr : Fin U → Prop) (In : Nat → (Fin U → Nat) → (Fin U → List Bool) → Prop) (Rpad : Fin U → Nat)
    (m : Nat) (H : Fin U → Nat) (A : Fin U → List Bool) : Prop :=
  PostLoop P coordinate ph ci L target R reg nT coefT Scr In m H A ∧ ∀ x, Rpad x ≤ (A x).length

/-- **ITEM 4 with the length floor.** -/
theorem residentRunH_of2 {U sS sW : Nat}
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
    (L target : Nat) (mode : Bool) (Rc b qCap : Nat) (nT qTape : Fin U) (coefT : Fin 3 → Fin U)
    (layoutAt : ∀ m : Nat, Packets.Layout a ((requestAt coordinate ph ci L target mode m).family a)
      (geometryOf selector a (requestAt coordinate ph ci L target mode m)))
    (capsAt : Nat → RowCaps) (Rpad : Fin U → Nat)
    (In : Nat → (Fin U → Nat) → (Fin U → List Bool) → Prop) (Out : Fin U → Prop)
    (selM : Machine U sS) (costS : Nat → Nat) (P : FactorProducer mode a pcpp)
    (reg : Fin (19 + 4 * P.t) → Fin U) (hreg : Function.Injective reg) (Scr : Fin U → Prop)
    (hsel : SelRun selM costS P coordinate ph ci L target Rc b qCap reg qTape nT coefT Scr In)
    (W : Machine U sW) (costW : Nat → Nat) (WOut : Fin U → Prop)
    (hW : WordsRun W costW mask packet rows maskSlots pslots slot ret retDrv log familySlots poolSlots
      rewindSlots s1 d1 l1 s2 d2 l2 lenTape coordinate ph ci L target mode layoutAt capsAt Rpad
      (PostLoopL P coordinate ph ci L target Rc reg nT coefT Scr In Rpad) WOut)
    (hq : ∀ m H A, In m H A → H qTape = 0 ∧
      A qTape = ZeroPadding.pad qCap (natListWord
        [RepairRepresentation.literalIndex (pcpp.clauses ci).left,
         RepairRepresentation.literalIndex (pcpp.clauses ci).right]))
    (hOk : ∀ m, m ≤ (monomials coordinate ph ci).length →
      ∀ i : Fin 4, P.Ok (factorsAt coordinate ph ci m)[i.val]?)
    (hneed : ∀ m, m ≤ (monomials coordinate ph ci).length →
      ∀ i : Fin 4, P.need (factorsAt coordinate ph ci m)[i.val]? ≤ Rc)
    (hN : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * (requestAt coordinate ph ci L target mode m).nativeWord.length + 1 ≤ Rc)
    (hS : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * ((requestAt coordinate ph ci L target mode m).supportWord a).length + 1 ≤ Rc)
    (hT : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * ((requestAt coordinate ph ci L target mode m).topWord a).length + 1 ≤ Rc)
    (hregN : ∀ i, reg i ≠ nT) (hregC : ∀ i j, reg i ≠ coefT j)
    (hWN : ¬ WOut nT) (hWC : ∀ i, ¬ WOut (coefT i))
    (hOutReg : ∀ i, Out (reg i)) (hOutN : Out nT) (hOutC : ∀ i, Out (coefT i))
    (hOutScr : ∀ x, Scr x → Out x) (hOutW : ∀ x, WOut x → Out x)
    (hInOut : ∀ m H A, In m H A → ∀ x, Out x → (A x).length ≤ Rc ∧ H x = 0)
    (hInLen : ∀ m H A, In m H A → ∀ x, Rpad x ≤ (A x).length)
    (hwin : ∀ m, m ≤ (monomials coordinate ph ci).length →
      g7Cost costS costW P coordinate ph ci L target m + 1 ≤ Rc) :
    SourceConstruction.Rest.ResidentRunH (g7Machine selM P reg W) (g7Cost costS costW P coordinate ph ci L target)
      mask packet rows maskSlots pslots slot ret retDrv log familySlots poolSlots rewindSlots
      s1 d1 l1 s2 d2 l2 lenTape coordinate ph ci L target mode Rc b nT coefT layoutAt capsAt Rpad In Out := by
  intro m hm H A hin
  obtain ⟨hqH, hqA⟩ := hq m H A hin
  obtain ⟨H1, A1, st1, n1H, n1A, f1, r1H, r1A, c1H, c1A⟩ := hsel m hm H A hin hqH hqA
  obtain ⟨X, sx, x17, x13, x15, x23, x19, x21, x29, x25, x27⟩ :=
    loop_step P L target (factorsAt coordinate ph ci m) (factorsAt_le coordinate ph ci m) Rc
      (hOk m hm) (hneed m hm) (hN m hm) (hS m hm) (hT m hm)
  have st2 := sx.dock reg hreg H1 A1 (fun i => r1H i) (fun i => r1A i)
  have k2 : ∀ x, (∀ i, reg i ≠ x) →
      install reg A1 X x = A1 x ∧ dockH reg H1 (fun _ => 0) x = H1 x :=
    fun x hx => ⟨install_other reg A1 X x hx, dockH_other reg H1 _ x hx⟩
  have hpost : PostLoopL P coordinate ph ci L target Rc reg nT coefT Scr In Rpad m
      (dockH reg H1 (fun _ => 0)) (install reg A1 X) := by
    refine ⟨⟨H, A, hin, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro x hx hn hc hs
      obtain ⟨e1, e2⟩ := k2 x hx
      obtain ⟨g1, g2⟩ := f1 x hx hn hc hs
      exact ⟨e1.trans g1, e2.trans g2⟩
    · intro i; rw [dockH_slot reg hreg]
    · rw [install_slot reg hreg]; exact x17
    · rw [install_slot reg hreg]; exact x13
    · rw [install_slot reg hreg]; exact x15
    · rw [install_slot reg hreg]; exact x23
    · rw [install_slot reg hreg]; exact x19
    · rw [install_slot reg hreg]; exact x21
    · rw [install_slot reg hreg]; exact x29
    · rw [install_slot reg hreg]; exact x25
    · rw [install_slot reg hreg]; exact x27
    · intro x
      exact ((hInLen m H A hin x).trans (RunBound.step_len_ge st1 x)).trans (RunBound.step_len_ge st2 x)
  obtain ⟨H3, A3, Av, st3, hpad, hres, f3⟩ := hW m hm _ _ hpost
  have st : Step (g7Machine selM P reg W) (g7Cost costS costW P coordinate ph ci L target m) H A H3 A3 :=
    st1.seq (st2.seq st3)
  have keep23 : ∀ x, (∀ i, reg i ≠ x) → ¬ WOut x → A3 x = A1 x ∧ H3 x = H1 x := by
    intro x hx hw
    obtain ⟨e1, e2⟩ := f3 x hw
    obtain ⟨g1, g2⟩ := k2 x hx
    exact ⟨e1.trans g1, e2.trans g2⟩
  have kN := keep23 nT hregN hWN
  have kC : ∀ i, A3 (coefT i) = A1 (coefT i) ∧ H3 (coefT i) = H1 (coefT i) :=
    fun i => keep23 (coefT i) (fun j => hregC j i) (hWC i)
  refine ⟨H3, A3, Av, st, hpad, hres, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [kN.2]; exact n1H
  · rw [kN.1]; exact n1A
  · intro i; rw [(kC i).2]; exact c1H i
  · intro hlt i; rw [(kC i).1]; exact c1A hlt i
  · intro x hx
    have hr : ∀ i, reg i ≠ x := fun i e => hx (e ▸ hOutReg i)
    have hn : x ≠ nT := fun e => hx (e ▸ hOutN)
    have hc : ∀ i, coefT i ≠ x := fun i e => hx (e ▸ hOutC i)
    have hs : ¬ Scr x := fun h => hx (hOutScr x h)
    have hw : ¬ WOut x := fun h => hx (hOutW x h)
    obtain ⟨e1, e2⟩ := keep23 x hr hw
    obtain ⟨g1, g2⟩ := f1 x hr hn hc hs
    exact ⟨e1.trans g1, e2.trans g2⟩
  · intro x hx
    obtain ⟨hl, hh⟩ := hInOut m H A hin x hx
    exact RunBound.step_len_window st Rc x hl hh (hwin m hm)

end
end NearCubicWires.SourceFactorSel.Item4
end

