import Proof.SourceAssembly.SourceFactorSelWordsHostRun
import Proof.SourceAssembly.SourceFactorSelItem4Top2

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceFactorSel.WordsHost
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source PCJ6fbdd6f776f6447d_Source
open NearCubicWires.SourceFactorSel.Words
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
open SourceInterfaces RepairSource.VerifierDecoding NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
noncomputable section
attribute [local irreducible] NearCubicWires.P1TopDownPaidPayload.tapes

/-- The six loop field ports the words stage reads: `fslot 17, 15, 23, 19, 21, 29`. -/
def srcIdx : Fin 6 → Fin 31 := ![17, 15, 23, 19, 21, 29]

theorem srcIdx_inj : Function.Injective srcIdx := by decide

section wr
variable {mask : MaskProducer} {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm} {printer : WilliamsAlgorithm}
  {packet : PacketWriter selector a} {rows : RowProducer selector a printer} {V : Nat}
  {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit} {mode : Bool}

/-- The words stage's sources on the loop region. -/
def srcOf (P : FactorProducer mode a pcpp) (reg : Fin (19 + 4 * P.t) → Fin V) : Fin 6 → Fin V :=
  fun i => reg (fslot P (srcIdx i))

theorem srcOf_inj (P : FactorProducer mode a pcpp) (reg : Fin (19 + 4 * P.t) → Fin V) (hreg : Function.Injective reg) :
    Function.Injective (srcOf P reg) :=
  fun _ _ h => srcIdx_inj (fslot_injective P (hreg h))

/-- **The words stage's contract on S's layout.** -/
theorem wordsRun_host (L : HostLay mask packet rows V) {k : Nat} (SB : Item4.StartBank a k)
    (hIn : ∀ j, (SB.inPort j).val = j.val)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits)) (Lsc target Rc : Nat)
    (P : FactorProducer mode a pcpp) (reg : Fin (19 + 4 * P.t) → Fin V) (hreg : Function.Injective reg)
    (nT : Fin V) (coefT : Fin 3 → Fin V) (Scr : Fin V → Prop) (In : Nat → (Fin V → Nat) → (Fin V → List Bool) → Prop)
    (layoutAt : ∀ m : Nat, Packets.Layout a ((requestAt coordinate ph ci Lsc target mode m).family a)
      (geometryOf selector a (requestAt coordinate ph ci Lsc target mode m)))
    (capsAt : Nat → RowCaps) (MB : List Bool) (dR : Nat) (Rpad : Fin V → Nat)
    (hregR : ∀ i, L.gB ≤ (reg i).val ∧ (reg i).val < L.wB)
    (hnT : nT.val = L.B + 89) (hcoefT : ∀ i, (coefT i).val = L.B + 80 + i.val)
    (hScr : ∀ x, Scr x → L.gB ≤ x.val ∧ x.val < L.wB) (hgB90 : L.B + 90 ≤ L.gB)
    (hN : L.wB + (nW mask.work (Cold.tapes a) k - 29) ≤ L.B + 43 + L.Pc) (hVB : L.B + 48 + L.Pc ≤ V)
    (hR1 : L.R1 = rowTapes printer rows.privateWork + 1)
    (hMB : ∀ m, SLoad.Setup.metaBits (layoutAt m).w (layoutAt m).degree (layoutAt m).C (capsAt m) = MB)
    (hdR : ∀ m, (capsAt m).descriptorReserve = dR)
    (hRpad : ∀ x : Fin V, L.G ≤ x.val → x.val < L.P0 + 408 + mask.work + L.tc → Rpad x = Rc)
    (hInRes : ∀ m, m ≤ (monomials coordinate ph ci).length → ∀ H A, In m H A → ∀ x : Fin V,
      L.B + 43 + L.Pc ≤ x.val → x.val < L.B + 48 + L.Pc →
      A x = ZeroPadding.pad Rc (wd a (requestAt coordinate ph ci Lsc target mode m) MB (x.val - (L.B + 43 + L.Pc) + 6)) ∧
        H x = 0)
    (hInBl : ∀ m H A, In m H A → ∀ x : Fin V, L.Blank (gwW mask.work (Cold.tapes a) k) x.val →
      A x = List.replicate Rc false ∧ H x = 0)
    (hInRw : ∀ m H A, In m H A → A (L.rewindSlots 1) = List.replicate dR true ∧ H (L.rewindSlots 1) = 0 ∧
      A (L.rewindSlots 2) = List.replicate dR false ∧ H (L.rewindSlots 2) = 0)
    (hNw : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * (requestAt coordinate ph ci Lsc target mode m).nativeWord.length + 1 ≤ Rc)
    (hS : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * ((requestAt coordinate ph ci Lsc target mode m).supportWord a).length + 1 ≤ Rc)
    (hT : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * ((requestAt coordinate ph ci Lsc target mode m).topWord a).length + 1 ≤ Rc)
    (cq : ∀ m, m ≤ (monomials coordinate ph ci).length → 4 * (requestAt coordinate ph ci Lsc target mode m).q + 3 ≤ Rc)
    (ck : ∀ m, m ≤ (monomials coordinate ph ci).length →
      4 * normalizedLiveCount (requestAt coordinate ph ci Lsc target mode m).q
        (requestAt coordinate ph ci Lsc target mode m).liveScale + 3 ≤ Rc)
    (cm : ∀ m, m ≤ (monomials coordinate ph ci).length →
      4 * ((requestAt coordinate ph ci Lsc target mode m).family a).occurrences.length + 3 ≤ Rc)
    (ci' : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * ((requestAt coordinate ph ci Lsc target mode m).indexWord a).length + 1 ≤ Rc)
    (hneed : ∀ m, m ≤ (monomials coordinate ph ci).length → SB.need (requestAt coordinate ph ci Lsc target mode m) ≤ Rc)
    (cl1 : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * ((requestAt coordinate ph ci Lsc target mode m).input a).length + 1 ≤ Rc)
    (cl2 : 2 * MB.length + 1 ≤ Rc) :
    Item4.WordsRun (wordsHostM L SB (srcOf P reg) (L.hostV_lt _ hN hVB))
      (fun m => Words.wordsCost mask SB (requestAt coordinate ph ci Lsc target mode m) MB)
      mask packet rows L.maskSlots L.pslots L.slot L.ret L.retDrv L.log L.familySlots L.poolSlots L.rewindSlots
      L.s1 L.d1 L.l1 L.s2 L.d2 L.l2 L.lenTape coordinate ph ci Lsc target mode layoutAt capsAt Rpad
      (Item4.PostLoopL P coordinate ph ci Lsc target Rc reg nT coefT Scr In Rpad)
      (fun x => ∃ p : Fin (nW mask.work (Cold.tapes a) k), 11 ≤ p.val ∧
        L.dock (srcOf P reg) (nW mask.work (Cold.tapes a) k) (L.hostV_lt _ hN hVB) p = x) := by
  intro m hm H A hpost
  obtain ⟨⟨H0, A0, hin, hoff, hregH, x17, x13, x15, x23, x19, x21, x29, x25, x27⟩, hlen⟩ := hpost
  have hgB := L.hgB
  have hwB := L.hwB
  
  have foot : ∀ x : Fin V, (x.val < L.B + 80 ∨ L.wB ≤ x.val) → A x = A0 x ∧ H x = H0 x := by
    intro x hx
    refine hoff x ?_ ?_ ?_ ?_
    · intro i e; have := hregR i; rw [e] at this; simp only [HostLay.B, HostLay.P0, HostLay.tc] at *; omega
    · intro e; rw [e, hnT] at hx; simp only [HostLay.B, HostLay.P0, HostLay.tc] at *; omega
    · intro i e; have := hcoefT i; have := i.isLt; rw [← e] at hx; simp only [HostLay.B, HostLay.P0, HostLay.tc] at *; omega
    · intro hs; have := hScr x hs; simp only [HostLay.B, HostLay.P0, HostLay.tc] at *; omega
  obtain ⟨H1, A1, Av, st, hpad, hres, fr⟩ := words_host_req L SB hIn (srcOf P reg) (srcOf_inj P reg hreg)
    (fun i => hregR _) hN hVB hR1 (requestAt coordinate ph ci Lsc target mode m) (layoutAt m) (capsAt m) MB Rc dR
    (hMB m) (hdR m) Rpad hRpad H A
    (by
      intro i
      refine ⟨?_, hregH _⟩
      fin_cases i
      · exact x17
      · exact x15
      · exact x23
      · exact x19
      · exact x21
      · exact x29)
    (by
      intro x h1 h2
      obtain ⟨e1, e2⟩ := foot x (Or.inr (by simp only [HostLay.B, HostLay.P0, HostLay.tc] at *; omega))
      obtain ⟨g1, g2⟩ := hInRes m hm H0 A0 hin x h1 h2
      exact ⟨e1.trans g1, e2.trans g2⟩)
    (by
      intro x hx
      have hx' : x.val < L.B + 80 ∨ L.wB ≤ x.val := by
        have hG := L.hG
        simp only [HostLay.Blank, HostLay.B, HostLay.P0, HostLay.tc] at *; omega
      obtain ⟨e1, e2⟩ := foot x hx'
      obtain ⟨g1, g2⟩ := hInBl m H0 A0 hin x hx
      exact ⟨e1.trans g1, e2.trans g2⟩)
    (by
      have v1 := L.hrw1
      have v2 := L.hrw2
      have hG := L.hG
      have hF := L.hF
      obtain ⟨e1, e2⟩ := foot (L.rewindSlots 1) (Or.inl (by simp only [HostLay.B, HostLay.P0, HostLay.tc] at *; omega))
      obtain ⟨f1, f2⟩ := foot (L.rewindSlots 2) (Or.inl (by simp only [HostLay.B, HostLay.P0, HostLay.tc] at *; omega))
      obtain ⟨g1, g2, g3, g4⟩ := hInRw m H0 A0 hin
      exact ⟨e1.trans g1, e2.trans g2, f1.trans g3, f2.trans g4⟩)
    hlen (hNw m hm) (hS m hm) (hT m hm) (cq m hm) (ck m hm) (cm m hm) (ci' m hm) (hneed m hm) (cl1 m hm) cl2
  refine ⟨H1, A1, Av, st, hpad, hres, ?_⟩
  intro x hx
  exact fr x (fun p hp e => hx ⟨p, hp, e⟩)

end wr

end
end NearCubicWires.SourceFactorSel.WordsHost

