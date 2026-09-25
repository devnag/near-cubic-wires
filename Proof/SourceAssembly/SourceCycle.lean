import Proof.SourceAssembly.SourceFinishCycle
import Proof.SourceAssembly.SourceRequestConsumer

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding SourceInterfaces
open PCJ1fef9807c6954e94_Native PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open SupplierEstimator SupplierPipeline NearCubicWires.P1Closure
namespace NearCubicWires.SourceConstruction.Cycle
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

/-- The rows family loop leaves its counter at `word N`, head `1`, with `N = |ds|`. -/
theorem exit_counter {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    {printer : WilliamsAlgorithm} (rows : RowProducer selector a printer) {r : Request}
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (facts : ∀ row ∈ (r.family a).rows, Packets.PacketFacts a (r.family a) (geometryOf selector a r) row)
    (caps : RowCaps) :
    (SLoad.Final.exitCfg printer rows layout facts caps).tapes (Fin.last _) =
      CompareMachine.word (dataList a (r.family a) (geometryOf selector a r) layout facts).length ∧
    (SLoad.Final.exitCfg printer rows layout facts caps).heads (Fin.last _) = 1 := by
  constructor
  · simp only [SLoad.Final.exitCfg, PCJ38fbfed565f64139_Family.exit, RepeatMachine.cfg, controlConfig,
      TapeEmbedding.config, dataList, List.length_map, List.length_attach]
    exact Fin.addCases_right (0 : Fin 1)
  · simp only [SLoad.Final.exitCfg, PCJ38fbfed565f64139_Family.exit, RepeatMachine.cfg, controlConfig,
      TapeEmbedding.config]
    exact Fin.addCases_right (0 : Fin 1)

/-- `pad 0` is the identity. -/
theorem pad_zero (w : List Bool) : ZeroPadding.pad 0 w = w := by
  simp [ZeroPadding.pad]

def Free {U tc w m : Nat} (slot : Fin 13 → Fin U) (maskSlots : Fin (5 + w) → Fin U)
    (pslots : Fin tc → Fin U) (poolSlots : Fin 373 → Fin U) (familySlots : Fin m → Fin U)
    (rewindSlots : Fin 3 → Fin U) (x : Fin U) : Prop :=
  SourceRequest.Outside slot maskSlots pslots poolSlots x ∧ (∀ i, familySlots i ≠ x) ∧
    (∀ i, rewindSlots i ≠ x)

structure Wiring {U : Nat} (mask : MaskProducer) {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} {printer : WilliamsAlgorithm}
    (packet : PacketWriter selector a) (rows : RowProducer selector a printer)
    (maskSlots : Fin (5 + mask.work) → Fin U)
    (pslots : Fin packet.ordinary.program.tapeCount → Fin U)
    (slot : Fin 13 → Fin U) (ret : Fin 4 → Fin U) (retDrv log : Fin U)
    (familySlots : Fin (rowTapes printer rows.privateWork + 1) → Fin U)
    (poolSlots : Fin 373 → Fin U) (rewindSlots : Fin 3 → Fin U)
    (s1 d1 l1 s2 d2 l2 lenTape : Fin U)
    (cs : Fin 16 → Fin U) (fam : Fin (r_tapes printer) → Fin U) (drv : Fin 7 → Fin U) : Prop where
  hinj : Function.Injective slot
  hmsk : slot 0 = maskSlots ⟨4, by omega⟩
  hoffm : ∀ j : Fin 13, j ≠ 0 → ∀ i, maskSlots i ≠ slot j
  hslot0 : ∀ j : Fin packet.ordinary.program.tapeCount, j.val = 0 → pslots j = slot 11
  hoffp : ∀ j : Fin packet.ordinary.program.tapeCount, j.val ≠ 0 → ∀ k, slot k ≠ pslots j
  hmp : ∀ (j : Fin packet.ordinary.program.tapeCount) (i : Fin (5 + mask.work)),
    maskSlots i ≠ pslots j
  hrm : ∀ (i : Fin 4) (j : Fin (5 + mask.work)), ret i ≠ maskSlots j
  hrl : ∀ i, ret i ≠ log
  hlm : ∀ j, log ≠ maskSlots j
  hdr : ∀ i, slot 1 ≠ ret i
  hdl : slot 1 ≠ log
  hDd : retDrv ≠ slot 1
  hDl : retDrv ≠ log
  hpS : ∀ (j : Fin 13) (i : Fin 373), slot j ≠ poolSlots i
  hpM : ∀ (j : Fin (5 + mask.work)) (i : Fin 373), maskSlots j ≠ poolSlots i
  hpP : ∀ (j : Fin packet.ordinary.program.tapeCount) (i : Fin 373), pslots j ≠ poolSlots i
  hpool0 : ∀ i : Fin (rowTapes printer rows.privateWork + 1), i.val = 0 →
    familySlots i = poolSlots 34
  hraw262 : ∀ i : Fin (rowTapes printer rows.privateWork + 1), i.val = 262 →
    familySlots i = pslots packet.ordinary.program.outputTape
  hfamOut : ∀ i : Fin (rowTapes printer rows.privateWork + 1), i.val ≠ 0 → i.val ≠ 262 →
    SourceRequest.Outside slot maskSlots pslots poolSlots (familySlots i)
  os1 : SourceRequest.Outside slot maskSlots pslots poolSlots s1
  od1 : SourceRequest.Outside slot maskSlots pslots poolSlots d1
  ol1 : SourceRequest.Outside slot maskSlots pslots poolSlots l1
  os2 : SourceRequest.Outside slot maskSlots pslots poolSlots s2
  od2 : SourceRequest.Outside slot maskSlots pslots poolSlots d2
  ol2 : SourceRequest.Outside slot maskSlots pslots poolSlots l2
  e1 : s1 ≠ d1
  e2 : s1 ≠ familySlots (rowRequestPort printer rows.privateWork)
  e3 : s1 ≠ l1
  e4 : d1 ≠ familySlots (rowRequestPort printer rows.privateWork)
  e5 : d1 ≠ l1
  e6 : familySlots (rowRequestPort printer rows.privateWork) ≠ l1
  k1 : s2 ≠ d2
  k2 : s2 ≠ familySlots (rowCapsPort printer rows.privateWork)
  k3 : s2 ≠ l2
  k4 : d2 ≠ familySlots (rowCapsPort printer rows.privateWork)
  k5 : d2 ≠ l2
  k6 : familySlots (rowCapsPort printer rows.privateWork) ≠ l2
  m1 : familySlots (rowRequestPort printer rows.privateWork) ≠ s2
  m2 : familySlots (rowRequestPort printer rows.privateWork) ≠ d2
  m4 : familySlots (rowRequestPort printer rows.privateWork) ≠ l2
  h1 : ∀ j, familySlots j ≠ rewindSlots 1
  h2 : ∀ j, familySlots j ≠ rewindSlots 2
  or1 : SourceRequest.Outside slot maskSlots pslots poolSlots (rewindSlots 1)
  or2 : SourceRequest.Outside slot maskSlots pslots poolSlots (rewindSlots 2)
  hcs : Function.Injective cs
  hjoin : Function.Injective (Finish.joinSlots printer fam drv)
  hd3 : drv 3 = cs 4
  hd5 : drv 5 = cs 3
  hd6 : drv 6 = cs 5
  hfam_cs : ∀ i k, fam i ≠ cs k
  hdu_cs : ∀ k : Fin 7, (k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 4) → ∀ j, drv k ≠ cs j
  hlen : cs 0 = lenTape
  hcnt : cs 3 = familySlots (Fin.last _)
  hcntRew : ∀ i, rewindSlots i ≠ familySlots (Fin.last _)
  hsrcp : fam (PCJ515eaa990d75455b_FamilyInit.sourcePort printer) = rewindSlots 0
  fcs : ∀ k : Fin 16, k.val ≠ 3 → Free slot maskSlots pslots poolSlots familySlots rewindSlots (cs k)
  fdrv : ∀ k : Fin 7, (k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 4) →
    Free slot maskSlots pslots poolSlots familySlots rewindSlots (drv k)
  ffam : ∀ i, i ≠ PCJ515eaa990d75455b_FamilyInit.sourcePort printer →
    Free slot maskSlots pslots poolSlots familySlots rewindSlots (fam i)

def cycleCode {U s : Nat} (mask : MaskProducer) {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} {printer : WilliamsAlgorithm}
    (packet : PacketWriter selector a) (rows : RowProducer selector a printer)
    (maskSlots : Fin (5 + mask.work) → Fin U) (hminj : Function.Injective maskSlots)
    (pslots : Fin packet.ordinary.program.tapeCount → Fin U) (hsinj : Function.Injective pslots)
    (slot : Fin 13 → Fin U) (ret : Fin 4 → Fin U)
    (retDrv log rawDrv rawDst rawLog : Fin U)
    (familySlots : Fin (rowTapes printer rows.privateWork + 1) → Fin U)
    (hfinj : Function.Injective familySlots)
    (poolSlots : Fin 373 → Fin U) (hpinj : Function.Injective poolSlots)
    (rewindSlots : Fin 3 → Fin U) (hrinj : Function.Injective rewindSlots)
    (hraw : pslots packet.ordinary.program.outputTape = familySlots
      ((PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork rows.privateWork) 262).castAdd 1))
    (hpool : poolSlots 34 = familySlots
      ((PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork rows.privateWork) 0).castAdd 1))
    (hsrc : rewindSlots 0 = familySlots
      ((PCJ38fbfed565f64139_Ready.descriptor printer (rowWork rows.privateWork)).castAdd 1))
    (s1 d1 l1 s2 d2 l2 : Fin U) (pre : Machine U s)
    (cs : Fin 16 → Fin U) (fam : Fin (r_tapes printer) → Fin U) (drv : Fin 7 → Fin U) :
    MaskFamilyCode mask packet rows U :=
  { SLoad.Prepared.code mask packet rows maskSlots hminj pslots hsinj slot ret retDrv log rawDrv
      rawDst rawLog familySlots hfinj poolSlots hpinj rewindSlots hrinj hraw hpool hsrc
      s1 d1 l1 s2 d2 l2 _ (FinishCycle.machine printer cs fam drv) with
    seed := PCJ6e421fabe2aa4155_SourceRefill.prepend
      (SourceRequest.seedCode mask packet maskSlots hminj pslots hsinj slot ret retDrv log rawDrv
        rawDst rawLog) pre }

/-- The descriptor port and the counter are ordinary family tapes (not the aliased `0` or `262`). -/
theorem port_val {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    {printer : WilliamsAlgorithm} (rows : RowProducer selector a printer) :
    (SLoad.Final.port printer rows).val ≠ 0 ∧ (SLoad.Final.port printer rows).val ≠ 262 := by
  simp only [SLoad.Final.port, Fin.val_castAdd, PCJ38fbfed565f64139_Ready.descriptor,
    PCJ38fbfed565f64139_Ready.frameSlots, Fin.val_natAdd]
  omega

theorem last_val {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    {printer : WilliamsAlgorithm} (rows : RowProducer selector a printer) :
    (Fin.last (rowTapes printer rows.privateWork)).val ≠ 0 ∧
      (Fin.last (rowTapes printer rows.privateWork)).val ≠ 262 := by
  simp only [Fin.val_last, rowTapes, rowWork, PCJ38fbfed565f64139_Ready.tapes]
  omega

end
end NearCubicWires.SourceConstruction.Cycle
end
