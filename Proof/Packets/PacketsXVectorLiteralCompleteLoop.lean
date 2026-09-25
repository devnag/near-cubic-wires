import Proof.Packets.PacketsXVectorLiteralLevelReentry

/-! The full fixed ordinary vector machine, with both providers instantiated.
The premise is only a resident data layout and the frozen numerical census;
all preparation, child, parent, and level executions are proved here. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.RepairSource.CloseoutRawRows
open CloseoutRowsModeCache NormalizedFiniteTransport Theorem25Completion.CycleBounds SubstitutionCensus
noncomputable section

def uniformPrepareBudget (R root depth fuel : Nat) :=
  10*R+4*depth+depth*(8*R+22)+2*root+186+fuel

theorem prepare_budget_uniform (R root depth level fuel : Nat) (hl : level≤depth) :
    prepareBudget R root level fuel≤uniformPrepareBudget R root depth fuel := by
  have hh:=GradedHalveRound.halve_iterate_le root (level/3)
  have hd : level/3≤depth := (Nat.div_le_self level 3).trans hl
  have hm:=Nat.mul_le_mul_right (8*R+22) hd
  unfold prepareBudget GradedWindow.budget uniformPrepareBudget
  omega

def denseLevels (C M depth : Nat) (p : Parameters) (initial : List PacketVector.Packet) : Nat → List PacketVector.Packet
  | 0=>initial
  | done+1=>let q:={p with level:=depth-(done+1)}
      DenseAtomProgram.table C (q.level+1) (WindowProvider.modePairs q M) (denseLevels C M depth p initial done)
        (WindowProvider.modePairs q M).length

def literalLevelFuel (C w M root depth : Nat) :=
  oneLevelFuel (commonReserve C w) (literalDeltaFuel C w) (M+1)
    (uniformPrepareBudget (commonReserve C w) root depth (WindowProvider.levelUniformBudget C w))

def literalLoopState (C R M root depth : Nat) (p : Parameters) (initial : List PacketVector.Packet)
    (done : Nat) (left right : PacketVector.Packet) (fields : Fin 222 → List Bool) (extra : Fin 32 → List Bool) : Prop :=
  VectorAccumulator.Fits R left ∧ VectorAccumulator.Fits R right ∧
    LiteralLevelState C R M root p (denseLevels C M depth p initial done) fields extra

theorem literal_complete_loop (C w d population active depth root : Nat)
    (mask : Finset (Fin population)) (seed : ToeplitzSeed (canonicalGradedRank population active))
    (wins : Fin depth → Nat) (initial : List PacketVector.Packet) (input : Fin 298 → List Bool)
    (hd : depth≤canonicalGradedRank population active)
    (hrank : canonicalGradedRank population active≤9*population)
    (hC : (258*population+2)^2≤C) (hcodesC : (depth+2*population+2)^2≤C)
    (hpop : 1≤population) (hi : population≤2^(canonicalGradedRank population active))
    (hw : 3≤w) (hdegree : structuralListCoordinateRawDegree depth wins 0≤d)
    (hfit : (population*(2*depth+1)+2)^d≤2^w)
    (hwin : ∀level,wins level=GradedWindow.window root level.val)
    (hW : ∀level,wins level≤64*(C+2)) (hroot : root+67≤commonReserve C w)
    (hinput : LevelReady C (commonReserve C w) (population+1) depth
      (NormalizedVector.table (canonicalGradedLabel population active) seed wins 0)
      (literalLoopState C (commonReserve C w) population root depth
        (parameters population active 0 (C+9) mask seed) initial) 0 input) :
    ∃output,Step (machine WindowProvider.literalProvider WindowProvider.levelProvider)
      (depth*(literalLevelFuel C w population root depth+2*depth+6)+3)
      (Fin.addCases (levelH (fun _ : Fin 222=>0)) (fun _ : Fin 1=>1))
      (Fin.addCases input (fun _ : Fin 1=>WindowSeed.source (commonReserve C w) depth))
      (Fin.addCases (levelH (fun _ : Fin 222=>0)) (fun _ : Fin 1=>1))
      (Fin.addCases output (fun _ : Fin 1=>WindowSeed.source (commonReserve C w) depth)) ∧
      LevelReady C (commonReserve C w) (population+1) depth
        (NormalizedVector.table (canonicalGradedLabel population active) seed wins 0)
        (literalLoopState C (commonReserve C w) population root depth
          (parameters population active 0 (C+9) mask seed) initial) depth output := by
  let R:=commonReserve C w
  let p:=parameters population active 0 (C+9) mask seed
  have reserve : C+2≤R := LiteralCacheReuse.reserve_width C w
  have small : depth+2*population+2≤C := by
    nlinarith only [hcodesC,Nat.zero_le ((depth+2*population+2-1)^2)]
  apply level_loop_run WindowProvider.literalProvider WindowProvider.levelProvider C R (population+1) depth
    (literalLevelFuel C w population root depth) _ _ input hinput (by omega) (by omega)
  intro done hdone ci pi left right fields extra hci hpi hstate
  obtain ⟨hlf,hrf,hs⟩:=hstate
  let level : Fin depth:=⟨depth-(done+1),by omega⟩
  let q:=parameters population active level.val (C+9) mask seed
  let bank:=denseLevels C population depth p initial done
  have hs0 : LiteralLevelState C R population root q bank fields extra :=
    level_state_change_level C R population root level.val p bank fields extra hs
  obtain ⟨old,hold,hin⟩:=level_state_window C R population root ci pi level.val q bank fields extra hs0
    (by omega) left right
    (vectorBank C R (NormalizedVector.table (canonicalGradedLabel population active) seed wins 0 done))
    (PacketVector.bank R (List.replicate (population+1) []))
  obtain ⟨out,priv,hout,hpriv,hmode⟩:=hs0.modeWords
  obtain ⟨left',right',fields',extra',run,hl',hr',hq⟩:=literal_level_transaction C w d population active depth done ci pi root old
    mask seed wins level hdone rfl hd q rfl out priv bank hrank hC hcodesC hpop hi hw hdegree hfit
    (hwin level) (hW level) hpriv hout hs0.bankLength hs0.bankFits left right fields extra hlf hrf hci hpi hs0.ready hs0.cold
    hin hroot hold hs0.tagLength (hmode left right) hs0.width hs0.count hs0.digit hs0.bank
    (hs0.privateLength left right) hs0.denseCountLength hs0.levelLength hs0.tempLength
  have prepared:=level_state_prepared C w population root q bank left right fields extra hs0 rfl hrank
    (level.isLt.le.trans hd) hC (by omega) hroot
  have returned:=level_state_preserved C R population root q _ _ fields' extra prepared hq.1.ready hq.2.2.1
  have next:=level_state_change_level C R population root 0 q _ fields' extra returned
  have fuel : oneLevelFuel R (literalDeltaFuel C w) (population+1)
      (prepareBudget R root level.val (WindowProvider.levelUniformBudget C w))≤literalLevelFuel C w population root depth := by
    have bound:=prepare_budget_uniform R root depth level.val (WindowProvider.levelUniformBudget C w) level.isLt.le
    unfold literalLevelFuel oneLevelFuel
    dsimp only [R] at bound ⊢
    omega
  refine ⟨left',right',fields',extra',run.enlarge fuel,hl',hr',?_⟩
  rw [hq.2.2.2]
  exact next

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
