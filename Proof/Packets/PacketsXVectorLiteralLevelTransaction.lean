import Proof.Packets.PacketsXVectorLiteralLevelPrepare
import Proof.Packets.PacketsXVectorLiteralParents
import Proof.Packets.PacketsXVectorWorkerLevelBounded
import Proof.Packets.PacketsXWindowLevelProviderMeaning

/-! One complete level update of the fixed ordinary vector program. The
preparation, literal delta calls, both arithmetic loops, indexed writes, and
bank turnover are all instantiated by their concrete execution theorems. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.RepairSource.CloseoutRawRows
open CloseoutRowsModeCache NormalizedFiniteTransport Theorem25Completion.CycleBounds SubstitutionCensus
noncomputable section

theorem literal_level_transaction (C w d population active depth done ci pi root old : Nat)
    (mask : Finset (Fin population)) (seed : ToeplitzSeed (canonicalGradedRank population active))
    (wins : Fin depth → Nat) (level : Fin depth) (hdone : done<depth)
    (hlevel : level.val=depth-(done+1)) (hd : depth≤canonicalGradedRank population active)
    (p : Parameters) (hp : p=parameters population active level.val (C+9) mask seed)
    (out : List Bool) (priv : Fin 15 → List Bool) (initial : List PacketVector.Packet)
    (hrank : p.rank≤9*population) (hC : (258*population+2)^2≤C)
    (hcodesC : (depth+2*population+2)^2≤C) (hpop : 1≤population) (hi : population≤2^p.rank)
    (hw : 3≤w) (hdegree : structuralListCoordinateRawDegree depth wins 0≤d)
    (hfit : (population*(2*depth+1)+2)^d≤2^w)
    (hwin : wins level=GradedWindow.window root level.val) (hW : wins level≤64*(C+2))
    (hpriv : ∀i,(priv i).length≤commonReserve C w) (hout : out.length≤commonReserve C w)
    (hinit : initial.length=C) (hinits : ∀P∈initial,PacketVector.Fits (commonReserve C w) P)
    (left right : PacketVector.Packet) (fields : Fin 222 → List Bool) (extra : Fin 32 → List Bool)
    (hleft : VectorAccumulator.Fits (commonReserve C w) left)
    (hright : VectorAccumulator.Fits (commonReserve C w) right)
    (hci : ci+1≤commonReserve C w) (hpi : pi+1≤commonReserve C w)
    (hready : ProviderReady C (commonReserve C w) fields)
    (hcold : ∀j,j.val<17 → extra j=List.replicate (commonReserve C w) false)
    (hin : ∀j,A C (commonReserve C w) ci pi level.val left right []
      (vectorBank C (commonReserve C w) (NormalizedVector.table (canonicalGradedLabel population active) seed wins 0 done))
      (PacketVector.bank (commonReserve C w) (List.replicate (population+1) [])) fields extra (VectorWorkerArena.windowSlots j)=
      GradedWindow.A (commonReserve C w) root level.val 0 0 old j)
    (hroot : root+67≤commonReserve C w) (hold : old+1≤commonReserve C w)
    (htag : (fields 153).length=commonReserve C w)
    (hmode : ∀i,i≠12 → ModeCacheReady.A p population (commonReserve C w) out priv i=
      providerA C (commonReserve C w) left right fields (WindowProvider.modePorts i))
    (au : fields 149=WindowSeed.source (commonReserve C w) (C+9))
    (aM : fields 150=WindowSeed.source (commonReserve C w) (2*population))
    (av : fields 151=WindowSeed.source (commonReserve C w) (Nat.log 2 (2*population)+1))
    (abank : fields 106=PacketVector.bank (commonReserve C w) initial)
    (hprivate : ∀i,i≠59 → i≠60 → i≠62 → i≠64 → i≠65 →
      (providerA C (commonReserve C w) left right fields (WindowProvider.literalPorts i)).length≤commonReserve C w)
    (h129 : (fields 95).length≤commonReserve C w)
    (h159 : (fields 125).length≤commonReserve C w) (h176 : (fields 142).length≤commonReserve C w) :
    ∃left' right' fields' extra',
      Step (levelBody WindowProvider.literalProvider WindowProvider.levelProvider)
        (oneLevelFuel (commonReserve C w) (literalDeltaFuel C w) (population+1)
          (prepareBudget (commonReserve C w) root level.val (WindowProvider.levelUniformBudget C w)))
        (levelH (fun _=>0))
        (levelData C (commonReserve C w) (population+1) ci pi level.val left right
          (vectorBank C (commonReserve C w) (NormalizedVector.table (canonicalGradedLabel population active) seed wins 0 done))
          (PacketVector.bank (commonReserve C w) (List.replicate (population+1) [])) fields extra)
        (levelH (fun _=>0))
        (levelData C (commonReserve C w) (population+1) (population+1) (population+1) level.val left' right'
          (vectorBank C (commonReserve C w) (NormalizedVector.table (canonicalGradedLabel population active) seed wins 0 (done+1)))
          (PacketVector.bank (commonReserve C w) (List.replicate (population+1) [])) fields' extra') ∧
      VectorAccumulator.Fits (commonReserve C w) left' ∧ VectorAccumulator.Fits (commonReserve C w) right' ∧
      literalParentInvariant C (commonReserve C w) (canonicalGradedLabel population active) seed wins level
        (fun j=>literalLevelOutput p population C (commonReserve C w) root initial left right fields (j.natAdd 34)) extra fields' extra' := by
  let R:=commonReserve C w
  let label:=canonicalGradedLabel population active
  let ps:=NormalizedVector.table label seed wins 0 done
  let ds:=levelDelta label seed wins level
  let fs:=levelFields R root level.val fields
  let f0 : Fin 222 → List Bool :=fun j=>literalLevelOutput p population C R root initial left right fields (j.natAdd 34)
  let Q:=literalParentInvariant C R label seed wins level f0 extra
  have hpLevel : p.level=level.val := by rw [hp];rfl
  have hpC : p.C=C+9 := by rw [hp];rfl
  have hl : p.level≤p.rank := by rw [hp];exact level.isLt.le.trans hd
  have hlen : ps.length=population+1 := NormalizedVector.table_length label seed wins 0 done
  have reserve : C+2≤R := LiteralCacheReuse.reserve_width C w
  have splitDegree:=level_degree_split wins done d hdone hdegree
  have degree : 2*wins level≤d := by
    have hfin : (⟨depth-(done+1),by omega⟩ : Fin depth)=level := Fin.ext hlevel.symm
    rw [hfin] at splitDegree
    omega
  obtain ⟨_,_,_,_,hpopulation⟩:=literal_delta_guards C w d level wins hpop hcodesC degree hfit
  have prep:= (literal_level_prepare_run p population C w ci pi root old out priv initial hpC hrank hl hC hi
    (by omega) hpriv hout hinit hinits left right (vectorBank C R ps)
    (PacketVector.bank R (List.replicate (population+1) [])) fields extra hright hready
    (by simpa only [hpLevel] using hin) hroot hold htag hmode
    (by rw [WindowProvider.mode_pairs_length];exact aM) abank hprivate h129 h159 h176).1
  rw [hpLevel] at prep
  have fsReady : ProviderReady C R fs := ready_level_fields C R root level.val fields hready
  have htagC : p.level+1≤C := (WindowProvider.mode_pair_guards C population p hrank hl hC).1
  have htwo : 2*population≤C := by
    simpa only [WindowProvider.mode_pairs_length] using (WindowProvider.mode_pair_guards C population p hrank hl hC).2.1
  have resident : LiteralDeltaResident C R (deltaChildCard label seed level) (wins level)
      (deltaLiteralVariableCodes (population:=population) level) f0 := by
    have actual:=WindowProvider.level_output_delta_resident C R population active depth (wins level)
      mask seed level hd initial left right fs (by omega) fsReady
      (by simp only [fs,levelFields,Function.update_self];rfl)
      (by simp only [fs,levelFields,Function.update_of_ne (by decide : (118 : Fin 222)≠153),Function.update_self];rw [hwin];rfl)
      (by simpa [fs,levelFields,Function.update] using au)
      (by simpa [fs,levelFields,Function.update] using aM)
      (by simpa [fs,levelFields,Function.update] using av) (by omega) (by omega)
    dsimp only [f0,literalLevelOutput]
    rw [hpLevel,hp]
    exact actual
  have hq0 : Q f0 extra := ⟨resident,hcold,(by intros;rfl),rfl⟩
  have emptyFits : VectorAccumulator.Fits R [] := by simp [VectorAccumulator.Fits];omega
  let input:=parentA C R ps.length ci 0 level.val left [] [] (vectorBank C R ps)
    (vectorBank C R (parentTable ps.length (parentAnswer ps ds) 0)) f0 extra
  have ready : ParentReady C R level.val ps ds Q 0 input := ⟨ci,left,[],f0,extra,hci,by simp,hleft,emptyFits,hq0,rfl⟩
  have levelEq : (⟨depth-(done+1),by omega⟩ : Fin depth)=level := Fin.ext hlevel.symm
  obtain ⟨output,run,ci',left',right',fields',extra',hci',hciDone,hl',hr',hq',rfl⟩:=
    literal_parents_run C w d done label seed wins hdone hpop hw hcodesC hdegree hfit
      (by simpa only [levelEq] using hW) f0 extra input (by simpa only [levelEq,←hlevel] using ready)
  have ciEq : ci'=population+1 := (hciDone (by omega)).trans hlen
  subst ci'
  have zeroBank : vectorBank C R (parentTable ps.length (parentAnswer ps ds) 0)=
      PacketVector.bank R (List.replicate ps.length []) := by
    rw [parentTable_zero]
    simp only [vectorBank,List.map_replicate]
    rfl
  simp only [input,parentH,parentA,PhysicalAppendAssociativity.double,parentTable_full,levelEq,←hlevel] at run
  rw [zeroBank] at run
  let ns:=List.ofFn (fun i : Fin ps.length=>parentAnswer ps ds i.val)
  have fitP : ∀P∈ps,VectorAccumulator.Fits R (masks C P) :=
    (VectorChildGuardBundle.guards C w d
      (structuralListCoordinateRawDegreeFrom depth wins 0 (depth-done)) (2*wins level)
      (LiteralAlphabet.codes depth population) ps (ds 0)
      (fun j hj=>(LiteralAlphabet.codes_lt_square depth population j hj).trans_le hcodesC)
      (level_table_bounded label seed wins done hdone.le)
      (fun child hc=>level_delta_bounded label seed wins level 0 child (by omega) (by omega))
      (by simpa only [levelEq] using splitDegree) (literal_census depth population d w hfit) (by omega)).packet
  have fitN : ∀P∈ns,VectorAccumulator.Fits R (masks C P) := by
    intro P hP
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hP
    exact (VectorChildGuardBundle.guards C w d
      (structuralListCoordinateRawDegreeFrom depth wins 0 (depth-done)) (2*wins level)
      (LiteralAlphabet.codes depth population) ps (ds i.val)
      (fun j hj=>(LiteralAlphabet.codes_lt_square depth population j hj).trans_le hcodesC)
      (level_table_bounded label seed wins done hdone.le)
      (fun child hc=>level_delta_bounded label seed wins level i.val child (by have h:=i.isLt;omega) (by omega))
      (by simpa only [levelEq] using splitDegree) (literal_census depth population d w hfit) (by omega)).prefixFits ps.length le_rfl
  have fitMap (qs : List (Ring.Poly Nat)) (hf : ∀P∈qs,VectorAccumulator.Fits R (masks C P)) :
      ∀P∈qs.map (masks C),PacketVector.Fits R P := by
    intro P hP
    obtain ⟨T,hT,rfl⟩:=List.mem_map.mp hP
    exact packet_fits R _ (hf T hT)
  have whole:=level_body_run WindowProvider.literalProvider WindowProvider.levelProvider C R ci pi level.val
    (prepareBudget R root level.val (WindowProvider.levelUniformBudget C w)) (allParentsFuel R (literalDeltaFuel C w) ps.length)
    (ps.map (masks C)) (ns.map (masks C)) left right left [] left' right' fields f0 fields' extra extra extra'
    (by simp only [List.length_map,ns,List.length_ofFn]) (by omega) hpi (fitMap ps fitP) (fitMap ns fitN)
    (by simpa only [List.length_map,vectorBank,hlen] using prep)
    (by simpa only [List.length_map,vectorBank,levelData,levelH,ns,R,hlen,NormalizedVector.table_length,parentTable_full,Fin.val_cast,PhysicalAppendAssociativity.double] using run)
  have next : ns=NormalizedVector.table label seed wins 0 (done+1) := by
    dsimp only [ns,ds]
    rw [parent_level_exact label seed wins level ps hlen]
    rw [NormalizedVector.table,dif_pos hdone]
    simp only [levelEq]
    rfl
  refine ⟨left',right',fields',extra',?_,hl',hr',?_⟩
  · simpa only [List.length_map,vectorBank,oneLevelFuel,hlen,next] using whole
  · simpa only [levelEq,←hlevel] using hq'

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
