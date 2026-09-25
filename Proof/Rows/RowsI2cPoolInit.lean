import Proof.Rows.RowsI2cPoolShape

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

section
/- Copied from source-reuse-20260922/PCJ6e421fabe2aa4155_SourcePoolBank.lean (namespace renamed; see module header). -/
namespace RowsConstruction.I2c.PoolBank
open NearCubicWires LocalBitMultitape ExtDecompositionBatch ExtIncidence RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound P1Closure RepairSource RepairSource.VerifierDecoding
open RowsConstruction.I2c.PoolSeedFanout (pad_pad)
noncomputable section

def data {q : Nat} (live : Finset (Fin q)) (B N : Nat) (source : List Bool) : Fin 9→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool)
    (RowsConstruction.I2c.PoolSeedFanout.masters live (B+q+1))
    (![List.replicate (PoolEntry.reserve B q (B+q+1)) true,source,natWord (2*N),CompareMachine.word N])
def lift (o : Option (Fin 5)) : Option (Fin 9):=o.map (fun i=>i.castAdd 4)
def child (i : Fin 64) : Option (Fin 9):=
  if i=61 then some 7 else lift (RowsConstruction.I2c.PoolSeedFanout.select i)
def select : Fin 132→Option (Fin 9):=
  Fin.addCases (motive:=fun _=>Option (Fin 9))
    (Fin.addCases (motive:=fun _=>Option (Fin 9))
      (Fin.addCases (motive:=fun _=>Option (Fin 9)) child
        (Fin.addCases (motive:=fun _=>Option (Fin 9))
          (fun j : Fin 62=>lift (RowsConstruction.I2c.PoolSeedFanout.select (PoolEntryRestore.work j)))
          (![none,some 5,none] : Fin 3→Option (Fin 9))))
      (![some 6,none] : Fin 2→Option (Fin 9))) (fun _ : Fin 1=>some 8)

def prefixWord (N : Nat):=natWord (2*N)++RepairOrdinary.frame []
def startBank {q : Nat} (live : Finset (Fin q)) (B N : Nat) (source : List Bool) : Fin 132→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool)
    (PoolEntryOccurrence.bank live B (B+q+1) source
      (List.replicate (PoolEntry.reserve B q (B+q+1)) false) (prefixWord N))
    (fun _ : Fin 1=>CompareMachine.word N)

theorem word_lift {q : Nat} (live : Finset (Fin q)) (B N : Nat) (source : List Bool) (o : Option (Fin 5)) :
    (lift o).elim [] (data live B N source)=
    o.elim [] (RowsConstruction.I2c.PoolSeedFanout.masters live (B+q+1)) := by
  cases o <;>simp only [lift,Option.map_none,Option.map_some,Option.elim_none,Option.elim_some,data,Fin.addCases_left]

theorem pad_append_false (P : Nat) (bits : List Bool) (h:bits.length+1≤P) :
    ZeroPadding.pad P (bits++[false])=ZeroPadding.pad P bits := by
  have he:ZeroPadding.pad (bits.length+1) bits=bits++[false]:=by simp [ZeroPadding.pad]
  rw [←he];exact pad_pad _ _ _ h

theorem prefix_bound (B q N : Nat) (hn:N≤B) :
    (natWord (2*N)).length+1≤RowsConstruction.I2c.PoolCapacity.value B q := by
  have hp:=RowsConstruction.I2c.PoolCapacity.arithmetic N B q hn
  have hb:natBitLength (2*N)≤2*N+1:=Nat.add_le_add_right (Nat.log_le_self 2 (2*N)) 1
  rw [DecompositionSource.natWord_length]
  omega

attribute [local irreducible] PoolEntry.input

theorem bank_at {q : Nat} (live : Finset (Fin q)) (B w : Nat) (framed out : List Bool) (i : Fin 64) :
    PoolEntryBaseline.bank live B w framed out i=
    if i=55 then framed else if i=61 then out else RowsConstruction.I2c.PoolSeedShape.table live B w i := by
  by_cases h:i=55
  · subst i;rw [PoolEntryBaseline.bank_source,if_pos rfl]
  rw [if_neg h]
  by_cases ho:i=61
  · subst i;rw [PoolEntryBaseline.bank_output,if_pos rfl]
  rw [if_neg ho,PoolEntryBaseline.bank_outside _ _ _ _ _ _ ho]
  have he:PoolEntryBaseline.bank live B w framed [] i=PoolEntryBaseline.bank live B w [] [] i:=by
    simp only [PoolEntryBaseline.bank,Function.update_of_ne h]
  rw [he,RowsConstruction.I2c.PoolSeedShape.bank_eq]

theorem child_scalar {q : Nat} (live : Finset (Fin q)) (B N P S : Nat) (source : List Bool)
    (hs:S≤P) (hp:(natWord (2*N)).length+1≤P)
    (hc:ConstantGateReusable.C (B+q+1)+1≤P) (he:ConstantGateReusable.E B q≤P)
    (hl:PoolEntry.logCapacity B q≤P) (i : Fin 64) :
    ZeroPadding.pad (P)
      (ZeroPadding.pad (PoolEntryRestore.caps (S) i)
        (if i=55 then List.replicate (S) false else
          if i=61 then prefixWord N else RowsConstruction.I2c.PoolSeedShape.table live B (B+q+1) i))=
    ZeroPadding.pad (P)
      ((child i).elim [] (data live B N source)) := by
  by_cases ho:i=61
  · subst i
    rw [if_neg (by decide : (61 : Fin 64)≠55),if_pos rfl]
    change ZeroPadding.pad P (ZeroPadding.pad 0 (prefixWord N))=ZeroPadding.pad P (natWord (2*N))
    rw [ZeroPadding.pad_zero]
    exact pad_append_false P _ hp
  by_cases hi:i=55
  · subst i
    rw [if_pos rfl]
    change ZeroPadding.pad P (ZeroPadding.pad 0 (List.replicate (S) false))=ZeroPadding.pad P []
    rw [ZeroPadding.pad_zero]
    exact pad_replicate_false _ _ hs
  rw [if_neg hi,if_neg ho,PoolEntryRestore.caps,if_neg (not_or_intro ho hi),pad_pad _ _ _ hs]
  rw [child,if_neg ho,word_lift]
  exact RowsConstruction.I2c.PoolSeedFanout.padded_table live B (B+q+1) P
    hc he hl i

theorem child_padded {q : Nat} (live : Finset (Fin q)) (B N P : Nat) (source : List Bool)
    (hs:PoolEntry.reserve B q (B+q+1)≤P) (hp:(natWord (2*N)).length+1≤P)
    (hc:ConstantGateReusable.C (B+q+1)+1≤P) (he:ConstantGateReusable.E B q≤P)
    (hl:PoolEntry.logCapacity B q≤P) (i : Fin 64) :
    ZeroPadding.pad (P)
      (PoolEntryRestore.padded (PoolEntryBaseline.bank live B (B+q+1)
        (List.replicate (PoolEntry.reserve B q (B+q+1)) false)) (prefixWord N)
        (PoolEntry.reserve B q (B+q+1)) i)=
    ZeroPadding.pad (P)
      ((child i).elim [] (data live B N source)) := by
  rw [PoolEntryRestore.padded,bank_at]
  exact child_scalar live B N P _ source hs hp hc he hl i

theorem start_padded {q : Nat} (live : Finset (Fin q)) (B N P : Nat) (source : List Bool)
    (hs:PoolEntry.reserve B q (B+q+1)+1≤P) (hp:(natWord (2*N)).length+1≤P)
    (hc:ConstantGateReusable.C (B+q+1)+1≤P) (he:ConstantGateReusable.E B q≤P)
    (hl:PoolEntry.logCapacity B q≤P) (i : Fin 132) :
    ZeroPadding.pad (P) (startBank live B N source i)=
    ZeroPadding.pad (P)
      (NativeFanout.word select (data live B N source) i) := by
  simp only [startBank,PoolEntryOccurrence.bank,PoolEntryBaseline.state,
    PoolEntryRestore.input,PoolEntryRestore.state,NativeFanout.word,select]
  refine Fin.addCases (m:=131) (n:=1) (fun j=>?_) (fun j=>?_) i <;>
    simp only [Fin.addCases_left,Fin.addCases_right]
  · refine Fin.addCases (m:=129) (n:=2) (fun j=>?_) (fun j=>?_) j
    · simp only [Fin.addCases_left]
      refine Fin.addCases (m:=64) (n:=65) (fun j=>?_) (fun j=>?_) j <;>
        simp only [Fin.addCases_left,Fin.addCases_right]
      · exact child_padded live B N P source (by omega) hp hc he hl j
      · refine Fin.addCases (m:=62) (n:=3) (fun j=>?_) (fun j=>?_) j <;>
          simp only [Fin.addCases_left,Fin.addCases_right]
        · change ZeroPadding.pad _ (PoolEntryBaseline.bank live B (B+q+1)
            (List.replicate (PoolEntry.reserve B q (B+q+1)) false) [] (PoolEntryRestore.work j))=
            ZeroPadding.pad _ ((lift _).elim [] (data live B N source))
          have hj:PoolEntryRestore.work j≠55:=by fin_cases j <;>decide
          have he:PoolEntryBaseline.bank live B (B+q+1)
              (List.replicate (PoolEntry.reserve B q (B+q+1)) false) [] (PoolEntryRestore.work j)=
              PoolEntryBaseline.bank live B (B+q+1) [] [] (PoolEntryRestore.work j):=by
            simp only [PoolEntryBaseline.bank,Function.update_of_ne hj]
          rw [he,RowsConstruction.I2c.PoolSeedShape.bank_eq,word_lift]
          exact RowsConstruction.I2c.PoolSeedFanout.padded_table live B _ P hc ‹ConstantGateReusable.E B q≤P› hl _
        · fin_cases j
          · exact pad_replicate_false _ _ (by omega)
          · rfl
          · exact pad_replicate_false _ _ hs
    · simp only [Fin.addCases_right]
      fin_cases j
      · rfl
      · exact pad_replicate_false _ _ (by omega)
  · rfl

theorem actual_start_padded {q : Nat} (live : Finset (Fin q)) (B N : Nat) (source : List Bool)
    (hn:N≤B) (i : Fin 132) :
    ZeroPadding.pad (RowsConstruction.I2c.PoolCapacity.value B q) (startBank live B N source i)=
    ZeroPadding.pad (RowsConstruction.I2c.PoolCapacity.value B q)
      (NativeFanout.word select (data live B N source) i) :=
  start_padded live B N _ source (RowsConstruction.I2c.PoolCapacity.small_bounds B q).2.1
    (prefix_bound B q N hn) (RowsConstruction.I2c.PoolSeedFanout.scalar_bounds B q).1
    (RowsConstruction.I2c.PoolSeedFanout.scalar_bounds B q).2.1
    (RowsConstruction.I2c.PoolSeedFanout.scalar_bounds B q).2.2 i

end
end RowsConstruction.I2c.PoolBank
end

section
/- Copied from source-reuse-20260922/PCJ6e421fabe2aa4155_SourcePoolAllocate.lean (namespace renamed; see module header). -/
namespace RowsConstruction.I2c.PoolAllocate
open NearCubicWires LocalBitMultitape ExtDecompositionBatch ExtIncidence RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound P1Closure RepairSource RepairSource.VerifierDecoding
open RowsConstruction.I2c.PoolBank
noncomputable section

def worker (i : Fin 132) : Fin 143:=((i.castAdd 1).natAdd 9).castAdd 1
def machine:=NativeFanout.machine select

theorem fits {q : Nat} (live : Finset (Fin q)) (B N : Nat) (source : List Bool)
    (hn:N≤B) (hs:source.length≤RowsConstruction.I2c.PoolCapacity.value B q) :
    ∀i,(data live B N source i).length≤RowsConstruction.I2c.PoolCapacity.value B q := by
  have small:=RowsConstruction.I2c.PoolCapacity.small_bounds B q
  have scalars:=RowsConstruction.I2c.PoolSeedFanout.scalar_bounds B q
  have hC:ConstantGateReusable.C (B+q+1)=8*(B+q+1)+12:=rfl
  intro i
  refine Fin.addCases (m:=5) (n:=4) (fun j=>?_) (fun j=>?_) i
  · fin_cases j
    · change (List.replicate (B+q+1) true).length≤_
      rw [List.length_replicate];omega
    · change (RepairOrdinary.frame (SignedSortKey.binary (B+q+1) 0)).length≤_
      rw [frame_length,SignedSortKey.binary_length];omega
    · change (CloseoutRowsGateSupport.gateMembers live).length≤_
      rw [CloseoutRowsGateSupport.gateMembers,List.length_ofFn];omega
    · change (List.replicate (ConstantGateReusable.C (B+q+1)) true).length≤_
      rw [List.length_replicate];omega
    · change (CompareMachine.word q).length≤_
      simp only [CompareMachine.word,List.length_cons,List.length_replicate];omega
  · fin_cases j
    · change (List.replicate (PoolEntry.reserve B q (B+q+1)) true).length≤_
      rw [List.length_replicate];omega
    · exact hs
    · have h:=prefix_bound B q N hn
      change (natWord (2*N)).length≤_
      omega
    · change (CompareMachine.word N).length≤_
      simp only [CompareMachine.word,List.length_cons,List.length_replicate];omega

end
end RowsConstruction.I2c.PoolAllocate
end

section
/- Copied from source-reuse-20260922/PCJ6e421fabe2aa4155_SourcePoolBoot.lean (namespace renamed; see module header). -/
namespace RowsConstruction.I2c.PoolBoot
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound RepairSource.VerifierDecoding
noncomputable section

theorem skip_step (n : Nat) (tail : List Bool) :
    Step (PCPPQueryField.machine false) (2*natBitLength n+3)
      (fun _=>0) ![natWord n++tail,[],[]] (![(natWord n).length,0,0])
      ![natWord n++tail,PCPPQueryField.saved n [],[]] := by
  obtain ⟨f,hf,ff,_⟩:=PCPPQueryField.nat_run false [] tail [] [] n
  apply ((Step.of_run hf (congrArg Configuration.heads ff) (congrArg Configuration.tapes ff)).congr_in ?_ ?_).congr ?_ ?_
  all_goals funext i;fin_cases i <;>simp [PCPPQueryField.cfg,PCPPQueryField.payload,
    PCPPQueryField.selected,PCPPQueryField.saved,DecompositionSource.natWord_length]

def slots : Fin 3→Fin 134:=![61,132,133]
def scan:=RecoveryFocus.machine slots (PCPPQueryField.machine false)
def directions (i : Fin 134) : HeadMove:=if i=61 ∨ i=131 then .right else .stay
def finish:=DecompositionCountPosition.move directions
def machine:=Composition.machine scan finish
def heads (N : Nat) (i : Fin 134):=if i=61 then (natWord (2*N)).length+1 else if i=131 then 1 else 0

theorem run (N P : Nat) (A : Fin 134→List Bool)
    (h61:A 61=ZeroPadding.pad P (natWord (2*N))) (h132:A 132=[]) (h133:A 133=[]) :
    ∃ F,Step machine (2*natBitLength (2*N)+5) (fun _=>0) A (heads N) F ∧
      ∀i : Fin 134,i≠132→F i=A i := by
  let tail:=List.replicate (P-(natWord (2*N)).length) false
  let words : Fin 3→List Bool:=![natWord (2*N)++tail,PCPPQueryField.saved (2*N) [],[]]
  let H:=dockH slots (fun _=>0) (![(natWord (2*N)).length,0,0])
  let F:=install slots A words
  have first:= (skip_step (2*N) tail).dock slots (by decide) (fun _=>0) A
    (by intro i;fin_cases i <;>rfl) (by
      intro i;fin_cases i
      · exact h61
      · exact h132
      · exact h133)
  obtain ⟨r,hr,hf,_⟩:=DecompositionCountPosition.move_run directions H F
  have last:Step finish 1 H F (heads N) F:=Step.of_run hr (by
    rw [hf]
    funext i
    have hi:∀i : Fin 134,(∀j,slots j≠i)→H i=0:=by
      intro i h;exact dockH_other slots _ _ i h
    by_cases h:i=61
    · subst i
      have he:H 61=(natWord (2*N)).length:=dockH_slot slots (by decide) _ _ 0
      simp only [directions,heads,ite_true,true_or,he,HeadMove.apply]
    by_cases h':i=131
    · subst i
      have he:H 131=0:=hi _ (by decide)
      simp only [directions,heads,if_neg h,or_true,ite_true,he,HeadMove.apply]
    have he:H i=0:=by
      by_cases h132':i=132
      · subst i;exact dockH_slot slots (by decide) _ _ 1
      by_cases h133':i=133
      · subst i;exact dockH_slot slots (by decide) _ _ 2
      exact hi i (by intro j;fin_cases j <;>first | exact Ne.symm h | exact Ne.symm h132' | exact Ne.symm h133')
    simp only [directions,heads,if_neg h,if_neg h',if_neg (not_or_intro h h'),he,HeadMove.apply])
    (by rw [hf])
  refine ⟨F,first.seq last,?_⟩
  intro i hi
  by_cases h:i=61
  · subst i;exact (install_slot slots (by decide) A words 0).trans h61.symm
  by_cases h':i=133
  · subst i;exact (install_slot slots (by decide) A words 2).trans h133.symm
  exact install_other slots A words i (by intro j;fin_cases j <;>first | exact Ne.symm h | exact Ne.symm hi | exact Ne.symm h')

end
end RowsConstruction.I2c.PoolBoot
end

section
/- Copied from source-reuse-20260922/PCJ6e421fabe2aa4155_SourcePoolInitialize.lean (namespace renamed; see module header). -/
namespace RowsConstruction.I2c.PoolInitialize
open NearCubicWires LocalBitMultitape ExtDecompositionBatch ExtIncidence RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound P1Closure RepairSource RepairSource.VerifierDecoding
open RowsConstruction.I2c.PoolBank
noncomputable section

def worker (i : Fin 132) : Fin 145:=(RowsConstruction.I2c.PoolAllocate.worker i).castAdd 2
def bootSlots : Fin 134→Fin 145:=Fin.addCases (motive:=fun _=>Fin 145) worker (fun j : Fin 2=>j.natAdd 143)
theorem boot_inj : Function.Injective bootSlots:=by decide
def first:=TapeEmbedding.machine 2 RowsConstruction.I2c.PoolAllocate.machine
def boot:=RecoveryFocus.machine bootSlots RowsConstruction.I2c.PoolBoot.machine
def machine:=Composition.machine first boot
def input {q : Nat} (live : Finset (Fin q)) (B N : Nat) (source : List Bool) : Fin 145→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool)
    (NativeFanout.input (m:=132) (data live B N source) (RowsConstruction.I2c.PoolCapacity.value B q))
    (fun _ : Fin 2=>[])
def budget (B q N : Nat):=(2*RowsConstruction.I2c.PoolCapacity.value B q+4)+1+(2*natBitLength (2*N)+5)
def head (N : Nat) (i : Fin 132):=if i=61 then (prefixWord N).length else if i=131 then 1 else 0

theorem run {q : Nat} (live : Finset (Fin q)) (B N : Nat) (source : List Bool)
    (hn:N≤B) (hs:source.length≤RowsConstruction.I2c.PoolCapacity.value B q) :
    ∃ H A,Step machine (budget B q N) (fun _=>0) (input live B N source) H A ∧
      (∀i,H (worker i)=head N i) ∧
      (∀i,A (worker i)=ZeroPadding.pad (RowsConstruction.I2c.PoolCapacity.value B q) (startBank live B N source i)) := by
  let P:=RowsConstruction.I2c.PoolCapacity.value B q
  let D:=data live B N source
  let V:=NativeFanout.output select D P
  have hV:=Step.of_ready (NativeFanout.ready select D P (RowsConstruction.I2c.PoolAllocate.fits live B N source hn hs))
  let A0 : Fin 145→List Bool:=Fin.addCases (motive:=fun _=>List Bool) V (fun _ : Fin 2=>[])
  have hz:(Fin.addCases (motive:=fun _ : Fin 145=>Nat) (fun _ : Fin 143=>0) (fun _ : Fin 2=>0))=(fun _=>0):=by
    funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]
  have hf:Step first (2*P+4) (fun _=>0) (input live B N source) (fun _=>0) A0:=
    ((hV.embed (fun _ : Fin 2=>0) (fun _=>[])).congr_in hz rfl).congr hz rfl
  let localBank:=fun i=>A0 (bootSlots i)
  have h61:localBank 61=ZeroPadding.pad P (natWord (2*N)):=rfl
  have h132:localBank 132=[]:=rfl
  have h133:localBank 133=[]:=rfl
  obtain ⟨F,hb,keep⟩:=RowsConstruction.I2c.PoolBoot.run N P localBank h61 h132 h133
  have hb':=hb.dock bootSlots boot_inj (fun _=>0) A0 (by intro i;rfl) (by intro i;rfl)
  refine ⟨_,_,hf.seq hb',?_,?_⟩
  · intro i
    have h:bootSlots (i.castAdd 2)=worker i:=by simp only [bootSlots,Fin.addCases_left]
    rw [←h,dockH_slot bootSlots boot_inj]
    unfold RowsConstruction.I2c.PoolBoot.heads head
    have h61':(i.castAdd 2 : Fin 134)=61↔i=61:=by constructor <;>intro h <;>have hv:=congrArg Fin.val h <;>exact Fin.ext hv
    have h131':(i.castAdd 2 : Fin 134)=131↔i=131:=by constructor <;>intro h <;>have hv:=congrArg Fin.val h <;>exact Fin.ext hv
    simp only [h61',h131']
    by_cases hi:i=61
    · rw [if_pos hi,if_pos hi];simp [prefixWord,frame_length]
    · rw [if_neg hi,if_neg hi]
  · intro i
    have h:bootSlots (i.castAdd 2)=worker i:=by simp only [bootSlots,Fin.addCases_left]
    have hk:F (i.castAdd 2)=localBank (i.castAdd 2):=keep (i.castAdd 2) (by
      intro he
      have hv:i.val=132:=congrArg Fin.val he
      have hi:=i.isLt
      omega)
    have heq:install bootSlots A0 F (worker i)=F (i.castAdd 2):=by
      rw [←h];exact install_slot bootSlots boot_inj A0 F (i.castAdd 2)
    rw [heq,hk]
    change A0 (bootSlots (i.castAdd 2))=_
    rw [h]
    simp only [A0,worker,Fin.addCases_left,V,NativeFanout.output,RowsConstruction.I2c.PoolAllocate.worker,Fin.addCases_right]
    exact (actual_start_padded live B N source hn i).symm

end
end RowsConstruction.I2c.PoolInitialize
end

section
/- Copied from source-reuse-20260922/PCJ6e421fabe2aa4155_SourcePoolMasters.lean (namespace renamed; see module header). -/
namespace RowsConstruction.I2c.PoolMasters
open NearCubicWires LocalBitMultitape ExtDecompositionBatch ExtIncidence RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound P1Closure RepairSource RepairSource.VerifierDecoding
open RowsConstruction.I2c.Log (dock_zero)
noncomputable section

def extra {q : Nat} (live : Finset (Fin q)) (N : Nat) (source : List Bool) (i : Fin 22) : List Bool:=
  if i=0 then CompareMachine.word N else if i=1 then CloseoutRowsGateSupport.gateMembers live else if i=2 then source else []
def input {q : Nat} (live : Finset (Fin q)) (B N : Nat) (source : List Bool) : Fin 84→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool) (RowsConstruction.I2c.PoolPreparation.input q B) (extra live N source)
def headerSlots (i : Fin 20) : Fin 84:=if i=0 then 62 else ⟨i.val+64,by omega⟩
theorem header_inj : Function.Injective headerSlots:=by decide
def fields : Fin 9→Fin 84:=![8,39,63,36,0,17,64,82,62]
def first:=TapeEmbedding.machine 22 RowsConstruction.I2c.PoolPreparation.machine
def last:=RecoveryFocus.machine headerSlots RowsConstruction.I2c.PoolHeader.machine
def machine:=Composition.machine first last
def budget (B q N : Nat):=RowsConstruction.I2c.PoolPreparation.budget q B+1+
  RowsConstruction.I2c.PoolHeader.budget N

theorem run {q : Nat} (live : Finset (Fin q)) (B N : Nat) (source : List Bool) :
    ∃ A,Step machine (budget B q N) (fun _=>0) (input live B N source) (fun _=>0) A ∧
      (∀i,A (fields i)=RowsConstruction.I2c.PoolBank.data live B N source i) ∧
      A 51=List.replicate (RowsConstruction.I2c.PoolCapacity.value B q) true := by
  obtain ⟨D,hd,d0,_d1,_d6,d8,d36,d39,d17,d51⟩:=RowsConstruction.I2c.PoolPreparation.run q B
  let A0 : Fin 84→List Bool:=Fin.addCases (motive:=fun _=>List Bool) D (extra live N source)
  have hz:(Fin.addCases (motive:=fun _ : Fin 84=>Nat) (fun _ : Fin 62=>0) (fun _ : Fin 22=>0))=(fun _=>0):=by
    funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]
  have hfirst:Step first _ (fun _=>0) (input live B N source) (fun _=>0) A0:=
    ((hd.embed (fun _ : Fin 22=>0) (extra live N source)).congr_in hz rfl).congr hz rfl
  obtain ⟨H,hh,h0,h18⟩:=RowsConstruction.I2c.PoolHeader.run N
  have selected:∀i,A0 (headerSlots i)=RowsConstruction.I2c.PoolHeader.input N i:=by
    intro i;by_cases hi:i=0
    · subst i;rfl
    rw [headerSlots,if_neg hi]
    have he:(⟨i.val+64,by omega⟩ : Fin 84)=(⟨i.val+2,by omega⟩ : Fin 22).natAdd 62:=Fin.ext (by simp;omega)
    rw [he]
    simp only [A0,Fin.addCases_right]
    have hn:i.val≠0:=by intro h;exact hi (Fin.ext h)
    have h0':(⟨i.val+2,by omega⟩ : Fin 22)≠0:=by intro h;have hv:=congrArg Fin.val h;dsimp at hv;omega
    have h1':(⟨i.val+2,by omega⟩ : Fin 22)≠1:=by intro h;have hv:=congrArg Fin.val h;dsimp at hv;omega
    have h2':(⟨i.val+2,by omega⟩ : Fin 22)≠2:=by intro h;have hv:=congrArg Fin.val h;dsimp at hv;omega
    simp only [extra,if_neg h0',if_neg h1',if_neg h2',RowsConstruction.I2c.PoolHeader.input,if_neg hi]
  have hlast:=dock_zero hh headerSlots header_inj A0 selected
  refine ⟨_,hfirst.seq hlast,?_,?_⟩
  · intro i;fin_cases i
    · exact (install_other headerSlots A0 H 8 (by decide)).trans d8
    · exact (install_other headerSlots A0 H 39 (by decide)).trans d39
    · exact install_other headerSlots A0 H 63 (by decide)
    · exact (install_other headerSlots A0 H 36 (by decide)).trans d36
    · exact (install_other headerSlots A0 H 0 (by decide)).trans d0
    · exact (install_other headerSlots A0 H 17 (by decide)).trans d17
    · exact install_other headerSlots A0 H 64 (by decide)
    · exact (install_slot headerSlots header_inj A0 H 18).trans h18
    · exact (install_slot headerSlots header_inj A0 H 0).trans h0
  · exact (install_other headerSlots A0 H 51 (by decide)).trans d51

end
end RowsConstruction.I2c.PoolMasters
end

section
/- Copied from source-reuse-20260922/PCJ6e421fabe2aa4155_SourcePoolProduced.lean (namespace renamed; see module header). -/
namespace RowsConstruction.I2c.PoolProduced
open NearCubicWires LocalBitMultitape ExtDecompositionBatch ExtIncidence RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound P1Closure RepairSource RepairSource.VerifierDecoding
noncomputable section

def slots (i : Fin 145) : Fin 229:=if h:i.val<9 then
  (RowsConstruction.I2c.PoolMasters.fields ⟨i.val,h⟩).castAdd 145
  else if i=141 then 51 else i.natAdd 84
theorem slots_inj : Function.Injective slots:=by decide
def first:=TapeEmbedding.machine 145 RowsConstruction.I2c.PoolMasters.machine
def last:=RecoveryFocus.machine slots RowsConstruction.I2c.PoolInitialize.machine
def machine:=Composition.machine first last
def input {q : Nat} (live : Finset (Fin q)) (B N : Nat) (source : List Bool) : Fin 229→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool) (RowsConstruction.I2c.PoolMasters.input live B N source) (fun _ : Fin 145=>[])
def budget (B q N : Nat):=RowsConstruction.I2c.PoolMasters.budget B q N+1+
  RowsConstruction.I2c.PoolInitialize.budget B q N

theorem input_shape (D : Fin 9→List Bool) (P : Nat) (i : Fin 145) :
    Fin.addCases (motive:=fun _=>List Bool) (NativeFanout.input (m:=132) D P) (fun _ : Fin 2=>[]) i=
    if h:i.val<9 then D ⟨i.val,h⟩ else if i=141 then List.replicate P true else [] := by
  fin_cases i <;>rfl

theorem run {q : Nat} (live : Finset (Fin q)) (B N : Nat) (source : List Bool)
    (hn:N≤B) (hs:source.length≤RowsConstruction.I2c.PoolCapacity.value B q) :
    ∃ H A,Step machine (budget B q N) (fun _=>0) (input live B N source) H A ∧
      (∀i,H (slots (RowsConstruction.I2c.PoolInitialize.worker i))=
        RowsConstruction.I2c.PoolInitialize.head N i) ∧
      (∀i,A (slots (RowsConstruction.I2c.PoolInitialize.worker i))=
        ZeroPadding.pad (RowsConstruction.I2c.PoolCapacity.value B q)
          (RowsConstruction.I2c.PoolBank.startBank live B N source i)) := by
  obtain ⟨D,hd,fields,hP⟩:=RowsConstruction.I2c.PoolMasters.run live B N source
  let A0 : Fin 229→List Bool:=Fin.addCases (motive:=fun _=>List Bool) D (fun _ : Fin 145=>[])
  have hz:(Fin.addCases (motive:=fun _ : Fin 229=>Nat) (fun _ : Fin 84=>0) (fun _ : Fin 145=>0))=(fun _=>0):=by
    funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]
  have hf:Step first _ (fun _=>0) (input live B N source) (fun _=>0) A0:=
    ((hd.embed (fun _ : Fin 145=>0) (fun _=>[])).congr_in hz rfl).congr hz rfl
  obtain ⟨H,F,hi,fh,fw⟩:=RowsConstruction.I2c.PoolInitialize.run live B N source hn hs
  have selected:∀i,A0 (slots i)=RowsConstruction.I2c.PoolInitialize.input live B N source i:=by
    intro i
    rw [RowsConstruction.I2c.PoolInitialize.input,input_shape]
    by_cases h:i.val<9
    · rw [slots,dif_pos h,dif_pos h]
      simp only [A0,Fin.addCases_left]
      exact fields ⟨i.val,h⟩
    rw [slots,dif_neg h,dif_neg h]
    by_cases hi:i=141
    · subst i;rw [if_pos rfl,if_pos rfl];exact hP
    rw [if_neg hi,if_neg hi]
    simp only [A0,Fin.addCases_right]
  have hl:=hi.dock slots slots_inj (fun _=>0) A0 (by intro i;rfl) selected
  refine ⟨_,_,hf.seq hl,?_,?_⟩
  · intro i;exact (dockH_slot slots slots_inj _ _ _).trans (fh i)
  · intro i;exact (install_slot slots slots_inj _ _ _).trans (fw i)

end
end RowsConstruction.I2c.PoolProduced
end

