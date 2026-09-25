import Proof.SourceAssembly.SourceRequestSelKeptS
import Proof.SourceAssembly.SourceRequestSelDistinct
import Proof.SourceAssembly.SourceSkelKeptW2

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
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.Rest
open NearCubicWires.SourceRequest.SelLocal (resW resWS)
open NearCubicWires.SourceRequest.CurContract (curBig rhoW)
open NearCubicWires.SourceRequest.TermReader (rawTerms)
open NearCubicWires.SourceRequest.LitInfo (litCost)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
open NearCubicWires.RepairRepresentation (PCPPRequest PointwisePCPPAlgorithm pcppOutput)
open NearCubicWires.SourceRequest.SelLocal (resW resWS)
open NearCubicWires.SourceRequest.CurContract (curBig rhoW)
open NearCubicWires.SourceRequest.TermReader (rawTerms)
open NearCubicWires.SourceRequest.LitInfo (litCost)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
open NearCubicWires.RepairRepresentation (PCPPRequest PointwisePCPPAlgorithm pcppOutput)
namespace NearCubicWires.SourceRequest.SelKeptSite
noncomputable section

section site
variable (selector : CyclicChoice.Laws) (xtra : NearCubicWires.SourceSkeleton.Fill.XtraW selector) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)

set_option hygiene false in
local notation "𝔡" => NearCubicWires.SourceSkeleton.FirstW.dSite selector xtra mask packets rows sources gamma hg hh p

theorem kept_site (V : Nat) (hV : (𝔡).U ≤ V) (mode : Bool) (bits qW : List Bool) (cdW : Fin 19 → List Bool)
    (Rc q L CP DP CW DW CL DL tg DD CD Dcw Ccw b : Nat) (MB : List Bool) (Vv NC : Nat) :
    (∀ j, (NearCubicWires.SourceSkeleton.KeptW.KSite selector xtra mask packets rows sources gamma hg hh p V hV mode) (NearCubicWires.SourceSkeleton.FirstW.cacheSite selector xtra mask packets rows sources gamma hg hh p V hV mode j) ∧
      (NearCubicWires.SourceSkeleton.KeptW.K0Site selector xtra mask packets rows sources gamma hg hh p V hV mode (RepairOrdinary.frame bits) qW cdW
      (NearCubicWires.SourceSkeleton.InitS.initResVal Rc q L CP DP CW DW CL DL mode tg
        (NearCubicWires.SourceSkeleton.InitS.valAllX mode L q Rc DD CD Dcw Ccw CL DL b MB)) Vv NC) (NearCubicWires.SourceSkeleton.FirstW.cacheSite selector xtra mask packets rows sources gamma hg hh p V hV mode j) = cdW j ∧ (fun _ : Fin V => (0 : Nat)) (NearCubicWires.SourceSkeleton.FirstW.cacheSite selector xtra mask packets rows sources gamma hg hh p V hV mode j) = 0) ∧
    (∀ x : Fin V, x.val = 1 → (NearCubicWires.SourceSkeleton.KeptW.KSite selector xtra mask packets rows sources gamma hg hh p V hV mode) x ∧ (NearCubicWires.SourceSkeleton.KeptW.K0Site selector xtra mask packets rows sources gamma hg hh p V hV mode (RepairOrdinary.frame bits) qW cdW
      (NearCubicWires.SourceSkeleton.InitS.initResVal Rc q L CP DP CW DW CL DL mode tg
        (NearCubicWires.SourceSkeleton.InitS.valAllX mode L q Rc DD CD Dcw Ccw CL DL b MB)) Vv NC) x = RepairOrdinary.frame bits ∧ (fun _ : Fin V => (0 : Nat)) x = 0) ∧
    (∀ i, i < 10 → ∀ x : Fin V, x.val = (𝔡).B + 29 + restPc (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).se.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).sp.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).gW + i →
      (NearCubicWires.SourceSkeleton.KeptW.KSite selector xtra mask packets rows sources gamma hg hh p V hV mode) x ∧ (NearCubicWires.SourceSkeleton.KeptW.K0Site selector xtra mask packets rows sources gamma hg hh p V hV mode (RepairOrdinary.frame bits) qW cdW
      (NearCubicWires.SourceSkeleton.InitS.initResVal Rc q L CP DP CW DW CL DL mode tg
        (NearCubicWires.SourceSkeleton.InitS.valAllX mode L q Rc DD CD Dcw Ccw CL DL b MB)) Vv NC) x = ZeroPadding.pad Rc ((if mode then SelLocal.resWS else SelLocal.resW) q (CP*(q+1)^DP) (CW*(q+1)^DW) (CL*(q+1)^DL) L tg
        (NearCubicWires.SourceSkeleton.InitS.cwidOf mode (CL*(q+1)^DL)) (Ccw*(q+1)^Dcw) i) ∧ (fun _ : Fin V => (0 : Nat)) x = 0) ∧
    (∀ x : Fin V, x.val = (𝔡).B + 41 + restPc (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).se.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).sp.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).gW →
      (NearCubicWires.SourceSkeleton.KeptW.KSite selector xtra mask packets rows sources gamma hg hh p V hV mode) x ∧ (NearCubicWires.SourceSkeleton.KeptW.K0Site selector xtra mask packets rows sources gamma hg hh p V hV mode (RepairOrdinary.frame bits) qW cdW
      (NearCubicWires.SourceSkeleton.InitS.initResVal Rc q L CP DP CW DW CL DL mode tg
        (NearCubicWires.SourceSkeleton.InitS.valAllX mode L q Rc DD CD Dcw Ccw CL DL b MB)) Vv NC) x = ZeroPadding.pad Rc (List.replicate (CD*(q+1)^DD) true) ∧ (fun _ : Fin V => (0 : Nat)) x = 0) ∧
    ((NearCubicWires.SourceSkeleton.KeptW.KSite selector xtra mask packets rows sources gamma hg hh p V hV mode) (NearCubicWires.SourceSkeleton.FirstW.terminalSite selector xtra mask packets rows sources gamma hg hh p V hV) ∧
      (NearCubicWires.SourceSkeleton.KeptW.K0Site selector xtra mask packets rows sources gamma hg hh p V hV mode (RepairOrdinary.frame bits) qW cdW
      (NearCubicWires.SourceSkeleton.InitS.initResVal Rc q L CP DP CW DW CL DL mode tg
        (NearCubicWires.SourceSkeleton.InitS.valAllX mode L q Rc DD CD Dcw Ccw CL DL b MB)) Vv NC) (NearCubicWires.SourceSkeleton.FirstW.terminalSite selector xtra mask packets rows sources gamma hg hh p V hV) = ZeroPadding.pad 0 (List.replicate NC true) ∧
      (fun _ : Fin V => (0 : Nat)) (NearCubicWires.SourceSkeleton.FirstW.terminalSite selector xtra mask packets rows sources gamma hg hh p V hV) = 0) ∧
    (∀ x : Fin V, x.val = (𝔡).B + 48 + restPc (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).se.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).sp.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).gW →
      (NearCubicWires.SourceSkeleton.KeptW.KSite selector xtra mask packets rows sources gamma hg hh p V hV mode) x ∧ (NearCubicWires.SourceSkeleton.KeptW.K0Site selector xtra mask packets rows sources gamma hg hh p V hV mode (RepairOrdinary.frame bits) qW cdW
      (NearCubicWires.SourceSkeleton.InitS.initResVal Rc q L CP DP CW DW CL DL mode tg
        (NearCubicWires.SourceSkeleton.InitS.valAllX mode L q Rc DD CD Dcw Ccw CL DL b MB)) Vv NC) x = ZeroPadding.pad Rc (List.replicate b true) ∧ (fun _ : Fin V => (0 : Nat)) x = 0) := by
  obtain ⟨hF, ho, hB, hU, hres, hx25⟩ := NearCubicWires.SourceSkeleton.KeptW.site_nums selector xtra mask packets rows sources gamma hg hh p
  have hFB : (𝔡).F ≤ (𝔡).B := by omega
  have strip : ∀ x : Fin V, (𝔡).F ≤ x.val → (NearCubicWires.SourceSkeleton.KeptW.K0Site selector xtra mask packets rows sources gamma hg hh p V hV mode (RepairOrdinary.frame bits) qW cdW
      (NearCubicWires.SourceSkeleton.InitS.initResVal Rc q L CP DP CW DW CL DL mode tg
        (NearCubicWires.SourceSkeleton.InitS.valAllX mode L q Rc DD CD Dcw Ccw CL DL b MB)) Vv NC) x =
      NearCubicWires.SourceSkeleton.InitS.initResVal Rc q L CP DP CW DW CL DL mode tg
        (NearCubicWires.SourceSkeleton.InitS.valAllX mode L q Rc DD CD Dcw Ccw CL DL b MB)
        (x.val - ((𝔡).B + 29 + restPc (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).se.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).sp.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).gW)) :=
    fun x hx => NearCubicWires.SourceSkeleton.KeptW.K0Site_strip selector xtra mask packets rows sources gamma hg hh p V hV mode _ qW cdW _ Vv NC x hx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact ⟨Or.inl (Or.inr (Or.inr (Or.inl ⟨j, rfl⟩))), NearCubicWires.SourceSkeleton.KeptW.K0Site_cache selector xtra mask packets rows sources gamma hg hh p V hV mode _ qW cdW _ Vv NC j, rfl⟩
  · intro x hx
    refine ⟨Or.inl (Or.inl hx), NearCubicWires.SourceSkeleton.KeptW.K0Site_one selector xtra mask packets rows sources gamma hg hh p V hV mode _ qW cdW _ Vv NC
      (fun i => SelLocal.cache_ne_one sources p (NearCubicWires.SourceSkeleton.FirstW.kSite selector xtra mask packets rows sources gamma hg hh p) (NearCubicWires.SourceSkeleton.FirstW.rSite selector xtra mask packets rows sources gamma hg hh p)
        (NearCubicWires.SourceSkeleton.FirstW.scrSite selector mask packets rows sources gamma hg hh p) mode i) x hx, rfl⟩
  · intro i hi x hx
    refine ⟨SelLocal.srcK4_hrT _ _ i hi x hx, ?_, rfl⟩
    rw [strip x (by omega), show x.val - ((𝔡).B + 29 + restPc (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).se.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).sp.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).gW) = i by omega]
    cases mode with
    | false => exact SelLocal.initRes_resW Rc q L CP DP CW DW CL DL tg DD CD Dcw Ccw b MB i hi
    | true => exact SelLocal.initRes_resWS Rc q L CP DP CW DW CL DL tg DD CD Dcw Ccw b MB i hi
  · intro x hx
    refine ⟨SelLocal.srcK4_hrD _ _ x hx, ?_, rfl⟩
    rw [strip x (by omega), show x.val - ((𝔡).B + 29 + restPc (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).se.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).sp.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).gW) = 12 by omega]
    exact SelLocal.initRes_D Rc q L CP DP CW DW CL DL mode tg DD CD Dcw Ccw b MB
  · refine ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), ?_, rfl⟩
    rw [ZeroPadding.pad_zero]
    exact NearCubicWires.SourceSkeleton.KeptW.K0Site_terminal selector xtra mask packets rows sources gamma hg hh p V hV mode _ qW cdW _ Vv NC
  · intro x hx
    refine ⟨SelLocal.srcK4_hrG5 _ _ x hx, ?_, rfl⟩
    rw [strip x (by omega), show x.val - ((𝔡).B + 29 + restPc (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).se.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).sp.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).gW) = 19 by omega]
    exact SelLocal.initRes_b Rc q L CP DP CW DW CL DL mode tg DD CD Dcw Ccw b MB

end site

end
end NearCubicWires.SourceRequest.SelKeptSite
end

