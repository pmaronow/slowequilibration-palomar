-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairCountRates
public import SlowEquilibration.SphericalNegativeHessianMark
public import Mathlib.Topology.Order.Compact

/-! Literal sphere regularity and Hessian-margin events for the retained
selection event. The cubic operator is obtained by differentiating the
actual projected sphere Hessian and projecting its arguments and output. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory Filter Set Metric
open SphericalModel SphericalGaussianJet SphericalForm SphereHessian
open NegativeDefiniteOperators SphericalPosteriorMaps
open scoped ENNReal Topology RealInnerProductSpace
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma source_field_joint_contDiff {N P:ℕ} (c:Degree P→ℝ) :
    ContDiff ℝ ⊤ (fun z:Disorder N P×Vector N=>field c z.1 z.2):=by
  unfold field blockField SphericalAging.FiniteModel.Hamiltonian
    SphericalAging.FiniteModel.tensorMonomial
  apply ContDiff.sum
  intro p _
  apply contDiff_const.mul
  apply contDiff_const.mul
  apply ContDiff.sum
  intro I _
  apply ContDiff.mul
  · let Lp:Disorder N P→L[ℝ]SphericalAging.FiniteModel.Disorder N p.val.val:=ContinuousLinearMap.proj p
    let LI:SphericalAging.FiniteModel.Disorder N p.val.val→L[ℝ]ℝ:=ContinuousLinearMap.proj I
    exact LI.contDiff.comp (Lp.contDiff.comp contDiff_fst)
  · apply contDiff_prod
    intro k _
    let Li:Vector N→L[ℝ]ℝ:=EuclideanSpace.proj (I k)
    exact Li.contDiff.comp contDiff_snd

lemma source_param_fderiv_contDiff {E F G:Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f:E→F→G) (hf:ContDiff ℝ ⊤ (Function.uncurry f)) :
    ContDiff ℝ ⊤ (fun z:E×F=>fderiv ℝ (f z.1) z.2):=by
  have hh:ContDiff ℝ ⊤ (fun z:(E×F)×F=>f z.1.1 z.2):=
    hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact hh.fderiv (f:=fun z:E×F=>f z.1) contDiff_snd (by simp)

lemma source_tangentProjection_contDiff (N:ℕ) :
    ContDiff ℝ ⊤ (fun x:Vector N=>tangentProjection x):=by
  unfold tangentProjection
  have hr:ContDiff ℝ ⊤ (fun x:Vector N=>InnerProductSpace.rankOne ℝ x x):=by
    have heq:(fun x:Vector N=>InnerProductSpace.rankOne ℝ x x)=
        (fun x=>(ContinuousLinearMap.toSpanSingletonLIE ℝ (Vector N) x).comp
          (InnerProductSpace.toDual ℝ (Vector N) x)):=by
      funext x
      apply ContinuousLinearMap.ext
      intro v
      simp only [InnerProductSpace.rankOne_apply,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingletonLIE_apply,InnerProductSpace.toDual_apply_apply]
      rfl
    rw [heq]
    exact (ContinuousLinearMap.toSpanSingletonLIE ℝ (Vector N)).contDiff.clm_comp
      (InnerProductSpace.toDual ℝ (Vector N)).contDiff
  exact contDiff_const.sub (hr.const_smul (1/(N:ℝ)))

lemma source_surfaceGradient_joint_contDiff {N P:ℕ} (c:Degree P→ℝ) :
    ContDiff ℝ ⊤ (fun z:Disorder N P×Vector N=>surfaceGradient (field c z.1) z.2):=by
  have hd:=source_param_fderiv_contDiff (fun (J:Disorder N P) (x:Vector N)=>field c J x) (source_field_joint_contDiff c)
  have hg:ContDiff ℝ ⊤ (fun z:Disorder N P×Vector N=>gradient (field c z.1) z.2):=
    (InnerProductSpace.toDual ℝ (Vector N)).symm.contDiff.comp hd
  exact ((source_tangentProjection_contDiff N).comp contDiff_snd).clm_apply hg

def sourceSphereHessianExtension {N P:ℕ} (c:Degree P→ℝ) (J:Disorder N P) (x:Vector N) :
    Vector N→L[ℝ]Vector N:=
  (tangentProjection x).comp ((fderiv ℝ (surfaceGradient (field c J)) x).comp (tangentProjection x))

lemma sourceSphereHessianExtension_joint_contDiff {N P:ℕ} (c:Degree P→ℝ) :
    ContDiff ℝ ⊤ (fun z:Disorder N P×Vector N=>sourceSphereHessianExtension c z.1 z.2):=by
  have hπ:ContDiff ℝ ⊤ (fun z:Disorder N P×Vector N=>tangentProjection z.2):=
    (source_tangentProjection_contDiff N).comp contDiff_snd
  have hd:=source_param_fderiv_contDiff (fun (J:Disorder N P) (x:Vector N)=>surfaceGradient (field c J) x)
    (source_surfaceGradient_joint_contDiff c)
  exact hπ.clm_comp (hd.clm_comp hπ)

def sourceSphereThirdExtension {N P:ℕ} (c:Degree P→ℝ) (J:Disorder N P) (x:Vector N) :
    Vector N→L[ℝ]Vector N→L[ℝ]Vector N:=
  (((ContinuousLinearMap.compL ℝ (Vector N) (Vector N) (Vector N) (tangentProjection x)).comp
    ((ContinuousLinearMap.compL ℝ (Vector N) (Vector N) (Vector N)).flip (tangentProjection x))).comp
      (fderiv ℝ (sourceSphereHessianExtension c J) x)).comp (tangentProjection x)

lemma sourceSphereThirdExtension_joint_contDiff {N P:ℕ} (c:Degree P→ℝ) :
    ContDiff ℝ ⊤ (fun z:Disorder N P×Vector N=>sourceSphereThirdExtension c z.1 z.2):=by
  have hπ:ContDiff ℝ ⊤ (fun z:Disorder N P×Vector N=>tangentProjection z.2):=
    (source_tangentProjection_contDiff N).comp contDiff_snd
  let L:(Vector N→L[ℝ]Vector N)→L[ℝ](Vector N→L[ℝ]Vector N)→L[ℝ]Vector N→L[ℝ]Vector N:=
    ContinuousLinearMap.compL ℝ (Vector N) (Vector N) (Vector N)
  have hl:ContDiff ℝ ⊤ (fun z:Disorder N P×Vector N=>L (tangentProjection z.2)):=
    by simpa only [Function.comp_def] using (ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Vector N→L[ℝ]Vector N) (F:=(Vector N→L[ℝ]Vector N)→L[ℝ]Vector N→L[ℝ]Vector N) L).comp hπ
  have hr:ContDiff ℝ ⊤ (fun z:Disorder N P×Vector N=>L.flip (tangentProjection z.2)):=
    by simpa only [Function.comp_def] using (ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Vector N→L[ℝ]Vector N) (F:=(Vector N→L[ℝ]Vector N)→L[ℝ]Vector N→L[ℝ]Vector N) L.flip).comp hπ
  have hd:=source_param_fderiv_contDiff (sourceSphereHessianExtension (N:=N) c)
    (sourceSphereHessianExtension_joint_contDiff c)
  exact ((hl.clm_comp hr).clm_comp hd).clm_comp hπ

lemma sourceSphere_compact (N:ℕ) : IsCompact {x:Vector N|‖x‖^2=(N:ℝ)}:=by
  have heq:{x:Vector N|‖x‖^2=(N:ℝ)}=sphere 0 (Real.sqrt (N:ℝ)):=by
    ext x
    simp only [mem_ofPred_eq,mem_sphere,dist_zero_right]
    constructor
    · intro hx
      rw [←hx,Real.sqrt_sq (norm_nonneg x)]
    · intro hx
      rw [hx,Real.sq_sqrt (Nat.cast_nonneg N)]
  rw [heq]
  exact isCompact_sphere _ _

def sourceSphereRegularity {N P:ℕ} (c:Degree P→ℝ) (J:Disorder N P):ℝ:=
  sSup ((fun x:Vector N=>|field c J x|) '' {x|‖x‖^2=(N:ℝ)})/(N:ℝ)+
  sSup ((fun x:Vector N=>‖surfaceGradient (field c J) x‖) '' {x|‖x‖^2=(N:ℝ)})/Real.sqrt (N:ℝ)+
  sSup ((fun x:Vector N=>‖sourceSphereHessianExtension c J x‖) '' {x|‖x‖^2=(N:ℝ)})+
  Real.sqrt (N:ℝ)*sSup ((fun x:Vector N=>‖sourceSphereThirdExtension c J x‖) '' {x|‖x‖^2=(N:ℝ)})

lemma sourceSphereRegularity_continuous {N P:ℕ} (c:Degree P→ℝ) :
    Continuous (sourceSphereRegularity (N:=N) c):=by
  have h0:Continuous (fun J:Disorder N P=>sSup ((fun x:Vector N=>|field c J x|) '' {x|‖x‖^2=(N:ℝ)})):=
    (sourceSphere_compact N).continuous_sSup ((field_jointContinuous c).abs)
  have h1:Continuous (fun J:Disorder N P=>sSup ((fun x:Vector N=>‖surfaceGradient (field c J) x‖) '' {x|‖x‖^2=(N:ℝ)})):=
    (sourceSphere_compact N).continuous_sSup ((source_surfaceGradient_joint_contDiff c).continuous.norm)
  have h2:Continuous (fun J:Disorder N P=>sSup ((fun x:Vector N=>‖sourceSphereHessianExtension c J x‖) '' {x|‖x‖^2=(N:ℝ)})):=
    (sourceSphere_compact N).continuous_sSup ((sourceSphereHessianExtension_joint_contDiff c).continuous.norm)
  have h3base:=sourceSphereThirdExtension_joint_contDiff (N:=N) c
  have h3norm:Continuous (fun z:Disorder N P×Vector N=>‖sourceSphereThirdExtension c z.1 z.2‖):=by
    let :SeminormedAddGroup (Vector N→L[ℝ]Vector N→L[ℝ]Vector N):=
      { (inferInstance:NormedAddCommGroup (Vector N→L[ℝ]Vector N→L[ℝ]Vector N)) with }
    exact continuous_norm.comp h3base.continuous
  have h3:Continuous (fun J:Disorder N P=>sSup ((fun x:Vector N=>‖sourceSphereThirdExtension c J x‖) '' {x|‖x‖^2=(N:ℝ)})):=
    (sourceSphere_compact N).continuous_sSup h3norm
  exact (((h0.div_const (N:ℝ)).add (h1.div_const (Real.sqrt (N:ℝ)))).add h2).add (h3.const_mul _)

def sourceHessianMargin {N P:ℕ} (c:Degree P→ℝ) (κ:ℝ) (J:Disorder N P) (u:Vector N):Prop:=
  ∀ v:Vector N,inner ℝ v (sourceSphereHessianExtension c J u v) ≤ -κ*‖tangentProjection u v‖^2

lemma sourceHessianMargin_closed {N P:ℕ} (c:Degree P→ℝ) (κ:ℝ) :
    IsClosed {p:Disorder N P×Vector N|sourceHessianMargin c κ p.1 p.2}:=by
  have heq:{p:Disorder N P×Vector N|sourceHessianMargin c κ p.1 p.2}=
      ⋂ v:Vector N,{p:Disorder N P×Vector N|inner ℝ v (sourceSphereHessianExtension c p.1 p.2 v) ≤ -κ*‖tangentProjection p.2 v‖^2}:=by
    ext p
    simp only [sourceHessianMargin,mem_ofPred_eq,mem_iInter]
  rw [heq]
  apply isClosed_iInter
  intro v
  exact isClosed_le (continuous_const.inner ((sourceSphereHessianExtension_joint_contDiff c).continuous.clm_apply continuous_const))
    ((((tangentProjection_continuous N).comp continuous_snd).clm_apply continuous_const).norm.pow 2 |>.const_mul (-κ))

end
end SlowEquilibration.PairConditionalDeterminantMoments
