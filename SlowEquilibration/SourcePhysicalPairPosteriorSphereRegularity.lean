-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairSphereActualJetBounds
public import SlowEquilibration.SourcePhysicalPairPhysicalPosteriorRegularity

/-! Exponential control of the actual full covariant jet norm D_N under
the original mixed and proper value-only physical one-point posterior. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory Set
open SphericalModel SphericalGaussianJet SphericalForm SphericalMarkedWindows
open scoped RealInnerProductSpace
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

lemma sourceSphere_nonempty {N:ℕ} (hN:0<N) : {x:Vector N|‖x‖^2=(N:ℝ)}.Nonempty:=by
  let :NeZero N:=⟨Nat.ne_of_gt hN⟩
  have hS:(Metric.sphere (0:Vector N) (Real.sqrt N)).Nonempty:=
    NormedSpace.sphere_nonempty.mpr (Real.sqrt_nonneg _)
  obtain ⟨x,hx⟩:=hS
  refine ⟨x,?_⟩
  simp only [Metric.mem_sphere,dist_zero_right] at hx
  change ‖x‖^2=(N:ℝ)
  rw [hx,Real.sq_sqrt (Nat.cast_nonneg N)]

theorem source_ordered_sphere_regularity_bound {N P:ℕ} (hN:0<N)
    (c:Degree P→ℝ) {K:ℝ} (hK:0 ≤ K) (J:Disorder N P)
    (hJ:J ∈ sourcePosteriorOrderedRegularity K) :
    sourceSphereRegularity c J ≤ 13*sourcePosteriorDerivativeConstant c K:=by
  let L:=sourcePosteriorDerivativeConstant c K
  have hS:=sourceSphere_nonempty hN
  have hNr:(0:ℝ)<N:=Nat.cast_pos.mpr hN
  have hr:0<Real.sqrt (N:ℝ):=Real.sqrt_pos.mpr hNr
  have h0:sSup ((fun x:Vector N=>|field c J x|) '' {x|‖x‖^2=(N:ℝ)}) ≤ L*N:=by
    apply csSup_le (hS.image _)
    rintro _ ⟨x,hx,rfl⟩
    have hxnorm:‖x‖=Real.sqrt (N:ℝ):=SphericalAging.LandscapeDerivatives.sphere_norm x hx
    exact (source_posterior_ordered_ball_bounds (by omega) c K J hJ x hxnorm.le).1
  have h1:sSup ((fun x:Vector N=>‖surfaceGradient (field c J) x‖) '' {x|‖x‖^2=(N:ℝ)}) ≤ L*Real.sqrt N:=by
    apply csSup_le (hS.image _)
    rintro _ ⟨x,hx,rfl⟩
    exact (source_ordered_sphere_jet_bounds hN c hK J hJ x hx).1
  have h2:sSup ((fun x:Vector N=>‖sourceSphereHessianExtension c J x‖) '' {x|‖x‖^2=(N:ℝ)}) ≤ 2*L:=by
    apply csSup_le (hS.image _)
    rintro _ ⟨x,hx,rfl⟩
    exact (source_ordered_sphere_jet_bounds hN c hK J hJ x hx).2.1
  have h3:sSup ((fun x:Vector N=>‖sourceSphereThirdExtension c J x‖) '' {x|‖x‖^2=(N:ℝ)}) ≤ 9*L/Real.sqrt N:=by
    apply csSup_le (hS.image _)
    rintro _ ⟨x,hx,rfl⟩
    exact (source_ordered_sphere_jet_bounds hN c hK J hJ x hx).2.2
  unfold sourceSphereRegularity
  calc
    _ ≤ (L*N)/(N:ℝ)+(L*Real.sqrt N)/Real.sqrt N+2*L+Real.sqrt N*(9*L/Real.sqrt N):=by
      apply add_le_add
      · apply add_le_add
        · exact add_le_add (div_le_div_of_nonneg_right h0 hNr.le) (div_le_div_of_nonneg_right h1 hr.le)
        · exact h2
      · exact mul_le_mul_of_nonneg_left h3 hr.le
    _ = _:=by field_simp;ring

theorem source_mixed_physical_posterior_sphere_regularity (μ:FiniteMixture) {Q M:ℝ}
    (hQ:0<Q) (hnp:μ.minDegree<μ.maxDegree) (hM:0 ≤ M) :
    ∃ C:ℝ,0<C ∧ ∀ n:ℕ,∀ (x:Vector (n+1)) (hx:‖x‖^2=(n+1:ℕ)),
      ∀ (h k:ℝ),|h| ≤ M → |k| ≤ M →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      (mixedConditionedLaw c x hx (WithLp.toLp 2 ![h,k])).real
        {J|C<sourceSphereRegularity c J} ≤
        (Fintype.card (Degree μ.maxDegree):ℝ)*Real.exp (-(n+1:ℕ)/2):=by
  obtain ⟨K,hK,hall⟩:=source_mixed_physical_posterior_orderedRegularity μ hQ hnp hM
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let C:=13*sourcePosteriorDerivativeConstant c K
  have hC:0<C:=mul_pos (by norm_num) (sourcePosteriorDerivativeConstant_pos c hK.le)
  refine ⟨C,hC,?_⟩
  intro n x hx h k hh hk
  dsimp only
  let :IsProbabilityMeasure (mixedConditionedLaw c x hx (WithLp.toLp 2 ![h,k])):=by
    unfold mixedConditionedLaw
    infer_instance
  have hsub:{J:Disorder (n+1) μ.maxDegree|C<sourceSphereRegularity c J} ⊆
      (sourcePosteriorOrderedRegularity (N:=n+1) (P:=μ.maxDegree) K)ᶜ:=by
    intro J hbad hgood
    exact not_lt_of_ge (source_ordered_sphere_regularity_bound (by omega) c hK.le J hgood) hbad
  exact (measureReal_mono hsub).trans (hall n x hx h k hh hk)

theorem source_value_physical_posterior_sphere_regularity (μ:FiniteMixture) {Q M:ℝ}
    (hQ:0<Q) (hM:0 ≤ M) :
    ∃ C:ℝ,0<C ∧ ∀ n:ℕ,∀ (x:Vector (n+1)) (hx:‖x‖^2=(n+1:ℕ)),
      ∀ h:ℝ,|h| ≤ M →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      (valueConditionedLaw c x hx h).real {J|C<sourceSphereRegularity c J} ≤
        (Fintype.card (Degree μ.maxDegree):ℝ)*Real.exp (-(n+1:ℕ)/2):=by
  obtain ⟨K,hK,hall⟩:=source_value_physical_posterior_orderedRegularity μ hQ hM
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let C:=13*sourcePosteriorDerivativeConstant c K
  have hC:0<C:=mul_pos (by norm_num) (sourcePosteriorDerivativeConstant_pos c hK.le)
  refine ⟨C,hC,?_⟩
  intro n x hx h hh
  dsimp only
  let :IsProbabilityMeasure (valueConditionedLaw c x hx h):=by
    unfold valueConditionedLaw
    infer_instance
  have hsub:{J:Disorder (n+1) μ.maxDegree|C<sourceSphereRegularity c J} ⊆
      (sourcePosteriorOrderedRegularity (N:=n+1) (P:=μ.maxDegree) K)ᶜ:=by
    intro J hbad hgood
    exact not_lt_of_ge (source_ordered_sphere_regularity_bound (by omega) c hK.le J hgood) hbad
  exact (measureReal_mono hsub).trans (hall n x hx h hh)

end
end SlowEquilibration.PairConditionalDeterminantMoments
