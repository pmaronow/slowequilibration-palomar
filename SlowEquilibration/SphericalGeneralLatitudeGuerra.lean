-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeThreeBlockBounds
public import SlowEquilibration.SphericalLatitudePositiveCube
public import SlowEquilibration.SphericalLatitudeCubePositivity

@[expose] public section

/-! # Genuine odd-mixture latitude Guerra upper bound

A fixed finite tensor positivity bank controls the literal negative
transverse-overlap covariance error. The actual bank pressure cost is O(1),
so the normalized error vanishes without changing the original model.
-/
namespace SlowEquilibration.SphericalModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalPositivePerturbation
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 1900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The genuine finite latitude pressure is eventually below its actual
linear trial up to every prescribed error, uniformly on a positive compact
latitude interval. This includes every finite odd and quadratic mixture. -/
theorem general_latitudeQuenchedPressure_eventually_le_linearTrial
    (μ : FiniteMixture) (β : ℝ) {δ ρ : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρ : ρ < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,∀ q∈Icc δ ρ,∀ (u : Vector (n+1)),‖u‖^2=((n+1 : ℕ) : ℝ) →
      ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)),(∀ x,inner ℝ (e x) u=0) →
      latitudeQuenchedPressure n μ β u e q ≤
        (n : ℝ)/((n+1 : ℕ) : ℝ)*linearSphereQuenchedPressure n (latitudeLinearVariance n μ β q)+
          β^2/2*(μ.xi 1-μ.xi q-(1-q)*μ.xi1 q)+ε := by
  obtain ⟨η,C,hη,hη1,hC,hdef⟩ := exists_uniform_latitude_tangent_deficit_bound μ hδ hδρ hρ
  let ζ := ε/(β^2*C+1)
  have hζ : 0 < ζ := by dsimp [ζ];positivity
  have hζeq : (β^2*C+1)*ζ=ε := by dsimp [ζ];field_simp
  have hζsmall : β^2*C*ζ/2 ≤ ε/2 := by nlinarith [hζ.le]
  obtain ⟨K,V,hK,hV,hPos⟩ := exists_uniform_latitudeCube_positivity hη hη1 hζ
  have hv : 0 ≤ V := (show (0 : ℝ)≤1 by norm_num).trans hV
  have hcost := ((tendsto_const_div_atTop_nhds_zero_nat (2*V^2)).comp
    (tendsto_add_atTop_nat 1)).eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hcost,eventually_ge_atTop 1] with n hcost hn
  dsimp only [Function.comp_def] at hcost
  intro q hq u hu e he
  have hq01 : q∈Icc (0 : ℝ) 1 := ⟨hδ.le.trans hq.1,hq.2.trans hρ.le⟩
  have hqabs : |q|≤1 := abs_le.mpr ⟨by linarith [hq01.1],hq01.2⟩
  let κ := latitudeLinearVariance n μ β q
  have hκ : 0 ≤ κ := latitudeLinearVariance_nonneg n μ β hq01
  let L := fun cube : Fin K → ℝ => latitudeThreeLinear (mixtureCoefficients μ) β κ u e q
    (latitudePositivityFeature n K V cube)
  let E : Set (Vector n × Vector n) := {z | overlap z.1 z.2≤-η}
  have hE : MeasurableSet E := by
    have hm : Measurable (fun z : Vector n × Vector n => overlap z.1 z.2) := by unfold overlap;fun_prop
    exact measurableSet_le hm measurable_const
  let c := latitudeRSPairLevel n μ β q
  let a := β^2*((n+1 : ℕ) : ℝ)*C
  let d := κ*(n : ℝ)-β^2*((n+1 : ℕ) : ℝ)*μ.xi 1
  have ha : 0 ≤ a := by dsimp [a];positivity
  have hL (cube : Fin K → ℝ) : Measurable (L cube) :=
    (latitudeThreeLinear_continuous _ β κ u e q _ (latitudePositivityFeature_continuous n K V cube)).measurable
  have hpair (cube : Fin K → ℝ) : ∀ᵐ z ∂(sphereLaw n).prod (sphereLaw n),
      GaussianThreeBlockComparison.signedKernel (L cube) latitudeThreeLabel z.1 z.2 ≤
        c+a*E.indicator (fun _ => (1 : ℝ)) z := by
    filter_upwards [sphereLaw_prod_support hn] with z hz
    have ht := mul_le_mul_of_nonneg_left
      (hdef q hq (overlap z.1 z.2) (overlap_mem_Icc_of_norm_sq hn _ _ hz.1 hz.2))
      (mul_nonneg (sq_nonneg β) (Nat.cast_nonneg (n+1)))
    rw [← latitudeThree_signedKernel_sub_pairLevel hn μ β hq01 u hu e he
      (latitudePositivityFeature n K V cube) z.1 z.2] at ht
    have hI : ({t : ℝ | t < -η}.indicator (fun _ => (1 : ℝ))) (overlap z.1 z.2) ≤
        E.indicator (fun _ => (1 : ℝ)) z := by
      by_cases hs : overlap z.1 z.2 < -η
      · have hc : overlap z.1 z.2≤-η := hs.le
        simp [E,hs,hc]
      · by_cases hc : overlap z.1 z.2≤-η <;> simp [hs,E,hc]
    have hh := mul_le_mul_of_nonneg_left hI ha
    dsimp only [L,c,a] at hh ⊢
    nlinarith
  have hneg (θ : ℝ) :
      (∫cube,∫D,GaussianThreeBlockComparison.pairEventMass (sphereLaw n) (L cube) latitudeThreeLabel θ E D
        ∂SYK.standardGaussianMeasureOnEuclidean (LatitudeThreeCoordinate n μ.maxDegree (TensorCoordinate n K))
        ∂positiveCubeLaw K)≤ζ :=
    hPos n μ.maxDegree hn (mixtureCoefficients μ) (mixtureCoefficients_nonnegative μ) β κ hκ
      u hu e he q hqabs V le_rfl θ
  have hmean (θ : ℝ) : latitudePositiveCubePairKernel n K (mixtureCoefficients μ) β κ u e q V θ≤c+a*ζ := by
    let f := fun cube : Fin K → ℝ => ∫D,
      GaussianThreeBlockComparison.pairEventMass (sphereLaw n) (L cube) latitudeThreeLabel θ E D
      ∂SYK.standardGaussianMeasureOnEuclidean (LatitudeThreeCoordinate n μ.maxDegree (TensorCoordinate n K))
    have hf : Integrable f (positiveCubeLaw K) :=
      latitudePositivity_meanEventMass_integrable hn _ β κ u e q V θ E hE
    have hi := latitudePositivity_meanPair_integrable (K := K) hn _ (mixtureCoefficients_nonnegative μ) β hκ u hu e he hqabs hv θ
    have hb : ∀ᵐ cube ∂positiveCubeLaw K,
        GaussianThreeBlockComparison.meanPairKernel (sphereLaw n) (L cube) latitudeThreeLabel θ ≤ c+a*f cube := by
      exact .of_forall fun cube => by
        obtain ⟨B,hB,hbound⟩ := exists_latitudeThreeLinear_sphere_bound _ β κ u e q
          (latitudePositivityFeature n K V cube) (latitudePositivityFeature_continuous n K V cube)
        have hLb : ∀ᵐ x ∂sphereLaw n,‖L cube x‖≤B := (sphereLaw_support hn).mono fun x hx => hbound x hx
        exact GaussianThreeBlockComparison.meanPairKernel_le_of_indicator (sphereLaw n) (L cube) (hL cube)
          hB hLb latitudeThreeLabel E hE (hpair cube) θ
    have hh := integral_mono_ae hi ((integrable_const c).add (hf.const_mul a)) hb
    simp only [Pi.add_apply] at hh
    rw [integral_add (integrable_const c) (hf.const_mul a),integral_const_mul] at hh
    simp only [integral_const,probReal_univ,one_smul] at hh
    change latitudePositiveCubePairKernel n K (mixtureCoefficients μ) β κ u e q V θ≤c+a*(∫cube,f cube ∂positiveCubeLaw K) at hh
    exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hneg θ) ha))
  let B := Real.sqrt (β^2*((n+1 : ℕ) : ℝ)*covariancePolynomial (mixtureCoefficients μ) 1+κ*(n : ℝ)+(2*V)^2)
  have hLb : ∀ᵐ cube ∂positiveCubeLaw K,∀ᵐ x ∂sphereLaw n,‖L cube x‖≤B :=
    (positiveCubeLaw_abs_le_two K).mono fun cube hcube => latitudeThreeLinear_positivity_bound hn _
      (mixtureCoefficients_nonnegative μ) β hκ u hu e he hqabs hv cube hcube
  have hdiag : ∀ᵐ cube ∂positiveCubeLaw K,∀ᵐ x ∂sphereLaw n,
      GaussianThreeBlockComparison.signedKernel (L cube) latitudeThreeLabel x x=d := by
    exact .of_forall fun cube => (sphereLaw_support hn).mono fun x hx =>
      latitudeThree_signedKernel_diagonal hn μ β hq01 u hu e he _ x hx
  have hc := GaussianThreeBlockComparison.gaussian_covariance_comparison_of_parameter_mean_pair
    (positiveCubeLaw K) (sphereLaw n) L hL (Real.sqrt_nonneg _) hLb latitudeThreeLabel hdiag
    (fun θ => (latitudePositivity_pressure_measurable hn _ β κ u e q V θ).aestronglyMeasurable)
    (fun θ => latitudePositivity_meanPair_integrable (K := K) hn _ (mixtureCoefficients_nonnegative μ) β hκ u hu e he hqabs hv θ)
    (fun θ _ => hmean θ)
  have hleft := (latitudePositiveCubePressure_sub_mean_mem_Icc hn _ (mixtureCoefficients_nonnegative μ)
    β hκ u hu e he hqabs hv (K := K) 0).1
  have hright := (latitudePositiveCubePressure_sub_mean_mem_Icc hn _ (mixtureCoefficients_nonnegative μ)
    β hκ u hu e he hqabs hv (K := K) (Real.pi/2)).2
  change latitudePositiveCubePressure n K (mixtureCoefficients μ) β κ u e q V 0≤
    latitudePositiveCubePressure n K (mixtureCoefficients μ) β κ u e q V (Real.pi/2)+(c+a*ζ-d)/2 at hc
  have hh : GaussianSpinComparison.averagedRotatedLogPartition (sphereLaw n)
      (latitudeGuerraLinear (mixtureCoefficients μ) β κ u e q) latitudeGuerraLabel 0≤
      GaussianSpinComparison.averagedRotatedLogPartition (sphereLaw n)
        (latitudeGuerraLinear (mixtureCoefficients μ) β κ u e q) latitudeGuerraLabel (Real.pi/2)+
          (c-d)/2+a*ζ/2+2*V^2 := by linarith
  rw [latitudeGuerraMean_zero_eq_physical hn _ (mixtureCoefficients_nonnegative μ) β κ u hu e he hqabs,
    latitudeGuerraMean_pi_div_two_eq_linear hn _ β hκ u e q] at hh
  have hNpos : 0 < ((n+1 : ℕ) : ℝ) := by positivity
  have hd := div_le_div_of_nonneg_right hh hNpos.le
  have heval : ((n : ℝ)*linearSphereQuenchedPressure n κ+(c-d)/2+a*ζ/2+2*V^2)/((n+1 : ℕ) : ℝ)=
      (n : ℝ)/((n+1 : ℕ) : ℝ)*linearSphereQuenchedPressure n κ+
        β^2/2*(μ.xi 1-μ.xi q-(1-q)*μ.xi1 q)+β^2*C*ζ/2+2*V^2/((n+1 : ℕ) : ℝ) := by
    dsimp only [c,d,a]
    rw [show κ*(n : ℝ)=β^2*((n+1 : ℕ) : ℝ)*(1-q^2)*μ.xi1 q from latitudeLinearVariance_mul_dim hn μ β q]
    unfold latitudeRSPairLevel
    field_simp
    ring
  rw [heval] at hd
  change latitudeQuenchedPressure n μ β u e q≤_ at hd
  dsimp only [κ] at hd
  exact hd.trans (by linarith)

end
end SlowEquilibration.SphericalModel
