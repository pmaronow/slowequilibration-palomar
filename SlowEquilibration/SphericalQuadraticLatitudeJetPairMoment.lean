-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetPhysicalPalmMarginal

@[expose] public section

/-! Exact two-point exponential moment of the genuine degree-two Taylor
bank in the original ordered tensor disorder. This is the Gaussian part of
the source `mb-quadratic` second-moment computation. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open SphericalTAPCriticalAnalyticNeighborhood
open ConditionedDeterminantMoments
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem quadraticLatitudeJet_memLp {N : ℕ} (μ : FiniteMixture)
    (a : ℝ) (u ω : Vector N) :
    MemLp (quadraticLatitudeJet μ a u ω) 2 (disorderLaw N μ.maxDegree) := by
  exact (jet_memLp (mixtureCoefficients μ) 2 (a • u) ![ω,ω]).const_mul _

private theorem quadraticLatitudeJet_mean {N : ℕ} (μ : FiniteMixture)
    (a : ℝ) (u ω : Vector N) :
    (∫ J, quadraticLatitudeJet μ a u ω J ∂disorderLaw N μ.maxDegree)=0 := by
  unfold quadraticLatitudeJet
  rw [integral_const_mul,jet_mean,mul_zero]

def quadraticLatitudeJetPair {N : ℕ} (μ : FiniteMixture) (a : ℝ)
    (u ω ω' : Vector N) (J : Disorder N μ.maxDegree) : ℝ :=
  quadraticLatitudeJet μ a u ω J + quadraticLatitudeJet μ a u ω' J

/-- The pair is itself a centered real Gaussian because it is a linear
functional of the original tensor coefficient array. -/
theorem quadraticLatitudeJetPair_hasGaussianLaw {N : ℕ} (μ : FiniteMixture)
    (a : ℝ) (u ω ω' : Vector N) :
    HasGaussianLaw (quadraticLatitudeJetPair μ a u ω ω')
      (disorderLaw N μ.maxDegree) := by
  have hraw := (disorder_hasGaussianLaw N μ.maxDegree).map_fun
    (((1-a^2)/2) • jetCLM (mixtureCoefficients μ) 2 (a • u) ![ω,ω] +
      ((1-a^2)/2) • jetCLM (mixtureCoefficients μ) 2 (a • u) ![ω',ω'])
  exact hraw.congr (Y := quadraticLatitudeJetPair μ a u ω ω')
    (Filter.Eventually.of_forall (fun J => by
      simp [quadraticLatitudeJetPair,quadraticLatitudeJet]))

/-- Exact pair variance in terms of the physical overlap kernel. -/
theorem quadraticLatitudeJetPair_variance {N : ℕ} (hN : 0 < N)
    (μ : FiniteMixture) (a : ℝ) (u ω ω' : Vector N)
    (hu : ‖u‖^2=(N:ℝ))
    (hω : inner ℝ ω u=0) (hω' : inner ℝ ω' u=0) :
    variance (quadraticLatitudeJetPair μ a u ω ω')
      (disorderLaw N μ.maxDegree) =
      (N:ℝ)*sourceQuadraticLatitudeVariance μ a *
        ((overlap ω ω)^2 + 2*(overlap ω ω')^2 + (overlap ω' ω')^2) := by
  change variance (fun J => quadraticLatitudeJet μ a u ω J+
    quadraticLatitudeJet μ a u ω' J) (disorderLaw N μ.maxDegree)=_
  rw [variance_fun_add
    (quadraticLatitudeJet_memLp μ a u ω)
    (quadraticLatitudeJet_memLp μ a u ω')]
  rw [← covariance_self (quadraticLatitudeJet_memLp μ a u ω).aemeasurable,
    ← covariance_self (quadraticLatitudeJet_memLp μ a u ω').aemeasurable,
    quadraticLatitudeJet_covariance hN μ a u ω ω hu hω hω,
    quadraticLatitudeJet_covariance hN μ a u ω ω' hu hω hω',
    quadraticLatitudeJet_covariance hN μ a u ω' ω' hu hω' hω']
  ring

/-- Exact unconditioned Gaussian replica exponential moment. -/
theorem quadraticLatitudeJetPair_exp_integral {N : ℕ} (hN : 0 < N)
    (μ : FiniteMixture) (a β : ℝ) (u ω ω' : Vector N)
    (hu : ‖u‖^2=(N:ℝ))
    (hω : inner ℝ ω u=0) (hω' : inner ℝ ω' u=0) :
    (∫ J, Real.exp (β*quadraticLatitudeJetPair μ a u ω ω' J)
      ∂disorderLaw N μ.maxDegree) =
      Real.exp (β^2*(N:ℝ)*sourceQuadraticLatitudeVariance μ a *
        ((overlap ω ω)^2 + 2*(overlap ω ω')^2 + (overlap ω' ω')^2)/2) := by
  have hG := quadraticLatitudeJetPair_hasGaussianLaw μ a u ω ω'
  change mgf (quadraticLatitudeJetPair μ a u ω ω')
    (disorderLaw N μ.maxDegree) β = _
  rw [mgf_gaussianReal ⟨hG.aemeasurable,hG.map_eq_gaussianReal⟩,
    Real.coe_toNNReal _ (variance_nonneg _ _),
    quadraticLatitudeJetPair_variance hN μ a u ω ω' hu hω hω']
  have hmean : (∫ J, quadraticLatitudeJetPair μ a u ω ω' J
      ∂disorderLaw N μ.maxDegree)=0 := by
    change (∫ J, quadraticLatitudeJet μ a u ω J+
      quadraticLatitudeJet μ a u ω' J ∂disorderLaw N μ.maxDegree)=0
    rw [integral_add]
    · simp [quadraticLatitudeJet_mean]
    · exact (quadraticLatitudeJet_memLp μ a u ω).integrable (by norm_num)
    · exact (quadraticLatitudeJet_memLp μ a u ω').integrable (by norm_num)
  rw [hmean]
  congr 1
  ring

/-- The physical transverse sphere has radius `sqrt n`; its image in the
ambient `(n+1)`-dimensional Hamiltonian must be rescaled to radius
`sqrt (n+1)` before the Taylor-jet covariance has source normalization. -/
def quadraticBankDirection (n : ℕ) (u : Vector (n+1))
    (y : Vector n) : Vector (n+1) :=
  Real.sqrt (((n+1:ℕ):ℝ)/(n:ℝ)) • latitudeFrameAt u y

theorem quadraticBankDirection_tangent {n : ℕ}
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1:ℕ):ℝ))
    (y : Vector n) : inner ℝ (quadraticBankDirection n u y) u=0 := by
  unfold quadraticBankDirection
  rw [real_inner_smul_left,latitudeFrameAt_orthogonal u hu y,mul_zero]

theorem quadraticBankDirection_overlap {n : ℕ} (hn : 0 < n)
    (u : Vector (n+1)) (y z : Vector n) :
    overlap (quadraticBankDirection n u y)
      (quadraticBankDirection n u z)=overlap y z := by
  have hnr : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnr0 : (0:ℝ) ≤ ((n+1:ℕ):ℝ)/(n:ℝ) := by positivity
  unfold quadraticBankDirection overlap
  rw [real_inner_smul_left,real_inner_smul_right,
    (latitudeFrameAt u).inner_map_map]
  rw [← mul_assoc,← pow_two,Real.sq_sqrt hnr0]
  push_cast
  field_simp

theorem quadraticBankDirection_norm_sq {n : ℕ} (hn : 0 < n)
    (u : Vector (n+1)) (y : Vector n) (hy : ‖y‖^2=(n:ℝ)) :
    ‖quadraticBankDirection n u y‖^2=((n+1:ℕ):ℝ) := by
  have hnr : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnr0 : (0:ℝ) ≤ ((n+1:ℕ):ℝ)/(n:ℝ) := by positivity
  unfold quadraticBankDirection
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    (latitudeFrameAt u).norm_map,mul_pow,Real.sq_sqrt hnr0,hy]
  push_cast
  field_simp

/-- Literal two-replica exponential moment, now in the transverse overlap
coordinates appearing in `mb-quadratic`. -/
theorem quadraticLatitudeJetPair_exp_integral_transverse {n : ℕ}
    (hn : 0 < n) (μ : FiniteMixture) (a β : ℝ)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1:ℕ):ℝ))
    (y z : Vector n) (hy : ‖y‖^2=(n:ℝ))
    (hz : ‖z‖^2=(n:ℝ)) :
    (∫ J, Real.exp (β * quadraticLatitudeJetPair μ a u
      (quadraticBankDirection n u y) (quadraticBankDirection n u z) J)
      ∂disorderLaw (n+1) μ.maxDegree) =
      Real.exp (β^2*((n+1:ℕ):ℝ)*sourceQuadraticLatitudeVariance μ a *
        (1+(overlap y z)^2)) := by
  rw [quadraticLatitudeJetPair_exp_integral (by omega) μ a β u _ _ hu
    (quadraticBankDirection_tangent u hu y)
    (quadraticBankDirection_tangent u hu z)]
  rw [overlap_self (by omega) _ (quadraticBankDirection_norm_sq hn u y hy),
    overlap_self (by omega) _ (quadraticBankDirection_norm_sq hn u z hz),
    quadraticBankDirection_overlap hn]
  congr 1
  ring

/-- The exact two-point Gaussian moment holds at every literal physical
mixed Palm mark, including null targets. The finite-family law is essential:
two separate one-point marginal identities would not preserve covariance. -/
theorem quadraticLatitudeJetPair_physicalMixedPalm_exp_integral
    {n : ℕ} (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    (Q a β : ℝ) (u : Vector (n+2))
    (hu : ‖u‖^2=((n+2:ℕ):ℝ))
    (ω ω' : Vector (n+2))
    (hω : inner ℝ ω u=0) (hω' : inner ℝ ω' u=0)
    (z : EuclideanSpace ℝ (Fin 2)) :
    (∫ J, Real.exp (β*quadraticLatitudeJetPair μ a u ω ω' J)
      ∂mixedLaw μ Q u hu z) =
      Real.exp (β^2*((n+2:ℕ):ℝ)*sourceQuadraticLatitudeVariance μ a *
        ((overlap ω ω)^2 + 2*(overlap ω ω')^2 + (overlap ω' ω')^2)/2) := by
  let F := fun J : Disorder (n+2) μ.maxDegree =>
    flatQuadraticLatitudeJetFamily μ a u ![ω,ω'] (euclideanDisorder J)
  have hF : Measurable F := by
    unfold F
    exact (flatQuadraticLatitudeJetFamily μ a u ![ω,ω']).continuous.measurable.comp
      ((PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : Coordinate (n+2) μ.maxDegree => ℝ)).symm.continuous.measurable.comp
        (flatDisorder_measurable (n+2) μ.maxDegree))
  let g : EuclideanSpace ℝ (Fin 2) → ℝ := fun v => Real.exp (β*(v 0+v 1))
  have hg : Measurable g := by fun_prop
  have hmap := quadraticLatitudeJetFamily_physicalMixedPalm_marginal
    μ hμ Q a u hu ![ω,ω'] (by intro i; fin_cases i <;> assumption) z
  change (mixedLaw μ Q u hu z).map F=(disorderLaw (n+2) μ.maxDegree).map F at hmap
  have hint := congrArg (fun ν : Measure (EuclideanSpace ℝ (Fin 2)) =>
    ∫ v, g v ∂ν) hmap
  rw [integral_map hF.aemeasurable hg.aestronglyMeasurable,
    integral_map hF.aemeasurable hg.aestronglyMeasurable] at hint
  have hpoint (J : Disorder (n+2) μ.maxDegree) :
      g (F J)=Real.exp (β*quadraticLatitudeJetPair μ a u ω ω' J) := by
    simp [g,F,quadraticLatitudeJetPair]
  simp_rw [hpoint] at hint
  rw [hint]
  exact quadraticLatitudeJetPair_exp_integral (by omega) μ a β u ω ω' hu hω hω'

theorem quadraticLatitudeJetPair_physicalMixedPalm_exp_integral_transverse
    {d : ℕ} (μ : FiniteMixture)
    (hμ : 3 ≤ μ.minDegree) (Q a β : ℝ)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (y z : Vector (d+1)) (hy : ‖y‖^2=((d+1:ℕ):ℝ))
    (hz : ‖z‖^2=((d+1:ℕ):ℝ))
    (mark : EuclideanSpace ℝ (Fin 2)) :
    (∫ J, Real.exp (β * quadraticLatitudeJetPair μ a u
      (quadraticBankDirection (d+1) u y) (quadraticBankDirection (d+1) u z) J)
      ∂mixedLaw μ Q u hu mark) =
      Real.exp (β^2*((d+2:ℕ):ℝ)*sourceQuadraticLatitudeVariance μ a *
        (1+(overlap y z)^2)) := by
  rw [quadraticLatitudeJetPair_physicalMixedPalm_exp_integral
    μ hμ Q a β u hu _ _
    (quadraticBankDirection_tangent u hu y)
    (quadraticBankDirection_tangent u hu z) mark]
  rw [overlap_self (by omega) _ (quadraticBankDirection_norm_sq (by omega) u y hy),
    overlap_self (by omega) _ (quadraticBankDirection_norm_sq (by omega) u z hz),
    quadraticBankDirection_overlap (by omega)]
  congr 1
  ring

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
