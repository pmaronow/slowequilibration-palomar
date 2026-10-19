-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetPhysicalWeightedPoint
public import SlowEquilibration.SphericalQuadraticLatitudeJetPhysicalResidualMGF

@[expose] public section

/-! The actual determinant-weighted original latitude partition obeys the
source `mb-quadratic` estimate: the correlated quadratic bank costs one
dimension- and mark-uniform constant, and the full exponential rate is the
printed conditional Gaussian exponent. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory Filter Set SphericalModel ConditionedDeterminantMoments
open SphericalTAPCertificate SphericalTAPCriticalAnalyticNeighborhood
open SphericalTAPMixedBandExponent GOEPhysicalPotential
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-- Source `mb-quadratic` for the literal original tensor Hamiltonian,
physical latitude sphere, conditioned Hessian determinant, and actual mixed
value/radial/zero-gradient Palm law. -/
theorem source_mb_quadratic_physicalMixedPalm
    (μ : FiniteMixture) (hnp : μ.minDegree < μ.maxDegree)
    {β x Q : ℝ} (h : Certificate μ β x Q)
    {g : ℝ} (hg : 0 < g) :
    ∃ b₀ C : ℝ, 0 < b₀ ∧ b₀ < Real.sqrt Q ∧ 0 < C ∧
      ∀ᶠ d : ℕ in atTop,
        ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
          (mark : EuclideanSpace ℝ (Fin 2)),
          2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ mark 1 →
          ∀ (b : ℝ), 0 < b → b ≤ b₀ →
          ∀ a ∈ Icc (Real.sqrt Q-b) (Real.sqrt Q+b),
            Integrable (fun J => intrinsicDet μ Q u J *
              partitionAgainst (latitudeLaw u (latitudeFrameAt u) a) β
                (field (mixtureCoefficients μ) J))
              (mixedLaw μ Q u hu mark) ∧
            (∫ J, intrinsicDet μ Q u J *
              partitionAgainst (latitudeLaw u (latitudeFrameAt u) a) β
                (field (mixtureCoefficients μ) J)
              ∂mixedLaw μ Q u hu mark) ≤
                C * physicalMean d (d+2) (Q^2*μ.xi2 Q) (mark 1) *
                  Real.exp (((d+2:ℕ):ℝ)*
                    sourceMixedXi μ β Q (mark 0) (mark 1) a) := by
  have hμ : 3 ≤ μ.minDegree := by have := h.min_degree; omega
  obtain ⟨bm,_,hbm,hbmQ,_,_,hband,_⟩ := quadratic_fixed_band_margin μ h
  obtain ⟨bb,Cb,hbb,hbbQ,hCb,hbank⟩ :=
    quadraticBankPartition_certificate_determinant_cauchy μ hnp h hg
  let K := (2 : ℝ)^2 * Real.exp
    (4*(Q^2*μ.xi2 Q)*(2 : ℝ)^2/g^2)
  let C := Real.sqrt K * Real.sqrt Cb
  have hK : 0 < K := by dsimp [K]; positivity
  have hC : 0 < C := mul_pos (Real.sqrt_pos.mpr hK) (Real.sqrt_pos.mpr hCb)
  refine ⟨min bb bm,C,lt_min hbb hbm,(min_lt_iff).mpr (Or.inl hbbQ),hC,?_⟩
  have hpoint := intrinsicDet_physicalMixedPalm_sq_integrable_eventually
    μ h.overlap_range.1 hnp hg
  have hdet := mixed_conditioned_determinant_moments_sharp_eventually
    μ h.overlap_range.1 hnp hg
  filter_upwards [hbank,hpoint,hdet] with d hbd hpd hdd
  intro u hu mark hmark b hb hbb' a ha
  have hbbank : b ≤ bb := hbb'.trans (min_le_left _ _)
  have hbmargin : b ≤ bm := hbb'.trans (min_le_right _ _)
  have ha' : a ∈ Icc (Real.sqrt Q-bm) (Real.sqrt Q+bm) :=
    ⟨by linarith [ha.1],by linarith [ha.2]⟩
  have haar : a ∈ Ioo (0:ℝ) 1 := hband ha'
  have ha0 : 0 ≤ 1-a^2 := by nlinarith [haar.1,haar.2]
  let residualMean := Real.exp (((d+2:ℕ):ℝ)*
    (β*sourceMixedMean μ Q (mark 0) (mark 1) a+
      β^2/2*(sourceMixedVariance μ Q a-sourceQuadraticLatitudeVariance μ a)))
  have hres (y : Vector (d+1)) (hy : ‖y‖^2=((d+1:ℕ):ℝ)) :
      (∫ J, Real.exp (β*(field (mixtureCoefficients μ) J
          (originalLatitudePoint a u (quadraticBankDirection (d+1) u y)) -
        quadraticLatitudeJet μ a u (quadraticBankDirection (d+1) u y) J))
        ∂mixedLaw μ Q u hu mark) = residualMean := by
    exact nonquadraticLatitudeField_physicalMixedPalm_exp_integral
      μ hμ h.overlap_range.1 hnp a β ha0 u
      (quadraticBankDirection (d+1) u y) hu
      (quadraticBankDirection_tangent u hu y)
      (quadraticBankDirection_norm_sq (by omega : 0 < d+1) u y hy) mark
  obtain ⟨hfullInt,hfullEq⟩ := mixed_palm_determinant_latitude_angular_factorization
    μ hμ hnp h.overlap_range.1 a β ha0 u hu mark residualMean
    (fun y => originalLatitudeBankPoint_det_integrable_of_det_sq
      μ Q a β u hu mark (hpd u hu mark hmark) y)
    hres (hbd u hu mark hmark b hb hbbank a ha).1
  obtain ⟨_,hDZle⟩ := hbd u hu mark hmark b hb hbbank a ha
  have hdetMean := (hdd u hu mark hmark 2 (by norm_num)).2.1
  let detMean := ∫ J, intrinsicDet μ Q u J ∂mixedLaw μ Q u hu mark
  let m := Real.exp (β^2*((d+2:ℕ):ℝ)*sourceQuadraticLatitudeVariance μ a/2)
  have hexp : residualMean*m =
      Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q (mark 0) (mark 1) a) := by
    dsimp [residualMean,m]
    rw [← Real.exp_add]
    congr 1
    dsimp [sourceMixedXi]
    ring
  have hfinal : (∫ J, intrinsicDet μ Q u J *
      originalLatitudeBankPartition μ a β u J ∂mixedLaw μ Q u hu mark) ≤
        C * physicalMean d (d+2) (Q^2*μ.xi2 Q) (mark 1) *
          Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q (mark 0) (mark 1) a) := by
    rw [hfullEq]
    calc
      _ ≤ residualMean * (detMean*m*Real.sqrt K*Real.sqrt Cb) :=
        mul_le_mul_of_nonneg_left hDZle (Real.exp_pos _).le
      _ = C * physicalMean d (d+2) (Q^2*μ.xi2 Q) (mark 1) *
          Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q (mark 0) (mark 1) a) := by
        rw [show detMean = physicalMean d (d+2) (Q^2*μ.xi2 Q) (mark 1) from hdetMean]
        rw [←hexp]
        dsimp [C]
        ring
  simpa only [originalLatitudeBankPartition_eq_physical] using
    (show Integrable (fun J => intrinsicDet μ Q u J *
      originalLatitudeBankPartition μ a β u J) (mixedLaw μ Q u hu mark) ∧
    (∫ J, intrinsicDet μ Q u J * originalLatitudeBankPartition μ a β u J
      ∂mixedLaw μ Q u hu mark) ≤
      C * physicalMean d (d+2) (Q^2*μ.xi2 Q) (mark 1) *
        Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q (mark 0) (mark 1) a)
      from ⟨hfullInt,hfinal⟩)

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
