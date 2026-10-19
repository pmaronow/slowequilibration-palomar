-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetPureAngularFactorization
public import SlowEquilibration.SphericalTAPCriticalPureLatitudeProfile
public import SlowEquilibration.SphericalTAPQuadraticBankPhysicalOverlap

@[expose] public section

/-! The proper-pure physical source section estimate. The final analytic
input is the exact scalar residual Gaussian MGF at each transverse point. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory Filter Set SphericalModel ConditionedDeterminantMoments
open SphericalTAPCertificate SphericalTAPCriticalAnalyticNeighborhood
open SphericalTAPCriticalPureLatitudeVariance GOEPhysicalPotential
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

theorem source_mb_quadratic_physicalPurePalm_of_residualMGF
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp alpha halpha) β x Q)
    {g : ℝ} (hg : 0 < g)
    (hres : ∀ (d : ℕ) (u : Vector (d+2))
      (hu : ‖u‖^2=((d+2:ℕ):ℝ)) (e a : ℝ)
      (_ha : 0 ≤ 1-a^2) (ω : Vector (d+2))
      (_hω : inner ℝ ω u=0) (_hωn : ‖ω‖^2=((d+2:ℕ):ℝ)),
      let μ := FiniteMixture.pure p hp alpha halpha
      (∫ J, Real.exp (β*(field (mixtureCoefficients μ) J
          (originalLatitudePoint a u ω)-quadraticLatitudeJet μ a u ω J))
        ∂pureLaw p hp alpha halpha Q u hu e) =
        Real.exp (((d+2:ℕ):ℝ)*
          (β*e*(a/Real.sqrt Q)^p+
            β^2/2*(sourcePureLatitudeVariance p alpha a-
              sourceQuadraticLatitudeVariance μ a)))) :
    let μ := FiniteMixture.pure p hp alpha halpha
    ∃ b₀ C : ℝ, 0 < b₀ ∧ b₀ < Real.sqrt Q ∧ 0 < C ∧
      ∀ᶠ d : ℕ in atTop,
        ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)) (e : ℝ),
          2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ (p:ℝ)*e →
          ∀ (b : ℝ), 0 < b → b ≤ b₀ →
          ∀ a ∈ Icc (Real.sqrt Q-b) (Real.sqrt Q+b),
            Integrable (fun J => intrinsicDet μ Q u J *
              partitionAgainst (latitudeLaw u (latitudeFrameAt u) a) β
                (field (mixtureCoefficients μ) J))
              (pureLaw p hp alpha halpha Q u hu e) ∧
            (∫ J, intrinsicDet μ Q u J *
              partitionAgainst (latitudeLaw u (latitudeFrameAt u) a) β
                (field (mixtureCoefficients μ) J)
              ∂pureLaw p hp alpha halpha Q u hu e) ≤
                C * physicalMean d (d+2) (Q^2*μ.xi2 Q) ((p:ℝ)*e) *
                  Real.exp (((d+2:ℕ):ℝ)*
                    (β*e*(a/Real.sqrt Q)^p+
                      β^2/2*sourcePureLatitudeVariance p alpha a)) := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  have hμ : 3 ≤ μ.minDegree := by
    have hh : 4 ≤ μ.minDegree := h.min_degree
    omega
  obtain ⟨bm,_,hbm,hbmQ,_,_,hband,_⟩ := quadratic_fixed_band_margin μ h
  obtain ⟨bb,Cb,hbb,hbbQ,hCb,hbank⟩ :=
    quadraticBankPartition_pure_certificate_determinant_cauchy
      p hp alpha halpha h hg
  let K := (2 : ℝ)^2 * Real.exp
    (4*(Q^2*μ.xi2 Q)*(2 : ℝ)^2/g^2)
  let C := Real.sqrt K * Real.sqrt Cb
  have hK : 0 < K := by dsimp [K]; positivity
  have hC : 0 < C := mul_pos (Real.sqrt_pos.mpr hK) (Real.sqrt_pos.mpr hCb)
  refine ⟨min bb bm,C,lt_min hbb hbm,(min_lt_iff).mpr (Or.inl hbbQ),hC,?_⟩
  have hpoint := intrinsicDet_physicalPurePalm_sq_integrable_eventually
    p hp alpha halpha h.overlap_range.1 hg
  have hdet := pure_conditioned_determinant_moments_sharp_eventually
    p hp alpha halpha h.overlap_range.1 hg
  filter_upwards [hbank,hpoint,hdet] with d hbd hpd hdd
  intro u hu e he b hb hbb' a ha
  have hbbank : b ≤ bb := hbb'.trans (min_le_left _ _)
  have hbmargin : b ≤ bm := hbb'.trans (min_le_right _ _)
  have ha' : a ∈ Icc (Real.sqrt Q-bm) (Real.sqrt Q+bm) :=
    ⟨by linarith [ha.1],by linarith [ha.2]⟩
  have haar : a ∈ Ioo (0:ℝ) 1 := hband ha'
  have ha0 : 0 ≤ 1-a^2 := by nlinarith [haar.1,haar.2]
  let residualMean := Real.exp (((d+2:ℕ):ℝ)*
    (β*e*(a/Real.sqrt Q)^p+
      β^2/2*(sourcePureLatitudeVariance p alpha a-
        sourceQuadraticLatitudeVariance μ a)))
  have hres' (y : Vector (d+1)) (hy : ‖y‖^2=((d+1:ℕ):ℝ)) :
      (∫ J, Real.exp (β*(field (mixtureCoefficients μ) J
          (originalLatitudePoint a u (quadraticBankDirection (d+1) u y)) -
        quadraticLatitudeJet μ a u (quadraticBankDirection (d+1) u y) J))
        ∂pureLaw p hp alpha halpha Q u hu e) = residualMean := by
    exact hres d u hu e a ha0 (quadraticBankDirection (d+1) u y)
      (quadraticBankDirection_tangent u hu y)
      (quadraticBankDirection_norm_sq (by omega : 0 < d+1) u y hy)
  obtain ⟨hfullInt,hfullEq⟩ := pure_palm_determinant_latitude_angular_factorization
    p hp alpha halpha hμ h.overlap_range.1 a β ha0 u hu e residualMean
    (fun y => originalLatitudeBankPoint_det_integrable_pure_of_det_sq
      p hp alpha halpha Q a β u hu e (hpd u hu e he) y)
    hres' (hbd u hu e he b hb hbbank a ha).1
  obtain ⟨_,hDZle⟩ := hbd u hu e he b hb hbbank a ha
  have hdetMean := (hdd u hu e he 2 (by norm_num)).2.1
  let detMean := ∫ J, intrinsicDet μ Q u J
    ∂pureLaw p hp alpha halpha Q u hu e
  let m := Real.exp (β^2*((d+2:ℕ):ℝ)*sourceQuadraticLatitudeVariance μ a/2)
  have hexp : residualMean*m =
      Real.exp (((d+2:ℕ):ℝ)*
        (β*e*(a/Real.sqrt Q)^p+
          β^2/2*sourcePureLatitudeVariance p alpha a)) := by
    dsimp [residualMean,m]
    rw [← Real.exp_add]
    congr 1
    ring
  have hfinal : (∫ J, intrinsicDet μ Q u J *
      originalLatitudeBankPartition μ a β u J
      ∂pureLaw p hp alpha halpha Q u hu e) ≤
        C * physicalMean d (d+2) (Q^2*μ.xi2 Q) ((p:ℝ)*e) *
          Real.exp (((d+2:ℕ):ℝ)*
            (β*e*(a/Real.sqrt Q)^p+
              β^2/2*sourcePureLatitudeVariance p alpha a)) := by
    rw [hfullEq]
    calc
      _ ≤ residualMean * (detMean*m*Real.sqrt K*Real.sqrt Cb) :=
        mul_le_mul_of_nonneg_left hDZle (Real.exp_pos _).le
      _ = C * physicalMean d (d+2) (Q^2*μ.xi2 Q) ((p:ℝ)*e) *
          Real.exp (((d+2:ℕ):ℝ)*
            (β*e*(a/Real.sqrt Q)^p+
              β^2/2*sourcePureLatitudeVariance p alpha a)) := by
        rw [show detMean = physicalMean d (d+2) (Q^2*μ.xi2 Q) ((p:ℝ)*e)
          from hdetMean]
        rw [←hexp]
        dsimp [C]
        ring
  simpa only [originalLatitudeBankPartition_eq_physical] using
    (show Integrable (fun J => intrinsicDet μ Q u J *
      originalLatitudeBankPartition μ a β u J)
      (pureLaw p hp alpha halpha Q u hu e) ∧
    (∫ J, intrinsicDet μ Q u J * originalLatitudeBankPartition μ a β u J
      ∂pureLaw p hp alpha halpha Q u hu e) ≤
      C * physicalMean d (d+2) (Q^2*μ.xi2 Q) ((p:ℝ)*e) *
        Real.exp (((d+2:ℕ):ℝ)*
          (β*e*(a/Real.sqrt Q)^p+
            β^2/2*sourcePureLatitudeVariance p alpha a))
      from ⟨hfullInt,hfinal⟩)

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
