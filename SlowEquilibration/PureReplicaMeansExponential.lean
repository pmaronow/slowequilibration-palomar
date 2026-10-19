-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.MixedReplicaMeanEnergyAssembly
public import SlowEquilibration.SphericalPureCapSourceScalars

/-! The exponential form of manuscript `prop:pc-replica-means` in
`sections/09-purecover.tex`. For the amplitude-one pure model at a
certificate, Chen's pressure limit and Subag's Proposition 24 give one
positive overlap tolerance and one positive exponential rate before the
fixed replica count is chosen. The contact-mean assembly is repeated only
to retain this stronger quantifier order: its good-event exponent is
bounded below using the replica count at least one. The endpoint uses the
same original disorder and Gibbs law, the literal center field, the
normalized empirical mean, and the explicit source energy
`E₀ = e_p * (sqrt Q)^p`. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.PureReplicaMeansExponential

open Set Filter MeasureTheory ProbabilityTheory SphericalModel SphericalTAPCertificate
open SourceLiteratureParisi LiteratureSubagProposition24
open PureCapturePhysicalCoarseTransfer MixedCapturePhysicalReplicaGeometry
open LiteratureSubagPhysicalDefinitions SphericalGaussianJet TwoAtomStationarity
open ReplicaMeanNetCover ReplicaBandGibbsMass ReplicaBandExpectedUpper
open MixedReplicaMeanEnergyAssembly SphericalBarycenter MixedCaptureReplicaGeometry
open PureStationarity
open SphericalAging.HardSphereDynamics
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The annealed expectation is an integral of a genuine bounded Borel
original-disorder probability. -/
private lemma contactReplicaMeanLowEnergy_probability_integrable {n k : ℕ}
    (μ : FiniteMixture) (β Q η E ε : ℝ) :
    Integrable (fun J : Disorder (n + 2) μ.maxDegree =>
      (Measure.pi (fun _ : Fin k => gibbsLaw (n + 2) β
        (field (mixtureCoefficients μ) J))).real (contactReplicaMeanLowEnergy μ J Q η E ε))
      (disorderLaw (n + 2) μ.maxDegree) := by
  let G := allDimensionGibbsKernel (N := n + 2) (mixtureCoefficients μ) β
  have h := (Kernel.measurable_kernel_prodMk_left
    (κ := GaussianReplicaKernel.iid G k)
      (joint_contactReplicaMeanLowEnergy_measurable (k := k) μ Q η E ε)).ennreal_toReal
  have hm : Measurable (fun J : Disorder (n + 2) μ.maxDegree =>
      (Measure.pi (fun _ : Fin k => gibbsLaw (n + 2) β
        (field (mixtureCoefficients μ) J))).real (contactReplicaMeanLowEnergy μ J Q η E ε)) := by
    convert h using 1
    funext J
    simp only [GaussianReplicaKernel.iid_apply, G, allDimensionGibbsKernel_apply]
    rfl
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact .of_forall fun J => by
    let : IsProbabilityMeasure (gibbsLaw (n + 2) β (field (mixtureCoefficients μ) J)) :=
      gibbsLaw_probability (by omega) β (field_contDiff (mixtureCoefficients μ) J).continuous
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one


/-- The built original-disorder regularity event supplies the ball Lipschitz
estimate used in the geometry-of-the-mean paragraph. -/
private lemma regular_ball_lipschitz {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (J : Disorder N P) (hJ : J ∈ regularDisorder)
    (u v : Vector N) (hu : ‖u‖ ≤ Real.sqrt (N : ℝ))
    (hv : ‖v‖ ≤ Real.sqrt (N : ℝ)) :
    |field c J u - field c J v| ≤
      derivativeConstant c * Real.sqrt (N : ℝ) * ‖u - v‖ := by
  have hb : ∀ z ∈ Metric.closedBall (0 : Vector N) (Real.sqrt (N : ℝ)),
      ‖fderiv ℝ (field c J) z‖ ≤ derivativeConstant c * Real.sqrt (N : ℝ) := by
    intro z hz
    have hg := (field_regularDisorder_ball_bounds hN c J hJ z
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)).2.1
    simpa only [gradient, LinearIsometryEquiv.norm_map] using hg
  simpa only [Real.norm_eq_abs] using
    (convex_closedBall (0 : Vector N) (Real.sqrt (N : ℝ))).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (field_contDiff c J).differentiable (by simp) z) hb
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hv)
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hu)

/-- Deterministic cover of the low-energy event by bands at low-energy net
points, on the contact sphere of a general finite mixture. -/
private lemma deterministic_low_energy_cover (μ : FiniteMixture)
    {N k M : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k)
    {Q η δ ρ ϑ E ε : ℝ} (hQ : Q ∈ Ioo (0 : ℝ) 1)
    (hη : 0 ≤ η) (hηQ : η < Q / 2) (hηρ : η ≤ ρ)
    (hgeometry : (2 * Real.sqrt 2 + 1) * η + 1 / (k : ℝ) + ϑ ≤ δ * Real.sqrt Q)
    (hLip : derivativeConstant (mixtureCoefficients μ) *
      ϑ ≤ ε / 4)
    (points : Fin M → Vector N)
    (hnorm : ∀ j, ‖points j‖ = Real.sqrt (N : ℝ) * Real.sqrt Q)
    (hnet : ∀ m : Vector N, ‖m‖ = Real.sqrt (N : ℝ) * Real.sqrt Q →
      ∃ j, ‖m - points j‖ ≤ ϑ * Real.sqrt (N : ℝ))
    (J : Disorder N μ.maxDegree)
    (hJ : J ∈ regularDisorder) (σ : Fin k → Vector N)
    (hσ : ∀ i, OnSphere (σ i))
    (hlow : σ ∈ contactReplicaMeanLowEnergy μ J Q η E ε) :
    ∃ j, σ ∈ ReplicatedBand k Q δ ρ (points j) ∧
      field (mixtureCoefficients μ) J (points j) ≤
        (N : ℝ) * (E - 3 * ε / 4) := by
  have hpair := hlow.1
  have hcm := physicalContactMean_norm_sq hN (by omega) σ hσ hQ hη hηQ
    (fun i j hij => (hpair i j hij).le)
  have hroot : Real.sqrt Q ≤ 1 := (Real.sqrt_le_one).mpr hQ.2.le
  have hcmnorm : ‖physicalContactMean Q σ‖ = Real.sqrt (N : ℝ) * Real.sqrt Q := by
    rw [← Real.sqrt_sq (norm_nonneg (physicalContactMean Q σ)), hcm,
      Real.sqrt_mul (Nat.cast_nonneg N)]
  obtain ⟨j, hj⟩ := hnet _ hcmnorm
  have hj' : ‖points j - physicalContactMean Q σ‖ ≤ ϑ * Real.sqrt (N : ℝ) := by
    simpa only [norm_sub_rev] using hj
  refine ⟨j, mem_replicatedBand_of_near_contactMean hN hk hQ hη hηQ hηρ
    hgeometry σ hσ hpair (points j) hj', ?_⟩
  have henergy : field (mixtureCoefficients μ) J
      (physicalContactMean Q σ) ≤ (N : ℝ) * (E - ε) := hlow.2
  have hball (m : Vector N) (hm : ‖m‖ = Real.sqrt (N : ℝ) * Real.sqrt Q) :
      ‖m‖ ≤ Real.sqrt (N : ℝ) := by
    rw [hm]
    exact mul_le_of_le_one_right (Real.sqrt_nonneg _) hroot
  have hl := regular_ball_lipschitz hN (mixtureCoefficients μ) J hJ (points j) (physicalContactMean Q σ)
    (hball _ (hnorm j)) (hball _ hcmnorm)
  have herror : |field (mixtureCoefficients μ) J
      (points j) - field (mixtureCoefficients μ) J
      (physicalContactMean Q σ)| ≤ (N : ℝ) * (ε / 4) := by
    calc
      _ ≤ derivativeConstant (mixtureCoefficients μ) *
          Real.sqrt (N : ℝ) * (ϑ * Real.sqrt (N : ℝ)) :=
        hl.trans (mul_le_mul_of_nonneg_left hj'
          (mul_nonneg (derivativeConstant_pos _).le (Real.sqrt_nonneg _)))
      _ = (N : ℝ) *
          (derivativeConstant (mixtureCoefficients μ) * ϑ) := by
        calc
          _ = (derivativeConstant (mixtureCoefficients μ) * ϑ) *
              (Real.sqrt (N : ℝ)) ^ 2 := by ring
          _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg N)]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hLip (Nat.cast_nonneg N)
  linarith [le_abs_self (field (mixtureCoefficients μ) J
    (points j) - field (mixtureCoefficients μ) J
    (physicalContactMean Q σ))]

/-- The union over the net on the good disorder event. Zero-volume bands
are removed before applying the expected-pressure estimate. -/
private lemma on_event_gibbs_bound {N k M : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k)
    (μ : FiniteMixture) {β Q η δ ρ E ε T A : ℝ} (hβ : 0 < β)
    (points : Fin M → Vector N) (hM : 0 < M)
    (hnorm : ∀ j, ‖points j‖ ^ 2 = (N : ℝ) * Q)
    (hcard : Real.log (M : ℝ) ≤ (N : ℝ) * A)
    (hbeat : A ≤ (k : ℝ) * β * ε / 8)
    (J : Disorder N μ.maxDegree)
    (hcover : ∀ σ : Fin k → Vector N, (∀ i, OnSphere (σ i)) →
      σ ∈ contactReplicaMeanLowEnergy μ J Q η E ε →
      ∃ j, σ ∈ ReplicatedBand k Q δ ρ (points j) ∧
        field (mixtureCoefficients μ) J (points j) ≤ (N : ℝ) * (E - 3 * ε / 4))
    (hpressure : β * E + T - β * ε / 8 ≤
      Real.log (mixturePartition μ β J) / (N : ℝ))
    (hupper : ∀ m : Vector N, ‖m‖ ^ 2 = (N : ℝ) * Q →
      replicatedBandPressure k μ β Q δ ρ J m <
        expectedReplicatedBandPressure k μ β Q δ ρ m + β * ε / 8)
    (hexpected : ∀ m : Vector N, ‖m‖ ^ 2 = (N : ℝ) * Q →
      0 < (Measure.pi (fun _ : Fin k => sphereLaw N)) (ReplicatedBand k Q δ ρ m) →
      expectedReplicatedBandPressure k μ β Q δ ρ m ≤ T + β * ε / 8) :
    (Measure.pi (fun _ : Fin k => gibbsLaw N β (field (mixtureCoefficients μ) J))).real
      (contactReplicaMeanLowEnergy μ J Q η E ε) ≤
        Real.exp (-(N : ℝ) * (k : ℝ) * β * ε / 4) := by
  classical
  let π := gibbsLaw N β (field (mixtureCoefficients μ) J)
  let ν := Measure.pi (fun _ : Fin k => π)
  let : IsProbabilityMeasure π := gibbsLaw_probability hN β (field_contDiff _ J).continuous
  let B : Fin M → Set (Fin k → Vector N) := fun j =>
    {σ | field (mixtureCoefficients μ) J (points j) ≤ (N : ℝ) * (E - 3 * ε / 4) ∧
      σ ∈ ReplicatedBand k Q δ ρ (points j)}
  have ha : ∀ᵐ σ ∂ν, ∀ i, OnSphere (σ i) :=
    eventually_all.mpr (fun i => (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin k => π) (i := i)).eventually
      ((gibbsLaw_support hN β (field (mixtureCoefficients μ) J)).mono
        (fun x hx => (onSphere_iff_norm_sq x).mpr hx)))
  have hsub : contactReplicaMeanLowEnergy μ J Q η E ε ≤ᵐ[ν] ⋃ j, B j := by
    filter_upwards [ha] with σ hσ hl
    obtain ⟨j, hj, he⟩ := hcover σ hσ hl
    exact mem_iUnion.mpr ⟨j, he, hj⟩
  have hband (j : Fin M) : ν.real (B j) ≤
      Real.exp (-(N : ℝ) * (k : ℝ) * (3 * β * ε / 8)) := by
    by_cases he : field (mixtureCoefficients μ) J (points j) ≤
        (N : ℝ) * (E - 3 * ε / 4)
    · have hs : B j ⊆ ReplicatedBand k Q δ ρ (points j) := fun σ hσ => hσ.2
      apply (measureReal_mono hs).trans
      by_cases hv : (Measure.pi (fun _ : Fin k => sphereLaw N))
          (ReplicatedBand k Q δ ρ (points j)) = 0
      · rw [show ν.real (ReplicatedBand k Q δ ρ (points j)) = 0 from
          productGibbs_band_eq_zero_of_volume_zero hN μ β Q δ ρ J (points j) hv]
        exact (Real.exp_pos _).le
      · have hA : replicatedBandPressure k μ β Q δ ρ J (points j) < T + β * ε / 4 := by
          have hu := hupper _ (hnorm j)
          have hx := hexpected _ (hnorm j) (pos_iff_ne_zero.mpr hv)
          linarith
        have hb := productGibbs_band_le hN hk μ β Q δ ρ J (points j) hA
        apply hb.trans (Real.exp_le_exp.mpr ?_)
        have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
        have he' : β * field (mixtureCoefficients μ) J (points j) / (N : ℝ) ≤
            β * (E - 3 * ε / 4) := by
          apply (div_le_iff₀ hNr).mpr
          nlinarith [mul_le_mul_of_nonneg_left he hβ.le]
        have hh : β * field (mixtureCoefficients μ) J (points j) / (N : ℝ) +
            (T + β * ε / 4) - Real.log (mixturePartition μ β J) / (N : ℝ) ≤
              -(3 * β * ε / 8) := by linarith
        calc
          _ ≤ (N : ℝ) * (k : ℝ) * (-(3 * β * ε / 8)) :=
            mul_le_mul_of_nonneg_left hh (by positivity)
          _ = _ := by ring
    · have hz : B j = ∅ := by ext σ; simp [B, he]
      rw [hz, measureReal_empty]
      exact (Real.exp_pos _).le
  calc
    _ ≤ ν.real (⋃ j, B j) := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
    _ ≤ ∑ j, ν.real (B j) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin M, Real.exp (-(N : ℝ) * (k : ℝ) * (3 * β * ε / 8)) :=
      Finset.sum_le_sum (fun j _ => hband j)
    _ = (M : ℝ) * Real.exp (-(N : ℝ) * (k : ℝ) * (3 * β * ε / 8)) := by simp
    _ ≤ Real.exp ((N : ℝ) * A) *
        Real.exp (-(N : ℝ) * (k : ℝ) * (3 * β * ε / 8)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      rw [← Real.exp_log (Nat.cast_pos.mpr hM)]
      exact Real.exp_le_exp.mpr hcard
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hbeat (Nat.cast_nonneg N)
      nlinarith

/-- All tolerances and the replica threshold are fixed before the dimension
limit. Continuity at zero controls the expected-band error simultaneously. -/
private lemma choose_parameters {Q β ε C L δ₀ ρ₀ : ℝ}
    (hQ : Q ∈ Ioo (0 : ℝ) 1) (hβ : 0 < β) (hε : 0 < ε)
    (hC : 0 < C) (hL : 0 < L) (hδ₀ : 0 < δ₀) (hρ₀ : 0 < ρ₀) (K : ℕ) :
    ∃ δ ρ ϑ η : ℝ, ∃ k₀ : ℕ,
      0 < δ ∧ δ ≤ δ₀ ∧ δ ≤ Real.sqrt Q / 2 ∧ δ ≤ (1 - Real.sqrt Q) / 2 ∧
      0 < ρ ∧ ρ ≤ ρ₀ ∧ 0 < ϑ ∧ L * ϑ ≤ ε / 4 ∧
      0 < η ∧ η < Q / 2 ∧ η ≤ ρ ∧
      ∀ k : ℕ, k₀ ≤ k → K ≤ k ∧ 1 ≤ k ∧
        (2 * Real.sqrt 2 + 1) * η + 1 / (k : ℝ) + ϑ ≤ δ * Real.sqrt Q ∧
        Real.log (1 + 2 * Real.sqrt Q / ϑ) ≤ (k : ℝ) * β * ε / 8 ∧
        C * (Real.sqrt δ +
          Real.sqrt (1 / (k : ℝ) + (ρ + Real.sqrt (8 * δ)) / (1 - Q))) ≤ β * ε / 16 := by
  have hr : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ.1
  have hQpos : 0 < Q := hQ.1
  have hr1 : Real.sqrt Q < 1 := by
    nlinarith [Real.sq_sqrt hQ.1.le, Real.sqrt_nonneg Q, hQ.2]
  let f : ℝ → ℝ := fun u => C * (Real.sqrt u +
    Real.sqrt (u + (u + Real.sqrt (8 * u)) / (1 - Q)))
  have hf : ContinuousAt f 0 := by dsimp [f]; fun_prop
  have hf0 : f 0 = 0 := by simp [f]
  have hsmall : ∀ᶠ u in 𝓝 (0 : ℝ), f u < β * ε / 16 :=
    hf.tendsto.eventually_lt_const (by rw [hf0]; positivity)
  obtain ⟨r, hrpos, hrsmall⟩ := Metric.eventually_nhds_iff.mp hsmall
  let δ := min δ₀ (min (Real.sqrt Q / 2)
    (min ((1 - Real.sqrt Q) / 2) (min ρ₀ (r / 2))))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδδ₀ : δ ≤ δ₀ := min_le_left _ _
  have hδq : δ ≤ Real.sqrt Q / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ1 : δ ≤ (1 - Real.sqrt Q) / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδρ : δ ≤ ρ₀ := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδr : δ ≤ r / 2 := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hfδ : f δ < β * ε / 16 := hrsmall (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ]; linarith)
  let ϑ := min (δ * Real.sqrt Q / 4) (ε / (4 * L))
  have hϑ : 0 < ϑ := by dsimp [ϑ]; positivity
  have hϑδ : ϑ ≤ δ * Real.sqrt Q / 4 := min_le_left _ _
  have hLϑ : L * ϑ ≤ ε / 4 := by
    have hh := (min_le_right (δ * Real.sqrt Q / 4) (ε / (4 * L)))
    have hh' := (le_div_iff₀ (show 0 < 4 * L by positivity)).mp hh
    dsimp only [ϑ]
    linarith
  let η := min (Q / 4) (min (δ / 2) (δ * Real.sqrt Q / 32))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηQ : η < Q / 2 := lt_of_le_of_lt (min_le_left _ _) (by linarith [hQ.1])
  have hηρ : η ≤ δ := (min_le_right _ _).trans
    ((min_le_left _ _).trans (by linarith))
  have hηδ : η ≤ δ * Real.sqrt Q / 32 :=
    (min_le_right _ _).trans (min_le_right _ _)
  let A := Real.log (1 + 2 * Real.sqrt Q / ϑ)
  obtain ⟨B, hB⟩ := exists_nat_gt (8 * A / (β * ε))
  have hlarge : ∀ᶠ k : ℕ in atTop,
      K ≤ k ∧ 1 ≤ k ∧ 1 / (k : ℝ) ≤ min δ (δ * Real.sqrt Q / 4) ∧ B ≤ k := by
    filter_upwards [eventually_ge_atTop K, eventually_ge_atTop (1 : ℕ),
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually_lt_const
        (show 0 < min δ (δ * Real.sqrt Q / 4) by positivity),
      eventually_ge_atTop B] with k hK hk hi hBk
    exact ⟨hK, hk, hi.le, hBk⟩
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp hlarge
  refine ⟨δ, δ, ϑ, η, k₀, hδ, hδδ₀, hδq, hδ1, hδ, hδρ, hϑ, hLϑ,
    hη, hηQ, hηρ, ?_⟩
  intro k hk
  obtain ⟨hK, hk1, hi, hBk⟩ := hk₀ k hk
  have hiδ : 1 / (k : ℝ) ≤ δ := hi.trans (min_le_left _ _)
  have hiq : 1 / (k : ℝ) ≤ δ * Real.sqrt Q / 4 := hi.trans (min_le_right _ _)
  refine ⟨hK, hk1, ?_, ?_, ?_⟩
  · have hc2 : 2 * Real.sqrt 2 + 1 ≤ 5 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    have hcη := mul_le_mul_of_nonneg_right hc2 hη.le
    nlinarith [mul_pos hδ hr]
  · have hcast : (B : ℝ) ≤ k := by exact_mod_cast hBk
    have hh : 8 * A / (β * ε) ≤ (k : ℝ) := hB.le.trans hcast
    have hh' := (div_le_iff₀ (mul_pos hβ hε)).mp hh
    dsimp only [A] at hh'
    nlinarith
  · have hmono : C * (Real.sqrt δ +
        Real.sqrt (1 / (k : ℝ) + (δ + Real.sqrt (8 * δ)) / (1 - Q))) ≤ f δ := by
      dsimp only [f]
      gcongr
    exact hmono.trans hfδ.le

/-- Probability of the complement of the intersection of regularity,
lower pressure, and the fixed-parameter Proposition 24 event. -/
private lemma good_event_failure_bound {N : ℕ} (hN : 2 ≤ N)
    (μ : FiniteMixture) (β F t : ℝ) (Ω : Set (Disorder N μ.maxDegree))
    (hΩ : MeasurableSet Ω)
    (hprob : 1 - Real.exp (-(N : ℝ)) < (disorderLaw N μ.maxDegree).real Ω) :
    (disorderLaw N μ.maxDegree).real
      (regularDisorder ∩
        {J | Real.log (mixturePartition μ β J) / (N : ℝ) < F - t}ᶜ ∩ Ω)ᶜ ≤
      2 * Real.exp (-(N : ℝ)) + (disorderLaw N μ.maxDegree).real
        {J | Real.log (mixturePartition μ β J) / (N : ℝ) < F - t} := by
  have hc : (disorderLaw N μ.maxDegree).real Ωᶜ ≤ Real.exp (-(N : ℝ)) := by
    rw [measureReal_compl hΩ, probReal_univ]
    linarith
  simp only [compl_inter, compl_compl]
  exact (measureReal_union_le _ _).trans (by
    have hu := measureReal_union_le (μ := disorderLaw N μ.maxDegree)
      (regularDisorder (N := N) (P := μ.maxDegree))ᶜ
      {J | Real.log (mixturePartition μ β J) / (N : ℝ) < F - t}
    have hr := regularDisorder_failure_probability (P := μ.maxDegree) hN
    linarith)

/-- Integrating a product Gibbs bound on a measurable good disorder event
costs only the probability of its complement. -/
private lemma expected_low_energy_le_failure {n k : ℕ}
    (μ : FiniteMixture) (β Q η E ε : ℝ)
    (G : Set (Disorder (n + 2) μ.maxDegree)) (hG : MeasurableSet G)
    {b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ J ∈ G,
      (Measure.pi (fun _ : Fin k => gibbsLaw (n + 2) β (field (mixtureCoefficients μ) J))).real
        (contactReplicaMeanLowEnergy μ J Q η E ε) ≤ b) :
    expectedContactReplicaMeanLowEnergy (k := k) n μ β Q η E ε ≤
      (disorderLaw (n + 2) μ.maxDegree).real Gᶜ + b := by
  have hi : Integrable (Gᶜ.indicator (fun _ => (1 : ℝ)))
      (disorderLaw (n + 2) μ.maxDegree) := (integrable_const 1).indicator hG.compl
  calc
    _ ≤ ∫ J, Gᶜ.indicator (fun _ => (1 : ℝ)) J + b
        ∂disorderLaw (n + 2) μ.maxDegree := by
      apply integral_mono (contactReplicaMeanLowEnergy_probability_integrable μ β Q η E ε)
        (hi.add (integrable_const b))
      intro J
      change (Measure.pi (fun _ : Fin k => gibbsLaw (n + 2) β
        (field (mixtureCoefficients μ) J))).real (contactReplicaMeanLowEnergy μ J Q η E ε) ≤
          Gᶜ.indicator (fun _ => (1 : ℝ)) J + b
      by_cases hJ : J ∈ G
      · simpa only [Set.indicator_of_notMem (show J ∉ Gᶜ by simpa only [mem_compl_iff, not_not] using hJ), zero_add]
          using hbound J hJ
      · let : IsProbabilityMeasure (gibbsLaw (n + 2) β (field (mixtureCoefficients μ) J)) :=
          gibbsLaw_probability (by omega) β (field_contDiff _ J).continuous
        rw [Set.indicator_of_mem (show J ∈ Gᶜ from hJ)]
        exact measureReal_le_one.trans (by linarith)
    _ = _ := by
      rw [integral_add hi (integrable_const b), integral_indicator_const (1 : ℝ) hG.compl]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_one]

/-- A common positive overlap tolerance works for every sufficiently
large fixed replica count, on measurable original-disorder events. -/
private lemma mixed_contact_replica_good_events
    (μ : FiniteMixture) {β x Q ε : ℝ} (h : Certificate μ β x Q)
    (h24 : Proposition24 μ β Q) (hε : 0 < ε) :
    ∃ k₀ : ℕ, ∃ η : ℝ, 0 < η ∧ ∀ k : ℕ, k₀ ≤ k → 1 ≤ k ∧
      ∀ᶠ n : ℕ in atTop, ∃ G : Set (Disorder (n + 2) μ.maxDegree),
        MeasurableSet G ∧ (disorderLaw (n + 2) μ.maxDegree).real Gᶜ ≤
          2 * Real.exp (-(n + 2 : ℕ)) + (disorderLaw (n + 2) μ.maxDegree).real
            {J | Real.log (mixturePartition μ β J) / (n + 2 : ℕ) <
              CSParisiMeasure.variationalValue μ β - β * ε / 8} ∧
        ∀ J ∈ G,
          (Measure.pi (fun _ : Fin k => gibbsLaw (n + 2) β
            (field (mixtureCoefficients μ) J))).real
              (contactReplicaMeanLowEnergy μ J Q η (markE μ β x Q) ε) ≤
                Real.exp (-(n + 2 : ℕ) * (k : ℝ) * β * ε / 4) := by
  classical
  have hβ : 0 < β := h.beta_pos
  have hQ : Q ∈ Ioo (0 : ℝ) 1 := h.overlap_range
  let E := TwoAtomStationarity.markE μ β x Q
  let T := Real.log (1 - Q) / 2 + β ^ 2 * TwoAtomStationarity.residualAtOne μ Q / 2
  let F := CSParisiMeasure.variationalValue μ β
  have hTAP : F = β * E + T := by
    have hh := h.variational_TAP
    dsimp only [F, E, T]
    linarith
  obtain ⟨δ₀, hδ₀, ρ₀, hρ₀, K, hfixed⟩ :=
    fixedParameters_uniform_upper μ β Q h24
      (t := β * ε / 8) (c := 1) (by positivity) (by norm_num)
  obtain ⟨C, hC, hCupper⟩ := expectedReplicatedBandPressure_upper μ hβ hQ
  obtain ⟨δ, ρ, ϑ, η, k₀, hδ, hδδ₀, hδq, hδ1, hρ, hρρ₀, hϑ, hLip,
      hη, hηQ, hηρ, hparams⟩ := choose_parameters hQ hβ hε hC
    (derivativeConstant_pos (mixtureCoefficients μ)) hδ₀ hρ₀ K
  refine ⟨k₀, η, hη, ?_⟩
  intro k hk₀
  obtain ⟨hK, hk, hgeometry, hbeat, herror⟩ := hparams k hk₀
  have hupper := hCupper δ hδ hδq hδ1 ρ hρ k hk (β * ε / 16) (by positivity)
  have hshift : Tendsto (fun n : ℕ => n + 2) atTop atTop := tendsto_add_atTop_nat 2
  refine ⟨hk, ?_⟩
  have hdim : ∀ᶠ n : ℕ in atTop,
      k + 1 ≤ n + 2 ∧ ∀ m : Vector (n + 2), ‖m‖ ^ 2 = (n + 2 : ℕ) * Q →
        0 < (Measure.pi (fun _ : Fin k => sphereLaw (n + 2))) (ReplicatedBand k Q δ ρ m) →
        expectedReplicatedBandPressure k μ β Q δ ρ m ≤ T + β * ε / 8 := by
    have hU : ∀ᶠ n in atTop, ∀ m : Vector (n + 2), ‖m‖ ^ 2 = (n + 2 : ℕ) * Q →
        0 < (Measure.pi (fun _ : Fin k => sphereLaw (n + 2))) (ReplicatedBand k Q δ ρ m) →
        expectedReplicatedBandPressure k μ β Q δ ρ m ≤
          T + C * (Real.sqrt δ +
            Real.sqrt (1 / (k : ℝ) + (ρ + Real.sqrt (8 * δ)) / (1 - Q))) + β * ε / 16 :=
      hshift.eventually hupper
    filter_upwards [hU, hshift.eventually (eventually_ge_atTop (k + 1))] with n hUn hn
    refine ⟨hn, ?_⟩
    intro m hm hv
    have hh := hUn m hm hv
    linarith
  filter_upwards [hdim] with n hn
  obtain ⟨Ω, hΩ, hΩprob, hΩupper⟩ := hfixed δ hδ hδδ₀ ρ hρ hρρ₀ k hK (n + 2) hn.1
  have hΩprob' : 1 - Real.exp (-(n + 2 : ℕ)) < (disorderLaw (n + 2) μ.maxDegree).real Ω := by
    simpa only [neg_one_mul] using hΩprob
  let B : Set (Disorder (n + 2) μ.maxDegree) :=
    {J | Real.log (mixturePartition μ β J) / (n + 2 : ℕ) < F - β * ε / 8}
  let G : Set (Disorder (n + 2) μ.maxDegree) := regularDisorder ∩ Bᶜ ∩ Ω
  have hB : MeasurableSet B :=
    PhysicalPressureLowerDeviation.pressure_lower_deviation_measurable μ β F (β * ε / 8) _
  have hG : MeasurableSet G := ((regularDisorder_measurable _ _).inter hB.compl).inter hΩ
  refine ⟨G, hG, good_event_failure_bound (by omega) μ β F (β * ε / 8) Ω hΩ hΩprob', ?_⟩
  intro J hJG
  obtain ⟨⟨hreg, hpress⟩, hJΩ⟩ := hJG
  have hpress' : β * E + T - β * ε / 8 ≤
      Real.log (mixturePartition μ β J) / (n + 2 : ℕ) := by
    have hh : F - β * ε / 8 ≤ Real.log (mixturePartition μ β J) / (n + 2 : ℕ) :=
      le_of_not_gt hpress
    rwa [hTAP] at hh
  obtain ⟨M, points, hM, hnorm, hnet, hcard⟩ :=
    SourcePureCaptureReplicaNetGeometry.exists_physical_center_net (n + 2) (by omega) hQ.1 hϑ
  have hnormsq : ∀ j, ‖points j‖ ^ 2 = (n + 2 : ℕ) * Q := by
    intro j
    rw [hnorm j, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt hQ.1.le]
  have hcover : ∀ σ : Fin k → Vector (n + 2), (∀ i, OnSphere (σ i)) →
      σ ∈ contactReplicaMeanLowEnergy μ J Q η E ε →
      ∃ j, σ ∈ ReplicatedBand k Q δ ρ (points j) ∧
        field (mixtureCoefficients μ) J (points j) ≤ (n + 2 : ℕ) * (E - 3 * ε / 4) := by
    intro σ hσ hl
    exact deterministic_low_energy_cover μ (by omega) hk hQ hη.le hηQ hηρ
      hgeometry hLip points hnorm hnet J hreg σ hσ hl
  have hb := on_event_gibbs_bound (by omega) hk μ hβ points hM hnormsq hcard hbeat J
    hcover hpress' (hΩupper J hJΩ) hn.2
  exact hb

/-- Shrinking the overlap tolerance can only shrink the original-model
low-energy event and its annealed probability. -/
private lemma expected_contact_low_energy_mono {n k : ℕ} (μ : FiniteMixture)
    (β Q E ε : ℝ) {η η' : ℝ} (hη : η ≤ η') :
    expectedContactReplicaMeanLowEnergy (k := k) n μ β Q η E ε ≤
      expectedContactReplicaMeanLowEnergy (k := k) n μ β Q η' E ε := by
  apply integral_mono (contactReplicaMeanLowEnergy_probability_integrable μ β Q η E ε)
    (contactReplicaMeanLowEnergy_probability_integrable μ β Q η' E ε)
  intro J
  let : IsProbabilityMeasure (gibbsLaw (n + 2) β (field (mixtureCoefficients μ) J)) :=
    gibbsLaw_probability (by omega) β (field_contDiff _ J).continuous
  exact measureReal_mono (fun σ hσ =>
    ⟨fun i j hij => (hσ.1 i j hij).trans_le hη, hσ.2⟩) (measure_ne_top _ _)

/-- The regularity, pressure and net errors have a common positive
exponential rate; their fixed prefactor is absorbed for large dimensions. -/
private lemma exponential_error_sum {d a : ℝ} (hd : 0 < d) (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      2 * Real.exp (-(n + 2 : ℕ)) + 2 * Real.exp (-d * (n + 2 : ℕ)) +
        Real.exp (-a * (n + 2 : ℕ)) ≤ Real.exp (-c * (n + 2 : ℕ)) := by
  let b : ℝ := min 1 (min d a)
  have hb : 0 < b := lt_min (by norm_num) (lt_min hd ha)
  have hb1 : b ≤ 1 := min_le_left _ _
  have hbd : b ≤ d := (min_le_right _ _).trans (min_le_left _ _)
  have hba : b ≤ a := (min_le_right _ _).trans (min_le_right _ _)
  let c : ℝ := b / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hexp : Tendsto (fun n : ℕ => Real.exp (-c * (n + 2 : ℕ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)).const_mul_atTop_of_neg
        (neg_neg_of_pos hc))
  refine ⟨c, hc, ?_⟩
  filter_upwards [hexp.eventually_lt_const (show (0 : ℝ) < 1 / 5 by norm_num)] with n hn
  have hN : (0 : ℝ) ≤ (n + 2 : ℕ) := Nat.cast_nonneg _
  have h1 : Real.exp (-(n + 2 : ℕ)) ≤ Real.exp (-b * (n + 2 : ℕ)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hd' : Real.exp (-d * (n + 2 : ℕ)) ≤ Real.exp (-b * (n + 2 : ℕ)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have ha' : Real.exp (-a * (n + 2 : ℕ)) ≤ Real.exp (-b * (n + 2 : ℕ)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hsq : Real.exp (-b * (n + 2 : ℕ)) =
      Real.exp (-c * (n + 2 : ℕ)) * Real.exp (-c * (n + 2 : ℕ)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [c]
    ring
  calc
    _ ≤ 5 * Real.exp (-b * (n + 2 : ℕ)) := by linarith
    _ = (5 * Real.exp (-c * (n + 2 : ℕ))) * Real.exp (-c * (n + 2 : ℕ)) := by
      rw [hsq]
      ring
    _ ≤ 1 * Real.exp (-c * (n + 2 : ℕ)) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ = _ := one_mul _

/-- The good-disorder replica exponent has the lower bound `β ε / 4`
for every positive replica count. Thus the rate can be fixed before that
count, while the dimension threshold can still depend on it. -/
private lemma contact_replica_uniform_exponential
    (μ : FiniteMixture) {β x Q : ℝ} (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi) (h24 : Proposition24 μ β Q) :
    ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∃ η c : ℝ, 0 < η ∧ 0 < c ∧
      ∀ k : ℕ, k₀ ≤ k → ∀ᶠ n : ℕ in atTop,
        expectedContactReplicaMeanLowEnergy (k := k) n μ β Q η (markE μ β x Q) ε ≤
          Real.exp (-c * (n + 2 : ℕ)) := by
  intro ε hε
  have hβ : 0 < β := h.beta_pos
  have hxi : 0 < μ.xi 1 := μ.xi_pos (by norm_num)
  obtain ⟨k₀, η, hη, hgood⟩ := mixed_contact_replica_good_events μ h h24 hε
  let a : ℝ := β * ε / 4
  have ha : 0 < a := by dsimp only [a]; positivity
  let d : ℝ := (β * ε / 8) ^ 2 / (8 * β ^ 2 * μ.xi 1)
  have hd : 0 < d := by dsimp only [d]; positivity
  have hp := (tendsto_add_atTop_nat 2).eventually
    (PhysicalPressureLowerDeviation.pressure_lower_deviation_exponential μ hβ
      (hChen μ β hβ.le) (t := β * ε / 8) (by positivity))
  obtain ⟨c, hc, hsum⟩ := exponential_error_sum hd ha
  refine ⟨k₀, η, c, hη, hc, ?_⟩
  intro k hk₀
  obtain ⟨hk, hgood⟩ := hgood k hk₀
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  filter_upwards [hgood, hp, hsum] with n hn hpn hsn
  obtain ⟨G, hG, hGr, hGb⟩ := hn
  have hGb' : ∀ J ∈ G,
      (Measure.pi (fun _ : Fin k => gibbsLaw (n + 2) β
        (field (mixtureCoefficients μ) J))).real
          (contactReplicaMeanLowEnergy μ J Q η (markE μ β x Q) ε) ≤
            Real.exp (-a * (n + 2 : ℕ)) := by
    intro J hJ
    apply (hGb J hJ).trans
    apply Real.exp_le_exp.mpr
    dsimp only [a]
    have hh := mul_le_mul_of_nonneg_left hkr (mul_pos hβ hε).le
    have hN : (0 : ℝ) ≤ (n + 2 : ℕ) := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hh hN]
  have he := expected_low_energy_le_failure μ β Q η (markE μ β x Q) ε
    G hG (Real.exp_pos _).le hGb'
  have hp' : (disorderLaw (n + 2) μ.maxDegree).real
      {J | Real.log (mixturePartition μ β J) / (n + 2 : ℕ) <
        CSParisiMeasure.variationalValue μ β - β * ε / 8} ≤
          2 * Real.exp (-d * (n + 2 : ℕ)) := hpn
  have he' : expectedContactReplicaMeanLowEnergy (k := k) n μ β Q η
      (markE μ β x Q) ε ≤ 2 * Real.exp (-(n + 2 : ℕ)) +
        2 * Real.exp (-d * (n + 2 : ℕ)) + Real.exp (-a * (n + 2 : ℕ)) := by
    linarith
  exact he'.trans hsn

/-- The contact/center identity extends to the zero-mean tuple under total
normalization, so the two literal energy events agree everywhere. -/
private lemma center_field_trainingCenter_eq_contactMean {N k : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 ≤ Q) (J : Disorder N μ.maxDegree)
    (σ : Fin k → Vector N) :
    field (centerCoefficients (mixtureCoefficients μ) Q) J (physicalTrainingCenter σ) =
      field (mixtureCoefficients μ) J (physicalContactMean Q σ) := by
  have hroot : Real.sqrt (N : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < N by omega))).ne'
  have hs := congrArg (fun u : Vector N => Real.sqrt (N : ℝ) • u)
    (spin_physicalContactMean hN hQ σ)
  have hm : physicalContactMean Q σ = Real.sqrt Q • physicalTrainingCenter σ := by
    simpa only [spin, contactReplicaMean, physicalTrainingCenter, smul_smul,
      mul_inv_cancel₀ hroot, one_smul, mul_comm] using hs
  rw [field_center_scale _ (mixtureCoefficients_nonnegative μ) hQ, hm]

/-- Source `prop:pc-replica-means`, with `n₀`, `η` and `c` all chosen
before the fixed replica count `n`. Only the eventual dimension threshold
may depend on `n`. The source mean is well defined on the Gibbs event:
`η < Q / 2` and `n ≥ 1` give positive empirical mean norm by
`physicalMeanNormSq_pos`, and `physicalTrainingCenter_sphere` puts it on
`S_N`. No parity or further literature hypothesis is needed. -/
theorem pure_replica_means_exponential_of_literature
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (hChen : Chen2013FiniteParisi)
    (h24 : Proposition24 (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let E₀ := pureEnergyConstant p (by omega) * (Real.sqrt Q) ^ p
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∃ η c : ℝ,
      1 ≤ n₀ ∧ 0 < η ∧ η < Q / 2 ∧ 0 < c ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ᶠ N : ℕ in atTop,
        (∫ J : Disorder N μ.maxDegree,
          (Measure.pi (fun _ : Fin n =>
            gibbsLaw N β (field (mixtureCoefficients μ) J))).real
            {σ : Fin n → Vector N |
              (∀ i j : Fin n, i ≠ j → |overlap (σ i) (σ j) - Q| < η) ∧
              field (centerCoefficients (mixtureCoefficients μ) Q) J
                (physicalTrainingCenter σ) ≤ (N : ℝ) * (E₀ - ε)}
          ∂disorderLaw N μ.maxDegree) ≤ Real.exp (-c * (N : ℝ)) := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  have hE : markE μ β x Q = pureEnergyConstant p (by omega) * (Real.sqrt Q) ^ p :=
    (SphericalPureCapSourceScalars.sourcePure_certificate_scalar_coordinates p hp h).1
  intro ε hε
  obtain ⟨k₀, η₀, c, hη₀, hc, hbound⟩ :=
    contact_replica_uniform_exponential μ h hChen h24 ε hε
  let η := min η₀ (Q / 4)
  have hη : 0 < η := lt_min hη₀ (by linarith [h.overlap_range.1])
  have hηQ : η < Q / 2 := (min_le_right _ _).trans_lt (by linarith [h.overlap_range.1])
  refine ⟨max k₀ 1, η, c, le_max_right _ _, hη, hηQ, hc, ?_⟩
  intro n hn
  have hbound' := hbound n ((le_max_left _ _).trans hn)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hbound'
  refine eventually_atTop.mpr ⟨M + 2, ?_⟩
  intro N hN
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, N = m + 2 := ⟨N - 2, by omega⟩
  have hh := (expected_contact_low_energy_mono μ β Q (markE μ β x Q) ε
    (min_le_left η₀ (Q / 4))).trans (hM m (by omega))
  unfold expectedContactReplicaMeanLowEnergy at hh
  have heq :
      (∫ J : Disorder (m + 2) μ.maxDegree,
        (Measure.pi (fun _ : Fin n =>
          gibbsLaw (m + 2) β (field (mixtureCoefficients μ) J))).real
          {σ : Fin n → Vector (m + 2) |
            (∀ i j : Fin n, i ≠ j → |overlap (σ i) (σ j) - Q| < η) ∧
            field (centerCoefficients (mixtureCoefficients μ) Q) J
              (physicalTrainingCenter σ) ≤
                (m + 2 : ℕ) * (pureEnergyConstant p (by omega) * (Real.sqrt Q) ^ p - ε)}
        ∂disorderLaw (m + 2) μ.maxDegree) =
      ∫ J : Disorder (m + 2) μ.maxDegree,
        (Measure.pi (fun _ : Fin n =>
          gibbsLaw (m + 2) β (field (mixtureCoefficients μ) J))).real
          (contactReplicaMeanLowEnergy μ J Q η (markE μ β x Q) ε)
        ∂disorderLaw (m + 2) μ.maxDegree := by
    apply integral_congr_ae
    filter_upwards [] with J
    congr 1
    ext σ
    simp only [contactReplicaMeanLowEnergy, mem_ofPred_eq, hE,
      center_field_trainingCenter_eq_contactMean (by omega) μ h.overlap_range.1.le J σ]
  rw [heq]
  exact hh

end SlowEquilibration.PureReplicaMeansExponential
