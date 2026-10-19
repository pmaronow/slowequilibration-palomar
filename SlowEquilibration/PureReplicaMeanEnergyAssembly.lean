-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalCoarseDiniAssembly
public import SlowEquilibration.ReplicaBandGibbsMass
public import SlowEquilibration.ReplicaBandExpectedUpper
public import SlowEquilibration.PhysicalPressureLowerDeviation
public import SlowEquilibration.ReplicaMeanNetCover
public import SlowEquilibration.SourcePureCaptureReplicaNetGeometry
public import SlowEquilibration.SphericalPureCapSourceScalars
public import SlowEquilibration.SourceLiteratureParisi
public import SlowEquilibration.LiteratureSubagProposition24

/-! The replicated-mean energy premise of manuscript `prop:pc-replica-means`
for the pure model. A deterministic net covers low-energy replica means;
the TAP pressure identity and Subag's fixed-parameter concentration bound
make its product Gibbs mass vanish after averaging the original disorder. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.PureReplicaMeanEnergyAssembly

open Set Filter MeasureTheory SphericalModel SphericalTAPCertificate PureStationarity
open PureCapturePhysicalCoarseDiniAssembly SourceLiteratureParisi LiteratureSubagProposition24
open PureCapturePhysicalCoarseDiniLowEnergy PureCapturePhysicalCoarseTransfer
open MixedCapturePhysicalReplicaGeometry LiteratureSubagPhysicalDefinitions
open ReplicaMeanNetCover ReplicaBandGibbsMass ReplicaBandExpectedUpper
open SphericalAging.HardSphereDynamics
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 800000

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
points, using the exact radial homogeneity of the pure field. -/
private lemma deterministic_low_energy_cover (p : ℕ) (hp : 2 ≤ p)
    {N k M : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k)
    {Q η δ ρ ϑ e τ E ε : ℝ} (hQ : Q ∈ Ioo (0 : ℝ) 1)
    (hη : 0 ≤ η) (hηQ : η < Q / 2) (hηρ : η ≤ ρ)
    (hgeometry : (2 * Real.sqrt 2 + 1) * η + 1 / (k : ℝ) + ϑ ≤ δ * Real.sqrt Q)
    (hE : E = e * (Real.sqrt Q) ^ p) (hε : ε = (Real.sqrt Q) ^ p * τ)
    (hLip : derivativeConstant (mixtureCoefficients (FiniteMixture.pure p hp 1 one_pos)) *
      ϑ ≤ ε / 4)
    (points : Fin M → Vector N)
    (hnorm : ∀ j, ‖points j‖ = Real.sqrt (N : ℝ) * Real.sqrt Q)
    (hnet : ∀ m : Vector N, ‖m‖ = Real.sqrt (N : ℝ) * Real.sqrt Q →
      ∃ j, ‖m - points j‖ ≤ ϑ * Real.sqrt (N : ℝ))
    (J : Disorder N (FiniteMixture.pure p hp 1 one_pos).maxDegree)
    (hJ : J ∈ regularDisorder) (σ : Fin k → Vector N)
    (hσ : ∀ i, OnSphere (σ i))
    (hlow : σ ∈ replicaMeanLowEnergy (FiniteMixture.pure p hp 1 one_pos) J Q η e τ) :
    ∃ j, σ ∈ ReplicatedBand k Q δ ρ (points j) ∧
      field (mixtureCoefficients (FiniteMixture.pure p hp 1 one_pos)) J (points j) ≤
        (N : ℝ) * (E - 3 * ε / 4) := by
  have hpair := hlow.1
  have hpos := physicalMeanNormSq_pos hN (by omega) σ hσ hQ hη hηQ
    (fun i j hij => (hpair i j hij).le)
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
  have hhom : field (mixtureCoefficients (FiniteMixture.pure p hp 1 one_pos)) J
      (physicalContactMean Q σ) = (Real.sqrt Q) ^ p *
        field (mixtureCoefficients (FiniteMixture.pure p hp 1 one_pos)) J
          (physicalTrainingCenter σ) := by
    rw [physicalContactMean_eq_smul_trainingCenter hN hk hQ.1.le σ hpos]
    exact pure_field_smul p hp J (Real.sqrt_nonneg Q) _
  have henergy : field (mixtureCoefficients (FiniteMixture.pure p hp 1 one_pos)) J
      (physicalContactMean Q σ) ≤ (N : ℝ) * (E - ε) := by
    rw [hhom]
    calc
      _ ≤ (Real.sqrt Q) ^ p * ((N : ℝ) * (e - τ)) :=
        mul_le_mul_of_nonneg_left hlow.2 (by positivity)
      _ = _ := by rw [hE, hε]; ring
  have hball (m : Vector N) (hm : ‖m‖ = Real.sqrt (N : ℝ) * Real.sqrt Q) :
      ‖m‖ ≤ Real.sqrt (N : ℝ) := by
    rw [hm]
    exact mul_le_of_le_one_right (Real.sqrt_nonneg _) hroot
  have hl := regular_ball_lipschitz hN (mixtureCoefficients (FiniteMixture.pure p hp 1 one_pos)) J hJ (points j) (physicalContactMean Q σ)
    (hball _ (hnorm j)) (hball _ hcmnorm)
  have herror : |field (mixtureCoefficients (FiniteMixture.pure p hp 1 one_pos)) J
      (points j) - field (mixtureCoefficients (FiniteMixture.pure p hp 1 one_pos)) J
      (physicalContactMean Q σ)| ≤ (N : ℝ) * (ε / 4) := by
    calc
      _ ≤ derivativeConstant (mixtureCoefficients (FiniteMixture.pure p hp 1 one_pos)) *
          Real.sqrt (N : ℝ) * (ϑ * Real.sqrt (N : ℝ)) :=
        hl.trans (mul_le_mul_of_nonneg_left hj'
          (mul_nonneg (derivativeConstant_pos _).le (Real.sqrt_nonneg _)))
      _ = (N : ℝ) *
          (derivativeConstant (mixtureCoefficients (FiniteMixture.pure p hp 1 one_pos)) * ϑ) := by
        calc
          _ = (derivativeConstant (mixtureCoefficients (FiniteMixture.pure p hp 1 one_pos)) * ϑ) *
              (Real.sqrt (N : ℝ)) ^ 2 := by ring
          _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg N)]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hLip (Nat.cast_nonneg N)
  linarith [le_abs_self (field (mixtureCoefficients (FiniteMixture.pure p hp 1 one_pos)) J
    (points j) - field (mixtureCoefficients (FiniteMixture.pure p hp 1 one_pos)) J
    (physicalContactMean Q σ))]

/-- The union over the net on the good disorder event. Zero-volume bands
are removed before applying the expected-pressure estimate. -/
private lemma on_event_gibbs_bound {N k M : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k)
    (μ : FiniteMixture) {β Q η δ ρ e τ E ε T A : ℝ} (hβ : 0 < β)
    (points : Fin M → Vector N) (hM : 0 < M)
    (hnorm : ∀ j, ‖points j‖ ^ 2 = (N : ℝ) * Q)
    (hcard : Real.log (M : ℝ) ≤ (N : ℝ) * A)
    (hbeat : A ≤ (k : ℝ) * β * ε / 8)
    (J : Disorder N μ.maxDegree)
    (hcover : ∀ σ : Fin k → Vector N, (∀ i, OnSphere (σ i)) →
      σ ∈ replicaMeanLowEnergy μ J Q η e τ →
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
      (replicaMeanLowEnergy μ J Q η e τ) ≤
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
  have hsub : replicaMeanLowEnergy μ J Q η e τ ≤ᵐ[ν] ⋃ j, B j := by
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
    (μ : FiniteMixture) (β Q η e τ : ℝ)
    (G : Set (Disorder (n + 2) μ.maxDegree)) (hG : MeasurableSet G)
    {b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ J ∈ G,
      (Measure.pi (fun _ : Fin k => gibbsLaw (n + 2) β (field (mixtureCoefficients μ) J))).real
        (replicaMeanLowEnergy μ J Q η e τ) ≤ b) :
    expectedReplicaMeanLowEnergy (k := k) n μ β Q η e τ ≤
      (disorderLaw (n + 2) μ.maxDegree).real Gᶜ + b := by
  have hi : Integrable (Gᶜ.indicator (fun _ => (1 : ℝ)))
      (disorderLaw (n + 2) μ.maxDegree) := (integrable_const 1).indicator hG.compl
  calc
    _ ≤ ∫ J, Gᶜ.indicator (fun _ => (1 : ℝ)) J + b
        ∂disorderLaw (n + 2) μ.maxDegree := by
      apply integral_mono (replicaMeanLowEnergy_probability_integrable μ β Q η e τ)
        (hi.add (integrable_const b))
      intro J
      change (Measure.pi (fun _ : Fin k => gibbsLaw (n + 2) β
        (field (mixtureCoefficients μ) J))).real (replicaMeanLowEnergy μ J Q η e τ) ≤
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

/-- The final dimension limit needs no quantitative pressure-deviation
rate: a vanishing failure probability and the net bound suffice. -/
private lemma replica_mean_limit {k : ℕ} (μ : FiniteMixture) (β Q η e τ : ℝ)
    {a : ℝ} (ha : 0 < a) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (hgood : ∀ᶠ n : ℕ in atTop, ∃ G : Set (Disorder (n + 2) μ.maxDegree),
      MeasurableSet G ∧ (disorderLaw (n + 2) μ.maxDegree).real Gᶜ ≤ r n ∧
        ∀ J ∈ G,
          (Measure.pi (fun _ : Fin k => gibbsLaw (n + 2) β (field (mixtureCoefficients μ) J))).real
            (replicaMeanLowEnergy μ J Q η e τ) ≤ Real.exp (-a * (n + 2 : ℕ))) :
    Tendsto (fun n => expectedReplicaMeanLowEnergy (k := k) n μ β Q η e τ)
      atTop (𝓝 0) := by
  have hexp : Tendsto (fun n : ℕ => Real.exp (-a * (n + 2 : ℕ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)).const_mul_atTop_of_neg
        (neg_neg_of_pos ha))
  have hbound : ∀ᶠ n : ℕ in atTop,
      expectedReplicaMeanLowEnergy (k := k) n μ β Q η e τ ≤
        r n + Real.exp (-a * (n + 2 : ℕ)) := by
    filter_upwards [hgood] with n hn
    obtain ⟨G, hG, hGr, hGb⟩ := hn
    exact (expected_low_energy_le_failure μ β Q η e τ G hG (Real.exp_pos _).le hGb).trans
      (by linarith)
  exact squeeze_zero' (.of_forall (fun n => integral_nonneg (fun J => measureReal_nonneg)))
    hbound (by simpa only [add_zero] using hr.add hexp)

/-- Source `prop:pc-replica-means` for the pure model, in the exact form consumed by the
coarse-cover assembly. -/
theorem pure_physicalReplicaMeanEnergy_of_literature
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (hChen : Chen2013FiniteParisi)
    (h24 : Proposition24 (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q) :
    PhysicalReplicaMeanEnergy (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q
      (pureEnergyConstant p (by omega)) := by
  classical
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  have hβ : 0 < β := h.beta_pos
  have hQ : Q ∈ Ioo (0 : ℝ) 1 := h.overlap_range
  intro τ hτ
  let e := pureEnergyConstant p (by omega)
  let E := TwoAtomStationarity.markE μ β x Q
  let ε := (Real.sqrt Q) ^ p * τ
  let T := Real.log (1 - Q) / 2 + β ^ 2 * TwoAtomStationarity.residualAtOne μ Q / 2
  let F := CSParisiMeasure.variationalValue μ β
  have hε : 0 < ε := mul_pos (pow_pos (Real.sqrt_pos.mpr hQ.1) _) hτ
  have hE : E = e * (Real.sqrt Q) ^ p :=
    (SphericalPureCapSourceScalars.sourcePure_certificate_scalar_coordinates p hp h).1
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
  have hpressure := PhysicalPressureLowerDeviation.pressure_lower_deviation_tendsto_zero
    μ hβ (hChen μ β hβ.le) (t := β * ε / 8) (by positivity)
  let r : ℕ → ℝ := fun n => 2 * Real.exp (-(n + 2 : ℕ)) +
    (disorderLaw (n + 2) μ.maxDegree).real
      {J | Real.log (mixturePartition μ β J) / (n + 2 : ℕ) < F - β * ε / 8}
  have hfailure : Tendsto r atTop (𝓝 0) := by
    have hexp : Tendsto (fun n : ℕ => Real.exp (-(n + 2 : ℕ))) atTop (𝓝 0) := by
      have hcast : Tendsto (fun n : ℕ => ((n + 2 : ℕ) : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp hshift
      simpa only [Function.comp_def, neg_one_mul] using Real.tendsto_exp_atBot.comp
        (hcast.const_mul_atTop_of_neg (show (-1 : ℝ) < 0 by norm_num))
    simpa only [r, Function.comp_def, mul_zero, add_zero] using
      (hexp.const_mul 2).add (hpressure.comp hshift)
  let a : ℝ := (k : ℝ) * β * ε / 4
  have ha : 0 < a := by
    have hkr : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    dsimp only [a]
    positivity
  apply replica_mean_limit μ β Q η e τ ha r hfailure
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
      σ ∈ replicaMeanLowEnergy μ J Q η e τ →
      ∃ j, σ ∈ ReplicatedBand k Q δ ρ (points j) ∧
        field (mixtureCoefficients μ) J (points j) ≤ (n + 2 : ℕ) * (E - 3 * ε / 4) := by
    intro σ hσ hl
    exact deterministic_low_energy_cover p (by omega) (by omega) hk hQ hη.le hηQ hηρ
      hgeometry hE rfl hLip points hnorm hnet J hreg σ hσ hl
  have hb := on_event_gibbs_bound (by omega) hk μ hβ points hM hnormsq hcard hbeat J
    hcover hpress' (hΩupper J hJΩ) hn.2
  convert hb using 1
  dsimp only [a]
  congr 1
  ring

end SlowEquilibration.PureReplicaMeanEnergyAssembly
