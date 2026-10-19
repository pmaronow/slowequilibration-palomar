-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.InfiniteMixtureUniformGeneralCapRate
public import SlowEquilibration.InfiniteMixtureCutoffCollarBarrier
public import SlowEquilibration.SphericalGeneralCollarEigenvalue
public import SlowEquilibration.SphericalInfiniteSpectralTransfer

/-! Genuine infinite-mixture cusp eigenvalues. The mode-count exponent
is selected before the cusp tolerance and before epsilon. Every stochastic
input is proved for the original infinite tensor law; a fixed cutoff is
chosen only after epsilon, and no uniform dimension threshold is asserted. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalInfiniteModel
open Set Filter MeasureTheory ProbabilityTheory SphericalModel SphericalForm InfiniteMixture
open scoped Topology
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual spectrum has exponentially many eigenvalues below the source
cusp scale, with one strictly positive mode-count exponent for all small
epsilon and all relative tolerances. This theorem uses the genuine general finite-mixture providers. -/
theorem cuspCoordinate_eigenvalues (μ : InfiniteMixture)
    (hgap : Thresholds.dynamicalThreshold μ.xi<Thresholds.staticThreshold μ.xi)
    (c : CuspCoordinate μ) :
    ∃ κ : ℝ,0<κ ∧ ∀ θ∈Ioo (0:ℝ) 1,∀ᶠ ε in 𝓝[>] (0:ℝ),
      ∃ a : ℝ,0<a ∧ ∀ᶠ n : ℕ in atTop,
        ∃ Ω : Set (Disorder (n+1)),MeasurableSet Ω ∧
          (disorderLaw (n+1)).real Ωᶜ≤14*Real.exp (-a*(n+1:ℕ)) ∧
          ∀ J∈Ω,∀ hn : 1≤n,
            (infiniteSpectralData n hn (c.epsilonTemperature ε) μ J).eigenvalue
              (Nat.floor (Real.exp (κ*(n+1:ℕ))))≤
                Real.exp (-((1-θ)*(c.barrierCoefficient*ε^(1+((2*c.m:ℕ):ℝ)⁻¹)))*(n+1:ℕ)) := by
  have hd : 0<Thresholds.dynamicalThreshold μ.xi := Real.sqrt_pos.mpr (inv_pos.mpr μ.Amax_pos)
  obtain ⟨β₀,hβ₀d,hβ₀s⟩ := exists_between hgap
  have hβ₀ : 0<β₀ := hd.trans hβ₀d
  have hqD := μ.qD_mem_interior hgap
  have hs : μ.qD/2∈Ioo (0:ℝ) 1 := ⟨half_pos hqD.1,by linarith [hqD.2]⟩
  obtain ⟨c₀,hc₀,hcap⟩ := μ.exists_uniform_finiteCutoff_cap_rate hβ₀ hβ₀s hs
  obtain ⟨P₀,_hP₀,h₀⟩ := μ.exists_positive_coefficient
  have htemp : ∀ᶠ ε in 𝓝[>] (0:ℝ),c.epsilonTemperature ε<β₀ := by
    have ht : ContinuousAt c.epsilonTemperature 0 := by unfold CuspCoordinate.epsilonTemperature;fun_prop
    have hv : c.epsilonTemperature 0=Thresholds.dynamicalThreshold μ.xi := by simp [CuspCoordinate.epsilonTemperature]
    exact eventually_nhdsWithin_of_eventually_nhds (ht.eventually (Iio_mem_nhds (by rwa [hv])))
  refine ⟨c₀/2,half_pos hc₀,?_⟩
  intro θ hθ
  filter_upwards [self_mem_nhdsWithin,htemp,
    c.basedCutoff_scalar_certificate_eventually P₀ h₀ hgap (half_pos hθ.1)] with ε hε htemp hscalar
  change 0<ε at hε
  let β := c.epsilonTemperature ε
  let D := c.barrierCoefficient*ε^(1+((2*c.m:ℕ):ℝ)⁻¹)
  have hD : 0<D := mul_pos c.barrierCoefficient_pos (Real.rpow_pos_of_pos hε _)
  let h := θ*D/(8*β₀)
  have hh : 0<h := div_pos (mul_pos hθ.1 hD) (by positivity)
  have hi : Tendsto (fun p : ℕ => P₀+p-1) atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp (by simpa only [Nat.add_comm] using tendsto_add_atTop_nat P₀)
  have htail := hi.eventually (tailSphere_fixed_exponential_rate_eventually μ hh)
  obtain ⟨p,hcert,bt,hbt,htail⟩ := (hscalar.2.2.and htail).exists
  let P := P₀+p
  have hP : ∃ q,q≤P ∧ 0<μ.coeff q := ⟨P₀,Nat.le_add_right _ _,h₀⟩
  let ν := μ.finiteCutoff P hP
  have hβd : Thresholds.dynamicalThreshold ν.xi<β := hcert.1
  have hβs : β<Thresholds.staticThreshold ν.xi := hcert.2.1
  have hβ : 0<β := ν.dynamicalThreshold_pos.trans hβd
  have hcollar : IsAdmissibleCollar ν β (c.collarLeft ε) (c.collarRight ε) := hcert.2.2.1
  have hσ : (1-θ/2)*D<plantedCollarGap ν β (c.collarRight ε) := hcert.2.2.2
  obtain ⟨af,haf,hfinite⟩ := general_collar_eigenvalue_of_cap_rate ν hβd hβs hcollar
    hscalar.1.le hc₀ hσ (hcap P hP β hβ htemp.le)
  have htransfer := infinite_spectral_transfer μ P hP hβ.le haf hbt (by norm_num : (0:ℝ)≤12)
    htail hfinite
  refine ⟨min af bt,lt_min haf hbt,?_⟩
  filter_upwards [htransfer] with n hn
  obtain ⟨Ω,hΩ,hfail,hgood⟩ := hn
  refine ⟨Ω,hΩ,by simpa only [show (12:ℝ)+2=14 by norm_num] using hfail,?_⟩
  intro J hJ hn'
  apply (hgood J hJ hn').trans
  apply Real.exp_le_exp.mpr
  have hloss : 2*β*h≤θ*D/4 := by
    have hm := mul_le_mul_of_nonneg_right htemp.le hh.le
    have heq : 2*β₀*h=θ*D/4 := by dsimp [h];field_simp;ring
    nlinarith
  have hrate : (1-θ)*D≤(1-θ/2)*D-2*β*h := by nlinarith
  exact mul_le_mul_of_nonneg_right (neg_le_neg hrate) (by positivity)

/-- All analytic cusp data are constructed from source summability and the
strict separation of the actual thresholds. -/
theorem cusp_eigenvalues (μ : InfiniteMixture)
    (hgap : Thresholds.dynamicalThreshold μ.xi<Thresholds.staticThreshold μ.xi) :
    ∃ c : CuspCoordinate μ,∃ κ : ℝ,0<κ ∧ ∀ θ∈Ioo (0:ℝ) 1,
      ∀ᶠ ε in 𝓝[>] (0:ℝ),∃ a : ℝ,0<a ∧ ∀ᶠ n : ℕ in atTop,
        ∃ Ω : Set (Disorder (n+1)),MeasurableSet Ω ∧
          (disorderLaw (n+1)).real Ωᶜ≤14*Real.exp (-a*(n+1:ℕ)) ∧
          ∀ J∈Ω,∀ hn : 1≤n,
            (infiniteSpectralData n hn (c.epsilonTemperature ε) μ J).eigenvalue
              (Nat.floor (Real.exp (κ*(n+1:ℕ))))≤
                Real.exp (-((1-θ)*(c.barrierCoefficient*ε^(1+((2*c.m:ℕ):ℝ)⁻¹)))*(n+1:ℕ)) := by
  obtain ⟨c⟩ := μ.exists_cuspCoordinate hgap
  exact ⟨c,cuspCoordinate_eigenvalues μ hgap c⟩

end SlowEquilibration.SphericalInfiniteModel
