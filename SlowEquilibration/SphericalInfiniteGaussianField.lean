-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalInfiniteFieldL2

/-! Actual finite-dimensional Gaussian laws of the infinite spherical field.
The entire original countable coefficient space is retained throughout. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalInfiniteModel
open MeasureTheory ProbabilityTheory SphericalModel Filter
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem weighted_sum_coe_ae {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [Fintype ι] (a : ι → ℝ) (Z : ι → Lp ℝ 2 P) :
    (∑ i,a i • Z i : Lp ℝ 2 P) =ᵐ[P] fun ω => ∑ i,a i*Z i ω := by
  have hc : ∀ᵐ ω ∂P,∀ i,(a i • Z i : Lp ℝ 2 P) ω=a i*Z i ω := by
    rw [ae_all_iff]
    intro i
    filter_upwards [Lp.coeFn_smul (a i) (Z i)] with ω hω
    exact hω
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => a i • Z i),hc] with ω hω he
  rw [hω]
  exact Finset.sum_congr rfl (fun i _ => he i)

private theorem block_partialSum_coe_ae {N : ℕ} (μ : InfiniteMixture)
    (x : Vector N) (n : ℕ) :
    (∑ p∈Finset.range n,blockLp μ p x : Lp ℝ 2 (disorderLaw N)) =ᵐ[disorderLaw N]
      fun J => ∑ p∈Finset.range n,block μ p J x := by
  have hc : ∀ᵐ J ∂disorderLaw N,∀ p,blockLp μ p x J=block μ p J x := by
    rw [ae_all_iff]
    exact fun p => (block_memLp μ p x).coeFn_toLp
  filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range n) (fun p => blockLp μ p x),hc] with J hJ he
  rw [hJ]
  exact Finset.sum_congr rfl (fun p _ => he p)

/-- Every finite real linear combination of field values is genuinely Gaussian. -/
theorem field_linearCombination_hasGaussianLaw {N : ℕ} (hN : 0<N) (μ : InfiniteMixture)
    {ι : Type*} [Fintype ι] (a : ι → ℝ) (x : ι → Vector N)
    (hx : ∀ i,‖x i‖^2≤(N:ℝ)) :
    HasGaussianLaw (fun J => ∑ i,a i*field μ J (x i)) (disorderLaw N) := by
  let Z : ℕ → Lp ℝ 2 (disorderLaw N) := fun n =>
    ∑ i,a i • ∑ p∈Finset.range n,blockLp μ p (x i)
  let W : Lp ℝ 2 (disorderLaw N) := ∑ i,a i • fieldLp μ (x i)
  let L (p : ℕ) : SphericalAging.FiniteModel.Disorder N (p+2) →L[ℝ] ℝ :=
    ∑ i,a i • (Real.sqrt (μ.coeff (p+2)) • pureFieldCLM N (p+2) (x i))
  have hL (p : ℕ) (J : Disorder N) : L p (J p)=∑ i,a i*block μ p J (x i) := by
    simp [L,ContinuousLinearMap.sum_apply,smul_apply,smul_eq_mul,pureFieldCLM_apply,block]
  have hGi (p : ℕ) : HasGaussianLaw (fun J : Disorder N => L p (J p)) (disorderLaw N) :=
    (degree_hasGaussianLaw p).map_fun (L p)
  have hI : iIndepFun (fun p (J : Disorder N) => L p (J p)) (disorderLaw N) :=
    (independent_degrees N).comp (fun p => L p) (fun p => (L p).measurable)
  have hG (n : ℕ) : HasGaussianLaw (Z n) (disorderLaw N) := by
    have hin : iIndepFun (fun p : Finset.range n => fun J : Disorder N => L p (J p))
        (disorderLaw N) := hI.precomp Subtype.val_injective
    have hg := hin.hasGaussianLaw_fun_sum (fun p : Finset.range n => hGi p)
    apply hg.congr
    have hc : ∀ᵐ J ∂disorderLaw N,∀ i,
        (∑ p∈Finset.range n,blockLp μ p (x i) : Lp ℝ 2 (disorderLaw N)) J=
          ∑ p∈Finset.range n,block μ p J (x i) := by
      rw [ae_all_iff]
      exact fun i => block_partialSum_coe_ae μ (x i) n
    filter_upwards [weighted_sum_coe_ae a (fun i => ∑ p∈Finset.range n,blockLp μ p (x i)),hc]
      with J hJ he
    change _=(∑ i,a i • ∑ p∈Finset.range n,blockLp μ p (x i) : Lp ℝ 2 (disorderLaw N)) J
    rw [hJ]
    simp_rw [he,Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [show (∑ p : Finset.range n,L p (J p)) = ∑ p∈Finset.range n,L p (J p) from
      Finset.sum_coe_sort (Finset.range n) (fun p => L p (J p))]
    exact Finset.sum_congr rfl (fun p _ => hL p J)
  have hlim : Tendsto Z atTop (𝓝 W) := by
    apply tendsto_finset_sum
    intro i _
    exact tendsto_const_nhds.smul (summable_blockLp_norm hN μ (x i) (hx i)).of_norm.tendsto_sum_tsum_nat
  apply (FourPapersCommon.hasGaussianLaw_of_L2_tendsto hG hlim).congr
  have hc : ∀ᵐ J ∂disorderLaw N,∀ i,fieldLp μ (x i) J=field μ J (x i) := by
    rw [ae_all_iff]
    exact fun i => fieldLp_coe_ae hN μ (x i) (hx i)
  filter_upwards [weighted_sum_coe_ae a (fun i => fieldLp μ (x i)),hc] with J hJ he
  change (∑ i,a i • fieldLp μ (x i) : Lp ℝ 2 (disorderLaw N)) J=_
  rw [hJ]
  simp_rw [he]

/-- The actual vector of values at any finite family of ball points has a
Gaussian law, not just individually Gaussian marginals. -/
theorem field_finiteFamily_hasGaussianLaw {N : ℕ} (hN : 0<N) (μ : InfiniteMixture)
    {ι : Type*} [Fintype ι] (x : ι → Vector N) (hx : ∀ i,‖x i‖^2≤(N:ℝ)) :
    HasGaussianLaw (fun J i => field μ J (x i)) (disorderLaw N) := by
  classical
  have hm : AEMeasurable (fun J i => field μ J (x i)) (disorderLaw N) :=
    AEMeasurable.of_eval (fun i => (field_memLp hN μ (x i) (hx i)).aemeasurable)
  refine ⟨hm,isGaussian_of_isGaussian_map (fun L => ?_)⟩
  have he (J : Disorder N) : L (fun i => field μ J (x i))=
      ∑ i,L (Pi.single i 1)*field μ J (x i) := by
    conv_lhs => rw [pi_eq_sum_univ' (fun i => field μ J (x i))]
    rw [map_sum]
    simp only [map_smul,smul_eq_mul,mul_comm]
  have hg := field_linearCombination_hasGaussianLaw hN μ
    (fun i => L (Pi.single i 1)) x hx
  have hg' : HasGaussianLaw (L ∘ (fun J i => field μ J (x i))) (disorderLaw N) := by
    simpa only [Function.comp_def,he] using hg
  rw [AEMeasurable.map_map_of_aemeasurable L.measurable.aemeasurable hm]
  exact hg'.isGaussian_map

end SlowEquilibration.SphericalInfiniteModel
