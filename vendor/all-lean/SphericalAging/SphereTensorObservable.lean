module

public import SphericalAging.AdaptiveGradientDisclosure

public section

/-! Actual ordered tensor observables Phi_k(x)=(x/sqrt N) tensor k used
in source10.3, with genuine Frechet derivative and dimension-sharp norm
bounds. These are deterministic receipts, not a semigroup realization. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.SphereTensorObservable
open FiniteModel GaussianLandscape LandscapeDerivatives AdaptiveGradientDisclosure
open scoped InnerProductSpace BigOperators

@[expose]  def pureForm (N k : ℕ) : ContinuousMultilinearMap ℝ (fun _ : Fin k => Vector N) (TensorSpace N k) :=
  (EuclideanSpace.equiv (TensorIndex N k) ℝ).symm.toContinuousLinearMap.compContinuousMultilinearMap
    (ContinuousMultilinearMap.pi (fun I : TensorIndex N k => coordinateForm N k I))

 theorem pureForm_apply {N k : ℕ} (v : Fin k→Vector N) : pureForm N k v=pureTensor v := by
  ext I
  simp [pureForm,pureTensor,coordinateForm,ContinuousMultilinearMap.compContinuousLinearMap_apply]

 theorem pureTensor_norm {N k : ℕ} (v : Fin k→Vector N) : ‖pureTensor v‖=∏i : Fin k,‖v i‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (Finset.prod_nonneg (fun _ _ => norm_nonneg _))).mp
  rw [←real_inner_self_eq_norm_sq,pureTensor_inner]
  simp only [real_inner_self_eq_norm_sq,Finset.prod_pow]

@[expose]  def derivativeTensor {N k : ℕ} (x : Vector N) : Vector N→L[ℝ] TensorSpace N k :=
  ∑i : Fin k,(pureForm N k).toContinuousLinearMap (fun _ => x) i

 theorem diagonal_hasFDerivAt {N k : ℕ} (x : Vector N) :
    HasFDerivAt (fun y => pureTensor (fun _ : Fin k => y)) (derivativeTensor (k:=k) x) x := by
  have hh := HasFDerivAt.multilinear_comp (f:=pureForm N k) (fun _ : Fin k => hasFDerivAt_id x)
  simpa only [derivativeTensor,pureForm_apply,ContinuousLinearMap.comp_id,id_eq] using hh

 theorem derivativeTensor_apply {N k : ℕ} (x y : Vector N) :
    derivativeTensor (k:=k) x y=gradientTensor (p:=k) x y := by
  rw [derivativeTensor,sum_apply,gradientTensor]
  apply Finset.sum_congr rfl
  intro i _
  exact pureForm_apply _

 theorem derivativeTensor_apply_norm_le {N k : ℕ} (x y : Vector N) :
    ‖derivativeTensor (k:=k) x y‖≤(k:ℝ)*‖x‖^(k-1)*‖y‖ := by
  rw [derivativeTensor_apply,gradientTensor]
  apply (norm_sum_le _ _).trans
  calc
    (∑i : Fin k,‖pureTensor (Function.update (fun _ => x) i y)‖)=
        ∑i : Fin k,‖y‖*‖x‖^(k-1) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [pureTensor_norm,updated_norm_product]
    _ = (k:ℝ)*‖x‖^(k-1)*‖y‖ := by simp;ring
    _ ≤ (k:ℝ)*‖x‖^(k-1)*‖y‖ := le_rfl

@[expose]  def observable (N k : ℕ) (x : Vector N) : TensorSpace N k :=
  (1/Real.sqrt (N:ℝ)^k) • pureTensor (fun _ : Fin k => x)
@[expose]  def observableDerivative {N k : ℕ} (x : Vector N) : Vector N→L[ℝ] TensorSpace N k :=
  (1/Real.sqrt (N:ℝ)^k) • derivativeTensor (k:=k) x

 theorem observable_hasFDerivAt {N k : ℕ} (x : Vector N) :
    HasFDerivAt (observable N k) (observableDerivative (k:=k) x) x :=
  by
    convert (diagonal_hasFDerivAt (k:=k) x).const_smul (1/Real.sqrt (N:ℝ)^k) using 1 <;> rfl

 theorem observable_norm_one {N k : ℕ} (hN : 0<N) {x : Vector N} (hx : ‖x‖=Real.sqrt N) :
    ‖observable N k x‖=1 := by
  have hr : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  rw [observable,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity),pureTensor_norm]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,hx]
  exact one_div_mul_cancel (pow_ne_zero _ hr.ne')

 theorem observable_derivative_bound {N k : ℕ} (hN : 0<N) (hk : 1≤k)
    {x : Vector N} (hx : ‖x‖=Real.sqrt N) (y : Vector N) :
    ‖observableDerivative (k:=k) x y‖≤(k:ℝ)/Real.sqrt (N:ℝ)*‖y‖ := by
  have hr : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  rw [observableDerivative,ContinuousLinearMap.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hb := mul_le_mul_of_nonneg_left (derivativeTensor_apply_norm_le (k:=k) x y)
    (show 0≤1/Real.sqrt (N:ℝ)^k by positivity)
  rw [hx] at hb
  have he : Real.sqrt (N:ℝ)^k=Real.sqrt (N:ℝ)^(k-1)*Real.sqrt (N:ℝ) := by
    rw [←pow_succ]
    congr 1
    omega
  have hconst : (1/Real.sqrt (N:ℝ)^k)*((k:ℝ)*Real.sqrt (N:ℝ)^(k-1)*‖y‖)=
      (k:ℝ)/Real.sqrt (N:ℝ)*‖y‖ := by
    rw [he]
    field_simp
  exact hb.trans_eq hconst

 theorem observable_inner {N k : ℕ} (hN : 0<N) (x y : Vector N) :
    ⟪observable N k x,observable N k y⟫_ℝ=(⟪x,y⟫_ℝ/(N:ℝ))^k := by
  have hn : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  rw [observable,observable,real_inner_smul_left,real_inner_smul_right,pureTensor_inner]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,div_pow]
  have he : (Real.sqrt (N:ℝ)^k)^2=(N:ℝ)^k := by
    rw [←pow_mul,Nat.mul_comm,pow_mul,Real.sq_sqrt hn.le]
  field_simp
  rw [he]
  ring

 theorem observable_contDiff (N k : ℕ) : ContDiff ℝ (⊤:ℕ∞) (observable N k) := by
  have hdiag : ContDiff ℝ (⊤:ℕ∞) (fun x : Vector N => pureTensor (fun _ : Fin k => x)) := by
    have hm : ContDiff ℝ (⊤:ℕ∞) (fun x : Vector N => fun _ : Fin k => x) :=
      contDiff_pi.mpr (fun _ => contDiff_id)
    have hh : ContDiff ℝ (⊤:ℕ∞) (fun x : Vector N => pureForm N k (fun _ => x)) :=
      (pureForm N k).contDiff.comp hm
    simpa only [pureForm_apply] using hh
  have hh := hdiag.const_smul (1/Real.sqrt (N:ℝ)^k)
  convert hh using 1 <;> rfl

 theorem observable_fderiv {N k : ℕ} (x : Vector N) :
    fderiv ℝ (observable N k) x=observableDerivative (k:=k) x := (observable_hasFDerivAt x).fderiv

 theorem observable_fderiv_norm_le {N k : ℕ} (hN : 0<N) (hk : 1≤k)
    {x : Vector N} (hx : ‖x‖=Real.sqrt N) :
    ‖fderiv ℝ (observable N k) x‖≤(k:ℝ)/Real.sqrt (N:ℝ) := by
  rw [observable_fderiv]
  apply (observableDerivative (k:=k) x).opNorm_le_bound (div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
  exact observable_derivative_bound hN hk hx

end SphericalAging.SphereTensorObservable
