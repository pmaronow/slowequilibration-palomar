-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntranceLatitudeSourceQuadraticMoments
public import SlowEquilibration.SphericalOverlapPolynomialExponentialMoments

/-! The three literal source quadratic radial powers have their genuine
uniform sphere order. Fixed constants precede the dimension and axis. -/

@[expose] public section
namespace SlowEquilibration.EntranceLatitudeTangentObservable
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel SphericalForm
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual overlap moments give the full source radial square order,
including its higher trace term, uniformly at arbitrary spherical axes. -/
theorem sourceLatitudeQuadraticPower_sphere_eventually_bounded (μ : FiniteMixture) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,∀ x : Vector (n+1),‖x‖^2=((n+1 : ℕ) : ℝ) →
      Integrable (fun u => sourceLatitudeQuadraticPower n μ (overlap x u)*
        Real.exp (((n+1 : ℕ) : ℝ)*(overlap x u)^2/8)) (sphereLaw (n+1)) ∧
      (∫ u,sourceLatitudeQuadraticPower n μ (overlap x u)*
        Real.exp (((n+1 : ℕ) : ℝ)*(overlap x u)^2/8) ∂sphereLaw (n+1))≤
      C*((n+1 : ℕ) : ℝ)^(2-(μ.minDegree : ℝ)) := by
  obtain ⟨Ca,hCa,ha⟩ := sphere_overlap_polynomial_exp_square_eventually_bounded
    (2*μ.minDegree) (by norm_num : (0 : ℝ)≤1/8) (by norm_num : (1 : ℝ)/8<1/2)
  obtain ⟨Cb,hCb,hb⟩ := sphere_overlap_polynomial_exp_square_eventually_bounded
    (2*μ.minDegree-2) (by norm_num : (0 : ℝ)≤1/8) (by norm_num : (1 : ℝ)/8<1/2)
  obtain ⟨Cc,hCc,hc⟩ := sphere_overlap_polynomial_exp_square_eventually_bounded
    (4*μ.minDegree-4) (by norm_num : (0 : ℝ)≤1/8) (by norm_num : (1 : ℝ)/8<1/2)
  refine ⟨Ca+Cb+Cc,by positivity,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually ha,(tendsto_add_atTop_nat 1).eventually hb,
    (tendsto_add_atTop_nat 1).eventually hc] with n hA hB hC
  intro x hx
  let N := ((n+1 : ℕ) : ℝ)
  let ν := sphereLaw (n+1)
  let E := fun u : Vector (n+1) => Real.exp (N*(overlap x u)^2/8)
  have hNp : 0<N := by dsimp [N];positivity
  have hN1 : 1≤N := by dsimp [N];norm_cast;omega
  have hmin := μ.minDegree_ge_two
  have hcastB : ((2*μ.minDegree-2 : ℕ) : ℝ)=2*(μ.minDegree : ℝ)-2 := by
    rw [Nat.cast_sub (by omega),Nat.cast_mul];norm_num
  have hcastC : ((4*μ.minDegree-4 : ℕ) : ℝ)=4*(μ.minDegree : ℝ)-4 := by
    rw [Nat.cast_sub (by omega),Nat.cast_mul];norm_num
  have hPA : N^2*N^(-((2*μ.minDegree : ℕ) : ℝ)/2)=N^(2-(μ.minDegree : ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_add hNp]
    congr 1
    push_cast
    ring
  have hPB : N*N^(-((2*μ.minDegree-2 : ℕ) : ℝ)/2)=N^(2-(μ.minDegree : ℝ)) := by
    rw [hcastB]
    calc
      _=N^(1 : ℝ)*N^(-(2*(μ.minDegree : ℝ)-2)/2) := by rw [Real.rpow_one]
      _=N^(1+(-(2*(μ.minDegree : ℝ)-2)/2)) := (Real.rpow_add hNp _ _).symm
      _=_ := by congr 1;ring
  have hPC : N^2*N^(-((4*μ.minDegree-4 : ℕ) : ℝ)/2)≤N^(2-(μ.minDegree : ℝ)) := by
    rw [hcastC,←Real.rpow_natCast,←Real.rpow_add hNp]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    have hd : (2 : ℝ)≤μ.minDegree := by exact_mod_cast hmin
    linarith
  have hA' : Integrable (fun u => |overlap x u|^(2*μ.minDegree)*E u) ν ∧
      (∫ u,|overlap x u|^(2*μ.minDegree)*E u ∂ν)≤Ca*N^(-((2*μ.minDegree : ℕ) : ℝ)/2) := by
    have hf : (fun u => |overlap x u|^(2*μ.minDegree)*E u)=
        (fun u => |overlap x u|^(2*μ.minDegree)*Real.exp ((1/8)*((n+1 : ℕ) : ℝ)*(overlap x u)^2)) := by
      funext u
      congr 1
      dsimp only [E,N]
      congr 1
      ring
    rw [hf]
    exact hA x hx
  have hB' : Integrable (fun u => |overlap x u|^(2*μ.minDegree-2)*E u) ν ∧
      (∫ u,|overlap x u|^(2*μ.minDegree-2)*E u ∂ν)≤Cb*N^(-((2*μ.minDegree-2 : ℕ) : ℝ)/2) := by
    have hf : (fun u => |overlap x u|^(2*μ.minDegree-2)*E u)=
        (fun u => |overlap x u|^(2*μ.minDegree-2)*Real.exp ((1/8)*((n+1 : ℕ) : ℝ)*(overlap x u)^2)) := by
      funext u
      congr 1
      dsimp only [E,N]
      congr 1
      ring
    rw [hf]
    exact hB x hx
  have hC' : Integrable (fun u => |overlap x u|^(4*μ.minDegree-4)*E u) ν ∧
      (∫ u,|overlap x u|^(4*μ.minDegree-4)*E u ∂ν)≤Cc*N^(-((4*μ.minDegree-4 : ℕ) : ℝ)/2) := by
    have hf : (fun u => |overlap x u|^(4*μ.minDegree-4)*E u)=
        (fun u => |overlap x u|^(4*μ.minDegree-4)*Real.exp ((1/8)*((n+1 : ℕ) : ℝ)*(overlap x u)^2)) := by
      funext u
      congr 1
      dsimp only [E,N]
      congr 1
      ring
    rw [hf]
    exact hC x hx
  have hiA : Integrable (fun u => N^2*(|overlap x u|^(2*μ.minDegree)*E u)) ν := hA'.1.const_mul _
  have hiB : Integrable (fun u => N*(|overlap x u|^(2*μ.minDegree-2)*E u)) ν := hB'.1.const_mul _
  have hiC : Integrable (fun u => N^2*(|overlap x u|^(4*μ.minDegree-4)*E u)) ν := hC'.1.const_mul _
  have hiS : Integrable (fun u => N^2*(|overlap x u|^(2*μ.minDegree)*E u)+
      N*(|overlap x u|^(2*μ.minDegree-2)*E u)+N^2*(|overlap x u|^(4*μ.minDegree-4)*E u)) ν := by
    convert (hiA.add hiB).add hiC using 1
  have heq : (fun u => sourceLatitudeQuadraticPower n μ (overlap x u)*E u)=
      (fun u => N^2*(|overlap x u|^(2*μ.minDegree)*E u)+
        N*(|overlap x u|^(2*μ.minDegree-2)*E u)+N^2*(|overlap x u|^(4*μ.minDegree-4)*E u)) := by
    funext u
    unfold sourceLatitudeQuadraticPower
    dsimp only [N]
    ring
  refine ⟨by rw [heq];exact hiS,?_⟩
  change (∫ u,sourceLatitudeQuadraticPower n μ (overlap x u)*E u ∂ν)≤_
  have hiAB : Integrable (fun u => N^2*(|overlap x u|^(2*μ.minDegree)*E u)+
      N*(|overlap x u|^(2*μ.minDegree-2)*E u)) ν := by
    convert hiA.add hiB using 1
  have hsumeq : (∫ u,N^2*(|overlap x u|^(2*μ.minDegree)*E u)+
      N*(|overlap x u|^(2*μ.minDegree-2)*E u)+N^2*(|overlap x u|^(4*μ.minDegree-4)*E u) ∂ν)=
      (∫ u,N^2*(|overlap x u|^(2*μ.minDegree)*E u)+N*(|overlap x u|^(2*μ.minDegree-2)*E u) ∂ν)+
      (∫ u,N^2*(|overlap x u|^(4*μ.minDegree-4)*E u) ∂ν) := by
    convert integral_add hiAB hiC using 1
  have habeq : (∫ u,N^2*(|overlap x u|^(2*μ.minDegree)*E u)+N*(|overlap x u|^(2*μ.minDegree-2)*E u) ∂ν)=
      (∫ u,N^2*(|overlap x u|^(2*μ.minDegree)*E u) ∂ν)+(∫ u,N*(|overlap x u|^(2*μ.minDegree-2)*E u) ∂ν) := by
    convert integral_add hiA hiB using 1
  rw [heq,hsumeq,habeq,integral_const_mul,integral_const_mul,integral_const_mul]
  have hs := add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hA'.2 (sq_nonneg N))
    (mul_le_mul_of_nonneg_left hB'.2 hNp.le))
    (mul_le_mul_of_nonneg_left hC'.2 (sq_nonneg N))
  apply hs.trans
  have hAA : N^2*(Ca*N^(-((2*μ.minDegree : ℕ) : ℝ)/2))=Ca*N^(2-(μ.minDegree : ℝ)) := by
    rw [mul_left_comm,hPA]
  have hBB : N*(Cb*N^(-((2*μ.minDegree-2 : ℕ) : ℝ)/2))=Cb*N^(2-(μ.minDegree : ℝ)) := by
    rw [mul_left_comm,hPB]
  have hCC : N^2*(Cc*N^(-((4*μ.minDegree-4 : ℕ) : ℝ)/2))≤Cc*N^(2-(μ.minDegree : ℝ)) := by
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left hPC hCc.le
  rw [hAA,hBB]
  apply (add_le_add le_rfl hCC).trans_eq
  ring

end
end SlowEquilibration.EntranceLatitudeTangentObservable
