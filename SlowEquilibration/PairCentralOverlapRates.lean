-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PhysicalPairRatioAlgebra

/-! Dimension-uniform scalar rates for the source shrinking overlap window.
These convert the proved physical density and determinant errors to the
literal N^(1-4*alpha)+N^(-1/2) rate when alpha>1/4. -/
@[expose] public section
namespace SlowEquilibration.PairSchurExpectation
noncomputable section
open Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

lemma inverse_sqrt_eq_rpow {N:ℝ} (hN:0 ≤ N) : 1/Real.sqrt N=N^(-(1/2:ℝ)):=by
  rw [Real.rpow_neg hN,←Real.sqrt_eq_rpow,one_div]

lemma central_overlap_scalar_rates {N r α:ℝ} {d:ℕ} (hN:1 ≤ N)
    (hr:0 ≤ r) (hd:4 ≤ d) (hα:1/4 ≤ α) (hCore:r ≤ N^(-α)) :
    N*r^d+N*r^(2*(d-1))+r^(2*(d-2)) ≤ 3*N^(1-4*α) ∧
      r^(d-2)+1/Real.sqrt N ≤ 2/Real.sqrt N:=by
  have hN0:0 ≤ N:=by linarith
  have hNpos:0<N:=by linarith
  have hrOne:r ≤ 1:=hCore.trans (Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith))
  have hFour:(N^(-α))^4=N^(-4*α):=by
    rw [←Real.rpow_natCast,←Real.rpow_mul hN0]
    congr 1
    ring
  have hQuartic:N*r^4 ≤ N^(1-4*α):=by
    calc
      _ ≤ N*(N^(-α))^4:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hCore 4) hN0
      _ = N*N^(-4*α):=by rw [hFour]
      _ = N^(1:ℝ)*N^(-4*α):=by rw [Real.rpow_one]
      _ = N^(1+(-4*α)):=(Real.rpow_add hNpos 1 (-4*α)).symm
      _ = _:=by congr 1;ring
  have hpd:r^d ≤ r^4:=pow_le_pow_of_le_one hr hrOne hd
  have hpg:r^(2*(d-1)) ≤ r^4:=pow_le_pow_of_le_one hr hrOne (by omega)
  have hpc:r^(2*(d-2)) ≤ r^4:=pow_le_pow_of_le_one hr hrOne (by omega)
  have hT1:=mul_le_mul_of_nonneg_left hpd hN0
  have hT2:=mul_le_mul_of_nonneg_left hpg hN0
  have hT3:r^(2*(d-2)) ≤ N*r^4:=hpc.trans (by nlinarith [mul_le_mul_of_nonneg_right hN (pow_nonneg hr 4)])
  refine ⟨by linarith,?_⟩
  have hTwo:(N^(-α))^2=N^(-2*α):=by
    rw [←Real.rpow_two,←Real.rpow_mul hN0]
    congr 1
    ring
  have hQuad:r^2 ≤ N^(-(1/2:ℝ)):=by
    calc
      _ ≤ (N^(-α))^2:=pow_le_pow_left₀ hr hCore 2
      _ = N^(-2*α):=hTwo
      _ ≤ _:=Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hpd2:r^(d-2) ≤ r^2:=pow_le_pow_of_le_one hr hrOne (by omega)
  rw [←inverse_sqrt_eq_rpow hN0] at hQuad
  rw [show 2/Real.sqrt N=2*(1/Real.sqrt N) by ring]
  linarith

lemma local_overlap_scalar_envelope {N r δ:ℝ} {d:ℕ} (hN:1 ≤ N)
    (hr:0 ≤ r) (hd:4 ≤ d) (hrδ:r ≤ δ) (hδ:δ ≤ 1) :
    N*r^d+N*r^(2*(d-1))+r^(2*(d-2)) ≤ 3*δ^2*N*r^2 ∧
      r^(d-2)+1/Real.sqrt N ≤ 2:=by
  have hN0:0 ≤ N:=by linarith
  have hrOne:r ≤ 1:=hrδ.trans hδ
  have hpd:r^d ≤ r^4:=pow_le_pow_of_le_one hr hrOne hd
  have hpg:r^(2*(d-1)) ≤ r^4:=pow_le_pow_of_le_one hr hrOne (by omega)
  have hpc:r^(2*(d-2)) ≤ r^4:=pow_le_pow_of_le_one hr hrOne (by omega)
  have hT1:=mul_le_mul_of_nonneg_left hpd hN0
  have hT2:=mul_le_mul_of_nonneg_left hpg hN0
  have hT3:r^(2*(d-2)) ≤ N*r^4:=hpc.trans (by nlinarith [mul_le_mul_of_nonneg_right hN (pow_nonneg hr 4)])
  have hQuartic:r^4 ≤ δ^2*r^2:=by
    have hh:=mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr hrδ 2) (sq_nonneg r)
    nlinarith
  have hRate:=mul_le_mul_of_nonneg_left hQuartic hN0
  refine ⟨by nlinarith,?_⟩
  have hPower:r^(d-2) ≤ 1:=pow_le_one₀ hr hrOne
  have hRoot:1 ≤ Real.sqrt N:=(Real.le_sqrt (by norm_num) hN0).mpr (by simpa using hN)
  have hInv:1/Real.sqrt N ≤ 1:=(div_le_one (by positivity : 0<Real.sqrt N)).mpr hRoot
  linarith

lemma ambient_central_rate_tendsto {α:ℝ} (hα:1/4<α) :
    Tendsto (fun n:ℕ=>((n+3:ℕ):ℝ)^(1-4*α)) atTop (𝓝 0):=by
  have hN:Tendsto (fun n:ℕ=>((n+3:ℕ):ℝ)) atTop atTop:=tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 3)
  have hh:=(tendsto_rpow_neg_atTop (show 0<4*α-1 by linarith)).comp hN
  convert hh using 1
  funext n
  congr 1
  ring

lemma ambient_inverse_sqrt_tendsto :
    Tendsto (fun n:ℕ=>1/Real.sqrt ((n+3:ℕ):ℝ)) atTop (𝓝 0):=by
  have hN:Tendsto (fun n:ℕ=>((n+3:ℕ):ℝ)) atTop atTop:=tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 3)
  have hh:=(tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/2)).comp hN
  convert hh using 1
  funext n
  exact inverse_sqrt_eq_rpow (by positivity)

end
end SlowEquilibration.PairSchurExpectation
