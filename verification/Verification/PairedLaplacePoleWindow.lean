import Verification.GeneralLaplaceMoments
import Verification.CriticalGammaWindow
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-! # A single Laplace pole forces signed oscillation on power windows -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace D5.S3.Analytic.Laplace.PairedLaplacePoleWindow

private def coeff (F : ℂ → ℂ) (k : ℕ) (s : ℂ) : ℂ :=
  ((-1 : ℂ) ^ k / k.factorial) * iteratedDeriv k F s

private lemma normalize_coefficients (q c : ℂ) (a : ℕ → ℂ) {r B : ℝ}
    (hq : q ≠ 0) (hc : c ≠ 0) (hr : 0 < r)
    (h : ∀ n : ℕ, ‖a n - c * ((-1 : ℂ)^n * n.factorial * q^(-1-(n : ℤ)))‖ ≤
      (n.factorial : ℝ) * B / r^n) :
    let J := fun n : ℕ => q^(n+1) * ((-1 : ℂ)^n / n.factorial) * a n
    (∀ n : ℕ, ‖J n - c‖ ≤ B * ‖q‖ * (‖q‖ / r)^n) ∧
    (‖q‖ < r → Tendsto J atTop (𝓝 c) ∧ ∀ᶠ n in atTop, ‖c‖ / 2 ≤ ‖J n‖) := by
  intro J
  have bound (n : ℕ) : ‖J n - c‖ ≤ B * ‖q‖ * (‖q‖ / r)^n := by
    let K := q^(n+1) * ((-1 : ℂ)^n / n.factorial)
    have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hpow : q^(-1-(n : ℤ)) = (q^(n+1))⁻¹ := by
      rw [show (-1-(n : ℤ)) = -((n+1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
    have hsign : (-1 : ℂ)^n * (-1 : ℂ)^n = 1 := by rw [← mul_pow]; simp
    have cancel : K * (c * ((-1 : ℂ)^n * n.factorial * q^(-1-(n : ℤ)))) = c := by
      rw [hpow]
      dsimp only [K]
      field_simp [hn, hq]
      simpa only [pow_two] using hsign
    have herr : J n - c = K * (a n - c * ((-1 : ℂ)^n * n.factorial * q^(-1-(n : ℤ)))) := by
      rw [mul_sub, cancel]
    rw [herr, norm_mul]
    apply (mul_le_mul_of_nonneg_left (h n) (norm_nonneg K)).trans_eq
    dsimp only [K]
    simp only [norm_mul, norm_pow, norm_div, norm_neg, norm_one, one_pow, Complex.norm_natCast,
      div_pow, pow_succ]
    field_simp [hr.ne', Nat.factorial_ne_zero]
  refine ⟨bound, fun hqr => ?_⟩
  have hdecay := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (div_nonneg (norm_nonneg q) hr.le) ((div_lt_one hr).mpr hqr)).const_mul (B * ‖q‖)
  have hlim : Tendsto J atTop (𝓝 c) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) bound (by simpa using hdecay)
  exact ⟨hlim, (hlim.norm.eventually (eventually_gt_nhds (half_lt_self (norm_pos_iff.mpr hc)))).mono
    fun n hn => hn.le⟩

private lemma complex_disk_dominance {F H : ℂ → ℂ} {p z c : ℂ} {r : ℝ}
    (hpz : p ≠ z) (hc0 : c ≠ 0) (hr : 0 < r) (hdr : ‖p - z‖ < r)
    (haF : ∀ s ∈ Metric.closedBall p r, s ≠ z → AnalyticAt ℂ F s)
    (hH : AnalyticAt ℂ H z)
    (hprincipal : F =ᶠ[𝓝[≠] z] fun s => c / (s - z) + H s) :
    ∀ᶠ k : ℕ in atTop, ‖c‖ / 2 ≤ ‖(p - z)^(k+1) * coeff F k p‖ := by
  let P := fun s : ℂ => c / (s - z)
  let G := Function.update (fun s => F s - P s) z (H z)
  have hoff (s : ℂ) (hs : s ≠ z) : G s = F s - P s := Function.update_of_ne hs _ _
  have hgerm : G =ᶠ[𝓝 z] H := by
    have h := eventually_nhdsWithin_iff.mp hprincipal
    filter_upwards [h] with s he
    by_cases hs : s = z
    · subst s
      exact Function.update_self ..
    · rw [hoff s hs, he hs]
      ring
  have haP {s : ℂ} (hs : s ≠ z) : AnalyticAt ℂ P s :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hs)
  have hmodel (s : ℂ) (hs : s ≠ z) : G =ᶠ[𝓝 s] fun w => F w - P w :=
    (continuousAt_id.eventually_ne hs).mono fun w hw => hoff w hw
  have ha : AnalyticOnNhd ℂ G (Metric.closedBall p r) := by
    intro s hs
    by_cases hsz : s = z
    · subst s
      exact hH.congr hgerm.symm
    · exact ((haF s hs hsz).sub (haP hsz)).congr (hmodel s hsz).symm
  obtain ⟨B, hB⟩ := (isCompact_closedBall p r).exists_bound_of_continuousOn ha.continuousOn
  have hraw (n : ℕ) :
      ‖iteratedDeriv n F p - c * ((-1 : ℂ)^n * n.factorial * (p - z)^(-1-(n : ℤ)))‖ ≤
        (n.factorial : ℝ) * max B 0 / r^n := by
    have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr
      (ha.differentiableOn.diffContOnCl_ball (Subset.rfl)) (fun w hw =>
        (hB w (Metric.sphere_subset_closedBall hw)).trans (le_max_left B 0))
    rw [(hmodel p hpz).iteratedDeriv_eq n, iteratedDeriv_fun_sub
      (haF p (Metric.mem_closedBall_self hr.le) hpz).contDiffAt (haP hpz).contDiffAt] at hc
    have hP : iteratedDeriv n P p = c * ((-1 : ℂ)^n * n.factorial * (p - z)^(-1-(n : ℤ))) := by
      dsimp only [P]
      simp only [div_eq_mul_inv, iteratedDeriv_const_mul_field]
      rw [iteratedDeriv_comp_sub_const (f := Inv.inv), iteratedDeriv_eq_iterate]
      exact congrArg (c * ·) (iter_deriv_inv n (p - z))
    rwa [hP] at hc
  simpa only [coeff, mul_assoc] using ((normalize_coefficients (p - z) c
    (fun n => iteratedDeriv n F p) (sub_ne_zero.mpr hpz) hc0 hr hraw).2 hdr).2


private lemma paired_disk_lower {F H : ℂ → ℂ} {p z c : ℂ} {r : ℝ}
    (hc : c ≠ 0) (hd : 0 < ‖p - z‖) (hdr : ‖p - z‖ < r)
    (hcomplex : ∀ s ∈ Metric.closedBall p r, s ≠ z → AnalyticAt ℂ F s)
    (hreal : AnalyticOnNhd ℂ F (Metric.closedBall (p.re : ℂ) r))
    (hH : AnalyticAt ℂ H z)
    (hprincipal : F =ᶠ[𝓝[≠] z] fun s => c / (s - z) + H s) :
    ∃ L : ℝ, 0 < L ∧ ∀ᶠ k : ℕ in atTop,
      L ≤ ‖p - z‖^k * (‖coeff F k p‖ - |(coeff F k (p.re : ℂ)).re|) := by
  have hr := hd.trans hdr
  have hpz := sub_ne_zero.mp (norm_pos_iff.mp hd)
  have hc0 : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hconv := complex_disk_dominance hpz hc hr hdr hcomplex hH hprincipal
  obtain ⟨B, hB⟩ := (isCompact_closedBall (p.re : ℂ) r).exists_bound_of_continuousOn
    hreal.continuousOn
  have hsmall := (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hd.le hr.le)
    ((div_lt_one hr).mpr hdr)).const_mul B
  have herr : ∀ᶠ k : ℕ in atTop, B * (‖p - z‖/r)^k < ‖c‖ / (4*‖p - z‖) := by
    apply (tendsto_order.mp (by simpa using hsmall :
      Tendsto (fun k : ℕ => B * (‖p - z‖/r)^k) atTop (𝓝 0))).2
    positivity
  refine ⟨‖c‖ / (4*‖p - z‖), by positivity, ?_⟩
  filter_upwards [herr, hconv] with k he hk
  have hcr := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr
    (hreal.differentiableOn.diffContOnCl_ball (Subset.rfl))
    (fun w hw => hB w (Metric.sphere_subset_closedBall hw))
  have hfac : (0 : ℝ) < k.factorial := by positivity
  have hrc : ‖coeff F k (p.re : ℂ)‖ ≤ B / r^k := by
    unfold coeff
    simp only [norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast]
    change 1 / (k.factorial : ℝ) * _ ≤ _
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hfac]
    exact hcr.trans_eq (by ring)
  have hscale : ‖p - z‖^k * ‖coeff F k (p.re : ℂ)‖ ≤ B * (‖p - z‖/r)^k :=
    (mul_le_mul_of_nonneg_left hrc (pow_nonneg hd.le _)).trans_eq (by rw [div_pow]; ring)
  have hcplx : ‖c‖ / 2 ≤ ‖p - z‖^(k+1) * ‖coeff F k p‖ := by
    rw [← norm_pow, ← norm_mul]
    exact hk
  have hpos : ‖c‖ / (2*‖p - z‖) ≤ ‖p - z‖^k * ‖coeff F k p‖ := by
    rw [div_mul_eq_div_div, div_le_iff₀ hd]
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hcplx
  have hn := (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm (coeff F k (p.re : ℂ)))
    (pow_nonneg hd.le k)).trans hscale
  rw [mul_sub]
  have hid : ‖c‖ / (2*‖p - z‖) = 2 * (‖c‖ / (4*‖p - z‖)) := by ring
  linarith



/-- At a fixed convergence rate, an isolated closer complex pole and two
Gamma tail estimates force values beyond a signed exponential envelope in
every sufficiently late interval of the prescribed relative width. -/
theorem signed_peaks_of_paired_disks {g : ℝ → ℝ} {F H : ℂ → ℂ}
    {p z c : ℂ} {r b h M α σ₀ : ℝ}
    (hg : Continuous g)
    (hF : ∀ s : ℂ, σ₀ < s.re →
      IntegrableOn (fun u : ℝ => Complex.exp (-s * u) * (g u : ℂ)) (Ioi 0) ∧
      (∫ u : ℝ in Ioi 0, Complex.exp (-s * u) * (g u : ℂ)) = F s)
    (hM : ∀ u, 0 ≤ u → |g u| ≤ M * Real.exp (2*u))
    (hM0 : 0 ≤ M)
    (hp : σ₀ < p.re) (hσ : 0 < p.re) (hα : 0 ≤ α)
    (hc : c ≠ 0) (hd : 0 < ‖p - z‖) (hdr : ‖p - z‖ < r)
    (hgap : ‖p - z‖ < p.re - α)
    (hcomplex : ∀ s ∈ Metric.closedBall p r, s ≠ z → AnalyticAt ℂ F s)
    (hreal : AnalyticOnNhd ℂ F (Metric.closedBall (p.re : ℂ) r))
    (hH : AnalyticAt ℂ H z)
    (hprincipal : F =ᶠ[𝓝[≠] z] fun s => c / (s - z) + H s)
    (hh : 1 < h) (hb : h < b)
    (htilt : 2 < p.re * (1 - h/b))
    (hLtail : 0 ≤ p.re*(h*Real.log h-h+1)-2)
    (hRtail : 0 ≤ p.re*(b-h-h*Real.log (b/h))-2*b)
    {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ T : ℝ in atTop, ∀ e : ℝ, e = 1 ∨ e = -1 →
      ∃ u ∈ Icc T (b*T), C * Real.exp (α*u) < e*g u := by
  let σ := p.re
  let d := ‖p - z‖
  let A := M * (1/σ + b/(h*σ))
  have hh0 : 0 < h := by linarith
  have hb1 : 1 < b := hh.trans hb
  have hb0 : 0 < b := by linarith
  have hα' : α < σ := by dsimp [σ]; linarith
  have hdσ : d < σ := hgap.trans_le (sub_le_self _ hα)
  obtain ⟨L, hL, hD⟩ := paired_disk_lower hc hd hdr hcomplex hreal hH hprincipal
  have hgamma := CriticalGammaWindow.adjustable_window_off_mass hh hb
  let ℓ := σ*(h*Real.log h-h+1)-2
  let r' := σ*(b-h-h*Real.log (b/h))-2*b
  have hK : Tendsto (fun T : ℝ => ⌊σ*h*T⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (Filter.tendsto_id.const_mul_atTop (mul_pos hσ hh0))
  let q := d/(σ-α)
  let q' := d/σ
  have hq : 0 < q := div_pos hd (sub_pos.mpr hα')
  have hq1 : q < 1 := (div_lt_one (sub_pos.mpr hα')).mpr hgap
  have hq' : 0 < q' := div_pos hd hσ
  have hq1' : q' < 1 := (div_lt_one hσ).mpr hdσ
  have htime (j : ℝ) (hj : 0 < j) (hj1 : j < 1) :
      Tendsto (fun T : ℝ => T * j ^ ⌊σ*h*T⌋₊) atTop (𝓝 0) := by
    have hjlog : Real.log j < 0 := Real.log_neg hj hj1
    let τ := (σ*h) * Real.log j
    have hτ : τ < 0 := mul_neg_of_pos_of_neg (mul_pos hσ hh0) hjlog
    have hExp := (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (show τ / 2 < 0 by linarith))).const_mul j⁻¹
    have hLin : Tendsto (fun T : ℝ => T * Real.exp ((τ/2)*T)) atTop (𝓝 0) := by
      have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (-(τ/2))
        (neg_pos.mpr (show τ / 2 < 0 by linarith)))
      simpa only [Real.rpow_one, neg_neg] using h
    have hprod := hExp.mul hLin
    rw [mul_zero] at hprod
    apply squeeze_zero' _ _ hprod
    · exact (eventually_ge_atTop (0 : ℝ)).mono fun T hT => mul_nonneg hT (by positivity)
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      have hfloor := Nat.lt_floor_add_one (σ*h*T)
      have he := mul_le_mul_of_nonpos_right (show σ*h*T - 1 ≤ (⌊σ*h*T⌋₊ : ℝ) by linarith)
        hjlog.le
      have hup := Real.exp_le_exp.mpr he
      rw [show Real.exp ((⌊σ*h*T⌋₊ : ℝ) * Real.log j) = j ^ ⌊σ*h*T⌋₊ by
        rw [mul_comm, ← Real.rpow_def_of_pos hj, Real.rpow_natCast],
        show (σ*h*T - 1) * Real.log j = -Real.log j + (τ/2)*T + (τ/2)*T by dsimp [τ]; ring,
        Real.exp_add, Real.exp_add, Real.exp_neg, Real.exp_log hj] at hup
      exact (mul_le_mul_of_nonneg_left hup hT).trans_eq (by
        simp only [Function.comp_apply, id_eq]
        ring)
  have htailLim := ((tendsto_pow_atTop_nhds_zero_of_lt_one hq'.le hq1').comp hK).const_mul (2*A)
  have hboundLim := (htime q hq hq1).const_mul (2*C*(b-1))
  have hsmall : ∀ᶠ T : ℝ in atTop,
      2*C*(b-1) * (T*q^⌊σ*h*T⌋₊) + 2*A*q'^⌊σ*h*T⌋₊ < L := by
    have hh := hboundLim.add htailLim
    rw [mul_zero, mul_zero, add_zero] at hh
    exact hh.eventually_lt_const hL
  filter_upwards [eventually_gt_atTop (0 : ℝ), hK.eventually hD, hsmall] with T hT hdisc hsmallT
  intro e he
  by_contra! hnone
  let k := ⌊σ*h*T⌋₊
  have hTb : T ≤ b*T := le_mul_of_one_le_left hT.le hb1.le
  have hwindow (u : ℝ) (hu : u ∈ Icc T (b*T)) :
      max (e*g u) 0 * Real.exp (-α*u) ≤ C := by
    have hu' : max (e*g u) 0 ≤ C * Real.exp (α*u) :=
      max_le (hnone u hu) (by positivity)
    calc
      _ ≤ (C * Real.exp (α*u))*Real.exp (-α*u) :=
        mul_le_mul_of_nonneg_right hu' (by positivity)
      _ = C := by rw [neg_mul, mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  have hlocal : (∫ u in T..b*T, max (e*g u) 0 * Real.exp (-α*u)) ≤ C*((b-1)*T) := by
    have hcont : Continuous (fun u : ℝ => max (e*g u) 0 * Real.exp (-α*u)) :=
      ((hg.const_mul e).max continuous_const).mul (by fun_prop)
    have hl := intervalIntegral.integral_mono_on (μ := volume) hTb (hcont.intervalIntegrable _ _)
      (intervalIntegrable_const (c := C)) hwindow
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using
      hl.trans_eq (by simp only [intervalIntegral.integral_const, smul_eq_mul]; ring)
  have hTail := (hgamma.2 htilt hT hg.measurable hM).2
  have ht : (∫ u in Ioi (0 : ℝ) \ Icc T (b*T),
      |g u| * (u^k * Real.exp (-σ*u) / k.factorial)) ≤ A * σ⁻¹^k := by
    simp only [neg_mul]
    apply hTail.trans
    have hleft : Real.exp (-ℓ*T) ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hLtail) hT.le)
    have hright : Real.exp (-r'*T) ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hRtail) hT.le)
    calc
      _ ≤ (M*σ⁻¹^k) * (1/σ + b/(h*σ)*1) := by gcongr
      _ = _ := by dsimp [A]; ring
  have hB := GeneralLaplaceMoments.signed_window_moment_bound hg hF k hp hT hTb hα' he
  change ‖coeff F k p‖ + e * (coeff F k (σ : ℂ)).re ≤ _ at hB
  have hsignLower : -|(coeff F k (σ : ℂ)).re| ≤ e * (coeff F k (σ : ℂ)).re := by
    rcases he with rfl | rfl
    · rw [one_mul]
      exact neg_le.mp (neg_le_abs _)
    · simpa only [neg_one_mul, neg_le_neg_iff] using le_abs_self (coeff F k (σ : ℂ)).re
  have hupper : ‖coeff F k p‖ - |(coeff F k (σ : ℂ)).re| ≤
      2*(σ-α)⁻¹^k * (C*((b-1)*T)) + 2*(A*σ⁻¹^k) := by
    refine (show _ ≤ ‖coeff F k p‖ + e * (coeff F k (σ : ℂ)).re by linarith).trans
      (hB.trans (add_le_add ?_ (mul_le_mul_of_nonneg_left ht (by norm_num))))
    exact mul_le_mul_of_nonneg_left hlocal (by positivity)
  apply (not_lt_of_ge (hdisc.trans (mul_le_mul_of_nonneg_left hupper (pow_nonneg hd.le _))))
  simpa only [k, q, q', div_pow] using
    (show d^k * (2*(σ-α)⁻¹^k * (C*((b-1)*T)) + 2*(A*σ⁻¹^k)) < L by
      rw [show d^k * (2*(σ-α)⁻¹^k * (C*((b-1)*T)) + 2*(A*σ⁻¹^k)) =
        2*C*(b-1)*(T*q^k) + 2*A*q'^k by
          simp only [q, q', div_eq_mul_inv, inv_pow]; ring]
      exact hsmallT)

#print axioms signed_peaks_of_paired_disks

end D5.S3.Analytic.Laplace.PairedLaplacePoleWindow
