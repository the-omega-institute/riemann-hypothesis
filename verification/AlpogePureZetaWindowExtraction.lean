import Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion

/-! Extract the ordinary-zeta window estimate before the published proof's
zero-free reduction. Source pin c7d25b3bfd7906388bb8eb0774e027a2b756a7b6. -/

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.HC GlobalTheory.Fc GlobalTheory.EX

namespace PureZetaWindowExtraction

private theorem cyc_one_Gm (x : ℝ) : (Level.cyc PChar.one).Gm x = Formalism.Gz x := by
  classical
  have hmem (ψ : PChar) (hψ : ψ ∈ (Level.cyc PChar.one).KEPT) : ψ = PChar.one := by
    rw [Level.cyc, Level.mem_ofSub] at hψ
    obtain ⟨χ, hχ, heq⟩ := hψ
    change χ ∈ Subgroup.zpowers (1 : DirichletCharacter ℂ 1) at hχ
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hχ
    subst χ
    exact heq.symm.trans (PChar.of_one 1)
  have hNt : (Level.cyc PChar.one).Nt = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro ψ hψ
    change ψ ∈ (Level.cyc PChar.one).KEPT.erase PChar.one at hψ
    have h := Finset.mem_erase.mp hψ
    exact h.1 (hmem ψ h.2)
  simp [Level.Gm, hNt]

private theorem windows_of_host (H : UpperTheory.Top.TopG)
    (S : HostExW (3 / 2) (UpperTheory.Top.GChi PChar.one).req) :
    ∀ κ : ℝ, 0 < κ → ∀ R : ℝ, ∃ Y : ℝ, max R 2 ≤ Y ∧
      ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (3 / 2 : ℝ) → Formalism.Gz x ≤ x ^ (1 / 2 + κ) := by
  have hb : (1 : ℝ) < 3 / 2 := by norm_num
  obtain ⟨eD, eL, ε₁, hε₁, hw⟩ :=
    H (3 / 2) (UpperTheory.Top.GChi PChar.one) hb S
      (UpperTheory.Top.hypV_of_cls PChar.one (3 / 2))
  intro κ hκ R
  obtain ⟨ε, hε, hεlt, hκ'⟩ := exists_small_eps (eD+eL+7) hκ hε₁
  obtain ⟨Fm, hClass, hT⟩ := hw ε hε hεlt
  obtain ⟨x₁, hx₁⟩ := UpperTheory.Comparison₂.level_gm_le_on_family_scales
    (Level.cyc PChar.one) eD eL ε hε Fm
    (UpperTheory.Top.eFamC_of_cls PChar.one (3 / 2) Fm hClass) hT
  have hWindows := (windows_iff Fm.toFamCore (3 / 2)).1 hClass.1
  obtain ⟨Y, hY, hYw⟩ := hWindows (max (max R 2) x₁)
  refine ⟨Y, (le_max_left _ _).trans hY, fun x hx hx' => ?_⟩
  have hxbase : 1 ≤ x := by
    have h2 : 2 ≤ x := ((le_max_right R 2).trans ((le_max_left _ _).trans hY)).trans hx
    linarith
  have hEstimate := hx₁ x ((le_max_right _ _).trans (hY.trans hx)) (hYw x hx hx')
  rw [cyc_one_Gm] at hEstimate
  exact hEstimate.trans (Real.rpow_le_rpow_of_exponent_le hxbase (by linarith))

theorem pure_zeta_windows :
    ∀ κ : ℝ, 0 < κ → ∀ R : ℝ, ∃ Y : ℝ, max R 2 ≤ Y ∧
      ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (3 / 2 : ℝ) → Formalism.Gz x ≤ x ^ (1 / 2 + κ) := by
  let row := UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
  let O : UpperTheory.LiteratureTheorems.OpenLiteratureStatements :=
    ⟨row, UpperTheory.Zero.LLC.recTExists, row⟩
  let P := UpperTheory.LiteratureTheorems.published_results_eigen O
  let F := UpperTheory.LiteratureTheorems.published_results_first O
  let hMatch := UpperTheory.LiteratureTheorems.theta_integrals_agree_and_local_matching_of_literature O
  let hX := (_root_.SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt (_root_.UpperTheory.LiteratureTheorems.resolution_char_zero_of_literature O) (_root_.UpperTheory.LiteratureTheorems.principalisation_char_zero_of_literature O) (_root_.UpperTheory.LiteratureTheorems.poincare_lelong_inv_of_literature O) PositivityTheory.Pf1.HilbertSamuelMoriwaki.hsUse_outright PositivityTheory.Pf1.HilbertSamuelMoriwaki.moriwakiBig_outright (_root_.UpperTheory.LiteratureTheorems.fargues_exact_of_literature O) (_root_.UpperTheory.LiteratureTheorems.zarhin_statement O) (_root_.UpperTheory.LiteratureTheorems.nef_rr_of_literature O) (_root_.UpperTheory.LiteratureTheorems.siegel_toroidal_integral_of_literature O) (_root_.UpperTheory.LiteratureTheorems.toroidal_for_fan_ks_of_literature O) (_root_.UpperTheory.LiteratureTheorems.semi_abelian_lie_seminegative_of_literature O) (_root_.UpperTheory.LiteratureTheorems.point_separation_pair_of_literature O) (_root_.UpperTheory.LiteratureTheorems.ar_degree_of_literature O) (_root_.UpperTheory.LiteratureTheorems.published_results_arithmetic O) (_root_.UpperTheory.LiteratureTheorems.grothendieck_deformation_of_literature O))
  let hL := UpperTheory.LiteratureTheorems.local_langlands_gl_recT_exists_of_literature O
  have hG := GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters
  obtain ⟨h⟩ := UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound
    P F hMatch.1 hMatch.2 hX hL (fun cDep =>
      UpperTheory.N.boundAtTwoThree_linked_of_recT P.nLink
        (GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep))
  exact windows_of_host
    (GlobalTheory.Fc.forall_goal_of_shape_of_hyps _ _ _ _
      (UpperTheory.Top.shape_closed_link_n_of_green hG) trivial trivial h)
    (UpperTheory.Top.supplyChi PChar.one ((UpperTheory.One.vwin_of_row row) PChar.one))

#print axioms pure_zeta_windows

end PureZetaWindowExtraction
