(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Unavoid.thy
    Unavoidability assembly: a minimal counterexample has a hub of positive score whose arity lies
    in 5..11, and the presentation checks exclude each such arity (unavoidability.v).
    Ported from G. Gonthier's Coq development.
*)
theory Unavoid
  imports Four_Colour_Presentations.PresentBase
begin

section \<open>Euler's formula for a minimal counterexample\<close>

lemma (in birk) mce_euler: "6 * fcard f D = card D + 12"
proof -
  have cub: "cubic G" by (rule minimal_counter_example_is_cubic[OF mce])
  have "ucycle_plain_quasicubic_connected G []"
    using plainG cub connectedG hypermap_axioms
    by (simp add: ucycle_plain_quasicubic_connected_def ucycle_plain_quasicubic_def
        plain_quasicubic_def quasicubic_def cubic_def ucycle_def cycle_def)
  from quasicubic_Euler[OF this] planarG show ?thesis by simp
qed

section \<open>Discharge rule sizes\<close>

lemma drules_psize: "list_all (\<lambda>p. 5 \<le> psize p \<and> psize p \<le> 8) the_drules" by eval

lemma pick_source_nil: "\<not> (5 \<le> n \<and> n \<le> 8) \<Longrightarrow> pick_source_drules n = []"
  using drules_psize by (auto simp: pick_source_drules_def list_all_iff filter_empty_conv)

section \<open>Bounding the score of a hub\<close>

context present_ctx
begin

lemma dscore1_cap:
  assumes m: "minimal_counter_example (G :: 'a hypermap)" and yD: "y \<in> darts G"
    and ck: "\<And>n. 5 \<le> n \<Longrightarrow> n \<le> 8 \<Longrightarrow> check_dbound1 n (redpart qt) (pcons_any n) 5"
  shows "dscore1 G y \<le> 5"
proof -
  interpret P: pcp G by (rule mce_pcp[OF m])
  define x where "x = inv_face2 G y"
  have xD: "x \<in> darts G" using yD by (simp add: x_def inv_face2_def)
  have yx: "y = face G (face G x)" by (simp add: x_def)
  define nh where "nh = arity G x"
  have d1: "dscore1 G y = int (dbound1 G (pick_source_drules nh) x)"
    using P.dbound1_eq[of x nh] yx by (simp add: nh_def)
  show ?thesis
  proof (cases "5 \<le> nh \<and> nh \<le> 8")
    case False
    then show ?thesis using d1 pick_source_nil[OF False] by (simp add: dbound1_def)
  next
    case True
    have c: "check_dbound1 nh (redpart qt) (pcons_any nh) 5" using ck True by blast
    have ef: "exact_fitp G x (pcons_any nh)"
      using P.exact_fitp_pcons_any[OF P.pentaG xD] by (simp add: nh_def)
    have rp: "\<And>z p. z \<in> darts G \<Longrightarrow> redpart qt p \<Longrightarrow> \<not> exact_fitp G z p"
      using redpart_ok[OF m] by blast
    have cr: "check_dbound1_rec (redpart qt) (pcons_any nh) (pick_source_drules nh) 5
        (length (pick_source_drules nh) + 1)"
      using c unfolding check_dbound1_def by (simp only: Let_def)
    have "dbound1 G (pick_source_drules nh) x \<le> 5"
      by (rule P.check_dbound1_rec_ok[OF rp xD ef cr])
    then show ?thesis using d1 by simp
  qed
qed

lemma valid_hub_arity:
  assumes vh: "valid_hub (G :: 'a hypermap) x"
    and ck: "\<And>n. 5 \<le> n \<Longrightarrow> n \<le> 8 \<Longrightarrow> check_dbound1 n (redpart qt) (pcons_any n) 5"
  shows "5 \<le> arity G x \<and> arity G x \<le> 11"
proof -
  have m: "minimal_counter_example G" and xD: "x \<in> darts G" and pos: "0 < dscore G x"
    using vh by (simp_all add: valid_hub_def)
  interpret P: pcp G by (rule mce_pcp[OF m])
  have "arity G x < 12"
    by (rule P.dscore_cap1[of 5, OF _ xD pos]) (use dscore1_cap[OF m _ ck] in auto)
  then show ?thesis using P.pentaG[OF xD] by simp
qed

theorem no_minimal_counter_example:
  assumes ck: "\<And>n. 5 \<le> n \<Longrightarrow> n \<le> 8 \<Longrightarrow> check_dbound1 n (redpart qt) (pcons_any n) 5"
    and ex: "\<And>n. 5 \<le> n \<Longrightarrow> n \<le> 11 \<Longrightarrow> \<exists>s. check_ps qt [] (pcons_any n) (pcons_any n) s"
  shows "\<not> minimal_counter_example (G :: 'a hypermap)"
proof
  assume m: "minimal_counter_example G"
  interpret B: birk G by (simp add: birk_def birk_axioms_def mce_hypermap m)
  obtain x where xD: "x \<in> darts G" and pos: "0 < dscore G x"
    using B.posz_dscore[OF B.mce_euler] by blast
  have vh: "valid_hub G x" using m xD pos by (simp add: valid_hub_def)
  have r: "5 \<le> arity G x \<and> arity G x \<le> 11" by (rule valid_hub_arity[OF vh ck])
  then obtain s where "check_ps qt [] (pcons_any (arity G x)) (pcons_any (arity G x)) s"
    using ex by blast
  from exclude_arity[OF this vh] show False by simp
qed

end

end
