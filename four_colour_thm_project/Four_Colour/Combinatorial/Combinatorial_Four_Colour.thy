(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
theory Combinatorial_Four_Colour
  imports Four_Colour_Checkers.Unavoid Four_Colour_Checkers.Quiz_Embed Four_Colour_Checkers.Four_Colour_Reduction
    Four_Colour_Quizzes.Quiz_Certificates Four_Colour_Reducibility.Reducibility
    Four_Colour_Unavoidability.Score_Caps Four_Colour_Unavoidability.Present5 Four_Colour_Unavoidability.Present6
    Four_Colour_Unavoidability.Present7 Four_Colour_Unavoidability.Present8 Four_Colour_Unavoidability.Present9
    Four_Colour_Unavoidability.Present10 Four_Colour_Unavoidability.Present11
begin

lemma presentation_certificates:
  assumes "5 \<le> k" "k \<le> 11"
  shows "\<exists>s. check_ps the_quiz_tree [] (pcons_any k) (pcons_any k) s"
proof -
  have "k = 5 \<or> k = 6 \<or> k = 7 \<or> k = 8 \<or> k = 9 \<or> k = 10 \<or> k = 11"
    using assms by presburger
  then show ?thesis using check5 check6 check7 check8 check9 check10 check11 by blast
qed

theorem unavoidability: "\<not> minimal_counter_example (G :: 'a hypermap)"
proof -
  have nf: "\<forall>y. \<not> qzt_ctx.qzt_fit H y the_quiz_tree"
    if m: "minimal_counter_example (H :: 'a hypermap)" for H
    unfolding the_quiz_tree_def
    using no_fit_config_tree[OF the_reducibility the_quiz_correctness the_config_program m] by blast
  interpret P: present_ctx "TYPE('a)" the_quiz_tree
    by unfold_locales (rule nf)
  show ?thesis
    by (rule P.no_minimal_counter_example[OF caps presentation_certificates])
qed

text \<open>The combinatorial Four Colour Theorem: every finite planar bridgeless
  hypermap admits a face colouring with four colours. All configuration and
  presentation obligations are discharged above, without additional hypotheses.\<close>

theorem four_color_hypermap:
  "planar_bridgeless G \<Longrightarrow> four_colorable G"
  by (rule four_colour_from_no_minimal_counterexample[OF unavoidability])

corollary (in hypermap) four_colour_theorem:
  "planar G \<Longrightarrow> bridgeless G \<Longrightarrow> four_colorable G"
  by (rule four_color_hypermap) (simp add: planar_bridgeless_def hypermap_axioms)


lemma (in hypermap) loopless_imp_bridgeless_dual:
  assumes l: "loopless G"
  shows "bridgeless (dual G)"
  unfolding bridgeless_def
proof (intro ballI notI)
  fix x assume x: "x\<in>darts (dual G)"
    and c: "fconnect (face (dual G)) x (edge (dual G) x)"
  have yD: "inv e x\<in>D" using x by (metis dual_simps(1) E.closed E.f_inv)
  have con: "cnode x (inv e x)" using c by (simp only: dual_simps N.fconnect_inv)
  have rev: "cnode (inv e x) x" by (rule N.fconnect_sym[OF con])
  have no: "\<not> cnode (inv e x) (e (inv e x))"
    using l yD by (auto simp only: loopless_def)
  show False using no rev by simp
qed

corollary (in hypermap) four_colour_graph:
  assumes p: "planar G" and l: "loopless G"
  shows "graph_four_colorable G"
proof -
  have geo: "planar_bridgeless (dual G)"
    using hypermap_dual planar_dual p loopless_imp_bridgeless_dual[OF l]
    by (simp add: planar_bridgeless_def)
  have "four_colorable (dual G)" by (rule four_color_hypermap[OF geo])
  then show ?thesis by (simp only: four_colorable_dual)
qed

text \<open>The public map and graph theorems are checked for skipped proofs and
  unexpected oracle dependencies. Certificate computation uses Isabelle's
  standard evaluation oracle; no other oracle is allowed.\<close>

ML \<open>
val four_colour_audited =
  [@{thm four_color_hypermap}, @{thm hypermap.four_colour_theorem},
   @{thm hypermap.four_colour_graph}];
val _ = if Thm_Deps.has_skip_proof four_colour_audited
  then error "The Four Colour Theorem depends on a skipped proof" else ();
val four_colour_oracles = Thm_Deps.all_oracles four_colour_audited;
val four_colour_unexpected = filter
  (fn ((name, _), _) => name <> \<^verbatim>\<open>Code_Generator.holds_by_evaluation\<close>)
  four_colour_oracles;
val _ = if null four_colour_unexpected then ()
  else error "The Four Colour Theorem has an unexpected oracle dependency";
val _ = writeln ("Four Colour proof audit passed; oracle dependencies: " ^
  commas (map (fn ((name, _), _) => name) four_colour_oracles));
\<close>

end
