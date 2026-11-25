(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
theory Four_Colour_Reduction
  imports Four_Colour_Presentations.PresentBase
begin

text \<open>The purely mathematical final reduction. The no-counterexample premise
  must still be discharged by the configuration and presentation certificates.\<close>

lemma colorable_if_no_minimal_counterexample:
  assumes no: "\<And>H :: 'a hypermap. \<not> minimal_counter_example H"
    and geo: "planar_bridgeless_plain_precubic (G :: 'a hypermap)"
  shows "four_colorable G"
  using geo
proof (induction "card (darts G)" arbitrary: G rule: less_induct)
  case less
  show ?case
  proof (rule ccontr)
    assume nc: "\<not> four_colorable G"
    have sm: "\<forall>H :: 'a hypermap. planar_bridgeless_plain_precubic H \<longrightarrow>
        card (darts H) < card (darts G) \<longrightarrow> four_colorable H"
      using less.hyps by blast
    have "minimal_counter_example G"
      using less.prems nc sm by (simp add: minimal_counter_example_def)
    then show False using no[of G] by contradiction
  qed
qed

theorem four_colour_from_no_minimal_counterexample:
  assumes no: "\<And>H :: (cube_tag \<times> 'a) hypermap. \<not> minimal_counter_example H"
    and geo: "planar_bridgeless (G :: 'a hypermap)"
  shows "four_colorable G"
proof -
  interpret H: hypermap G using geo by (simp add: planar_bridgeless_def)
  have p: "planar (cube G)" and b: "bridgeless (cube G)"
    using geo H.planar_cube H.bridgeless_cube by (simp_all add: planar_bridgeless_def)
  have cg: "planar_bridgeless_plain_precubic (cube G)"
    using H.hypermap_cube H.plain_cube H.cubic_cube H.cubic_precubic p b
    by (simp add: planar_bridgeless_plain_precubic_def planar_bridgeless_plain_def
        planar_bridgeless_def cubic_def cubicb_def precubic_def)
  have "four_colorable (cube G)" by (rule colorable_if_no_minimal_counterexample[OF no cg])
  then show ?thesis by (rule H.cube_colorable)
qed

end
