(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(* Authored by Codex; extracted from the inherited Unavoid.thy computations. *)
theory Score_Caps
  imports Four_Colour_Runtime.Certificate_Runtime
begin

section \<open>The score-cap checks\<close>

lemma cap5: "check_dbound1 5 (redpart the_quiz_tree) (pcons_any 5) 5" by eval
lemma cap6: "check_dbound1 6 (redpart the_quiz_tree) (pcons_any 6) 5" by eval
lemma cap7: "check_dbound1 7 (redpart the_quiz_tree) (pcons_any 7) 5" by eval
lemma cap8: "check_dbound1 8 (redpart the_quiz_tree) (pcons_any 8) 5" by eval

lemma caps: "5 \<le> n \<Longrightarrow> n \<le> 8 \<Longrightarrow> check_dbound1 n (redpart the_quiz_tree) (pcons_any n) 5"
  using cap5 cap6 cap7 cap8 by (cases "n = 5 \<or> n = 6 \<or> n = 7 \<or> n = 8") auto

end
