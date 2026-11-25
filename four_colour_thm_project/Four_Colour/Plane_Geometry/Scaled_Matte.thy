(* Scaled mattes, the final part of approx.v. G. Gonthier et al., CeCILL-B.
   Isabelle/HOL port: Codex. *)
theory Scaled_Matte
  imports Approx Matte
begin

type_synonym scaled_matte = "nat \<times> matte"
definition smatte_set :: "scaled_matte \<Rightarrow> rp_point set" where
  "smatte_set m = mem_approx (fst m) (set (mdisk (snd m)))"
definition valid_smatte :: "scaled_matte \<Rightarrow> bool" where
  "valid_smatte m \<longleftrightarrow> valid_matte (snd m)"
definition refine_smatte :: "nat \<Rightarrow> scaled_matte \<Rightarrow> scaled_matte" where
  "refine_smatte n m = (n+fst m, (refine_matte ^^ n) (snd m))"

lemma mem_approx_refine_matte:
  "mem_approx (Suc s) (set (mdisk (refine_matte m))) = mem_approx s (set (mdisk m))"
  by (auto simp: mem_approx_iff in_refine_matte point_approx_halfg)
lemma in_refine_smatte: "smatte_set (refine_smatte n m) = smatte_set m"
  unfolding refine_smatte_def smatte_set_def
  by (induction n) (simp_all add: mem_approx_refine_matte)
lemma iter_refine_matte_valid:
  "valid_matte m \<Longrightarrow> valid_matte ((refine_matte ^^ n) m)"
  by (induction n) (auto intro: refine_matte_valid)
lemma refine_smatte_valid:
  "valid_smatte m \<Longrightarrow> valid_smatte (refine_smatte n m)"
  by (simp add: valid_smatte_def refine_smatte_def iter_refine_matte_valid)

lemma point_matte_in_open:
  assumes op: "open U" and z: "z\<in>U"
  shows "\<exists>m :: scaled_matte. valid_smatte m \<and> z\<in>smatte_set m \<and> smatte_set m\<subseteq>U"
proof -
  obtain b where b: "z\<in>srect_set (inset_srect b)" "srect_set b\<subseteq>U"
    using approx_open[OF op z] by blast
  let ?s = "fst b"
  let ?p = "point_approx ?s z"
  let ?m = "(?s,point_matte ?p)"
  have valid: "valid_smatte ?m" by (simp add: valid_smatte_def point_matte_valid)
  have at: "z\<in>smatte_set ?m"
    by (simp add: smatte_set_def point_matte_def mem_approx_iff)
  have p: "?p\<in>grect_set (snd b)"
    using b(1) insetW[of "snd b"] by (auto simp: srect_set_def inset_srect_def mem_approx_iff)
  have "smatte_set ?m\<subseteq>srect_set b"
    using p by (auto simp: smatte_set_def point_matte_def srect_set_def mem_approx_iff)
  then have sub: "smatte_set ?m\<subseteq>U" using b(2) by blast
  show ?thesis by (rule exI[of _ ?m]) (use valid at sub in blast)
qed

end
