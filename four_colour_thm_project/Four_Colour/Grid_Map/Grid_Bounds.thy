(* Bounding boxes and the finite dart grid from gridmap.v.
   Original G. Gonthier et al., CeCILL-B. Isabelle/HOL port: Codex. *)
theory Grid_Bounds
  imports Grid_Adjacency
begin

lemma fold_extend_contains:
  "set ps \<union> grect_set r \<subseteq> grect_set (foldr extend_grect ps r)"
proof (induction ps)
  case Nil then show ?case by simp
next
  case (Cons p ps)
  have step: "insert p (grect_set (foldr extend_grect ps r)) \<subseteq>
      grect_set (extend_grect p (foldr extend_grect ps r))" by (rule in_extend_grect)
  have bound: "insert p (set ps \<union> grect_set r) \<subseteq>
      grect_set (extend_grect p (foldr extend_grect ps r))"
    by (rule subset_trans[OF insert_mono[OF Cons.IH] step])
  show ?case using bound by auto
qed

definition matte_bbox :: "nat \<Rightarrow> (nat\<Rightarrow>matte) \<Rightarrow> grect" where
  "matte_bbox k cm = foldr extend_grect (concat (map (\<lambda>i. mdisk (cm i)) [0..<k])) (Grect 0 1 0 1)"

lemma matte_bbox_contains:
  assumes "i<k"
  shows "set (mdisk (cm i)) \<subseteq> grect_set (matte_bbox k cm)"
proof -
  have sub: "set (mdisk (cm i)) \<subseteq> set (concat (map (\<lambda>i. mdisk (cm i)) [0..<k]))"
    using assms by auto
  show ?thesis using sub fold_extend_contains[of "concat (map (\<lambda>i. mdisk (cm i)) [0..<k])" "Grect 0 1 0 1"]
    unfolding matte_bbox_def by blast
qed

lemma matte_bbox_proper: "gr_proper (matte_bbox k cm)"
proof -
  have sub: "grect_set (Grect 0 1 0 1) \<subseteq> grect_set (matte_bbox k cm)"
    using fold_extend_contains[of "concat (map (\<lambda>i. mdisk (cm i)) [0..<k])" "Grect 0 1 0 1"]
    unfolding matte_bbox_def by blast
  have "garea (Grect 0 1 0 1) \<le> garea (matte_bbox k cm)" by (rule garea_subrect[OF sub])
  then show ?thesis by (simp add: gr_proper_def garea_def zwidth_def)
qed

definition gmgrid :: "grect \<Rightarrow> gpoint set" where
  "gmgrid r = grect_set (refine_rect r) \<union> gedge ` grect_set (refine_rect r)"

lemma finite_gmgrid [simp]: "finite (gmgrid r)"
  by (simp add: gmgrid_def)

lemma gmgrid_iff:
  "d\<in>gmgrid r \<longleftrightarrow> halfg d\<in>grect_set r \<or> halfg (gedge d)\<in>grect_set r"
  unfolding gmgrid_def
  by (metis Un_iff image_iff in_refine_rect gedge2)

lemma gmgrid_edge [simp]: "gedge d\<in>gmgrid r \<longleftrightarrow> d\<in>gmgrid r"
  by (simp only: gmgrid_iff gedge2 disj_commute)

end
