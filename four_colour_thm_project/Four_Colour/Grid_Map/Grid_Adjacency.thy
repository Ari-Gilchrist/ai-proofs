(* Adjacency realization for finite grid maps, from gridmap.v.
   Original G. Gonthier et al., CeCILL-B. Isabelle/HOL port: Codex. *)
theory Grid_Adjacency
  imports Four_Colour_Matte_Geometry.Matte_Port_Audit
begin

lemma madj_monotone_disjoint:
  assumes v1: "valid_matte m1" and v2: "valid_matte m2" and vn: "valid_matte n"
    and sub: "set (mdisk m2)\<subseteq>set (mdisk n)"
    and disjoint: "set (mdisk m1) \<inter> set (mdisk n) = {}"
    and adj: "madj m1 m2"
  shows "madj m1 n"
proof -
  obtain d where d: "d\<in>set (mring m2)" "gedge d\<in>set (mring m1)"
    using adj unfolding madj_def by blast
  have cell: "halfg d\<in>set (mdisk m2)"
    using d(1) by (simp only: in_mring[OF v2] gborder_def mem_Collect_eq; blast)
  have other: "halfg (gedge d)\<in>set (mdisk m1)"
    using d(2) by (simp only: in_mring[OF v1] gborder_def mem_Collect_eq; blast)
  have newcell: "halfg d\<in>set (mdisk n)" using cell sub by blast
  have outside: "halfg (gedge d)\<notin>set (mdisk n)" using other disjoint by blast
  have boundary: "d\<in>set (mring n)"
    using newcell outside by (simp only: in_mring[OF vn] gborder_def mem_Collect_eq; blast)
  show ?thesis using d(2) boundary unfolding madj_def by blast
qed

lemma matte_growth_unchanged_outside:
  assumes "set (mdisk m)\<subseteq>set (mdisk n)"
    "set (mdisk n)\<subseteq>A \<union> set (mdisk m)" "A \<inter> B = {}"
  shows "\<forall>p\<in>B. (p\<in>set (mdisk n) \<longleftrightarrow> p\<in>set (mdisk m))"
  using assms by blast

lemma coarse_in_unchanged_refine:
  assumes coarse: "coarse_in (grect_set (refine_rect r)) m"
    and equal: "\<forall>p\<in>grect_set (refine_rect r).
      (p\<in>set (mdisk n) \<longleftrightarrow> p\<in>set (mdisk m))"
  shows "coarse_in (grect_set (refine_rect r)) n"
  using assms unfolding coarse_in_def by (metis in_refine_rect)

lemma grid_cm_replace_proper:
  assumes proper: "grid_cm_proper k cm" and j: "j<k" and vn: "valid_matte n"
    and apart: "\<And>i. i<k \<Longrightarrow> i\<noteq>j \<Longrightarrow> set (mdisk (cm i)) \<inter> set (mdisk n) = {}"
  shows "grid_cm_proper k (cm(j:=n))"
  using assms unfolding grid_cm_proper_def
  by (auto simp: fun_upd_apply Int_commute split: if_splits)

lemma grid_adjacency_preserved_update:
  assumes old: "grid_cm_proper k cm" and new: "grid_cm_proper k (cm(j:=n))"
    and j: "j<k" and sub: "set (mdisk (cm j))\<subseteq>set (mdisk n)"
    and i: "i<k" and l: "l<k" and adj: "madj (cm i) (cm l)"
  shows "madj ((cm(j:=n)) i) ((cm(j:=n)) l)"
proof -
  have valid: "valid_matte (cm a)" if "a<k" for a
    using old that by (simp only: grid_cm_proper_def; blast)
  have updated_valid: "valid_matte ((cm(j:=n)) j)"
    using new j by (simp only: grid_cm_proper_def; blast)
  have vn: "valid_matte n" using updated_valid by simp
  have ne: "i\<noteq>l" using adj madj_irrefl[OF valid[OF i]] by blast
  have apart: "set (mdisk (cm a)) \<inter> set (mdisk n) = {}"
    if a: "a<k" and ne: "a\<noteq>j" for a
  proof -
    have "set (mdisk ((cm(j:=n)) a)) \<inter> set (mdisk ((cm(j:=n)) j)) = {}"
      using new a j ne by (simp only: grid_cm_proper_def; blast)
    then show ?thesis using ne by simp
  qed
  show ?thesis
  proof (cases "l=j")
    case True
    have ij: "i\<noteq>j" using ne True by blast
    have "madj (cm i) n"
      by (rule madj_monotone_disjoint[OF valid[OF i] valid[OF j] vn sub apart[OF i ij]])
        (use adj True in simp)
    then show ?thesis by (simp add: True ij)
  next
    case False
    show ?thesis
    proof (cases "i=j")
      case True
      have rev: "madj (cm l) (cm j)" using adj True by (simp only: madj_sym)
      have "madj (cm l) n"
        by (rule madj_monotone_disjoint[OF valid[OF l] valid[OF j] vn sub apart[OF l False] rev])
      then show ?thesis by (simp add: True False madj_sym)
    next
      case False
      then show ?thesis using \<open>l\<noteq>j\<close> adj by simp
    qed
  qed
qed

definition grid_adj_pending :: "(nat\<times>nat) set \<Rightarrow> (nat\<Rightarrow>matte) \<Rightarrow> (nat\<times>nat) set" where
  "grid_adj_pending E cm = {e\<in>E. \<not>madj (cm (fst e)) (cm (snd e))}"

lemma grid_adj_pending_update:
  assumes indices: "\<forall>e\<in>E. fst e<k \<and> snd e<k"
    and old: "grid_cm_proper k cm" and new: "grid_cm_proper k (cm(j:=n))"
    and j: "j<k" and sub: "set (mdisk (cm j))\<subseteq>set (mdisk n)"
  shows "grid_adj_pending E (cm(j:=n)) \<subseteq> grid_adj_pending E cm"
  unfolding grid_adj_pending_def
  using grid_adjacency_preserved_update[OF old new j sub] indices by blast

end
