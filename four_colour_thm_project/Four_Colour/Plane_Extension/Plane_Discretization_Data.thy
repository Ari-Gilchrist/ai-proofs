(* Finite plane-map data preceding the grid-map construction in discretize.v.
   Original G. Gonthier et al., CeCILL-B. Isabelle/HOL port: Codex. *)
theory Plane_Discretization_Data
  imports Region_Mattes
begin

definition grid_cm_proper :: "nat \<Rightarrow> (nat \<Rightarrow> matte) \<Rightarrow> bool" where
  "grid_cm_proper k cm \<longleftrightarrow> (\<forall>i<k. valid_matte (cm i)) \<and>
    (\<forall>i<k. \<forall>j<k. i\<noteq>j \<longrightarrow> set (mdisk (cm i)) \<inter> set (mdisk (cm j)) = {})"

definition grid_ab_proper :: "(nat\<times>nat) set \<Rightarrow> ((nat\<times>nat) \<Rightarrow> grect) \<Rightarrow> bool" where
  "grid_ab_proper E ab \<longleftrightarrow>
    (\<forall>e\<in>E. \<forall>f\<in>E. e\<noteq>f \<longrightarrow> grect_set (ab e) \<inter> grect_set (ab f) = {})"

definition grid_ab_cm_proper :: "nat \<Rightarrow> (nat\<times>nat) set \<Rightarrow>
    ((nat\<times>nat) \<Rightarrow> grect) \<Rightarrow> (nat\<Rightarrow>matte) \<Rightarrow> bool" where
  "grid_ab_cm_proper k E ab cm \<longleftrightarrow> (\<forall>e\<in>E. gr_proper (ab e) \<and>
    (\<forall>i<k. (i=fst e \<or> i=snd e \<longrightarrow>
        set (mdisk (cm i)) \<inter> grect_set (inset_grect (ab e)) \<noteq> {}) \<and>
      (set (mdisk (cm i)) \<inter> grect_set (ab e) \<noteq> {} \<longrightarrow> i=fst e \<or> i=snd e)))"

lemma mem_approx_disjoint_iff:
  "mem_approx s A \<inter> mem_approx s B = {} \<longleftrightarrow> A \<inter> B = {}"
proof
  assume disjoint: "mem_approx s A \<inter> mem_approx s B = {}"
  show "A \<inter> B = {}"
  proof (rule equals0I)
    fix p assume p: "p\<in>A \<inter> B"
    have "scale_point s p\<in>mem_approx s A \<inter> mem_approx s B"
      using p by (simp only: mem_approx_scale Int_iff)
    then show False using disjoint by blast
  qed
next
  assume "A \<inter> B = {}"
  then show "mem_approx s A \<inter> mem_approx s B = {}"
    by (simp only: disjoint_iff mem_approx_iff; blast)
qed

lemma rp_represented_regions_disjoint:
  assumes plain: "rp_plain m" and repr: "rp_map_repr m k r"
    and i: "i<k" and j: "j<k" and ne: "i\<noteq>j"
  shows "rp_region m (r i) \<inter> rp_region m (r j) = {}"
proof (rule equals0I)
  fix z assume z: "z\<in>rp_region m (r i) \<inter> rp_region m (r j)"
  have iz: "m (r i) z" and jz: "m (r j) z" using z by (auto simp: rp_region_def)
  have zj: "m z (r j)" by (rule rp_map_sym[OF plain jz])
  have ij: "m (r i) (r j)" by (rule rp_map_trans[OF plain iz zj])
  have "i=j" using repr i j ij by (simp only: rp_map_repr_def; blast)
  then show False using ne by contradiction
qed

theorem rp_exists_grid_data:
  fixes m :: "rp_point region_map"
  assumes finite: "rp_finite_simple_map m"
  shows "\<exists>k r s ab cm. rp_map_repr m k r \<and>
    grid_cm_proper k cm \<and> grid_ab_proper (rp_adj_indices m k r) ab \<and>
    grid_ab_cm_proper k (rp_adj_indices m k r) ab cm \<and>
    (\<forall>i<k. smatte_set (s,cm i) \<subseteq> rp_region m (r i))"
proof -
  have simple: "rp_simple_map m" using finite by (simp add: rp_finite_simple_map_def)
  have plain: "rp_plain m" using simple by (simp add: rp_simple_map_def)
  obtain limit where limit: "rp_at_most_regions limit m"
    using finite by (auto simp: rp_finite_simple_map_def)
  obtain k r where repr: "rp_map_repr m k r"
    using rp_exists_indexed_map_repr[OF plain limit] by blast
  let ?E = "rp_adj_indices m k r"
  obtain b C where boxes: "\<forall>e\<in>?E. gr_proper (C e) \<and>
      rp_region m (r (fst e)) \<inter> srect_set (inset_srect (b,C e)) \<noteq> {} \<and>
      rp_region m (r (snd e)) \<inter> srect_set (inset_srect (b,C e)) \<noteq> {} \<and>
      (\<forall>i<k. i\<noteq>fst e \<and> i\<noteq>snd e \<longrightarrow>
        rp_region m (r i) \<inter> srect_set (b,C e) = {})"
    and apart: "\<forall>e\<in>?E. \<forall>f\<in>?E. e\<noteq>f \<longrightarrow>
      grect_set (C e) \<inter> grect_set (C f) = {}"
    using rp_exists_adjbox[OF plain repr]
    by (elim exE conjE) (rule that, assumption+)
  have targets: "\<forall>e\<in>?E. \<forall>i<k. i=fst e \<or> i=snd e \<longrightarrow>
      rp_region m (r i) \<inter> srect_set (inset_srect (b,C e)) \<noteq> {}"
    using boxes by blast
  obtain M where M: "\<forall>i<k. valid_smatte (M i) \<and> smatte_set (M i) \<subseteq> rp_region m (r i) \<and>
      (\<forall>e\<in>?E. i=fst e \<or> i=snd e \<longrightarrow>
        smatte_set (M i) \<inter> srect_set (inset_srect (b,C e)) \<noteq> {})"
    using rp_exists_smatte[OF simple repr finite_rp_adj_indices targets]
    by (elim exE) (rule that, assumption)
  have validM: "\<forall>i\<in>{..<k}. valid_smatte (M i)" using M by auto
  obtain s N D where mattes: "\<forall>i\<in>{..<k}. valid_matte (N i) \<and> smatte_set (s,N i)=smatte_set (M i)"
    and scale: "\<forall>e. srect_set (s,D e)=srect_set (b,C e) \<and>
      srect_set (inset_srect (b,C e))\<subseteq>srect_set (inset_srect (s,D e)) \<and>
      (gr_proper (D e)\<longleftrightarrow>gr_proper (C e))"
    and preserve: "\<forall>e f. grect_set (C e) \<inter> grect_set (C f) = {} \<longrightarrow>
      grect_set (D e) \<inter> grect_set (D f) = {}"
    using common_matte_box_scale[OF finite_lessThan validM, of b C]
    by (elim exE conjE) (rule that, assumption+)
  have contain: "smatte_set (s,N i) \<subseteq> rp_region m (r i)" if "i<k" for i
    using M mattes that by auto
  have valid: "valid_matte (N i)" if "i<k" for i using mattes that by auto
  have diskapart: "set (mdisk (N i)) \<inter> set (mdisk (N j)) = {}"
    if i: "i<k" and j: "j<k" and ne: "i\<noteq>j" for i j
  proof -
    have "smatte_set (s,N i) \<inter> smatte_set (s,N j) = {}"
      using contain[OF i] contain[OF j] rp_represented_regions_disjoint[OF plain repr i j ne] by blast
    then show ?thesis by (simp only: smatte_set_def fst_conv snd_conv mem_approx_disjoint_iff)
  qed
  have cm: "grid_cm_proper k N" using valid diskapart by (simp only: grid_cm_proper_def; blast)
  have ab: "grid_ab_proper ?E D" using apart preserve by (simp only: grid_ab_proper_def; blast)
  have incidence: "grid_ab_cm_proper k ?E D N"
  proof (unfold grid_ab_cm_proper_def, intro ballI conjI allI impI)
    fix e assume e: "e\<in>?E"
    show "gr_proper (D e)" using e boxes scale by blast
  next
    fix e i assume e: "e\<in>?E" and i: "i<k" and incident: "i=fst e \<or> i=snd e"
    have eq: "smatte_set (s,N i)=smatte_set (M i)" using mattes i by auto
    have oldmeet: "smatte_set (M i) \<inter> srect_set (inset_srect (b,C e)) \<noteq> {}"
      using M e i incident by blast
    have enlarge: "srect_set (inset_srect (b,C e))\<subseteq>srect_set (inset_srect (s,D e))"
      using scale by blast
    have "smatte_set (s,N i) \<inter> srect_set (inset_srect (s,D e)) \<noteq> {}"
      using oldmeet enlarge by (simp only: eq; blast)
    then show "set (mdisk (N i)) \<inter> grect_set (inset_grect (D e)) \<noteq> {}"
      by (simp only: smatte_set_def srect_set_def inset_srect_def fst_conv snd_conv mem_approx_disjoint_iff; blast)
  next
    fix e i assume e: "e\<in>?E" and i: "i<k"
      and meet: "set (mdisk (N i)) \<inter> grect_set (D e) \<noteq> {}"
    show "i=fst e \<or> i=snd e"
    proof (rule ccontr)
      assume "\<not>(i=fst e \<or> i=snd e)"
      then have empty: "rp_region m (r i) \<inter> srect_set (b,C e) = {}" using boxes e i by blast
      have eq: "srect_set (s,D e)=srect_set (b,C e)" using scale by blast
      have "smatte_set (s,N i) \<inter> srect_set (s,D e) = {}"
        using contain[OF i] empty by (simp only: eq; blast)
      then show False using meet
        by (simp only: smatte_set_def srect_set_def fst_conv snd_conv mem_approx_disjoint_iff; blast)
    qed
  qed
  show ?thesis
    by (rule exI[of _ k], rule exI[of _ r], rule exI[of _ s], rule exI[of _ D], rule exI[of _ N])
      (use repr cm ab incidence contain in blast)
qed

end
