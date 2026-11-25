(* Adjacency boxes from discretize.v. Original G. Gonthier et al., CeCILL-B.
   Isabelle/HOL port: Codex. *)
theory Adjacency_Boxes
  imports Approx Map_Representatives
begin

lemma finite_disjoint_plane_neighbourhoods:
  fixes w :: "'i \<Rightarrow> rp_point"
  assumes fin: "finite E" and inj: "inj_on w E"
  shows "\<exists>U. (\<forall>e\<in>E. open (U e) \<and> w e\<in>U e) \<and>
    (\<forall>e\<in>E. \<forall>f\<in>E. e\<noteq>f \<longrightarrow> U e\<inter>U f={})"
proof -
  define U where "U=(\<lambda>e. \<Inter>f\<in>E-{e}. sep_rect (w f) (w e))"
  have op: "open (U e)" for e
    unfolding U_def by (rule open_INT) (use fin open_sep_rect in auto)
  have at: "w e\<in>U e" for e by (simp add: U_def mem_sep_rect)
  have dis: "U e\<inter>U f={}" if e: "e\<in>E" and f: "f\<in>E" and ne: "e\<noteq>f" for e f
  proof (rule ccontr)
    assume "U e\<inter>U f\<noteq>{}"
    then have "sep_rect (w f) (w e)\<inter>sep_rect (w e) (w f)\<noteq>{}"
      using e f ne by (auto simp: U_def)
    then have "w f=w e" by (rule meet_sep_rect)
    then have "f=e" by (rule inj_onD[OF inj _ f e])
    then show False using ne by simp
  qed
  show ?thesis by (rule exI[of _ U]) (use op at dis in blast)
qed

lemma closure_meets_interior:
  assumes "z\<in>closure A" "z\<in>interior B"
  shows "A\<inter>B\<noteq>{}"
proof -
  have "interior B\<inter>closure A\<noteq>{}" using assms by blast
  then have "interior B\<inter>A\<noteq>{}"
    using open_Int_closure_eq_empty[OF open_interior[of B], of A] by blast
  then show ?thesis using interior_subset[of B] by blast
qed

lemma mem_approx_disjoint:
  "mem_approx s A\<inter>mem_approx s B={} \<longleftrightarrow> A\<inter>B={}"
proof
  assume dis: "mem_approx s A\<inter>mem_approx s B={}"
  show "A\<inter>B={}"
    using dis mem_approx_scale[of s _ A] mem_approx_scale[of s _ B] by blast
next
  assume "A\<inter>B={}"
  then show "mem_approx s A\<inter>mem_approx s B={}"
    by (auto simp: mem_approx_iff)
qed

lemma finite_common_scale:
  fixes B :: "'i \<Rightarrow> scaled_rect"
  assumes fin: "finite E"
  shows "\<exists>s C. \<forall>e\<in>E.
    srect_set (s,C e)=srect_set (B e) \<and>
    srect_set (inset_srect (B e))\<subseteq>srect_set (inset_srect (s,C e)) \<and>
    (gr_proper (C e)\<longleftrightarrow>gr_proper (snd (B e)))"
proof -
  let ?S = "insert 0 ((fst \<circ> B) ` E)"
  let ?s = "Max ?S"
  define C where "C=(\<lambda>e. snd (refine_srect (?s-fst (B e)) (B e)))"
  have bound: "fst (B e)\<le>?s" if "e\<in>E" for e
    by (rule Max_ge) (use fin that in auto)
  have eq: "(?s,C e)=refine_srect (?s-fst (B e)) (B e)" if e: "e\<in>E" for e
    using bound[OF e] by (simp add: C_def refine_srect_def)
  have props: "srect_set (?s,C e)=srect_set (B e) \<and>
    srect_set (inset_srect (B e))\<subseteq>srect_set (inset_srect (?s,C e)) \<and>
    (gr_proper (C e)\<longleftrightarrow>gr_proper (snd (B e)))" if e: "e\<in>E" for e
  proof -
    have sets: "srect_set (?s,C e)=srect_set (B e)"
      by (simp only: eq[OF e] in_refine_srect)
    have inset: "srect_set (inset_srect (B e))\<subseteq>srect_set (inset_srect (?s,C e))"
      using in_refine_inset[of "B e" "?s-fst (B e)"] by (simp only: eq[OF e])
    have proper: "gr_proper (C e)\<longleftrightarrow>gr_proper (snd (B e))"
      by (simp add: C_def refine_srect_def gr_proper_refine)
    show ?thesis using sets inset proper by blast
  qed
  show ?thesis
    apply (rule exI[of _ ?s])
    apply (rule exI[of _ C])
    using props by blast
qed

text \<open>Each adjacency receives a disjoint dyadic box. Both incident regions
  meet its inset, and every other represented region avoids the entire box.\<close>
lemma rp_exists_scaled_adjboxes:
  fixes m :: "rp_point region_map"
  assumes p: "rp_plain m" and repr: "rp_map_repr m k r"
  shows "\<exists>B :: (nat\<times>nat)\<Rightarrow>scaled_rect.
    (\<forall>e\<in>rp_adj_indices m k r.
      gr_proper (snd (B e)) \<and>
      rp_region m (r (fst e))\<inter>srect_set (inset_srect (B e))\<noteq>{} \<and>
      rp_region m (r (snd e))\<inter>srect_set (inset_srect (B e))\<noteq>{} \<and>
      (\<forall>i<k. i\<noteq>fst e \<and> i\<noteq>snd e \<longrightarrow> rp_region m (r i)\<inter>srect_set (B e)={})) \<and>
    (\<forall>e\<in>rp_adj_indices m k r. \<forall>f\<in>rp_adj_indices m k r.
       e\<noteq>f \<longrightarrow> srect_set (B e)\<inter>srect_set (B f)={})"
proof -
  let ?E = "rp_adj_indices m k r"
  obtain w where inj: "inj_on w ?E" and w: "\<forall>e\<in>?E.
    w e\<in>rp_not_corner m\<inter>rp_border m (r (fst e)) (r (snd e))"
    using rp_exists_adjacency_witnesses[OF p repr] by blast
  obtain U where op: "\<forall>e\<in>?E. open (U e) \<and> w e\<in>U e"
    and dis: "\<forall>e\<in>?E. \<forall>f\<in>?E. e\<noteq>f \<longrightarrow> U e\<inter>U f={}"
    using finite_disjoint_plane_neighbourhoods[OF finite_rp_adj_indices inj]
    by (elim exE conjE) (rule that, assumption+)
  define P where "P=(\<lambda>e q. w e\<in>interior (srect_set (inset_srect q)) \<and>
    srect_set q\<subseteq>U e \<and> (\<forall>i<k. i\<noteq>fst e \<and> i\<noteq>snd e \<longrightarrow>
      srect_set q\<inter>closure (rp_region m (r i))={}))"
  have ex: "\<exists>q. P e q" if ee: "e\<in>?E" for e
  proof -
    have ei: "fst e<k" and ej: "snd e<k" and ad: "rp_adjacent m (r (fst e)) (r (snd e))"
      using ee by (auto simp: rp_adj_indices_def)
    have wz: "w e\<in>rp_not_corner m\<inter>rp_border m (r (fst e)) (r (snd e))"
      using w ee by blast
    obtain a b c d where at: "w e\<in>rp_rectangle a b c d" and avoids:
      "\<forall>x\<in>r ` {..<k}. \<not>m (r (fst e)) x \<and> \<not>m (r (snd e)) x \<longrightarrow>
        rp_rectangle a b c d\<inter>closure (rp_region m x)={}"
      using rp_adjacency_neighbourhood[OF p _ ad wz, of "r ` {..<k}"] by auto
    have Uopen: "open (U e)" using bspec[OF op ee] by simp
    have Ropen: "open (rp_rectangle a b c d)"
      unfolding rp_rectangle_def by (rule open_Times) simp_all
    have O: "open (U e\<inter>rp_rectangle a b c d)"
      by (rule open_Int[OF Uopen Ropen])
    have W: "w e\<in>U e\<inter>rp_rectangle a b c d" using op ee at by blast
    obtain q where q: "w e\<in>interior (srect_set (inset_srect q))"
      "srect_set q\<subseteq>U e\<inter>rp_rectangle a b c d"
      using approx_open_interior[OF O W] by blast
    have other: "srect_set q\<inter>closure (rp_region m (r i))={}" if ii: "i<k" "i\<noteq>fst e" "i\<noteq>snd e" for i
    proof -
      have ne: "\<not>m (r (fst e)) (r i)" "\<not>m (r (snd e)) (r i)"
        using rp_repr_relation[OF repr ei ii(1)] rp_repr_relation[OF repr ej ii(1)] ii by auto
      have "rp_rectangle a b c d\<inter>closure (rp_region m (r i))={}"
        using avoids ne ii(1) by blast
      then show ?thesis using q(2) by blast
    qed
    show ?thesis by (rule exI[of _ q]) (use q other in \<open>auto simp: P_def\<close>)
  qed
  define B where "B=(\<lambda>e. SOME q. P e q)"
  have B: "P e (B e)" if "e\<in>?E" for e unfolding B_def by (rule someI_ex[OF ex[OF that]])
  have props: "gr_proper (snd (B e)) \<and>
    rp_region m (r (fst e))\<inter>srect_set (inset_srect (B e))\<noteq>{} \<and>
    rp_region m (r (snd e))\<inter>srect_set (inset_srect (B e))\<noteq>{} \<and>
    (\<forall>i<k. i\<noteq>fst e \<and> i\<noteq>snd e \<longrightarrow> rp_region m (r i)\<inter>srect_set (B e)={})"
    if ee: "e\<in>?E" for e
  proof -
    have at: "w e\<in>interior (srect_set (inset_srect (B e)))" using B[OF ee] by (simp add: P_def)
    have za: "w e\<in>closure (rp_region m (r (fst e)))" and zb: "w e\<in>closure (rp_region m (r (snd e)))"
      using w ee by (auto simp: rp_border_def rp_closure_eq)
    have ma: "rp_region m (r (fst e))\<inter>srect_set (inset_srect (B e))\<noteq>{}"
      by (rule closure_meets_interior[OF za at])
    have mb: "rp_region m (r (snd e))\<inter>srect_set (inset_srect (B e))\<noteq>{}"
      by (rule closure_meets_interior[OF zb at])
    have proper: "gr_proper (snd (B e))" by (rule srect_nonempty_proper)
      (use ma inset_srect_sub[of "B e"] in blast)
    have other: "rp_region m (r i)\<inter>srect_set (B e)={}" if "i<k" "i\<noteq>fst e" "i\<noteq>snd e" for i
      using B[OF ee] that closure_subset[of "rp_region m (r i)"] by (auto simp: P_def)
    show ?thesis using proper ma mb other by blast
  qed
  have boxes: "srect_set (B e)\<inter>srect_set (B f)={}" if "e\<in>?E" "f\<in>?E" "e\<noteq>f" for e f
  proof -
    have disjoint: "U e\<inter>U f={}"
      using bspec[OF bspec[OF dis that(1)] that(2)] that(3) by simp
    have sube: "srect_set (B e)\<subseteq>U e"
      using B[OF that(1)] by (simp add: P_def)
    have subf: "srect_set (B f)\<subseteq>U f"
      using B[OF that(2)] by (simp add: P_def)
    show ?thesis using disjoint sube subf by blast
  qed
  show ?thesis by (rule exI[of _ B]) (use props boxes in blast)
qed

text \<open>The common-scale form used by the grid-map construction. This is
  exists_adjbox in discretize.v, with only actual adjacencies in the index set.\<close>
lemma rp_exists_adjbox:
  fixes m :: "rp_point region_map"
  assumes p: "rp_plain m" and repr: "rp_map_repr m k r"
  shows "\<exists>s C. (\<forall>e\<in>rp_adj_indices m k r.
    gr_proper (C e) \<and>
    rp_region m (r (fst e))\<inter>srect_set (inset_srect (s,C e))\<noteq>{} \<and>
    rp_region m (r (snd e))\<inter>srect_set (inset_srect (s,C e))\<noteq>{} \<and>
    (\<forall>i<k. i\<noteq>fst e \<and> i\<noteq>snd e \<longrightarrow> rp_region m (r i)\<inter>srect_set (s,C e)={})) \<and>
    (\<forall>e\<in>rp_adj_indices m k r. \<forall>f\<in>rp_adj_indices m k r.
      e\<noteq>f \<longrightarrow> grect_set (C e)\<inter>grect_set (C f)={})"
proof -
  let ?E = "rp_adj_indices m k r"
  obtain B where B: "\<forall>e\<in>?E. gr_proper (snd (B e)) \<and>
      rp_region m (r (fst e))\<inter>srect_set (inset_srect (B e))\<noteq>{} \<and>
      rp_region m (r (snd e))\<inter>srect_set (inset_srect (B e))\<noteq>{} \<and>
      (\<forall>i<k. i\<noteq>fst e \<and> i\<noteq>snd e \<longrightarrow> rp_region m (r i)\<inter>srect_set (B e)={})"
    and dis: "\<forall>e\<in>?E. \<forall>f\<in>?E. e\<noteq>f \<longrightarrow> srect_set (B e)\<inter>srect_set (B f)={}"
    using rp_exists_scaled_adjboxes[OF p repr]
    by (elim exE conjE) (rule that, assumption+)
  obtain s C where C: "\<forall>e\<in>?E. srect_set (s,C e)=srect_set (B e) \<and>
      srect_set (inset_srect (B e))\<subseteq>srect_set (inset_srect (s,C e)) \<and>
      (gr_proper (C e)\<longleftrightarrow>gr_proper (snd (B e)))"
    using finite_common_scale[where E="?E" and B=B, OF finite_rp_adj_indices]
    by (elim exE) (rule that, assumption)
  have props: "gr_proper (C e) \<and>
    rp_region m (r (fst e))\<inter>srect_set (inset_srect (s,C e))\<noteq>{} \<and>
    rp_region m (r (snd e))\<inter>srect_set (inset_srect (s,C e))\<noteq>{} \<and>
    (\<forall>i<k. i\<noteq>fst e \<and> i\<noteq>snd e \<longrightarrow> rp_region m (r i)\<inter>srect_set (s,C e)={})"
    if ee: "e\<in>?E" for e
    using bspec[OF B ee] bspec[OF C ee] by blast
  have boxes: "grect_set (C e)\<inter>grect_set (C f)={}" if e: "e\<in>?E" and f: "f\<in>?E" and ne: "e\<noteq>f" for e f
  proof -
    have "srect_set (s,C e)\<inter>srect_set (s,C f)={}"
      using bspec[OF C e] bspec[OF C f] dis e f ne by blast
    then show ?thesis by (simp add: srect_set_def mem_approx_disjoint)
  qed
  show ?thesis
    apply (rule exI[of _ s])
    apply (rule exI[of _ C])
    using props boxes by blast
qed

end
