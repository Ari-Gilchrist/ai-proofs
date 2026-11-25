(* Finite region approximations used by exists_smatte in discretize.v.
   Original G. Gonthier et al., CeCILL-B. Isabelle/HOL port: Codex. *)
theory Region_Mattes
  imports Connected_Matte Four_Colour_Plane_Geometry.Adjacency_Boxes
begin

lemma finite_smatte_meet:
  assumes fin: "finite E" and op: "open U" and conn: "connected U"
    and valid: "valid_smatte m" and sub: "smatte_set m\<subseteq>U"
    and targets: "\<forall>i\<in>E. U \<inter> B i \<noteq> {}"
  shows "\<exists>n. valid_smatte n \<and> smatte_set m\<subseteq>smatte_set n \<and>
    smatte_set n\<subseteq>U \<and> (\<forall>i\<in>E. smatte_set n \<inter> B i \<noteq> {})"
  using fin targets
proof (induction E rule: finite_induct)
  case empty
  show ?case by (rule exI[of _ m]) (use valid sub in auto)
next
  case (insert i E)
  obtain n where n: "valid_smatte n" "smatte_set m\<subseteq>smatte_set n"
    "smatte_set n\<subseteq>U" "\<forall>j\<in>E. smatte_set n \<inter> B j \<noteq> {}"
    using insert.IH insert.prems by blast
  obtain z where z: "z\<in>U" "z\<in>B i" using insert.prems by blast
  obtain k where k: "valid_smatte k" "z\<in>smatte_set k"
    "smatte_set n\<subseteq>smatte_set k" "smatte_set k\<subseteq>U"
    using connected_matte[OF op conn n(1,3) z(1)] by blast
  show ?case by (rule exI[of _ k]) (use n k z in blast)
qed

lemma exists_region_smatte:
  assumes "open U" "connected U" "U\<noteq>{}" "finite E"
    "\<forall>i\<in>E. U \<inter> B i \<noteq> {}"
  shows "\<exists>n. valid_smatte n \<and> smatte_set n\<subseteq>U \<and>
    (\<forall>i\<in>E. smatte_set n \<inter> B i \<noteq> {})"
proof -
  obtain z where z: "z\<in>U" using assms(3) by blast
  obtain m where m: "valid_smatte m" "smatte_set m\<subseteq>U"
    using point_matte_in_open[OF assms(1) z] by blast
  show ?thesis using finite_smatte_meet[OF assms(4,1,2) m assms(5)] by blast
qed

lemma common_smatte_scale:
  assumes fin: "finite I" and valid: "\<forall>i\<in>I. valid_smatte (m i)"
  shows "\<exists>s n. \<forall>i\<in>I. valid_matte (n i) \<and> smatte_set (s,n i)=smatte_set (m i)"
proof -
  let ?s = "Max (insert 0 ((\<lambda>i. fst (m i)) ` I))"
  let ?n = "\<lambda>i. (refine_matte ^^ (?s-fst (m i))) (snd (m i))"
  have bound: "fst (m i) \<le> ?s" if "i\<in>I" for i
    by (rule Max_ge) (use fin that in auto)
  have good: "valid_matte (?n i) \<and> smatte_set (?s,?n i)=smatte_set (m i)" if i: "i\<in>I" for i
  proof -
    have v: "valid_matte (?n i)"
      by (rule iter_refine_matte_valid) (use valid i in \<open>auto simp: valid_smatte_def\<close>)
    have eq: "smatte_set (?s,?n i)=smatte_set (m i)"
      using in_refine_smatte[of "?s-fst (m i)" "m i"] bound[OF i]
      by (simp add: refine_smatte_def)
    show ?thesis using v eq by blast
  qed
  show ?thesis by (rule exI[of _ ?s], rule exI[of _ ?n]) (use good in blast)
qed

lemma rp_exists_smatte:
  fixes m :: "rp_point region_map"
  assumes simple: "rp_simple_map m" and repr: "rp_map_repr m k r"
    and fin: "finite E"
    and boxes: "\<forall>e\<in>E. \<forall>i<k. i=fst e \<or> i=snd e \<longrightarrow>
      rp_region m (r i) \<inter> srect_set (inset_srect (B e)) \<noteq> {}"
  shows "\<exists>M. \<forall>i<k. valid_smatte (M i) \<and>
    smatte_set (M i) \<subseteq> rp_region m (r i) \<and>
    (\<forall>e\<in>E. i=fst e \<or> i=snd e \<longrightarrow>
      smatte_set (M i) \<inter> srect_set (inset_srect (B e)) \<noteq> {})"
proof -
  let ?P = "\<lambda>i n. valid_smatte n \<and> smatte_set n \<subseteq> rp_region m (r i) \<and>
    (\<forall>e\<in>E. i=fst e \<or> i=snd e \<longrightarrow>
      smatte_set n \<inter> srect_set (inset_srect (B e)) \<noteq> {})"
  have exists: "\<exists>n. ?P i n" if i: "i<k" for i
  proof -
    let ?U = "rp_region m (r i)"
    let ?E = "{e\<in>E. i=fst e \<or> i=snd e}"
    have top: "open ?U \<and> connected ?U"
      using simple by (simp only: rp_simple_map_iff; blast)
    have op: "open ?U" and conn: "connected ?U" using top by auto
    have at: "r i\<in>?U" using repr i by (auto simp: rp_map_repr_def rp_cover_def rp_region_def)
    have nonempty: "?U\<noteq>{}" using at by blast
    have finite: "finite ?E" using fin by simp
    have targets: "\<forall>e\<in>?E. ?U \<inter> srect_set (inset_srect (B e)) \<noteq> {}"
      using boxes i by blast
    obtain n where n: "valid_smatte n" "smatte_set n\<subseteq>?U"
      "\<forall>e\<in>?E. smatte_set n \<inter> srect_set (inset_srect (B e)) \<noteq> {}"
      using exists_region_smatte[OF op conn nonempty finite targets] by blast
    show ?thesis by (rule exI[of _ n]) (use n in blast)
  qed
  let ?M = "\<lambda>i. SOME n. ?P i n"
  have good: "?P i (?M i)" if "i<k" for i
    by (rule someI_ex[OF exists[OF that]])
  show ?thesis by (rule exI[of _ ?M]) (use good in blast)
qed

lemma iter_refine_rect_disjoint:
  assumes "grect_set r \<inter> grect_set q = {}"
  shows "grect_set ((refine_rect ^^ n) r) \<inter> grect_set ((refine_rect ^^ n) q) = {}"
  using assms
proof (induction n)
  case 0 then show ?case by simp
next
  case (Suc n)
  then show ?case
    by (simp only: funpow.simps comp_apply disjoint_iff in_refine_rect; blast)
qed

lemma common_matte_box_scale:
  assumes fin: "finite I" and valid: "\<forall>i\<in>I. valid_smatte (M i)"
  shows "\<exists>s N D. (\<forall>i\<in>I. valid_matte (N i) \<and> smatte_set (s,N i)=smatte_set (M i)) \<and>
    (\<forall>e. srect_set (s,D e)=srect_set (b,C e) \<and>
      srect_set (inset_srect (b,C e))\<subseteq>srect_set (inset_srect (s,D e)) \<and>
      (gr_proper (D e)\<longleftrightarrow>gr_proper (C e))) \<and>
    (\<forall>e f. grect_set (C e) \<inter> grect_set (C f) = {} \<longrightarrow>
      grect_set (D e) \<inter> grect_set (D f) = {})"
proof -
  obtain t n where n: "\<forall>i\<in>I. valid_matte (n i) \<and> smatte_set (t,n i)=smatte_set (M i)"
    using common_smatte_scale[OF fin valid] by blast
  let ?s = "b+t"
  let ?N = "\<lambda>i. (refine_matte ^^ b) (n i)"
  let ?D = "\<lambda>e. (refine_rect ^^ t) (C e)"
  have mattes: "valid_matte (?N i) \<and> smatte_set (?s,?N i)=smatte_set (M i)" if "i\<in>I" for i
  proof -
    have v: "valid_matte (?N i)" by (rule iter_refine_matte_valid) (use n that in blast)
    have eq: "smatte_set (?s,?N i)=smatte_set (M i)"
      using in_refine_smatte[of b "(t,n i)"] n that by (simp add: refine_smatte_def; blast)
    show ?thesis using v eq by blast
  qed
  have boxes: "srect_set (?s,?D e)=srect_set (b,C e) \<and>
      srect_set (inset_srect (b,C e))\<subseteq>srect_set (inset_srect (?s,?D e)) \<and>
      (gr_proper (?D e)\<longleftrightarrow>gr_proper (C e))" for e
    using in_refine_srect[of t "(b,C e)"] in_refine_inset[of "(b,C e)" t]
    by (simp add: refine_srect_def add.commute gr_proper_refine)
  have disjoint: "grect_set (?D e) \<inter> grect_set (?D f) = {}"
    if "grect_set (C e) \<inter> grect_set (C f) = {}" for e f
    by (rule iter_refine_rect_disjoint[OF that])
  show ?thesis by (rule exI[of _ ?s], rule exI[of _ ?N], rule exI[of _ ?D])
    (use mattes boxes disjoint in blast)
qed

end
