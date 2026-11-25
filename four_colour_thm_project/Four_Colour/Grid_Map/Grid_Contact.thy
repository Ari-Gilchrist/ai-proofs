(* Realizing adjacency boxes as matte boundary contacts, from gridmap.v.
   Original G. Gonthier et al., CeCILL-B. Isabelle/HOL port: Codex. *)
theory Grid_Contact
  imports Four_Colour_Grid_Map.Grid_Adjacency
begin

lemma refine_grid_cm_proper:
  assumes proper: "grid_cm_proper k cm"
  shows "grid_cm_proper k (\<lambda>i. refine_matte (cm i))"
proof -
  have valid: "valid_matte (refine_matte (cm i))" if "i<k" for i
    by (rule refine_matte_valid) (use proper that in \<open>simp only: grid_cm_proper_def; blast\<close>)
  have apart: "set (mdisk (refine_matte (cm i))) \<inter> set (mdisk (refine_matte (cm j))) = {}"
    if "i<k" "j<k" "i\<noteq>j" for i j
  proof -
    have "set (mdisk (cm i)) \<inter> set (mdisk (cm j)) = {}"
      using proper that by (simp only: grid_cm_proper_def; blast)
    then show ?thesis by (simp only: disjoint_iff in_refine_matte; blast)
  qed
  show ?thesis using valid apart by (simp only: grid_cm_proper_def; blast)
qed

lemma inset_refine_double:
  assumes "p\<in>grect_set (inset_grect r)"
  shows "doubleg p\<in>grect_set (inset_grect (refine_rect r))"
proof -
  have "doubleg p\<in>grect_set (refine_rect (inset_grect r))"
    using assms by (simp only: in_refine_rect halfg_double)
  then have "doubleg p\<in>grect_set (inset_grect (inset_grect (refine_rect r)))"
    by (simp only: refine_inset)
  then show ?thesis using insetW[of "inset_grect (refine_rect r)"] by blast
qed

lemma refine_grid_ab_cm_proper:
  assumes proper: "grid_ab_cm_proper k E B cm"
  shows "grid_ab_cm_proper k E (\<lambda>e. refine_rect (B e)) (\<lambda>i. refine_matte (cm i))"
proof (unfold grid_ab_cm_proper_def, intro ballI conjI allI impI)
  fix e assume e: "e\<in>E"
  have "gr_proper (B e)" using proper e by (simp only: grid_ab_cm_proper_def; blast)
  then show "gr_proper (refine_rect (B e))" using gr_proper_refine[of 1 "B e"] by simp
next
  fix e i assume e: "e\<in>E" and i: "i<k" and incident: "i=fst e \<or> i=snd e"
  have meet: "set (mdisk (cm i)) \<inter> grect_set (inset_grect (B e)) \<noteq> {}"
    using proper e i incident by (simp only: grid_ab_cm_proper_def; blast)
  obtain p where p: "p\<in>set (mdisk (cm i))" "p\<in>grect_set (inset_grect (B e))"
    using meet by blast
  have "doubleg p\<in>set (mdisk (refine_matte (cm i)))"
    using p(1) by (simp only: in_refine_matte halfg_double)
  moreover have "doubleg p\<in>grect_set (inset_grect (refine_rect (B e)))"
    by (rule inset_refine_double[OF p(2)])
  ultimately show "set (mdisk (refine_matte (cm i))) \<inter>
      grect_set (inset_grect (refine_rect (B e))) \<noteq> {}" by blast
next
  fix e i assume e: "e\<in>E" and i: "i<k"
    and meet: "set (mdisk (refine_matte (cm i))) \<inter> grect_set (refine_rect (B e)) \<noteq> {}"
  have oldmeet: "set (mdisk (cm i)) \<inter> grect_set (B e) \<noteq> {}"
    using meet by (simp only: disjoint_iff in_refine_matte in_refine_rect; blast)
  show "i=fst e \<or> i=snd e" using proper e i oldmeet
    by (simp only: grid_ab_cm_proper_def; blast)
qed

definition grid_contact_invariant :: "nat \<Rightarrow> (nat\<times>nat) set \<Rightarrow>
    ((nat\<times>nat)\<Rightarrow>grect) \<Rightarrow> (nat\<Rightarrow>matte) \<Rightarrow> bool" where
  "grid_contact_invariant k E B cm \<longleftrightarrow> grid_cm_proper k cm \<and>
    (\<forall>e\<in>grid_adj_pending E cm. \<forall>i<k.
      (i=fst e \<or> i=snd e \<longrightarrow>
        coarse_in (grect_set (refine_rect (B e))) (cm i) \<and>
        set (mdisk (cm i)) \<inter> grect_set (inset_grect (refine_rect (B e))) \<noteq> {}) \<and>
      (set (mdisk (cm i)) \<inter> grect_set (refine_rect (B e)) \<noteq> {} \<longrightarrow>
        i=fst e \<or> i=snd e))"

lemma grid_contact_initial:
  assumes cm: "grid_cm_proper k cm" and incidence: "grid_ab_cm_proper k E B cm"
  shows "grid_contact_invariant k E B (\<lambda>i. refine_matte (cm i))"
  using refine_grid_cm_proper[OF cm] refine_grid_ab_cm_proper[OF incidence] refine_matte_coarse
  unfolding grid_contact_invariant_def grid_ab_cm_proper_def grid_adj_pending_def by blast

lemma refine_grid_ab_proper:
  assumes "grid_ab_proper E B"
  shows "grid_ab_proper E (\<lambda>e. refine_rect (B e))"
  using assms by (simp only: grid_ab_proper_def disjoint_iff in_refine_rect; blast)

lemma grid_contact_step:
  assumes inv: "grid_contact_invariant k E B cm"
    and boxes: "grid_ab_proper E B"
    and indices: "\<forall>e\<in>E. fst e<k \<and> snd e<k \<and> fst e\<noteq>snd e"
    and pending: "e\<in>grid_adj_pending E cm"
  shows "\<exists>xm. grid_contact_invariant k E B xm \<and>
    grid_adj_pending E xm \<subset> grid_adj_pending E cm"
proof -
  let ?i = "fst e"
  let ?j = "snd e"
  let ?R = "grect_set (refine_rect (B e))"
  have eE: "e\<in>E" using pending by (simp only: grid_adj_pending_def mem_Collect_eq; blast)
  have ik: "?i<k" and jk: "?j<k" and ne: "?i\<noteq>?j" using indices eE by blast+
  have proper: "grid_cm_proper k cm" using inv by (simp only: grid_contact_invariant_def; blast)
  have valid: "valid_matte (cm a)" if "a<k" for a
    using proper that by (simp only: grid_cm_proper_def; blast)
  have oldfacts: "(a=fst f \<or> a=snd f \<longrightarrow>
      coarse_in (grect_set (refine_rect (B f))) (cm a) \<and>
      set (mdisk (cm a)) \<inter> grect_set (inset_grect (refine_rect (B f))) \<noteq> {}) \<and>
      (set (mdisk (cm a)) \<inter> grect_set (refine_rect (B f)) \<noteq> {} \<longrightarrow>
        a=fst f \<or> a=snd f)"
    if "f\<in>grid_adj_pending E cm" "a<k" for f a
    using inv that by (simp only: grid_contact_invariant_def; blast)
  have coarsej: "coarse_in ?R (cm ?j)"
    and meetj: "set (mdisk (cm ?j)) \<inter> grect_set (inset_grect (refine_rect (B e))) \<noteq> {}"
    using oldfacts[OF pending jk] by blast+
  have meeti: "set (mdisk (cm ?i)) \<inter> grect_set (inset_grect (refine_rect (B e))) \<noteq> {}"
    using oldfacts[OF pending ik] by blast
  have meetjr: "set (mdisk (cm ?j)) \<inter> ?R \<noteq> {}"
    using meetj insetW[of "refine_rect (B e)"] by blast
  have disjoint: "set (mdisk (cm ?j)) \<inter> set (mdisk (cm ?i)) = {}"
    using proper ik jk ne by (simp only: grid_cm_proper_def; blast)
  obtain n where nvalid: "valid_matte n"
    and sub: "set (mdisk (cm ?j))\<subseteq>set (mdisk n)"
    and bound: "set (mdisk n)\<subseteq>(?R \<union> set (mdisk (cm ?j))) - set (mdisk (cm ?i))"
    and contact: "madj (cm ?i) n"
    using extend_madj[OF valid[OF jk] valid[OF ik] coarsej meetjr meeti disjoint]
    by (elim exE conjE) (rule that, assumption+)
  let ?xm = "cm(?j:=n)"
  have apart: "set (mdisk (cm a)) \<inter> set (mdisk n) = {}" if a: "a<k" and aj: "a\<noteq>?j" for a
  proof (cases "a=?i")
    case True
    then show ?thesis using bound by blast
  next
    case False
    have outside: "set (mdisk (cm a)) \<inter> ?R = {}"
      using oldfacts[OF pending a] aj False by blast
    have oldapart: "set (mdisk (cm a)) \<inter> set (mdisk (cm ?j)) = {}"
      using proper a jk aj by (simp only: grid_cm_proper_def; blast)
    show ?thesis using bound outside oldapart by blast
  qed
  have newproper: "grid_cm_proper k ?xm" by (rule grid_cm_replace_proper[OF proper jk nvalid apart])
  have indices2: "\<forall>f\<in>E. fst f<k \<and> snd f<k" using indices by blast
  have shrink: "grid_adj_pending E ?xm \<subseteq> grid_adj_pending E cm"
    by (rule grid_adj_pending_update[OF indices2 proper newproper jk sub])
  have realized: "e\<notin>grid_adj_pending E ?xm"
    using contact ne by (simp add: grid_adj_pending_def)
  have strict: "grid_adj_pending E ?xm \<subset> grid_adj_pending E cm" using shrink pending realized by blast
  have loose: "set (mdisk n)\<subseteq>?R \<union> set (mdisk (cm ?j))" using bound by blast
  have fineboxes: "grid_ab_proper E (\<lambda>f. refine_rect (B f))" by (rule refine_grid_ab_proper[OF boxes])
  have newfacts: "(a=fst f \<or> a=snd f \<longrightarrow>
      coarse_in (grect_set (refine_rect (B f))) (?xm a) \<and>
      set (mdisk (?xm a)) \<inter> grect_set (inset_grect (refine_rect (B f))) \<noteq> {}) \<and>
      (set (mdisk (?xm a)) \<inter> grect_set (refine_rect (B f)) \<noteq> {} \<longrightarrow>
        a=fst f \<or> a=snd f)"
    if fp: "f\<in>grid_adj_pending E ?xm" and ak: "a<k" for f a
  proof -
    have oldpending: "f\<in>grid_adj_pending E cm" using shrink fp by blast
    have fE: "f\<in>E" using fp by (simp only: grid_adj_pending_def mem_Collect_eq; blast)
    have fe: "f\<noteq>e" using fp realized by blast
    show ?thesis
    proof (cases "a=?j")
      case False
      then show ?thesis using oldfacts[OF oldpending ak] by simp
    next
      case True
      let ?F = "grect_set (refine_rect (B f))"
      have boxapart: "?R \<inter> ?F = {}"
        using fineboxes eE fE fe by (simp only: grid_ab_proper_def; blast)
      have unchanged: "\<forall>p\<in>?F. (p\<in>set (mdisk n) \<longleftrightarrow> p\<in>set (mdisk (cm ?j)))"
        by (rule matte_growth_unchanged_outside[OF sub loose boxapart])
      have coarse: "coarse_in ?F n" if incident: "?j=fst f \<or> ?j=snd f"
      proof -
        have "coarse_in ?F (cm ?j)" using oldfacts[OF oldpending jk] incident by blast
        then show ?thesis by (rule coarse_in_unchanged_refine[OF _ unchanged])
      qed
      have meet: "set (mdisk n) \<inter> grect_set (inset_grect (refine_rect (B f))) \<noteq> {}"
        if incident: "?j=fst f \<or> ?j=snd f"
        using oldfacts[OF oldpending jk] incident sub by blast
      have reverse: "?j=fst f \<or> ?j=snd f" if "set (mdisk n) \<inter> ?F \<noteq> {}"
      proof -
        have "set (mdisk (cm ?j)) \<inter> ?F \<noteq> {}" using unchanged that by blast
        then show ?thesis using oldfacts[OF oldpending jk] by blast
      qed
      show ?thesis using coarse meet reverse True by simp
    qed
  qed
  have invariant: "grid_contact_invariant k E B ?xm"
    using newproper newfacts by (simp only: grid_contact_invariant_def; blast)
  show ?thesis by (rule exI[of _ ?xm]) (use invariant strict in blast)
qed

lemma grid_contact_finish:
  assumes finite: "finite E" and boxes: "grid_ab_proper E B"
    and indices: "\<forall>e\<in>E. fst e<k \<and> snd e<k \<and> fst e\<noteq>snd e"
    and inv: "grid_contact_invariant k E B cm"
  shows "\<exists>xm. grid_cm_proper k xm \<and> (\<forall>e\<in>E. madj (xm (fst e)) (xm (snd e)))"
  using inv
proof (induction "card (grid_adj_pending E cm)" arbitrary: cm rule: less_induct)
  case less
  show ?case
  proof (cases "grid_adj_pending E cm = {}")
    case True
    have proper: "grid_cm_proper k cm" using less.prems by (simp only: grid_contact_invariant_def; blast)
    have all: "\<forall>e\<in>E. madj (cm (fst e)) (cm (snd e))"
      using True by (simp only: grid_adj_pending_def; blast)
    show ?thesis by (rule exI[of _ cm]) (use proper all in blast)
  next
    case False
    obtain e where e: "e\<in>grid_adj_pending E cm" using False by blast
    obtain n where n: "grid_contact_invariant k E B n"
      "grid_adj_pending E n \<subset> grid_adj_pending E cm"
      using grid_contact_step[OF less.prems boxes indices e] by blast
    have fin: "finite (grid_adj_pending E cm)" using finite by (simp add: grid_adj_pending_def)
    have decrease: "card (grid_adj_pending E n) < card (grid_adj_pending E cm)"
      by (rule psubset_card_mono[OF fin n(2)])
    show ?thesis by (rule less.hyps[OF decrease n(1)])
  qed
qed

theorem grid_extend_adj:
  assumes "finite E" "grid_ab_proper E B"
    "\<forall>e\<in>E. fst e<k \<and> snd e<k \<and> fst e\<noteq>snd e"
    "grid_cm_proper k cm" "grid_ab_cm_proper k E B cm"
  shows "\<exists>xm. grid_cm_proper k xm \<and> (\<forall>e\<in>E. madj (xm (fst e)) (xm (snd e)))"
  by (rule grid_contact_finish[OF assms(1-3) grid_contact_initial[OF assms(4,5)]])

theorem rp_exists_touching_grid_mattes:
  fixes m :: "rp_point region_map"
  assumes finite: "rp_finite_simple_map m"
  shows "\<exists>k r cm. rp_map_repr m k r \<and> grid_cm_proper k cm \<and>
    (\<forall>e\<in>rp_adj_indices m k r. madj (cm (fst e)) (cm (snd e)))"
proof -
  obtain k r s B cm where repr: "rp_map_repr m k r" and proper: "grid_cm_proper k cm"
    and boxes: "grid_ab_proper (rp_adj_indices m k r) B"
    and incidence: "grid_ab_cm_proper k (rp_adj_indices m k r) B cm"
    and contain: "\<forall>i<k. smatte_set (s,cm i)\<subseteq>rp_region m (r i)"
    using rp_exists_grid_data[OF finite] by (elim exE conjE) (rule that, assumption+)
  have indices: "\<forall>e\<in>rp_adj_indices m k r. fst e<k \<and> snd e<k \<and> fst e\<noteq>snd e"
    by (auto simp: rp_adj_indices_def)
  obtain xm where xm: "grid_cm_proper k xm"
    "\<forall>e\<in>rp_adj_indices m k r. madj (xm (fst e)) (xm (snd e))"
    using grid_extend_adj[OF finite_rp_adj_indices boxes indices proper incidence]
    by (elim exE conjE) (rule that, assumption+)
  show ?thesis by (rule exI[of _ k], rule exI[of _ r], rule exI[of _ xm])
    (use repr xm in blast)
qed

lemma rp_touching_matte_colour_transfer:
  fixes m :: "rp_point region_map"
    and c :: "nat\<Rightarrow>nat"
  assumes plain: "rp_plain m" and repr: "rp_map_repr m k r"
    and contact: "\<forall>e\<in>rp_adj_indices m k r. madj (cm (fst e)) (cm (snd e))"
    and palette: "\<forall>i<k. c i<4"
    and proper: "\<And>i j. i<k \<Longrightarrow> j<k \<Longrightarrow> madj (cm i) (cm j) \<Longrightarrow> c i\<noteq>c j"
  shows "rp_colorable_with 4 m"
proof -
  have colours: "c i\<noteq>c j"
    if i: "i<k" and j: "j<k" and adj: "rp_adjacent m (r i) (r j)" for i j
  proof -
    have self: "m (r i) (r i)" using repr i by (auto simp: rp_map_repr_def rp_cover_def)
    have ne: "i\<noteq>j" using self adj by (auto simp: rp_adjacent_def)
    show ?thesis
    proof (cases "i<j")
      case True
      have e: "(i,j)\<in>rp_adj_indices m k r" using i j True adj by (simp add: rp_adj_indices_def)
      have "madj (cm i) (cm j)" using bspec[OF contact e] by simp
      then show ?thesis by (rule proper[OF i j])
    next
      case False
      have lt: "j<i" using False ne by arith
      have reverse: "rp_adjacent m (r j) (r i)" by (rule rp_adjacent_sym[OF plain adj])
      have e: "(j,i)\<in>rp_adj_indices m k r" using i j lt reverse by (simp add: rp_adj_indices_def)
      have "madj (cm j) (cm i)" using bspec[OF contact e] by simp
      then have "c j\<noteq>c i" by (rule proper[OF j i])
      then show ?thesis by simp
    qed
  qed
  show ?thesis by (rule rp_representative_colour_transfer[OF plain repr, where c=c])
    (use palette colours in auto)
qed

end
