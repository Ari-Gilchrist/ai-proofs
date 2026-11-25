(* Connected-region interpolation from discretize.v.
   Original G. Gonthier et al., CeCILL-B. Isabelle/HOL port: Codex. *)
theory Connected_Matte
  imports Four_Colour_Matte_Geometry.Matte_Refinement Four_Colour_Plane_Geometry.Scaled_Matte
begin

definition smatte_interpolated :: "rp_point set \<Rightarrow> rp_point set \<Rightarrow> rp_point set" where
  "smatte_interpolated K U = {z. \<exists>m. valid_smatte m \<and>
    z\<in>smatte_set m \<and> K\<subseteq>smatte_set m \<and> smatte_set m\<subseteq>U}"

lemma smatte_interpolated_sub: "smatte_interpolated K U \<subseteq> U"
  by (auto simp: smatte_interpolated_def)

lemma smatte_nonempty:
  assumes "valid_smatte m"
  shows "smatte_set m \<noteq> {}"
proof -
  obtain s n where m: "m=(s,n)" by (cases m) auto
  have vn: "valid_matte n" using assms by (simp add: m valid_smatte_def)
  let ?p = "hd (mdisk n)"
  have p: "?p\<in>set (mdisk n)" by (rule hd_in_set[OF matte_ne[OF vn]])
  have "scale_point s ?p\<in>smatte_set m"
    using p by (simp add: m smatte_set_def mem_approx_scale)
  then show ?thesis by blast
qed

lemma mem_approx_halfg_preimage:
  "mem_approx (Suc s) {p. halfg p\<in>A} = mem_approx s A"
  by (auto simp: mem_approx_iff point_approx_halfg)

lemma mem_approx_union:
  "mem_approx s (A \<union> B) = mem_approx s A \<union> mem_approx s B"
  by (auto simp: mem_approx_iff)

lemma matte_interior_aux:
  assumes "valid_matte m" "z\<in>mem_approx s (set (mdisk m))"
    "mem_approx s (set (mdisk m)) \<subseteq> U"
    "z\<in>srect_set (s,inset_grect r)" "srect_set (s,r) \<subseteq> U"
  shows "\<exists>t n. valid_matte n \<and>
    mem_approx s (set (mdisk m)) \<subseteq> mem_approx t (set (mdisk n)) \<and>
    mem_approx t (set (mdisk n)) \<subseteq> U \<and>
    z\<in>interior (mem_approx t (set (mdisk n)))"
  using assms
proof (induction "mcorner m (point_approx s z)" arbitrary: s m r rule: less_induct)
  case less
  note v = less.prems(1) and at = less.prems(2) and sub = less.prems(3)
    and zin = less.prems(4) and box = less.prems(5)
  let ?p = "point_approx s z"
  have pm: "?p\<in>set (mdisk m)" using at by (simp only: mem_approx_iff)
  show ?case
  proof (cases "mcorner m ?p=0")
    case True
    have disk: "grect_set (ltouch ?p) \<subseteq> set (mdisk m)" by (rule mcorner0[OF pm True])
    obtain a b c d where rect: "z\<in>rp_rectangle a b c d"
      "rp_rectangle a b c d \<subseteq> srect_set (s,ltouch ?p)"
      using rect_approx[of s z ?p] by (auto simp: approx_point_iff)
    have rectsub: "rp_rectangle a b c d \<subseteq> mem_approx s (set (mdisk m))"
      using rect(2) sub_mem_approx[OF disk, of s] by (auto simp: srect_set_def)
    have interior: "z\<in>interior (mem_approx s (set (mdisk m)))"
      by (rule interiorI[OF _ rect(1) rectsub]) (simp add: rp_rectangle_def open_Times)
    show ?thesis by (rule exI[of _ s], rule exI[of _ m]) (use v sub interior in blast)
  next
    case False
    let ?q = "point_approx (Suc s) z"
    have half: "halfg ?q=?p" by (rule point_approx_halfg)
    have inset: "halfg ?q\<in>grect_set (inset_grect r)"
      using zin by (simp add: half srect_set_def mem_approx_iff)
    have pos: "0 < mcorner m (halfg ?q)" using False by (simp add: half)
    obtain n where n: "valid_matte n"
      "{p. halfg p\<in>set (mdisk m)} \<subseteq> set (mdisk n)"
      "set (mdisk n) \<subseteq> {p. halfg p\<in>grect_set r \<union> set (mdisk m)}"
      "mcorner n ?q < mcorner m (halfg ?q)"
      using refine_mcorner[OF v _ inset pos] pm by (auto simp only: half)
    have old: "mem_approx s (set (mdisk m)) \<subseteq> mem_approx (Suc s) (set (mdisk n))"
      using sub_mem_approx[OF n(2), of "Suc s"] by (simp only: mem_approx_halfg_preimage)
    have new: "mem_approx (Suc s) (set (mdisk n)) \<subseteq> U"
    proof -
      have bound: "mem_approx (Suc s) (set (mdisk n)) \<subseteq>
          mem_approx s (grect_set r \<union> set (mdisk m))"
        using sub_mem_approx[OF n(3), of "Suc s"] by (simp only: mem_approx_halfg_preimage)
      show ?thesis using bound box sub
        by (simp only: mem_approx_union srect_set_def fst_conv snd_conv; blast)
    qed
    have atn: "z\<in>mem_approx (Suc s) (set (mdisk n))" using old at by blast
    have zinnew: "z\<in>srect_set (Suc s,inset_grect (refine_rect r))"
      using mem_approx_refine_inset[of s r] zin by (auto simp: srect_set_def)
    have boxnew: "srect_set (Suc s,refine_rect r) \<subseteq> U"
      using box by (simp add: srect_set_def mem_approx_refine_rect)
    have decrease: "mcorner n ?q < mcorner m ?p" using n(4) by (simp only: half)
    obtain t k where k: "valid_matte k"
      "mem_approx (Suc s) (set (mdisk n)) \<subseteq> mem_approx t (set (mdisk k))"
      "mem_approx t (set (mdisk k)) \<subseteq> U"
      "z\<in>interior (mem_approx t (set (mdisk k)))"
      using less.hyps[OF decrease n(1) atn new zinnew boxnew] by blast
    show ?thesis by (rule exI[of _ t], rule exI[of _ k]) (use old k in blast)
  qed
qed

lemma smatte_interior:
  assumes op: "open U" and v: "valid_smatte m" and at: "z\<in>smatte_set m"
    and sub: "smatte_set m\<subseteq>U"
  shows "\<exists>n. valid_smatte n \<and> smatte_set m\<subseteq>smatte_set n \<and>
    smatte_set n\<subseteq>U \<and> z\<in>interior (smatte_set n)"
proof -
  obtain b where b: "z\<in>srect_set (inset_srect b)" "srect_set b\<subseteq>U"
    using approx_open[OF op subsetD[OF sub at]] by blast
  obtain s0 m0 where m: "m=(s0,m0)" by (cases m) auto
  obtain s1 r where br: "b=(s1,r)" by (cases b) auto
  let ?s = "s1+s0"
  let ?mr = "(refine_matte ^^ s1) m0"
  let ?rr = "(refine_rect ^^ s0) r"
  have valid: "valid_matte ?mr"
    by (rule iter_refine_matte_valid) (use v in \<open>simp add: m valid_smatte_def\<close>)
  have old: "mem_approx ?s (set (mdisk ?mr)) = smatte_set m"
    using in_refine_smatte[of s1 m] by (simp add: m refine_smatte_def smatte_set_def)
  have rect: "srect_set (?s,?rr) = srect_set b"
    using in_refine_srect[of s0 b] by (simp add: br refine_srect_def add.commute)
  have inset: "z\<in>srect_set (?s,inset_grect ?rr)"
    using in_refine_inset[of b s0] b(1)
    by (auto simp: br refine_srect_def inset_srect_def add.commute)
  obtain t n where n: "valid_matte n"
    "mem_approx ?s (set (mdisk ?mr)) \<subseteq> mem_approx t (set (mdisk n))"
    "mem_approx t (set (mdisk n)) \<subseteq> U"
    "z\<in>interior (mem_approx t (set (mdisk n)))"
    using matte_interior_aux[OF valid _ _ inset, of U] at sub b(2)
    by (auto simp only: old rect)
  show ?thesis by (rule exI[of _ "(t,n)"])
    (use n in \<open>auto simp: valid_smatte_def smatte_set_def old\<close>)
qed

lemma open_smatte_interpolated:
  assumes "open U"
  shows "open (smatte_interpolated K U)"
proof (subst open_subopen, intro ballI)
  fix z assume "z\<in>smatte_interpolated K U"
  then obtain m where m: "valid_smatte m" "z\<in>smatte_set m"
    "K\<subseteq>smatte_set m" "smatte_set m\<subseteq>U"
    by (auto simp: smatte_interpolated_def)
  obtain n where n: "valid_smatte n" "smatte_set m\<subseteq>smatte_set n"
    "smatte_set n\<subseteq>U" "z\<in>interior (smatte_set n)"
    using smatte_interior[OF assms m(1,2,4)] by blast
  have sub: "interior (smatte_set n) \<subseteq> smatte_interpolated K U"
    using n m(3) interior_subset[of "smatte_set n"]
    unfolding smatte_interpolated_def by blast
  show "\<exists>T. open T \<and> z\<in>T \<and> T\<subseteq>smatte_interpolated K U"
    by (rule exI[of _ "interior (smatte_set n)"]) (use n(4) sub in auto)
qed

lemma smatte_box_extension:
  assumes v: "valid_smatte m" and sub: "smatte_set m\<subseteq>U"
    and box: "srect_set b\<subseteq>U" and inset: "z\<in>srect_set (inset_srect b)"
    and meet: "smatte_set m \<inter> srect_set b \<noteq> {}"
  shows "\<exists>n. valid_smatte n \<and> smatte_set m\<subseteq>smatte_set n \<and>
    smatte_set n\<subseteq>U \<and> z\<in>smatte_set n"
proof -
  obtain s0 m0 where m: "m=(s0,m0)" by (cases m) auto
  obtain s1 r where br: "b=(s1,r)" by (cases b) auto
  let ?s = "Suc (s0+s1)"
  let ?mr = "(refine_matte ^^ Suc s1) m0"
  let ?rr = "(refine_rect ^^ Suc s0) r"
  have valid: "valid_matte ?mr"
    by (rule iter_refine_matte_valid) (use v in \<open>simp add: m valid_smatte_def\<close>)
  have old: "mem_approx ?s (set (mdisk ?mr)) = smatte_set m"
    using in_refine_smatte[of "Suc s1" m]
    by (simp add: m refine_smatte_def smatte_set_def add.commute)
  have rect: "mem_approx ?s (grect_set ?rr) = srect_set b"
    using in_refine_srect[of "Suc s0" b]
    by (simp add: br refine_srect_def srect_set_def)
  have coarse: "coarse_in (grect_set ?rr) ?mr" by (simp add: refine_matte_coarse)
  obtain t where t: "t\<in>smatte_set m" "t\<in>srect_set b" using meet by blast
  have meetgrid: "set (mdisk ?mr) \<inter> grect_set ?rr \<noteq> {}"
  proof -
    have "point_approx ?s t\<in>set (mdisk ?mr)"
      using t(1) by (simp only: old[symmetric] mem_approx_iff)
    moreover have "point_approx ?s t\<in>grect_set ?rr"
      using t(2) by (simp only: rect[symmetric] mem_approx_iff)
    ultimately show ?thesis by blast
  qed
  have insetgrid: "point_approx ?s z\<in>grect_set (inset_grect ?rr)"
    using in_refine_inset[of b "Suc s0"] inset
    by (auto simp: br refine_srect_def inset_srect_def srect_set_def mem_approx_iff)
  obtain n where ext: "matte_extension ?mr n"
    and bound: "set (mdisk n) \<subseteq> grect_set ?rr \<union> set (mdisk ?mr)"
    and at: "point_approx ?s z\<in>set (mdisk n)"
    using coarse_extends_in[OF valid coarse meetgrid insetgrid]
    unfolding extends_in_def by blast
  have vn: "valid_matte n" using matte_extension_valid[OF ext] by simp
  have oldsub: "smatte_set m \<subseteq> mem_approx ?s (set (mdisk n))"
    using sub_mem_approx[OF in_extension[OF ext], of ?s] by (simp only: old)
  have newsub: "mem_approx ?s (set (mdisk n)) \<subseteq> U"
  proof -
    have "mem_approx ?s (set (mdisk n)) \<subseteq>
        mem_approx ?s (grect_set ?rr) \<union> mem_approx ?s (set (mdisk ?mr))"
      using sub_mem_approx[OF bound, of ?s] by (simp only: mem_approx_union)
    then show ?thesis using sub box by (simp only: rect old) blast
  qed
  show ?thesis by (rule exI[of _ "(?s,n)"])
    (use vn oldsub newsub at in \<open>auto simp: valid_smatte_def smatte_set_def mem_approx_iff\<close>)
qed

lemma open_smatte_interpolated_complement:
  assumes op: "open U"
  shows "open (U - smatte_interpolated K U)"
proof (subst open_subopen, intro ballI)
  let ?I = "smatte_interpolated K U"
  fix z assume z: "z\<in>U - ?I"
  obtain b where b: "z\<in>srect_set (inset_srect b)" "srect_set b\<subseteq>U"
    using approx_open[OF op] z by blast
  have disjoint: "srect_set b \<inter> ?I = {}"
  proof (rule ccontr)
    assume "srect_set b \<inter> ?I \<noteq> {}"
    then obtain t where t: "t\<in>srect_set b" "t\<in>?I" by blast
    obtain m where m: "valid_smatte m" "t\<in>smatte_set m"
      "K\<subseteq>smatte_set m" "smatte_set m\<subseteq>U"
      using t(2) by (auto simp: smatte_interpolated_def)
    have meet: "smatte_set m \<inter> srect_set b \<noteq> {}" using m(2) t(1) by blast
    obtain n where n: "valid_smatte n" "smatte_set m\<subseteq>smatte_set n"
      "smatte_set n\<subseteq>U" "z\<in>smatte_set n"
      using smatte_box_extension[OF m(1,4) b(2,1) meet] by blast
    have "z\<in>?I" unfolding smatte_interpolated_def
      by (rule CollectI, rule exI[of _ n]) (use n m(3) in blast)
    then show False using z by blast
  qed
  have at: "z\<in>interior (srect_set b)" by (rule srect_inset_interior[OF b(1)])
  have sub: "interior (srect_set b) \<subseteq> U - ?I"
    using interior_subset[of "srect_set b"] b(2) disjoint by blast
  show "\<exists>T. open T \<and> z\<in>T \<and> T\<subseteq>U - ?I"
    by (rule exI[of _ "interior (srect_set b)"]) (use at sub in auto)
qed

lemma connected_smatte_interpolated:
  assumes op: "open U" and conn: "connected U"
    and valid: "valid_smatte m" and sub: "smatte_set m\<subseteq>U"
  shows "U\<subseteq>smatte_interpolated (smatte_set m) U"
proof -
  let ?I = "smatte_interpolated (smatte_set m) U"
  have isub: "?I\<subseteq>U" by (rule smatte_interpolated_sub)
  have initial: "smatte_set m\<subseteq>?I"
    unfolding smatte_interpolated_def
    by (intro subsetI CollectI, rule exI[of _ m]) (use valid sub in blast)
  have nonempty: "?I \<inter> U \<noteq> {}"
    using smatte_nonempty[OF valid] initial sub by blast
  have sep: "?I \<inter> (U-?I) \<inter> U = {}" by blast
  have cover: "U\<subseteq>?I \<union> (U-?I)" by blast
  have "?I \<inter> U = {} \<or> (U-?I) \<inter> U = {}"
    by (rule connectedD[OF conn open_smatte_interpolated[OF op]
        open_smatte_interpolated_complement[OF op] sep cover])
  then show ?thesis using nonempty by blast
qed

theorem connected_matte:
  assumes "open U" "connected U" "valid_smatte m" "smatte_set m\<subseteq>U" "z\<in>U"
  shows "\<exists>n. valid_smatte n \<and> z\<in>smatte_set n \<and>
    smatte_set m\<subseteq>smatte_set n \<and> smatte_set n\<subseteq>U"
  using connected_smatte_interpolated[OF assms(1-4)] assms(5)
  by (auto simp: smatte_interpolated_def)

end
