(* Matte extensions from matte.v. Original G. Gonthier et al., CeCILL-B.
   Isabelle/HOL port: Codex. *)
theory Matte_Extension
  imports Matte
begin

lemma grid_cycle_rotate_head:
  "grid_cycle r (x#xs) \<longleftrightarrow> grid_cycle r (xs@[x])"
  by (cases xs) (auto simp: grid_cycle_def)

lemma grid_cycle_append_commute:
  "grid_cycle r (xs@ys) \<longleftrightarrow> grid_cycle r (ys@xs)"
proof (induction xs arbitrary: ys)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  have "grid_cycle r ((x#xs)@ys) = grid_cycle r ((xs@ys)@[x])"
    by (simp only: append_Cons; rule grid_cycle_rotate_head)
  also have "\<dots> = grid_cycle r ((ys@[x])@xs)"
    by (simp only: append_assoc Cons.IH)
  also have "\<dots> = grid_cycle r (ys@(x#xs))" by simp
  finally show ?case .
qed

lemma matte_ring_at:
  assumes v: "valid_matte m" and d: "d\<in>set (mring m)"
  obtains ds where "grid_cycle mrlink (d#ds)"
    "distinct (map end0g (d#ds))" "set (d#ds)=set (mring m)"
proof -
  obtain xs ys where split: "mring m=xs@d#ys" using split_list[OF d] by blast
  have cyc: "grid_cycle mrlink (d#(ys@xs))"
    using mring_cycle[OF v] grid_cycle_append_commute[of mrlink xs "d#ys"]
    by (simp add: split)
  have simple: "distinct (map end0g (d#(ys@xs)))"
    using mring_simple[OF v] by (auto simp: split distinct_append)
  have sets: "set (d#(ys@xs))=set (mring m)" by (auto simp: split)
  show thesis by (rule that[OF cyc simple sets])
qed

definition ext_mdisk :: "matte \<Rightarrow> gpoint \<Rightarrow> gpoint list" where
  "ext_mdisk m d = halfg d # mdisk m"
definition ehex :: "gpoint \<Rightarrow> grect" where
  "ehex d = gchop_rect (gtouch (halfg d)) d"
definition equad :: "gpoint \<Rightarrow> grect" where
  "equad d = gchop_rect (ehex d) (gface d)"

lemma ehexF: "grect_set (equad d) \<subseteq> grect_set (ehex (gface d))"
  by (auto simp: equad_def ehex_def in_gchop_rect)

lemma end0g_equad:
  assumes "grect_set (equad (gface d)) \<inter> set (mdisk m) = {}"
  shows "end0g d \<notin> set (mdisk m)"
proof -
  have "end0g d \<in> grect_set (equad (gface d))"
    using oddg_corners[of d]
    by (cases "halfg d"; auto simp: equad_def ehex_def in_gchop_rect
        gchop_def end0g_def gcorners_def ccw_def)
  then show ?thesis using assms by blast
qed

lemma equad_vertex: "equad (gface d) = ltouch (end0g d)"
  using oddg_corners[of d]
  by (cases "halfg d";
    auto simp: equad_def ehex_def gchop_rect.simps end0g_def gcorners_def ccw_def)

lemma halfg_ltouch_vertex: "halfg d\<in>grect_set (ltouch (end0g d))"
  using oddg_corners[of d]
  by (cases "halfg d") (auto simp: end0g_def gcorners_def)

lemma mring_equad:
  assumes v: "valid_matte m"
    and empty: "grect_set (equad (gface d)) \<inter> set (mdisk m) = {}"
  shows "end0g d \<notin> end0g ` set (mring m)"
proof
  assume "end0g d \<in> end0g ` set (mring m)"
  then obtain e where e: "e\<in>set (mring m)" "end0g d=end0g e" by blast
  have cell: "halfg e\<in>set (mdisk m)" using e(1) in_mring[OF v]
    by (auto simp: gborder_def)
  have inside: "halfg e\<in>grect_set (equad (gface d))"
    by (simp only: equad_vertex e(2) halfg_ltouch_vertex)
  show False using cell inside empty by blast
qed


lemma mring_gedge_iff:
  assumes "valid_matte m"
  shows "gedge d\<in>set (mring m) \<longleftrightarrow>
    halfg (gedge d)\<in>set (mdisk m) \<and> halfg d\<notin>set (mdisk m)"
  by (simp only: in_mring[OF assms] gborder_def mem_Collect_eq gedge2)

definition ext1_loop :: "gpoint \<Rightarrow> gpoint list" where
  "ext1_loop d = [gface d, gface (gface d), gface (gface (gface d))]"

definition ext1_hex :: "matte \<Rightarrow> gpoint \<Rightarrow> bool" where
  "ext1_hex m d \<longleftrightarrow> halfg (gedge d)\<in>set (mdisk m) \<and>
    grect_set (ehex d)\<inter>set (mdisk m)={}"

text \<open>The new pixel shares one side with the old disk. The empty hexagon
  excludes other occupied neighbours and keeps the two new boundary vertices
  away from the existing ring.\<close>

lemma ext1_hex_fresh:
  "ext1_hex m d \<Longrightarrow> halfg d\<notin>set (mdisk m)"
  by (auto simp: ext1_hex_def ehex_def in_gchop_rect dest: disjoint_iff[THEN iffD1]
      intro: gtouch_refl)

lemma ext1_loop_outside:
  assumes h: "ext1_hex m d" and q: "q\<in>set (ext1_loop d)"
  shows "halfg (gedge q)\<notin>set (mdisk m)"
proof -
  have "halfg (gedge q)\<in>grect_set (ehex d)"
    using q oddg_corners[of d]
    by (cases "halfg d"; auto simp: ext1_loop_def ehex_def in_gchop_rect
        gchop_def gcorners_def ccw_def arcg_def)
  then show ?thesis using h unfolding ext1_hex_def by blast
qed

lemma ext1_new_vertices:
  assumes v: "valid_matte m" and h: "ext1_hex m d"
  shows "end0g (gface (gface d))\<notin>end0g ` set (mring m)"
    "end0g (gface (gface (gface d)))\<notin>end0g ` set (mring m)"
proof -
  have empty: "grect_set (ehex d)\<inter>set (mdisk m)={}"
    using h by (simp add: ext1_hex_def)
  have sub2: "grect_set (equad (gface (gface (gface d))))\<subseteq>grect_set (ehex d)"
    using ehexF[of "gface (gface (gface d))"] by (simp add: gface4)
  have sub3: "grect_set (equad d)\<subseteq>grect_set (ehex d)"
    by (auto simp: equad_def in_gchop_rect)
  show "end0g (gface (gface d))\<notin>end0g ` set (mring m)"
    by (rule mring_equad[OF v]) (use empty sub2 in blast)
  show "end0g (gface (gface (gface d)))\<notin>end0g ` set (mring m)"
    by (rule mring_equad[OF v]) (use empty sub3 in \<open>simp add: gface4; blast\<close>)
qed

lemma pixel_sides:
  "halfg q=halfg d \<longleftrightarrow> q=d \<or> q\<in>set (ext1_loop d)"
proof
  assume eq: "halfg q=halfg d"
  have "q\<in>set [d,gface d,gface (gface d),gface (gface (gface d))]"
    by (rule same_halfg) (rule eq[symmetric])
  then show "q=d \<or> q\<in>set (ext1_loop d)" by (simp add: ext1_loop_def)
qed (auto simp: ext1_loop_def)

lemma gborder_add_pixel:
  assumes fresh: "halfg d\<notin>A" and old: "halfg (gedge d)\<in>A"
    and outside: "\<And>q. q\<in>set (ext1_loop d) \<Longrightarrow> halfg (gedge q)\<notin>A"
  shows "gborder (insert (halfg d) A) = (gborder A - {gedge d}) \<union> set (ext1_loop d)"
proof -
  have removed: "q\<in>gborder A \<and> halfg (gedge q)=halfg d \<longleftrightarrow> q=gedge d" for q
  proof
    assume q: "q\<in>gborder A \<and> halfg (gedge q)=halfg d"
    have cases: "gedge q=d \<or> gedge q\<in>set (ext1_loop d)"
      using q pixel_sides[of "gedge q" d] by blast
    have "gedge q=d"
    proof (rule ccontr)
      assume "gedge q\<noteq>d"
      then have "gedge q\<in>set (ext1_loop d)" using cases by blast
      then have "halfg q\<notin>A" using outside[of "gedge q"] by simp
      then show False using q by (simp add: gborder_def)
    qed
    then show "q=gedge d" by (metis gedge2)
  next
    assume q: "q=gedge d"
    show "q\<in>gborder A \<and> halfg (gedge q)=halfg d"
      unfolding q gborder_def
      by (simp only: mem_Collect_eq gedge2) (use fresh old in blast)
  qed
  have no_self: "halfg (gedge q)\<noteq>halfg d" if "q\<in>set (ext1_loop d)" for q
    using that neq_halfg_edge[of q] by (auto simp: ext1_loop_def)
  show ?thesis
  proof (rule set_eqI)
    fix q
    show "q\<in>gborder (insert (halfg d) A) \<longleftrightarrow>
      q\<in>(gborder A - {gedge d}) \<union> set (ext1_loop d)"
    proof (cases "halfg q=halfg d")
      case True
      then have sides: "q=d \<or> q\<in>set (ext1_loop d)" by (simp only: pixel_sides)
      show ?thesis using True sides outside[of q] no_self[of q] fresh old
        by (auto simp: gborder_def)
    next
      case False
      then have off: "q\<notin>set (ext1_loop d)" using pixel_sides[of q d] by blast
      show ?thesis using removed[of q] False off
        by (auto simp: gborder_def)
    qed
  qed
qed


lemma grid_path_mrlink_endpoints:
  assumes "end1g a=end1g b" "end0g c=end0g d"
  shows "grid_path mrlink a (xs@[c]) = grid_path mrlink b (xs@[d])"
  using assms
proof (induction xs arbitrary: a b)
  case Nil then show ?case by (simp add: mrlink_def)
next
  case (Cons x xs)
  have head: "mrlink a x = mrlink b x"
    by (simp only: mrlink_def Cons.prems(1))
  have tail: "grid_path mrlink x (xs@[c]) = grid_path mrlink x (xs@[d])"
    by (rule Cons.IH[OF refl Cons.prems(2)])
  show ?case by (simp only: append_Cons grid_path.simps head tail)
qed

lemma ext1_loop_cycle:
  assumes "grid_cycle mrlink (gedge d#ds)"
  shows "grid_cycle mrlink (ext1_loop d@ds)"
proof -
  have start: "end1g (gface (gface (gface d)))=end1g (gedge d)"
    using end0g_face[of "gface (gface (gface d))"]
    by (simp add: gface4 end1g_edge)
  have finish: "end0g (gface d)=end0g (gedge d)"
    by (simp add: end0g_face end0g_edge)
  have path: "grid_path mrlink (gface (gface (gface d))) (ds@[gface d])"
    using assms grid_path_mrlink_endpoints[OF start finish, of ds]
    by (simp add: grid_cycle_def)
  show ?thesis using path
    by (simp add: ext1_loop_def grid_cycle_def mrlink_def end0g_face)
qed

lemma ext1_loop_simple: "distinct (map end0g (ext1_loop d))"
  using oddg_corners[of d]
  by (cases "halfg d") (auto simp: ext1_loop_def end0g_def gcorners_def ccw_def)

lemma ext1_matte:
  assumes v: "valid_matte m" and h: "ext1_hex m d"
  shows "\<exists>xm. valid_matte xm \<and> mdisk xm=ext_mdisk m d"
proof -
  have fresh: "halfg d\<notin>set (mdisk m)" by (rule ext1_hex_fresh[OF h])
  have old: "halfg (gedge d)\<in>set (mdisk m)" using h by (simp add: ext1_hex_def)
  have edge: "gedge d\<in>set (mring m)"
    by (rule iffD2[OF mring_gedge_iff[OF v]]) (rule conjI[OF old fresh])
  obtain ds where cyc: "grid_cycle mrlink (gedge d#ds)"
    and simple: "distinct (map end0g (gedge d#ds))"
    and sets: "set (gedge d#ds)=set (mring m)"
    by (rule matte_ring_at[OF v edge])
  have dsset: "set ds=set (mring m)-{gedge d}"
    using sets simple by auto
  have disjoint: "end0g ` set (ext1_loop d) \<inter> end0g ` set ds={}"
    using ext1_new_vertices[OF v h] simple sets
    by (auto simp: ext1_loop_def end0g_face end0g_edge)
  have ring_simple: "distinct (map end0g (ext1_loop d@ds))"
    using simple disjoint ext1_loop_simple[of d] by (simp add: distinct_append)
  have border: "set (ext1_loop d@ds)=gborder (set (ext_mdisk m d))"
    using gborder_add_pixel[OF fresh old ext1_loop_outside[OF h]] dsset in_mring[OF v]
    by (auto simp: ext_mdisk_def)
  let ?xm = "\<lparr>mdisk=ext_mdisk m d, mring=ext1_loop d@ds\<rparr>"
  have "valid_matte ?xm"
    using ext1_loop_cycle[OF cyc] ring_simple border
    by (simp add: valid_matte_def ext_mdisk_def)
  then show ?thesis by (intro exI[of _ ?xm]) simp
qed

inductive matte_extension :: "matte \<Rightarrow> matte \<Rightarrow> bool" where
  refl: "valid_matte m \<Longrightarrow> matte_extension m m"
| add: "matte_extension m xm \<Longrightarrow> valid_matte ym \<Longrightarrow>
    gedge d\<in>set (mring xm) \<Longrightarrow>
    set (mdisk ym)=set (ext_mdisk xm d) \<Longrightarrow> matte_extension m ym"

lemma matte_extension_valid:
  "matte_extension m xm \<Longrightarrow> valid_matte m \<and> valid_matte xm"
  by (induction rule: matte_extension.induct) auto

lemma matte_extension_ext1:
  assumes ext: "matte_extension m xm" and h: "ext1_hex xm d"
  shows "\<exists>ym. matte_extension m ym \<and> mdisk ym=ext_mdisk xm d"
proof -
  have v: "valid_matte xm" using matte_extension_valid[OF ext] by simp
  obtain ym where valid: "valid_matte ym" and disk: "mdisk ym=ext_mdisk xm d"
    using ext1_matte[OF v h] by blast
  have edge: "gedge d\<in>set (mring xm)"
    using ext1_hex_fresh[OF h] h
    by (simp only: mring_gedge_iff[OF v] ext1_hex_def) blast
  have "matte_extension m ym"
    by (rule matte_extension.add[OF ext valid edge]) (simp only: disk)
  then show ?thesis using disk by blast
qed

lemma in_extension:
  "matte_extension m xm \<Longrightarrow> set (mdisk m) \<subseteq> set (mdisk xm)"
  by (induction rule: matte_extension.induct) (auto simp: ext_mdisk_def)

lemma matte_extension_trans:
  assumes "matte_extension m xm" "matte_extension xm ym"
  shows "matte_extension m ym"
  using assms(2,1)
  by (induction rule: matte_extension.induct) (auto intro: matte_extension.add)

definition extends_in :: "matte \<Rightarrow> grect \<Rightarrow> gpoint \<Rightarrow> bool" where
  "extends_in m r p \<longleftrightarrow> (\<exists>xm. matte_extension m xm \<and>
    set (mdisk xm) \<subseteq> grect_set r \<union> set (mdisk m) \<and> p\<in>set (mdisk xm))"

lemma extends_in_sub:
  "grect_set r \<subseteq> grect_set s \<Longrightarrow> extends_in m r p \<Longrightarrow> extends_in m s p"
  unfolding extends_in_def by blast

lemma extends_in_self:
  "valid_matte m \<Longrightarrow> p\<in>set (mdisk m) \<Longrightarrow> extends_in m r p"
  unfolding extends_in_def
  by (rule exI[of _ m]) (auto intro: matte_extension.refl)

lemma ext1_extends_in:
  assumes v: "valid_matte m" and h: "ext1_hex m d" and p: "halfg d\<in>grect_set r"
  shows "extends_in m r (halfg d)"
proof -
  obtain xm where ext: "matte_extension m xm" and disk: "mdisk xm=ext_mdisk m d"
    using matte_extension_ext1[OF matte_extension.refl[OF v] h] by blast
  show ?thesis unfolding extends_in_def
    by (rule exI[of _ xm]) (use ext disk p in \<open>auto simp: ext_mdisk_def\<close>)
qed

end
