(* Two-side matte extension from matte.v. G. Gonthier et al., CeCILL-B.
   Isabelle/HOL port: Codex. *)
theory Matte_Extension2
  imports Four_Colour_Plane_Geometry.Matte_Extension
begin

lemma grid_endpoints_distinct: "end0g d \<noteq> end1g d"
  using oddg_corners[of d]
  by (auto simp: end0g_def end1g_def gcorners_def ccw_def)

lemma matte_ring_at_pair:
  assumes v: "valid_matte m" and a: "a\<in>set (mring m)"
    and b: "b\<in>set (mring m)" and link: "mrlink a b"
  obtains ds where "grid_cycle mrlink (a#b#ds)"
    "distinct (map end0g (a#b#ds))" "set (a#b#ds)=set (mring m)"
proof -
  obtain rs where cyc: "grid_cycle mrlink (a#rs)"
    and simple: "distinct (map end0g (a#rs))"
    and sets: "set (a#rs)=set (mring m)"
    by (rule matte_ring_at[OF v a])
  have inj: "inj_on end0g (set (mring m))"
    using mring_simple[OF v] by (simp add: distinct_map)
  obtain c ds where rs: "rs=c#ds"
  proof (cases rs)
    case Nil
    then have "end1g a=end0g a" using cyc by (simp add: grid_cycle_def mrlink_def)
    then show thesis using grid_endpoints_distinct[of a] by blast
  next
    case (Cons c ds)
    then show thesis by (rule that)
  qed
  have cb: "end0g c=end0g b" using cyc link by (simp add: rs grid_cycle_def mrlink_def)
  have c: "c\<in>set (mring m)" using sets rs by simp
  have eq: "c=b" by (rule inj_onD[OF inj cb c b])
  show thesis by (rule that) (use cyc simple sets in \<open>simp_all only: rs eq\<close>)
qed

definition ext2_quad :: "matte \<Rightarrow> gpoint \<Rightarrow> bool" where
  "ext2_quad m d \<longleftrightarrow> halfg (gedge d)\<in>set (mdisk m) \<and>
    halfg (gedge (gface d))\<in>set (mdisk m) \<and>
    grect_set (equad d)\<inter>set (mdisk m)={}"

definition ext2_loop :: "gpoint \<Rightarrow> gpoint list" where
  "ext2_loop d = [gface (gface d),gface (gface (gface d))]"

lemma halfg_equad: "halfg d\<in>grect_set (equad d)"
proof -
  have "halfg d\<in>gchop (gface d)" using gchop_halfg[of "gface d"] by simp
  then show ?thesis by (simp add: equad_def ehex_def in_gchop_rect gtouch_refl)
qed

lemma ext2_quad_fresh:
  "ext2_quad m d \<Longrightarrow> halfg d\<notin>set (mdisk m)"
  using halfg_equad[of d] by (auto simp: ext2_quad_def)

lemma ext2_loop_outside:
  assumes h: "ext2_quad m d" and q: "q\<in>set (ext2_loop d)"
  shows "halfg (gedge q)\<notin>set (mdisk m)"
proof -
  have "halfg (gedge q)\<in>grect_set (equad d)"
    using q oddg_corners[of d]
    by (cases "halfg d"; auto simp: ext2_loop_def equad_def ehex_def in_gchop_rect
      gchop_def gcorners_def ccw_def arcg_def)
  then show ?thesis using h unfolding ext2_quad_def by blast
qed

lemma ext2_new_vertex:
  assumes v: "valid_matte m" and h: "ext2_quad m d"
  shows "end0g (gface (gface (gface d)))\<notin>end0g ` set (mring m)"
  by (rule mring_equad[OF v]) (use h in \<open>simp add: ext2_quad_def gface4\<close>)

lemma pixel_sides_two:
  "halfg q=halfg d \<longleftrightarrow> q=d \<or> q=gface d \<or> q\<in>set (ext2_loop d)"
  by (simp add: pixel_sides ext1_loop_def ext2_loop_def)

lemma gborder_add_pixel_two:
  assumes fresh: "halfg d\<notin>A" and old0: "halfg (gedge d)\<in>A"
    and old1: "halfg (gedge (gface d))\<in>A"
    and outside: "\<And>q. q\<in>set (ext2_loop d) \<Longrightarrow> halfg (gedge q)\<notin>A"
  shows "gborder (insert (halfg d) A) =
    (gborder A - {gedge d,gedge (gface d)}) \<union> set (ext2_loop d)"
proof -
  have removed: "q\<in>gborder A \<and> halfg (gedge q)=halfg d \<longleftrightarrow>
    q=gedge d \<or> q=gedge (gface d)" for q
  proof
    assume q: "q\<in>gborder A \<and> halfg (gedge q)=halfg d"
    have cases: "gedge q=d \<or> gedge q=gface d \<or> gedge q\<in>set (ext2_loop d)"
      using q pixel_sides_two[of "gedge q" d] by blast
    have "gedge q=d \<or> gedge q=gface d"
    proof (rule ccontr)
      assume "\<not>(gedge q=d \<or> gedge q=gface d)"
      then have "gedge q\<in>set (ext2_loop d)" using cases by blast
      then have "halfg q\<notin>A" using outside[of "gedge q"] by (simp only: gedge2)
      then show False using q by (simp add: gborder_def)
    qed
    then show "q=gedge d \<or> q=gedge (gface d)" by (metis gedge2)
  next
    assume q: "q=gedge d \<or> q=gedge (gface d)"
    then show "q\<in>gborder A \<and> halfg (gedge q)=halfg d"
    proof
      assume "q=gedge d"
      then show ?thesis unfolding gborder_def
        by (simp only: mem_Collect_eq gedge2) (use fresh old0 in blast)
    next
      assume "q=gedge (gface d)"
      then show ?thesis unfolding gborder_def
        by (simp only: mem_Collect_eq gedge2 halfg_face) (use fresh old1 in blast)
    qed
  qed
  have no_self: "halfg (gedge q)\<noteq>halfg d" if "q\<in>set (ext2_loop d)" for q
    using that neq_halfg_edge[of q] by (auto simp: ext2_loop_def)
  show ?thesis
  proof (rule set_eqI)
    fix q
    show "q\<in>gborder (insert (halfg d) A) \<longleftrightarrow>
      q\<in>(gborder A - {gedge d,gedge (gface d)}) \<union> set (ext2_loop d)"
    proof (cases "halfg q=halfg d")
      case True
      then have sides: "q=d \<or> q=gface d \<or> q\<in>set (ext2_loop d)"
        by (simp only: pixel_sides_two)
      show ?thesis using True sides outside[of q] no_self[of q] fresh old0 old1
        by (auto simp: gborder_def)
    next
      case False
      then have off: "q\<notin>set (ext2_loop d)" using pixel_sides_two[of q d] by blast
      show ?thesis using removed[of q] False off by (auto simp: gborder_def)
    qed
  qed
qed

end
