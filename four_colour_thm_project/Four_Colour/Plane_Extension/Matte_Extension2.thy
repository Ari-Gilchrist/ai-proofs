(* Two-side matte extension from matte.v. G. Gonthier et al., CeCILL-B.
   Isabelle/HOL port: Codex. *)
theory Matte_Extension2
  imports Four_Colour_Plane_Geometry.Matte_Extension
begin

lemma grid_endpoints_distinct: "end0g d \<noteq> end1g d"
  using neq_ccw[of "oddg d"] by (simp add: end0g_def end1g_def)

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
    then have False using grid_endpoints_distinct[of a] by simp
    then show thesis by (rule FalseE)
  next
    case (Cons c ds)
    then show thesis by (rule that)
  qed
  have cb: "end0g c=end0g b" using cyc link by (simp add: rs grid_cycle_def mrlink_def)
  have c: "c\<in>set (mring m)" using sets rs by auto
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
      then have in_loop: "gedge q\<in>set (ext2_loop d)" using cases by blast
      have notin: "halfg (gedge (gedge q))\<notin>A" by (rule outside[OF in_loop])
      have inside: "halfg q\<in>A" using q by (simp add: gborder_def)
      have outsideq: "halfg q\<notin>A" using notin by (simp only: gedge2; blast)
      show False by (rule notE[OF outsideq inside])
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


lemma ext2_loop_cycle:
  assumes cyc: "grid_cycle mrlink (gedge (gface d)#gedge d#ds)"
  shows "grid_cycle mrlink (ext2_loop d@ds)"
proof -
  have start: "end1g (gface (gface (gface d)))=end1g (gedge d)"
    using end0g_face[of "gface (gface (gface d))"]
    by (simp add: gface4 end1g_edge)
  have finish: "end0g (gface (gface d))=end0g (gedge (gface d))"
    by (simp add: end0g_face end0g_edge)
  have old: "grid_path mrlink (gedge d) (ds@[gedge (gface d)])"
    using cyc by (simp add: grid_cycle_def)
  have path: "grid_path mrlink (gface (gface (gface d))) (ds@[gface (gface d)])"
    using grid_path_mrlink_endpoints[OF start finish, of ds] old by simp
  show ?thesis using path
    by (simp add: ext2_loop_def grid_cycle_def mrlink_def end0g_face)
qed

lemma ext2_loop_simple: "distinct (map end0g (ext2_loop d))"
  using ext1_loop_simple[of d] by (simp add: ext1_loop_def ext2_loop_def)

lemma ext2_matte:
  assumes v: "valid_matte m" and h: "ext2_quad m d"
  shows "\<exists>xm. valid_matte xm \<and> mdisk xm=ext_mdisk m d"
proof -
  have fresh: "halfg d\<notin>set (mdisk m)" by (rule ext2_quad_fresh[OF h])
  have old0: "halfg (gedge d)\<in>set (mdisk m)"
    and old1: "halfg (gedge (gface d))\<in>set (mdisk m)"
    using h by (simp_all add: ext2_quad_def)
  have a: "gedge (gface d)\<in>set (mring m)"
    by (rule iffD2[OF mring_gedge_iff[OF v]]) (use old1 fresh in simp)
  have b: "gedge d\<in>set (mring m)"
    by (rule iffD2[OF mring_gedge_iff[OF v]]) (rule conjI[OF old0 fresh])
  have link: "mrlink (gedge (gface d)) (gedge d)"
    by (simp add: mrlink_def end1g_edge end0g_edge end0g_face)
  obtain ds where cyc: "grid_cycle mrlink (gedge (gface d)#gedge d#ds)"
    and simple: "distinct (map end0g (gedge (gface d)#gedge d#ds))"
    and sets: "set (gedge (gface d)#gedge d#ds)=set (mring m)"
    by (rule matte_ring_at_pair[OF v a b link])
  have dsset: "set ds=set (mring m)-{gedge d,gedge (gface d)}"
    using sets simple by auto
  have disjoint: "end0g ` set (ext2_loop d) \<inter> end0g ` set ds={}"
    using ext2_new_vertex[OF v h] simple sets
    by (auto simp: ext2_loop_def end0g_face end0g_edge)
  have ring_simple: "distinct (map end0g (ext2_loop d@ds))"
    using simple disjoint ext2_loop_simple[of d] by (simp add: distinct_append)
  have border: "set (ext2_loop d@ds)=gborder (set (ext_mdisk m d))"
    using gborder_add_pixel_two[OF fresh old0 old1 ext2_loop_outside[OF h]] dsset in_mring[OF v]
    by (auto simp: ext_mdisk_def)
  let ?xm = "\<lparr>mdisk=ext_mdisk m d, mring=ext2_loop d@ds\<rparr>"
  have "valid_matte ?xm"
    using ext2_loop_cycle[OF cyc] ring_simple border
    by (simp add: valid_matte_def ext_mdisk_def)
  then show ?thesis by (intro exI[of _ ?xm]) simp
qed

lemma matte_extension_ext2:
  assumes ext: "matte_extension m xm" and h: "ext2_quad xm d"
  shows "\<exists>ym. matte_extension m ym \<and> mdisk ym=ext_mdisk xm d"
proof -
  have v: "valid_matte xm" using matte_extension_valid[OF ext] by simp
  obtain ym where valid: "valid_matte ym" and disk: "mdisk ym=ext_mdisk xm d"
    using ext2_matte[OF v h] by blast
  have edge: "gedge d\<in>set (mring xm)"
    using ext2_quad_fresh[OF h] h
    by (simp only: mring_gedge_iff[OF v] ext2_quad_def) blast
  have "matte_extension m ym"
    by (rule matte_extension.add[OF ext valid edge]) (simp only: disk)
  then show ?thesis using disk by blast
qed

end
