(* Coarse matte extension from matte.v. Original G. Gonthier et al.,
   CeCILL-B. Isabelle/HOL port: Codex. *)
theory Coarse_Extension
  imports Four_Colour_Matte_Geometry.Matte_Extension2
    Four_Colour_Matte_Geometry.Coarse_Geometry Four_Colour_Matte_Geometry.Matte_Contact
begin

lemma extends_in_hex:
  assumes p: "halfg d\<in>grect_set r"
    and empty: "grect_set (ehex d) \<inter> set (mdisk m) = {}"
    and ext: "extends_in m (gchop_rect r (gedge d)) (halfg (gedge d))"
  shows "extends_in m r (halfg d)"
proof -
  obtain xm where xm: "matte_extension m xm"
    and sub: "set (mdisk xm) \<subseteq>
      grect_set (gchop_rect r (gedge d)) \<union> set (mdisk m)"
    and at: "halfg (gedge d)\<in>set (mdisk xm)"
    using ext unfolding extends_in_def by blast
  have new_empty: "grect_set (ehex d) \<inter> set (mdisk xm) = {}"
    using sub empty
    by (auto simp: ehex_def in_gchop_rect gchop_edge)
  have hex: "ext1_hex xm d" using at new_empty by (simp add: ext1_hex_def)
  obtain ym where ym: "matte_extension m ym" and disk: "mdisk ym=ext_mdisk xm d"
    using matte_extension_ext1[OF xm hex] by blast
  show ?thesis unfolding extends_in_def
    by (rule exI[of _ ym])
      (use ym disk sub p in \<open>auto simp: ext_mdisk_def in_gchop_rect\<close>)
qed

lemma inset_gchop1:
  assumes p: "p\<in>grect_set (inset_grect r)" and d: "halfg d=p"
  shows "p\<in>grect_set (inset_grect (gchop1_rect r d))"
proof -
  have "grect_set (gtouch p) \<subseteq> gchop1 d"
    using gtouch_chop1[of d] by (auto simp: d)
  then show ?thesis using p
    by (auto simp: insetP in_gchop1_rect)
qed

lemma coarse_extends_in_aux:
  assumes "valid_matte m" "coarse_in (grect_set r0) m"
    "set (mdisk m) \<inter> grect_set r0 \<subseteq> grect_set r"
    "grect_set r \<subseteq> grect_set r0"
    "set (mdisk m) \<inter> grect_set r \<noteq> {}"
    "p\<in>grect_set r" "p\<in>grect_set (inset_grect r0)"
  shows "extends_in m r p"
  using assms
proof (induction "garea r" arbitrary: r r0 p rule: less_induct)
  case less
  note v = less.prems(1) and coarse = less.prems(2)
    and retain = less.prems(3) and sub = less.prems(4)
    and meet = less.prems(5) and pr = less.prems(6) and pinset = less.prems(7)
  let ?M = "set (mdisk m)"
  show ?case
  proof (cases "p\<in>?M")
    case True
    then show ?thesis by (rule extends_in_self[OF v])
  next
    case False
    have p0: "p\<in>grect_set r0" using sub pr by blast
    have IHp: "extends_in m r p"
      if dp: "halfg d=p" and far: "?M \<inter> (grect_set r0 - gchop1 d) \<noteq> {}" for d
    proof -
      obtain q where q: "q\<in>?M" "q\<in>grect_set r0" "q\<notin>gchop1 d"
        using far by blast
      have qr: "q\<in>grect_set r" using q retain by blast
      let ?outer_cut = "gchop1_rect r0 d"
      have pinset1: "p\<in>grect_set (inset_grect ?outer_cut)"
        by (rule inset_gchop1[OF pinset dp])
      show ?thesis
      proof (cases "?M \<inter> grect_set ?outer_cut = {}")
        case False
        let ?inner_cut = "gchop1_rect r d"
        have sub1: "grect_set ?inner_cut \<subseteq> grect_set r" by (auto simp: in_gchop1_rect)
        have area: "garea ?inner_cut < garea r"
          by (rule ltn_garea_subrect[OF sub1, of q]) (use qr q(3) in \<open>simp add: in_gchop1_rect\<close>)
        have coarse1: "coarse_in (grect_set ?outer_cut) m"
          using coarse by (auto simp: coarse_in_def in_gchop1_rect)
        have retain1: "?M \<inter> grect_set ?outer_cut \<subseteq> grect_set ?inner_cut"
          using retain by (auto simp: in_gchop1_rect)
        have sub01: "grect_set ?inner_cut \<subseteq> grect_set ?outer_cut"
          using sub by (auto simp: in_gchop1_rect)
        have meet1: "?M \<inter> grect_set ?inner_cut \<noteq> {}" using False retain1 by blast
        have p1: "p\<in>grect_set ?inner_cut"
          using pr insetW[of ?outer_cut] pinset1 by (auto simp: in_gchop1_rect)
        have "extends_in m ?inner_cut p"
          by (rule less.hyps[OF area v coarse1 retain1 sub01 meet1 p1 pinset1])
        then show ?thesis by (rule extends_in_sub[OF sub1])
      next
        case True
        let ?inner_cut = "gchop_rect r (gedge d)"
        have sub1: "grect_set ?inner_cut \<subseteq> grect_set r" by (auto simp: in_gchop_rect)
        have q1: "q\<in>grect_set ?inner_cut"
          using qr q(3) gchop_chop1[of d] by (auto simp: in_gchop_rect gchop_edge)
        have area: "garea ?inner_cut < garea r"
          by (rule ltn_garea_subrect[OF sub1, of p])
            (use pr gchop_halfg[of d] in \<open>simp add: in_gchop_rect gchop_edge dp\<close>)
        have retain1: "?M \<inter> grect_set r0 \<subseteq> grect_set ?inner_cut"
          using retain True gchop_chop1[of d]
          by (auto simp: in_gchop_rect in_gchop1_rect gchop_edge)
        have sub01: "grect_set ?inner_cut \<subseteq> grect_set r0" using sub1 sub by blast
        have meet1: "?M \<inter> grect_set ?inner_cut \<noteq> {}" using q(1) q1 by blast
        have ep1: "halfg (gedge d)\<in>grect_set ?inner_cut"
          by (rule gchop_rect_edge[of "gedge d" r q]) (use pr q1 dp in simp_all)
        have einset: "halfg (gedge d)\<in>grect_set (inset_grect r0)"
          by (rule inset_edge_away[of d r0 q]) (use pinset q dp in auto)
        have ext: "extends_in m ?inner_cut (halfg (gedge d))"
          by (rule less.hyps[OF area v coarse retain1 sub01 meet1 ep1 einset])
        have empty: "grect_set (ehex d) \<inter> ?M = {}"
          using True pinset1
          by (auto simp: ehex_def in_gchop_rect in_gchop1_rect insetP dp)
        have "extends_in m r (halfg d)" by (rule extends_in_hex[OF _ empty ext]) (simp add: dp pr)
        then show ?thesis by (simp only: dp)
      qed
    qed
    let ?d = "neighbour_dart p"
    have n0: "gnode p\<in>grect_set r0"
      using pinset node_touch[of p] by (auto simp: insetP)
    have fe0: "gface (gedge p)\<in>grect_set r0"
    proof -
      have "gface (gedge p)\<in>grect_set (gtouch p)"
        using gtouch_edge[of "gface ?d"]
        by (simp only: halfg_face halfg_neighbour_dart
            neighbour_dart_face_edge[symmetric])
      then show ?thesis using pinset by (auto simp: insetP)
    qed
    have empty_quad: "grect_set (equad ?d) \<inter> ?M = {}"
      using coarse_equad_occupied[OF coarse p0] False by blast
    show ?thesis
    proof (cases "grect_set (ehex ?d) \<inter> ?M = {}")
      case False
      obtain q where q: "q\<in>grect_set (ehex ?d)" "q\<in>?M" using False by blast
      have qquad: "q\<in>grect_set (equad (gedge (gface ?d)))"
        using ehex_shift_quad[of ?d] q empty_quad by blast
      have old1: "halfg (gedge (gface ?d))\<in>?M"
      proof -
        have "gface (gedge p)\<in>?M"
          by (rule coarse_equad_occupied[OF coarse fe0])
            (use q qquad in \<open>auto simp: neighbour_dart_face_edge\<close>)
        then show ?thesis by (metis halfg_neighbour_dart neighbour_dart_face_edge)
      qed
      show ?thesis
      proof (cases "grect_set (ehex (gface ?d)) \<inter> ?M = {}")
        case True
        have hex: "ext1_hex m (gface ?d)" using old1 True by (simp add: ext1_hex_def)
        show ?thesis using ext1_extends_in[OF v hex] pr by simp
      next
        case False
        obtain q where q: "q\<in>grect_set (ehex (gface ?d))" "q\<in>?M" using False by blast
        have shifted: "gedge (gface (neighbour_dart (gnode p))) = ?d"
          by (metis neighbour_dart_face_edge gnodeK)
        have qquad: "q\<in>grect_set (equad (neighbour_dart (gnode p)))"
          using ehex_shift_quad[of "neighbour_dart (gnode p)"] q empty_quad
          by (auto simp only: shifted)
        have old0: "halfg (gedge ?d)\<in>?M"
        proof -
          have "gnode p\<in>?M"
            by (rule coarse_equad_occupied[OF coarse n0]) (use qquad q in blast)
          then show ?thesis by (simp only: halfg_edge_neighbour_dart)
        qed
        have quad: "ext2_quad m ?d" using old0 old1 empty_quad by (simp add: ext2_quad_def)
        obtain xm where ext: "matte_extension m xm" and disk: "mdisk xm=ext_mdisk m ?d"
          using matte_extension_ext2[OF matte_extension.refl[OF v] quad] by blast
        show ?thesis unfolding extends_in_def
          by (rule exI[of _ xm]) (use ext disk pr in \<open>auto simp: ext_mdisk_def\<close>)
      qed
    next
      case True
      note empty_hex = True
      show ?thesis
      proof (cases "grect_set (gtouch p) \<inter> ?M = {}")
        case True
        obtain q where q: "q\<in>?M" "q\<in>grect_set r" using meet by blast
        have nottouch: "q\<notin>grect_set (gtouch p)" using True q by blast
        have touch: "grect_set (gtouch p) = gchop1 ?d \<inter> gchop1 (gface ?d) \<inter>
            gchop1 (gface (gface ?d)) \<inter> gchop1 (gface (gface (gface ?d)))"
          using gtouch_chop1[of ?d] by simp
        have outside: "q\<notin>gchop1 ?d \<or> q\<notin>gchop1 (gface ?d) \<or>
            q\<notin>gchop1 (gface (gface ?d)) \<or> q\<notin>gchop1 (gface (gface (gface ?d)))"
          using nottouch by (auto simp only: touch Int_iff)
        obtain d where d: "d\<in>set [?d,gface ?d,gface (gface ?d),gface (gface (gface ?d))]"
          "q\<notin>gchop1 d" using outside by (simp only: list.set; blast)
        have hd: "halfg d=p" using d(1) by auto
        show ?thesis by (rule IHp[OF hd]) (use d q sub in blast)
      next
        case False
        obtain q where q: "q\<in>grect_set (gtouch p)" "q\<in>?M" using False by blast
        show ?thesis
        proof (rule extends_in_hex[of ?d r m,
            unfolded halfg_neighbour_dart halfg_edge_neighbour_dart, OF pr empty_hex])
          show "extends_in m (gchop_rect r (gedge ?d)) (gnode p)"
          proof (cases "gnode p\<in>?M")
            case True
            then show ?thesis by (rule extends_in_self[OF v])
          next
            case False
            have empty_nquad: "grect_set (equad (neighbour_dart (gnode p))) \<inter> ?M = {}"
              using coarse_equad_occupied[OF coarse n0] False by blast
            have n20: "gnode (gnode p)\<in>grect_set r0"
              using pinset node2_touch[of p] by (auto simp: insetP)
            have behind: "q\<in>gchop (gedge ?d)"
              using q empty_hex by (auto simp: ehex_def in_gchop_rect gchop_edge)
            have qquad: "q\<in>grect_set (equad (neighbour_dart (gnode (gnode p))))"
              using touch_behind_neighbour[of p] q behind empty_nquad by blast
            have old2: "gnode (gnode p)\<in>?M"
              by (rule coarse_equad_occupied[OF coarse n20]) (use q qquad in blast)
            have n2r: "gnode (gnode p)\<in>grect_set r" using old2 n20 retain by blast
            have nr: "gnode p\<in>grect_set r" by (rule node_between[OF pr n2r])
            have shifted: "gedge (gface (neighbour_dart (gnode p))) = ?d"
              by (metis neighbour_dart_face_edge gnodeK)
            have nhex: "grect_set (ehex (neighbour_dart (gnode p))) \<inter> ?M = {}"
              using ehex_shift_quad[of "neighbour_dart (gnode p)"] empty_nquad empty_quad
              by (auto simp only: shifted)
            have hex: "ext1_hex m (neighbour_dart (gnode p))"
              using old2 nhex by (simp only: ext1_hex_def halfg_edge_neighbour_dart; blast)
            have chop: "gnode p\<in>gchop (gedge ?d)"
              using gchop_halfg[of "gedge ?d"] by (simp only: halfg_edge_neighbour_dart)
            have atcut: "gnode p\<in>grect_set (gchop_rect r (gedge ?d))"
              using nr chop by (simp only: in_gchop_rect Int_iff; blast)
            show ?thesis
              using ext1_extends_in[OF v hex, of "gchop_rect r (gedge ?d)"] atcut
              by (simp only: halfg_neighbour_dart; blast)
          qed
        qed
      qed
    qed
  qed
qed

lemma coarse_extends_in:
  assumes "valid_matte m" "coarse_in (grect_set r) m"
    "set (mdisk m) \<inter> grect_set r \<noteq> {}"
    "p\<in>grect_set (inset_grect r)"
  shows "extends_in m r p"
  by (rule coarse_extends_in_aux[OF assms(1,2) _ _ assms(3) _ assms(4)])
    (use assms(4) insetW[of r] in auto)

lemma extend_madj:
  assumes v: "valid_matte m" and v1: "valid_matte m1"
    and coarse: "coarse_in (grect_set r) m"
    and meet: "set (mdisk m) \<inter> grect_set r \<noteq> {}"
    and meet1: "set (mdisk m1) \<inter> grect_set (inset_grect r) \<noteq> {}"
    and disjoint: "set (mdisk m) \<inter> set (mdisk m1) = {}"
  shows "\<exists>xm. valid_matte xm \<and> set (mdisk m) \<subseteq> set (mdisk xm) \<and>
    set (mdisk xm) \<subseteq> (grect_set r \<union> set (mdisk m)) - set (mdisk m1) \<and>
    madj m1 xm"
proof -
  obtain p where p: "p\<in>set (mdisk m1)" "p\<in>grect_set (inset_grect r)"
    using meet1 by blast
  obtain xm where ext: "matte_extension m xm"
    and bound: "set (mdisk xm) \<subseteq> grect_set r \<union> set (mdisk m)"
    and at: "p\<in>set (mdisk xm)"
    using coarse_extends_in[OF v coarse meet p(2)] unfolding extends_in_def by blast
  have contact: "set (mdisk xm) \<inter> set (mdisk m1) \<noteq> {}" using at p(1) by blast
  obtain ym where ym: "matte_extension m ym"
    "set (mdisk ym) \<subseteq> (grect_set r \<union> set (mdisk m)) - set (mdisk m1)"
    "madj m1 ym"
    using matte_extension_first_contact[OF ext v1 disjoint bound contact] by blast
  show ?thesis by (rule exI[of _ ym])
    (use ym in_extension[OF ym(1)] matte_extension_valid[OF ym(1)] in blast)
qed

end
