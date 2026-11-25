(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Hypermap_iso.thy
    Transporting a hypermap along an injection of its darts, and the consequence
    that minimality of a counterexample applies to smaller maps of any dart type.
*)
theory Hypermap_iso
  imports Four_Colour_Base.Mincex Four_Colour_Maps.Snip
begin

definition hmap_img :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b hypermap \<Rightarrow> 'a hypermap" where
  "hmap_img \<phi> H =
     \<lparr>darts = \<phi> ` darts H,
      edge = (\<lambda>x. if x \<in> \<phi> ` darts H then \<phi> (edge H (inv_into (darts H) \<phi> x)) else x),
      node = (\<lambda>x. if x \<in> \<phi> ` darts H then \<phi> (node H (inv_into (darts H) \<phi> x)) else x),
      face = (\<lambda>x. if x \<in> \<phi> ` darts H then \<phi> (face H (inv_into (darts H) \<phi> x)) else x)\<rparr>"

locale hiso = hypermap H for H :: "'b hypermap" +
  fixes \<phi> :: "'b \<Rightarrow> 'a"
  assumes inj: "inj_on \<phi> (darts H)"
begin

abbreviation I where "I \<equiv> hmap_img \<phi> H"

lemma inv_phi [simp]: "x \<in> D \<Longrightarrow> inv_into D \<phi> (\<phi> x) = x"
  using inj by (simp add: inv_into_f_f)

lemma I_simps [simp]:
  "darts I = \<phi> ` D"
  "x \<in> D \<Longrightarrow> edge I (\<phi> x) = \<phi> (e x)"
  "x \<in> D \<Longrightarrow> node I (\<phi> x) = \<phi> (n x)"
  "x \<in> D \<Longrightarrow> face I (\<phi> x) = \<phi> (f x)"
  by (simp_all add: hmap_img_def)

lemma I_out: "y \<notin> \<phi> ` D \<Longrightarrow> edge I y = y \<and> node I y = y \<and> face I y = y"
  by (simp add: hmap_img_def)

lemma hypermap_I: "hypermap I"
proof -
  have eq: "I = \<lparr>darts = \<phi> ` D, edge = edge I, node = node I, face = face I\<rparr>" by (simp add: hmap_img_def)
  have cl: "edge I y \<in> \<phi> ` D \<and> node I y \<in> \<phi> ` D \<and> face I y \<in> \<phi> ` D" if "y \<in> \<phi> ` D" for y
    using that by auto
  have c3: "node I (face I (edge I y)) = y" for y
  proof (cases "y \<in> \<phi> ` D")
    case True
    then obtain x where x: "x \<in> D" "y = \<phi> x" by blast
    then show ?thesis by (simp add: edgeK)
  next
    case False then show ?thesis using I_out by simp
  qed
  have "hypermap \<lparr>darts = \<phi> ` D, edge = edge I, node = node I, face = face I\<rparr>"
    by (rule hypermap_cancel3) (use finite_darts cl I_out c3 in auto)
  then show ?thesis unfolding eq[symmetric] .
qed

sublocale J: hypermap I by (rule hypermap_I)

lemma funpow_I:
  assumes "x \<in> D"
  shows "(edge I ^^ k) (\<phi> x) = \<phi> ((e ^^ k) x)" "(node I ^^ k) (\<phi> x) = \<phi> ((n ^^ k) x)"
    "(face I ^^ k) (\<phi> x) = \<phi> ((f ^^ k) x)"
  using assms by (induction k) simp_all

lemma phi_eq: "x \<in> D \<Longrightarrow> y \<in> D \<Longrightarrow> \<phi> x = \<phi> y \<longleftrightarrow> x = y"
  using inj by (auto dest: inj_onD)

lemma fconnect_I:
  assumes x: "x \<in> D" and y: "y \<in> D"
  shows "fconnect (edge I) (\<phi> x) (\<phi> y) \<longleftrightarrow> cedge x y"
    "fconnect (node I) (\<phi> x) (\<phi> y) \<longleftrightarrow> cnode x y"
    "fconnect (face I) (\<phi> x) (\<phi> y) \<longleftrightarrow> cface x y"
  using funpow_I[OF x] phi_eq[OF _ y] x by (auto simp: fconnect_def)

lemma order_I:
  assumes x: "x \<in> D"
  shows "order (edge I) (\<phi> x) = order e x" "order (node I) (\<phi> x) = order n x"
    "order (face I) (\<phi> x) = order f x"
proof -
  have "card (cyc (edge I) (\<phi> x)) = card (\<phi> ` cyc e x)"
  proof -
    have "cyc (edge I) (\<phi> x) = \<phi> ` cyc e x"
    proof
      show "cyc (edge I) (\<phi> x) \<subseteq> \<phi> ` cyc e x"
      proof
        fix z assume "z \<in> cyc (edge I) (\<phi> x)"
        then obtain k where "z = (edge I ^^ k) (\<phi> x)" by (auto simp: cyc_def fconnect_def)
        then show "z \<in> \<phi> ` cyc e x" using funpow_I[OF x] by (auto simp: cyc_def fconnect_def)
      qed
      show "\<phi> ` cyc e x \<subseteq> cyc (edge I) (\<phi> x)"
        using funpow_I[OF x] by (auto simp: cyc_def fconnect_def)
    qed
    then show ?thesis by simp
  qed
  moreover have "inj_on \<phi> (cyc e x)" using inj E.cyc_subset[OF x] inj_on_subset by blast
  ultimately show "order (edge I) (\<phi> x) = order e x" by (simp add: order_def card_image)
next
  have "cyc (node I) (\<phi> x) = \<phi> ` cyc n x"
  proof
    show "cyc (node I) (\<phi> x) \<subseteq> \<phi> ` cyc n x"
    proof
      fix z assume "z \<in> cyc (node I) (\<phi> x)"
      then obtain k where "z = (node I ^^ k) (\<phi> x)" by (auto simp: cyc_def fconnect_def)
      then show "z \<in> \<phi> ` cyc n x" using funpow_I[OF x] by (auto simp: cyc_def fconnect_def)
    qed
    show "\<phi> ` cyc n x \<subseteq> cyc (node I) (\<phi> x)"
      using funpow_I[OF x] by (auto simp: cyc_def fconnect_def)
  qed
  moreover have "inj_on \<phi> (cyc n x)" using inj N.cyc_subset[OF x] inj_on_subset by blast
  ultimately show "order (node I) (\<phi> x) = order n x" by (simp add: order_def card_image)
next
  have "cyc (face I) (\<phi> x) = \<phi> ` cyc f x"
  proof
    show "cyc (face I) (\<phi> x) \<subseteq> \<phi> ` cyc f x"
    proof
      fix z assume "z \<in> cyc (face I) (\<phi> x)"
      then obtain k where "z = (face I ^^ k) (\<phi> x)" by (auto simp: cyc_def fconnect_def)
      then show "z \<in> \<phi> ` cyc f x" using funpow_I[OF x] by (auto simp: cyc_def fconnect_def)
    qed
    show "\<phi> ` cyc f x \<subseteq> cyc (face I) (\<phi> x)"
      using funpow_I[OF x] by (auto simp: cyc_def fconnect_def)
  qed
  moreover have "inj_on \<phi> (cyc f x)" using inj F.cyc_subset[OF x] inj_on_subset by blast
  ultimately show "order (face I) (\<phi> x) = order f x" by (simp add: order_def card_image)
qed

lemma fcard_I: "fcard (edge I) (darts I) = fcard e D" "fcard (node I) (darts I) = fcard n D"
  "fcard (face I) (darts I) = fcard f D"
proof -
  show "fcard (edge I) (darts I) = fcard e D" unfolding I_simps(1)
    by (rule fcard_hom[OF E.fperm_axioms J.E.fperm_axioms[unfolded I_simps(1)], symmetric])
      (simp_all add: inj)
  show "fcard (node I) (darts I) = fcard n D" unfolding I_simps(1)
    by (rule fcard_hom[OF N.fperm_axioms J.N.fperm_axioms[unfolded I_simps(1)], symmetric])
      (simp_all add: inj)
  show "fcard (face I) (darts I) = fcard f D" unfolding I_simps(1)
    by (rule fcard_hom[OF F.fperm_axioms J.F.fperm_axioms[unfolded I_simps(1)], symmetric])
      (simp_all add: inj)
qed

lemma card_I: "card (darts I) = card D"
  using inj by (simp add: card_image)

lemma glink_I: "x \<in> D \<Longrightarrow> y \<in> D \<Longrightarrow> glink I (\<phi> x) (\<phi> y) \<longleftrightarrow> glink H x y"
  using phi_eq by (auto simp: glink_def)

lemma gcomp_I:
  assumes x: "x \<in> D"
  shows "gcomp I (\<phi> x) z \<longleftrightarrow> (\<exists>y. gcomp H x y \<and> z = \<phi> y)"
proof
  assume "gcomp I (\<phi> x) z"
  then show "\<exists>y. gcomp H x y \<and> z = \<phi> y"
  proof (induction rule: rtranclp_induct)
    case base then show ?case by blast
  next
    case (step u v)
    then obtain y where y: "gcomp H x y" "u = \<phi> y" by blast
    have yD: "y \<in> D" using y(1) x gcomp_closed by blast
    have "glink H y (inv_into D \<phi> v) \<and> v = \<phi> (inv_into D \<phi> v)"
      using step(2) y(2) yD by (auto simp: glink_def)
    then show ?case using y(1) by (meson rtranclp.rtrancl_into_rtrancl)
  qed
next
  assume "\<exists>y. gcomp H x y \<and> z = \<phi> y"
  then obtain y where y: "gcomp H x y" "z = \<phi> y" by blast
  have "gcomp I (\<phi> x) (\<phi> y)" using y(1) x
  proof (induction rule: rtranclp_induct)
    case (step u v)
    have uD: "u \<in> D" using step(1) x gcomp_closed by blast
    have vD: "v \<in> D" using step(2) uD glink_closed by blast
    have "glink I (\<phi> u) (\<phi> v)" using glink_I[OF uD vD] step(2) by simp
    then show ?case using step by (meson rtranclp.rtrancl_into_rtrancl)
  qed simp
  then show "gcomp I (\<phi> x) z" using y(2) by simp
qed

lemma n_comp_I: "n_comp (glink I) (darts I) = n_comp (glink H) D"
proof -
  have "card (comp_of (glink H) ` D) = card (comp_of (glink I) ` (\<phi> ` D))"
  proof (rule card_classes_reflect[where h = \<phi>])
    fix xa xb assume xa: "xa \<in> D" and xb: "xb \<in> D"
    have "comp_of (glink I) (\<phi> xa) = comp_of (glink I) (\<phi> xb) \<longleftrightarrow> gcomp I (\<phi> xa) (\<phi> xb)"
      by (rule J.comp_eq_iff)
    also have "\<dots> \<longleftrightarrow> gcomp H xa xb"
    proof -
      have "gcomp I (\<phi> xa) (\<phi> xb) \<longleftrightarrow> (\<exists>y. gcomp H xa y \<and> \<phi> xb = \<phi> y)" by (rule gcomp_I[OF xa])
      also have "\<dots> \<longleftrightarrow> gcomp H xa xb"
      proof
        assume "\<exists>y. gcomp H xa y \<and> \<phi> xb = \<phi> y"
        then obtain y where y: "gcomp H xa y" "\<phi> xb = \<phi> y" by blast
        have "y \<in> D" using y(1) xa gcomp_closed by blast
        then have "y = xb" using y(2) phi_eq[OF xb] by simp
        then show "gcomp H xa xb" using y(1) by simp
      qed blast
      finally show ?thesis .
    qed
    also have "\<dots> \<longleftrightarrow> comp_of (glink H) xa = comp_of (glink H) xb" by (rule comp_eq_iff[symmetric])
    finally show "comp_of (glink H) xa = comp_of (glink H) xb \<longleftrightarrow>
                  comp_of (glink I) (\<phi> xa) = comp_of (glink I) (\<phi> xb)" by simp
  next
    show "\<phi> ` D \<subseteq> \<phi> ` D" by simp
  next
    fix z assume "z \<in> \<phi> ` D"
    then show "\<exists>x \<in> D. comp_of (glink I) (\<phi> x) = comp_of (glink I) z" by blast
  qed
  then show ?thesis by (simp add: n_comp_def)
qed

lemma genus_I: "genus I = genus H"
  using n_comp_I fcard_I card_I by (simp add: genus_def Euler_lhs_def Euler_rhs_def)

lemma planar_I: "planar I \<longleftrightarrow> planar H"
  by (simp add: planar_def genus_I)

lemma connected_I: "connected I \<longleftrightarrow> connected H"
  using n_comp_I by (simp add: connected_def)

lemma plain_I: "plain I \<longleftrightarrow> plain H"
  by (auto simp: plain_def plainb_def order_I)

lemma cubic_I: "cubic I \<longleftrightarrow> cubic H"
  by (auto simp: cubic_def cubicb_def order_I)

lemma precubic_I: "precubic I \<longleftrightarrow> precubic H"
  by (auto simp: precubic_def order_I)

lemma bridgeless_I: "bridgeless I \<longleftrightarrow> bridgeless H"
  by (auto simp: bridgeless_def fconnect_I)

lemma four_colorable_I: "four_colorable I \<longleftrightarrow> four_colorable H"
proof
  assume "four_colorable I"
  then obtain k where k: "coloring I k" by (auto simp: four_colorable_def)
  have "coloring H (k \<circ> \<phi>)" using k by (auto simp: coloring_def)
  then show "four_colorable H" by (auto simp: four_colorable_def)
next
  assume "four_colorable H"
  then obtain k where k: "coloring H k" by (auto simp: four_colorable_def)
  have "coloring I (k \<circ> inv_into D \<phi>)" using k by (auto simp: coloring_def)
  then show "four_colorable I" by (auto simp: four_colorable_def)
qed

lemma pbpp_I: "planar_bridgeless_plain_precubic I \<longleftrightarrow> planar_bridgeless_plain_precubic H"
  using hypermap_I hypermap_axioms
  by (simp add: planar_bridgeless_plain_precubic_def planar_bridgeless_plain_def planar_bridgeless_def
      planar_I bridgeless_I plain_I precubic_I)

end

theorem minimal_counter_example_any_type:
  fixes G :: "'a hypermap" and H :: "'b hypermap"
  assumes mce: "minimal_counter_example G" and pH: "planar_bridgeless_plain_precubic H"
    and lt: "card (darts H) < card (darts G)"
  shows "four_colorable H"
proof -
  have hH: "hypermap H"
    using pH by (simp add: planar_bridgeless_plain_precubic_def planar_bridgeless_plain_def planar_bridgeless_def)
  have hG: "hypermap G" by (rule mce_hypermap[OF mce])
  have finH: "finite (darts H)" using hypermap.finite_darts[OF hH] .
  have finG: "finite (darts G)" using hypermap.finite_darts[OF hG] .
  obtain \<phi> :: "'b \<Rightarrow> 'a" where \<phi>: "\<phi> ` darts H \<subseteq> darts G" "inj_on \<phi> (darts H)"
    using card_le_inj[OF finH finG] lt by (metis less_imp_le)
  interpret I: hiso H \<phi> using hH \<phi>(2) by (simp add: hiso_def hiso_axioms_def)
  have "planar_bridgeless_plain_precubic I.I" using pH I.pbpp_I by simp
  moreover have "card (darts I.I) < card (darts G)" using lt I.card_I by simp
  ultimately have "four_colorable I.I" using mce by (auto simp: minimal_counter_example_def)
  then show ?thesis using I.four_colorable_I by simp
qed

end
