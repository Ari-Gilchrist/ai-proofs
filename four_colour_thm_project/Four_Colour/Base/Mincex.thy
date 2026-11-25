(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Mincex.thy
    Minimal counterexamples to the four colour theorem, and the fact that they
    are cubic.  Ported from G. Gonthier's Coq development (coloring.v).
*)
theory Mincex
  imports Coloring
begin

definition minimal_counter_example :: "'a hypermap \<Rightarrow> bool" where
  "minimal_counter_example G \<longleftrightarrow>
     planar_bridgeless_plain_precubic G \<and> \<not> four_colorable G \<and>
     (\<forall>G' :: 'a hypermap. planar_bridgeless_plain_precubic G' \<longrightarrow>
         card (darts G') < card (darts G) \<longrightarrow> four_colorable G')"

lemma mce_hypermap: "minimal_counter_example G \<Longrightarrow> hypermap G"
  by (simp add: minimal_counter_example_def planar_bridgeless_plain_precubic_def
      planar_bridgeless_plain_def planar_bridgeless_def)

context hypermap
begin

theorem minimal_counter_example_is_cubic:
  assumes mce: "minimal_counter_example G"
  shows "cubic G"
proof (rule ccontr)
  assume "\<not> cubic G"
  then obtain x where xD: "x \<in> D" and nx3: "order n x \<noteq> 3"
    by (auto simp: cubic_def cubicb_def)
  have planG: "planar G" and bG: "bridgeless G" and pG: "plain G" and pcG: "precubic G"
    and ncol: "\<not> four_colorable G"
    using mce by (auto simp: minimal_counter_example_def planar_bridgeless_plain_precubic_def
        planar_bridgeless_plain_def planar_bridgeless_def)
  have minG: "\<And>G' :: 'a hypermap. planar_bridgeless_plain_precubic G' \<Longrightarrow> card (darts G') < card D \<Longrightarrow> four_colorable G'"
    using mce unfolding minimal_counter_example_def by blast
  have bridge: "\<not> cface y (e y)" if "y \<in> D" for y using bG that by (simp add: bridgeless_def)
  \<comment> \<open>Faces never contain a dart and its node image.\<close>
  have no_fn: "\<not> cface y (n y)" if yD: "y \<in> D" for y
  proof
    assume c: "cface y (n y)"
    have "f (e (n y)) = y" by (rule nodeK)
    then have "cface (e (n y)) y" using fconnect_step[of f "e (n y)"] by simp
    then have "cface (n y) (e (n y))"
      using fconnect_trans[OF F.fconnect_sym[OF c] F.fconnect_sym] by blast
    then show False using bridge[of "n y"] yD by simp
  qed
  have nx: "n x \<noteq> x" using no_fn[OF xD] by auto
  have nnx: "n (n x) = x"
  proof -
    have "order n x \<le> 3" using pcG xD by (simp add: precubic_def)
    moreover have "order n x \<noteq> 1" using nx N.order_1_iff by simp
    moreover have "order n x > 0" by simp
    ultimately have "order n x = 2" using nx3 by linarith
    then have "(n ^^ 2) x = x" using N.funpow_order[of x] by simp
    then show ?thesis by (simp add: numeral_2_eq_2)
  qed
  have nxD: "n x \<in> D" using xD by simp
  define G1 where "G1 = WalkupE G x"
  define G2 where "G2 = WalkupE G1 (n x)"
  interpret W1: hypermap G1 unfolding G1_def by (rule hypermap_WalkupE)
  interpret W2: hypermap G2 unfolding G2_def by (rule W1.hypermap_WalkupE)
  have D1: "darts G1 = D - {x}" by (simp add: G1_def)
  have D2: "darts G2 = D - {x} - {n x}" by (simp add: G2_def G1_def)
  have nx1: "n x \<in> darts G1" using D1 nxD nx by simp
  have inD2: "w \<in> darts G2 \<longleftrightarrow> w \<in> D \<and> w \<noteq> x \<and> w \<noteq> n x" for w using D2 by auto
  \<comment> \<open>Node and face of G2.\<close>
  have hN: "node G2 w = n w" if "w \<in> darts G2" for w
  proof -
    have w: "w \<noteq> x" "w \<noteq> n x" using that inD2 by auto
    have nwx: "n w \<noteq> x" using w nnx N.eq_iff[of w "n x"] by auto
    have nwnx: "n w \<noteq> n x" using w by simp
    show ?thesis using w nwx nwnx by (simp add: G2_def G1_def skip_def)
  qed
  have hF: "fconnect (face G2) a b \<longleftrightarrow> cface a b" if ab: "a \<in> darts G2" "b \<in> darts G2" for a b
  proof -
    have a: "a \<noteq> x" "a \<noteq> n x" and b: "b \<noteq> x" "b \<noteq> n x" using ab inD2 by auto
    have "fconnect (face G2) a b \<longleftrightarrow> fconnect (face G1) a b \<and> b \<noteq> n x"
      unfolding G2_def using W1.F.fconnect_skip[OF a(2)] by simp
    also have "fconnect (face G1) a b \<longleftrightarrow> cface a b \<and> b \<noteq> x"
      unfolding G1_def using F.fconnect_skip[OF a(1)] by simp
    finally show ?thesis using b by simp
  qed
  have glnx: "glink G1 (n x) (n x)"
  proof -
    have "node G1 (n x) = n x" using nnx nx by (simp add: G1_def skip_def)
    then show ?thesis by (simp add: glink_def)
  qed
  have eG2: "edge G2 = skip (n x) (skip_edge G x)"
    using W1.glink_fp_skip_edge[OF glnx] by (simp add: G2_def G1_def fun_eq_iff)
  \<comment> \<open>G2 satisfies the induction hypotheses.\<close>
  have card2: "card (darts G2) < card D"
  proof -
    have "darts G2 \<subset> D" using D2 xD by auto
    then show ?thesis using finite_darts by (rule psubset_card_mono[rotated])
  qed
  have plan2: "planar G2"
    unfolding G2_def using W1.planar_WalkupE[OF _ nx1] planar_WalkupE[OF planG xD]
    by (simp add: G1_def)
  have cnx: "cyc n x = {x, n x}"
  proof -
    have c: "cycle (frel n) [x, n x]" using nnx by (simp add: cycle_Cons)
    have d: "distinct [x, n x]" using nx by simp
    have "cyc n x = set [x, n x]" by (rule F.distinct_cycle_cyc[OF N.fperm_axioms c d]) simp
    then show ?thesis by simp
  qed
  have ncyc2: "y \<in> darts G2" if w2: "w \<in> darts G2" and wy: "cnode w y" for w y
  proof -
    have yD: "y \<in> D" using wy w2 inD2 N.fconnect_in_D by blast
    have "y \<notin> cyc n x"
    proof
      assume "y \<in> cyc n x"
      then have "cyc n x = cyc n y" by (rule N.cyc_unique)
      also have "cyc n y = cyc n w" using wy by (simp add: N.cyc_eq)
      finally have "w \<in> cyc n x" by simp
      then show False using w2 inD2 cnx by auto
    qed
    then show ?thesis using yD inD2 cnx by auto
  qed
  have pc2: "precubic G2" unfolding precubic_def
  proof
    fix w assume w2: "w \<in> darts G2"
    have "cyc (node G2) w = cyc n w"
      by (rule cyc_eq_on) (use hN ncyc2[OF w2] in blast)
    then have "order (node G2) w = order n w" by (simp add: order_def)
    also have "\<dots> \<le> 3" using pcG w2 inD2 by (simp add: precubic_def)
    finally show "order (node G2) w \<le> 3" .
  qed
  have b2: "bridgeless G2" unfolding bridgeless_def
  proof (intro ballI notI)
    fix w assume w2: "w \<in> darts G2" and br: "fconnect (face G2) w (edge G2 w)"
    define y where "y = face G2 (edge G2 w)"
    have y2: "y \<in> darts G2" using w2 by (simp add: y_def)
    have wy: "node G2 y = w" unfolding y_def by (rule W2.edgeK)
    have "fconnect (face G2) (edge G2 w) y" using fconnect_step[of "face G2" "edge G2 w"] by (simp add: y_def)
    then have "fconnect (face G2) w y" by (rule fconnect_trans[OF br])
    then have "cface w y" using hF[OF w2 y2] by simp
    moreover have "w = n y" using wy hN[OF y2] by simp
    ultimately have "cface (n y) y" by simp
    then have "cface y (n y)" by (rule F.fconnect_sym)
    then show False using no_fn y2 inD2 by blast
  qed
  have p2: "plain G2" unfolding plain_def plainb_def
  proof
    fix w assume w2: "w \<in> darts G2"
    have wx: "w \<noteq> x" and wnx: "w \<noteq> n x" and wD: "w \<in> D" using w2 inD2 by auto
    have w1: "w \<in> darts G1" using D1 wD wx by simp
    have c2: "cyc (edge G2) w = cyc (skip_edge G x) w - {n x}"
      using W1.E.cyc_skip[OF wnx] eG2 by (simp add: G1_def)
    have ecyc: "cyc e y = {y, e y}" for y
      using plain_orbit[OF pG] by (auto simp: cyc_def)
    show "order (edge G2) w = 2"
    proof (cases "edom x w")
      case True
      have nc: "\<not> cross_edge G x"
      proof
        assume "cross_edge G x"
        then have "n x = x \<or> n x = e x" using plain_orbit[OF pG] by (simp add: cross_edge_def)
        then have nxe: "n x = e x" using nx by simp
        have "cyc e (n x) = cyc e x" using nxe E.cyc_eq fconnect_step by metis
        then have cc: "cyc e (n x) = cyc e x" .
        have "x \<in> cyc e w \<or> n x \<in> cyc e w" using True by (simp add: edom_def E.in_cyc_iff)
        then have "cyc e w = cyc e x" using E.cyc_unique cc by metis
        then have "w \<in> cyc e x" using E.x_in_cyc[of w] by simp
        then have "w = x \<or> w = e x" using ecyc by auto
        then show False using wx wnx nxe by auto
      qed
      have cw: "cyc (skip_edge G x) w = {e x, n x, e (n x)}"
      proof (intro set_eqI iffI)
        fix y assume "y \<in> cyc (skip_edge G x)  w"
        then have wy: "fconnect (skip_edge G x) w y" by (simp add: cyc_def)
        have wy1: "fconnect (edge G1) w y" using wy by (simp add: G1_def)
        have "y \<in> darts G1" using W1.E.fconnect_in_D[OF wy1] w1 by simp
        then have yx: "y \<noteq> x" using D1 by simp
        have "edom x y" using cskip_edge_merge[OF nc xD True wx yx] wy by simp
        then have "cedge y x \<or> cedge y (n x)" by (simp add: edom_def)
        then have "x = y \<or> x = e y \<or> n x = y \<or> n x = e y" using plain_orbit[OF pG] by blast
        moreover have "x = e y \<Longrightarrow> y = e x" "n x = e y \<Longrightarrow> y = e (n x)" using plain_eq[OF pG] by auto
        ultimately show "y \<in> {e x, n x, e (n x)}" using yx by auto
      next
        fix y assume yin: "y \<in> {e x, n x, e (n x)}"
        have exnx: "e x \<noteq> n x"
        proof
          assume "e x = n x"
          then have "cedge x (n x)" using fconnect_step[of e x] by simp
          then show False using nc by (simp add: cross_edge_def)
        qed
        have enx: "e (n x) \<noteq> x"
        proof
          assume "e (n x) = x"
          then have "n x = e x" using plain_eq[OF pG, of "n x"] by simp
          then show False using exnx by simp
        qed
        have yx: "y \<noteq> x" using yin nx plain_neq[OF pG xD] enx by auto
        have "edom x y" using yin by (auto simp: edom_def E.fconnect_commute fconnect_step)
        then have "fconnect (skip_edge G x) w y" using cskip_edge_merge[OF nc xD True wx yx] by simp
        then show "y \<in> cyc (skip_edge G x) w" by (simp add: cyc_def)
      qed
      have d1: "e x \<noteq> e (n x)" using nx by simp
      have d2: "e x \<noteq> n x"
      proof
        assume "e x = n x"
        then have "cedge x (n x)" using fconnect_step[of e x] by simp
        then show False using nc by (simp add: cross_edge_def)
      qed
      have d3: "e (n x) \<noteq> n x" using plain_neq[OF pG nxD] .
      have "cyc (edge G2) w = {e x, e (n x)}" using c2 cw d2 d3 by auto
      then show ?thesis using d1 by (simp add: order_def)
    next
      case False
      have cw: "cyc (skip_edge G x) w = {w, e w}"
        using same_cskip_edge[OF False wx] ecyc[of w] by (auto simp: cyc_def)
      have "n x \<noteq> e w"
      proof
        assume "n x = e w"
        then have "cedge w (n x)" using fconnect_step[of e w] by simp
        then show False using False by (simp add: edom_def)
      qed
      then have "cyc (edge G2) w = {w, e w}" using c2 cw wnx by auto
      then show ?thesis using plain_neq[OF pG wD] by (simp add: order_def)
    qed
  qed
  have "planar_bridgeless_plain_precubic G2"
    using W2.hypermap_axioms plan2 b2 p2 pc2
    by (simp add: planar_bridgeless_plain_precubic_def planar_bridgeless_plain_def planar_bridgeless_def)
  then obtain k where k: "coloring G2 k" using minG card2 by (auto simp: four_colorable_def)
  \<comment> \<open>Lifting the colouring back to G.\<close>
  define k' where "k' y = (if \<exists>w \<in> darts G2. cface y w then k (SOME w. w \<in> darts G2 \<and> cface y w)
                          else if y = x then Color1 else Color0)" for y
  have F1: "k w = k w'" if "w \<in> darts G2" "w' \<in> darts G2" "cface w w'" for w w'
    using W2.coloring_cface[OF k, of w w'] hF that by simp
  have F2: "k' z = k z" if z2: "z \<in> darts G2" for z
  proof -
    have ex: "\<exists>w. w \<in> darts G2 \<and> cface z w" using z2 by blast
    define w where "w = (SOME w. w \<in> darts G2 \<and> cface z w)"
    have sm: "w \<in> darts G2 \<and> cface z w" unfolding w_def by (rule someI_ex[OF ex])
    have "k' z = k w" using ex unfolding k'_def w_def by auto
    also have "\<dots> = k z" using F1[of z w] z2 sm by simp
    finally show ?thesis .
  qed
  have F3: "y = x \<or> y = n x" if yD: "y \<in> D" and no: "\<forall>w \<in> darts G2. \<not> cface y w" for y
    using no inD2[of y] yD by auto
  have nswap: "n y = (if y = x then n x else x)" if "y = x \<or> y = n x" for y
    using that nnx by auto
  have F4: "y = z" if yD: "y \<in> D" and no: "\<forall>w \<in> darts G2. \<not> cface y w" and yz: "cface y z" for y z
  proof (rule ccontr)
    assume yz': "y \<noteq> z"
    have zD: "z \<in> D" using yz yD F.fconnect_in_D by blast
    have noz: "\<forall>w \<in> darts G2. \<not> cface z w"
      using no fconnect_trans[OF yz] by blast
    have "y = x \<or> y = n x" "z = x \<or> z = n x" using F3[OF yD no] F3[OF zD noz] by simp_all
    then have "z = n y" using yz' nnx by auto
    then show False using no_fn[OF yD] yz by simp
  qed
  have F5: "k' y = k' z" if yD: "y \<in> D" and yz: "cface y z" for y z
  proof (cases "\<exists>w \<in> darts G2. cface y w")
    case True
    then obtain w where w: "w \<in> darts G2" "cface y w" by blast
    have zw: "cface z w" using fconnect_trans[OF F.fconnect_sym[OF yz] w(2)] .
    have "k' y = k' w" proof -
      have ex: "\<exists>u \<in> darts G2. cface y u" using True .
      obtain u where u: "u \<in> darts G2" "cface y u" "u = (SOME u. u \<in> darts G2 \<and> cface y u)"
        using someI_ex[of "\<lambda>u. u \<in> darts G2 \<and> cface y u"] ex by blast
      have "k u = k w" using F1[OF u(1) w(1)] fconnect_trans[OF F.fconnect_sym[OF u(2)] w(2)] by simp
      then show ?thesis using u ex F2[OF w(1)] by (simp add: k'_def)
    qed
    also have "k' w = k' z" proof -
      have ex: "\<exists>u \<in> darts G2. cface z u" using w(1) zw by blast
      obtain u where u: "u \<in> darts G2" "cface z u" "u = (SOME u. u \<in> darts G2 \<and> cface z u)"
        using someI_ex[of "\<lambda>u. u \<in> darts G2 \<and> cface z u"] ex by blast
      have "k u = k w" using F1[OF u(1) w(1)] fconnect_trans[OF F.fconnect_sym[OF u(2)] zw] by simp
      then show ?thesis using u ex F2[OF w(1)] by (simp add: k'_def)
    qed
    finally show ?thesis .
  next
    case False
    then show ?thesis using F4[OF yD _ yz] by simp
  qed
  have F6: "k' (e y) \<noteq> k' y" if y2: "y \<in> darts G2" for y
  proof -
    define u where "u = face G2 (edge G2 y)"
    have u2: "u \<in> darts G2" using y2 by (simp add: u_def)
    have a1: "n (f (e y)) = y" by (rule edgeK)
    have a2: "n u = y" using W2.edgeK[of y] hN[OF u2] by (simp add: u_def)
    have "n (f (e y)) = n u" using a1 a2 by simp
    then have fe: "f (e y) = u" by simp
    have yD: "y \<in> D" using y2 inD2 by simp
    have "k' (e y) = k' (f (e y))" using F5[of "e y" "f (e y)"] yD fconnect_step[of f "e y"] by simp
    also have "\<dots> = k u" using F2[OF u2] fe by simp
    also have "k u = k (edge G2 y)" using k y2 by (simp add: coloring_def u_def)
    also have "\<dots> \<noteq> k y" using k y2 by (simp add: coloring_def)
    finally show ?thesis using F2[OF y2] by simp
  qed
  have F7: "k' (e y) \<noteq> k' y" if yD: "y \<in> D" and yx: "y = x \<or> y = n x" for y
  proof (cases "e y \<in> darts G2")
    case True
    have "k' (e (e y)) \<noteq> k' (e y)" by (rule F6[OF True])
    then show ?thesis using plain_eq[OF pG] by simp
  next
    case False
    have eyD: "e y \<in> D" using yD by simp
    have eyx: "e y = x \<or> e y = n x" using False inD2 eyD by auto
    have eyy: "e y \<noteq> y" using plain_neq[OF pG yD] .
    have fe_in: "f (e z) = x \<or> f (e z) = n x" if "z = x \<or> z = n x" for z
    proof -
      have "f (e (n x)) = x" by (rule nodeK)
      moreover have "f (e x) = n x" using nodeK[of "n x"] nnx by simp
      ultimately show ?thesis using that by auto
    qed
    have single: "\<forall>w \<in> darts G2. \<not> cface v w" if vD: "v \<in> D" and vx: "v = x \<or> v = n x"
      and ev: "e v = x \<or> e v = n x" for v
    proof
      fix w assume w2: "w \<in> darts G2"
      have "f v = f (e (e v))" using plain_eq[OF pG] by simp
      then have fv: "f v = x \<or> f v = n x" using fe_in[OF ev] by simp
      have "f v = v"
      proof (rule ccontr)
        assume "f v \<noteq> v"
        then have "f v = n v" using fv vx nnx by auto
        then have "cface v (n v)" using fconnect_step[of f v] by simp
        then show False using no_fn[OF vD] by simp
      qed
      then have "cyc f v = {v}" using F.order_1_iff[of v] F.cyc_order[of v] by auto
      then show "\<not> cface v w" using w2 inD2 vx by (auto simp: F.in_cyc_iff[symmetric])
    qed
    have s1: "\<forall>w \<in> darts G2. \<not> cface y w" using single[OF yD yx eyx] .
    have s2: "\<forall>w \<in> darts G2. \<not> cface (e y) w"
      using single[OF eyD eyx] yx plain_eq[OF pG] by simp
    have "k' y = (if y = x then Color1 else Color0)" using s1 by (simp add: k'_def)
    moreover have "k' (e y) = (if e y = x then Color1 else Color0)" using s2 by (simp add: k'_def)
    moreover have "(y = x) \<noteq> (e y = x)" using yx eyx eyy by auto
    ultimately show ?thesis by auto
  qed
  have "coloring G k'" unfolding coloring_def
  proof (intro conjI ballI)
    fix y assume yD: "y \<in> D"
    show "k' (e y) \<noteq> k' y"
    proof (cases "y \<in> darts G2")
      case True then show ?thesis by (rule F6)
    next
      case False then show ?thesis using F7[OF yD] inD2 yD by auto
    qed
    show "k' (f y) = k' y" using F5[OF yD, of "f y"] fconnect_step[of f y] by simp
  qed
  then show False using ncol by (auto simp: four_colorable_def)
qed

subsection \<open>Mirror images\<close>

lemma cface_mirror: "fconnect (face (mirror G)) x y \<longleftrightarrow> cface x y"
  by (simp add: F.fconnect_inv)

lemma bridgeless_mirror: "bridgeless (mirror G) \<longleftrightarrow> bridgeless G"
proof -
  have m: "bridgeless (mirror G) \<longleftrightarrow> (\<forall>x \<in> D. \<not> cface x (n x))"
  proof -
    have "cface x (f (n x)) \<longleftrightarrow> cface x (n x)" for x by simp
    then show ?thesis by (simp add: bridgeless_def F.fconnect_inv)
  qed
  have "(\<exists>x \<in> D. cface x (n x)) \<longleftrightarrow> (\<exists>y \<in> D. cface y (e y))"
  proof
    assume "\<exists>x \<in> D. cface x (n x)"
    then obtain x where xD: "x \<in> D" and c: "cface x (n x)" by blast
    have "f (e (n x)) = x" by (rule nodeK)
    then have "cface (e (n x)) x" using fconnect_step[of f "e (n x)"] by simp
    then have "cface (n x) (e (n x))" using fconnect_trans[OF F.fconnect_sym[OF c] F.fconnect_sym] by blast
    then show "\<exists>y \<in> D. cface y (e y)" using xD by force
  next
    assume "\<exists>y \<in> D. cface y (e y)"
    then obtain y where yD: "y \<in> D" and c: "cface y (e y)" by blast
    define x where "x = f (e y)"
    have nx: "n x = y" unfolding x_def by (rule edgeK)
    have "cface (e y) x" using fconnect_step[of f "e y"] by (simp add: x_def)
    then have "cface y x" by (rule fconnect_trans[OF c])
    then have "cface x (n x)" using nx F.fconnect_sym by simp
    moreover have "x \<in> D" using yD by (simp add: x_def)
    ultimately show "\<exists>x \<in> D. cface x (n x)" by blast
  qed
  then show ?thesis using m by (auto simp: bridgeless_def)
qed

lemma order_mirror_edge: "order (f \<circ> n) (f y) = order e y"
proof -
  have eq: "f \<circ> n = f \<circ> inv e \<circ> inv f"
    by (simp add: fun_eq_iff inv_edge_apply inv_face_apply nodeK)
  have pow: "((f \<circ> n) ^^ k) (f y) = f (((inv e) ^^ k) y)" for k
    by (induction k) (simp_all add: eq)
  have "cyc (f \<circ> n) (f y) = f ` cyc (inv e) y"
    unfolding cyc_def fconnect_def pow by auto
  moreover have "card (f ` cyc (inv e) y) = card (cyc (inv e) y)"
    by (rule card_image) (rule inj_on_subset[OF F.inj subset_UNIV])
  ultimately have "order (f \<circ> n) (f y) = order (inv e) y" by (simp add: order_def)
  then show ?thesis by (simp add: E.order_inv)
qed

lemma plain_mirror: "plain (mirror G) \<longleftrightarrow> plain G"
proof -
  have "plain (mirror G) \<longleftrightarrow> (\<forall>x \<in> D. order (f \<circ> n) x = 2)" by (simp add: plain_def plainb_def)
  also have "\<dots> \<longleftrightarrow> (\<forall>y \<in> D. order e y = 2)"
  proof
    assume h: "\<forall>x \<in> D. order (f \<circ> n) x = 2"
    show "\<forall>y \<in> D. order e y = 2"
    proof
      fix y assume "y \<in> D"
      then have "f y \<in> D" by simp
      then show "order e y = 2" using h order_mirror_edge by metis
    qed
  next
    assume h: "\<forall>y \<in> D. order e y = 2"
    show "\<forall>x \<in> D. order (f \<circ> n) x = 2"
    proof
      fix x assume xD: "x \<in> D"
      have "x = f (inv f x)" by simp
      moreover have "inv f x \<in> D" using xD by (metis F.closed F.f_inv)
      ultimately show "order (f \<circ> n) x = 2" using h order_mirror_edge by metis
    qed
  qed
  finally show ?thesis by (simp add: plain_def plainb_def)
qed

lemma precubic_mirror: "precubic (mirror G) \<longleftrightarrow> precubic G"
  by (simp add: precubic_def N.order_inv)

lemma planar_bridgeless_plain_precubic_mirror:
  "planar_bridgeless_plain_precubic (mirror G) \<longleftrightarrow> planar_bridgeless_plain_precubic G"
  using hypermap_mirror hypermap_axioms
  by (simp add: planar_bridgeless_plain_precubic_def planar_bridgeless_plain_def
      planar_bridgeless_def planar_mirror bridgeless_mirror plain_mirror precubic_mirror)

lemma minimal_counter_example_mirror:
  assumes "minimal_counter_example G"
  shows "minimal_counter_example (mirror G)"
proof -
  have a: "planar_bridgeless_plain_precubic G" and b: "\<not> four_colorable G"
    and c: "\<forall>G' :: 'a hypermap. planar_bridgeless_plain_precubic G' \<longrightarrow>
         card (darts G') < card D \<longrightarrow> four_colorable G'"
    using assms by (simp_all add: minimal_counter_example_def)
  have "planar_bridgeless_plain_precubic (mirror G)"
    using a planar_bridgeless_plain_precubic_mirror by simp
  moreover have "\<not> four_colorable (mirror G)" using b colorable_mirror by blast
  ultimately show ?thesis using c by (simp add: minimal_counter_example_def)
qed

end

end
