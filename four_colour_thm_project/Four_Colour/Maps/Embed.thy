(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Embed.thy
    The embedding of a configuration into a minimal counterexample (embed.v): from a
    preembedding of the kernel of a C-reducible configuration, derive a contradiction.
    Ported from G. Gonthier's Coq development (embed.v).
*)
theory Embed
  imports Four_Colour_Maps.Embed_pre
begin

lemma arc_mid:
  assumes d: "distinct (a @ u # b @ v # c)"
  shows "arc (a @ u # b @ v # c) u v = u # b"
proof -
  have ua: "u \<notin> set a" using d by auto
  have l1: "lindex (a @ u # b @ v # c) u = length a" using ua by (simp add: lindex_append)
  have r: "rot (length a) (a @ u # b @ v # c) = u # b @ v # c @ a" by (simp add: rot_def)
  have vb: "v \<notin> set (u # b)" using d by auto
  have "lindex (u # b @ v # c @ a) v = Suc (length b)" using vb by (auto simp: lindex_append)
  then show ?thesis using l1 r by (simp add: arc_def)
qed

lemma arc_wrap:
  assumes d: "distinct ((a @ v # c) @ u # b)"
  shows "arc ((a @ v # c) @ u # b) u v = u # b @ a"
proof -
  have ua: "u \<notin> set (a @ v # c)" using d by auto
  have l1: "lindex ((a @ v # c) @ u # b) u = length (a @ v # c)" using ua by (auto simp: lindex_append)
  have r: "rot (length (a @ v # c)) ((a @ v # c) @ u # b) = u # b @ a @ v # c" by (simp add: rot_def)
  have vb: "v \<notin> set (u # b @ a)" using d by auto
  have "lindex (u # b @ a @ v # c) v = Suc (length (b @ a))"
    using vb by (auto simp: lindex_append)
  then show ?thesis using l1 r by (simp add: arc_def)
qed

lemma next_in_last:
  assumes d: "distinct (a # l @ [b])"
  shows "next_in (a # l @ [b]) b = a"
proof -
  have "b \<notin> set (a # l)" using d by auto
  then have "lindex (a # l @ [b]) b = Suc (length l)"
    by (induction l arbitrary: a) (auto split: if_splits)
  then show ?thesis by (simp add: next_in_def)
qed

lemma path_mid: "path r x p \<Longrightarrow> x # p = l1 @ u # v # l2 \<Longrightarrow> r u v"
  by (cases l1) auto

lemma (in hypermap) simple_snoc_cface:
  "simple G (l @ [a]) \<Longrightarrow> cface a b \<Longrightarrow> simple G (l @ [b])"
  using F.cyc_eq[of a b] by (simp add: simple_def)

locale embed_ctx =
  fixes Gm :: "'b hypermap" and Gc :: "'a hypermap" and rc cc :: "'a list" and h :: "'a \<Rightarrow> 'b"
  assumes cexGm: "minimal_counter_example Gm"
    and embedGc: "embeddable Gc rc"
    and embed_h: "preembedding Gc Gm {x \<in> darts Gc. kernel Gc rc x} h"
    and Cred: "C_reducible Gc rc cc"
    and hD: "h ` darts Gc \<subseteq> darts Gm"
begin

sublocale M: birk Gm using cexGm hypermap_cpmap
  by (simp add: birk_def birk_axioms_def minimal_counter_example_def planar_bridgeless_plain_precubic_def
      planar_bridgeless_plain_def planar_bridgeless_def)

lemma geoGc: "hypermap Gc" "planar Gc" "bridgeless Gc" "plain Gc" "quasicubic Gc rc" "connected Gc"
  "ucycle (frel (node Gc)) rc" "set rc \<subseteq> darts Gc" "simple Gc rc"
  using embedGc by (auto simp: embeddable_def scycle_planar_bridgeless_plain_quasicubic_connected_def
      ucycle_plain_quasicubic_connected_def ucycle_plain_quasicubic_def plain_quasicubic_def)

sublocale C: hypermap Gc by (rule geoGc(1))

definition ac :: "'a set" where "ac = {x \<in> darts Gc. kernel Gc rc x}"
definition bc :: "'a set" where "bc = darts Gc - set rc"

lemma ac_bc: "ac \<subseteq> bc" using C.kernel_off_ring by (auto simp: ac_def bc_def)

lemma acF: "x \<in> ac \<longleftrightarrow> face Gc x \<in> ac"
  by (simp add: ac_def kernel_def)

lemma hF: "x \<in> ac \<Longrightarrow> h (face Gc x) = face Gm (h x)"
  using embed_h by (simp add: preembedding_def ac_def)

lemma hFn: "x \<in> ac \<Longrightarrow> order (face Gm) (h x) = order (face Gc) x"
  using embed_h by (simp add: preembedding_def ac_def)

abbreviation hc :: "'a \<Rightarrow> bool" where "hc \<equiv> edge_central Gc Gm h"

lemma hcE: "hc (edge Gc x) \<longleftrightarrow> hc x"
  using edge_central_edge[OF geoGc(1) M.hypermap_axioms geoGc(4) M.plainG] .

lemma h_spoke:
  assumes "edge Gc x \<in> ac" "y \<in> ac"
  shows "\<exists>p. path (rlink Gc) x p \<and> C.cface (lastd x p) y \<and> p \<noteq> [] \<and> simple Gc p \<and>
           (\<forall>z \<in> set p. z \<in> ac \<and> hc z)"
  using C.preembedding_simple_path[OF embed_h[folded ac_def] acF] assms by blast

lemma node_h:
  assumes "y \<in> ac" and "hc (node Gc y)"
  shows "node Gm (h y) = h (node Gc y)"
proof -
  have "face Gc (edge Gc (node Gc y)) \<in> ac" using assms(1) by (simp add: C.nodeK)
  then have eny: "edge Gc (node Gc y) \<in> ac" using acF by blast
  have "h y = h (face Gc (edge Gc (node Gc y)))" by (simp add: C.nodeK)
  also have "\<dots> = face Gm (h (edge Gc (node Gc y)))" by (rule hF[OF eny])
  also have "\<dots> = face Gm (edge Gm (h (node Gc y)))" using assms(2) by (simp add: edge_central_def)
  finally have "h y = face Gm (edge Gm (h (node Gc y)))" .
  then show ?thesis by (simp add: M.edgeK)
qed

lemma both_hc:
  assumes ac: "x \<in> ac" "node Gc x \<in> ac" "node Gc (node Gc x) \<in> ac"
    and n3: "node Gc (node Gc (node Gc x)) = x" and hn: "hc (node Gc x)" "hc (node Gc (node Gc x))"
  shows "hc x"
proof -
  have a: "node Gm (h x) = h (node Gc x)" by (rule node_h[OF ac(1) hn(1)])
  have b: "node Gm (h (node Gc x)) = h (node Gc (node Gc x))" by (rule node_h[OF ac(2) hn(2)])
  have hxD: "h x \<in> darts Gm" using hD ac(1) by (auto simp: ac_def)
  have c: "node Gm (h (node Gc (node Gc x))) = h x"
    using M.nnn[OF hxD] a b by simp
  have fex: "face Gc (edge Gc x) = node Gc (node Gc x)"
    using C.nodeK[of "node Gc (node Gc x)"] n3 by simp
  then have exac: "edge Gc x \<in> ac" using ac(3) acF by metis
  have "face Gm (h (edge Gc x)) = h (node Gc (node Gc x))" using hF[OF exac] fex by simp
  also have "\<dots> = face Gm (edge Gm (node Gm (h (node Gc (node Gc x)))))" by (simp add: M.nodeK)
  also have "\<dots> = face Gm (edge Gm (h x))" using c by simp
  finally show ?thesis by (simp add: edge_central_def)
qed

lemma revsnipC: "scycle Gc (rlink Gc) q \<Longrightarrow> set q \<subseteq> darts Gc \<Longrightarrow> revsnip Gc q"
  using geoGc C.hypermap_axioms
  by (simp add: revsnip_def revsnip_axioms_def snip_ring_def snip_ring_axioms_def)

lemma takeWhile_last:
  assumes "y \<in> set (takeWhile P l)" "y = last l" "distinct l"
  shows "takeWhile P l = l"
proof (rule ccontr)
  assume ne: "takeWhile P l \<noteq> l"
  obtain z rest where dw: "dropWhile P l = z # rest" using ne takeWhile_dropWhile_id[of P l]
    by (cases "dropWhile P l") auto
  have l: "l = takeWhile P l @ z # rest" using dw takeWhile_dropWhile_id[of P l] by simp
  then have "last l = last (z # rest)" by (metis last_appendR list.distinct(1))
  then have "y \<in> set (z # rest)" using assms(2) by (metis last_in_set list.distinct(1))
  then show False using assms(1,3) l by (metis disjoint_iff_not_equal distinct_append)
qed

lemma case_nnx:
  assumes Ur: "scycle Gc (rlink Gc) (x # p)" and xpD: "set (x # p) \<subseteq> darts Gc"
    and phc: "\<forall>y \<in> set p. hc y" and hcnx: "hc (C.n x)" and nhc: "\<not> hc (C.n (C.n x))"
    and n3: "C.n (C.n (C.n x)) = x" and xnx: "C.n x \<noteq> x"
  shows "\<exists>x' p'. \<not> hc x' \<and> scycle Gc (rlink Gc) (x' # p') \<and> set (x' # p') \<subseteq> darts Gc \<and>
     (\<forall>y \<in> set p'. hc y) \<and> snip_ring.diskN Gc (x' # p') \<subseteq> snip_ring.diskN Gc (x # p) \<and>
     x \<notin> snip_ring.diskN Gc (x' # p')"
proof -
  interpret S: revsnip Gc "x # p" by (rule revsnipC[OF Ur xpD])
  have xD: "x \<in> C.D" using xpD by simp
  have brC: "\<not> C.cface y (C.e y)" if "y \<in> C.D" for y using geoGc(3) that by (simp add: bridgeless_def)
  have cyc: "path (rlink Gc) x (p @ [x])" using S.cycle_r by (simp add: cycle_Cons)
  have simxp: "simple Gc (x # p)" by (rule S.simple_r)
  have pne: "p \<noteq> []"
  proof
    assume "p = []"
    then have "rlink Gc x x" using cyc by simp
    then have "C.cface x (C.e x)" by (simp add: rlink_def C.F.fconnect_commute)
    then show False using brC[OF xD] by simp
  qed
  define enx where "enx = C.e (C.n x)"
  define ennx where "ennx = C.e (C.n (C.n x))"
  define p1 where "p1 = p @ [enx]"
  have eeC: "C.e (C.e y) = y" for y using geoGc(4) by (rule C.plain_eq)
  have enxx: "C.cface enx x" using fconnect_step[of "face Gc" enx] by (simp add: enx_def C.nodeK)
  have fex: "C.f (C.e x) = C.n (C.n x)" using C.nodeK[of "C.n (C.n x)"] n3 by simp
  have ennx_nx: "C.cface ennx (C.n x)" using fconnect_step[of "face Gc" ennx] by (simp add: ennx_def C.nodeK)
  have e_ennx: "C.e ennx = C.n (C.n x)" by (simp add: ennx_def eeC)
  have rl_eq: "rlink Gc ennx y \<longleftrightarrow> rlink Gc x y" for y
  proof -
    have a: "C.cface (C.e x) (C.n (C.n x))" using fconnect_step[of "face Gc" "C.e x"] fex by simp
    show ?thesis unfolding rlink_def e_ennx
      using fconnect_trans[OF a, of y] fconnect_trans[OF C.F.fconnect_sym[OF a], of y] by blast
  qed
  have pp: "path (rlink Gc) x p" and lastx: "rlink Gc (lastd x p) x" using cyc by simp_all
  have xp1: "path (rlink Gc) x p1"
    using pp lastx C.rlink_cface[OF C.F.fconnect_sym[OF enxx]] by (simp add: p1_def)
  have ep1: "path (rlink Gc) ennx p1"
  proof -
    obtain a l where p1c: "p1 = a # l" by (cases p1) (auto simp: p1_def)
    then show ?thesis using xp1 rl_eq[of a] by simp
  qed
  have simC: "a = b" if "a \<in> set (x # p)" "b \<in> set (x # p)" "C.cface a b" for a b
    by (rule S.r_cface[OF that])
  have dxp: "distinct (x # p)" by (rule S.distinct_r)
  have enx_nb: "\<not> fband Gc p enx"
  proof
    assume "fband Gc p enx"
    then obtain y where yp: "y \<in> set p" and ey: "C.cface enx y" by (auto simp: fband_def)
    have "C.cface x y" by (rule fconnect_trans[OF C.F.fconnect_sym[OF enxx] ey])
    then have "x = y" using simC yp by simp
    then show False using dxp yp by simp
  qed
  have simp_p: "simple Gc p" using simxp by (simp add: C.simple_Cons)
  have sn: "simple Gc []" by (simp add: simple_def)
  have simp1: "simple Gc p1" using simp_p enx_nb sn by (simp add: p1_def C.simple_append C.simple_Cons fband_def)
  have dp1: "distinct p1" and sim1: "\<And>a b. a \<in> set p1 \<Longrightarrow> b \<in> set p1 \<Longrightarrow> C.cface a b \<Longrightarrow> a = b"
    using simp1 C.simple_iff by blast+
  define T where "T = takeWhile (\<lambda>y. \<not> C.cface ennx y) p1"
  define R where "R = dropWhile (\<lambda>y. \<not> C.cface ennx y) p1"
  have p1TR: "p1 = T @ R" by (simp add: T_def R_def)
  have Tnb: "\<forall>y \<in> set T. \<not> C.cface ennx y" by (auto simp: T_def dest: set_takeWhileD)
  have eT: "path (rlink Gc) ennx T" using ep1 p1TR by (metis path_append)
  have closing: "rlink Gc (lastd ennx T) ennx"
  proof (cases R)
    case Nil
    then have "T = p1" using p1TR by simp
    then have "lastd ennx T = enx" by (simp add: p1_def)
    moreover have "rlink Gc enx ennx"
      using C.F.fconnect_sym[OF ennx_nx] by (simp add: rlink_def enx_def eeC)
    ultimately show ?thesis by simp
  next
    case (Cons z rest)
    have zF: "C.cface ennx z" using Cons by (simp add: R_def dropWhile_eq_Cons_conv)
    have "path (rlink Gc) ennx (T @ z # rest)" using ep1 p1TR Cons by simp
    then have "rlink Gc (lastd ennx T) z" by simp
    then show ?thesis using C.rlink_cface[OF C.F.fconnect_sym[OF zF]] by simp
  qed
  have simT: "simple Gc T" using simp1 p1TR by (simp add: C.simple_append)
  have Uq: "scycle Gc (rlink Gc) (ennx # T)"
    unfolding scycle_def cycle_Cons
    using eT closing simT Tnb by (simp add: C.simple_Cons fband_def C.F.fconnect_commute)
  have nnxD: "C.n (C.n x) \<in> C.D" using xD by simp
  have Tne: "T \<noteq> []"
  proof
    assume "T = []"
    then have "rlink Gc ennx ennx" using closing by simp
    then have "C.cface (C.n (C.n x)) ennx" by (simp add: rlink_def e_ennx)
    then show False using brC[OF nnxD] by (simp add: ennx_def)
  qed
  have Tsub: "set T \<subseteq> set p1" using p1TR by auto
  have Thc: "\<forall>y \<in> set T. hc y"
  proof
    fix y assume "y \<in> set T"
    then have "y \<in> set p \<or> y = enx" using Tsub by (auto simp: p1_def)
    then show "hc y" using phc hcnx hcE[of "C.n x"] by (auto simp: enx_def)
  qed
  have prq: "proper_ring Gc (ennx # T)"
  proof (cases T)
    case (Cons t1 T')
    show ?thesis
    proof (cases T')
      case Nil
      have "hc t1" using Thc Cons by simp
      then have "t1 \<noteq> C.n (C.n x)" using nhc by blast
      then show ?thesis using Cons Nil by (simp add: e_ennx)
    qed (simp add: Cons)
  qed (use Tne in simp)
  have p1D: "set p1 \<subseteq> C.D" using xpD xD by (auto simp: p1_def enx_def)
  have qD: "set (ennx # T) \<subseteq> C.D" using Tsub p1D xD by (auto simp: ennx_def)
  interpret Q: revsnip Gc "ennx # T" by (rule revsnipC[OF Uq qD])
  have C1: "x \<notin> Q.diskN"
  proof
    assume "x \<in> Q.diskN"
    then have "C.n x \<in> Q.diskN" using Q.diskN_node[OF xD] by simp
    then have "C.n (C.n x) \<in> Q.diskN" using Q.diskN_node[of "C.n x"] xD by simp
    then show False using Q.diskN_edge_ring[OF prq, of ennx] e_ennx by simp
  qed
  have xN: "x \<in> S.diskN" by (rule S.r_diskN) simp
  have nxN: "C.n x \<in> S.diskN" using S.diskN_node[OF xD] xN by simp
  have nnxN: "C.n (C.n x) \<in> S.diskN" using S.diskN_node[of "C.n x"] xD nxN by simp
  have nnx_off: "C.n (C.n x) \<notin> set (x # p)"
  proof -
    have "C.n (C.n x) \<noteq> x" using n3 xnx by (metis)
    moreover have "C.n (C.n x) \<notin> set p" using phc nhc by blast
    ultimately show ?thesis by simp
  qed
  have a: "z \<in> S.diskN" if zq: "z \<in> set (ennx # T)" for z
  proof (cases "z = ennx")
    case True
    have "C.n (C.n x) \<in> S.diskE" using nnxN nnx_off by (simp add: S.diskE_def)
    then have "ennx \<in> S.diskE" using S.diskE_edge[OF nnxD] by (simp add: ennx_def)
    then show ?thesis using True by (simp add: S.diskE_def)
  next
    case False
    then have zT: "z \<in> set T" using zq by simp
    show ?thesis
    proof (cases "z = enx")
      case False
      then have "z \<in> set p" using zT Tsub by (auto simp: p1_def)
      then show ?thesis by (intro S.r_diskN) simp
    next
      case True
      have "T = p1" unfolding T_def
      proof (rule takeWhile_last[of z])
        show "z \<in> set (takeWhile (\<lambda>y. \<not> C.cface ennx y) p1)" using zT by (simp add: T_def)
        show "z = last p1" using True by (simp add: p1_def)
        show "distinct p1" by (rule dp1)
      qed
      then have nob: "\<forall>y \<in> set p1. \<not> C.cface ennx y" using Tnb by simp
      have "C.n x \<notin> set p" using nob ennx_nx by (auto simp: p1_def)
      then have "C.n x \<notin> set (x # p)" using xnx by simp
      then have "C.n x \<in> S.diskE" using nxN by (simp add: S.diskE_def)
      then have "enx \<in> S.diskE" using S.diskE_edge[of "C.n x"] xD by (simp add: enx_def)
      then show ?thesis using True by (simp add: S.diskE_def)
    qed
  qed
  have b: "y \<in> set (ennx # T)" if yxp: "y \<in> set (x # p)" and yQ: "y \<in> Q.diskN" for y
  proof (rule ccontr)
    assume nyq: "y \<notin> set (ennx # T)"
    have yx: "y \<noteq> x" using yQ C1 by blast
    then have yp: "y \<in> set p" using yxp by simp
    have "y \<in> set p1" using yp by (simp add: p1_def)
    then have yR: "y \<in> set R" using nyq p1TR by (metis Un_iff list.set_intros(2) set_append)
    obtain l1 l2 where Rs: "R = l1 @ y # l2" using split_list[OF yR] by blast
    have p1s: "p1 = T @ l1 @ y # l2" using p1TR Rs by simp
    have yl2: "path (rlink Gc) y l2" using ep1 p1s by (simp add: path_append)
    have yne: "y \<noteq> enx" using yp enx_nb C.fband_ring by blast
    have l2ne: "l2 \<noteq> []"
    proof
      assume "l2 = []"
      then have "last p1 = y" using p1s by simp
      then show False using yne by (simp add: p1_def)
    qed
    have "last p1 = last l2" using p1s l2ne by simp
    then have lastl2: "last l2 = enx" by (simp add: p1_def)
    obtain z rest where Rz: "R = z # rest" using Rs by (cases "l1 @ y # l2") auto
    have zF: "C.cface ennx z" using Rz by (simp add: R_def dropWhile_eq_Cons_conv)
    have nbw: "\<not> fband Gc (ennx # T) w" if wl: "w \<in> set l2" for w
    proof
      assume "fband Gc (ennx # T) w"
      then consider "C.cface w ennx" | t where "t \<in> set T" "C.cface w t" by (auto simp: fband_def)
      then show False
      proof cases
        case 1
        have "C.cface w z" by (rule fconnect_trans[OF 1 zF])
        moreover have "w \<in> set p1" using wl p1s by simp
        moreover have "z \<in> set p1" using p1TR Rz by simp
        ultimately have "w = z" using sim1 by blast
        moreover have "z \<notin> set l2"
        proof (cases l1)
          case Nil then have "z = y" using Rs Rz by simp
          then show ?thesis using dp1 p1s by auto
        next
          case (Cons z' l1') then have "z = z'" using Rs Rz by simp
          then show ?thesis using dp1 p1s Cons by auto
        qed
        ultimately show False using wl by simp
      next
        case (2 t)
        have "w \<in> set p1" "t \<in> set p1" using wl p1s 2(1) by auto
        then have "w = t" using sim1 2(2) by blast
        then show False using dp1 p1s 2(1) wl by auto
      qed
    qed
    have "\<forall>w \<in> set l2. w \<in> Q.diskN" by (rule Q.walk_diskN[OF yl2 yQ]) (use nbw in blast)
    then have enxN: "enx \<in> Q.diskN" using lastl2 l2ne by (metis last_in_set)
    have "\<not> fband Gc (ennx # T) enx" using nbw lastl2 l2ne by (metis last_in_set)
    then have "enx \<in> Q.diskF" using enxN by (simp add: Q.diskF_def)
    then have "C.f enx \<in> Q.diskF" by (rule Q.diskF_face)
    then have "x \<in> Q.diskN" by (simp add: enx_def C.nodeK Q.diskF_def)
    then show False using C1 by simp
  qed
  have sub: "Q.diskN \<subseteq> S.diskN"
    by (rule disk_sub[OF Q.snip_ring_axioms S.snip_ring_axioms a b])
  have "\<not> hc ennx" using nhc hcE[of "C.n (C.n x)"] by (simp add: ennx_def)
  then show ?thesis using Uq qD Thc sub C1 by blast
qed

lemma case_nx:
  assumes Ur: "scycle Gc (rlink Gc) (x # p)" and xpD: "set (x # p) \<subseteq> darts Gc"
    and phc: "\<forall>y \<in> set p. hc y" and nhc: "\<not> hc (C.n x)"
    and dNac: "snip_ring.diskN Gc (x # p) \<subseteq> ac" and xnx: "C.n x \<noteq> x"
  shows "\<exists>x' p'. \<not> hc x' \<and> scycle Gc (rlink Gc) (x' # p') \<and> set (x' # p') \<subseteq> darts Gc \<and>
     (\<forall>y \<in> set p'. hc y) \<and> snip_ring.diskN Gc (x' # p') \<subseteq> snip_ring.diskN Gc (x # p) \<and>
     x \<notin> snip_ring.diskN Gc (x' # p')"
proof -
  interpret S: revsnip Gc "x # p" by (rule revsnipC[OF Ur xpD])
  have xD: "x \<in> C.D" using xpD by simp
  have brC: "\<not> C.cface y (C.e y)" if "y \<in> C.D" for y using geoGc(3) that by (simp add: bridgeless_def)
  have eeC: "C.e (C.e y) = y" for y using geoGc(4) by (rule C.plain_eq)
  have cyc: "path (rlink Gc) x (p @ [x])" using S.cycle_r by (simp add: cycle_Cons)
  have simxp: "simple Gc (x # p)" by (rule S.simple_r)
  have pne: "p \<noteq> []"
  proof
    assume "p = []"
    then have "rlink Gc x x" using cyc by simp
    then have "C.cface x (C.e x)" by (simp add: rlink_def C.F.fconnect_commute)
    then show False using brC[OF xD] by simp
  qed
  define enx where "enx = C.e (C.n x)"
  define p1 where "p1 = p @ [enx]"
  have enxx: "C.cface enx x" using fconnect_step[of "face Gc" enx] by (simp add: enx_def C.nodeK)
  have pp: "path (rlink Gc) x p" and lastx: "rlink Gc (lastd x p) x" using cyc by simp_all
  have xp1: "path (rlink Gc) x p1"
    using pp lastx C.rlink_cface[OF C.F.fconnect_sym[OF enxx]] by (simp add: p1_def)
  have simC: "a = b" if "a \<in> set (x # p)" "b \<in> set (x # p)" "C.cface a b" for a b
    by (rule S.r_cface[OF that])
  have dxp: "distinct (x # p)" by (rule S.distinct_r)
  have enx_nb: "\<not> fband Gc p enx"
  proof
    assume "fband Gc p enx"
    then obtain y where yp: "y \<in> set p" and ey: "C.cface enx y" by (auto simp: fband_def)
    have "C.cface x y" by (rule fconnect_trans[OF C.F.fconnect_sym[OF enxx] ey])
    then have "x = y" using simC yp by simp
    then show False using dxp yp by simp
  qed
  have simp_p: "simple Gc p" using simxp by (simp add: C.simple_Cons)
  have sn: "simple Gc []" by (simp add: simple_def)
  have simp1: "simple Gc p1" using simp_p enx_nb sn by (simp add: p1_def C.simple_append C.simple_Cons fband_def)
  have dp1: "distinct p1" and sim1: "\<And>a b. a \<in> set p1 \<Longrightarrow> b \<in> set p1 \<Longrightarrow> C.cface a b \<Longrightarrow> a = b"
    using simp1 C.simple_iff by blast+
  have nxD: "C.n x \<in> C.D" using xD by simp
  have xN: "x \<in> S.diskN" by (rule S.r_diskN) simp
  have nxN: "C.n x \<in> S.diskN" using S.diskN_node[OF xD] xN by simp
  have nx_off: "C.n x \<notin> set (x # p)" using phc nhc xnx by auto
  have nxE: "C.n x \<in> S.diskE" using nxN nx_off by (simp add: S.diskE_def)
  have enxE: "enx \<in> S.diskE" using S.diskE_edge[OF nxD] nxE by (simp add: enx_def)
  have enxN: "enx \<in> S.diskN" using enxE by (simp add: S.diskE_def)
  have nxac: "C.n x \<in> ac" and enxac: "enx \<in> ac" using dNac nxN enxN by auto
  have eenx: "C.e enx = C.n x" by (simp add: enx_def eeC)
  obtain q1 where q1: "path (rlink Gc) enx q1" "C.cface (lastd enx q1) enx" "q1 \<noteq> []" "simple Gc q1"
    "\<forall>z \<in> set q1. z \<in> ac \<and> hc z"
    using h_spoke[of enx enx] nxac enxac eenx by auto
  define q2 where "q2 = takeWhile (\<lambda>z. \<not> fband Gc p1 z) q1"
  define R where "R = dropWhile (\<lambda>z. \<not> fband Gc p1 z) q1"
  have q1s: "q1 = q2 @ R" by (simp add: q2_def R_def)
  have q2nb: "\<forall>z \<in> set q2. \<not> fband Gc p1 z" by (auto simp: q2_def dest: set_takeWhileD)
  have Rne: "R \<noteq> []"
  proof
    assume "R = []"
    then have "q2 = q1" using q1s by simp
    moreover have "fband Gc p1 (lastd enx q1)" using q1(2) by (auto simp: fband_def p1_def)
    moreover have "lastd enx q1 \<in> set q1" using q1(3) by simp
    ultimately show False using q2nb by simp
  qed
  obtain w R' where Rw: "R = w # R'" using Rne by (cases R) auto
  have wF: "fband Gc p1 w" using Rw by (simp add: R_def dropWhile_eq_Cons_conv)
  obtain y where yp1: "y \<in> set p1" and wy: "C.cface w y" using wF by (auto simp: fband_def)
  obtain p2 p3 where p1s: "p1 = p2 @ y # p3" using split_list[OF yp1] by blast
  define B where "B = butlast (y # p3)"
  have p1B: "p1 = p2 @ B @ [enx]"
  proof -
    have "last (y # p3) = enx" using p1s by (metis last_appendR last_snoc list.distinct(1) p1_def)
    then have "y # p3 = B @ [enx]" by (simp add: B_def) (metis append_butlast_last_id list.distinct(1))
    then show ?thesis using p1s by simp
  qed
  define q where "q = enx # q2 @ B"
  have Bp3: "B @ [enx] = y # p3" using p1B p1s by simp
  have pB: "p = p2 @ B" using p1B by (simp add: p1_def)
  have eq2: "path (rlink Gc) enx q2" and lw: "rlink Gc (lastd enx q2) w"
    using q1(1) q1s Rw by simp_all
  have ly: "rlink Gc (lastd enx q2) y" using lw C.rlink_cface[OF wy] by simp
  have yp3: "path (rlink Gc) y p3" using xp1 p1s by simp
  have cycq: "cycle (rlink Gc) q"
    unfolding q_def cycle_Cons using eq2 ly yp3 Bp3 by simp
  have simq2: "simple Gc q2" using q1(4) q1s by (simp add: C.simple_append)
  have simB: "simple Gc B" using simp1 p1B by (simp add: C.simple_append)
  have Bsub: "set B \<subseteq> set p1" using p1B by auto
  have dB: "enx \<notin> set B" using dp1 p1B by simp
  have nbq2: "\<not> fband Gc q2 b" if "b \<in> set p1" for b
  proof
    assume "fband Gc q2 b"
    then obtain z where zq: "z \<in> set q2" and bz: "C.cface b z" by (auto simp: fband_def)
    have "fband Gc p1 z" using that C.F.fconnect_sym[OF bz] by (auto simp: fband_def)
    then show False using q2nb zq by blast
  qed
  have enxp1: "enx \<in> set p1" by (simp add: p1_def)
  have nbB: "\<not> fband Gc B enx"
  proof
    assume "fband Gc B enx"
    then obtain b where "b \<in> set B" "C.cface enx b" by (auto simp: fband_def)
    then show False using sim1[OF enxp1] Bsub dB by blast
  qed
  have simq: "simple Gc q"
    unfolding q_def using simq2 simB nbq2 Bsub nbB nbq2[OF enxp1]
    by (auto simp: C.simple_Cons C.simple_append C.fband_append)
  have Uq: "scycle Gc (rlink Gc) q" using cycq simq by (simp add: scycle_def)
  have q2sub: "set q2 \<subseteq> set q1" using q1s by auto
  have q3hc: "\<forall>z \<in> set (q2 @ B). hc z" using q1(5) q2sub pB phc by auto
  have acD: "ac \<subseteq> C.D" by (auto simp: ac_def)
  have qD: "set q \<subseteq> C.D" using q1(5) q2sub acD pB xpD enxac by (auto simp: q_def)
  have q3ne: "q2 @ B \<noteq> []"
  proof
    assume "q2 @ B = []"
    then have "rlink Gc enx enx" using cycq by (simp add: q_def cycle_Cons)
    then have "C.cface (C.n x) (C.e (C.n x))" by (simp add: rlink_def eenx enx_def)
    then show False using brC[OF nxD] by simp
  qed
  have prq: "proper_ring Gc q"
  proof (cases "q2 @ B")
    case (Cons t1 T')
    show ?thesis
    proof (cases T')
      case Nil
      have "hc t1" using q3hc Cons by simp
      then have "t1 \<noteq> C.n x" using nhc by blast
      then show ?thesis using Cons Nil by (simp add: q_def eenx)
    qed (simp add: q_def Cons)
  qed (use q3ne in simp)
  interpret Q: revsnip Gc q by (rule revsnipC[OF Uq qD])
  have C1: "x \<notin> Q.diskN"
  proof
    assume "x \<in> Q.diskN"
    then have "C.n x \<in> Q.diskN" using Q.diskN_node[OF xD] by simp
    then show False using Q.diskN_edge_ring[OF prq, of enx] eenx by (simp add: q_def)
  qed
  have a: "z \<in> S.diskN" if zq: "z \<in> set q" for z
  proof -
    consider "z = enx" | "z \<in> set q2" | "z \<in> set B" using zq by (auto simp: q_def)
    then show ?thesis
    proof cases
      case 1 then show ?thesis using enxN by simp
    next
      case 2
      have nbx: "\<not> fband Gc (x # p) v" if "v \<in> set q2" for v
      proof
        assume "fband Gc (x # p) v"
        then obtain t where t: "t \<in> set (x # p)" and vt: "C.cface v t" by (auto simp: fband_def)
        have "fband Gc p1 v"
        proof (cases "t = x")
          case True
          then have "C.cface v enx" using vt C.F.fconnect_sym[OF enxx] fconnect_trans by metis
          then show ?thesis by (auto simp: fband_def p1_def)
        next
          case False then show ?thesis using t vt by (auto simp: fband_def p1_def)
        qed
        then show False using q2nb that by blast
      qed
      have "\<forall>v \<in> set q2. v \<in> S.diskN" by (rule S.walk_diskN[OF eq2 enxN]) (use nbx in blast)
      then show ?thesis using 2 by blast
    next
      case 3 then show ?thesis using pB by (intro S.r_diskN) auto
    qed
  qed
  have b: "y' \<in> set q" if y'xp: "y' \<in> set (x # p)" and y'Q: "y' \<in> Q.diskN" for y'
  proof (rule ccontr)
    assume nq: "y' \<notin> set q"
    have "y' \<noteq> x" using y'Q C1 by blast
    then have y'p2: "y' \<in> set p2" using y'xp nq pB by (auto simp: q_def)
    obtain l1 l2 where p2s: "p2 = l1 @ y' # l2" using split_list[OF y'p2] by blast
    have pth: "path (rlink Gc) x (l1 @ [y'])" using xp1 p1s p2s by simp
    have nbw: "\<forall>v \<in> set (l1 @ [y']). \<not> fband Gc q v"
    proof
      fix v assume v: "v \<in> set (l1 @ [y'])"
      then have vp2: "v \<in> set p2" using p2s by auto
      then have vp1: "v \<in> set p1" using p1s by simp
      show "\<not> fband Gc q v"
      proof
        assume "fband Gc q v"
        then consider "C.cface v enx" | z where "z \<in> set q2" "C.cface v z" | b where "b \<in> set B" "C.cface v b"
          by (auto simp: fband_def q_def)
        then show False
        proof cases
          case 1 then have "v = enx" using sim1[OF vp1 enxp1] by simp
          then show False using dp1 p1B vp2 by auto
        next
          case (2 z) then show False using nbq2[OF vp1] by (auto simp: fband_def)
        next
          case (3 b) then have "v = b" using sim1[OF vp1] Bsub by blast
          then show False using dp1 p1B vp2 3(1) by auto
        qed
      qed
    qed
    have "x \<in> Q.diskN" by (rule Q.walk_back[OF pth _ nbw xD]) (use y'Q in simp)
    then show False using C1 by simp
  qed
  have sub: "Q.diskN \<subseteq> S.diskN"
    by (rule disk_sub[OF Q.snip_ring_axioms S.snip_ring_axioms a b])
  have "\<not> hc enx" using nhc hcE[of "C.n x"] by (simp add: enx_def)
  then show ?thesis using Uq qD q3hc sub C1 by (intro exI[of _ enx] exI[of _ "q2 @ B"]) (simp add: q_def)
qed

lemma ac_cubic:
  assumes "x \<in> ac"
  shows "C.n (C.n (C.n x)) = x" and "C.n x \<noteq> x"
proof -
  have xD: "x \<in> C.D" and xr: "x \<notin> set rc" using assms ac_bc by (auto simp: ac_def bc_def)
  show "C.n (C.n (C.n x)) = x" by (rule C.quasicubic_eq[OF geoGc(5) xD xr])
  have "order (C.n) x = 3" using geoGc(5) xD xr by (simp add: quasicubic_def cubicb_def)
  then show "C.n x \<noteq> x" using C.N.order_1_iff[of x] by auto
qed

lemma no_hc_ring:
  "card (snip_ring.diskN Gc (x # p)) < m \<Longrightarrow> \<not> hc x \<Longrightarrow> scycle Gc (rlink Gc) (x # p) \<Longrightarrow>
   set (x # p) \<subseteq> darts Gc \<Longrightarrow> (\<forall>y \<in> set p. hc y) \<Longrightarrow> snip_ring.diskN Gc (x # p) \<subseteq> ac \<Longrightarrow> False"
proof (induction m arbitrary: x p)
  case 0 then show ?case by simp
next
  case (Suc m)
  interpret S: revsnip Gc "x # p" by (rule revsnipC[OF Suc.prems(3,4)])
  have xD: "x \<in> C.D" using Suc.prems(4) by simp
  have xN: "x \<in> S.diskN" by (rule S.r_diskN) simp
  have nxN: "C.n x \<in> S.diskN" using S.diskN_node[OF xD] xN by simp
  have nnxN: "C.n (C.n x) \<in> S.diskN" using S.diskN_node[of "C.n x"] xD nxN by simp
  have xac: "x \<in> ac" "C.n x \<in> ac" "C.n (C.n x) \<in> ac" using Suc.prems(6) xN nxN nnxN by auto
  note cub = ac_cubic[OF xac(1)]
  have fin: "finite S.diskN" using S.diskN_D C.finite_darts finite_subset by blast
  have step: False if ex: "\<exists>x' p'. \<not> hc x' \<and> scycle Gc (rlink Gc) (x' # p') \<and> set (x' # p') \<subseteq> darts Gc \<and>
     (\<forall>y \<in> set p'. hc y) \<and> snip_ring.diskN Gc (x' # p') \<subseteq> S.diskN \<and> x \<notin> snip_ring.diskN Gc (x' # p')"
  proof -
    obtain x' p' where o: "\<not> hc x'" "scycle Gc (rlink Gc) (x' # p')" "set (x' # p') \<subseteq> darts Gc"
      "\<forall>y \<in> set p'. hc y" "snip_ring.diskN Gc (x' # p') \<subseteq> S.diskN" "x \<notin> snip_ring.diskN Gc (x' # p')"
      using ex by blast
    have "card (snip_ring.diskN Gc (x' # p')) < card S.diskN"
      using o(5,6) xN fin by (intro psubset_card_mono) auto
    then have "card (snip_ring.diskN Gc (x' # p')) < m" using Suc.prems(1) by simp
    then show False using Suc.IH o Suc.prems(6) by blast
  qed
  show False
  proof (cases "hc (C.n x)")
    case True
    show ?thesis
    proof (cases "hc (C.n (C.n x))")
      case True
      then show ?thesis using both_hc[OF xac cub(1)] \<open>hc (C.n x)\<close> Suc.prems(2) by blast
    next
      case False
      show ?thesis by (rule step[OF case_nnx[OF Suc.prems(3,4,5) \<open>hc (C.n x)\<close> False cub]])
    qed
  next
    case False
    show ?thesis by (rule step[OF case_nx[OF Suc.prems(3,4,5) False Suc.prems(6) cub(2)]])
  qed
qed

lemma ac_cface: "y \<in> ac \<Longrightarrow> C.cface y z \<Longrightarrow> z \<in> ac"
proof -
  assume y: "y \<in> ac" and yz: "C.cface y z"
  have "z \<in> C.D" using y yz C.F.fconnect_in_D by (auto simp: ac_def)
  moreover have "\<not> fband Gc rc z" using y C.fband_cface[OF yz] by (simp add: ac_def kernel_def)
  ultimately show ?thesis by (simp add: ac_def kernel_def)
qed

lemma rc_node_conn: "z \<in> set rc \<Longrightarrow> z' \<in> set rc \<Longrightarrow> C.cnode z z'"
proof -
  assume z: "z \<in> set rc" and z': "z' \<in> set rc"
  have cyc: "cycle (frel (C.n)) rc" and d: "distinct rc" using geoGc(7) by (simp_all add: ucycle_def)
  have "\<forall>i < length rc. C.cnode (rc ! 0) (rc ! i)"
  proof (intro allI impI)
    fix i assume "i < length rc"
    then show "C.cnode (rc ! 0) (rc ! i)"
    proof (induction i)
      case 0 then show ?case by simp
    next
      case (Suc i)
      have "C.n (rc ! i) = rc ! (Suc i mod length rc)" using cyc Suc.prems by (simp add: cycle_nth)
      then have "C.n (rc ! i) = rc ! Suc i" using Suc.prems by simp
      then show ?case using Suc fconnect_trans[OF _ fconnect_step[of "C.n" "rc ! i"]] by simp
    qed
  qed
  then show ?thesis using z z' C.N.fconnect_sym fconnect_trans by (metis in_set_conv_nth)
qed

lemma embed_functor_ring:
  assumes x: "x \<in> ac" and nh: "\<not> hc x" and Ur: "scycle Gc (rlink Gc) (x # p)"
    and pac: "\<forall>y \<in> set p. y \<in> ac \<and> hc y"
  shows False
proof -
  have acD: "ac \<subseteq> C.D" by (auto simp: ac_def)
  have xpD: "set (x # p) \<subseteq> C.D" using x pac acD by auto
  interpret S: revsnip Gc "x # p" by (rule revsnipC[OF Ur xpD])
  have phc: "\<forall>y \<in> set p. hc y" using pac by blast
  show False
  proof (cases "\<exists>z \<in> set rc. z \<in> S.diskF")
    case False
    have "S.diskN \<subseteq> ac"
    proof
      fix y assume yN: "y \<in> S.diskN"
      have yD: "y \<in> C.D" using yN S.diskN_D by blast
      show "y \<in> ac"
      proof (cases "fband Gc (x # p) y")
        case True
        then obtain t where "t \<in> set (x # p)" "C.cface y t" by (auto simp: fband_def)
        then show ?thesis using ac_cface[of t y] x pac C.F.fconnect_sym by auto
      next
        case nb: False
        then have yF: "y \<in> S.diskF" using yN by (simp add: S.diskF_def)
        have "\<not> fband Gc rc y"
        proof
          assume "fband Gc rc y"
          then obtain z where "z \<in> set rc" "C.cface y z" by (auto simp: fband_def)
          then show False using S.diskF_cface[OF yF] False by blast
        qed
        then show ?thesis using yD by (simp add: ac_def kernel_def)
      qed
    qed
    then show False using no_hc_ring[OF _ nh Ur xpD phc] by blast
  next
    case True
    then obtain z where zr: "z \<in> set rc" and zF: "z \<in> S.diskF" by blast
    have pne: "p \<noteq> []"
    proof
      assume "p = []"
      then have "rlink Gc x x" using S.cycle_r by (simp add: cycle_Cons)
      then show False using geoGc(3) xpD by (simp add: rlink_def bridgeless_def C.F.fconnect_commute)
    qed
    have prxp: "proper_ring Gc (x # p)"
    proof (cases p rule: remdups_adj.cases)
      case (2 x2)
      have "hc x2" using phc 2 by simp
      then have "C.e x \<noteq> x2" using nh hcE[of x] by auto
      then show ?thesis using 2 by simp
    qed (use pne in simp_all)
    define q0 where "q0 = rot 1 (x # p)"
    have q0: "q0 = p @ [x]" by (simp add: q0_def rot_def)
    have Uq0: "scycle Gc (rlink Gc) q0" and q0D: "set q0 \<subseteq> C.D"
      using S.snip_ring_rot[of 1] xpD by (auto simp: q0_def snip_ring_def snip_ring_axioms_def)
    interpret Q0: revsnip Gc q0 by (rule revsnipC[OF Uq0 q0D])
    have prq0: "proper_ring Gc q0" unfolding q0_def by (simp only: C.proper_ring_rot[OF geoGc(4)] prxp)
    have rr: "rev_ring Gc q0 = C.e x # rev_ring Gc p" by (simp add: q0 rev_ring_def)
    have Urr: "scycle Gc (rlink Gc) (C.e x # rev_ring Gc p)" using Q0.scycle_rev_ring rr by simp
    have rrD: "set (C.e x # rev_ring Gc p) \<subseteq> C.D" using Q0.rr_D rr by simp
    have nhe: "\<not> hc (C.e x)" using nh hcE by simp
    have rhc: "\<forall>y \<in> set (rev_ring Gc p). hc y" using phc hcE by (auto simp: rev_ring_def)
    have dq0: "Q0.diskN = S.diskN" using S.rot_disks(1)[of 1] by (simp add: q0_def)
    have zN: "z \<in> S.diskN" using zF by (simp add: S.diskF_def)
    have "Q0.R.diskN \<subseteq> ac"
    proof
      fix y assume yR: "y \<in> Q0.R.diskN"
      have yD: "y \<in> C.D" using yR Q0.R.diskN_D by blast
      have yN: "y \<notin> S.diskN" using Q0.diskN_rev_ring[OF prq0 yD] yR dq0 by simp
      have "\<not> fband Gc rc y"
      proof
        assume "fband Gc rc y"
        then obtain z' where z'r: "z' \<in> set rc" and yz': "C.cface y z'" by (auto simp: fband_def)
        have "C.cnode z z'" by (rule rc_node_conn[OF zr z'r])
        then have z'N: "z' \<in> S.diskN"
        proof (induction rule: fconnect_induct)
          case refl then show ?case by (rule zN)
        next
          case (step w)
          have wD: "w \<in> C.D" using step.IH S.diskN_D by blast
          then show ?case using S.diskN_node[OF wD] step.IH by simp
        qed
        show False
        proof (cases "fband Gc (x # p) z'")
          case True
          then obtain t where "t \<in> set (x # p)" "C.cface z' t" by (auto simp: fband_def)
          then have "z' \<in> ac" using ac_cface[of t z'] x pac C.F.fconnect_sym by auto
          then show False using z'r C.fband_ring[of z' rc] by (simp add: ac_def kernel_def)
        next
          case False
          then have "z' \<in> S.diskF" using z'N by (simp add: S.diskF_def)
          then have "y \<in> S.diskF" using S.diskF_cface C.F.fconnect_sym[OF yz'] by blast
          then show False using yN by (simp add: S.diskF_def)
        qed
      qed
      then show "y \<in> ac" using yD by (simp add: ac_def kernel_def)
    qed
    then have "snip_ring.diskN Gc (C.e x # rev_ring Gc p) \<subseteq> ac" using rr by simp
    then show False using no_hc_ring[OF _ nhe Urr rrD rhc] by blast
  qed
qed

theorem embed_functor:
  assumes x: "x \<in> ac" and ex: "C.e x \<in> ac"
  shows "h (C.e x) = edge Gm (h x)"
proof (rule ccontr)
  assume "h (C.e x) \<noteq> edge Gm (h x)"
  then have nh: "\<not> hc x" by (simp add: edge_central_def)
  obtain p where pth: "path (rlink Gc) x p" and lx: "C.cface (lastd x p) x" and pne: "p \<noteq> []"
    and sp: "simple Gc p" and pac: "\<forall>z \<in> set p. z \<in> ac \<and> hc z"
    using h_spoke[OF ex x] by blast
  obtain p' y' where ps: "p = p' @ [y']" using pne by (cases p rule: rev_cases) auto
  have "rlink Gc (lastd x p') y'" using pth ps by simp
  then have cl: "rlink Gc (lastd x p') x" using C.rlink_cface[of y' x] lx ps by simp
  have "path (rlink Gc) x p'" using pth ps by simp
  then have cyc: "cycle (rlink Gc) (x # p')" using cl by (simp add: cycle_Cons)
  have simp': "simple Gc p'" and nb: "\<not> fband Gc p' y'" using sp ps
    by (simp_all add: C.simple_append C.simple_Cons fband_def)
  have "\<not> fband Gc p' x" using nb C.fband_cface[OF lx] ps by simp
  then have "simple Gc (x # p')" using simp' by (simp add: C.simple_Cons)
  then have Ur: "scycle Gc (rlink Gc) (x # p')" using cyc by (simp add: scycle_def)
  show False by (rule embed_functor_ring[OF x nh Ur]) (use pac ps in auto)
qed

lemma cface_ac_h: "x \<in> ac \<Longrightarrow> C.cface x y \<Longrightarrow> M.cface (h x) (h y)"
proof -
  assume x: "x \<in> ac" and xy: "C.cface x y"
  from xy show ?thesis
  proof (induction rule: fconnect_induct)
    case refl then show ?case by simp
  next
    case (step y)
    have "y \<in> ac" using ac_cface[OF x step.hyps] .
    then have "h (C.f y) = M.f (h y)" by (rule hF)
    then show ?case using fconnect_trans[OF step.IH fconnect_step[of "M.f" "h y"]] by simp
  qed
qed

lemma cface_h_ac: "x \<in> ac \<Longrightarrow> M.cface (h x) u \<Longrightarrow> \<exists>y. C.cface x y \<and> h y = u"
proof -
  assume x: "x \<in> ac" and xu: "M.cface (h x) u"
  from xu show ?thesis
  proof (induction rule: fconnect_induct)
    case refl then show ?case by auto
  next
    case (step u)
    then obtain y where xy: "C.cface x y" and yu: "h y = u" by blast
    have "y \<in> ac" using ac_cface[OF x xy] .
    then have "h (C.f y) = M.f u" using hF yu by simp
    moreover have "C.cface x (C.f y)" using fconnect_trans[OF xy fconnect_step] .
    ultimately show ?case by blast
  qed
qed

lemma cface_inj_embed:
  assumes x: "x \<in> ac" and xy: "C.cface x y" and eq: "h x = h y"
  shows "x = y"
proof -
  have iter: "h ((C.f ^^ k) x) = (M.f ^^ k) (h x)" for k
  proof (induction k)
    case 0 then show ?case by simp
  next
    case (Suc k)
    have "(C.f ^^ k) x \<in> ac" using ac_cface[OF x fconnect_funpow] .
    then show ?case using hF Suc by simp
  qed
  obtain k where k: "k < order C.f x" and yk: "(C.f ^^ k) x = y" using C.F.fconnect_order xy by blast
  have hxD: "h x \<in> M.D" using hD x by (auto simp: ac_def)
  have "(M.f ^^ k) (h x) = h x" using iter[of k] yk eq by simp
  then have "order M.f (h x) dvd k" using M.F.order_dvd by blast
  moreover have "order M.f (h x) = order C.f x" by (rule hFn[OF x])
  ultimately have "k = 0" using k by (metis dvd_imp_le gr0I not_less)
  then show ?thesis using yk by simp
qed

definition pre_hom_ring :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "pre_hom_ring x p \<longleftrightarrow> path (rlink Gc) x p \<and> set (x # p) \<subseteq> ac \<and>
     scycle Gm (rlink Gm) (map h (x # p))"

lemma rlink_h: "a \<in> ac \<Longrightarrow> b \<in> ac \<Longrightarrow> rlink Gc a b \<Longrightarrow> rlink Gm (h a) (h b)"
proof -
  assume a: "a \<in> ac" and b: "b \<in> ac" and ab: "rlink Gc a b"
  have eab: "C.cface (C.e a) b" using ab by (simp add: rlink_def)
  have eac: "C.e a \<in> ac" using ac_cface[OF b C.F.fconnect_sym[OF eab]] .
  have "h (C.e a) = M.e (h a)" by (rule embed_functor[OF a eac])
  moreover have "M.cface (h (C.e a)) (h b)" by (rule cface_ac_h[OF eac eab])
  ultimately show ?thesis by (simp add: rlink_def)
qed

lemma path_h: "path (rlink Gc) x p \<Longrightarrow> set (x # p) \<subseteq> ac \<Longrightarrow> path (rlink Gm) (h x) (map h p)"
  by (induction p arbitrary: x) (auto intro: rlink_h)

lemma intro_pre_hom_ring:
  assumes xp: "path (rlink Gc) x p" and lst: "rlink Gm (h (lastd x p)) (h x)"
    and pac: "set (x # p) \<subseteq> ac" and sm: "simple Gm (map h (x # p))"
  shows "pre_hom_ring x p"
proof -
  have "path (rlink Gm) (h x) (map h p)" by (rule path_h[OF xp pac])
  moreover have "lastd (h x) (map h p) = h (lastd x p)" by (cases p rule: rev_cases) auto
  ultimately have "cycle (rlink Gm) (map h (x # p))" using lst by (simp add: cycle_Cons)
  then show ?thesis using xp pac sm by (simp add: pre_hom_ring_def scycle_def)
qed

lemma trivial_hom_ring_aux:
  "pre_hom_ring x p \<Longrightarrow> snip_ring.diskF Gm (map h (x # p)) = {} \<Longrightarrow> rlink Gc (lastd x p) x"
proof (induction "length p" arbitrary: x p rule: less_induct)
  case less
  define xp where "xp = x # p"
  define hxp where "hxp = map h xp"
  have xRp: "path (rlink Gc) x p" and pac: "set xp \<subseteq> ac" and Uh: "scycle Gm (rlink Gm) hxp"
    using less.prems(1) by (simp_all add: pre_hom_ring_def xp_def hxp_def)
  have dF0: "snip_ring.diskF Gm hxp = {}" using less.prems(2) by (simp add: hxp_def xp_def)
  have hxpD: "set hxp \<subseteq> M.D" using pac hD by (auto simp: hxp_def ac_def)
  interpret S: snip_ring Gm hxp using M.planarG Uh hxpD by unfold_locales auto
  have simp_h: "simple Gm hxp" and cyc_h: "cycle (rlink Gm) hxp" using Uh by (simp_all add: scycle_def)
  have dh: "distinct hxp" by (rule M.simple_distinct[OF simp_h])
  have inj: "inj_on h (set xp)" using dh by (simp add: hxp_def distinct_map)
  have sameh: "a = b" if "a \<in> set xp" "b \<in> set xp" "M.cface (h a) (h b)" for a b
  proof -
    have "h a \<in> set hxp" "h b \<in> set hxp" using that(1,2) by (auto simp: hxp_def)
    then have "h a = h b" using M.simple_cface[OF simp_h] that(3) by blast
    then show ?thesis using inj that(1,2) by (auto simp: inj_on_def)
  qed
  have notF: "fband Gm hxp w" if "w \<in> S.diskN" for w using that dF0 by (auto simp: S.diskF_def)
  have plC: "C.e (C.e w) = w" for w using C.plain_eq[OF geoGc(4)] .
  have plM: "M.e (M.e w) = w" for w using M.plain_eq[OF M.plainG] .
  define y where "y = lastd x p"
  have yxp: "y \<in> set xp" by (simp add: y_def xp_def)
  have yac: "y \<in> ac" using pac yxp by auto
  have hyD: "h y \<in> M.D" using hxpD yxp by (auto simp: hxp_def)
  have hyr: "h y \<in> set hxp" using yxp by (simp add: hxp_def)
  have hyRx: "rlink Gm (h y) (h x)"
  proof -
    have "path (rlink Gm) (h x) (map h p @ [h x])" using cyc_h by (simp add: hxp_def xp_def cycle_Cons)
    moreover have "lastd (h x) (map h p) = h y" by (cases p rule: rev_cases) (auto simp: y_def)
    ultimately show ?thesis by simp
  qed
  have nhyD: "M.n (h y) \<in> M.D" using hyD by simp
  have nhyN: "M.n (h y) \<in> S.diskN" using S.diskN_node[OF hyD] S.r_diskN[OF hyr] by simp
  have nnhyN: "M.n (M.n (h y)) \<in> S.diskN" using S.diskN_node[OF nhyD] nhyN by simp
  obtain z where zxp: "z \<in> set xp" and zF: "M.cface (h z) (M.n (h y))"
  proof -
    obtain w where "w \<in> set hxp" "M.cface (M.n (h y)) w" using notF[OF nhyN] by (auto simp: fband_def)
    then obtain z' where z1: "z' \<in> set xp" and z2: "M.cface (M.n (h y)) (h z')" by (auto simp: hxp_def)
    show ?thesis by (rule that[OF z1 M.F.fconnect_sym[OF z2]])
  qed
  have zac: "z \<in> ac" using zxp pac by auto
  have hzr: "h z \<in> set hxp" using zxp by (simp add: hxp_def)
  have zy: "z \<noteq> y"
  proof
    assume "z = y"
    then have "M.cface (M.n (h y)) (h y)" using M.F.fconnect_sym[OF zF] by simp
    then show False using M.no_cface_node[OF hyD] by simp
  qed
  \<comment> \<open>decompose the ring around z and y\<close>
  obtain l1' l2 where dp: "p = l1' @ z # l2 @ [y]"
  proof -
    obtain l1 r where xs: "xp = l1 @ z # r" using split_list[OF zxp] by blast
    have rne: "r \<noteq> []"
    proof
      assume "r = []"
      then have "y = z" using xs by (simp add: y_def xp_def)
      then show False using zy by simp
    qed
    then obtain l2 y' where r: "r = l2 @ [y']" by (cases r rule: rev_cases) auto
    have yy: "y' = y" using xs r by (simp add: y_def xp_def[symmetric])
    have l1ne: "l1 \<noteq> []"
    proof
      assume l1: "l1 = []"
      then have zx: "z = x" using xs by (simp add: xp_def)
      have "M.cface (M.e (h y)) (h x)" using hyRx by (simp add: rlink_def)
      then have a: "M.cface (M.n (M.n (h y))) (h x)"
        by (rule fconnect_trans[OF M.F.fconnect_sym[OF M.cface_edge_nn[OF hyD]]])
      have zF': "M.cface (h x) (M.n (h y))" using zF zx by simp
      have "M.cface (M.n (M.n (h y))) (M.n (h y))" by (rule fconnect_trans[OF a zF'])
      then show False using M.no_cface_node[OF nhyD] by simp
    qed
    then obtain l1' where "l1 = x # l1'" using xs by (cases l1) (auto simp: xp_def)
    then show ?thesis using that xs r yy by (simp add: xp_def)
  qed
  have xpd: "xp = x # l1' @ z # l2 @ [y]" using dp by (simp add: xp_def)
  have len3: "2 < length hxp" by (simp add: hxp_def xpd)
  interpret Rv: revsnip_proper Gm hxp by (rule M.revsnip_properI[OF Uh hxpD size_proper_ring[OF len3]])
  \<comment> \<open>the chord argument: a chord through w cuts off a ring whose face disk is empty\<close>
  have chord_dF: "snip_ring.diskF Gm (u # l @ [w]) = {}"
    if hs: "hxp = la @ u # l @ v # lc" and ewN: "M.e w \<in> S.diskN" and ewr: "M.e w \<notin> set hxp"
      and ewu: "M.cface (M.e w) u" and wv: "M.cface w v" for la u l v lc w
  proof -
    have ewD: "M.e w \<in> M.D" using ewN S.diskN_D by blast
    have ewE: "M.e w \<in> S.diskE" using ewN ewr by (simp add: S.diskE_def)
    have wE: "w \<in> S.diskE" using S.diskE_edge[OF ewD] ewE plM by simp
    have ur: "u \<in> set hxp" and vr: "v \<in> set hxp" using hs by auto
    have fbw: "fband Gm hxp w" using wv vr by (auto simp: fband_def)
    have fbew: "fband Gm hxp (M.e w)" using ewu ur by (auto simp: fband_def)
    interpret Ch: chord Gm hxp w by unfold_locales (use wE fbw fbew in auto)
    have fp1: "fproj Gm hxp w = v"
      using M.fproj_cface[OF wv fbw] M.simple_fproj[OF simp_h vr] by simp
    have fp2: "fproj Gm hxp (M.e w) = u"
      using M.fproj_cface[OF ewu fbew] M.simple_fproj[OF simp_h ur] by simp
    have "arc hxp u v = u # l" using arc_mid[of la u l v lc] dh hs by simp
    then have cr: "chord_ring Gm hxp w = w # u # l" using fp1 fp2 by (simp add: chord_ring_def)
    have "snip_ring.diskF Gm (u # l @ [w]) = snip_ring.diskF Gm (rot 1 (chord_ring Gm hxp w))"
      using cr by (simp add: rot1_Cons)
    also have "\<dots> = Ch.C1.diskF" by (rule Ch.C1.rot_disks(3))
    finally show ?thesis using Ch.diskF_chord_ring dF0 by blast
  qed
  define eny where "eny = C.e (C.n y)"
  have feny: "C.f eny = y" by (simp add: eny_def C.nodeK)
  have enyac: "eny \<in> ac" using acF[of eny] feny yac by simp
  have h_eny: "h eny = M.e (M.n (h y))"
  proof -
    have "h y = M.f (h eny)" using hF[OF enyac] feny by simp
    then show ?thesis using M.faceK[of "h eny"] by simp
  qed
  have enyFy: "C.cface eny y" using fconnect_step[of "C.f" eny] feny by simp
  have henyFhy: "M.cface (h eny) (h y)" using fconnect_step[of "M.f" "h eny"] h_eny M.nodeK by simp
  have pz: "path (rlink Gc) z (l2 @ [y])" and px: "path (rlink Gc) x (l1' @ [z])"
    using xRp dp by simp_all
  \<comment> \<open>claim A: the node of y is face-connected to z\<close>
  have nyz: "C.cface (C.n y) z"
  proof (cases "M.n (h y) \<in> set hxp")
    case True
    then obtain t where txp: "t \<in> set xp" and ht: "h t = M.n (h y)" by (auto simp: hxp_def)
    have tz: "t = z" using sameh[OF txp zxp] M.F.fconnect_sym[OF zF] ht by simp
    obtain t1 rest where tr: "l2 @ [y] = t1 # rest" by (cases l2) auto
    have "t1 \<in> set (l2 @ [y])" using tr by simp
    then have t1xp: "t1 \<in> set xp" using xpd by auto
    have zt1: "rlink Gc z t1" using path_mid[OF xRp, of "x # l1'" z t1 rest] tr dp by simp
    have t1ac: "t1 \<in> ac" using t1xp pac by auto
    have "M.cface (M.e (h z)) (h t1)" using rlink_h[OF zac t1ac zt1] by (simp add: rlink_def)
    moreover have "M.cface (h y) (M.e (h z))"
      using M.F.fconnect_sym[OF M.cface_enK[of "h y"]] ht tz by simp
    ultimately have "M.cface (h y) (h t1)" by (rule fconnect_trans[rotated])
    then have t1y: "t1 = y" using sameh[OF yxp t1xp] by simp
    have zy': "C.cface (C.e z) y" using zt1 t1y by (simp add: rlink_def)
    have ezac: "C.e z \<in> ac" using ac_cface[OF yac C.F.fconnect_sym[OF zy']] .
    have "h (C.e z) = M.e (h z)" by (rule embed_functor[OF zac ezac])
    then have heq: "h (C.e z) = h eny" using h_eny ht tz by simp
    have "C.cface (C.e z) eny" by (rule fconnect_trans[OF zy' C.F.fconnect_sym[OF enyFy]])
    then have "C.e z = eny" using cface_inj_embed[OF ezac] heq by blast
    then have "z = C.n y" using plC[of z] plC[of "C.n y"] by (simp add: eny_def)
    then show ?thesis by simp
  next
    case False
    define q where "q = l2 @ [eny]"
    have lq: "length q < length p" by (simp add: q_def dp)
    have zq: "pre_hom_ring z q"
    proof (rule intro_pre_hom_ring)
      have "rlink Gc (lastd z l2) y" using pz by simp
      then have "rlink Gc (lastd z l2) eny" unfolding rlink_def
        by (rule fconnect_trans[OF _ C.F.fconnect_sym[OF enyFy]])
      then show "path (rlink Gc) z q" using pz by (simp add: q_def)
      have "M.cface (M.n (h y)) (h z)" using M.F.fconnect_sym[OF zF] .
      then show "rlink Gm (h (lastd z q)) (h z)" using h_eny plM by (simp add: q_def rlink_def)
      show "set (z # q) \<subseteq> ac" using pac enyac zac by (auto simp: q_def xpd)
      have "simple Gm (map h (z # l2 @ [y]))"
        using simp_h M.simple_append[of "map h (x # l1')" "map h (z # l2 @ [y])"]
        by (simp add: hxp_def xpd)
      then show "simple Gm (map h (z # q))"
        using M.simple_snoc_cface[of "map h (z # l2)" "h y" "h eny"] M.F.fconnect_sym[OF henyFhy]
        by (simp add: q_def)
    qed
    have dq: "snip_ring.diskF Gm (map h (z # q)) = {}"
    proof -
      have hs: "hxp = map h (x # l1') @ h z # map h l2 @ h y # []" by (simp add: hxp_def xpd)
      have ewN: "M.e (h eny) \<in> S.diskN" using nhyN h_eny plM by simp
      have ewr: "M.e (h eny) \<notin> set hxp" using False h_eny plM by simp
      have ewu: "M.cface (M.e (h eny)) (h z)" using M.F.fconnect_sym[OF zF] h_eny plM by simp
      show ?thesis using chord_dF[OF hs ewN ewr ewu henyFhy] by (simp add: q_def)
    qed
    have "rlink Gc (lastd z q) z" using less.hyps[OF lq zq dq] .
    then show ?thesis using plC by (simp add: q_def rlink_def eny_def)
  qed
  have nyac: "C.n y \<in> ac" using ac_cface[OF zac C.F.fconnect_sym[OF nyz]] .
  have h_ny: "h (C.n y) = M.n (h y)"
  proof -
    have "h eny = M.e (h (C.n y))" using embed_functor[OF nyac] enyac by (simp add: eny_def)
    then have "M.e (h (C.n y)) = M.e (M.n (h y))" using h_eny by simp
    then have "M.e (M.e (h (C.n y))) = M.e (M.e (M.n (h y)))" by simp
    then show ?thesis using plM by simp
  qed
  define enny where "enny = C.e (C.n (C.n y))"
  have fenny: "C.f enny = C.n y" by (simp add: enny_def C.nodeK)
  have ennyac: "enny \<in> ac" using acF[of enny] fenny nyac by simp
  have h_enny: "h enny = M.e (M.n (M.n (h y)))"
  proof -
    have "M.n (h y) = M.f (h enny)" using hF[OF ennyac] fenny h_ny by simp
    then show ?thesis using M.faceK[of "h enny"] by simp
  qed
  have ennyFny: "C.cface enny (C.n y)" using fconnect_step[of "C.f" enny] fenny by simp
  have hennyFz: "M.cface (h enny) (h z)"
  proof -
    have "M.cface (h enny) (M.n (h y))" using fconnect_step[of "M.f" "h enny"] h_enny M.nodeK by simp
    then show ?thesis by (rule fconnect_trans[OF _ M.F.fconnect_sym[OF zF]])
  qed
  have nnhyFx: "M.cface (M.n (M.n (h y))) (h x)"
    using fconnect_trans[OF M.F.fconnect_sym[OF M.cface_edge_nn[OF hyD]], of "h x"] hyRx
    unfolding rlink_def by simp
  have xxp: "x \<in> set xp" and xac: "x \<in> ac" using pac by (auto simp: xp_def)
  \<comment> \<open>claim B: the second node of y is face-connected to x\<close>
  have nnyx: "C.cface (C.n (C.n y)) x"
  proof (cases "M.n (M.n (h y)) \<in> set hxp")
    case True
    then obtain t where txp: "t \<in> set xp" and ht: "h t = M.n (M.n (h y))" by (auto simp: hxp_def)
    have tx: "t = x" using sameh[OF txp xxp] nnhyFx ht by simp
    obtain t1 rest where tr: "l1' @ z # l2 @ [y] = t1 # rest" by (cases l1') auto
    have t1xp: "t1 \<in> set xp" using tr xpd by simp
    have xt1: "rlink Gc x t1" using path_mid[OF xRp, of "[]" x t1 rest] tr dp by simp
    have t1ac: "t1 \<in> ac" using t1xp pac by auto
    have "M.cface (M.e (h x)) (h t1)" using rlink_h[OF xac t1ac xt1] by (simp add: rlink_def)
    moreover have "M.cface (h z) (M.e (h x))"
      using fconnect_trans[OF zF M.F.fconnect_sym[OF M.cface_enK[of "M.n (h y)"]]] ht tx by simp
    ultimately have "M.cface (h z) (h t1)" by (rule fconnect_trans[rotated])
    then have t1z: "t1 = z" using sameh[OF zxp t1xp] by simp
    have xz: "C.cface (C.e x) z" using xt1 t1z by (simp add: rlink_def)
    have exac: "C.e x \<in> ac" using ac_cface[OF zac C.F.fconnect_sym[OF xz]] .
    have "h (C.e x) = M.e (h x)" by (rule embed_functor[OF xac exac])
    then have heq: "h (C.e x) = h enny" using h_enny ht tx by simp
    have zenny: "C.cface z enny"
      by (rule fconnect_trans[OF C.F.fconnect_sym[OF nyz] C.F.fconnect_sym[OF ennyFny]])
    have "C.cface (C.e x) enny" by (rule fconnect_trans[OF xz zenny])
    then have "C.e x = enny" using cface_inj_embed[OF exac] heq by blast
    then have "x = C.n (C.n y)" using plC[of x] plC[of "C.n (C.n y)"] by (simp add: enny_def)
    then show ?thesis by simp
  next
    case False
    define q where "q = l1' @ [enny]"
    have lq: "length q < length p" by (simp add: q_def dp)
    have xq: "pre_hom_ring x q"
    proof (rule intro_pre_hom_ring)
      have "rlink Gc (lastd x l1') z" using px by simp
      moreover have "C.cface z enny"
        by (rule fconnect_trans[OF C.F.fconnect_sym[OF nyz] C.F.fconnect_sym[OF ennyFny]])
      ultimately have "rlink Gc (lastd x l1') enny" unfolding rlink_def by (rule fconnect_trans)
      then show "path (rlink Gc) x q" using px by (simp add: q_def)
      show "rlink Gm (h (lastd x q)) (h x)" using nnhyFx h_enny plM by (simp add: q_def rlink_def)
      show "set (x # q) \<subseteq> ac" using pac ennyac by (auto simp: q_def xpd)
      have "simple Gm (map h (x # l1' @ [z]))"
        using simp_h M.simple_append[of "map h (x # l1' @ [z])" "map h (l2 @ [y])"]
        by (simp add: hxp_def xpd)
      then show "simple Gm (map h (x # q))"
        using M.simple_snoc_cface[of "map h (x # l1')" "h z" "h enny"] M.F.fconnect_sym[OF hennyFz]
        by (simp add: q_def)
    qed
    have dq: "snip_ring.diskF Gm (map h (x # q)) = {}"
    proof -
      have hs: "hxp = [] @ h x # map h l1' @ h z # map h (l2 @ [y])" by (simp add: hxp_def xpd)
      have ewN: "M.e (h enny) \<in> S.diskN" using nnhyN h_enny plM by simp
      have ewr: "M.e (h enny) \<notin> set hxp" using False h_enny plM by simp
      have ewu: "M.cface (M.e (h enny)) (h x)" using nnhyFx h_enny plM by simp
      show ?thesis using chord_dF[OF hs ewN ewr ewu hennyFz] by (simp add: q_def)
    qed
    have "rlink Gc (lastd x q) x" using less.hyps[OF lq xq dq] .
    then show ?thesis using plC by (simp add: q_def rlink_def enny_def)
  qed
  have "C.f (C.e y) = C.n (C.n y)" using C.nodeK[of "C.n (C.n y)"] ac_cubic(1)[OF yac] by simp
  then have "C.cface (C.e y) (C.n (C.n y))" using fconnect_step[of "C.f" "C.e y"] by simp
  then have "C.cface (C.e y) x" by (rule fconnect_trans[OF _ nnyx])
  then show ?case by (simp add: rlink_def y_def)
qed

theorem trivial_hom_ring:
  assumes "pre_hom_ring x p" and "fcard (face Gm) (snip_ring.diskF Gm (map h (x # p))) = 0"
  shows "rlink Gc (lastd x p) x"
proof -
  have Uh: "scycle Gm (rlink Gm) (map h (x # p))" and pac: "set (x # p) \<subseteq> ac"
    using assms(1) by (simp_all add: pre_hom_ring_def)
  have "set (map h (x # p)) \<subseteq> M.D" using pac hD by (auto simp: ac_def)
  then interpret S: snip_ring Gm "map h (x # p)" using M.planarG Uh by unfold_locales auto
  have "S.diskF = {}" using assms(2) fcard0P[of S.diskF "face Gm"] S.diskF_D M.finite_darts
    by (metis finite_subset less_numeral_extra(3))
  then show ?thesis by (rule trivial_hom_ring_aux[OF assms(1)])
qed

lemma rcN: "C.n x \<in> set rc \<longleftrightarrow> x \<in> set rc"
proof -
  define L where "L = length rc"
  have cyc: "\<forall>i < L. C.n (rc ! i) = rc ! (Suc i mod L)"
    using geoGc(7) by (simp add: ucycle_def cycle_nth L_def)
  have fw: "C.n w \<in> set rc" if wr: "w \<in> set rc" for w
  proof -
    obtain i where i: "i < L" "rc ! i = w" using wr unfolding L_def in_set_conv_nth by blast
    then have "C.n w = rc ! (Suc i mod L)" using cyc by auto
    moreover have "Suc i mod L < L" using i by simp
    ultimately show ?thesis by (simp add: L_def)
  qed
  have bw: "w \<in> set rc" if wr: "C.n w \<in> set rc" for w
  proof -
    obtain i where i: "i < L" "rc ! i = C.n w" using wr unfolding L_def in_set_conv_nth by blast
    define j where "j = (i + L - 1) mod L"
    have j: "j < L" using i by (simp add: j_def)
    have "Suc j mod L = Suc (i + L - 1) mod L" by (simp add: j_def mod_Suc_eq)
    also have "Suc (i + L - 1) = i + L" using i by simp
    also have "(i + L) mod L = i" using i by simp
    finally have "C.n (rc ! j) = C.n w" using cyc j i by auto
    then have "rc ! j = w" using C.N.inj by (simp add: inj_eq)
    then show ?thesis using j by (auto simp: L_def)
  qed
  show ?thesis using fw bw by blast
qed

lemma edge_perimeter:
  assumes xD: "x \<in> C.D"
  shows "x \<in> bc \<or> C.e x \<in> bc"
proof (rule ccontr)
  assume "\<not> (x \<in> bc \<or> C.e x \<in> bc)"
  then have xr: "x \<in> set rc" and exr: "C.e x \<in> set rc" using xD by (auto simp: bc_def)
  have "C.n (C.f x) = C.e x" by (rule C.plain_eq'[OF geoGc(4)])
  then have fxr: "C.f x \<in> set rc" using rcN[of "C.f x"] exr by simp
  have "C.f x = x"
    by (rule C.simple_cface[OF geoGc(9) fxr xr C.F.fconnect_sym[OF fconnect_step[of "C.f" x]]])
  then have "arity Gc x = 1" using C.F.order_1_iff by simp
  moreover have "good_ring_arity Gc x" using embedGc xr by (simp add: embeddable_def)
  ultimately show False by (simp add: good_ring_arity_def)
qed

definition erc :: "'a list" where "erc = map C.e rc"

lemma C_no_cface_node: "x \<in> C.D \<Longrightarrow> \<not> C.cface (C.n x) x"
proof
  assume xD: "x \<in> C.D" and c: "C.cface (C.n x) x"
  have "C.cface (C.e (C.n x)) x" using fconnect_step[of "C.f" "C.e (C.n x)"] by (simp add: C.nodeK)
  then have "C.cface (C.n x) (C.e (C.n x))" by (rule fconnect_trans[OF c C.F.fconnect_sym])
  then show False using geoGc(3) xD by (simp add: bridgeless_def)
qed

lemma bc_cubic:
  assumes "x \<in> bc"
  shows "C.n (C.n (C.n x)) = x" and "C.n x \<noteq> x"
proof -
  have xD: "x \<in> C.D" and xr: "x \<notin> set rc" using assms by (auto simp: bc_def)
  show "C.n (C.n (C.n x)) = x" by (rule C.quasicubic_eq[OF geoGc(5) xD xr])
  have "order (C.n) x = 3" using geoGc(5) xD xr by (simp add: quasicubic_def cubicb_def)
  then show "C.n x \<noteq> x" using C.N.order_1_iff[of x] by auto
qed

lemma nt_ring:
  "scycle Gc (rlink Gc) p \<Longrightarrow> set p \<subseteq> C.D \<Longrightarrow> proper_ring Gc p \<Longrightarrow> set (tl p) \<subseteq> set erc \<Longrightarrow>
   snip_ring.diskN Gc p \<subseteq> bc \<Longrightarrow> snip_ring.diskF Gc p \<noteq> {}"
proof (induction "length p" arbitrary: p rule: less_induct)
  case less
  have Up: "scycle Gc (rlink Gc) p" and pD: "set p \<subseteq> C.D" and pr: "proper_ring Gc p"
    and perc: "set (tl p) \<subseteq> set erc" and Nbc: "snip_ring.diskN Gc p \<subseteq> bc" using less.prems by auto
  interpret S: revsnip_proper Gc p
    using revsnipC[OF Up pD] pr by (simp add: revsnip_proper_def revsnip_proper_axioms_def)
  show ?case
  proof
    assume dF0: "S.diskF = {}"
    obtain x z p1 where p: "p = x # z # p1" using pr by (cases p rule: remdups_adj.cases) auto
    have xp: "x \<in> set p" and zp: "z \<in> set p" and xD: "x \<in> C.D" using p pD by auto
    have dp: "distinct p" by (rule S.distinct_r)
    have notF: "fband Gc p w" if "w \<in> S.diskN" for w using that dF0 by (auto simp: S.diskF_def)
    have xN: "x \<in> S.diskN" by (rule S.r_diskN[OF xp])
    have xbc: "x \<in> bc" using Nbc xN by blast
    have cub: "C.n (C.n (C.n x)) = x" and nxx: "C.n x \<noteq> x" using bc_cubic[OF xbc] by auto
    have plC: "C.e (C.e w) = w" for w using C.plain_eq[OF geoGc(4)] .
    have nxt: "next_in p x = z" using p dp by (simp add: next_in_def)
    have xz: "C.cface (C.e x) z" using S.cface_e_next[OF xp] nxt by simp
    have nxN: "C.n x \<in> S.diskN" using S.diskN_node[OF xD] xN by simp
    have tlp: "set (tl p) = set p - {x}" using dp p by auto
    have chordarg: False if wE: "w \<in> S.diskE" and fw: "fband Gc p w" and few: "fband Gc p (C.e w)"
      and cr: "chord_ring Gc p w = w # u # b" and sub: "set (u # b) \<subseteq> set (tl p)"
      and len: "length b + 2 < length p" for w u b
    proof -
      interpret Ch: chord Gc p w by unfold_locales (use wE fw few in auto)
      have l: "length (chord_ring Gc p w) < length p" using cr len by simp
      have t: "set (tl (chord_ring Gc p w)) \<subseteq> set erc" using cr sub perc by auto
      have n: "snip_ring.diskN Gc (chord_ring Gc p w) \<subseteq> bc" using Ch.diskN_chord_ring Nbc by blast
      have "Ch.C1.diskF \<noteq> {}"
        by (rule less.hyps[OF l conjunct1[OF Ch.sc1] conjunct2[OF Ch.sc1] Ch.proper_chord_ring t n])
      then obtain v where "v \<in> Ch.C1.diskF" by blast
      then show False using Ch.diskF_chord_ring dF0 by blast
    qed
    define efex where "efex = C.e (C.f (C.e x))"
    have fe: "C.f (C.e x) = C.n (C.n x)" using C.nodeK[of "C.n (C.n x)"] cub by simp
    have f_efex: "C.f efex = C.n x" using C.nodeK[of "C.n x"] fe by (simp add: efex_def)
    have efexD: "efex \<in> C.D" using xD by (simp add: efex_def)
    have eefex: "C.e efex = C.f (C.e x)" using plC by (simp add: efex_def)
    have fexN: "C.f (C.e x) \<in> S.diskN"
    proof -
      have "C.n (C.f (C.e x)) = x" using C.plain_eq'[OF geoGc(4), of "C.e x"] plC by simp
      then show ?thesis using S.diskN_node[of "C.f (C.e x)"] xN xD by simp
    qed
    have exz: "C.cface (C.f (C.e x)) z"
      by (rule fconnect_trans[OF C.F.fconnect_sym[OF fconnect_step[of "C.f" "C.e x"]] xz])
    have efexnx: "C.cface efex (C.n x)" using fconnect_step[of "C.f" efex] f_efex by simp
    show False
    proof (cases "efex \<in> S.diskE")
      case True
      have fb1: "fband Gc p efex" using notF[OF nxN] C.fband_face[of p efex] f_efex by simp
      have exz': "C.cface (C.e efex) z" using exz eefex by simp
      have fb2: "fband Gc p (C.e efex)" using exz' zp by (auto simp: fband_def)
      define y where "y = fproj Gc p efex"
      have yp: "y \<in> set p" and efy: "C.cface efex y" using C.fprojP[OF fb1] by (auto simp: y_def)
      have fp2: "fproj Gc p (C.e efex) = z"
        using C.fproj_cface[OF exz' fb2] C.simple_fproj[OF S.simple_r zp] by simp
      have yz: "y \<noteq> z" using S.chord_neq[OF fb1 fb2] fp2 by (simp add: y_def)
      have yx: "y \<noteq> x"
      proof
        assume yx: "y = x"
        have "C.cface (C.f efex) y" by (rule fconnect_trans[OF C.F.fconnect_sym[OF fconnect_step[of "C.f" efex]] efy])
        then show False using yx f_efex C_no_cface_node[OF xD] by simp
      qed
      have "y \<in> set p1" using yp yz yx p by auto
      then obtain l1 l2 where p1: "p1 = l1 @ y # l2" using split_list by metis
      have "arc p z y = z # l1" using arc_mid[of "[x]" z l1 y l2] dp p p1 by simp
      then have cr: "chord_ring Gc p efex = efex # z # l1" using fp2 by (simp add: chord_ring_def y_def)
      show False by (rule chordarg[OF True fb1 fb2 cr]) (auto simp: p p1)
    next
      case False
      have fexE: "C.f (C.e x) \<notin> S.diskE" using S.diskE_edge[OF efexD] False eefex by simp
      have fexp: "C.f (C.e x) \<in> set p" using fexE fexN by (simp add: S.diskE_def)
      have fz: "C.f (C.e x) = z" by (rule S.r_cface[OF fexp zp exz])
      have ez: "C.e z = efex" using fz by (simp add: efex_def)
      have nz: "\<And>z'. C.cface (C.e z) z' \<Longrightarrow> C.cface (C.n x) z'"
        using fconnect_trans[OF C.F.fconnect_sym[OF efexnx]] ez by simp
      obtain z1 p3 where p1: "p1 = z1 # p3"
      proof (cases p1)
        case Nil
        then have "next_in p z = x" using p dp by (simp add: next_in_def)
        then have "C.cface (C.n x) x" using nz S.cface_e_next[OF zp] by simp
        then show ?thesis using C_no_cface_node[OF xD] by simp
      qed
      have nxt2: "next_in p z = z1" using p p1 dp by (simp add: next_in_def)
      have nxz1: "C.cface (C.n x) z1" using nz S.cface_e_next[OF zp] nxt2 by simp
      define enx where "enx = C.e (C.n x)"
      have fenx: "C.f enx = x" by (simp add: enx_def C.nodeK)
      have enxD: "enx \<in> C.D" using xD by (simp add: enx_def)
      have enxx: "C.cface enx x" using fconnect_step[of "C.f" enx] fenx by simp
      have fb1: "fband Gc p enx" using xp enxx by (auto simp: fband_def)
      have eenx: "C.e enx = C.n x" using plC by (simp add: enx_def)
      have z1p: "z1 \<in> set p" using p p1 by simp
      have fb2: "fband Gc p (C.e enx)" using nxz1 z1p eenx by (auto simp: fband_def)
      have nxp: "C.n x \<notin> set p"
      proof
        assume nxp: "C.n x \<in> set p"
        have "C.n x \<in> set (tl p)" using nxp nxx tlp by auto
        then have "C.n x \<in> set erc" using perc by auto
        then obtain r where rr: "r \<in> set rc" "C.n x = C.e r" by (auto simp: erc_def)
        then have enxr: "C.e (C.n x) \<in> set rc" using plC by simp
        have "C.n (C.f (C.n x)) = C.e (C.n x)" by (rule C.plain_eq'[OF geoGc(4)])
        then have fnxr: "C.f (C.n x) \<in> set rc" using rcN[of "C.f (C.n x)"] enxr by simp
        have "z \<in> set (tl p)" using p by simp
        then have "z \<in> set erc" using perc by auto
        then obtain r' where "r' \<in> set rc" "z = C.e r'" by (auto simp: erc_def)
        then have efexr: "efex \<in> set rc" using ez plC by auto
        have "C.cface efex (C.f (C.n x))" by (rule fconnect_trans[OF efexnx fconnect_step])
        then have ff: "C.f (C.n x) = efex"
          by (rule C.simple_cface[OF geoGc(9) fnxr efexr C.F.fconnect_sym])
        have "(C.f ^^ 2) efex = efex" using f_efex ff by (simp add: numeral_2_eq_2)
        then have "order C.f efex dvd 2" using C.F.order_dvd by blast
        then have "arity Gc efex \<le> 2" by (simp add: dvd_imp_le)
        moreover have "good_ring_arity Gc efex" using embedGc efexr by (simp add: embeddable_def)
        ultimately show False by (simp add: good_ring_arity_def)
      qed
      have nxE: "C.n x \<in> S.diskE" using nxN nxp by (simp add: S.diskE_def)
      have enxE: "enx \<in> S.diskE" using S.diskE_edge[OF enxD] nxE eenx by simp
      have fp1: "fproj Gc p enx = x"
        using C.fproj_cface[OF enxx fb1] C.simple_fproj[OF S.simple_r xp] by simp
      have fp2: "fproj Gc p (C.e enx) = z1"
        using C.fproj_cface[OF _ fb2, of z1] nxz1 eenx C.simple_fproj[OF S.simple_r z1p] by simp
      have "arc (([] @ x # [z]) @ z1 # p3) z1 x = z1 # p3 @ []"
        by (rule arc_wrap) (use dp p p1 in simp)
      then have "arc p z1 x = z1 # p3" using p p1 by simp
      then have cr: "chord_ring Gc p enx = enx # z1 # p3" using fp1 fp2 by (simp add: chord_ring_def)
      show False by (rule chordarg[OF enxE fb1 fb2 cr]) (auto simp: p p1)
    qed
  qed
qed

lemma scycle_rrc: "scycle Gc (rlink Gc) (rev rc)"
proof -
  have cyc: "cycle (frel C.n) rc" using geoGc(7) by (simp add: ucycle_def)
  have st: "rlink Gc (C.n a) a" for a
    using fconnect_step[of "C.f" "C.e (C.n a)"] by (simp add: rlink_def C.nodeK)
  have "cycle (\<lambda>a b. rlink Gc b a) rc"
    using cycle_mono[of "frel C.n" "\<lambda>a b. rlink Gc b a" rc] cyc st by auto
  then have "cycle (rlink Gc) (rev rc)" by (simp add: cycle_rev)
  moreover have "simple Gc (rev rc)" using geoGc(9) by (simp add: C.simple_rev)
  ultimately show ?thesis by (simp add: scycle_def)
qed

lemma erc_rev: "rev_ring Gc (rev rc) = erc"
  by (simp add: rev_ring_def erc_def rev_map)

lemma erc_props:
  assumes rc0: "rc \<noteq> []"
  shows "revsnip_proper Gc erc" and "proper_ring Gc (rev rc)"
    and "fband Gc erc w \<longleftrightarrow> fband Gc rc w" and "w \<in> snip_ring.diskN Gc erc \<Longrightarrow> w \<in> bc"
proof -
  have rrD: "set (rev rc) \<subseteq> C.D" using geoGc(8) by simp
  interpret Q: revsnip Gc "rev rc" by (rule revsnipC[OF scycle_rrc rrD])
  have Ue: "scycle Gc (rlink Gc) erc" using Q.scycle_rev_ring erc_rev by simp
  have eD: "set erc \<subseteq> C.D" using geoGc(8) by (auto simp: erc_def)
  have plC: "C.e (C.e w) = w" for w using C.plain_eq[OF geoGc(4)] .
  have pr2: "C.e a \<noteq> b" if rc: "rc = [a, b]" for a b
  proof
    assume eab: "C.e a = b"
    have aD: "a \<in> C.D" using geoGc(8) rc by simp
    have "a \<in> bc \<or> C.e a \<in> bc" by (rule edge_perimeter[OF aD])
    then show False unfolding bc_def using rc eab by auto
  qed
  have len1: "rc \<noteq> [a]" for a
  proof
    assume rc: "rc = [a]"
    have aD: "a \<in> C.D" using geoGc(8) rc by simp
    have "cycle (rlink Gc) erc" using Ue by (simp add: scycle_def)
    moreover have "erc = [C.e a]"
    proof -
      have "erc = map C.e rc" by (rule erc_def)
      then show ?thesis using rc by (simp only: list.map)
    qed
    ultimately have "cycle (rlink Gc) [C.e a]" by simp
    then have "C.cface a (C.e a)" using plC by (simp add: cycle_Cons rlink_def)
    then show False using geoGc(3) aD by (simp add: bridgeless_def)
  qed
  have shape: "2 < length rc \<or> (\<exists>a b. rc = [a, b])"
  proof -
    obtain a l where rcl: "rc = a # l" using rc0 by (cases rc) auto
    show ?thesis
    proof (cases l)
      case Nil
      then show ?thesis using len1[of a] rcl by simp
    next
      case (Cons b l')
      then show ?thesis using rcl by (cases l') auto
    qed
  qed
  have lerc: "length erc = length rc" by (simp add: erc_def)
  show prr: "proper_ring Gc (rev rc)"
  proof (cases "2 < length rc")
    case True
    then show ?thesis by (intro size_proper_ring) simp
  next
    case False
    then obtain a b where rc: "rc = [a, b]" using shape by blast
    have "C.e a \<noteq> b" by (rule pr2[OF rc])
    then have "C.e b \<noteq> a" using plC by metis
    then show ?thesis using rc by simp
  qed
  have "proper_ring Gc erc"
  proof (cases "2 < length rc")
    case True
    then show ?thesis using lerc by (intro size_proper_ring) simp
  next
    case False
    then obtain a b where rc: "rc = [a, b]" using shape by blast
    have ne: "C.e a \<noteq> b" by (rule pr2[OF rc])
    have "erc = map C.e rc" by (rule erc_def)
    then have "erc = [C.e a, C.e b]" using rc by (simp only: list.map)
    then show ?thesis using ne plC by (metis proper_ring_simps(3))
  qed
  then show "revsnip_proper Gc erc"
    using revsnipC[OF Ue eD] by (simp add: revsnip_proper_def revsnip_proper_axioms_def)
  show "fband Gc erc w \<longleftrightarrow> fband Gc rc w"
    using Q.fband_rev_ring[of w] erc_rev by (simp add: fband_def)
  show "w \<in> bc" if wN: "w \<in> snip_ring.diskN Gc erc"
  proof -
    have "w \<in> Q.R.diskN" using wN erc_rev by simp
    moreover have wD: "w \<in> C.D" using Q.R.diskN_D calculation by blast
    ultimately have "w \<notin> Q.diskN" using Q.diskN_rev_ring[OF prr wD] by simp
    then have "w \<notin> set rc" using Q.r_diskN[of w] by auto
    then show ?thesis using wD by (simp add: bc_def)
  qed
qed

lemma chord_erc_ac:
  assumes rc0: "rc \<noteq> []" and wE: "w \<in> snip_ring.diskE Gc erc"
    and fw: "fband Gc erc w" and few: "fband Gc erc (C.e w)"
  shows "snip_ring.diskF Gc (chord_ring Gc erc w) = ac"
proof -
  interpret E: revsnip_proper Gc erc by (rule erc_props(1)[OF rc0])
  interpret Ch: chord Gc erc w by unfold_locales (use wE fw few in auto)
  have plC: "C.e (C.e u) = u" for u using C.plain_eq[OF geoGc(4)] .
  have sub: "Ch.C1.diskF \<subseteq> ac"
  proof
    fix v assume "v \<in> Ch.C1.diskF"
    then have "v \<in> E.diskF" using Ch.diskF_chord_ring by blast
    then have "v \<in> C.D" "\<not> fband Gc erc v" using E.diskF_D by (auto simp: E.diskF_def)
    then show "v \<in> ac" using erc_props(3)[OF rc0, of v] by (simp add: ac_def kernel_def)
  qed
  have ne: "Ch.C1.diskF \<noteq> {}"
  proof (rule nt_ring)
    show "scycle Gc (rlink Gc) (chord_ring Gc erc w)" "set (chord_ring Gc erc w) \<subseteq> C.D"
      using Ch.sc1 by auto
    show "proper_ring Gc (chord_ring Gc erc w)" by (rule Ch.proper_chord_ring)
    show "set (tl (chord_ring Gc erc w)) \<subseteq> set erc"
    proof -
      obtain i p1 p2 where rt: "rot i erc = fproj Gc erc w # p1 @ fproj Gc erc (C.e w) # p2"
        and c1: "chord_ring Gc erc w = w # fproj Gc erc (C.e w) # p2"
        using Ch.decomp by blast
      have "set (rot i erc) = set erc" by simp
      then show ?thesis using rt c1 by auto
    qed
    show "snip_ring.diskN Gc (chord_ring Gc erc w) \<subseteq> bc"
      using Ch.diskN_chord_ring erc_props(4)[OF rc0] by blast
  qed
  have nb: "\<not> fband Gc (chord_ring Gc erc w) u" if "u \<in> ac" for u
    using that Ch.fband_chord_ring[of u] erc_props(3)[OF rc0, of u] by (auto simp: ac_def kernel_def)
  have walk: "lastd a l \<in> Ch.C1.diskF"
    if "a \<in> Ch.C1.diskF" "path (rlink Gc) a l" "\<forall>u \<in> set l. u \<in> ac" for a l
    using that
  proof (induction l arbitrary: a)
    case Nil
    then show ?case by simp
  next
    case (Cons b l)
    have aN: "a \<in> Ch.C1.diskN" using Cons.prems(1) by (simp add: Ch.C1.diskF_def)
    have ab: "rlink Gc a b" and bac: "b \<in> ac" using Cons.prems(2,3) by auto
    have "b \<in> Ch.C1.diskF" by (rule Ch.C1.rlink_diskF[OF aN ab nb[OF bac]])
    then show ?case using Cons.IH Cons.prems by simp
  qed
  have sup: "ac \<subseteq> Ch.C1.diskF"
  proof
    fix z assume zac: "z \<in> ac"
    obtain v where vF: "v \<in> Ch.C1.diskF" using ne by blast
    have "C.e (C.e v) \<in> ac" using sub vF plC by auto
    then obtain q where qp: "path (rlink Gc) (C.e v) q" and lz: "C.cface (lastd (C.e v) q) z"
      and qne: "q \<noteq> []" and qac: "\<forall>u \<in> set q. u \<in> ac \<and> hc u"
      using h_spoke[of "C.e v" z] zac by blast
    obtain y1 q' where q: "q = y1 # q'" using qne by (cases q) auto
    have "C.cface v y1" using qp q plC by (simp add: rlink_def)
    then have y1F: "y1 \<in> Ch.C1.diskF" using Ch.C1_diskF_cface vF by blast
    have "lastd y1 q' \<in> Ch.C1.diskF" by (rule walk[OF y1F]) (use qp qac q in auto)
    then have "lastd (C.e v) q \<in> Ch.C1.diskF" using q by simp
    then show "z \<in> Ch.C1.diskF" using Ch.C1_diskF_cface[OF lz] by blast
  qed
  show ?thesis using sub sup by blast
qed

theorem chordless_perimeter:
  assumes xbc: "x \<in> bc" and exbc: "C.e x \<in> bc"
  shows "x \<in> ac \<or> C.e x \<in> ac"
proof (rule ccontr)
  assume nac: "\<not> (x \<in> ac \<or> C.e x \<in> ac)"
  have xD: "x \<in> C.D" and xr: "x \<notin> set rc" using xbc by (auto simp: bc_def)
  have exD: "C.e x \<in> C.D" using xD by simp
  have fx: "fband Gc rc x" and fex: "fband Gc rc (C.e x)" using nac xD by (auto simp: ac_def kernel_def)
  have rc0: "rc \<noteq> []" using fx by (auto simp: fband_def)
  interpret E: revsnip_proper Gc erc by (rule erc_props(1)[OF rc0])
  have plC: "C.e (C.e w) = w" for w using C.plain_eq[OF geoGc(4)] .
  have exE: "C.e x \<in> E.diskE"
  proof -
    have rrD: "set (rev rc) \<subseteq> C.D" using geoGc(8) by simp
    interpret Q: revsnip Gc "rev rc" by (rule revsnipC[OF scycle_rrc rrD])
    have "C.e x \<notin> Q.diskN"
    proof
      assume "C.e x \<in> Q.diskN"
      then obtain y where yr: "y \<in> set (rev rc)" and c: "connect Q.dlink (inv C.n y) (C.e x)"
        by (auto simp: Q.diskN_def Q.dconnect_def)
      have iyr: "inv C.n y \<in> set rc" using rcN[of "inv C.n y"] yr by simp
      from c show False
      proof (cases rule: converse_rtranclpE)
        case base
        then show False using iyr exbc by (simp add: bc_def)
      next
        case (step w)
        then show False using iyr by (simp add: Q.dlink_def)
      qed
    qed
    then have "C.e x \<in> Q.R.diskN" using Q.diskN_rev_ring[OF erc_props(2)[OF rc0] exD] by simp
    then have "C.e x \<in> E.diskN" using erc_rev by simp
    moreover have "C.e x \<notin> set erc" using xr by (auto simp: erc_def C.E.inj[THEN inj_eq])
    ultimately show ?thesis by (simp add: E.diskE_def)
  qed
  have xE: "x \<in> E.diskE" using E.diskE_edge[OF xD] exE by simp
  have f1: "fband Gc erc (C.e x)" "fband Gc erc (C.e (C.e x))" "fband Gc erc x"
    using fx fex erc_props(3)[OF rc0] plC by auto
  interpret Ch: chord Gc erc "C.e x" by unfold_locales (use exE f1 in auto)
  have a1: "snip_ring.diskF Gc (chord_ring Gc erc (C.e x)) = ac" by (rule chord_erc_ac[OF rc0 exE f1(1,2)])
  have a2: "snip_ring.diskF Gc (chord_ring Gc erc x) = ac" by (rule chord_erc_ac[OF rc0 xE f1(3,1)])
  obtain v where vac: "v \<in> ac" using embedGc by (auto simp: embeddable_def radius2_def ac_def)
  have "v \<in> Ch.C1.diskF" using a1 vac by simp
  moreover have "v \<in> Ch.C2.diskF" using a2 vac plC by simp
  ultimately show False using Ch.diskF_chord_ring by blast
qed

end

end
