(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Jordan.thy
    The Euler formula bound and the Jordan property of planar hypermaps.
    Ported from G. Gonthier's Coq development (jordan.v).
*)
theory Jordan
  imports Walkup
begin

section \<open>The Euler inequality\<close>

theorem even_genusP: "hypermap G \<Longrightarrow> even_genus G"
proof (induction "card (darts G)" arbitrary: G rule: less_induct)
  case less
  interpret hypermap G by (rule less.prems)
  show ?case
  proof (cases "D = {}")
    case True
    then show ?thesis
      by (simp add: even_genus_def genus_def Euler_lhs_def Euler_rhs_def n_comp_def fcard_def)
  next
    case False
    then obtain z where z: "z \<in> D" by blast
    have "card (darts (WalkupE G z)) < card D"
      using card_Diff1_less[OF finite_darts z] by simp
    then have "even_genus (WalkupE G z)"
      using less.hyps hypermap_WalkupE by blast
    then show ?thesis using even_genus_WalkupE[OF z] by simp
  qed
qed

corollary Euler_le: "hypermap G \<Longrightarrow> Euler_rhs G \<le> Euler_lhs G"
proof -
  assume "hypermap G"
  then have "Euler_lhs G = 2 * genus G + Euler_rhs G"
    using even_genusP by (simp add: even_genus_def)
  then show ?thesis by linarith
qed

section \<open>Lifting contour paths to Walkup transforms\<close>

context hypermap
begin

lemma skip_edge_permN:
  "skip_edge (permN G) z w =
     (if w = z then z else if n z = z then n w else if e (n w) = z then n z
      else if n w = z then n (f z) else n w)"
  by (simp add: skip_edge_def)

lemma skip_edge_permF:
  "skip_edge (permF G) z w =
     (if w = z then z else if f z = z then f w else if n (f w) = z then f z
      else if f w = z then f (e z) else f w)"
  by (simp add: skip_edge_def)

lemma WalkupN_simps [simp]:
  "darts (WalkupN G z) = D - {z}" "edge (WalkupN G z) = skip z e"
  "node (WalkupN G z) = skip_edge (permN G) z" "face (WalkupN G z) = skip z f"
  by (simp_all add: WalkupN_def)

lemma WalkupF_simps [simp]:
  "darts (WalkupF G z) = D - {z}" "edge (WalkupF G z) = skip z e"
  "node (WalkupF G z) = skip z n" "face (WalkupF G z) = skip_edge (permF G) z"
  by (simp_all add: WalkupF_def)

lemma clink_liftE:
  "clink G x y \<Longrightarrow> x \<noteq> z \<Longrightarrow> y \<noteq> z \<Longrightarrow> clink (WalkupE G z) x y"
  by (auto simp: clink_def skip_def)

lemma clink_liftN:
  "clink G x y \<Longrightarrow> x \<noteq> z \<Longrightarrow> y \<noteq> z \<Longrightarrow> y \<noteq> f z \<Longrightarrow> clink (WalkupN G z) x y"
proof -
  assume c: "clink G x y" and xz: "x \<noteq> z" and yz: "y \<noteq> z" and yfz: "y \<noteq> f z"
  consider "x = n y" | "f x = y" using c by (auto simp: clink_def)
  then show ?thesis
  proof cases
    case 1
    have "e (n y) \<noteq> z"
    proof
      assume "e (n y) = z"
      then have "y = f z" using nodeK[of y] by auto
      then show False using yfz by simp
    qed
    then have "skip_edge (permN G) z y = n y" using 1 xz yz by (simp add: skip_edge_permN)
    then show ?thesis using 1 by (simp add: clink_def)
  next
    case 2
    then show ?thesis using yz xz by (simp add: clink_def skip_def)
  qed
qed

lemma clink_liftF:
  "clink G x y \<Longrightarrow> x \<noteq> z \<Longrightarrow> y \<noteq> z \<Longrightarrow> y \<noteq> f (e z) \<Longrightarrow> clink (WalkupF G z) x y"
proof -
  assume c: "clink G x y" and xz: "x \<noteq> z" and yz: "y \<noteq> z" and yfez: "y \<noteq> f (e z)"
  consider "x = n y" | "f x = y" using c by (auto simp: clink_def)
  then show ?thesis
  proof cases
    case 1
    then show ?thesis using yz xz by (simp add: clink_def skip_def)
  next
    case 2
    have "n (f x) \<noteq> z"
    proof
      assume "n (f x) = z"
      then have "f x = f (e z)" using edgeK[of z] N.eq_iff[of "f x" "f (e z)"] by simp
      then show False using 2 yfez by simp
    qed
    then have "skip_edge (permF G) z x = f x" using 2 xz yz by (simp add: skip_edge_permF)
    then show ?thesis using 2 by (simp add: clink_def)
  qed
qed

lemma path_lift:
  assumes "\<And>a b. a \<in> set (x # p) \<Longrightarrow> b \<in> set p \<Longrightarrow> clink G a b \<Longrightarrow> clink H a b"
    "path (clink G) x p"
  shows "path (clink H) x p"
  using path_mono_in[of x p "clink G" "clink H"] assms by blast

end

lemma Moebius_pathI:
  assumes "hypermap H" "distinct (x # p)" "path (clink H) x p" "node H t = lastd x p"
    "mem2 p t (node H x)"
  shows "Moebius_path H (x # p)"
proof -
  interpret hypermap H by fact
  have "inv (node H) (node H t) = t" by simp
  then have "inv (node H) (lastd x p) = t" using assms(4) by simp
  then show ?thesis using assms by (simp add: Moebius_path_def)
qed

section \<open>Planar hypermaps have the Jordan property\<close>

theorem planar_Jordan_aux:
  "hypermap G \<Longrightarrow> planar G \<Longrightarrow> set q \<subseteq> darts G \<Longrightarrow> \<not> Moebius_path G q"
proof (induction "card (darts G)" arbitrary: G q rule: less_induct)
  case less
  interpret hypermap G by (rule less.prems(1))
  have planarG: "planar G" by (rule less.prems(2))
  have small: "card (D - {z}) < card D" if "z \<in> D" for z
    using that finite_darts by (meson card_Diff1_less)
  have IHE: "\<not> Moebius_path (WalkupE G z) q'" if "z \<in> D" "set q' \<subseteq> D - {z}" for z q'
    using less.hyps[of "WalkupE G z" q'] small[OF that(1)] hypermap_WalkupE planar_WalkupE[OF planarG that(1)]
      that(2) by simp
  have IHN: "\<not> Moebius_path (WalkupN G z) q'" if "z \<in> D" "set q' \<subseteq> D - {z}" for z q'
    using less.hyps[of "WalkupN G z" q'] small[OF that(1)] hypermap_WalkupN planar_WalkupN[OF planarG that(1)]
      that(2) by simp
  have IHF: "\<not> Moebius_path (WalkupF G z) q'" if "z \<in> D" "set q' \<subseteq> D - {z}" for z q'
    using less.hyps[of "WalkupF G z" q'] small[OF that(1)] hypermap_WalkupF planar_WalkupF[OF planarG that(1)]
      that(2) by simp
  interpret HE: hypermap "WalkupE G z" for z by (rule hypermap_WalkupE)
  interpret HN: hypermap "WalkupN G z" for z by (rule hypermap_WalkupN)
  interpret HF: hypermap "WalkupF G z" for z by (rule hypermap_WalkupF)
  show ?case
  proof
    assume M: "Moebius_path G q"
    then obtain x p where q: "q = x # p" by (cases q) (auto simp: Moebius_path_def)
    let ?L = "lastd x p"
    define t where "t = inv n ?L"
    have nt: "n t = ?L" by (simp add: t_def)
    have dist: "distinct (x # p)" and pth: "path (clink G) x p" and m2: "mem2 p t (n x)"
      using M q by (auto simp: Moebius_path_def t_def)
    have qD: "set (x # p) \<subseteq> D" using less.prems q by simp
    have tp: "t \<in> set p" and nxp: "n x \<in> set p" using m2 by (auto dest: mem2_l mem2_r)
    have pne: "p \<noteq> []" using tp by auto
    have Lp: "?L \<in> set p" using pne by simp
    \<comment> \<open>Step 1: every dart lies on the path.\<close>
    have allD: "D \<subseteq> set (x # p)"
    proof
      fix z assume zD: "z \<in> D"
      show "z \<in> set (x # p)"
      proof (rule ccontr)
        assume zq: "z \<notin> set (x # p)"
        have "Moebius_path (WalkupE G z) (x # p)"
        proof (rule Moebius_pathI[OF hypermap_WalkupE dist])
          show "path (clink (WalkupE G z)) x p"
            by (rule path_lift[OF _ pth]) (use zq in \<open>auto intro: clink_liftE\<close>)
          show "node (WalkupE G z) t = ?L"
            using tp zq nt Lp by (auto simp: skip_def)
          show "mem2 p t (node (WalkupE G z) x)"
            using m2 zq nxp by (auto simp: skip_def)
        qed
        then show False using IHE[OF zD] qD zq by blast
      qed
    qed
    obtain y p1 where p: "p = y # p1" using pne by (cases p) auto
    have xy: "x \<noteq> y" using dist p by auto
    have xt: "x \<noteq> t" using dist tp by auto
    have ntx: "n t \<noteq> x" using nt Lp dist by auto
    have p1ne: "p1 \<noteq> []"
    proof
      assume p1: "p1 = []"
      then have "t = y" "n x = y" using m2 p by (auto simp: mem2_Cons split: if_splits)
      moreover have "n t = y" using nt p p1 by simp
      ultimately have "n x = n y" by simp
      then show False using xy by simp
    qed
    obtain z p2 where p1: "p1 = z # p2" using p1ne by (cases p1) auto
    have yL: "y \<noteq> ?L" using dist p p1 by (auto simp: last_in_set)
    have dxyz: "distinct (x # y # z # p2)" using dist p p1 by simp
    have Lz: "?L = lastd z p2" using p p1 by simp
    \<comment> \<open>Step 2: face x = y.\<close>
    have Dfx: "f x = y"
    proof (rule ccontr)
      assume fxy: "f x \<noteq> y"
      then have xny: "x = n y" using pth p by (simp add: clink_def)
      have "Moebius_path (WalkupE G x) (y # p1)"
      proof (rule Moebius_pathI[OF hypermap_WalkupE])
        show "distinct (y # p1)" using dist p by simp
        show "path (clink (WalkupE G x)) y p1"
          by (rule path_lift) (use pth p dist in \<open>auto intro: clink_liftE\<close>)
        show "node (WalkupE G x) t = lastd y p1"
          using xt ntx nt p by (simp add: skip_def)
        have "t \<noteq> y" using ntx xny by auto
        then show "mem2 p1 t (node (WalkupE G x) y)"
          using m2 p xny xy by (simp add: skip_def mem2_Cons)
      qed
      moreover have "set (y # p1) \<subseteq> D - {x}" using qD dist p by auto
      ultimately show False using IHE qD by auto
    qed
    \<comment> \<open>Step 3: face y = z.\<close>
    have Dfy: "f y = z"
    proof (rule ccontr)
      assume fyz: "f y \<noteq> z"
      then have ynz: "y = n z" using pth p p1 by (simp add: clink_def)
      have fyy: "f y \<noteq> y" using F.img_neq[OF Dfx, of y] xy by auto
      have nyy: "n y \<noteq> y" using N.img_neq[OF ynz[symmetric], of y] dxyz by auto
      define t' where "t' = (if t = y then z else t)"
      have fx': "skip_edge (permF G) y x = z"
        using Dfx xy fyy nyy ynz nodeK[of z] by (simp add: skip_edge_permF)
      have "Moebius_path (WalkupF G y) (x # z # p2)"
      proof (rule Moebius_pathI[OF hypermap_WalkupF])
        show "distinct (x # z # p2)" using dxyz by auto
        have "path (clink (WalkupF G y)) z p2"
          by (rule path_lift) (use pth p p1 dxyz nodeK[of z] ynz in \<open>auto intro!: clink_liftF\<close>)
        then show "path (clink (WalkupF G y)) x (z # p2)"
          using fx' by (simp add: clink_def)
        show "node (WalkupF G y) t' = lastd x (z # p2)"
          using nt ynz yL Lz by (auto simp: t'_def skip_def p p1)
        have nxy: "n x \<noteq> y"
        proof
          assume "n x = y"
          then have "n x = n z" using ynz by simp
          then have "x = z" by simp
          then show False using dxyz by simp
        qed
        have sx: "node (WalkupF G y) x = n x" using xy nxy by (simp add: skip_def)
        show "mem2 (z # p2) t' (node (WalkupF G y) x)"
        proof (cases "t = y")
          case True
          then have "n x \<in> set (y # z # p2)" using m2 p p1 by (simp add: mem2_Cons)
          then have "n x \<in> set (z # p2)" using nxy by simp
          then show ?thesis using True sx by (simp add: t'_def mem2_Cons)
        next
          case False
          then have "mem2 (z # p2) t (n x)" using m2 p p1 by (simp add: mem2_Cons)
          then show ?thesis using False sx by (simp add: t'_def)
        qed
      qed
      moreover have "set (x # z # p2) \<subseteq> D - {y}" using qD dxyz p p1 by auto
      ultimately show False using IHF qD p p1 by auto
    qed
    \<comment> \<open>Step 4: t = y.\<close>
    have Dt: "t = y"
    proof (rule ccontr)
      assume ty: "t \<noteq> y"
      have m2': "mem2 (z # p2) t (n x)" using m2 ty p p1 by (simp add: mem2_Cons)
      have nxy: "n x \<noteq> y" using m2' dxyz by (auto dest: mem2_r)
      have "Moebius_path (WalkupE G y) (x # z # p2)"
      proof (rule Moebius_pathI[OF hypermap_WalkupE])
        show "distinct (x # z # p2)" using dxyz by auto
        have "path (clink (WalkupE G y)) z p2"
          by (rule path_lift) (use pth p p1 dxyz in \<open>auto intro!: clink_liftE\<close>)
        then show "path (clink (WalkupE G y)) x (z # p2)"
          using Dfx Dfy xy by (simp add: clink_def skip_def)
        show "node (WalkupE G y) t = lastd x (z # p2)"
          using nt ty yL Lz by (simp add: skip_def p p1)
        show "mem2 (z # p2) t (node (WalkupE G y) x)"
          using m2' nxy xy by (simp add: skip_def)
      qed
      moreover have "set (x # z # p2) \<subseteq> D - {y}" using qD dxyz p p1 by auto
      ultimately show False using IHE qD p p1 by auto
    qed
    have ny: "n y = ?L" using nt Dt by simp
    \<comment> \<open>Step 5: node x = y.\<close>
    have Dnx: "n x = y"
    proof (rule ccontr)
      assume nxy: "n x \<noteq> y"
      have nxz: "n x \<in> set (z # p2)" using m2 Dt nxy p p1 by (simp add: mem2_Cons)
      have nyy: "n y \<noteq> y" using ny yL by simp
      have enz: "e (n z) = y" using Dfy faceK[of y] by simp
      have nz': "skip_edge (permN G) y z = n y"
        using dxyz nyy enz by (auto simp: skip_edge_permN)
      have enx: "e (n x) \<noteq> y"
      proof
        assume "e (n x) = y"
        then have "e (n x) = e (n z)" using enz by simp
        then have "x = z" by simp
        then show False using dxyz by simp
      qed
      have nx': "skip_edge (permN G) y x = n x"
        using xy nyy enx nxy by (simp add: skip_edge_permN)
      have "Moebius_path (WalkupN G y) (x # z # p2)"
      proof (rule Moebius_pathI[OF hypermap_WalkupN])
        show "distinct (x # z # p2)" using dxyz by auto
        have "path (clink (WalkupN G y)) z p2"
          by (rule path_lift) (use pth p p1 dxyz Dfy in \<open>auto intro!: clink_liftN\<close>)
        then show "path (clink (WalkupN G y)) x (z # p2)"
          using Dfx Dfy xy by (simp add: clink_def skip_def)
        show "node (WalkupN G y) z = lastd x (z # p2)"
          using nz' ny Lz by (simp add: p p1)
        show "mem2 (z # p2) z (node (WalkupN G y) x)"
          using nx' nxz by (simp add: mem2_Cons)
      qed
      moreover have "set (x # z # p2) \<subseteq> D - {y}" using qD dxyz p p1 by auto
      ultimately show False using IHN qD p p1 by auto
    qed
    show False
    proof (cases p2)
      case Nil
      \<comment> \<open>Step 6: a three-dart map would have genus 1.\<close>
      have Dset: "D = {x, y, z}" using allD qD p p1 Nil by auto
      have nyz: "n y = z" using ny p p1 Nil by simp
      have fz: "f z = x"
      proof -
        have "z \<in> D" using Dset by simp
        then have "f z \<in> D" by simp
        moreover have "f z \<noteq> y" using F.img_neq[OF Dfx, of z] dxyz by auto
        moreover have "f z \<noteq> z" using F.img_neq[OF Dfy, of z] dxyz by auto
        ultimately show ?thesis using Dset by auto
      qed
      have nz: "n z = x"
      proof -
        have "z \<in> D" using Dset by simp
        then have "n z \<in> D" by simp
        moreover have "n z \<noteq> y" using N.img_neq[OF Dnx, of z] dxyz by auto
        moreover have "n z \<noteq> z" using N.img_neq[OF nyz, of z] dxyz by auto
        ultimately show ?thesis using Dset by auto
      qed
      have ex: "e x = y" using edge_eq_iff[of x y] Dfy nz by simp
      have ey: "e y = z" using edge_eq_iff[of y z] fz Dnx by simp
      have ez: "e z = x" using edge_eq_iff[of z x] Dfx nyz by simp
      have dd: "x \<noteq> y" "y \<noteq> z" "x \<noteq> z" using dxyz by auto
      have one: "fcard g D = 1" if gp: "fperm g D" and gx: "g x = y" and gy: "g y = z" for g
      proof -
        interpret fperm g D by (rule gp)
        have c1: "fconnect g x y" using fconnect_step[of g x] gx by simp
        have c2: "fconnect g x z" using fconnect_stepI_r[OF c1] gy by simp
        have cw: "cyc g w = cyc g x" if "w \<in> D" for w
        proof -
          have "fconnect g x w" using that Dset c1 c2 by auto
          then show ?thesis by (simp add: cyc_eq)
        qed
        have "cyc g ` D = {cyc g x}"
        proof
          show "cyc g ` D \<subseteq> {cyc g x}" using cw by blast
          show "{cyc g x} \<subseteq> cyc g ` D" using Dset by blast
        qed
        then show ?thesis by (simp add: fcard_def)
      qed
      have fcE: "fcard e D = 1" using one[OF E.fperm_axioms ex ey] .
      have fcN: "fcard n D = 1" using one[OF N.fperm_axioms Dnx nyz] .
      have fcF: "fcard f D = 1" using one[OF F.fperm_axioms Dfx Dfy] .
      have "glink G x y" using Dfx by (simp add: glink_def)
      then have gy: "gcomp G x y" by (rule r_into_rtranclp)
      have "glink G y z" using Dfy by (simp add: glink_def)
      then have gz: "gcomp G x z" by (rule rtranclp.rtrancl_into_rtrancl[OF gy])
      have cw: "comp_of (glink G) w = comp_of (glink G) x" if "w \<in> D" for w
      proof -
        have "gcomp G x w" using that Dset gy gz by auto
        then show ?thesis by (simp add: comp_eq)
      qed
      have "comp_of (glink G) ` D = {comp_of (glink G) x}"
      proof
        show "comp_of (glink G) ` D \<subseteq> {comp_of (glink G) x}" using cw by blast
        show "{comp_of (glink G) x} \<subseteq> comp_of (glink G) ` D" using Dset by blast
      qed
      then have "n_comp (glink G) D = 1" by (simp add: n_comp_def)
      moreover have "card D = 3" using Dset dd by simp
      ultimately have "genus G = 1"
        using fcE fcN fcF by (simp add: genus_def Euler_lhs_def Euler_rhs_def)
      then show False using planarG by (simp add: planar_def)
    next
      case (Cons w p3)
      have dxyzw: "distinct (x # y # z # w # p3)" using dxyz Cons by simp
      have nyz: "n y \<noteq> z" using ny dxyzw Lz Cons by (auto simp: last_in_set)
      have Lw: "?L = lastd w p3" using Lz Cons by simp
      \<comment> \<open>Step 7: node w = z.\<close>
      have Dnw: "n w = z"
      proof (rule ccontr)
        assume nwz: "n w \<noteq> z"
        then have fzw: "f z = w" using pth p p1 Cons by (simp add: clink_def)
        have "Moebius_path (WalkupE G z) (x # y # w # p3)"
        proof (rule Moebius_pathI[OF hypermap_WalkupE])
          show "distinct (x # y # w # p3)" using dxyzw by auto
          have "path (clink (WalkupE G z)) w p3"
            by (rule path_lift) (use pth p p1 Cons dxyzw in \<open>auto intro!: clink_liftE\<close>)
          then show "path (clink (WalkupE G z)) x (y # w # p3)"
            using Dfx Dfy fzw dxyzw by (simp add: clink_def skip_def)
          show "node (WalkupE G z) y = lastd x (y # w # p3)"
            using ny nyz Lw dxyzw by (simp add: skip_def)
          show "mem2 (y # w # p3) y (node (WalkupE G z) x)"
            using Dnx dxyzw by (simp add: skip_def mem2_Cons)
        qed
        moreover have "set (x # y # w # p3) \<subseteq> D - {z}" using qD dxyzw p p1 Cons by auto
        ultimately show False using IHE qD p p1 by auto
      qed
      \<comment> \<open>Step 8: the final WalkupF contradiction.\<close>
      have fzz: "f z \<noteq> z" using F.img_neq[OF Dfy, of z] dxyzw by auto
      have nzz: "n z \<noteq> z" using N.img_neq[OF Dnw, of z] dxyzw by auto
      have fez: "f (e z) = w" using edgeK[of z] Dnw N.eq_iff[of "f (e z)" w] by simp
      have fx': "skip_edge (permF G) z x = y"
        using Dfx dxyzw fzz ny nyz Lw by (simp add: skip_edge_permF)
      have fy': "skip_edge (permF G) z y = w"
        using Dfy dxyzw fzz nzz fez by (simp add: skip_edge_permF)
      have "Moebius_path (WalkupF G z) (x # y # w # p3)"
      proof (rule Moebius_pathI[OF hypermap_WalkupF])
        show "distinct (x # y # w # p3)" using dxyzw by auto
        have "path (clink (WalkupF G z)) w p3"
          by (rule path_lift) (use pth p p1 Cons dxyzw fez in \<open>auto intro!: clink_liftF\<close>)
        then show "path (clink (WalkupF G z)) x (y # w # p3)"
          using fx' fy' by (simp add: clink_def)
        show "node (WalkupF G z) y = lastd x (y # w # p3)"
          using ny nyz Lw dxyzw by (simp add: skip_def)
        show "mem2 (y # w # p3) y (node (WalkupF G z) x)"
          using Dnx dxyzw by (simp add: skip_def mem2_Cons)
      qed
      moreover have "set (x # y # w # p3) \<subseteq> D - {z}" using qD dxyzw p p1 Cons by auto
      ultimately show False using IHF qD p p1 by auto
    qed
  qed
qed

theorem planar_Jordan: "hypermap G \<Longrightarrow> planar G \<Longrightarrow> Jordan G"
  using planar_Jordan_aux by (auto simp: Jordan_def)

end
