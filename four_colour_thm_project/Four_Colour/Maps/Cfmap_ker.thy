(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Cfmap_ker.thy
    Configuration maps, part 5: the kernel of a configuration map (the inner faces
    created by H steps), simplicity and covering of ring + kernel, masks and the
    adjacency closure cpadj of a mask.
    Ported from G. Gonthier's Coq development (cfmap.v).
*)
theory Cfmap_ker
  imports Four_Colour_Maps.Cfmap_prog
begin

section \<open>Generic facts about simple sequences\<close>

context hypermap
begin

lemma simple_iff: "simple G p \<longleftrightarrow> distinct p \<and> (\<forall>a \<in> set p. \<forall>b \<in> set p. cface a b \<longrightarrow> a = b)"
  by (auto simp: simple_def distinct_map inj_on_def F.cyc_eq_iff)

lemma fband_set: "set p = set q \<Longrightarrow> fband G p = fband G q"
  by (simp add: fband_def fun_eq_iff)

end

lemma simple_mset: "mset p = mset q \<Longrightarrow> simple G p \<longleftrightarrow> simple G q"
  unfolding simple_def by (rule mset_eq_imp_distinct_iff) (simp add: mset_map)

lemma simple_transfer:
  assumes hH: "hypermap H" and hG: "hypermap G" and pA: "set p \<subseteq> A"
    and eq: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> fconnect (face H) a b \<longleftrightarrow> fconnect (face G) a b"
  shows "simple H p \<longleftrightarrow> simple G p"
  using pA eq by (auto simp: hypermap.simple_iff[OF hH] hypermap.simple_iff[OF hG] subset_iff)

lemma mset_rot: "mset (rot k s) = mset s"
  unfolding rot_def by (metis append_take_drop_id mset_append union_commute)

section \<open>The kernel\<close>

text \<open>Darts of a configuration map are preserved by the construction steps (the injections
  are identities), so the kernel is a list of darts of the final map.  For configuration
  programs the ring is always proper, so the dart added by an H step is the pointer.\<close>

fun cpker :: "cprog \<Rightarrow> nat list" where
  "cpker (CpR _ # cp) = cpker cp"
| "cpker (CpY # cp) = cpker cp"
| "cpker (CpH # cp) = cpx cp # cpker cp"
| "cpker _ = []"

definition cpksize :: "cprog \<Rightarrow> nat" where
  "cpksize cp = count_list cp CpH"

lemma size_cpker: "config_prog cp \<Longrightarrow> length (cpker cp) = cpksize cp"
  by (induction cp rule: config_prog.induct) (simp_all add: cpksize_def)

lemma config_prog_Cons_cases:
  assumes "config_prog (s # cp)"
  shows "(s = CpY \<and> (cp = [] \<or> config_prog cp)) \<or> ((\<exists>k. s = CpR k) \<and> config_prog cp) \<or>
         (s = CpH \<and> config_prog cp)"
  using assms by (cases s; cases cp) auto

lemma cpker_darts: "cp = [] \<or> config_prog cp \<Longrightarrow> set (cpker cp) \<subseteq> darts (cpG cp)"
proof (induction cp)
  case Nil then show ?case by simp
next
  case (Cons s cp)
  obtain G x where c: "cpmap cp = (G, x)" by (cases "cpmap cp")
  interpret E: ecp G x using hypermap_cpmap[of cp] cpx_in[of cp] c by (intro ecp_intro) simp_all
  have cpo: "config_prog (s # cp)" using Cons.prems by simp
  show ?case
  proof (cases s)
    case CpY
    have h: "cp = [] \<or> config_prog cp" using cpo CpY by (cases cp) auto
    interpret E2: ecp2 G x by (simp add: ecp2_def E.ecp_axioms)
    have "set (cpker cp) \<subseteq> E.D" using Cons.IH[OF h] c by simp
    then show ?thesis using CpY cpmap_Cons_cases(4)[OF c E2.ecp2_axioms] E2.darts_GY by auto
  next
    case (CpR k)
    then have h: "config_prog cp" using cpo by simp
    then show ?thesis using CpR Cons.IH c cpmap_Cons_cases(1)[OF c] by simp
  next
    case CpH
    then have h: "config_prog cp" using cpo by simp
    have pr: "proper_cpring G x" using cpmap_proper[OF config_prog_cubic[OF h]] c by simp
    interpret E3: ecp3 G x using E.hypermap_axioms E.x0D pr by (intro ecp3_intro)
    have "set (cpker cp) \<subseteq> E.D" using Cons.IH h c by simp
    then show ?thesis using CpH cpmap_H[OF c E3.ecp2h_axioms] E3.darts_GH E.x0D c by auto
  qed (use cpo in simp_all)
qed

lemma cpmap0_simple: "simple cpmap0 [0, 1]"
  by (auto simp: hypermap.simple_iff[OF hypermap_cpmap0] fconnect_def)

section \<open>Ring and kernel: simple and covering\<close>

lemma cpring_of_Nil: "cpring_of [] = [0, 1]"
  unfolding cpring_of_def by (simp only: cpmap.simps fst_conv snd_conv cpring0)

lemma cpmap_simple: "cp = [] \<or> config_prog cp \<Longrightarrow> simple (cpG cp) (cpring_of cp @ cpker cp)"
proof (induction cp)
  case Nil then show ?case using cpmap0_simple by (simp add: cpring_of_Nil)
next
  case (Cons s cp)
  obtain G x where c: "cpmap cp = (G, x)" by (cases "cpmap cp")
  interpret E: ecp G x using hypermap_cpmap[of cp] cpx_in[of cp] c by (intro ecp_intro) simp_all
  have cpo: "config_prog (s # cp)" using Cons.prems by simp
  have kD: "set (cpker cp) \<subseteq> E.D" if "cp = [] \<or> config_prog cp" using cpker_darts[OF that] c by simp
  have rD: "set (cpring G x) \<subseteq> E.D" by (rule E.ringD)
  show ?case
  proof (cases s)
    case (CpR k)
    then have h: "config_prog cp" using cpo by simp
    have IH: "simple G (cpring G x @ cpker cp)" using Cons.IH h c by (simp add: cpring_of_def)
    have "mset (rot k (cpring G x) @ cpker cp) = mset (cpring G x @ cpker cp)" by (simp add: mset_rot)
    then have "simple G (rot k (cpring G x) @ cpker cp)" using IH simple_mset by blast
    then show ?thesis using CpR cpmap_Cons_cases(1)[OF c] by (simp add: cpring_of_def E.cpring_ecpR)
  next
    case CpY
    have h: "cp = [] \<or> config_prog cp" using cpo CpY by (cases cp) auto
    interpret E2: ecp2 G x by (simp add: ecp2_def E.ecp_axioms)
    obtain r0 where hr: "cpring G x = node G x # r0" using E.head_cpring[of x] by blast
    define ker where "ker = cpker cp"
    define rest where "rest = r0 @ ker"
    have IH: "simple G (node G x # rest)"
      using Cons.IH[OF h] c hr by (simp add: cpring_of_def rest_def ker_def)
    have restD: "set rest \<subseteq> E.D" using kD[OF h] rD hr by (auto simp: rest_def ker_def)
    have nb: "\<not> fband G rest (node G x)" and srest: "simple G rest"
      using IH by (simp_all add: E.simple_Cons)
    have sY: "simple E2.GY rest"
      using srest simple_transfer[OF E2.T.NN.hypermap_axioms E.hypermap_axioms restD]
        E2.cface_GY_old by blast
    have ringY: "cpring E2.GY E2.XY = E.Xe # E2.XY # r0" using E2.cpring_GY hr by simp
    have "node E2.GY E2.XY = E.Xe"
      using E2.T.NN.head_cpring[of E2.XY] ringY by (metis list.inject)
    then have XeN: "fconnect (face E2.GY) E.Xe (node G x)" using E2.cface_node_GY by simp
    have n1: "\<not> fband E2.GY rest E2.XY"
      using restD E2.cface_GY_XY by (auto simp: fband_def subset_iff)
    have n2: "\<not> fband E2.GY (E2.XY # rest) E.Xe"
    proof
      assume "fband E2.GY (E2.XY # rest) E.Xe"
      then consider "fconnect (face E2.GY) E.Xe E2.XY" | w where "w \<in> set rest" "fconnect (face E2.GY) E.Xe w"
        by (auto simp: fband_def)
      then show False
      proof cases
        case 1
        then have "fconnect (face E2.GY) E2.XY E.Xe" by (rule E2.T.NN.F.fconnect_sym)
        then show False using E2.cface_GY_XY by simp
      next
        case (2 w)
        have wD: "w \<in> E.D" using 2(1) restD by blast
        have "fconnect (face E2.GY) (node G x) w"
          by (rule fconnect_trans[OF E2.T.NN.F.fconnect_sym[OF XeN] 2(2)])
        then have "fconnect (face G) (node G x) w" using E2.cface_GY_old[OF E.nx0D wD] by simp
        then show False using nb 2(1) by (auto simp: fband_def)
      qed
    qed
    have "simple E2.GY (E.Xe # E2.XY # rest)" using n1 n2 sY by (simp add: E2.T.NN.simple_Cons)
    then show ?thesis using CpY cpmap_Cons_cases(4)[OF c E2.ecp2_axioms] ringY
      by (simp add: cpring_of_def rest_def ker_def)
  next
    case CpH
    then have h: "config_prog cp" using cpo by simp
    have pr: "proper_cpring G x" using cpmap_proper[OF config_prog_cubic[OF h]] c by simp
    interpret E3: ecp3 G x using E.hypermap_axioms E.x0D pr by (intro ecp3_intro)
    define r2 where "r2 = drop 2 (cpring G x)"
    have hr: "cpring G x = node G x # x # r2" using E.head_proper_cpring[OF pr] by (simp add: r2_def)
    define ker where "ker = cpker cp"
    define rest where "rest = r2 @ x # ker"
    have IH0: "simple G (node G x # x # r2 @ ker)"
      using Cons.IH h c hr by (simp add: cpring_of_def ker_def)
    have "mset (node G x # x # r2 @ ker) = mset (node G x # rest)" by (simp add: rest_def)
    then have IH: "simple G (node G x # rest)" using IH0 simple_mset by blast
    have restD: "set rest \<subseteq> E.D" using kD h rD hr E.x0D by (auto simp: rest_def ker_def)
    have nb: "\<not> fband G rest (node G x)" and srest: "simple G rest"
      using IH by (simp_all add: E.simple_Cons)
    have sH: "simple E3.GH rest"
      using srest simple_transfer[OF E3.T2.NN.hypermap_axioms E.hypermap_axioms restD]
        E3.cface_GH_old by blast
    have ringH: "cpring E3.GH E3.XH = E.Xe # E3.XH # r2" using E3.cpring_GH by (simp add: r2_def)
    have "node E3.GH E3.XH = E.Xe"
      using E3.T2.NN.head_cpring[of E3.XH] ringH by (metis list.inject)
    then have XeN: "fconnect (face E3.GH) E.Xe (node G x)" using E3.cface_node_GH by simp
    have n1: "\<not> fband E3.GH rest E3.XH"
      using restD E3.cface_GH_XH by (auto simp: fband_def subset_iff)
    have n2: "\<not> fband E3.GH (E3.XH # rest) E.Xe"
    proof
      assume "fband E3.GH (E3.XH # rest) E.Xe"
      then consider "fconnect (face E3.GH) E.Xe E3.XH" | w where "w \<in> set rest" "fconnect (face E3.GH) E.Xe w"
        by (auto simp: fband_def)
      then show False
      proof cases
        case 1
        then have "fconnect (face E3.GH) E3.XH E.Xe" by (rule E3.T2.NN.F.fconnect_sym)
        then show False using E3.cface_GH_XH by simp
      next
        case (2 w)
        have wD: "w \<in> E.D" using 2(1) restD by blast
        have "fconnect (face E3.GH) (node G x) w"
          by (rule fconnect_trans[OF E3.T2.NN.F.fconnect_sym[OF XeN] 2(2)])
        then have "fconnect (face G) (node G x) w" using E3.cface_GH_old[OF E.nx0D wD] by simp
        then show False using nb 2(1) by (auto simp: fband_def)
      qed
    qed
    have "simple E3.GH (E.Xe # E3.XH # rest)" using n1 n2 sH by (simp add: E3.T2.NN.simple_Cons)
    then show ?thesis using CpH cpmap_H[OF c E3.ecp2h_axioms] ringH c
      by (simp add: cpring_of_def rest_def ker_def)
  qed (use cpo in simp_all)
qed

lemma cpmap_cover:
  "cp = [] \<or> config_prog cp \<Longrightarrow> u \<in> darts (cpG cp) \<Longrightarrow> fband (cpG cp) (cpring_of cp @ cpker cp) u"
proof (induction cp arbitrary: u)
  case Nil then show ?case by (auto simp: cpring_of_Nil fband_def)
next
  case (Cons s cp)
  obtain G x where c: "cpmap cp = (G, x)" by (cases "cpmap cp")
  interpret E: ecp G x using hypermap_cpmap[of cp] cpx_in[of cp] c by (intro ecp_intro) simp_all
  have cpo: "config_prog (s # cp)" using Cons.prems by simp
  show ?case
  proof (cases s)
    case (CpR k)
    then have h: "config_prog cp" using cpo by simp
    have uD: "u \<in> E.D" using Cons.prems CpR cpmap_Cons_cases(1)[OF c] by simp
    have "fband G (cpring G x @ cpker cp) u" using Cons.IH[of u] h c uD by (simp add: cpring_of_def)
    moreover have "set (rot k (cpring G x) @ cpker cp) = set (cpring G x @ cpker cp)" by simp
    ultimately show ?thesis using CpR cpmap_Cons_cases(1)[OF c]
      by (simp add: cpring_of_def E.cpring_ecpR fband_def)
  next
    case CpY
    have h: "cp = [] \<or> config_prog cp" using cpo CpY by (cases cp) auto
    interpret E2: ecp2 G x by (simp add: ecp2_def E.ecp_axioms)
    obtain r0 where hr: "cpring G x = node G x # r0" using E.head_cpring[of x] by blast
    have ringY: "cpring E2.GY E2.XY = E.Xe # E2.XY # r0" using E2.cpring_GY hr by simp
    have "node E2.GY E2.XY = E.Xe"
      using E2.T.NN.head_cpring[of E2.XY] ringY by (metis list.inject)
    then have XeN: "fconnect (face E2.GY) E.Xe (node G x)" using E2.cface_node_GY by simp
    have cpY: "cpmap (CpY # cp) = (E2.GY, E2.XY)" using CpY cpmap_Cons_cases(4)[OF c E2.ecp2_axioms] by simp
    have uY: "u \<in> darts E2.GY" using Cons.prems(2) unfolding CpY cpY by (simp only: fst_conv)
    define L where "L = E.Xe # E2.XY # r0 @ cpker cp"
    have "fband E2.GY L u"
    proof (cases "\<exists>y \<in> E.D. fconnect (face E2.GY) u y")
      case False
      then have "fconnect (face E2.GY) E2.XY u" using E2.fband_GY[OF uY] by blast
      then show ?thesis using E2.T.NN.F.fconnect_sym by (auto simp: fband_def L_def)
    next
      case True
      then obtain y where yD: "y \<in> E.D" and uy: "fconnect (face E2.GY) u y" by blast
      have "fband G (cpring G x @ cpker cp) y" using Cons.IH[OF h] c yD by (simp add: cpring_of_def)
      then obtain w where w: "w \<in> set (cpring G x @ cpker cp)" and yw: "fconnect (face G) y w"
        by (auto simp: fband_def)
      have wD: "w \<in> E.D" using w cpker_darts[OF h] c E.ringD by auto
      have "fconnect (face E2.GY) y w" using yw E2.cface_GY_old[OF yD wD] by simp
      then have uw: "fconnect (face E2.GY) u w" by (rule fconnect_trans[OF uy])
      show ?thesis
      proof (cases "w = node G x")
        case True
        then have "fconnect (face E2.GY) u (node G x)" using uw by simp
        then have "fconnect (face E2.GY) u E.Xe" by (rule fconnect_trans[OF _ E2.T.NN.F.fconnect_sym[OF XeN]])
        then show ?thesis by (auto simp: fband_def L_def)
      next
        case False
        then have "w \<in> set L" using w hr by (auto simp: L_def)
        then show ?thesis using uw by (auto simp: fband_def)
      qed
    qed
    then show ?thesis unfolding CpY cpring_of_def cpY fst_conv snd_conv ringY cpker.simps L_def by simp
  next
    case CpH
    then have h: "config_prog cp" using cpo by simp
    have pr: "proper_cpring G x" using cpmap_proper[OF config_prog_cubic[OF h]] c by simp
    interpret E3: ecp3 G x using E.hypermap_axioms E.x0D pr by (intro ecp3_intro)
    define r2 where "r2 = drop 2 (cpring G x)"
    have hr: "cpring G x = node G x # x # r2" using E.head_proper_cpring[OF pr] by (simp add: r2_def)
    have ringH: "cpring E3.GH E3.XH = E.Xe # E3.XH # r2" using E3.cpring_GH by (simp add: r2_def)
    have "node E3.GH E3.XH = E.Xe"
      using E3.T2.NN.head_cpring[of E3.XH] ringH by (metis list.inject)
    then have XeN: "fconnect (face E3.GH) E.Xe (node G x)" using E3.cface_node_GH by simp
    have cpH: "cpmap (CpH # cp) = (E3.GH, E3.XH)" using CpH cpmap_H[OF c E3.ecp2h_axioms] by simp
    have uH: "u \<in> darts E3.GH" using Cons.prems(2) unfolding CpH cpH by (simp only: fst_conv)
    define L where "L = E.Xe # E3.XH # r2 @ x # cpker cp"
    have "fband E3.GH L u"
    proof (cases "\<exists>y \<in> E.D. fconnect (face E3.GH) u y")
      case False
      then have "fconnect (face E3.GH) E3.XH u" using E3.fband_GH[OF uH] by blast
      then show ?thesis using E3.T2.NN.F.fconnect_sym by (auto simp: fband_def L_def)
    next
      case True
      then obtain y where yD: "y \<in> E.D" and uy: "fconnect (face E3.GH) u y" by blast
      have "fband G (cpring G x @ cpker cp) y" using Cons.IH h c yD by (simp add: cpring_of_def)
      then obtain w where w: "w \<in> set (cpring G x @ cpker cp)" and yw: "fconnect (face G) y w"
        by (auto simp: fband_def)
      have "set (cpker cp) \<subseteq> E.D" using cpker_darts[of cp] h c by simp
      then have wD: "w \<in> E.D" using w E.ringD by auto
      have "fconnect (face E3.GH) y w" using yw E3.cface_GH_old[OF yD wD] by simp
      then have uw: "fconnect (face E3.GH) u w" by (rule fconnect_trans[OF uy])
      show ?thesis
      proof (cases "w = node G x")
        case True
        then have "fconnect (face E3.GH) u (node G x)" using uw by simp
        then have "fconnect (face E3.GH) u E.Xe" by (rule fconnect_trans[OF _ E3.T2.NN.F.fconnect_sym[OF XeN]])
        then show ?thesis by (auto simp: fband_def L_def)
      next
        case False
        then have "w \<in> set L" using w hr by (auto simp: L_def)
        then show ?thesis using uw by (auto simp: fband_def)
      qed
    qed
    then show ?thesis unfolding CpH cpring_of_def cpH fst_conv snd_conv ringH cpker.simps L_def c snd_conv
      by simp
  qed (use cpo in simp_all)
qed

section \<open>Masks\<close>

fun mask :: "bool list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "mask (b # m) (x # s) = (if b then x # mask m s else mask m s)"
| "mask _ _ = []"

lemma set_mask_Cons: "set (mask (b # m) (x # s)) = (if b then insert x (set (mask m s)) else set (mask m s))"
  by simp

lemma set_mask_subset: "set (mask m s) \<subseteq> set s"
  by (induction m s rule: mask.induct) auto

lemma mask_append:
  "length m1 = length s1 \<Longrightarrow> mask (m1 @ m2) (s1 @ s2) = mask m1 s1 @ mask m2 s2"
  by (induction m1 s1 rule: mask.induct) auto

lemma mask_replicate_False [simp]: "mask (replicate k False) s = []"
  by (induction k arbitrary: s) (auto, case_tac s, auto)

lemma mask_true: "length m = length s \<Longrightarrow> (\<forall>b \<in> set m. b) \<Longrightarrow> mask m s = s"
  by (induction m s rule: mask.induct) auto

lemma mask_pick:
  "mask (map (\<lambda>j. j = i) [k..<k + length s]) s = (if k \<le> i \<and> i < k + length s then [s ! (i - k)] else [])"
proof (induction s arbitrary: k)
  case Nil then show ?case by simp
next
  case (Cons x s)
  have u: "[k..<k + length (x # s)] = k # [Suc k..<Suc k + length s]" by (simp add: upt_rec)
  have "mask (map (\<lambda>j. j = i) [Suc k..<Suc k + length s]) s = []" if "i \<le> k"
    using Cons[of "Suc k"] that by simp
  then show ?case using Cons[of "Suc k"] unfolding u
    by (auto simp: nth_Cons' Suc_diff_Suc not_less_eq_eq)
qed

definition rotr :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rotr k s = rot (length s - k) s"

lemma length_rot [simp]: "length (rot k s) = length s"
  by (simp add: rot_def)

lemma length_rotr [simp]: "length (rotr k s) = length s"
  by (simp add: rotr_def)

lemma rot_rotr: "rot k (rotr k s) = s"
proof (cases "k \<le> length s")
  case True
  have "rot k (rotr k s) = rotate k (rotate (length s - k) s)"
    using True by (simp add: rotr_def rot_rotate)
  also have "\<dots> = rotate (length s) s" using True by (simp add: rotate_rotate)
  finally show ?thesis by simp
next
  case False
  then show ?thesis by (simp add: rotr_def rot_oversize)
qed

lemma set_mask_rot:
  assumes "length m = length s"
  shows "set (mask (rot k m) (rot k s)) = set (mask m s)"
proof (cases "k \<le> length s")
  case True
  have "mask (rot k m) (rot k s) = mask (drop k m) (drop k s) @ mask (take k m) (take k s)"
    using assms by (simp add: rot_def mask_append)
  moreover have "mask m s = mask (take k m) (take k s) @ mask (drop k m) (drop k s)"
    using assms mask_append[of "take k m" "take k s" "drop k m" "drop k s"] by simp
  ultimately show ?thesis by auto
next
  case False
  then show ?thesis using assms by (simp add: rot_oversize)
qed

datatype cfmask = Cfmask "bool list" "bool list"

fun proper_cpmask :: "cprog \<Rightarrow> cfmask \<Rightarrow> bool" where
  "proper_cpmask cp (Cfmask mr mk) \<longleftrightarrow> length mr = cprsize cp \<and> length mk = cpksize cp"

fun cpmask :: "cfmask \<Rightarrow> cprog \<Rightarrow> nat list" where
  "cpmask (Cfmask mr mk) cp = mask mr (cpring_of cp) @ mask mk (cpker cp)"

definition cfmask1 :: "cprog \<Rightarrow> nat \<Rightarrow> cfmask" where
  "cfmask1 cp i = Cfmask (replicate (cprsize cp) False) (map (\<lambda>j. j = i) [0..<cpksize cp])"

lemma proper_cpmask1: "proper_cpmask cp (cfmask1 cp i)"
  by (simp add: cfmask1_def)

lemma cpmask1:
  assumes "i < cpksize cp" "config_prog cp"
  shows "cpmask (cfmask1 cp i) cp = [cpker cp ! i]"
  using mask_pick[of i 0 "cpker cp"] assms size_cpker[OF assms(2)] by (simp add: cfmask1_def)

text \<open>The adjacency closure of a mask: @{term "cpadj cm cp"} selects the faces adjacent to
  a face selected by @{term cm}.\<close>

fun cpadj :: "cfmask \<Rightarrow> cprog \<Rightarrow> cfmask" where
  "cpadj (Cfmask mr mk) (CpR k # cp) =
     (case cpadj (Cfmask (rotr k mr) mk) cp of Cfmask mr' mk' \<Rightarrow> Cfmask (rot k mr') mk')"
| "cpadj (Cfmask (b0 # b1 # b2 # mr) mk) (CpY # cp) =
     (case cpadj (Cfmask (b0 # b2 # mr) mk) cp of
        Cfmask (a0 # a2 # mr') mk' \<Rightarrow> Cfmask ((a0 \<or> b1) # (b0 \<or> b2) # (a2 \<or> b1) # mr') mk'
      | _ \<Rightarrow> Cfmask (b0 # b1 # b2 # mr) mk)"
| "cpadj (Cfmask (b0 # b1 # mr) (b1' # mk)) (CpH # cp) =
     (case cpadj (Cfmask (b0 # b1' # mr) mk) cp of
        Cfmask (a0 # a1 # mr') mk' \<Rightarrow>
          Cfmask ((a0 \<or> b1) # (b0 \<or> b1' \<or> (case mr of [] \<Rightarrow> b0 | h # _ \<Rightarrow> h))
                  # (case mr' of [] \<Rightarrow> [] | a2 # mr'' \<Rightarrow> (a2 \<or> b1) # mr''))
                 ((a1 \<or> b1) # mk')
      | _ \<Rightarrow> Cfmask (b0 # b1 # mr) (b1' # mk))"
| "cpadj (Cfmask [b0, b1] []) [] = Cfmask [b1, b0] []"
| "cpadj cm _ = cm"

lemma cpadj_proper: "proper_cpmask cp cm \<Longrightarrow> proper_cpmask cp (cpadj cm cp)"
proof (induction cm cp rule: cpadj.induct)
  case (1 mr mk k cp)
  then show ?case by (auto simp: cpksize_def split: cfmask.splits)
next
  case (2 b0 b1 b2 mr mk cp)
  then show ?case by (auto simp: cpksize_def split: cfmask.splits list.splits)
next
  case (3 b0 b1 mr b1' mk cp)
  then show ?case by (auto simp: cpksize_def split: cfmask.splits list.splits)
qed simp_all

section \<open>Adjacency closure correctness\<close>

lemma fband_mask_Cons:
  "fband H (mask (b # m) (x # s)) u \<longleftrightarrow> (b \<and> fconnect (face H) u x) \<or> fband H (mask m s) u"
  by (auto simp: fband_def)

lemma fband_app: "fband H (p @ q) u \<longleftrightarrow> fband H p u \<or> fband H q u"
  by (auto simp: fband_def)

lemma bex_mask_Cons:
  "(\<exists>y \<in> set (mask (b # m) (x # s)). P y) \<longleftrightarrow> (b \<and> P x) \<or> (\<exists>y \<in> set (mask m s). P y)"
  by auto

lemma bex_Un_mask_Cons:
  "(\<exists>y \<in> set (mask (b # m) (x # s)) \<union> B. P y) \<longleftrightarrow> (b \<and> P x) \<or> (\<exists>y \<in> set (mask m s) \<union> B. P y)"
  by auto

lemma fband_transfer:
  assumes "set l \<subseteq> A" "u \<in> A"
    and "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> fconnect (face H) a b \<longleftrightarrow> fconnect (face G) a b"
  shows "fband H l u \<longleftrightarrow> fband G l u"
proof -
  have "\<forall>y \<in> set l. fconnect (face H) u y \<longleftrightarrow> fconnect (face G) u y" using assms by blast
  then show ?thesis unfolding fband_def by blast
qed

lemma bex_transfer:
  assumes "set l \<subseteq> A" "\<And>y. y \<in> A \<Longrightarrow> P y \<longleftrightarrow> Q y"
  shows "(\<exists>y \<in> set l. P y) \<longleftrightarrow> (\<exists>y \<in> set l. Q y)"
  using assms by blast

lemma length_Suc_Suc_conv:
  "length l = Suc (Suc k) \<Longrightarrow> \<exists>a b l'. l = a # b # l' \<and> length l' = k"
  by (metis length_Suc_conv)

lemma cpmask_adj:
  "cp = [] \<or> config_prog cp \<Longrightarrow> proper_cpmask cp cm \<Longrightarrow> u \<in> darts (cpG cp) \<Longrightarrow>
   fband (cpG cp) (cpmask (cpadj cm cp) cp) u \<longleftrightarrow> (\<exists>y \<in> set (cpmask cm cp). adj (cpG cp) u y)"
proof (induction cp arbitrary: cm u)
  case Nil
  obtain mr mk where cm: "cm = Cfmask mr mk" by (cases cm)
  have "length mr = 2" "mk = []" using Nil.prems(2) by (simp_all add: cm cpksize_def)
  then obtain b0 b1 where mr: "mr = [b0, b1]" by (metis length_Suc_Suc_conv length_0_conv numeral_2_eq_2)
  have u: "u = 0 \<or> u = 1" using Nil.prems(3) by simp
  have adj0: "adj cpmap0 v y \<longleftrightarrow> y = sw01 v" for v y
    by (auto simp: adj_def rlink_def fconnect_def)
  show ?case using u
    by (auto simp: cm mr \<open>mk = []\<close> cpring_of_Nil fband_def fconnect_def adj0 sw01_def)
next
  case (Cons s cp)
  obtain G x where c: "cpmap cp = (G, x)" by (cases "cpmap cp")
  interpret E: ecp G x using hypermap_cpmap[of cp] cpx_in[of cp] c by (intro ecp_intro) simp_all
  have cpo: "config_prog (s # cp)" using Cons.prems by simp
  obtain mr mk where cm: "cm = Cfmask mr mk" by (cases cm)
  show ?case
  proof (cases s)
    case (CpR k)
    then have h: "config_prog cp" using cpo by simp
    have cpR: "cpmap (CpR k # cp) = (G, E.ecpR_ptr k x)" by (rule cpmap_Cons_cases(1)[OF c])
    define r where "r = cpring G x"
    have ringR: "cpring_of (CpR k # cp) = rot k r" using cpR by (simp add: cpring_of_def E.cpring_ecpR r_def)
    have lr: "length r = cprsize cp" using size_ring_cpmap[of cp] c by (simp add: cpring_of_def r_def)
    have lmr: "length mr = length r" and lmk: "length mk = cpksize cp"
      using Cons.prems(2) CpR lr by (simp_all add: cm cpksize_def)
    define cm0 where "cm0 = Cfmask (rotr k mr) mk"
    have pr0: "proper_cpmask cp cm0" using lmr lmk lr by (simp add: cm0_def)
    obtain mr' mk' where ca: "cpadj cm0 cp = Cfmask mr' mk'" by (cases "cpadj cm0 cp")
    have lmr': "length mr' = length r" using cpadj_proper[OF pr0] ca lr by simp
    have uG: "u \<in> E.D" using Cons.prems(3) CpR cpR by simp
    have IH: "fband G (mask mr' r @ mask mk' (cpker cp)) u \<longleftrightarrow>
              (\<exists>y \<in> set (mask (rotr k mr) r @ mask mk (cpker cp)). adj G u y)"
      using Cons.IH[OF _ pr0, of u] h c uG ca by (simp add: cm0_def cpring_of_def r_def)
    have s1: "set (mask (rot k mr') (rot k r)) = set (mask mr' r)" by (rule set_mask_rot[OF lmr'])
    have s2: "set (mask mr (rot k r)) = set (mask (rotr k mr) r)"
      using set_mask_rot[of "rotr k mr" r k] lmr by (simp add: rot_rotr)
    have ad: "cpadj cm (CpR k # cp) = Cfmask (rot k mr') mk'" using ca by (simp add: cm cm0_def)
    show ?thesis using IH s1 s2 unfolding CpR ad unfolding cm cpmask.simps ringR cpker.simps cpR fst_conv
      by (simp add: fband_def)
  next
    case CpY
    have h: "cp = [] \<or> config_prog cp" using cpo CpY by (cases cp) auto
    have cq: "cubic_prog cp" using h config_prog_cubic by auto
    interpret E2: ecp2 G x by (simp add: ecp2_def E.ecp_axioms)
    have pr: "proper_cpring G x" using cpmap_proper[OF cq] c by simp
    define r2 where "r2 = drop 2 (cpring G x)"
    have hr: "cpring G x = node G x # x # r2" using E.head_proper_cpring[OF pr] by (simp add: r2_def)
    define ker where "ker = cpker cp"
    have kerD: "set ker \<subseteq> E.D" using cpker_darts[OF h] c by (simp add: ker_def)
    have r2D: "set r2 \<subseteq> E.D" using E.ringD hr by auto
    have lker: "length ker = cpksize cp" using h size_cpker by (auto simp: ker_def cpksize_def)
    have simpG: "simple G (node G x # x # r2 @ ker)"
      using cpmap_simple[OF h] c hr by (simp add: cpring_of_def ker_def)
    have sep: "\<not> fconnect (face G) y (node G x) \<and> \<not> fconnect (face G) y x" if "y \<in> set (r2 @ ker)" for y
      using simpG that unfolding E.simple_iff by auto
    have ringY: "cpring E2.GY E2.XY = E.Xe # E2.XY # x # r2" using E2.cpring_GY hr by simp
    have nY: "node E2.GY E2.XY = E.Xe" using E2.T.NN.head_cpring[of E2.XY] ringY by (metis list.inject)
    have XeN: "fconnect (face E2.GY) E.Xe (node G x)" using E2.cface_node_GY nY by simp
    have cpY: "cpmap (CpY # cp) = (E2.GY, E2.XY)" using CpY cpmap_Cons_cases(4)[OF c E2.ecp2_axioms] by simp
    have plY: "plain E2.GY" using E2.plain_GY cpmap_plain[OF cq] c by simp
    have lr: "cprsize cp = Suc (Suc (length r2))" using size_ring_cpmap[of cp] c hr by (simp add: cpring_of_def)
    have lmr: "length mr = Suc (Suc (Suc (length r2)))" and lmk: "length mk = cpksize cp"
      using Cons.prems(2) CpY lr by (simp_all add: cm cpksize_def)
    then obtain b0 b1 b2 mr2 where mr: "mr = b0 # b1 # b2 # mr2" and lmr2: "length mr2 = length r2"
      by (metis length_Suc_conv)
    define cm0 where "cm0 = Cfmask (b0 # b2 # mr2) mk"
    have pr0: "proper_cpmask cp cm0" using lmr2 lmk lr by (simp add: cm0_def)
    obtain ma mk' where ca: "cpadj cm0 cp = Cfmask ma mk'" by (cases "cpadj cm0 cp")
    have "length ma = Suc (Suc (length r2))" and lmk': "length mk' = cpksize cp"
      using cpadj_proper[OF pr0] ca lr by simp_all
    then obtain a0 a2 mr' where ma: "ma = a0 # a2 # mr'" and lmr': "length mr' = length r2"
      by (metis length_Suc_Suc_conv)
    have ad: "cpadj cm (CpY # cp) = Cfmask ((a0 \<or> b1) # (b0 \<or> b2) # (a2 \<or> b1) # mr') mk'"
      using ca by (simp add: cm mr cm0_def ma)
    define ml where "ml = mask mr' r2 @ mask mk' ker"
    define ml0 where "ml0 = mask mr2 r2 @ mask mk ker"
    have mlsub: "set ml \<subseteq> set (r2 @ ker)" "set ml0 \<subseteq> set (r2 @ ker)"
      using set_mask_subset[of mr' r2] set_mask_subset[of mk' ker] set_mask_subset[of mr2 r2]
        set_mask_subset[of mk ker] by (auto simp: ml_def ml0_def)
    have mlD: "set ml \<subseteq> E.D" "set ml0 \<subseteq> E.D" using mlsub r2D kerD by auto
    have IH: "((a0 \<and> fconnect (face G) v (node G x)) \<or> (a2 \<and> fconnect (face G) v x) \<or> fband G ml v) \<longleftrightarrow>
              ((b0 \<and> adj G v (node G x)) \<or> (b2 \<and> adj G v x) \<or> (\<exists>y \<in> set ml0. adj G v y))"
      if vD: "v \<in> E.D" for v
      using Cons.IH[OF h pr0, of v] c vD ca
      by (simp add: cm0_def ma cpring_of_def hr ker_def ml_def ml0_def fband_app fband_mask_Cons
          bex_mask_Cons bex_Un_mask_Cons del: mask.simps)
    define L where "L v \<longleftrightarrow> ((a0 \<or> b1) \<and> fconnect (face E2.GY) v E.Xe) \<or>
        ((b0 \<or> b2) \<and> fconnect (face E2.GY) v E2.XY) \<or> ((a2 \<or> b1) \<and> fconnect (face E2.GY) v x) \<or>
        fband E2.GY ml v" for v
    define R where "R v \<longleftrightarrow> (b0 \<and> adj E2.GY v E.Xe) \<or> (b1 \<and> adj E2.GY v E2.XY) \<or>
        (b2 \<and> adj E2.GY v x) \<or> (\<exists>y \<in> set ml0. adj E2.GY v y)" for v
    have goal: "?thesis \<longleftrightarrow> (L u \<longleftrightarrow> R u)"
      unfolding CpY ad unfolding cm mr cpmask.simps cpring_of_def cpY fst_conv snd_conv ringY cpker.simps
        ker_def[symmetric]
      by (simp only: fband_app fband_mask_Cons bex_mask_Cons set_append bex_Un L_def R_def ml_def ml0_def
          disj_assoc)
    have cY: "fconnect (face E2.GY) v t \<longleftrightarrow> fconnect (face E2.GY) w t"
      if "fconnect (face E2.GY) v w" for v w t
      using fconnect_trans[OF that] fconnect_trans[OF E2.T.NN.F.fconnect_sym[OF that]] by blast
    have invL: "L v \<longleftrightarrow> L w" if "fconnect (face E2.GY) v w" for v w
      using cY[OF that] E2.T.NN.fband_cface[OF that] unfolding L_def by simp
    have invR: "R v \<longleftrightarrow> R w" if "fconnect (face E2.GY) v w" for v w
      using E2.T.NN.adj_cface[OF that] unfolding R_def by simp
    have XY_old: "\<not> fconnect (face E2.GY) E2.XY v" if "v \<in> E.D" for v
      using E2.cface_GY_XY that by auto
    have old_XY: "\<not> fconnect (face E2.GY) v E2.XY" if "v \<in> E.D" for v
      using XY_old[OF that] E2.T.NN.F.fconnect_sym by blast
    have adjXY: "adj E2.GY E2.XY v \<longleftrightarrow> fconnect (face E2.GY) v (node G x) \<or> fconnect (face E2.GY) v x" for v
      using E2.adj_GY_XY[of v] by (simp add: fband_def)
    have caseXY: "L E2.XY \<longleftrightarrow> R E2.XY"
    proof -
      have l1: "\<not> fconnect (face E2.GY) E2.XY E.Xe" using E2.cface_GY_XY by simp
      have l2: "\<not> fband E2.GY ml E2.XY" using mlD XY_old by (auto simp: fband_def)
      have "L E2.XY \<longleftrightarrow> b0 \<or> b2" using l1 l2 XY_old[OF E.x0D] by (simp add: L_def)
      moreover have "adj E2.GY E2.XY E.Xe" using adjXY XeN by simp
      moreover have "\<not> adj E2.GY E2.XY E2.XY" using adjXY old_XY[OF E.nx0D] old_XY[OF E.x0D]
          E2.T.NN.F.fconnect_sym by blast
      moreover have "adj E2.GY E2.XY x" using adjXY by simp
      moreover have "\<not> adj E2.GY E2.XY y" if "y \<in> set ml0" for y
      proof -
        have yD: "y \<in> E.D" using that mlD by blast
        have "\<not> fconnect (face G) y (node G x) \<and> \<not> fconnect (face G) y x" using sep mlsub that by blast
        then show ?thesis using adjXY E2.cface_GY_old[OF yD E.nx0D] E2.cface_GY_old[OF yD E.x0D] by simp
      qed
      ultimately show ?thesis by (auto simp: R_def E2.T.NN.adj_sym[OF plY])
    qed
    have caseD: "L v \<longleftrightarrow> R v" if vD: "v \<in> E.D" for v
    proof -
      have f1: "fconnect (face E2.GY) v E.Xe \<longleftrightarrow> fconnect (face G) v (node G x)"
        using cY[OF XeN, of v] E2.cface_GY_old[OF vD E.nx0D] E2.T.NN.F.fconnect_commute by metis
      have f2: "fconnect (face E2.GY) v x \<longleftrightarrow> fconnect (face G) v x" by (rule E2.cface_GY_old[OF vD E.x0D])
      have f3: "fband E2.GY ml v \<longleftrightarrow> fband G ml v"
        by (rule fband_transfer[OF mlD(1) vD]) (rule E2.cface_GY_old)
      have a1: "adj E2.GY v E.Xe \<longleftrightarrow> adj G v (node G x)"
        using E2.T.NN.adj_cface_r[OF XeN, of v] E2.adj_GY_old[OF vD E.nx0D] by simp
      have a2: "adj E2.GY v E2.XY \<longleftrightarrow> fconnect (face G) v (node G x) \<or> fconnect (face G) v x"
        using E2.T.NN.adj_sym[OF plY, of v E2.XY] E2.T.NN.adj_sym[OF plY, of E2.XY v] adjXY[of v]
          E2.cface_GY_old[OF vD E.nx0D] f2 by blast
      have a3: "adj E2.GY v x \<longleftrightarrow> adj G v x" by (rule E2.adj_GY_old[OF vD E.x0D])
      have a4: "(\<exists>y \<in> set ml0. adj E2.GY v y) \<longleftrightarrow> (\<exists>y \<in> set ml0. adj G v y)"
        by (rule bex_transfer[OF mlD(2)]) (rule E2.adj_GY_old[OF vD])
      show ?thesis using IH[OF vD] f1 f2 f3 a1 a2 a3 a4 old_XY[OF vD] unfolding L_def R_def by blast
    qed
    have uY: "u \<in> darts E2.GY" using Cons.prems(3) unfolding CpY cpY by (simp only: fst_conv)
    have "L u \<longleftrightarrow> R u"
    proof (cases "\<exists>y \<in> E.D. fconnect (face E2.GY) u y")
      case True
      then obtain y where yD: "y \<in> E.D" and uy: "fconnect (face E2.GY) u y" by blast
      show ?thesis using invL[OF uy] invR[OF uy] caseD[OF yD] by simp
    next
      case False
      then have "fconnect (face E2.GY) E2.XY u" using E2.fband_GY[OF uY] by blast
      then have uy: "fconnect (face E2.GY) u E2.XY" by (rule E2.T.NN.F.fconnect_sym)
      show ?thesis using invL[OF uy] invR[OF uy] caseXY by simp
    qed
    then show ?thesis using goal by simp
  next
    case CpH
    then have h: "config_prog cp" using cpo by simp
    have cq: "cubic_prog cp" using h config_prog_cubic by auto
    have pr: "proper_cpring G x" using cpmap_proper[OF cq] c by simp
    interpret E3: ecp3 G x using E.hypermap_axioms E.x0D pr by (intro ecp3_intro)
    have lng: "long_cpring G x" using cfmap_long[OF h] c by simp
    define fex where "fex = face G (edge G x)"
    have fexD: "fex \<in> E.D" using E.x0D by (simp add: fex_def)
    define r3 where "r3 = drop 3 (cpring G x)"
    have hr: "cpring G x = node G x # x # fex # r3"
      using E.head_long_cpring[OF lng] by (simp add: r3_def fex_def)
    define ker where "ker = cpker cp"
    have kerD: "set ker \<subseteq> E.D" using cpker_darts[of cp] h c by (simp add: ker_def)
    have r3D: "set r3 \<subseteq> E.D" using E.ringD hr by auto
    have lker: "length ker = cpksize cp" using h size_cpker by (auto simp: ker_def cpksize_def)
    have simpG: "simple G (node G x # x # fex # r3 @ ker)"
      using cpmap_simple[of cp] h c hr by (simp add: cpring_of_def ker_def)
    have sep: "\<not> fconnect (face G) y (node G x) \<and> \<not> fconnect (face G) y x \<and> \<not> fconnect (face G) y fex"
      if "y \<in> set (r3 @ ker)" for y
      using simpG that unfolding E.simple_iff by auto
    have ringH: "cpring E3.GH E3.XH = E.Xe # E3.XH # fex # r3"
      using E3.cpring_GH hr by simp
    have nH: "node E3.GH E3.XH = E.Xe" using E3.T2.NN.head_cpring[of E3.XH] ringH by (metis list.inject)
    have XeN: "fconnect (face E3.GH) E.Xe (node G x)" using E3.cface_node_GH nH by simp
    have cpH: "cpmap (CpH # cp) = (E3.GH, E3.XH)" using CpH cpmap_H[OF c E3.ecp2h_axioms] by simp
    have plH: "plain E3.GH" using E3.plain_GH cpmap_plain[OF cq] c by simp
    have lr: "cprsize cp = Suc (Suc (Suc (length r3)))" using size_ring_cpmap[of cp] c hr
      by (simp add: cpring_of_def)
    have lmr: "length mr = Suc (Suc (Suc (length r3)))" and lmk: "length mk = Suc (cpksize cp)"
      using Cons.prems(2) CpH lr by (simp_all add: cm cpksize_def)
    then obtain b0 b1 c0 mr3 where mr: "mr = b0 # b1 # c0 # mr3" and lmr3: "length mr3 = length r3"
      by (metis length_Suc_conv)
    from lmk obtain b1' mk2 where mk: "mk = b1' # mk2" and lmk2: "length mk2 = cpksize cp"
      by (metis length_Suc_conv)
    define cm0 where "cm0 = Cfmask (b0 # b1' # c0 # mr3) mk2"
    have pr0: "proper_cpmask cp cm0" using lmr3 lmk2 lr by (simp add: cm0_def)
    obtain ma mk' where ca: "cpadj cm0 cp = Cfmask ma mk'" by (cases "cpadj cm0 cp")
    have "length ma = Suc (Suc (Suc (length r3)))" using cpadj_proper[OF pr0] ca lr by simp
    then obtain a0 a1 a2 mr'' where ma: "ma = a0 # a1 # a2 # mr''" by (metis length_Suc_conv)
    have ad: "cpadj cm (CpH # cp) =
        Cfmask ((a0 \<or> b1) # (b0 \<or> b1' \<or> c0) # (a2 \<or> b1) # mr'') ((a1 \<or> b1) # mk')"
      using ca by (simp add: cm mr mk cm0_def ma)
    have subs: "set (mask mr'' r3) \<subseteq> set (r3 @ ker)" "set (mask mk' ker) \<subseteq> set (r3 @ ker)"
      "set (mask mr3 r3) \<subseteq> set (r3 @ ker)" "set (mask mk2 ker) \<subseteq> set (r3 @ ker)"
      using set_mask_subset[of mr'' r3] set_mask_subset[of mk' ker] set_mask_subset[of mr3 r3]
        set_mask_subset[of mk2 ker] by auto
    have rkD: "set (r3 @ ker) \<subseteq> E.D" using r3D kerD by auto
    have IH: "((a0 \<and> fconnect (face G) v (node G x)) \<or> (a1 \<and> fconnect (face G) v x) \<or>
               (a2 \<and> fconnect (face G) v fex) \<or> fband G (mask mr'' r3) v \<or> fband G (mask mk' ker) v)
          \<longleftrightarrow> ((b0 \<and> adj G v (node G x)) \<or> (b1' \<and> adj G v x) \<or> (c0 \<and> adj G v fex) \<or>
               (\<exists>y \<in> set (mask mr3 r3). adj G v y) \<or> (\<exists>y \<in> set (mask mk2 ker). adj G v y))"
      if vD: "v \<in> E.D" for v
      using Cons.IH[OF _ pr0, of v] h c vD ca
      by (simp add: cm0_def ma cpring_of_def hr ker_def fband_app fband_mask_Cons
          bex_mask_Cons bex_Un_mask_Cons bex_Un del: mask.simps)
    define L where "L v \<longleftrightarrow> ((a0 \<or> b1) \<and> fconnect (face E3.GH) v E.Xe) \<or>
        ((b0 \<or> b1' \<or> c0) \<and> fconnect (face E3.GH) v E3.XH) \<or>
        ((a2 \<or> b1) \<and> fconnect (face E3.GH) v fex) \<or> fband E3.GH (mask mr'' r3) v \<or>
        ((a1 \<or> b1) \<and> fconnect (face E3.GH) v x) \<or> fband E3.GH (mask mk' ker) v" for v
    define R where "R v \<longleftrightarrow> (b0 \<and> adj E3.GH v E.Xe) \<or> (b1 \<and> adj E3.GH v E3.XH) \<or>
        (c0 \<and> adj E3.GH v fex) \<or> (\<exists>y \<in> set (mask mr3 r3). adj E3.GH v y) \<or>
        (b1' \<and> adj E3.GH v x) \<or> (\<exists>y \<in> set (mask mk2 ker). adj E3.GH v y)" for v
    have goal: "?thesis \<longleftrightarrow> (L u \<longleftrightarrow> R u)"
      unfolding CpH ad unfolding cm mr mk cpmask.simps cpring_of_def cpH fst_conv snd_conv ringH
        cpker.simps c ker_def[symmetric]
      by (simp only: fband_app fband_mask_Cons bex_mask_Cons set_append bex_Un L_def R_def disj_assoc)
    have cH: "fconnect (face E3.GH) v t \<longleftrightarrow> fconnect (face E3.GH) w t"
      if "fconnect (face E3.GH) v w" for v w t
      using fconnect_trans[OF that] fconnect_trans[OF E3.T2.NN.F.fconnect_sym[OF that]] by blast
    have invL: "L v \<longleftrightarrow> L w" if "fconnect (face E3.GH) v w" for v w
      using cH[OF that] E3.T2.NN.fband_cface[OF that] unfolding L_def by simp
    have invR: "R v \<longleftrightarrow> R w" if "fconnect (face E3.GH) v w" for v w
      using E3.T2.NN.adj_cface[OF that] unfolding R_def by simp
    have XH_old: "\<not> fconnect (face E3.GH) E3.XH v" if "v \<in> E.D" for v
      using E3.cface_GH_XH that by auto
    have old_XH: "\<not> fconnect (face E3.GH) v E3.XH" if "v \<in> E.D" for v
      using XH_old[OF that] E3.T2.NN.F.fconnect_sym by blast
    have adjXH: "adj E3.GH E3.XH v \<longleftrightarrow> fconnect (face E3.GH) v (node G x) \<or>
        fconnect (face E3.GH) v x \<or> fconnect (face E3.GH) v fex" for v
      using E3.adj_GH_XH[of v] by (simp add: fband_def fex_def)
    have oldf: "fconnect (face E3.GH) a b \<longleftrightarrow> fconnect (face G) a b" if "a \<in> E.D" "b \<in> E.D" for a b
      by (rule E3.cface_GH_old[OF that])
    have caseXH: "L E3.XH \<longleftrightarrow> R E3.XH"
    proof -
      have l1: "\<not> fconnect (face E3.GH) E3.XH E.Xe" using E3.cface_GH_XH by simp
      have l2: "\<not> fband E3.GH l E3.XH" if "set l \<subseteq> E.D" for l
        using that XH_old by (auto simp: fband_def)
      have mD: "set (mask mr'' r3) \<subseteq> E.D" "set (mask mk' ker) \<subseteq> E.D" using subs rkD by auto
      have "L E3.XH \<longleftrightarrow> b0 \<or> b1' \<or> c0"
        using l1 l2[OF mD(1)] l2[OF mD(2)] XH_old[OF fexD] XH_old[OF E.x0D]
        by (auto simp: L_def)
      moreover have "adj E3.GH E3.XH E.Xe" using adjXH XeN by simp
      moreover have "\<not> adj E3.GH E3.XH E3.XH"
        using adjXH old_XH[OF E.nx0D] old_XH[OF E.x0D] old_XH[OF fexD] E3.T2.NN.F.fconnect_sym by blast
      moreover have "adj E3.GH E3.XH x" "adj E3.GH E3.XH fex" using adjXH by simp_all
      moreover have noadj: "\<not> adj E3.GH E3.XH y" if "y \<in> set (r3 @ ker)" for y
      proof -
        have yD: "y \<in> E.D" using that rkD by blast
        show ?thesis using adjXH sep[OF that] oldf[OF yD E.nx0D] oldf[OF yD E.x0D] oldf[OF yD fexD] by simp
      qed
      moreover have "\<not> (\<exists>y \<in> set (mask mr3 r3). adj E3.GH E3.XH y)" using noadj subs(3) by blast
      moreover have "\<not> (\<exists>y \<in> set (mask mk2 ker). adj E3.GH E3.XH y)" using noadj subs(4) by blast
      ultimately show ?thesis unfolding R_def by (simp add: disj_commute disj_left_commute)
    qed
    have caseD: "L v \<longleftrightarrow> R v" if vD: "v \<in> E.D" for v
    proof -
      have f1: "fconnect (face E3.GH) v E.Xe \<longleftrightarrow> fconnect (face G) v (node G x)"
        using cH[OF XeN, of v] oldf[OF vD E.nx0D] E3.T2.NN.F.fconnect_commute by metis
      have f2: "fconnect (face E3.GH) v x \<longleftrightarrow> fconnect (face G) v x" by (rule oldf[OF vD E.x0D])
      have f2b: "fconnect (face E3.GH) v fex \<longleftrightarrow> fconnect (face G) v fex" by (rule oldf[OF vD fexD])
      have f3: "fband E3.GH (mask mr'' r3) v \<longleftrightarrow> fband G (mask mr'' r3) v"
        by (rule fband_transfer[OF _ vD]) (use subs rkD oldf in auto)
      have f4: "fband E3.GH (mask mk' ker) v \<longleftrightarrow> fband G (mask mk' ker) v"
        by (rule fband_transfer[OF _ vD]) (use subs rkD oldf in auto)
      have a1: "adj E3.GH v E.Xe \<longleftrightarrow> adj G v (node G x)"
        using E3.T2.NN.adj_cface_r[OF XeN, of v] E3.adj_GH_old[OF vD E.nx0D] by simp
      have a2: "adj E3.GH v E3.XH \<longleftrightarrow> fconnect (face G) v (node G x) \<or> fconnect (face G) v x \<or>
          fconnect (face G) v fex"
        using E3.T2.NN.adj_sym[OF plH, of v E3.XH] E3.T2.NN.adj_sym[OF plH, of E3.XH v] adjXH[of v]
          oldf[OF vD E.nx0D] f2 f2b by blast
      have a3: "adj E3.GH v x \<longleftrightarrow> adj G v x" by (rule E3.adj_GH_old[OF vD E.x0D])
      have a3b: "adj E3.GH v fex \<longleftrightarrow> adj G v fex" by (rule E3.adj_GH_old[OF vD fexD])
      have a4: "(\<exists>y \<in> set (mask mr3 r3). adj E3.GH v y) \<longleftrightarrow> (\<exists>y \<in> set (mask mr3 r3). adj G v y)"
        by (rule bex_transfer[of _ E.D]) (use subs rkD E3.adj_GH_old[OF vD] in auto)
      have a5: "(\<exists>y \<in> set (mask mk2 ker). adj E3.GH v y) \<longleftrightarrow> (\<exists>y \<in> set (mask mk2 ker). adj G v y)"
        by (rule bex_transfer[of _ E.D]) (use subs rkD E3.adj_GH_old[OF vD] in auto)
      have eL: "L v \<longleftrightarrow> ((a0 \<or> b1) \<and> fconnect (face G) v (node G x)) \<or>
          ((a2 \<or> b1) \<and> fconnect (face G) v fex) \<or> fband G (mask mr'' r3) v \<or>
          ((a1 \<or> b1) \<and> fconnect (face G) v x) \<or> fband G (mask mk' ker) v"
        unfolding L_def using f1 f2 f2b f3 f4 old_XH[OF vD] by simp
      have eR: "R v \<longleftrightarrow> (b0 \<and> adj G v (node G x)) \<or>
          (b1 \<and> (fconnect (face G) v (node G x) \<or> fconnect (face G) v x \<or> fconnect (face G) v fex)) \<or>
          (c0 \<and> adj G v fex) \<or> (\<exists>y \<in> set (mask mr3 r3). adj G v y) \<or>
          (b1' \<and> adj G v x) \<or> (\<exists>y \<in> set (mask mk2 ker). adj G v y)"
        unfolding R_def using a1 a2 a3 a3b a4 a5 by simp
      show ?thesis unfolding eL eR using IH[OF vD] by argo
    qed
    have uH: "u \<in> darts E3.GH" using Cons.prems(3) unfolding CpH cpH by (simp only: fst_conv)
    have "L u \<longleftrightarrow> R u"
    proof (cases "\<exists>y \<in> E.D. fconnect (face E3.GH) u y")
      case True
      then obtain y where yD: "y \<in> E.D" and uy: "fconnect (face E3.GH) u y" by blast
      show ?thesis using invL[OF uy] invR[OF uy] caseD[OF yD] by simp
    next
      case False
      then have "fconnect (face E3.GH) E3.XH u" using E3.fband_GH[OF uH] by blast
      then have uy: "fconnect (face E3.GH) u E3.XH" by (rule E3.T2.NN.F.fconnect_sym)
      show ?thesis using invL[OF uy] invR[OF uy] caseXH by simp
    qed
    then show ?thesis using goal by simp
  qed (use cpo in simp_all)
qed

end
