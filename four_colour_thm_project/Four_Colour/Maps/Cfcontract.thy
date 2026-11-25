(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Cfcontract.thy
    The contract of a configuration construction: a construction program whose ring
    colourings are the contract colourings of the original one.
    Ported from G. Gonthier's Coq development (cfcontract.v).
*)
theory Cfcontract
  imports Four_Colour_Maps.Cfmap_ker Four_Colour_Maps.Cfcolor
begin

section \<open>Kernel edges\<close>

fun ctrmsize :: "cprog \<Rightarrow> nat" where
  "ctrmsize (CpR _ # cp) = ctrmsize cp"
| "ctrmsize [CpY] = 0"
| "ctrmsize (CpY # cp) = Suc (ctrmsize cp)"
| "ctrmsize (CpH # cp) = ctrmsize cp + 3"
| "ctrmsize _ = 0"

fun ctrmask_rec :: "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool list" where
  "ctrmask_rec cci i 0 = []"
| "ctrmask_rec cci i (Suc k) = (i \<in> set cci) # ctrmask_rec cci (Suc i) k"

definition ctrmask :: "cprog \<Rightarrow> nat list \<Rightarrow> bool list" where
  "ctrmask cp cci = ctrmask_rec cci 0 (ctrmsize cp)"

lemma length_ctrmask_rec: "length (ctrmask_rec cci i k) = k"
  by (induction k arbitrary: i) simp_all

lemma size_ctrmask: "length (ctrmask cp cci) = ctrmsize cp"
  by (simp add: ctrmask_def length_ctrmask_rec)

text \<open>A transversal of the kernel edges, in reverse order of creation.  The injections
  being identities, the Y foot is @{term "node G x"} and the H darts are the crossbar
  @{term "face GH XH"} and the two feet @{term "node G x"}, @{term x}.\<close>

fun ctrenum :: "cprog \<Rightarrow> nat list" where
  "ctrenum (CpR _ # cp) = ctrenum cp"
| "ctrenum (CpY # cp) = (if cp = [] then [] else node (cpG cp) (cpx cp) # ctrenum cp)"
| "ctrenum (CpH # cp) = face (cpG (CpH # cp)) (cpx (CpH # cp)) # node (cpG cp) (cpx cp) # cpx cp # ctrenum cp"
| "ctrenum _ = []"

lemma size_ctrenum: "length (ctrenum cp) = ctrmsize cp"
  by (induction cp rule: ctrmsize.induct) simp_all

lemma insertE_app: "insertE G (p1 @ p2) = insertE G p1 @ insertE G p2"
  by (induction p1) simp_all

lemma insertE_cong: "(\<And>y. y \<in> set l \<Longrightarrow> edge H y = edge G y) \<Longrightarrow> insertE H l = insertE G l"
  by (induction l) auto

lemma insertE_rot: "mset (insertE G (rot k l)) = mset (insertE G l)"
  unfolding rot_def by (metis append_take_drop_id insertE_app mset_append union_commute)

lemma (in hypermap) insertE_D: "set l \<subseteq> D \<Longrightarrow> set (insertE G l) \<subseteq> D"
  by (induction l) auto

lemma ctrenum_darts: "q = [] \<or> config_prog q \<Longrightarrow> set (ctrenum q) \<subseteq> darts (cpG q)"
proof (induction q)
  case Nil then show ?case by simp
next
  case (Cons t q)
  obtain H y where cq: "cpmap q = (H, y)" by (cases "cpmap q")
  interpret F: ecp H y using hypermap_cpmap[of q] cpx_in[of q] cq by (intro ecp_intro) simp_all
  have qo: "config_prog (t # q)" using Cons.prems by simp
  show ?case
  proof (cases t)
    case (CpR k) then show ?thesis using Cons.IH qo cpmap_Cons_cases(1)[OF cq] cq by simp
  next
    case CpY
    have h: "q = [] \<or> config_prog q" using qo CpY by (cases q) auto
    interpret F2: ecp2 H y by (simp add: ecp2_def F.ecp_axioms)
    have "set (ctrenum q) \<subseteq> F.D" using Cons.IH[OF h] cq by simp
    then show ?thesis using CpY cpmap_Cons_cases(4)[OF cq F2.ecp2_axioms] F2.darts_GY F.nx0D cq
      by auto
  next
    case CpH
    then have h: "config_prog q" using qo by simp
    have pr: "proper_cpring H y" using cpmap_proper[OF config_prog_cubic[OF h]] cq by simp
    interpret F3: ecp3 H y using F.hypermap_axioms F.x0D pr by (intro ecp3_intro)
    have cpH: "cpmap (CpH # q) = (F3.GH, F3.XH)" using CpH cpmap_H[OF cq F3.ecp2h_axioms] by simp
    have "set (ctrenum q) \<subseteq> F.D" using Cons.IH h cq by simp
    moreover have "face F3.GH F3.XH \<in> darts F3.GH" using F3.face_GH_cycle(1) by simp
    ultimately show ?thesis using CpH cpH F3.darts_GH F.nx0D F.x0D cq by auto
  qed (use qo in simp_all)
qed

lemma uniq_ctrenum: "config_prog cp \<Longrightarrow> distinct (insertE (cpG cp) (cpring_of cp @ ctrenum cp))"
proof (induction cp)
  case Nil then show ?case by simp
next
  case (Cons s cp)
  obtain G x where c: "cpmap cp = (G, x)" by (cases "cpmap cp")
  interpret E: ecp G x using hypermap_cpmap[of cp] cpx_in[of cp] c by (intro ecp_intro) simp_all
  have cpo: "config_prog (s # cp)" using Cons.prems by simp
  have enD: "cp = [] \<or> config_prog cp \<Longrightarrow> set (ctrenum cp) \<subseteq> E.D"
    using ctrenum_darts[of cp] c by fastforce
  show ?case
  proof (cases s)
    case (CpR k)
    then have h: "config_prog cp" using cpo by simp
    have IH: "distinct (insertE G (cpring G x @ ctrenum cp))" using Cons.IH h c by (simp add: cpring_of_def)
    have "mset (insertE G (rot k (cpring G x) @ ctrenum cp)) = mset (insertE G (cpring G x @ ctrenum cp))"
      by (simp add: insertE_app insertE_rot)
    then have "distinct (insertE G (rot k (cpring G x) @ ctrenum cp))"
      using IH mset_eq_imp_distinct_iff by blast
    then show ?thesis using CpR cpmap_Cons_cases(1)[OF c] by (simp add: cpring_of_def E.cpring_ecpR)
  next
    case CpY
    interpret E2: ecp2 G x by (simp add: ecp2_def E.ecp_axioms)
    have cpY: "cpmap (CpY # cp) = (E2.GY, E2.XY)" using CpY cpmap_Cons_cases(4)[OF c E2.ecp2_axioms] by simp
    obtain r0 where hr: "cpring G x = node G x # r0" using E.head_cpring[of x] by blast
    have ringY: "cpring E2.GY E2.XY = E.Xe # E2.XY # r0" using E2.cpring_GY hr by simp
    have r0D: "set r0 \<subseteq> E.D" using E.ringD hr by auto
    have new: "insertE E2.GY [E.Xe, E2.XY] = [E.Xe, E.X, E2.XY, E2.T.Xe]" by simp
    have newd: "distinct [E.Xe, E.X, E2.XY, E2.T.Xe]" by simp
    define old where "old = (if cp = [] then r0 else r0 @ node G x # ctrenum cp)"
    have oldD: "set old \<subseteq> E.D" using r0D enD CpY cpo E.x0D by (cases cp) (auto simp: old_def)
    have lst: "cpring_of (CpY # cp) @ ctrenum (CpY # cp) = [E.Xe, E2.XY] @ old"
      using cpY ringY c by (simp add: cpring_of_def old_def)
    have insold: "insertE E2.GY old = insertE G old"
      using oldD E2.face_GY_old by (intro insertE_cong) blast
    have dold: "distinct (insertE G old)"
    proof (cases "cp = []")
      case True
      then have "G = cpmap0" "x = 1" using c by simp_all
      then have "r0 = [1]" using hr cpring0 by simp
      then show ?thesis using True \<open>G = cpmap0\<close> by (simp add: old_def sw01_def)
    next
      case False
      then have h: "config_prog cp" using cpo CpY by (cases cp) auto
      have IH: "distinct (insertE G (cpring G x @ ctrenum cp))" using Cons.IH h c by (simp add: cpring_of_def)
      have "mset (insertE G old) = mset (insertE G (cpring G x @ ctrenum cp))"
        using False hr by (simp add: old_def insertE_app)
      then show ?thesis using IH mset_eq_imp_distinct_iff by blast
    qed
    have "set (insertE G old) \<subseteq> E.D" by (rule E.insertE_D[OF oldD])
    then have disj: "set [E.Xe, E.X, E2.XY, E2.T.Xe] \<inter> set (insertE G old) = {}"
      using E2.D_neq_XY by fastforce
    have "insertE E2.GY ([E.Xe, E2.XY] @ old) = [E.Xe, E.X, E2.XY, E2.T.Xe] @ insertE G old"
      by (simp only: insertE_app new insold)
    then have "distinct (insertE E2.GY ([E.Xe, E2.XY] @ old))"
      unfolding distinct_append using newd dold disj by simp
    then show ?thesis unfolding CpY lst cpY fst_conv .
  next
    case CpH
    then have h: "config_prog cp" using cpo by simp
    have pr: "proper_cpring G x" using cpmap_proper[OF config_prog_cubic[OF h]] c by simp
    interpret E3: ecp3 G x using E.hypermap_axioms E.x0D pr by (intro ecp3_intro)
    have cpH: "cpmap (CpH # cp) = (E3.GH, E3.XH)" using CpH cpmap_H[OF c E3.ecp2h_axioms] by simp
    define r2 where "r2 = drop 2 (cpring G x)"
    have hr: "cpring G x = node G x # x # r2" using E.head_proper_cpring[OF pr] by (simp add: r2_def)
    have r2D: "set r2 \<subseteq> E.D" using E.ringD hr by auto
    have ringH: "cpring E3.GH E3.XH = E.Xe # E3.XH # r2" using E3.cpring_GH by (simp add: r2_def)
    have fXH: "face E3.GH E3.XH = E3.XY" by (rule E3.face_GH_cycle(1))
    define old where "old = r2 @ node G x # x # ctrenum cp"
    have oldD: "set old \<subseteq> E.D" using r2D enD h E.x0D by (auto simp: old_def)
    have lst: "cpring_of (CpH # cp) @ ctrenum (CpH # cp) = [E.Xe, E3.XH] @ r2 @ [E3.XY] @ node G x # x # ctrenum cp"
      using cpH ringH fXH c by (simp add: cpring_of_def)
    have mlst: "mset (insertE E3.GH ([E.Xe, E3.XH] @ r2 @ [E3.XY] @ node G x # x # ctrenum cp)) =
                mset (insertE E3.GH [E.Xe, E3.XH, E3.XY] @ insertE E3.GH old)"
      by (simp add: old_def insertE_app)
    have new: "insertE E3.GH [E.Xe, E3.XH, E3.XY] = [E.Xe, E.X, E3.XH, E3.T2.Xe, E3.XY, E3.T.Xe]" by simp
    have newd: "distinct [E.Xe, E.X, E3.XH, E3.T2.Xe, E3.XY, E3.T.Xe]" by simp
    have eH: "edge E3.GH y = edge G y" if "y \<in> E.D" for y using that by simp
    have insold: "insertE E3.GH old = insertE G old"
      using oldD eH by (intro insertE_cong) blast
    have IH: "distinct (insertE G (cpring G x @ ctrenum cp))" using Cons.IH h c by (simp add: cpring_of_def)
    have "mset (insertE G old) = mset (insertE G (cpring G x @ ctrenum cp))"
      using hr by (simp add: old_def insertE_app)
    then have dold: "distinct (insertE G old)" using IH mset_eq_imp_distinct_iff by blast
    have "set (insertE G old) \<subseteq> E.D" by (rule E.insertE_D[OF oldD])
    then have disj: "set [E.Xe, E.X, E3.XH, E3.T2.Xe, E3.XY, E3.T.Xe] \<inter> set (insertE G old) = {}"
      using E3.D_neq_XY E3.D_neq_XH by fastforce
    have "distinct (insertE E3.GH [E.Xe, E3.XH, E3.XY] @ insertE E3.GH old)"
      using newd dold disj by (simp only: new insold distinct_append)
    then have "distinct (insertE E3.GH ([E.Xe, E3.XH] @ r2 @ [E3.XY] @ node G x # x # ctrenum cp))"
      using mlst mset_eq_imp_distinct_iff by metis
    then show ?thesis unfolding CpH lst cpH fst_conv .
  qed (use cpo in simp_all)
qed

section \<open>The contract program\<close>

definition nsp :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
  "nsp b x y = (if b then x \<or> y else x \<and> y)"

fun cfctr :: "bool list \<Rightarrow> bool list \<Rightarrow> cprog \<Rightarrow> cprog option" where
  "cfctr mr mc (CpR i # cp) =
     (case cfctr (rotr i mr) mc cp of
        Some cpc \<Rightarrow> Some (CpR (count_list (take i (rotr i mr)) False) # cpc)
      | None \<Rightarrow> None)"
| "cfctr (b1 # b2 # b3 # _) mc [CpY] =
     (if nsp b1 b2 b3 then None else Some (if b1 \<or> b2 \<or> b3 then [] else [CpY]))"
| "cfctr (b1 # b2 # mr') (b3 # mc') (CpY # cp) =
     (if nsp b1 b2 b3 then None else
      case cfctr (b3 # mr') mc' cp of
        Some cpc \<Rightarrow> Some (if b1 \<or> b2 then cpc else (if b3 then CpU else CpY) # cpc)
      | None \<Rightarrow> None)"
| "cfctr (b1 # b2 # mr') (b3 # b4 # b5 # mc') (CpH # cp) =
     (if nsp b3 b1 b4 \<or> nsp b3 b2 b5 then None else
      if b1 \<and> b2 \<and> (\<forall>b \<in> set mr'. b) then None else
      case cfctr (b4 # b5 # mr') mc' cp of
        Some cpc \<Rightarrow> Some (if b3 then cpc else
          if b1 then (if b2 then CpA # cpc else if b5 then cpc else CpK # cpc)
          else if b2 then (if b4 then cpc else CpK # cpc)
          else if b4 then (if b5 then CpU # cpc else CpY # cpc)
          else if b5 then CpY # cpc else CpH # cpc)
      | None \<Rightarrow> None)"
| "cfctr _ _ _ = None"

lemma config_prog_CpY: "config_prog cp \<Longrightarrow> config_prog (CpY # cp)"
  by (cases cp) auto

lemma cfctr_config_prog: "cfctr mr mc cp \<noteq> None \<Longrightarrow> config_prog cp"
  by (induction mr mc cp rule: cfctr.induct) (auto simp: config_prog_CpY split: if_splits option.splits)

section \<open>Extending a colouring along a construction step\<close>

lemma (in hypermap) coloring_cface:
  assumes col: "\<forall>x \<in> D. k (f x) = k x" and xy: "cface x y"
  shows "k x = k y"
  using xy
proof (induction rule: fconnect_induct)
  case refl then show ?case by simp
next
  case (step y)
  then show ?case using col by (cases "y \<in> D") auto
qed

lemma (in hypermap) coloring_adj:
  assumes col: "coloring G k" and xD: "x \<in> D" and a: "adj G x y"
  shows "k x \<noteq> k y"
proof -
  obtain z where xz: "cface x z" and zy: "cface (e z) y" using a by (auto simp: adj_iff)
  have zD: "z \<in> D" using xz xD F.fconnect_in_D by blast
  have fc: "\<forall>x \<in> D. k (f x) = k x" using col by (simp add: coloring_def)
  have "k x = k z" by (rule coloring_cface[OF fc xz])
  moreover have "k (e z) = k y" by (rule coloring_cface[OF fc zy])
  moreover have "k (e z) \<noteq> k z" using col zD by (simp add: coloring_def)
  ultimately show ?thesis by simp
qed

definition ext_col :: "'a hypermap \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> color) \<Rightarrow> color \<Rightarrow> 'a \<Rightarrow> color" where
  "ext_col M A h c u =
     (if \<exists>y \<in> A. fconnect (face M) u y then h (SOME y. y \<in> A \<and> fconnect (face M) u y) else c)"

context hypermap
begin

lemma ext_col_cface:
  assumes "cface u v"
  shows "ext_col G A h c u = ext_col G A h c v"
proof -
  have "cface u y \<longleftrightarrow> cface v y" for y
    using fconnect_trans[OF assms] fconnect_trans[OF F.fconnect_sym[OF assms]] by blast
  then show ?thesis unfolding ext_col_def by simp
qed

lemma ext_col_face: "ext_col G A h c (f u) = ext_col G A h c u"
  by (rule ext_col_cface[symmetric]) simp

lemma ext_col_old:
  assumes inv: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> cface a b \<Longrightarrow> h a = h b" and yA: "y \<in> A"
  shows "ext_col G A h c y = h y"
proof -
  have ex: "\<exists>z. z \<in> A \<and> cface y z" using yA by blast
  define z where "z = (SOME z. z \<in> A \<and> cface y z)"
  have "z \<in> A \<and> cface y z" unfolding z_def by (rule someI_ex[OF ex])
  then have "h z = h y" using inv yA F.fconnect_sym by blast
  then show ?thesis using yA unfolding ext_col_def z_def by auto
qed

lemma ext_col_band:
  assumes inv: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> cface a b \<Longrightarrow> h a = h b"
    and yA: "y \<in> A" and uy: "cface u y"
  shows "ext_col G A h c u = h y"
  using ext_col_cface[OF uy] ext_col_old[OF inv yA] by simp

lemma ext_col_new: "\<not> (\<exists>y \<in> A. cface u y) \<Longrightarrow> ext_col G A h c u = c"
  by (simp add: ext_col_def)

end

text \<open>Old edges of a step map keep different colours, provided adjacency between old darts in
  the step map implies adjacency in the old map.\<close>

lemma ext_col_edge_old:
  assumes hM: "hypermap M" and hGc: "hypermap Gc" and sub: "darts Gc \<subseteq> darts M"
    and col: "coloring Gc h"
    and inv: "\<And>a b. a \<in> darts Gc \<Longrightarrow> b \<in> darts Gc \<Longrightarrow> fconnect (face M) a b \<Longrightarrow> h a = h b"
    and adjold: "\<And>a b. a \<in> darts Gc \<Longrightarrow> b \<in> darts Gc \<Longrightarrow> adj M a b \<Longrightarrow> adj Gc a b"
    and ux: "x \<in> darts Gc" "fconnect (face M) u x"
    and euy: "y \<in> darts Gc" "fconnect (face M) (edge M u) y"
  shows "ext_col M (darts Gc) h c (edge M u) \<noteq> ext_col M (darts Gc) h c u"
proof -
  interpret M: hypermap M by (rule hM)
  interpret C: hypermap Gc by (rule hGc)
  have "adj M x y"
    unfolding M.adj_iff using M.F.fconnect_sym[OF ux(2)] euy(2) by blast
  then have "adj Gc x y" by (rule adjold[OF ux(1) euy(1)])
  then have "h x \<noteq> h y" by (rule C.coloring_adj[OF col ux(1)])
  moreover have "ext_col M (darts Gc) h c u = h x" by (rule M.ext_col_band[OF inv ux])
  moreover have "ext_col M (darts Gc) h c (edge M u) = h y" by (rule M.ext_col_band[OF inv euy])
  ultimately show ?thesis by simp
qed

lemma ext_col_edge_gen:
  assumes hM: "hypermap M"
    and inv: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> fconnect (face M) a b \<Longrightarrow> h a = h b"
    and diff: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> adj M a b \<Longrightarrow> h a \<noteq> h b"
    and ux: "x \<in> A" "fconnect (face M) u x"
    and euy: "y \<in> A" "fconnect (face M) (edge M u) y"
  shows "ext_col M A h c (edge M u) \<noteq> ext_col M A h c u"
proof -
  interpret M: hypermap M by (rule hM)
  have "adj M x y" unfolding M.adj_iff using M.F.fconnect_sym[OF ux(2)] euy(2) by blast
  then have "h x \<noteq> h y" by (rule diff[OF ux(1) euy(1)])
  moreover have "ext_col M A h c u = h x" by (rule M.ext_col_band[OF inv ux])
  moreover have "ext_col M A h c (edge M u) = h y" by (rule M.ext_col_band[OF inv euy])
  ultimately show ?thesis by simp
qed

section \<open>Correctness of the contract program\<close>

lemma set_insertE: "set (insertE G p) = set p \<union> edge G ` set p"
  by (induction p) auto

lemma cc_coloring_set:
  "set cc = set cc' \<Longrightarrow> cc_coloring G cc k \<longleftrightarrow> cc_coloring G cc' k"
  by (simp add: cc_coloring_def set_insertE)

lemma count_map_Not: "count_list (map Not l) True = count_list l False"
  by (induction l) auto

lemma length_mask: "length m = length s \<Longrightarrow> length (mask m s) = count_list m True"
  by (induction m s rule: mask.induct) auto

lemma mask_rot:
  assumes "length m = length s"
  shows "mask (rot k m) (rot k s) = rot (count_list (take k m) True) (mask m s)"
proof (cases "k \<le> length s")
  case True
  have lt: "length (take k m) = length (take k s)" using assms by simp
  have a: "mask (rot k m) (rot k s) = mask (drop k m) (drop k s) @ mask (take k m) (take k s)"
    using assms by (simp add: rot_def mask_append)
  have b: "mask m s = mask (take k m) (take k s) @ mask (drop k m) (drop k s)"
    using assms mask_append[OF lt, of "drop k m" "drop k s"] by simp
  have c: "length (mask (take k m) (take k s)) = count_list (take k m) True"
    by (rule length_mask[OF lt])
  show ?thesis unfolding a b c[symmetric] by (simp add: rot_def)
next
  case False
  then have "take k m = m" using assms by simp
  then show ?thesis using False assms by (simp add: rot_oversize length_mask)
qed

lemma (in hypermap) cpring_succ:
  assumes "Suc i < length (cpring G x0)"
  shows "cpring G x0 ! Suc i = f (e (cpring G x0 ! i))"
  using assms by (simp add: nth_cpring length_cpring inv_node_apply)

lemma mask_head_color:
  assumes succ: "\<And>i. Suc i < length l \<Longrightarrow> l ! Suc i = g (l ! i)"
    and len: "length m = length l"
    and pk: "\<And>y. y \<in> set (mask m l) \<Longrightarrow> k (g y) = k y"
    and ne: "mask (map Not m) l \<noteq> []"
  shows "k (hd (mask (map Not m) l)) = k (hd l)"
  using succ len pk ne
proof (induction l arbitrary: m)
  case Nil then show ?case by simp
next
  case (Cons a l)
  obtain b m' where m: "m = b # m'" and lm': "length m' = length l"
    using Cons.prems(2) by (cases m) auto
  show ?case
  proof (cases b)
    case False then show ?thesis by (simp add: m)
  next
    case True
    have ne': "mask (map Not m') l \<noteq> []" using Cons.prems(4) True by (simp add: m)
    then have lne: "l \<noteq> []" by (cases l) auto
    have succ': "l ! Suc i = g (l ! i)" if "Suc i < length l" for i
      using Cons.prems(1)[of "Suc i"] that by simp
    have prop': "k (g y) = k y" if "y \<in> set (mask m' l)" for y
      using Cons.prems(3)[of y] that True by (simp add: m)
    have "k (hd (mask (map Not m') l)) = k (hd l)" by (rule Cons.IH[OF succ' lm' prop' ne'])
    moreover have "hd l = g a" using Cons.prems(1)[of 0] lne by (simp add: hd_conv_nth)
    moreover have "k (g a) = k a" using Cons.prems(3)[of a] True by (simp add: m)
    ultimately show ?thesis using True by (simp add: m)
  qed
qed

lemma cpring_of_CpR: "cpring_of (CpR j # cp) = rot j (cpring_of cp)" and cpG_CpR: "cpG (CpR j # cp) = cpG cp"
proof -
  obtain G x where c: "cpmap cp = (G, x)" by (cases "cpmap cp")
  interpret H: hypermap G using hypermap_cpmap[of cp] c by simp
  show "cpring_of (CpR j # cp) = rot j (cpring_of cp)"
    using cpmap_Cons_cases(1)[OF c] c by (simp add: cpring_of_def H.cpring_ecpR)
  show "cpG (CpR j # cp) = cpG cp" using cpmap_Cons_cases(1)[OF c] c by simp
qed

lemma cc_edge:
  "cc_coloring M cc k \<Longrightarrow> u \<in> darts M \<Longrightarrow> k (edge M u) = k u \<longleftrightarrow> u \<in> set cc \<union> edge M ` set cc"
  by (simp add: cc_coloring_def set_insertE)

lemma cc_face:
  assumes "hypermap M" "cc_coloring M cc k" "fconnect (face M) u v"
  shows "k u = k v"
proof -
  interpret M: hypermap M by fact
  show ?thesis by (rule M.coloring_cface[OF _ assms(3)]) (use assms(2) in \<open>simp add: cc_coloring_def\<close>)
qed

lemma cc_transfer:
  assumes hM: "hypermap M" and hG: "hypermap G" and sub: "darts G \<subseteq> darts M"
    and eq: "\<And>y. y \<in> darts G \<Longrightarrow> edge M y = edge G y"
    and fc: "\<And>y. y \<in> darts G \<Longrightarrow> fconnect (face M) y (face G y)"
    and kM: "cc_coloring M ccM k"
    and cc1: "set ccM \<inter> darts G = set ccG" and cc2: "set ccG \<subseteq> darts G"
    and new: "\<And>z. z \<in> set ccM \<Longrightarrow> z \<notin> darts G \<Longrightarrow> edge M z \<notin> darts G"
  shows "cc_coloring G ccG k"
  unfolding cc_coloring_def
proof (intro conjI ballI)
  fix y assume yD: "y \<in> darts G"
  show "k (face G y) = k y" using cc_face[OF hM kM fc[OF yD]] by simp
  have yM: "y \<in> darts M" using sub yD by blast
  have "k (edge G y) = k y \<longleftrightarrow> y \<in> set ccM \<union> edge M ` set ccM"
    using cc_edge[OF kM yM] eq[OF yD] by simp
  also have "\<dots> \<longleftrightarrow> y \<in> set ccG \<union> edge G ` set ccG"
  proof
    assume "y \<in> set ccM \<union> edge M ` set ccM"
    then consider "y \<in> set ccM" | z where "z \<in> set ccM" "y = edge M z" by blast
    then show "y \<in> set ccG \<union> edge G ` set ccG"
    proof cases
      case 1 then show ?thesis using cc1 yD by blast
    next
      case (2 z)
      then have zD: "z \<in> darts G" using new yD by blast
      then show ?thesis using 2 cc1 eq[OF zD] by blast
    qed
  next
    assume "y \<in> set ccG \<union> edge G ` set ccG"
    then consider "y \<in> set ccG" | z where "z \<in> set ccG" "y = edge G z" by blast
    then show "y \<in> set ccM \<union> edge M ` set ccM"
    proof cases
      case 1 then show ?thesis using cc1 by blast
    next
      case (2 z)
      have zM: "z \<in> set ccM" using 2(1) cc1 by blast
      have "edge M z = edge G z" using 2(1) cc2 eq by blast
      then have "y = edge M z" using 2(2) by simp
      then show ?thesis using zM by blast
    qed
  qed
  finally show "k (edge G y) = k y \<longleftrightarrow> y \<in> set (insertE G ccG)" by (simp add: set_insertE)
qed

definition cfctr_ok :: "cprog \<Rightarrow> bool" where
  "cfctr_ok cp \<longleftrightarrow> (\<forall>mr mc k cpc. length mr = cprsize cp \<longrightarrow> length mc = ctrmsize cp \<longrightarrow>
     cc_coloring (cpG cp) (mask mr (cpring_of cp) @ mask mc (ctrenum cp)) k \<longrightarrow>
     cfctr mr mc cp = Some cpc \<longrightarrow>
     (\<exists>k'. coloring (cpG cpc) k' \<and> map k' (cpring_of cpc) = map k (mask (map Not mr) (cpring_of cp))))"

lemma cfctr_Y:
  assumes c: "cpmap cp = (G, x)" and h: "config_prog cp" and IH: "cfctr_ok cp"
  shows "cfctr_ok (CpY # cp)"
  unfolding cfctr_ok_def
proof (intro allI impI)
  fix mr mc k cpc
  assume l1: "length mr = cprsize (CpY # cp)" and l2: "length mc = ctrmsize (CpY # cp)"
    and kc: "cc_coloring (cpG (CpY # cp)) (mask mr (cpring_of (CpY # cp)) @ mask mc (ctrenum (CpY # cp))) k"
    and cf: "cfctr mr mc (CpY # cp) = Some cpc"
  interpret E: ecp G x using hypermap_cpmap[of cp] cpx_in[of cp] c by (intro ecp_intro) simp_all
  interpret E2: ecp2 G x by (simp add: ecp2_def E.ecp_axioms)
  have hY: "hypermap E2.GY" by (rule E2.T.NN.hypermap_axioms)
  have cq: "cubic_prog cp" by (rule config_prog_cubic[OF h])
  have pr: "proper_cpring G x" using cpmap_proper[OF cq] c by simp
  define r2 where "r2 = drop 2 (cpring G x)"
  have hr: "cpring G x = node G x # x # r2" using E.head_proper_cpring[OF pr] by (simp add: r2_def)
  have r2D: "set r2 \<subseteq> E.D" using E.ringD hr by auto
  obtain s0 cp0 where cps: "cp = s0 # cp0" using h by (cases cp) auto
  have cpY: "cpmap (CpY # cp) = (E2.GY, E2.XY)" using cpmap_Cons_cases(4)[OF c E2.ecp2_axioms] by simp
  have ringY: "cpring E2.GY E2.XY = E.Xe # E2.XY # x # r2" using E2.cpring_GY hr by simp
  define En where "En = ctrenum cp"
  have EnD: "set En \<subseteq> E.D" using ctrenum_darts[of cp] h c by (simp add: En_def)
  have enY: "ctrenum (CpY # cp) = node G x # En" using cps c by (simp add: En_def)
  have lr: "cprsize cp = Suc (Suc (length r2))" using size_ring_cpmap[of cp] c hr by (simp add: cpring_of_def)
  obtain b1 b2 mr' where mr: "mr = b1 # b2 # mr'" and lmr': "length mr' = Suc (length r2)"
    using l1 lr by (metis cprsize.simps(2) length_Suc_conv)
  obtain b3 mc' where mc: "mc = b3 # mc'" and lmc': "length mc' = ctrmsize cp"
    using l2 cps by (metis ctrmsize.simps(3) length_Suc_conv)
  obtain cpc0 where nspF: "\<not> nsp b1 b2 b3" and cf0: "cfctr (b3 # mr') mc' cp = Some cpc0"
    and cpc: "cpc = (if b1 \<or> b2 then cpc0 else (if b3 then CpU else CpY) # cpc0)"
    using cf unfolding mr mc cps by (auto split: if_splits option.splits)
  define ccY where "ccY = mask (b1 # b2 # mr') (E.Xe # E2.XY # x # r2) @ mask (b3 # mc') (node G x # En)"
  define ccG where "ccG = mask (b3 # mr') (node G x # x # r2) @ mask mc' En"
  have kY: "cc_coloring E2.GY ccY k"
    using kc unfolding cpring_of_def cpY fst_conv snd_conv ringY enY mr mc ccY_def .
  have mD: "set (mask mr' (x # r2)) \<subseteq> E.D" "set (mask mc' En) \<subseteq> E.D"
    using set_mask_subset[of mr' "x # r2"] set_mask_subset[of mc' En] r2D EnD E.x0D by auto
  have ccGD: "set ccG \<subseteq> E.D" using mD E.x0D by (auto simp: ccG_def)
  have ccYs: "set ccY = (if b1 then {E.Xe} else {}) \<union> (if b2 then {E2.XY} else {}) \<union> set ccG"
    by (auto simp: ccY_def ccG_def)
  have XYnD: "E2.XY \<notin> E.D" and TXenD: "E2.T.Xe \<notin> E.D" using E2.D_neq_XY by blast+
  have ccY1: "set ccY \<inter> E.D = set ccG" using ccYs ccGD XYnD by auto
  have kG: "cc_coloring G ccG k"
  proof (rule cc_transfer[OF hY E.hypermap_axioms _ _ _ kY ccY1 ccGD])
    show "E.D \<subseteq> darts E2.GY" using E2.darts_GY by auto
    show "edge E2.GY y = edge G y" if "y \<in> E.D" for y using E2.face_GY_old[OF that] by simp
    show "fconnect (face E2.GY) y (face G y)" if "y \<in> E.D" for y
      using E2.cface_GY_old[of y "face G y"] that by simp
    show "edge E2.GY z \<notin> E.D" if "z \<in> set ccY" "z \<notin> E.D" for z
      using that ccYs ccGD TXenD by (auto split: if_splits)
  qed
  have ccGs: "set ccG = (if b3 then {node G x} else {}) \<union> set (mask mr' (x # r2)) \<union> set (mask mc' En)"
    by (auto simp: ccG_def)
  \<comment> \<open>colour facts in the Y map\<close>
  have nYXY: "node E2.GY E2.XY = E.Xe" using E2.long_GU by simp
  have kXeN: "k E.Xe = k (node G x)"
    using cc_face[OF hY kY, of E.Xe "node G x"] E2.cface_node_GY nYXY by simp
  have kXYX: "k E2.XY = k E.X" using cc_face[OF hY kY, of E2.XY E.X] E2.cface_GY_XY by simp
  have kTXe: "k E2.T.Xe = k x" using cc_face[OF hY kY E2.cface_GY_TXe] .
  have newY: "z \<in> set ccY \<Longrightarrow> z = E.Xe \<or> z = E2.XY \<or> z \<in> E.D" for z
    using ccYs ccGD by (auto split: if_splits)
  have eXe: "k E.X = k E.Xe \<longleftrightarrow> b1"
  proof -
    have "k (edge E2.GY E.Xe) = k E.Xe \<longleftrightarrow> E.Xe \<in> set ccY \<union> edge E2.GY ` set ccY"
      by (rule cc_edge[OF kY]) simp
    moreover have "E.Xe \<notin> edge E2.GY ` set ccY"
    proof
      assume "E.Xe \<in> edge E2.GY ` set ccY"
      then obtain z where z: "z \<in> set ccY" "E.Xe = edge E2.GY z" by blast
      have "edge E2.GY z \<noteq> E.Xe" using newY[OF z(1)]
      proof (elim disjE)
        assume "z = E.Xe" then show ?thesis by simp
      next
        assume "z = E2.XY" then show ?thesis by simp
      next
        assume zD: "z \<in> E.D"
        then have "edge E2.GY z \<in> E.D" using E2.face_GY_old[OF zD] by simp
        then show ?thesis by auto
      qed
      from this z(2)[symmetric] show False by contradiction
    qed
    moreover have "edge E2.GY E.Xe = E.X" by simp
    moreover have "E.Xe \<in> set ccY \<longleftrightarrow> b1" using ccYs ccGD E.Xe_notin by auto
    ultimately show ?thesis by (simp only: Un_iff) blast
  qed
  have eXY: "k E2.T.Xe = k E2.XY \<longleftrightarrow> b2"
  proof -
    have "k (edge E2.GY E2.XY) = k E2.XY \<longleftrightarrow> E2.XY \<in> set ccY \<union> edge E2.GY ` set ccY"
      by (rule cc_edge[OF kY]) simp
    moreover have "E2.XY \<notin> edge E2.GY ` set ccY"
    proof
      assume "E2.XY \<in> edge E2.GY ` set ccY"
      then obtain z where z: "z \<in> set ccY" "E2.XY = edge E2.GY z" by blast
      have "edge E2.GY z \<noteq> E2.XY" using newY[OF z(1)]
      proof (elim disjE)
        assume "z = E.Xe" then show ?thesis by simp
      next
        assume "z = E2.XY" then show ?thesis by simp
      next
        assume zD: "z \<in> E.D"
        then have "edge E2.GY z \<in> E.D" using E2.face_GY_old[OF zD] by simp
        then show ?thesis using XYnD by auto
      qed
      from this z(2)[symmetric] show False by contradiction
    qed
    moreover have "edge E2.GY E2.XY = E2.T.Xe" by simp
    moreover have "E2.XY \<in> set ccY \<longleftrightarrow> b2" using ccYs ccGD XYnD by auto
    ultimately show ?thesis by (simp only: Un_iff) blast
  qed
  \<comment> \<open>the recursive call\<close>
  have lG: "length (b3 # mr') = cprsize cp" using lmr' lr by simp
  have rof: "cpring_of cp = node G x # x # r2" using c hr by (simp add: cpring_of_def)
  have kG': "cc_coloring (cpG cp) (mask (b3 # mr') (cpring_of cp) @ mask mc' (ctrenum cp)) k"
    using kG c unfolding rof ccG_def En_def by simp
  obtain k' where col: "coloring (cpG cpc0) k'"
    and Ek0: "map k' (cpring_of cpc0) = map k (mask (map Not (b3 # mr')) (cpring_of cp))"
    using IH[unfolded cfctr_ok_def, rule_format, OF lG lmc' kG' cf0] by blast
  have Ek: "map k' (cpring_of cpc0) = map k (mask (map Not (b3 # mr')) (node G x # x # r2))"
    using Ek0 unfolding rof .
  \<comment> \<open>colours along the old ring\<close>
  have kprop: "k (face G (edge G y)) = k y" if "y \<in> set ccG" for y
  proof -
    have yD: "y \<in> E.D" using that ccGD by blast
    have "k (edge G y) = k y" using cc_edge[OF kG yD] that by simp
    moreover have "k (face G (edge G y)) = k (edge G y)"
      using kG yD by (simp add: cc_coloring_def)
    ultimately show ?thesis by simp
  qed
  have succ: "\<And>i. Suc i < length (cpring G x) \<Longrightarrow> cpring G x ! Suc i = face G (edge G (cpring G x ! i))"
    by (rule E.cpring_succ)
  have head_nx: "k (hd (mask (map Not (b3 # mr')) (node G x # x # r2))) = k (node G x)"
    if "mask (map Not (b3 # mr')) (node G x # x # r2) \<noteq> []"
    using mask_head_color[of "cpring G x" "\<lambda>y. face G (edge G y)" "b3 # mr'" k] succ that kprop lG lr
      size_ring_cpmap[of cp] c hr by (simp add: ccG_def cpring_of_def)
  have succ2: "(x # r2) ! Suc i = face G (edge G ((x # r2) ! i))" if "Suc i < length (x # r2)" for i
    using succ[of "Suc i"] that hr by simp
  have head_x: "k (hd (mask (map Not mr') (x # r2))) = k x"
    if "mask (map Not mr') (x # r2) \<noteq> []"
    using mask_head_color[of "x # r2" "\<lambda>y. face G (edge G y)" mr' k] succ2 that kprop lmr'
    by (simp add: ccG_def)
  obtain Gc xc where c0: "cpmap cpc0 = (Gc, xc)" by (cases "cpmap cpc0")
  interpret Ec: ecp Gc xc using hypermap_cpmap[of cpc0] cpx_in[of cpc0] c0 by (intro ecp_intro) simp_all
  have colc: "coloring Gc k'" using col c0 by simp
  have prc: "proper_cpring Gc xc" by (rule Ec.coloring_proper_cpring[OF colc Ec.x0D])
  define rc where "rc = drop 2 (cpring Gc xc)"
  have hrc: "cpring Gc xc = node Gc xc # xc # rc" using Ec.head_proper_cpring[OF prc] by (simp add: rc_def)
  have Ekc: "map k' (cpring Gc xc) = map k (mask (map Not (b3 # mr')) (node G x # x # r2))"
    using Ek c0 by (simp add: cpring_of_def)
  have finvc: "\<And>a b. a \<in> Ec.D \<Longrightarrow> b \<in> Ec.D \<Longrightarrow> fconnect (face Gc) a b \<Longrightarrow> k' a = k' b"
  proof -
    fix a b assume "a \<in> Ec.D" "b \<in> Ec.D" and ab: "fconnect (face Gc) a b"
    have "\<forall>x \<in> Ec.D. k' (face Gc x) = k' x" using colc by (simp add: coloring_def)
    then show "k' a = k' b" by (rule Ec.coloring_cface[OF _ ab])
  qed
  show "\<exists>k'. coloring (cpG cpc) k' \<and> map k' (cpring_of cpc) = map k (mask (map Not mr) (cpring_of (CpY # cp)))"
  proof (cases "b1 \<or> b2")
    case True
    then have nb3: "\<not> b3" and one: "b1 \<longleftrightarrow> \<not> b2" using nspF by (auto simp: nsp_def split: if_splits)
    have Ek2: "map k' (cpring Gc xc) = k (node G x) # map k (mask (map Not mr') (x # r2))"
      using Ekc nb3 by simp
    have "map k (mask (map Not mr) (cpring_of (CpY # cp))) = k (node G x) # map k (mask (map Not mr') (x # r2))"
    proof (cases b1)
      case True
      then have "\<not> b2" using one by simp
      then show ?thesis using True kXYX eXe kXeN unfolding mr cpring_of_def cpY fst_conv snd_conv ringY
        by simp
    next
      case False
      then have "b2" using one by simp
      then show ?thesis using False kXeN unfolding mr cpring_of_def cpY fst_conv snd_conv ringY by simp
    qed
    then show ?thesis using True colc Ek2 cpc c0 by (intro exI[of _ k']) (simp add: cpring_of_def)
  next
    case False
    then have nb1: "\<not> b1" and nb2: "\<not> b2" by auto
    have RHS: "map k (mask (map Not mr) (cpring_of (CpY # cp))) =
               k (node G x) # k E2.XY # map k (mask (map Not mr') (x # r2))"
      using nb1 nb2 kXeN unfolding mr cpring_of_def cpY fst_conv snd_conv ringY by simp
    have kXYne: "k E2.XY \<noteq> k (node G x)" using kXYX eXe nb1 kXeN by simp
    show ?thesis
    proof (cases b3)
      case True
      \<comment> \<open>contract the Y foot: a U step\<close>
      have cpU: "cpmap (CpU # cpc0) = (Ec.GU, Ec.X)" using cpmap_Cons_cases(3)[OF c0 Ec.ecp_axioms] .
      have ringU: "cpring Ec.GU Ec.X = Ec.Xe # Ec.X # cpring Gc xc" by (rule Ec.cpring_GU)
      define k'' where "k'' = ext_col Ec.GU Ec.D k' (k E2.XY)"
      have invU: "\<And>a b. a \<in> Ec.D \<Longrightarrow> b \<in> Ec.D \<Longrightarrow> fconnect (face Ec.GU) a b \<Longrightarrow> k' a = k' b"
        using finvc Ec.cface_GU_old by blast
      have k''old: "k'' y = k' y" if "y \<in> Ec.D" for y
        unfolding k''_def by (rule Ec.U.ext_col_old[OF invU that]) auto
      have k''X: "k'' Ec.X = k E2.XY"
        unfolding k''_def by (rule Ec.U.ext_col_new) (use Ec.cface_GU_X in auto)
      have Ekc1: "map k' (cpring Gc xc) = map k (mask (map Not mr') (x # r2))" using Ekc True by simp
      have hnc: "k' (node Gc xc) = k (node G x)"
      proof -
        have ne: "mask (map Not (b3 # mr')) (node G x # x # r2) \<noteq> []"
          using Ekc hrc by (metis list.map_disc_iff list.simps(3))
        have "k' (node Gc xc) = hd (map k' (cpring Gc xc))" using hrc by simp
        also have "\<dots> = k (hd (mask (map Not (b3 # mr')) (node G x # x # r2)))"
          using Ekc ne by (simp add: hd_map)
        finally show ?thesis using head_nx[OF ne] by simp
      qed
      have k''Xe: "k'' Ec.Xe = k (node G x)"
        using Ec.U.ext_col_band[OF invU Ec.nx0D Ec.cface_GU_Xe] hnc by (simp add: k''_def)
      have ring_eq: "map k'' (cpring_of (CpU # cpc0)) = map k (mask (map Not mr) (cpring_of (CpY # cp)))"
      proof -
        have "map k'' (cpring Gc xc) = map k' (cpring Gc xc)"
          using k''old Ec.ringD by (intro map_cong) auto
        then have "map k'' (cpring_of (CpU # cpc0)) = k (node G x) # k E2.XY # map k (mask (map Not mr') (x # r2))"
          using k''X k''Xe Ekc1 unfolding cpring_of_def cpU fst_conv snd_conv ringU by simp
        then show ?thesis using RHS True by simp
      qed
      have colU: "coloring Ec.GU k''"
        unfolding coloring_def
      proof (intro conjI ballI)
        fix u assume u: "u \<in> darts Ec.GU"
        show "k'' (face Ec.GU u) = k'' u" unfolding k''_def by (rule Ec.U.ext_col_face)
        consider "u = Ec.X" | "u = Ec.Xe" | "u \<in> Ec.D" using u by auto
        then show "k'' (edge Ec.GU u) \<noteq> k'' u"
        proof cases
          case 1 then show ?thesis using k''X k''Xe kXYne by simp
        next
          case 2 then show ?thesis using k''X k''Xe kXYne by simp
        next
          case 3
          have eu: "edge Ec.GU u = edge Gc u" "edge Gc u \<in> Ec.D" using 3 by simp_all
          have sub: "Ec.D \<subseteq> darts Ec.GU" by auto
          have adjold: "\<And>a b. a \<in> Ec.D \<Longrightarrow> b \<in> Ec.D \<Longrightarrow> adj Ec.GU a b \<Longrightarrow> adj Gc a b"
            using Ec.adj_GU_old by blast
          have fe: "fconnect (face Ec.GU) (edge Ec.GU u) (edge Gc u)" unfolding eu(1) by (rule fconnect_refl)
          show ?thesis unfolding k''_def
            by (rule ext_col_edge_old[OF Ec.U.hypermap_axioms Ec.hypermap_axioms sub colc invU adjold
                  3 fconnect_refl eu(2) fe])
        qed
      qed
      show ?thesis using cpc nb1 nb2 True colU ring_eq cpU by (intro exI[of _ k'']) simp
    next
      case False
      \<comment> \<open>keep the Y step\<close>
      interpret Ec2: ecp2 Gc xc by (simp add: ecp2_def Ec.ecp_axioms)
      have cpYc: "cpmap (CpY # cpc0) = (Ec2.GY, Ec2.XY)" using cpmap_Cons_cases(4)[OF c0 Ec2.ecp2_axioms] by simp
      have ringYc: "cpring Ec2.GY Ec2.XY = Ec.Xe # Ec2.XY # xc # rc" using Ec2.cpring_GY hrc by simp
      define k'' where "k'' = ext_col Ec2.GY Ec.D k' (k E2.XY)"
      have invY: "\<And>a b. a \<in> Ec.D \<Longrightarrow> b \<in> Ec.D \<Longrightarrow> fconnect (face Ec2.GY) a b \<Longrightarrow> k' a = k' b"
        using finvc Ec2.cface_GY_old by blast
      have k''old: "k'' y = k' y" if "y \<in> Ec.D" for y
        unfolding k''_def by (rule Ec2.T.NN.ext_col_old[OF invY that])
      have Ekc0: "map k' (cpring Gc xc) = k (node G x) # map k (mask (map Not mr') (x # r2))"
        using Ekc False by simp
      have hnc: "k' (node Gc xc) = k (node G x)" and Etl: "map k' (xc # rc) = map k (mask (map Not mr') (x # r2))"
        using Ekc0 hrc by simp_all
      have hxc: "k' xc = k x"
      proof -
        have ne: "mask (map Not mr') (x # r2) \<noteq> []" using Etl by (metis list.map_disc_iff list.simps(3))
        have "k' xc = hd (map k (mask (map Not mr') (x # r2)))" using Etl by (metis list.sel(1) list.simps(9))
        also have "\<dots> = k (hd (mask (map Not mr') (x # r2)))" using ne by (simp add: hd_map)
        finally show ?thesis using head_x[OF ne] by simp
      qed
      have nYc: "node Ec2.GY Ec2.XY = Ec.Xe" using Ec2.long_GU by simp
      have XeNc: "fconnect (face Ec2.GY) Ec.Xe (node Gc xc)" using Ec2.cface_node_GY nYc by simp
      have k''Xe: "k'' Ec.Xe = k (node G x)"
        using Ec2.T.NN.ext_col_band[OF invY Ec.nx0D XeNc] hnc by (simp add: k''_def)
      have nXYold: "\<not> (\<exists>y \<in> Ec.D. fconnect (face Ec2.GY) u y)" if "u = Ec2.XY \<or> u = Ec.X" for u
      proof
        assume "\<exists>y \<in> Ec.D. fconnect (face Ec2.GY) u y"
        then obtain y where yD: "y \<in> Ec.D" and uy: "fconnect (face Ec2.GY) u y" by blast
        have "fconnect (face Ec2.GY) Ec2.XY u" using that Ec2.cface_GY_XY by auto
        then have "fconnect (face Ec2.GY) Ec2.XY y" by (rule fconnect_trans[OF _ uy])
        then show False using yD Ec2.cface_GY_XY by auto
      qed
      have k''XY: "k'' Ec2.XY = k E2.XY" unfolding k''_def by (rule Ec2.T.NN.ext_col_new) (use nXYold in blast)
      have k''X: "k'' Ec.X = k E2.XY" unfolding k''_def by (rule Ec2.T.NN.ext_col_new) (use nXYold in blast)
      have k''TXe: "k'' Ec2.T.Xe = k x"
        using Ec2.T.NN.ext_col_band[OF invY Ec.x0D Ec2.cface_GY_TXe] hxc by (simp add: k''_def)
      have kXYx: "k E2.XY \<noteq> k x" using eXY nb2 kTXe by simp
      have ring_eq: "map k'' (cpring_of (CpY # cpc0)) = map k (mask (map Not mr) (cpring_of (CpY # cp)))"
      proof -
        have rcD: "set (xc # rc) \<subseteq> Ec.D" using Ec.ringD hrc by auto
        have "map k'' (xc # rc) = map k' (xc # rc)" using k''old rcD by (intro map_cong) auto
        then have Etl'': "map k'' (xc # rc) = map k (mask (map Not mr') (x # r2))"
          using Etl by (simp only:)
        have "map k'' (cpring_of (CpY # cpc0)) = k (node G x) # k E2.XY # map k (mask (map Not mr') (x # r2))"
          using k''XY k''Xe Etl'' unfolding cpring_of_def cpYc fst_conv snd_conv ringYc by simp
        then show ?thesis using RHS by simp
      qed
      have colY: "coloring Ec2.GY k''"
        unfolding coloring_def
      proof (intro conjI ballI)
        fix u assume u: "u \<in> darts Ec2.GY"
        show "k'' (face Ec2.GY u) = k'' u" unfolding k''_def by (rule Ec2.T.NN.ext_col_face)
        consider "u = Ec.X" | "u = Ec.Xe" | "u = Ec2.XY" | "u = Ec2.T.Xe" | "u \<in> Ec.D"
          using u Ec2.darts_GY by blast
        then show "k'' (edge Ec2.GY u) \<noteq> k'' u"
        proof cases
          case 1 then show ?thesis using k''X k''Xe kXYne by simp
        next
          case 2 then show ?thesis using k''X k''Xe kXYne by simp
        next
          case 3 then show ?thesis using k''XY k''TXe kXYx by simp
        next
          case 4 then show ?thesis using k''XY k''TXe kXYx by simp
        next
          case 5
          have eu: "edge Ec2.GY u = edge Gc u" "edge Gc u \<in> Ec.D"
            using Ec2.face_GY_old[OF 5] 5 by simp_all
          have sub: "Ec.D \<subseteq> darts Ec2.GY" using Ec2.darts_GY by blast
          have adjold: "\<And>a b. a \<in> Ec.D \<Longrightarrow> b \<in> Ec.D \<Longrightarrow> adj Ec2.GY a b \<Longrightarrow> adj Gc a b"
            using Ec2.adj_GY_old by blast
          have fe: "fconnect (face Ec2.GY) (edge Ec2.GY u) (edge Gc u)" unfolding eu(1) by (rule fconnect_refl)
          show ?thesis unfolding k''_def
            by (rule ext_col_edge_old[OF Ec2.T.NN.hypermap_axioms Ec.hypermap_axioms sub colc invY adjold
                  5 fconnect_refl eu(2) fe])
        qed
      qed
      show ?thesis using cpc nb1 nb2 False colY ring_eq cpYc by (intro exI[of _ k'']) simp
    qed
  qed
qed

lemma cfctr_Y0: "cfctr_ok [CpY]"
  unfolding cfctr_ok_def
proof (intro allI impI)
  fix mr mc k cpc
  assume l1: "length mr = cprsize [CpY]" and l2: "length mc = ctrmsize [CpY]"
    and kc: "cc_coloring (cpG [CpY]) (mask mr (cpring_of [CpY]) @ mask mc (ctrenum [CpY])) k"
    and cf: "cfctr mr mc [CpY] = Some cpc"
  define o1 where "o1 = (1::nat)"
  have c: "cpmap [] = (cpmap0, o1)" by (simp add: o1_def)
  interpret E: ecp cpmap0 o1 by (rule ecp_intro[OF hypermap_cpmap0]) (simp add: o1_def)
  have r0: "cpring cpmap0 o1 = [0, o1]" using cpring0 by (simp add: o1_def)
  interpret E2: ecp2 cpmap0 o1 unfolding ecp2_def by (rule E.ecp_axioms)
  have hY: "hypermap E2.GY" by (rule E2.T.NN.hypermap_axioms)
  have cpY: "cpmap [CpY] = (E2.GY, E2.XY)" using cpmap_Cons_cases(4)[OF c E2.ecp2_axioms] by simp
  have ringY: "cpring E2.GY E2.XY = [E.Xe, E2.XY, o1]" using E2.cpring_GY r0 by simp
  obtain b1 b2 b3 where mr: "mr = [b1, b2, b3]" using l1
    by (auto simp: numeral_eq_Suc length_Suc_conv)
  have mc: "mc = []" using l2 by simp
  have nspF: "\<not> nsp b1 b2 b3" and cpc: "cpc = (if b1 \<or> b2 \<or> b3 then [] else [CpY])"
    using cf by (auto simp: mr split: if_splits)
  define ccY where "ccY = mask [b1, b2, b3] [E.Xe, E2.XY, o1]"
  have kY: "cc_coloring E2.GY ccY k"
    using kc unfolding cpring_of_def cpY fst_conv snd_conv ringY mr mc ccY_def by simp
  have XYnD: "E2.XY \<notin> E.D" and TXenD: "E2.T.Xe \<notin> E.D" using E2.D_neq_XY by blast+
  have ccYs: "set ccY = (if b1 then {E.Xe} else {}) \<union> (if b2 then {E2.XY} else {}) \<union> (if b3 then {o1} else {})"
    by (auto simp: ccY_def)
  have newY: "z \<in> set ccY \<Longrightarrow> z = E.Xe \<or> z = E2.XY \<or> z = o1" for z using ccYs by (auto split: if_splits)
  have nYXY: "node E2.GY E2.XY = E.Xe" using E2.T.NN.head_cpring[of E2.XY] ringY by (metis list.inject)
  have kXeN: "k E.Xe = k 0"
    using cc_face[OF hY kY, of E.Xe "node cpmap0 o1"] E2.cface_node_GY nYXY by (simp add: sw01_def o1_def)
  have kXYX: "k E2.XY = k E.X" using cc_face[OF hY kY, of E2.XY E.X] E2.cface_GY_XY by simp
  have ez: "edge E2.GY z \<noteq> t" if "z \<in> set ccY" "t \<in> {E.Xe, E2.XY, o1}" "t \<noteq> o1 \<or> z \<noteq> o1" for z t
    using newY[OF that(1)]
  proof (elim disjE)
    assume z: "z = E.Xe"
    have "edge E2.GY E.Xe = E.X" by simp
    moreover have "E.X \<noteq> E.Xe" by simp
    moreover have "E.X \<noteq> E2.XY" by (rule E2.XY_neq(5))
    moreover have "E.X \<noteq> o1" using E.X_notin unfolding o1_def by (metis cpmap0_simps(1) insertCI)
    ultimately show ?thesis using that(2) unfolding z by (auto simp only: insert_iff empty_iff)
  next
    assume z: "z = E2.XY"
    have "edge E2.GY E2.XY = E2.T.Xe" by simp
    moreover have "E2.T.Xe \<noteq> E.Xe" by (rule E2.XY_neq(4))
    moreover have "E2.T.Xe \<noteq> E2.XY" using E2.T.X_neq(2) by simp
    moreover have "E2.T.Xe \<noteq> o1" using TXenD unfolding o1_def by auto
    ultimately show ?thesis using that(2) unfolding z by (auto simp only: insert_iff empty_iff)
  next
    assume z1: "z = o1"
    have ez0: "edge E2.GY z = 0" using E2.face_GY_old[of o1] z1 by (simp add: sw01_def o1_def)
    have zD: "(0::nat) \<in> E.D" by simp
    have n1: "(0::nat) \<noteq> E.Xe" using E.D_neq_X(2)[OF zD] .
    have n2: "(0::nat) \<noteq> E2.XY" using XYnD zD by metis
    have "t \<noteq> o1" using that(3) z1 by simp
    then show ?thesis using that(2) ez0 n1 n2 by (auto simp only: insert_iff empty_iff)
  qed
  have eXe: "k E.X = k E.Xe \<longleftrightarrow> b1"
  proof -
    have "k (edge E2.GY E.Xe) = k E.Xe \<longleftrightarrow> E.Xe \<in> set ccY \<union> edge E2.GY ` set ccY"
      by (rule cc_edge[OF kY]) simp
    moreover have "E.Xe \<notin> edge E2.GY ` set ccY"
    proof
      assume "E.Xe \<in> edge E2.GY ` set ccY"
      then obtain z where z: "z \<in> set ccY" "E.Xe = edge E2.GY z" by blast
      have "E.Xe \<noteq> o1" using E.D_neq_X(2)[of o1] by (simp add: o1_def)
      then have "edge E2.GY z \<noteq> E.Xe" by (intro ez[OF z(1)]) simp_all
      from this z(2)[symmetric] show False by contradiction
    qed
    moreover have "edge E2.GY E.Xe = E.X" by simp
    moreover have "E.Xe \<in> set ccY \<longleftrightarrow> b1" using ccYs XYnD by auto
    ultimately show ?thesis by (simp only: Un_iff) blast
  qed
  have e1: "k 0 = k o1 \<longleftrightarrow> b3"
  proof -
    have "k (edge E2.GY o1) = k o1 \<longleftrightarrow> o1 \<in> set ccY \<union> edge E2.GY ` set ccY"
      using E2.darts_GY E.x0D by (intro cc_edge[OF kY]) blast
    moreover have "edge E2.GY o1 = 0" using E2.face_GY_old[of o1] by (simp add: sw01_def o1_def)
    moreover have "o1 \<notin> edge E2.GY ` set ccY"
    proof
      assume "o1 \<in> edge E2.GY ` set ccY"
      then obtain z where z: "z \<in> set ccY" "o1 = edge E2.GY z" by blast
      have "edge E2.GY z \<noteq> o1"
        using newY[OF z(1)]
      proof (elim disjE)
        assume z: "z = E.Xe"
        have "edge E2.GY E.Xe = E.X" by simp
        moreover have "E.X \<noteq> o1" using E.D_neq_X(3)[of o1] by (simp add: o1_def)
        ultimately show ?thesis unfolding z by (simp only:) simp
      next
        assume z: "z = E2.XY"
        have "edge E2.GY E2.XY = E2.T.Xe" by simp
        moreover have "E2.T.Xe \<noteq> o1" using TXenD unfolding o1_def by auto
        ultimately show ?thesis unfolding z by (simp only:) simp
      next
        assume "z = o1" then show ?thesis using E2.face_GY_old[of o1] by (simp add: sw01_def o1_def)
      qed
      from this z(2)[symmetric] show False by contradiction
    qed
    moreover have "o1 \<in> set ccY \<longleftrightarrow> b3" using ccYs XYnD E.x0D by auto
    ultimately show ?thesis by (simp only: Un_iff) blast
  qed
  show "\<exists>k'. coloring (cpG cpc) k' \<and> map k' (cpring_of cpc) = map k (mask (map Not mr) (cpring_of [CpY]))"
  proof (cases "b1 \<or> b2 \<or> b3")
    case False
    have colY: "coloring E2.GY k"
      unfolding coloring_def
    proof (intro conjI ballI)
      fix u assume u: "u \<in> darts E2.GY"
      have kYf: "\<forall>x \<in> darts E2.GY. k (face E2.GY x) = k x" using kY unfolding cc_coloring_def by (rule conjunct2)
      show "k (face E2.GY u) = k u" using kYf u by blast
      have "set ccY = {}" using ccYs False by simp
      then show "k (edge E2.GY u) \<noteq> k u" using cc_edge[OF kY u] by (simp only: empty_iff Un_empty image_empty) simp
    qed
    have "map k (cpring_of [CpY]) = map k (mask (map Not mr) (cpring_of [CpY]))"
      using False unfolding cpring_of_def cpY fst_conv snd_conv ringY mr by simp
    then show ?thesis using False cpc colY cpY by (intro exI[of _ k]) simp
  next
    case True
    define l where "l = map k (mask (map Not mr) (cpring_of [CpY]))"
    have ll: "l = map k (mask [\<not> b1, \<not> b2, \<not> b3] [E.Xe, E2.XY, o1])"
      unfolding l_def cpring_of_def cpY fst_conv snd_conv ringY mr by simp
    obtain a b where ab: "l = [a, b]" and anb: "a \<noteq> b"
    proof -
      consider "b1" "\<not> b2" "\<not> b3" | "\<not> b1" "b2" "\<not> b3" | "\<not> b1" "\<not> b2" "b3"
        using True nspF by (auto simp: nsp_def split: if_splits)
      then show thesis
      proof cases
        case 1 then show ?thesis using that[of "k E2.XY" "k o1"] ll kXYX eXe kXeN e1 by simp
      next
        case 2 then show ?thesis using that[of "k E.Xe" "k o1"] ll kXeN e1 by simp
      next
        case 3 then show ?thesis using that[of "k E.Xe" "k E2.XY"] ll kXYX eXe by simp
      qed
    qed
    define k' where "k' u = (if u = 0 then a else b)" for u :: nat
    have col0: "coloring cpmap0 k'" using anb by (auto simp: coloring_def k'_def sw01_def)
    have "map k' (cpring_of []) = l" using ab by (simp add: cpring_of_Nil k'_def o1_def)
    then show ?thesis using True cpc col0 by (intro exI[of _ k']) (simp add: l_def)
  qed
qed

section \<open>The H step\<close>

locale hstep =
  fixes cp :: cprog and G :: "nat hypermap" and x :: nat and mr' mc' :: "bool list"
    and b1 b2 b3 b4 b5 :: bool and k :: "nat \<Rightarrow> color"
  assumes c: "cpmap cp = (G, x)" and h: "config_prog cp"
    and lmr': "Suc (Suc (length mr')) = cprsize cp" and lmc': "length mc' = ctrmsize cp"
    and kc: "cc_coloring (cpG (CpH # cp))
       (mask (b1 # b2 # mr') (cpring_of (CpH # cp)) @ mask (b3 # b4 # b5 # mc') (ctrenum (CpH # cp))) k"
begin

lemma cq: "cubic_prog cp" by (rule config_prog_cubic[OF h])
lemma pr: "proper_cpring G x" using cpmap_proper[OF cq] c by simp

sublocale E3: ecp3 G x
  using hypermap_cpmap[of cp] cpx_in[of cp] c pr by (intro ecp3_intro) simp_all

lemma hH: "hypermap E3.GH" by (rule E3.T2.NN.hypermap_axioms)
lemma lng: "long_cpring G x" using cfmap_long[OF h] c by simp

definition fex where "fex = face G (edge G x)"
definition r3 where "r3 = drop 3 (cpring G x)"
definition En where "En = ctrenum cp"

lemma fexD: "fex \<in> E3.D" using E3.x0D by (simp add: fex_def)
lemma hr: "cpring G x = node G x # x # fex # r3"
  using E3.head_long_cpring[OF lng] by (simp add: r3_def fex_def)
lemma r3D: "set r3 \<subseteq> E3.D" using E3.ringD hr by auto
lemma EnD: "set En \<subseteq> E3.D" using ctrenum_darts[of cp] h c by (simp add: En_def)
lemma cpH: "cpmap (CpH # cp) = (E3.GH, E3.XH)" using cpmap_H[OF c E3.ecp2h_axioms] by simp
lemma ringH: "cpring E3.GH E3.XH = E3.Xe # E3.XH # fex # r3"
  using E3.cpring_GH hr by simp
lemma enH: "ctrenum (CpH # cp) = E3.XY # node G x # x # En"
  using cpH c E3.face_GH_cycle(1) by (simp add: En_def)
lemma lmr3: "length mr' = Suc (length r3)"
  using lmr' size_ring_cpmap[of cp] c hr by (simp add: cpring_of_def)

definition ccH where "ccH = mask (b1 # b2 # mr') (E3.Xe # E3.XH # fex # r3) @ mask (b3 # b4 # b5 # mc') (E3.XY # node G x # x # En)"
definition ccG where "ccG = mask (b4 # b5 # mr') (node G x # x # fex # r3) @ mask mc' En"

lemma kH: "cc_coloring E3.GH ccH k"
  using kc unfolding cpring_of_def cpH fst_conv snd_conv ringH enH ccH_def .

lemma ccGD: "set ccG \<subseteq> E3.D"
  using set_mask_subset[of mr' "fex # r3"] set_mask_subset[of mc' En] r3D EnD fexD E3.x0D
  by (auto simp: ccG_def)

lemma newnD: "E3.XY \<notin> E3.D" "E3.XH \<notin> E3.D" "E3.T.Xe \<notin> E3.D" "E3.T2.Xe \<notin> E3.D"
  using E3.D_neq_XY E3.D_neq_XH by blast+

lemma ccHs: "set ccH = (if b1 then {E3.Xe} else {}) \<union> (if b2 then {E3.XH} else {}) \<union>
    (if b3 then {E3.XY} else {}) \<union> set ccG"
  by (auto simp: ccH_def ccG_def)

lemma newH: "z \<in> set ccH \<Longrightarrow> z = E3.Xe \<or> z = E3.XH \<or> z = E3.XY \<or> z \<in> E3.D"
  using ccHs ccGD by (auto split: if_splits)

lemma kG: "cc_coloring G ccG k"
proof (rule cc_transfer[OF hH E3.hypermap_axioms _ _ _ kH _ ccGD])
  show "E3.D \<subseteq> darts E3.GH" using E3.darts_GH by auto
  show "edge E3.GH y = edge G y" if "y \<in> E3.D" for y using that by simp
  show "fconnect (face E3.GH) y (face G y)" if "y \<in> E3.D" for y
    using E3.cface_GH_old[of y "face G y"] that by simp
  show "set ccH \<inter> E3.D = set ccG" using ccHs ccGD newnD E3.Xe_notin by auto
  show "edge E3.GH z \<notin> E3.D" if zc: "z \<in> set ccH" and zn: "z \<notin> E3.D" for z
  proof -
    consider "z = E3.Xe" | "z = E3.XH" | "z = E3.XY" using newH[OF zc] zn by blast
    then show ?thesis
    proof cases
      case 1
      have "edge E3.GH E3.Xe = E3.X" by simp
      then show ?thesis using 1 E3.X_notin by simp
    next
      case 2
      have "edge E3.GH E3.XH = E3.T2.Xe" by simp
      then show ?thesis using 2 newnD by simp
    next
      case 3
      have "edge E3.GH E3.XY = E3.T.Xe" by simp
      then show ?thesis using 3 newnD by simp
    qed
  qed
qed

text \<open>Colours around the new crossbar face.\<close>

lemma nHXH: "node E3.GH E3.XH = E3.Xe" using E3.T2.NN.head_cpring[of E3.XH] ringH by (metis list.inject)
lemma kXeN: "k E3.Xe = k (node G x)"
  using cc_face[OF hH kH, of E3.Xe "node G x"] E3.cface_node_GH nHXH by simp
lemma kXYH: "k E3.XY = k E3.XH" using cc_face[OF hH kH, of E3.XH E3.XY] E3.cface_GH_XH by simp
lemma kXH: "k E3.X = k E3.XH" using cc_face[OF hH kH, of E3.XH E3.X] E3.cface_GH_XH by simp
lemma kTXe: "k E3.T.Xe = k x" using cc_face[OF hH kH E3.cface_GH_TXe] .
lemma kT2Xe: "k E3.T2.Xe = k fex" using cc_face[OF hH kH E3.cface_GH_T2Xe] by (simp add: fex_def)

lemma not_edge_img:
  assumes t: "t \<in> {E3.Xe, E3.XH, E3.XY}"
  shows "t \<notin> edge E3.GH ` set ccH"
proof
  assume "t \<in> edge E3.GH ` set ccH"
  then obtain z where z: "z \<in> set ccH" "t = edge E3.GH z" by blast
  have "edge E3.GH z \<noteq> t" using newH[OF z(1)]
  proof (elim disjE)
    assume z1: "z = E3.Xe"
    have "edge E3.GH E3.Xe = E3.X" by simp
    moreover have "E3.X \<noteq> E3.Xe" "E3.X \<noteq> E3.XH" "E3.X \<noteq> E3.XY" by simp_all
    ultimately show ?thesis using t unfolding z1 by (auto simp only: insert_iff empty_iff)
  next
    assume z1: "z = E3.XH"
    have "edge E3.GH E3.XH = E3.T2.Xe" by simp
    moreover have "E3.T2.Xe \<noteq> E3.Xe" "E3.T2.Xe \<noteq> E3.XH" "E3.T2.Xe \<noteq> E3.XY" by simp_all
    ultimately show ?thesis using t unfolding z1 by (auto simp only: insert_iff empty_iff)
  next
    assume z1: "z = E3.XY"
    have "edge E3.GH E3.XY = E3.T.Xe" by simp
    moreover have "E3.T.Xe \<noteq> E3.Xe" "E3.T.Xe \<noteq> E3.XH" "E3.T.Xe \<noteq> E3.XY" by simp_all
    ultimately show ?thesis using t unfolding z1 by (auto simp only: insert_iff empty_iff)
  next
    assume zD: "z \<in> E3.D"
    have "edge E3.GH z = edge G z" using zD by simp
    moreover have "edge G z \<in> E3.D" using zD by simp
    ultimately show ?thesis using t newnD E3.Xe_notin by (auto simp only: insert_iff empty_iff)
  qed
  from this z(2)[symmetric] show False by contradiction
qed

lemma eXe: "k E3.X = k E3.Xe \<longleftrightarrow> b1"
proof -
  have "k (edge E3.GH E3.Xe) = k E3.Xe \<longleftrightarrow> E3.Xe \<in> set ccH \<union> edge E3.GH ` set ccH"
    by (rule cc_edge[OF kH]) simp
  moreover have "E3.Xe \<notin> edge E3.GH ` set ccH" by (rule not_edge_img) simp
  moreover have "edge E3.GH E3.Xe = E3.X" by simp
  moreover have "E3.Xe \<in> set ccH \<longleftrightarrow> b1" using ccHs ccGD E3.Xe_notin by auto
  ultimately show ?thesis by (simp only: Un_iff) blast
qed

lemma eXH: "k E3.T2.Xe = k E3.XH \<longleftrightarrow> b2"
proof -
  have "k (edge E3.GH E3.XH) = k E3.XH \<longleftrightarrow> E3.XH \<in> set ccH \<union> edge E3.GH ` set ccH"
    by (rule cc_edge[OF kH]) simp
  moreover have "E3.XH \<notin> edge E3.GH ` set ccH" by (rule not_edge_img) simp
  moreover have "edge E3.GH E3.XH = E3.T2.Xe" by simp
  moreover have "E3.XH \<in> set ccH \<longleftrightarrow> b2" using ccHs ccGD newnD by auto
  ultimately show ?thesis by (simp only: Un_iff) blast
qed

lemma eXY: "k E3.T.Xe = k E3.XY \<longleftrightarrow> b3"
proof -
  have "k (edge E3.GH E3.XY) = k E3.XY \<longleftrightarrow> E3.XY \<in> set ccH \<union> edge E3.GH ` set ccH"
    by (rule cc_edge[OF kH]) simp
  moreover have "E3.XY \<notin> edge E3.GH ` set ccH" by (rule not_edge_img) simp
  moreover have "edge E3.GH E3.XY = E3.T.Xe" by simp
  moreover have "E3.XY \<in> set ccH \<longleftrightarrow> b3" using ccHs ccGD newnD by auto
  ultimately show ?thesis by (simp only: Un_iff) blast
qed

text \<open>In terms of old darts, with kc the colour of the crossbar face.\<close>

lemma b1_iff: "b1 \<longleftrightarrow> k E3.XH = k (node G x)" using eXe kXH kXeN by metis
lemma b2_iff: "b2 \<longleftrightarrow> k fex = k E3.XH" using eXH kT2Xe by metis
lemma b3_iff: "b3 \<longleftrightarrow> k x = k E3.XH" using eXY kTXe kXYH by metis

end

lemma path_snoc_last: "path r a (l @ [b]) \<Longrightarrow> r (lastd a l) b"
  by (induction l arbitrary: a) auto

lemma mask_Not_nil: "mask (map Not m) l = [] \<Longrightarrow> length m = length l \<Longrightarrow> \<forall>b \<in> set m. b"
  by (induction m l rule: mask.induct) (auto split: if_splits)

lemma (in hypermap) cpring_last: "x0 \<in> D \<Longrightarrow> face G (edge G (last (cpring G x0))) = node G x0"
proof -
  assume x0D: "x0 \<in> D"
  interpret IN: fperm "inv n" D by (rule inv_node_fperm)
  have c: "cycle (frel (inv n)) (cpring G x0)" unfolding cpring_inv by (rule IN.cycle_orb)
  obtain l where l: "cpring G x0 = n x0 # l" using head_cpring[of x0] by blast
  have "path (frel (inv n)) (n x0) (l @ [n x0])" using c l by (simp add: cycle_Cons)
  then have "inv n (lastd (n x0) l) = n x0" by (rule path_snoc_last)
  moreover have "last (cpring G x0) = lastd (n x0) l" using l by (simp add: last_ConsL)
  ultimately show ?thesis by (simp add: inv_node_apply)
qed

locale hstep2 = hstep +
  fixes cpc0 :: cprog and k' :: "nat \<Rightarrow> color"
  assumes col: "coloring (cpG cpc0) k'"
    and Ek: "map k' (cpring_of cpc0) = map k (mask (map Not (b4 # b5 # mr')) (cpring G x))"
begin

abbreviation Gc where "Gc \<equiv> cpG cpc0"
abbreviation xc where "xc \<equiv> cpx cpc0"

sublocale Ec: ecp Gc xc using hypermap_cpmap[of cpc0] cpx_in[of cpc0] by (intro ecp_intro) simp_all

lemma prc: "proper_cpring Gc xc" by (rule Ec.coloring_proper_cpring[OF col Ec.x0D])

definition rc where "rc = drop 2 (cpring Gc xc)"
lemma hrc: "cpring Gc xc = node Gc xc # xc # rc"
  using Ec.head_proper_cpring[OF prc] by (simp add: rc_def)
lemma rcD: "set rc \<subseteq> Ec.D" using Ec.ringD hrc by auto

definition tailR where "tailR = map k (mask (map Not mr') (fex # r3))"

lemma Ek2: "k' (node Gc xc) # k' xc # map k' rc =
    (if b4 then [] else [k (node G x)]) @ (if b5 then [] else [k x]) @ tailR"
  using Ek hr hrc by (simp add: cpring_of_def tailR_def)

lemma RHS: "map k (mask (map Not (b1 # b2 # mr')) (cpring_of (CpH # cp))) =
    (if b1 then [] else [k E3.Xe]) @ (if b2 then [] else [k E3.XH]) @ tailR"
  unfolding cpring_of_def cpH fst_conv snd_conv ringH tailR_def by simp

lemma finvc: "a \<in> Ec.D \<Longrightarrow> b \<in> Ec.D \<Longrightarrow> fconnect (face Gc) a b \<Longrightarrow> k' a = k' b"
proof -
  assume ab: "fconnect (face Gc) a b"
  have "\<forall>y \<in> Ec.D. k' (face Gc y) = k' y" using col by (simp add: coloring_def)
  then show "k' a = k' b" by (rule Ec.coloring_cface[OF _ ab])
qed

lemma kprop: "y \<in> set ccG \<Longrightarrow> k (face G (edge G y)) = k y"
proof -
  assume y: "y \<in> set ccG"
  have yD: "y \<in> E3.D" using y ccGD by blast
  have "k (edge G y) = k y" using cc_edge[OF kG yD] y by simp
  moreover have "k (face G (edge G y)) = k (edge G y)" using kG yD by (simp add: cc_coloring_def)
  ultimately show ?thesis by simp
qed

lemma succ_tail: "(fex # r3) ! Suc i = face G (edge G ((fex # r3) ! i))" if "Suc i < length (fex # r3)" for i
  using E3.cpring_succ[of "Suc (Suc i)" x] that hr by simp

lemma mask_sub_ccG: "set (mask mr' (fex # r3)) \<subseteq> set ccG" by (auto simp: ccG_def)

lemma hd_tail: "tailR \<noteq> [] \<Longrightarrow> hd tailR = k fex"
proof -
  assume ne: "tailR \<noteq> []"
  then have ne': "mask (map Not mr') (fex # r3) \<noteq> []" by (simp add: tailR_def)
  have "k (hd (mask (map Not mr') (fex # r3))) = k (hd (fex # r3))"
    by (rule mask_head_color[OF succ_tail _ _ ne']) (use lmr3 kprop mask_sub_ccG in auto)
  then show ?thesis using ne' by (simp add: tailR_def hd_map)
qed

lemma nx_contract: "b4 \<Longrightarrow> k (node G x) = k x"
proof -
  assume b4: b4
  have "node G x \<in> set ccG" unfolding ccG_def using b4 by simp
  from kprop[OF this] show ?thesis by (simp add: E3.nodeK)
qed

lemma x_contract: "b5 \<Longrightarrow> k x = k fex"
proof -
  assume b5: b5
  have "x \<in> set ccG" unfolding ccG_def using b5 by simp
  from kprop[OF this] show ?thesis by (simp add: fex_def)
qed

lemma all_contract: "tailR = [] \<Longrightarrow> k fex = k (node G x)"
proof -
  assume e: "tailR = []"
  have allm: "\<forall>b \<in> set mr'. b"
  proof (rule mask_Not_nil[of mr' "fex # r3"])
    show "mask (map Not mr') (fex # r3) = []" using e by (simp add: tailR_def)
    show "length mr' = length (fex # r3)" using lmr3 by simp
  qed
  have mt: "mask mr' (fex # r3) = fex # r3" using allm lmr3 by (intro mask_true) simp_all
  have "\<forall>i < length (fex # r3). k ((fex # r3) ! i) = k (face G (edge G (last (fex # r3))))"
  proof (intro allI impI)
    fix i assume i: "i < length (fex # r3)"
    show "k ((fex # r3) ! i) = k (face G (edge G (last (fex # r3))))"
      using i
    proof (induction "length (fex # r3) - Suc i" arbitrary: i)
      case 0
      then have il: "i = length r3" by simp
      have "(fex # r3) ! i \<in> set (mask mr' (fex # r3))"
        using mt il by (metis length_Cons lessI nth_mem)
      then have "k (face G (edge G ((fex # r3) ! i))) = k ((fex # r3) ! i)"
        using kprop mask_sub_ccG by blast
      moreover have "(fex # r3) ! i = last (fex # r3)" using il by (simp add: last_conv_nth)
      ultimately show ?case by simp
    next
      case (Suc d)
      have si: "Suc i < length (fex # r3)" using Suc.hyps(2) by simp
      have IH: "k ((fex # r3) ! Suc i) = k (face G (edge G (last (fex # r3))))"
        using Suc.hyps(1)[of "Suc i"] Suc.hyps(2) si by simp
      have "(fex # r3) ! i \<in> set (mask mr' (fex # r3))"
        using mt Suc.prems by (metis nth_mem)
      then have "k (face G (edge G ((fex # r3) ! i))) = k ((fex # r3) ! i)"
        using kprop mask_sub_ccG by blast
      then show ?case using IH succ_tail[OF si] by simp
    qed
  qed
  then have "k fex = k (face G (edge G (last (fex # r3))))" by (metis length_greater_0_conv list.distinct(1) nth_Cons_0)
  moreover have "last (fex # r3) = last (cpring G x)" using hr by simp
  ultimately show ?thesis using E3.cpring_last[OF E3.x0D] by simp
qed

text \<open>Subcases where the contract program is unchanged.\<close>

lemma case_b3:
  assumes "b3" "\<not> b1" "\<not> b2" "\<not> b4" "\<not> b5"
  shows "map k' (cpring_of cpc0) = map k (mask (map Not (b1 # b2 # mr')) (cpring_of (CpH # cp)))"
proof -
  have "map k' (cpring_of cpc0) = k (node G x) # k x # tailR"
    using Ek2 assms hrc by (simp add: cpring_of_def)
  then show ?thesis unfolding RHS using assms kXeN b3_iff by simp
qed

lemma case_b1b5:
  assumes "b1" "\<not> b2" "\<not> b4" "b5"
  shows "map k' (cpring_of cpc0) = map k (mask (map Not (b1 # b2 # mr')) (cpring_of (CpH # cp)))"
proof -
  have "map k' (cpring_of cpc0) = k (node G x) # tailR" using Ek2 assms hrc by (simp add: cpring_of_def)
  then show ?thesis unfolding RHS using assms b1_iff by simp
qed

lemma case_b2b4:
  assumes "\<not> b1" "b2" "b4" "\<not> b5"
  shows "map k' (cpring_of cpc0) = map k (mask (map Not (b1 # b2 # mr')) (cpring_of (CpH # cp)))"
proof -
  have "map k' (cpring_of cpc0) = k x # tailR" using Ek2 assms hrc by (simp add: cpring_of_def)
  then show ?thesis unfolding RHS using assms kXeN nx_contract by simp
qed


lemma case_U:
  assumes nb1: "\<not> b1" and nb2: "\<not> b2" and Er: "map k' (cpring Gc xc) = tailR"
    and kXe: "k E3.Xe = k fex"
  shows "\<exists>k''. coloring (cpG (CpU # cpc0)) k'' \<and>
    map k'' (cpring_of (CpU # cpc0)) = map k (mask (map Not (b1 # b2 # mr')) (cpring_of (CpH # cp)))"
proof -
  have cpU: "cpmap (CpU # cpc0) = (Ec.GU, Ec.X)"
    using cpmap_Cons_cases(3)[of cpc0 Gc xc] Ec.ecp_axioms by simp
  have ringU: "cpring Ec.GU Ec.X = Ec.Xe # Ec.X # cpring Gc xc" by (rule Ec.cpring_GU)
  have tne: "tailR \<noteq> []" using Er Ec.cpring_ne[of xc] by auto
  have hnc: "k' (node Gc xc) = k fex"
    using Er hrc hd_tail[OF tne] by (metis list.sel(1) list.simps(9))
  have kXHne: "k E3.XH \<noteq> k fex" using b2_iff nb2 by simp
  define k'' where "k'' = ext_col Ec.GU Ec.D k' (k E3.XH)"
  have invU: "\<And>a b. a \<in> Ec.D \<Longrightarrow> b \<in> Ec.D \<Longrightarrow> fconnect (face Ec.GU) a b \<Longrightarrow> k' a = k' b"
    using finvc Ec.cface_GU_old by blast
  have k''old: "k'' y = k' y" if "y \<in> Ec.D" for y
    unfolding k''_def by (rule Ec.U.ext_col_old[OF invU that])
  have k''X: "k'' Ec.X = k E3.XH"
    unfolding k''_def by (rule Ec.U.ext_col_new) (use Ec.cface_GU_X in auto)
  have k''Xe: "k'' Ec.Xe = k fex"
    using Ec.U.ext_col_band[OF invU Ec.nx0D Ec.cface_GU_Xe] hnc by (simp add: k''_def)
  have "map k'' (cpring Gc xc) = map k' (cpring Gc xc)"
    using k''old Ec.ringD by (intro map_cong) auto
  then have ring_eq: "map k'' (cpring_of (CpU # cpc0)) = k fex # k E3.XH # tailR"
    using k''X k''Xe Er unfolding cpring_of_def cpU fst_conv snd_conv ringU by (simp only: list.map)
  have colU: "coloring Ec.GU k''"
    unfolding coloring_def
  proof (intro conjI ballI)
    fix u assume u: "u \<in> darts Ec.GU"
    show "k'' (face Ec.GU u) = k'' u" unfolding k''_def by (rule Ec.U.ext_col_face)
    consider "u = Ec.X" | "u = Ec.Xe" | "u \<in> Ec.D" using u by auto
    then show "k'' (edge Ec.GU u) \<noteq> k'' u"
    proof cases
      case 1 then show ?thesis using k''X k''Xe kXHne by simp
    next
      case 2 then show ?thesis using k''X k''Xe kXHne by simp
    next
      case 3
      have eu: "edge Ec.GU u = edge Gc u" "edge Gc u \<in> Ec.D" using 3 by simp_all
      have sub: "Ec.D \<subseteq> darts Ec.GU" by auto
      have adjold: "\<And>a b. a \<in> Ec.D \<Longrightarrow> b \<in> Ec.D \<Longrightarrow> adj Ec.GU a b \<Longrightarrow> adj Gc a b"
        using Ec.adj_GU_old by blast
      have fe: "fconnect (face Ec.GU) (edge Ec.GU u) (edge Gc u)" unfolding eu(1) by (rule fconnect_refl)
      show ?thesis unfolding k''_def
        by (rule ext_col_edge_old[OF Ec.U.hypermap_axioms Ec.hypermap_axioms sub col invU adjold
              3 fconnect_refl eu(2) fe])
    qed
  qed
  show ?thesis using colU ring_eq cpU RHS nb1 nb2 kXe by (intro exI[of _ k'']) simp
qed

lemma case_Yc:
  assumes nb1: "\<not> b1" and nb2: "\<not> b2" and hn: "k' (node Gc xc) = k E3.Xe"
    and Etl: "map k' (xc # rc) = tailR" and ne1: "k E3.XH \<noteq> k E3.Xe" and ne2: "k E3.XH \<noteq> k fex"
  shows "\<exists>k''. coloring (cpG (CpY # cpc0)) k'' \<and>
    map k'' (cpring_of (CpY # cpc0)) = map k (mask (map Not (b1 # b2 # mr')) (cpring_of (CpH # cp)))"
proof -
  interpret Ec2: ecp2 Gc xc unfolding ecp2_def by (rule Ec.ecp_axioms)
  have cpYc: "cpmap (CpY # cpc0) = (Ec2.GY, Ec2.XY)"
    using cpmap_Cons_cases(4)[of cpc0 Gc xc] Ec2.ecp2_axioms by simp
  have ringYc: "cpring Ec2.GY Ec2.XY = Ec.Xe # Ec2.XY # xc # rc" using Ec2.cpring_GY hrc by simp
  have tne: "tailR \<noteq> []" using Etl by auto
  have hxc: "k' xc = k fex" using Etl hd_tail[OF tne] by (metis list.sel(1) list.simps(9))
  define k'' where "k'' = ext_col Ec2.GY Ec.D k' (k E3.XH)"
  have invY: "\<And>a b. a \<in> Ec.D \<Longrightarrow> b \<in> Ec.D \<Longrightarrow> fconnect (face Ec2.GY) a b \<Longrightarrow> k' a = k' b"
    using finvc Ec2.cface_GY_old by blast
  have k''old: "k'' y = k' y" if "y \<in> Ec.D" for y
    unfolding k''_def by (rule Ec2.T.NN.ext_col_old[OF invY that])
  have nYc: "node Ec2.GY Ec2.XY = Ec.Xe" using Ec2.T.NN.head_cpring[of Ec2.XY] ringYc by (metis list.inject)
  have XeNc: "fconnect (face Ec2.GY) Ec.Xe (node Gc xc)" using Ec2.cface_node_GY nYc by simp
  have k''Xe: "k'' Ec.Xe = k E3.Xe"
    using Ec2.T.NN.ext_col_band[OF invY Ec.nx0D XeNc] hn by (simp add: k''_def)
  have nXYold: "\<not> (\<exists>y \<in> Ec.D. fconnect (face Ec2.GY) u y)" if "u = Ec2.XY \<or> u = Ec.X" for u
  proof
    assume "\<exists>y \<in> Ec.D. fconnect (face Ec2.GY) u y"
    then obtain y where yD: "y \<in> Ec.D" and uy: "fconnect (face Ec2.GY) u y" by blast
    have "fconnect (face Ec2.GY) Ec2.XY u" using that Ec2.cface_GY_XY by auto
    then have "fconnect (face Ec2.GY) Ec2.XY y" by (rule fconnect_trans[OF _ uy])
    then show False using yD Ec2.cface_GY_XY by auto
  qed
  have k''XY: "k'' Ec2.XY = k E3.XH" unfolding k''_def by (rule Ec2.T.NN.ext_col_new) (use nXYold in blast)
  have k''X: "k'' Ec.X = k E3.XH" unfolding k''_def by (rule Ec2.T.NN.ext_col_new) (use nXYold in blast)
  have k''TXe: "k'' Ec2.T.Xe = k fex"
    using Ec2.T.NN.ext_col_band[OF invY Ec.x0D Ec2.cface_GY_TXe] hxc by (simp add: k''_def)
  have "map k'' (xc # rc) = map k' (xc # rc)" using k''old rcD Ec.x0D by (intro map_cong) auto
  then have Etl'': "map k'' (xc # rc) = tailR" using Etl by (simp only:)
  have ring_eq: "map k'' (cpring_of (CpY # cpc0)) = k E3.Xe # k E3.XH # tailR"
    using k''XY k''Xe Etl'' unfolding cpring_of_def cpYc fst_conv snd_conv ringYc by simp
  have colY: "coloring Ec2.GY k''"
    unfolding coloring_def
  proof (intro conjI ballI)
    fix u assume u: "u \<in> darts Ec2.GY"
    show "k'' (face Ec2.GY u) = k'' u" unfolding k''_def by (rule Ec2.T.NN.ext_col_face)
    consider "u = Ec.X" | "u = Ec.Xe" | "u = Ec2.XY" | "u = Ec2.T.Xe" | "u \<in> Ec.D"
      using u Ec2.darts_GY by blast
    then show "k'' (edge Ec2.GY u) \<noteq> k'' u"
    proof cases
      case 1 then show ?thesis using k''X k''Xe ne1 by simp
    next
      case 2 then show ?thesis using k''X k''Xe ne1 by simp
    next
      case 3 then show ?thesis using k''XY k''TXe ne2 by simp
    next
      case 4 then show ?thesis using k''XY k''TXe ne2 by simp
    next
      case 5
      have eu: "edge Ec2.GY u = edge Gc u" "edge Gc u \<in> Ec.D"
        using Ec2.face_GY_old[OF 5] 5 by simp_all
      have sub: "Ec.D \<subseteq> darts Ec2.GY" using Ec2.darts_GY by blast
      have adjold: "\<And>a b. a \<in> Ec.D \<Longrightarrow> b \<in> Ec.D \<Longrightarrow> adj Ec2.GY a b \<Longrightarrow> adj Gc a b"
        using Ec2.adj_GY_old by blast
      have fe: "fconnect (face Ec2.GY) (edge Ec2.GY u) (edge Gc u)" unfolding eu(1) by (rule fconnect_refl)
      show ?thesis unfolding k''_def
        by (rule ext_col_edge_old[OF Ec2.T.NN.hypermap_axioms Ec.hypermap_axioms sub col invY adjold
              5 fconnect_refl eu(2) fe])
    qed
  qed
  show ?thesis using colY ring_eq cpYc RHS nb1 nb2 by (intro exI[of _ k'']) simp
qed

lemma ring_c2: "rc \<noteq> [] \<Longrightarrow> face Gc (edge Gc xc) = hd rc"
proof -
  assume ne: "rc \<noteq> []"
  have l: "Suc 1 < length (cpring Gc xc)" using hrc ne by simp
  have "cpring Gc xc ! Suc 1 = face Gc (edge Gc (cpring Gc xc ! 1))" by (rule Ec.cpring_succ[OF l])
  then show ?thesis using hrc ne by (simp add: hd_conv_nth numeral_2_eq_2)
qed

lemma ring_c2_nil: "rc = [] \<Longrightarrow> face Gc (edge Gc xc) = node Gc xc"
  using Ec.cpring_last[OF Ec.x0D] hrc by simp

lemma k'fe: "k' (face Gc (edge Gc xc)) = (if rc = [] then k' (node Gc xc) else hd (map k' rc))"
  using ring_c2 ring_c2_nil by (cases "rc = []") (simp_all add: hd_map)

lemma case_K:
  assumes nb4: "\<not> b4" and nb5: "\<not> b5" and fne: "k fex \<noteq> k (node G x)"
    and R: "map k (mask (map Not (b1 # b2 # mr')) (cpring_of (CpH # cp))) = k (node G x) # tailR"
  shows "\<exists>k''. coloring (cpG (CpK # cpc0)) k'' \<and>
    map k'' (cpring_of (CpK # cpc0)) = map k (mask (map Not (b1 # b2 # mr')) (cpring_of (CpH # cp)))"
proof -
  interpret Ek: ecpk Gc xc by (rule ecpk_intro[OF Ec.hypermap_axioms Ec.x0D])
  have cpK: "cpmap (CpK # cpc0) = (Ek.GK, Ek.pK)"
    using cpmap_Cons_cases(5)[of cpc0 Gc xc] Ek.ecpk_axioms by simp
  have ringK: "cpring Ek.GK Ek.pK = Ec.X # rc" using Ek.cpring_GK by (simp add: rc_def)
  have E3': "k' (node Gc xc) = k (node G x)" "map k' rc = tailR" using Ek2 nb4 nb5 by simp_all
  have tne: "tailR \<noteq> []" using all_contract fne by blast
  have rne: "rc \<noteq> []" using E3'(2) tne by auto
  have kfe: "k' (face Gc (edge Gc xc)) = k fex"
    using k'fe rne E3'(2) hd_tail[OF tne] by simp
  have ke: "k' (edge Gc xc) = k fex"
    using finvc[of "edge Gc xc" "face Gc (edge Gc xc)"] kfe Ec.x0D by simp
  define k'' where "k'' = ext_col Ek.GK Ec.D k' (k E3.XH)"
  have invK: "\<And>a b. a \<in> Ec.D \<Longrightarrow> b \<in> Ec.D \<Longrightarrow> fconnect (face Ek.GK) a b \<Longrightarrow> k' a = k' b"
    using finvc Ek.cface_GK_old by blast
  have diffK: "k' a \<noteq> k' b" if aD: "a \<in> Ec.D" and bD: "b \<in> Ec.D" and ab: "adj Ek.GK a b" for a b
  proof -
    have exD: "edge Gc xc \<in> Ec.D" using Ec.x0D by simp
    consider "adj Gc a b" | "fconnect (face Gc) (edge Gc xc) a" "fconnect (face Gc) (node Gc xc) b"
      | "fconnect (face Gc) (edge Gc xc) b" "fconnect (face Gc) (node Gc xc) a"
      using Ek.adj_GK_old[OF aD bD] ab by blast
    then show ?thesis
    proof cases
      case 1 then show ?thesis by (rule Ec.coloring_adj[OF col aD])
    next
      case 2
      have "k' a = k' (edge Gc xc)" using finvc[OF exD aD 2(1)] by simp
      moreover have "k' b = k' (node Gc xc)" using finvc[OF Ec.nx0D bD 2(2)] by simp
      ultimately show ?thesis using ke E3'(1) fne by simp
    next
      case 3
      have "k' b = k' (edge Gc xc)" using finvc[OF exD bD 3(1)] by simp
      moreover have "k' a = k' (node Gc xc)" using finvc[OF Ec.nx0D aD 3(2)] by simp
      ultimately show ?thesis using ke E3'(1) fne by simp
    qed
  qed
  have k''old: "k'' y = k' y" if "y \<in> Ec.D" for y
    unfolding k''_def by (rule Ek.K.NN.ext_col_old[OF invK that])
  have k''X: "k'' Ec.X = k (node G x)"
    using Ek.K.NN.ext_col_band[OF invK Ec.nx0D Ek.K.cface_GN_X] E3'(1) by (simp add: k''_def)
  have "map k'' rc = map k' rc" using k''old rcD by (intro map_cong) auto
  then have ring_eq: "map k'' (cpring_of (CpK # cpc0)) = k (node G x) # tailR"
    using k''X E3'(2) unfolding cpring_of_def cpK fst_conv snd_conv ringK by simp
  have colK: "coloring Ek.GK k''"
    unfolding coloring_def
  proof (intro conjI ballI)
    fix u assume u: "u \<in> darts Ek.GK"
    show "k'' (face Ek.GK u) = k'' u" unfolding k''_def by (rule Ek.K.NN.ext_col_face)
    obtain y1 where y1: "y1 \<in> Ec.D" "fconnect (face Ek.GK) u y1" using Ek.fband_GK[OF u] by blast
    have eu: "edge Ek.GK u \<in> darts Ek.GK" by (rule Ek.K.NN.E.closed[THEN iffD2, OF u])
    obtain y2 where y2: "y2 \<in> Ec.D" "fconnect (face Ek.GK) (edge Ek.GK u) y2" using Ek.fband_GK[OF eu] by blast
    show "k'' (edge Ek.GK u) \<noteq> k'' u" unfolding k''_def
      by (rule ext_col_edge_gen[OF Ek.K.NN.hypermap_axioms invK diffK y1 y2])
  qed
  show ?thesis using colK ring_eq cpK R by (intro exI[of _ k'']) simp
qed

lemma case_Hc:
  assumes nb: "\<not> b1" "\<not> b2" "\<not> b3" "\<not> b4" "\<not> b5"
  shows "\<exists>k''. coloring (cpG (CpH # cpc0)) k'' \<and>
    map k'' (cpring_of (CpH # cpc0)) = map k (mask (map Not (b1 # b2 # mr')) (cpring_of (CpH # cp)))"
proof -
  interpret Ec3: ecp3 Gc xc using Ec.hypermap_axioms Ec.x0D prc by (intro ecp3_intro)
  have cpHc: "cpmap (CpH # cpc0) = (Ec3.GH, Ec3.XH)" using cpmap_H[of cpc0 Gc xc] Ec3.ecp2h_axioms by simp
  have ringHc: "cpring Ec3.GH Ec3.XH = Ec.Xe # Ec3.XH # rc" using Ec3.cpring_GH by (simp add: rc_def)
  have E3': "k' (node Gc xc) = k (node G x)" "k' xc = k x" "map k' rc = tailR" using Ek2 nb by simp_all
  have kXHn: "k E3.XH \<noteq> k (node G x)" using b1_iff nb(1) by simp
  have kXHx: "k E3.XH \<noteq> k x" using b3_iff nb(3) by metis
  have kXHf: "k E3.XH \<noteq> k fex" using b2_iff nb(2) by simp
  have kfe: "k E3.XH \<noteq> k' (face Gc (edge Gc xc))"
  proof (cases "rc = []")
    case True then show ?thesis using k'fe E3'(1) kXHn by simp
  next
    case False
    then have "tailR \<noteq> []" using E3'(3) by auto
    then show ?thesis using k'fe False E3'(3) hd_tail kXHf by simp
  qed
  define k'' where "k'' = ext_col Ec3.GH Ec.D k' (k E3.XH)"
  have invH: "\<And>a b. a \<in> Ec.D \<Longrightarrow> b \<in> Ec.D \<Longrightarrow> fconnect (face Ec3.GH) a b \<Longrightarrow> k' a = k' b"
    using finvc Ec3.cface_GH_old by blast
  have k''old: "k'' y = k' y" if "y \<in> Ec.D" for y
    unfolding k''_def by (rule Ec3.T2.NN.ext_col_old[OF invH that])
  have nHc: "node Ec3.GH Ec3.XH = Ec.Xe" using Ec3.T2.NN.head_cpring[of Ec3.XH] ringHc by (metis list.inject)
  have XeNc: "fconnect (face Ec3.GH) Ec.Xe (node Gc xc)" using Ec3.cface_node_GH nHc by simp
  have fexcD: "face Gc (edge Gc xc) \<in> Ec.D" using Ec.x0D by simp
  have k''Xe: "k'' Ec.Xe = k (node G x)"
    using Ec3.T2.NN.ext_col_band[OF invH Ec.nx0D XeNc] E3'(1) by (simp add: k''_def)
  have k''TXe: "k'' Ec3.T.Xe = k x"
    using Ec3.T2.NN.ext_col_band[OF invH Ec.x0D Ec3.cface_GH_TXe] E3'(2) by (simp add: k''_def)
  have k''T2Xe: "k'' Ec3.T2.Xe = k' (face Gc (edge Gc xc))"
    using Ec3.T2.NN.ext_col_band[OF invH fexcD Ec3.cface_GH_T2Xe] by (simp add: k''_def)
  have nXHold: "\<not> (\<exists>y \<in> Ec.D. fconnect (face Ec3.GH) u y)" if "u = Ec3.XH \<or> u = Ec3.XY \<or> u = Ec.X" for u
  proof
    assume "\<exists>y \<in> Ec.D. fconnect (face Ec3.GH) u y"
    then obtain y where yD: "y \<in> Ec.D" and uy: "fconnect (face Ec3.GH) u y" by blast
    have "fconnect (face Ec3.GH) Ec3.XH u" using that Ec3.cface_GH_XH by auto
    then have "fconnect (face Ec3.GH) Ec3.XH y" by (rule fconnect_trans[OF _ uy])
    then show False using yD Ec3.cface_GH_XH by auto
  qed
  have k''new: "k'' u = k E3.XH" if "u = Ec3.XH \<or> u = Ec3.XY \<or> u = Ec.X" for u
    unfolding k''_def by (rule Ec3.T2.NN.ext_col_new) (use nXHold[OF that] in blast)
  have "map k'' rc = map k' rc" using k''old rcD by (intro map_cong) auto
  then have ring_eq: "map k'' (cpring_of (CpH # cpc0)) = k (node G x) # k E3.XH # tailR"
    using k''Xe k''new[of Ec3.XH] E3'(3) unfolding cpring_of_def cpHc fst_conv snd_conv ringHc by simp
  have colH: "coloring Ec3.GH k''"
    unfolding coloring_def
  proof (intro conjI ballI)
    fix u assume u: "u \<in> darts Ec3.GH"
    show "k'' (face Ec3.GH u) = k'' u" unfolding k''_def by (rule Ec3.T2.NN.ext_col_face)
    consider "u = Ec.X" | "u = Ec.Xe" | "u = Ec3.XY" | "u = Ec3.T.Xe" | "u = Ec3.XH" | "u = Ec3.T2.Xe"
      | "u \<in> Ec.D" using u Ec3.darts_GH by blast
    then show "k'' (edge Ec3.GH u) \<noteq> k'' u"
    proof cases
      case 1
      have "edge Ec3.GH Ec.X = Ec.Xe" by simp
      then show ?thesis using 1 k''new[of Ec.X] k''Xe kXHn by simp
    next
      case 2
      have "edge Ec3.GH Ec.Xe = Ec.X" by simp
      then show ?thesis using 2 k''new[of Ec.X] k''Xe kXHn by simp
    next
      case 3
      have "edge Ec3.GH Ec3.XY = Ec3.T.Xe" by simp
      then show ?thesis using 3 k''new[of Ec3.XY] k''TXe kXHx by simp
    next
      case 4
      have "edge Ec3.GH Ec3.T.Xe = Ec3.XY" by simp
      then show ?thesis using 4 k''new[of Ec3.XY] k''TXe kXHx by simp
    next
      case 5
      have "edge Ec3.GH Ec3.XH = Ec3.T2.Xe" by simp
      then show ?thesis using 5 k''new[of Ec3.XH] k''T2Xe kfe by simp
    next
      case 6
      have "edge Ec3.GH Ec3.T2.Xe = Ec3.XH" by simp
      then show ?thesis using 6 k''new[of Ec3.XH] k''T2Xe kfe by simp
    next
      case 7
      have eu: "edge Ec3.GH u = edge Gc u" "edge Gc u \<in> Ec.D" using 7 by simp_all
      have sub: "Ec.D \<subseteq> darts Ec3.GH" using Ec3.darts_GH by blast
      have adjold: "\<And>a b. a \<in> Ec.D \<Longrightarrow> b \<in> Ec.D \<Longrightarrow> adj Ec3.GH a b \<Longrightarrow> adj Gc a b"
        using Ec3.adj_GH_old by blast
      have fe: "fconnect (face Ec3.GH) (edge Ec3.GH u) (edge Gc u)" unfolding eu(1) by (rule fconnect_refl)
      show ?thesis unfolding k''_def
        by (rule ext_col_edge_old[OF Ec3.T2.NN.hypermap_axioms Ec.hypermap_axioms sub col invH adjold
              7 fconnect_refl eu(2) fe])
    qed
  qed
  have "map k (mask (map Not (b1 # b2 # mr')) (cpring_of (CpH # cp))) = k (node G x) # k E3.XH # tailR"
    using RHS nb kXeN by simp
  then show ?thesis using colH ring_eq cpHc by (intro exI[of _ k'']) simp
qed

lemma case_A:
  assumes b1: "b1" and b2: "b2" and nb4: "\<not> b4" and nb5: "\<not> b5" and tne: "tailR \<noteq> []"
  shows "\<exists>k''. coloring (cpG (CpA # cpc0)) k'' \<and>
    map k'' (cpring_of (CpA # cpc0)) = map k (mask (map Not (b1 # b2 # mr')) (cpring_of (CpH # cp)))"
proof -
  interpret Ea: ecpa Gc xc by (rule ecpa_intro[OF Ec.hypermap_axioms Ec.x0D])
  have cpA: "cpmap (CpA # cpc0) = (Ea.GA, Ea.pA)"
    using cpmap_Cons_cases(6)[of cpc0 Gc xc] Ea.ecpa_axioms by simp
  have E3': "k' (node Gc xc) = k (node G x)" "k' xc = k x" "map k' rc = tailR" using Ek2 nb4 nb5 by simp_all
  have rne: "rc \<noteq> []" using E3'(3) tne by auto
  have lngc: "long_cpring Gc xc" using Ec.size_long_cpring hrc rne by simp
  have ringA: "cpring Ea.GA Ea.pA = rc" using Ea.cpring_GA lngc by (simp add: rc_def)
  have EhA: "k' (face Gc (edge Gc xc)) = k' (node Gc xc)"
    using k'fe rne E3' hd_tail[OF tne] b1_iff b2_iff b1 b2 by simp
  have kf: "k' (face Gc y) = k' y" if "y \<in> Ec.D" for y using col that by (simp add: coloring_def)
  have ke: "k' (edge Gc y) \<noteq> k' y" if "y \<in> Ec.D" for y using col that by (simp add: coloring_def)
  have keFe: "k' (edge Gc y) = k' (face Gc (edge Gc y))" if "y \<in> Ec.D" for y using kf[of "edge Gc y"] that by simp
  have colA: "coloring Ea.GA k'"
    unfolding coloring_def
  proof (intro conjI ballI)
    fix u assume u: "u \<in> darts Ea.GA"
    then have uD: "u \<in> Ec.D" by simp
    show "k' (face Ea.GA u) = k' u"
    proof (cases "fconnect (face Gc) (edge Gc xc) (node Gc xc)")
      case True then show ?thesis using kf[OF uD] by simp
    next
      case False
      show ?thesis
      proof (cases "u = edge Gc xc")
        case True
        have "k' (node Gc xc) = k' (edge Gc xc)" using EhA keFe[OF Ec.x0D] by simp
        then show ?thesis using False True by simp
      next
        case nu: False
        show ?thesis
        proof (cases "face Gc u = node Gc xc")
          case True
          have "k' (face Gc (edge Gc xc)) = k' u" using EhA kf[OF uD] True by simp
          then show ?thesis using False nu True by simp
        next
          case nf: False
          then show ?thesis using False nu kf[OF uD] by simp
        qed
      qed
    qed
    show "k' (edge Ea.GA u) \<noteq> k' u"
    proof (cases "fconnect (face Gc) (edge Gc xc) (node Gc xc)")
      case False then show ?thesis using ke[OF uD] by simp
    next
      case cc: True
      show ?thesis
      proof (cases "u = xc")
        case True
        have nnD: "node Gc (node Gc xc) \<in> Ec.D" using Ec.x0D by simp
        have "k' (edge Gc (node Gc (node Gc xc))) = k' (node Gc xc)"
          using keFe[OF nnD] by (simp add: Ec.nodeK)
        also have "\<dots> = k' (edge Gc xc)" using EhA keFe[OF Ec.x0D] by simp
        finally show ?thesis using cc True ke[OF Ec.x0D] by simp
      next
        case nx: False
        show ?thesis
        proof (cases "u = node Gc (node Gc xc)")
          case True
          have nnD: "node Gc (node Gc xc) \<in> Ec.D" using Ec.x0D by simp
          have "k' (edge Gc xc) = k' (node Gc xc)" using EhA keFe[OF Ec.x0D] by simp
          also have "\<dots> = k' (edge Gc (node Gc (node Gc xc)))" using keFe[OF nnD] by (simp add: Ec.nodeK)
          finally show ?thesis using cc nx True ke[OF nnD] by simp
        next
          case False then show ?thesis using cc nx ke[OF uD] by simp
        qed
      qed
    qed
  qed
  have "map k' (cpring_of (CpA # cpc0)) = tailR"
    using E3'(3) unfolding cpring_of_def cpA fst_conv snd_conv ringA .
  then show ?thesis using colA cpA RHS b1 b2 by (intro exI[of _ k']) simp
qed
end

lemma cfctr_H:
  assumes c: "cpmap cp = (G, x)" and h: "config_prog cp" and IH: "cfctr_ok cp"
  shows "cfctr_ok (CpH # cp)"
  unfolding cfctr_ok_def
proof (intro allI impI)
  fix mr mc k cpc
  assume l1: "length mr = cprsize (CpH # cp)" and l2: "length mc = ctrmsize (CpH # cp)"
    and kc: "cc_coloring (cpG (CpH # cp)) (mask mr (cpring_of (CpH # cp)) @ mask mc (ctrenum (CpH # cp))) k"
    and cf: "cfctr mr mc (CpH # cp) = Some cpc"
  have cps: "2 < cprsize cp" by (rule config_prog_size[OF h])
  obtain b1 b2 mr' where mr: "mr = b1 # b2 # mr'" and lmr': "Suc (Suc (length mr')) = cprsize cp"
    using l1 cps by (cases mr rule: remdups_adj.cases) auto
  obtain b3 b4 b5 mc' where mc: "mc = b3 # b4 # b5 # mc'" and lmc': "length mc' = ctrmsize cp"
    using l2 by (auto simp: numeral_eq_Suc length_Suc_conv)
  obtain cpc0 where nsp1: "\<not> nsp b3 b1 b4" and nsp2: "\<not> nsp b3 b2 b5"
    and nall: "\<not> (b1 \<and> b2 \<and> (\<forall>b \<in> set mr'. b))" and cf0: "cfctr (b4 # b5 # mr') mc' cp = Some cpc0"
    and cpc: "cpc = (if b3 then cpc0 else
          if b1 then (if b2 then CpA # cpc0 else if b5 then cpc0 else CpK # cpc0)
          else if b2 then (if b4 then cpc0 else CpK # cpc0)
          else if b4 then (if b5 then CpU # cpc0 else CpY # cpc0)
          else if b5 then CpY # cpc0 else CpH # cpc0)"
    using cf unfolding mr mc by (auto split: if_splits option.splits)
  interpret H: hstep cp G x mr' mc' b1 b2 b3 b4 b5 k
    using c h lmr' lmc' kc by unfold_locales (simp_all add: mr mc)
  have rof: "cpring_of cp = cpring G x" using c by (simp add: cpring_of_def)
  have kG': "cc_coloring (cpG cp) (mask (b4 # b5 # mr') (cpring_of cp) @ mask mc' (ctrenum cp)) k"
    using H.kG c unfolding rof H.hr H.ccG_def H.En_def by simp
  have lG: "length (b4 # b5 # mr') = cprsize cp" using lmr' by simp
  obtain k' where col: "coloring (cpG cpc0) k'"
    and Ek0: "map k' (cpring_of cpc0) = map k (mask (map Not (b4 # b5 # mr')) (cpring_of cp))"
    using IH[unfolded cfctr_ok_def, rule_format, OF lG lmc' kG' cf0] by blast
  interpret H2: hstep2 cp G x mr' mc' b1 b2 b3 b4 b5 k cpc0 k'
    using col Ek0 unfolding rof by unfold_locales simp_all
  have main: "\<exists>k'. coloring (cpG cpc) k' \<and>
      map k' (cpring_of cpc) = map k (mask (map Not (b1 # b2 # mr')) (cpring_of (CpH # cp)))"
  proof (cases b3)
    case True
    then have nb: "\<not> b1" "\<not> b2" "\<not> b4" "\<not> b5" using nsp1 nsp2 by (simp_all add: nsp_def)
    show ?thesis using H2.case_b3[OF True nb] col cpc True by (intro exI[of _ k']) simp
  next
    case nb3: False
    then have n14: "\<not> (b1 \<and> b4)" and n25: "\<not> (b2 \<and> b5)" using nsp1 nsp2 by (simp_all add: nsp_def)
    show ?thesis
    proof (cases b1)
      case b1: True
      show ?thesis
      proof (cases b2)
        case b2: True
        have nb: "\<not> b4" "\<not> b5" using n14 n25 b1 b2 by auto
        have "\<not> (\<forall>b \<in> set mr'. b)" using nall b1 b2 by simp
        then have tne: "H2.tailR \<noteq> []"
          using mask_Not_nil[of mr' "H.fex # H.r3"] H.lmr3 by (auto simp: H2.tailR_def)
        show ?thesis using H2.case_A[OF b1 b2 nb tne] cpc nb3 b1 b2 by simp
      next
        case nb2: False
        have nb4: "\<not> b4" using n14 b1 by simp
        show ?thesis
        proof (cases b5)
          case True
          show ?thesis using H2.case_b1b5[OF b1 nb2 nb4 True] col cpc nb3 b1 nb2 True
            by (intro exI[of _ k']) simp
        next
          case nb5: False
          have fne: "k H.fex \<noteq> k (node G x)" using H.b1_iff H.b2_iff b1 nb2 by simp
          have R: "map k (mask (map Not (b1 # b2 # mr')) (cpring_of (CpH # cp))) = k (node G x) # H2.tailR"
            using H2.RHS b1 nb2 H.b1_iff by simp
          show ?thesis using H2.case_K[OF nb4 nb5 fne R] cpc nb3 b1 nb2 nb5 by simp
        qed
      qed
    next
      case nb1: False
      show ?thesis
      proof (cases b2)
        case b2: True
        have nb5: "\<not> b5" using n25 b2 by simp
        show ?thesis
        proof (cases b4)
          case True
          show ?thesis using H2.case_b2b4[OF nb1 b2 True nb5] col cpc nb3 nb1 b2 True
            by (intro exI[of _ k']) simp
        next
          case nb4: False
          have fne: "k H.fex \<noteq> k (node G x)" using H.b1_iff H.b2_iff nb1 b2 by simp
          have R: "map k (mask (map Not (b1 # b2 # mr')) (cpring_of (CpH # cp))) = k (node G x) # H2.tailR"
            using H2.RHS nb1 b2 H.kXeN by simp
          show ?thesis using H2.case_K[OF nb4 nb5 fne R] cpc nb3 nb1 b2 nb4 by simp
        qed
      next
        case nb2: False
        have ne1: "k H.E3.XH \<noteq> k H.E3.Xe" using H.b1_iff nb1 H.kXeN by simp
        have ne2: "k H.E3.XH \<noteq> k H.fex" using H.b2_iff nb2 by simp
        show ?thesis
        proof (cases b4)
          case b4: True
          show ?thesis
          proof (cases b5)
            case b5: True
            have Er: "map k' (cpring H2.Gc H2.xc) = H2.tailR" using H2.Ek2 H2.hrc b4 b5 by simp
            have kXe: "k H.E3.Xe = k H.fex" using H.kXeN H2.nx_contract[OF b4] H2.x_contract[OF b5] by simp
            show ?thesis using H2.case_U[OF nb1 nb2 Er kXe] cpc nb3 nb1 nb2 b4 b5 by simp
          next
            case nb5: False
            have hn: "k' (node H2.Gc H2.xc) = k H.E3.Xe" and Etl: "map k' (H2.xc # H2.rc) = H2.tailR"
              using H2.Ek2 b4 nb5 H.kXeN H2.nx_contract[OF b4] by simp_all
            show ?thesis using H2.case_Yc[OF nb1 nb2 hn Etl ne1 ne2] cpc nb3 nb1 nb2 b4 nb5 by simp
          qed
        next
          case nb4: False
          show ?thesis
          proof (cases b5)
            case b5: True
            have hn: "k' (node H2.Gc H2.xc) = k H.E3.Xe" and Etl: "map k' (H2.xc # H2.rc) = H2.tailR"
              using H2.Ek2 nb4 b5 H.kXeN by simp_all
            show ?thesis using H2.case_Yc[OF nb1 nb2 hn Etl ne1 ne2] cpc nb3 nb1 nb2 nb4 b5 by simp
          next
            case nb5: False
            show ?thesis using H2.case_Hc[OF nb1 nb2 nb3 nb4 nb5] cpc nb3 nb1 nb2 nb4 nb5 by simp
          qed
        qed
      qed
    qed
  qed
  then show "\<exists>k'. coloring (cpG cpc) k' \<and> map k' (cpring_of cpc) = map k (mask (map Not mr) (cpring_of (CpH # cp)))"
    unfolding mr .
qed

theorem cfctr_correct:
  assumes "length mr = cprsize cp" "length mc = ctrmsize cp"
    and "cc_coloring (cpG cp) (mask mr (cpring_of cp) @ mask mc (ctrenum cp)) k"
    and "cfctr mr mc cp = Some cpc"
  shows "\<exists>k'. coloring (cpG cpc) k' \<and> map k' (cpring_of cpc) = map k (mask (map Not mr) (cpring_of cp))"
  using assms
proof (induction cp arbitrary: mr mc k cpc)
  case Nil then show ?case by simp
next
  case (Cons s cp)
  have cpo: "config_prog (s # cp)" using cfctr_config_prog Cons.prems(4) by auto
  obtain G x where c: "cpmap cp = (G, x)" by (cases "cpmap cp")
  interpret E: ecp G x using hypermap_cpmap[of cp] cpx_in[of cp] c by (intro ecp_intro) simp_all
  show ?case
  proof (cases s)
    case (CpR i)
    have r: "cpring_of (CpR i # cp) = rot i (cpring_of cp)" by (rule cpring_of_CpR)
    have g: "cpG (CpR i # cp) = cpG cp" by (rule cpG_CpR)
    define r0 where "r0 = cpring_of cp"
    have lr0: "length r0 = cprsize cp" by (simp add: r0_def size_ring_cpmap)
    have lmr: "length mr = length r0" using Cons.prems(1) CpR lr0 by simp
    obtain cpc0 where cf0: "cfctr (rotr i mr) mc cp = Some cpc0"
      and cpc: "cpc = CpR (count_list (take i (rotr i mr)) False) # cpc0"
      using Cons.prems(4) CpR by (auto split: option.splits)
    have "set (mask mr (rot i r0)) = set (mask (rotr i mr) r0)"
      using set_mask_rot[of "rotr i mr" r0 i] lmr by (simp add: rot_rotr)
    then have se: "set (mask mr (rot i r0) @ mask mc (ctrenum cp)) = set (mask (rotr i mr) r0 @ mask mc (ctrenum cp))"
      by simp
    have "cc_coloring (cpG cp) (mask mr (rot i r0) @ mask mc (ctrenum cp)) k"
      using Cons.prems(3) unfolding CpR r g r0_def ctrenum.simps .
    then have "cc_coloring (cpG cp) (mask (rotr i mr) r0 @ mask mc (ctrenum cp)) k"
      using cc_coloring_set[OF se] by simp
    then obtain k' where col: "coloring (cpG cpc0) k'"
      and Ek: "map k' (cpring_of cpc0) = map k (mask (map Not (rotr i mr)) r0)"
      using Cons.IH[of "rotr i mr" mc k cpc0] Cons.prems(2) CpR cf0 lmr lr0 by (auto simp: r0_def)
    define j where "j = count_list (take i (rotr i mr)) False"
    have cnt: "count_list (take i (map Not (rotr i mr))) True = j"
      unfolding j_def take_map count_map_Not ..
    have mN: "map Not mr = rot i (map Not (rotr i mr))"
      using map_rot[of Not i "rotr i mr"] rot_rotr[of i mr] by simp
    have "mask (map Not mr) (rot i r0) = mask (rot i (map Not (rotr i mr))) (rot i r0)"
      by (subst mN) (rule refl)
    also have "\<dots> = rot j (mask (map Not (rotr i mr)) r0)"
      using mask_rot[of "map Not (rotr i mr)" r0 i] lmr cnt by simp
    finally have "map k (mask (map Not mr) (rot i r0)) = rot j (map k' (cpring_of cpc0))"
      using Ek by (simp add: map_rot)
    then show ?thesis using col unfolding cpc CpR r cpG_CpR cpring_of_CpR
      by (intro exI[of _ k']) (simp add: map_rot j_def r0_def)
  next
    case CpY
    have IHok: "cfctr_ok cp" unfolding cfctr_ok_def using Cons.IH by blast
    show ?thesis
    proof (cases "cp = []")
      case True
      show ?thesis using cfctr_Y0 Cons.prems unfolding cfctr_ok_def CpY True by blast
    next
      case False
      then have h: "config_prog cp" using cpo CpY by (cases cp) auto
      show ?thesis using cfctr_Y[OF c h IHok] Cons.prems unfolding cfctr_ok_def CpY by blast
    qed
  next
    case CpH
    have IHok: "cfctr_ok cp" unfolding cfctr_ok_def using Cons.IH by blast
    have h: "config_prog cp" using cpo CpH by simp
    show ?thesis using cfctr_H[OF c h IHok] Cons.prems unfolding cfctr_ok_def CpH by blast
  qed (use cpo in simp_all)
qed

end
