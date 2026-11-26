(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Cfcontract2.thy
    The contract of a configuration construction, part 2: sparseness of the contract,
    contract bands and the contract tree.
    Ported from G. Gonthier's Coq development (cfcontract.v).
*)
theory Cfcontract2
  imports Four_Colour_Maps.Cfcontract Four_Colour_Maps.Kempetree
begin

section \<open>Sparse sequences\<close>

lemma sparse_iff:
  assumes "hypermap G"
  shows "sparse G p \<longleftrightarrow> distinct p \<and> (\<forall>a \<in> set p. \<forall>b \<in> set p. fconnect (node G) a b \<longrightarrow> a = b)"
proof -
  interpret P: hypermap "permF G" by (rule hypermap.hypermap_permF[OF assms])
  show ?thesis unfolding sparse_def P.simple_iff by simp
qed

lemma sparse_mset: "mset p = mset q \<Longrightarrow> sparse G p \<longleftrightarrow> sparse G q"
  unfolding sparse_def by (rule simple_mset)

lemma sparse_head_cnode:
  assumes hG: "hypermap G" and ab: "fconnect (node G) a b"
  shows "sparse G (a # p) \<longleftrightarrow> sparse G (b # p)"
proof -
  interpret hypermap G by (rule hG)
  have "fconnect (node G) a y \<longleftrightarrow> fconnect (node G) b y" for y
    using fconnect_trans[OF ab] fconnect_trans[OF N.fconnect_sym[OF ab]] by blast
  then show ?thesis using sparse_Cons[OF hG] by simp
qed

lemma fconnect_closed:
  assumes "fconnect f a z" "a \<in> S" "\<And>y. y \<in> S \<Longrightarrow> f y \<in> S"
  shows "z \<in> S"
  using assms(1) by (induction rule: fconnect_induct) (use assms(2,3) in auto)

lemma fconnect_3cycle:
  assumes ab: "f a = b" and bc: "f b = c" and ca: "f c = a"
  shows "fconnect f a z \<longleftrightarrow> z = a \<or> z = b \<or> z = c"
proof
  assume fz: "fconnect f a z"
  have cl: "f y \<in> {a, b, c}" if yS: "y \<in> {a, b, c}" for y using yS ab bc ca by auto
  have "z \<in> {a, b, c}" by (rule fconnect_closed[OF fz _ cl]) simp
  then show "z = a \<or> z = b \<or> z = c" by simp
next
  have b': "fconnect f a b" using fconnect_step[of f a] ab by simp
  have c': "fconnect f a c" using fconnect_trans[OF b' fconnect_step[of f b]] bc by simp
  assume "z = a \<or> z = b \<or> z = c"
  then show "fconnect f a z" using b' c' by auto
qed

context ecp2
begin

lemma nodeY_X: "node GY X = T.Xe" by simp
lemma nodeY_TXe: "node GY T.Xe = n x0" using long_GU by simp
lemma nodeY_nx0: "node GY (n x0) = X" using long_GU D_neq_XY[OF nx0D] by simp

lemma cnodeY_X: "fconnect (node GY) X z \<longleftrightarrow> z = X \<or> z = T.Xe \<or> z = n x0"
proof
  assume fz: "fconnect (node GY) X z"
  have cl: "node GY y \<in> {X, T.Xe, n x0}" if yS: "y \<in> {X, T.Xe, n x0}" for y
  proof -
    consider "y = X" | "y = T.Xe" | "y = n x0" using yS by blast
    then show ?thesis
    proof cases
      case 1 then show ?thesis by (simp only: nodeY_X insert_iff simp_thms)
    next
      case 2 then show ?thesis by (simp only: nodeY_TXe insert_iff simp_thms)
    next
      case 3 then show ?thesis by (simp only: nodeY_nx0 insert_iff simp_thms)
    qed
  qed
  have "z \<in> {X, T.Xe, n x0}" by (rule fconnect_closed[OF fz _ cl]) (simp only: insert_iff simp_thms)
  then show "z = X \<or> z = T.Xe \<or> z = n x0" by (simp only: insert_iff empty_iff simp_thms)
next
  have a: "fconnect (node GY) X T.Xe" using fconnect_step[of "node GY" X] nodeY_X by simp
  have b: "fconnect (node GY) X (n x0)"
    using fconnect_trans[OF a fconnect_step[of "node GY" T.Xe]] nodeY_TXe by simp
  assume "z = X \<or> z = T.Xe \<or> z = n x0"
  then show "fconnect (node GY) X z" using a b by auto
qed

end

context ecp3
begin

lemma nU_x0: "node GU x0 = n x0" using x0_ne_n by simp
lemma nU_nx0: "node GU (n x0) = X" by simp

lemma nodeY_x0: "node GY x0 = XY"
proof -
  have ne: "x0 \<noteq> XY" "x0 \<noteq> T.Xe" "x0 \<noteq> X" using D_neq_XY[OF x0D] D_neq_X[OF x0D] by auto
  show ?thesis by (simp only: T.GN_simps(3) nU_x0 nU_nx0 ne if_False if_True simp_thms)
qed

lemma neqs_H: "XH \<noteq> T2.Xe" "XY \<noteq> XH" "XY \<noteq> T2.Xe" "T2.Xe \<noteq> XH" "Xe \<noteq> XY" "X \<noteq> XY"
  "X \<noteq> XH" "X \<noteq> T2.Xe" "T.Xe \<noteq> XH" "T.Xe \<noteq> T2.Xe" "T.Xe \<noteq> XY" "T.Xe \<noteq> X"
  by simp_all

lemma nodeH_x0: "node GH x0 = XY"
proof -
  have ne: "x0 \<noteq> XH" "x0 \<noteq> T2.Xe" "x0 \<noteq> XY" using D_neq_XH[OF x0D] D_neq_XY[OF x0D] by auto
  show ?thesis
    by (simp only: T2.GN_simps(3) nodeY_x0 node_GY_XY ne neqs_H if_False if_True simp_thms)
qed

lemma nodeH_XY: "node GH XY = T2.Xe"
  by (simp only: T2.GN_simps(3) neqs_H if_False if_True simp_thms)

lemma nodeH_T2Xe: "node GH T2.Xe = x0"
proof -
  have "edge GY XY = T.Xe" by simp
  then show ?thesis by (simp only: T2.GN_simps(3) neqs_H fY_TXe if_False if_True simp_thms)
qed

lemma nodeH_nx0: "node GH (n x0) = X"
proof -
  have ne: "n x0 \<noteq> XH" "n x0 \<noteq> T2.Xe" "n x0 \<noteq> XY" using D_neq_XH[OF nx0D] D_neq_XY[OF nx0D] by auto
  show ?thesis
    by (simp only: T2.GN_simps(3) nodeY_nx0 nodeY_X ne neqs_H if_False if_True simp_thms)
qed

lemma nodeH_X: "node GH X = T.Xe"
  by (simp only: T2.GN_simps(3) nodeY_X nodeY_TXe neqs_H if_False if_True simp_thms)
     (use D_neq_XY[OF nx0D] in auto)

lemma nodeH_TXe: "node GH T.Xe = n x0"
  by (simp only: T2.GN_simps(3) nodeY_TXe nodeY_nx0 neqs_H if_False if_True simp_thms)

lemma cnodeH_nx0: "fconnect (node GH) (n x0) z \<longleftrightarrow> z = n x0 \<or> z = X \<or> z = T.Xe"
  by (rule fconnect_3cycle[OF nodeH_nx0 nodeH_X nodeH_TXe])

lemma cnodeH_x0: "fconnect (node GH) x0 z \<longleftrightarrow> z = x0 \<or> z = XY \<or> z = T2.Xe"
  by (rule fconnect_3cycle[OF nodeH_x0 nodeH_XY nodeH_T2Xe])

end

section \<open>Sparseness of the contract\<close>

definition ctrlist :: "bool list \<Rightarrow> bool list \<Rightarrow> cprog \<Rightarrow> nat list" where
  "ctrlist mr mc cp = cpx cp # map (edge (cpG cp)) (mask mr (cpring_of cp)) @ insertE (cpG cp) (mask mc (ctrenum cp))"

definition sp_ok :: "cprog \<Rightarrow> bool" where
  "sp_ok cp \<longleftrightarrow> (\<forall>mr mc. length mr = cprsize cp \<longrightarrow> length mc = ctrmsize cp \<longrightarrow>
     cfctr mr mc cp \<noteq> None \<longrightarrow> sparse (cpG cp) (ctrlist mr mc cp))"

lemma nsp_atmost1: "\<not> nsp b1 b2 b3 \<Longrightarrow> length ((if b1 then [a] else []) @ (if b2 then [b] else []) @ (if b3 then [c] else [])) \<le> 1"
  by (auto simp: nsp_def split: if_splits)

lemma sparse_Y:
  assumes c: "cpmap cp = (G, x)" and h: "config_prog cp" and IH: "sp_ok cp"
  shows "sp_ok (CpY # cp)"
  unfolding sp_ok_def
proof (intro allI impI)
  fix mr mc
  assume l1: "length mr = cprsize (CpY # cp)" and l2: "length mc = ctrmsize (CpY # cp)"
    and cf: "cfctr mr mc (CpY # cp) \<noteq> None"
  interpret E: ecp G x using hypermap_cpmap[of cp] cpx_in[of cp] c by (intro ecp_intro) simp_all
  interpret E2: ecp2 G x by (simp add: ecp2_def E.ecp_axioms)
  have hY: "hypermap E2.GY" by (rule E2.T.NN.hypermap_axioms)
  have cq: "cubic_prog cp" by (rule config_prog_cubic[OF h])
  obtain r0 where hr: "cpring G x = node G x # r0" using E.head_cpring[of x] by blast
  have r0D: "set r0 \<subseteq> E.D" using E.ringD hr by auto
  have nxr0: "node G x \<notin> set r0" using E.cpring_distinct[of x] hr by simp
  obtain s0 cp0 where cps: "cp = s0 # cp0" using h by (cases cp) auto
  have cpY: "cpmap (CpY # cp) = (E2.GY, E2.XY)" using cpmap_Cons_cases(4)[OF c E2.ecp2_axioms] by simp
  have ringY: "cpring E2.GY E2.XY = E.Xe # E2.XY # r0" using E2.cpring_GY hr by simp
  define En where "En = ctrenum cp"
  have EnD: "set En \<subseteq> E.D" using ctrenum_darts[of cp] h c by (simp add: En_def)
  have enY: "ctrenum (CpY # cp) = node G x # En" using cps c by (simp add: En_def)
  have lr: "cprsize cp = Suc (length r0)" using size_ring_cpmap[of cp] c hr by (simp add: cpring_of_def)
  obtain b1 b2 mr' where mr: "mr = b1 # b2 # mr'" and lmr': "length mr' = length r0"
    using l1 lr by (metis cprsize.simps(2) length_Suc_conv)
  obtain b3 mc' where mc: "mc = b3 # mc'" and lmc': "length mc' = ctrmsize cp"
    using l2 cps by (metis ctrmsize.simps(3) length_Suc_conv)
  have nspF: "\<not> nsp b1 b2 b3" and cf0: "cfctr (b3 # mr') mc' cp \<noteq> None"
    using cf unfolding mr mc cps by (auto split: if_splits option.splits)
  define pG where "pG = map (edge G) (mask (b3 # mr') (node G x # r0)) @ insertE G (mask mc' En)"
  have spG0: "sparse G (x # pG)"
    using IH[unfolded sp_ok_def, rule_format, of "b3 # mr'" mc'] lmr' lr lmc' cf0 c hr
    by (simp add: ctrlist_def cpring_of_def pG_def En_def)
  have nr: "\<not> fconnect (node G) x y" if "y \<in> set pG" for y
    using spG0 that sparse_Cons[OF E.hypermap_axioms] by blast
  have spG: "sparse G pG" using spG0 sparse_Cons[OF E.hypermap_axioms] by blast
  have pGD: "set pG \<subseteq> E.D"
  proof -
    have a1: "set (mask (b3 # mr') (node G x # r0)) \<subseteq> E.D"
      using set_mask_subset[of "b3 # mr'" "node G x # r0"] r0D E.x0D set_mask_subset[of mr' r0]
      by (auto split: if_splits)
    have a2: "set (mask mc' En) \<subseteq> E.D" using set_mask_subset[of mc' En] EnD by auto
    show ?thesis using a1 E.insertE_D[OF a2] by (auto simp: pG_def)
  qed
  have ringG: "y \<in> set (cpring G x) \<longleftrightarrow> fconnect (node G) x y" for y by (rule E.mem_cpring)
  have nx_ring: "fconnect (node G) x (node G x)" using ringG hr by simp
  have pG_off: "y \<notin> set (cpring G x)" if "y \<in> set pG" for y using nr[OF that] ringG by blast
  define N where "N = (if b1 then [E.X] else []) @ (if b2 then [E2.T.Xe] else []) @ (if b3 then [node G x] else [])"
  have N1: "length N \<le> 1" unfolding N_def by (rule nsp_atmost1[OF nspF])
  have NS: "set N \<subseteq> {E.X, E2.T.Xe, node G x}" by (cases b1; cases b2; cases b3) (simp_all add: N_def)
  have XYnD: "E2.XY \<notin> E.D" and TXenD: "E2.T.Xe \<notin> E.D" using E2.D_neq_XY by blast+
  \<comment> \<open>the new list is a permutation of @{text "XY # N @ pG"}\<close>
  have eYold: "edge E2.GY y = edge G y" if "y \<in> E.D" for y using E2.face_GY_old[OF that] by simp
  have l_eq: "mset (ctrlist mr mc (CpY # cp)) = mset (E2.XY # N @ pG)"
  proof -
    have m1: "map (edge E2.GY) (mask mr' r0) = map (edge G) (mask mr' r0)"
      using set_mask_subset[of mr' r0] r0D eYold by (intro map_cong[OF refl]) blast
    have m2: "insertE E2.GY (mask mc' En) = insertE G (mask mc' En)"
      using set_mask_subset[of mc' En] EnD eYold by (intro insertE_cong) blast
    have eX: "edge E2.GY E.Xe = E.X" and eXY: "edge E2.GY E2.XY = E2.T.Xe" by simp_all
    have enx: "edge E2.GY (node G x) = edge G (node G x)" using eYold E.nx0D by simp
    show ?thesis
      unfolding ctrlist_def cpY fst_conv snd_conv cpring_of_def ringY enY mr mc N_def pG_def
      by (cases b1; cases b2; cases b3;
          simp only: mask.simps if_True if_False list.map insertE.simps insertE_app m1 m2 eX eXY enx
            append.simps append_Nil2 mset.simps mset_append;
          simp add: ac_simps)
  qed
  \<comment> \<open>node classes in the Y map\<close>
  have cXY: "fconnect (node E2.GY) E2.XY z \<longleftrightarrow> z \<in> set (E.Xe # E2.XY # r0)" for z
    using E2.T.NN.mem_cpring[of z E2.XY] ringY by simp
  have cN: "fconnect (node E2.GY) a z \<longleftrightarrow> z = E.X \<or> z = E2.T.Xe \<or> z = node G x"
    if aN: "a \<in> {E.X, E2.T.Xe, node G x}" for a z
  proof -
    have aX: "fconnect (node E2.GY) E.X a" using aN E2.cnodeY_X by auto
    have "fconnect (node E2.GY) a z \<longleftrightarrow> fconnect (node E2.GY) E.X z"
      using fconnect_trans[OF aX] fconnect_trans[OF E2.T.NN.N.fconnect_sym[OF aX]] by blast
    then show ?thesis using E2.cnodeY_X by simp
  qed
  have cold: "fconnect (node E2.GY) a z \<longleftrightarrow> fconnect (node G) a z" if "a \<in> set pG" for a z
  proof -
    have "a \<in> darts (cpG cp)" "a \<notin> set (cpring_of cp)" using that pGD pG_off c by (auto simp: cpring_of_def)
    from cnode_injcp[of "[CpY]", OF _ this] show ?thesis using cpY c by simp
  qed
  have spGi: "distinct pG" "\<And>a b. a \<in> set pG \<Longrightarrow> b \<in> set pG \<Longrightarrow> fconnect (node G) a b \<Longrightarrow> a = b"
    using spG sparse_iff[OF E.hypermap_axioms] by blast+
  have NpG: "y \<notin> set pG" if yN: "y \<in> set N" for y
  proof
    assume yp: "y \<in> set pG"
    have yD: "y \<in> E.D" using yp pGD by blast
    have "y \<noteq> node G x" using pG_off[OF yp] hr by auto
    moreover have "y \<noteq> E.X" using yD by auto
    moreover have "y \<noteq> E2.T.Xe" using yD TXenD by auto
    ultimately show False using yN NS by blast
  qed
  have XYN: "E2.XY \<notin> set N" using NS E2.XY_neq XYnD E.nx0D by auto
  have XYpG: "E2.XY \<notin> set pG" using pGD XYnD by blast
  have Nd: "distinct N" using N1 by (cases N) auto
  have Nsing: "a = b" if "a \<in> set N" "b \<in> set N" for a b using that N1 by (cases N) auto
  have sp: "sparse E2.GY (E2.XY # N @ pG)"
    unfolding sparse_iff[OF hY]
  proof (intro conjI ballI impI)
    show "distinct (E2.XY # N @ pG)" using Nd spGi(1) NpG XYN XYpG by auto
    fix a b assume a: "a \<in> set (E2.XY # N @ pG)" and b: "b \<in> set (E2.XY # N @ pG)"
      and ab: "fconnect (node E2.GY) a b"
    have ba: "fconnect (node E2.GY) b a" by (rule E2.T.NN.N.fconnect_sym[OF ab])
    have offY: "y \<notin> set (E.Xe # E2.XY # r0)" if "y \<in> set N \<union> set pG" for y
    proof -
      have "y \<noteq> E.Xe \<and> y \<noteq> E2.XY"
      proof (cases "y \<in> set pG")
        case True
        then have "y \<in> E.D" using pGD by blast
        then show ?thesis using XYnD by auto
      next
        case False
        then have "y = E.X \<or> y = E2.T.Xe \<or> y = node G x" using that NS by blast
        moreover have "E.X \<noteq> E.Xe" "E.X \<noteq> E2.XY" "E2.T.Xe \<noteq> E.Xe" "E2.T.Xe \<noteq> E2.XY"
          by (simp_all only: E2.XY_neq E.X_neq not_False_eq_True)
        moreover have "node G x \<noteq> E.Xe" "node G x \<noteq> E2.XY" using E.nx0D XYnD by auto
        ultimately show ?thesis by metis
      qed
      then have "y \<noteq> E.Xe" "y \<noteq> E2.XY" by simp_all
      moreover have "y \<notin> set r0"
      proof
        assume yr: "y \<in> set r0"
        then have yD: "y \<in> E.D" using r0D by blast
        show False
        proof (cases "y \<in> set pG")
          case True then show False using pG_off yr hr by auto
        next
          case False
          then have "y = E.X \<or> y = E2.T.Xe \<or> y = node G x" using that NS by blast
          then show False using yD TXenD nxr0 yr by auto
        qed
      qed
      ultimately show ?thesis by simp
    qed
    have N_not_old: "\<not> fconnect (node G) a' y" if "a' \<in> set pG" "y \<in> set N" for a' y
    proof
      assume ay: "fconnect (node G) a' y"
      have yD: "y \<in> E.D" using ay pGD that(1) E.N.fconnect_in_D by blast
      then have yn: "y = node G x" using that(2) NS E.X_notin TXenD by auto
      have "fconnect (node G) (node G x) a'" using E.N.fconnect_sym[OF ay] yn by simp
      then have "fconnect (node G) x a'" by (rule fconnect_trans[OF nx_ring])
      then show False using pG_off[OF that(1)] ringG by blast
    qed
    consider "a = E2.XY" | "a \<in> set N" | "a \<in> set pG" using a by auto
    then show "a = b"
    proof cases
      case 1
      then have "b \<in> set (E.Xe # E2.XY # r0)" using ab cXY by simp
      then show ?thesis using b offY 1 by auto
    next
      case 2
      have bN: "b = E.X \<or> b = E2.T.Xe \<or> b = node G x" using cN[of a b] 2 NS ab by auto
      consider "b = E2.XY" | "b \<in> set N" | "b \<in> set pG" using b by auto
      then show ?thesis
      proof cases
        case 1 then show ?thesis using bN E2.XY_neq XYnD E.nx0D by auto
      next
        case 3
        have "fconnect (node G) b a" using ba cold[OF 3] by simp
        then show ?thesis using N_not_old[OF 3 2] by simp
      qed (use 2 Nsing in blast)
    next
      case 3
      have abG: "fconnect (node G) a b" using ab cold[OF 3] by simp
      consider "b = E2.XY" | "b \<in> set N" | "b \<in> set pG" using b by auto
      then show ?thesis
      proof cases
        case 1
        have "b \<in> E.D" using abG pGD 3 E.N.fconnect_in_D by blast
        then show ?thesis using 1 XYnD by simp
      next
        case 2 then show ?thesis using N_not_old[OF 3 2] abG by simp
      next
        case 3
        then show ?thesis using spGi(2) \<open>a \<in> set pG\<close> abG by blast
      qed
    qed
  qed
  show "sparse (cpG (CpY # cp)) (ctrlist mr mc (CpY # cp))"
    using sp sparse_mset[OF l_eq] cpY by simp
qed

lemma sparse_R:
  assumes c: "cpmap cp = (G, x)" and IH: "sp_ok cp"
  shows "sp_ok (CpR i # cp)"
  unfolding sp_ok_def
proof (intro allI impI)
  fix mr mc
  assume l1: "length mr = cprsize (CpR i # cp)" and l2: "length mc = ctrmsize (CpR i # cp)"
    and cf: "cfctr mr mc (CpR i # cp) \<noteq> None"
  interpret E: hypermap G using hypermap_cpmap[of cp] c by simp
  have xD: "x \<in> E.D" using cpx_in[of cp] c by simp
  define r where "r = cpring G x"
  have lr: "length r = cprsize cp" using size_ring_cpmap[of cp] c by (simp add: r_def cpring_of_def)
  have lmr: "length mr = length r" using l1 lr by simp
  have cf0: "cfctr (rotr i mr) mc cp \<noteq> None" using cf by (auto split: option.splits)
  define K where "K = insertE G (mask mc (ctrenum cp))"
  have sp0: "sparse G (x # map (edge G) (mask (rotr i mr) r) @ K)"
    using IH[unfolded sp_ok_def, rule_format, of "rotr i mr" mc] lmr lr l2 cf0 c
    by (simp add: ctrlist_def cpring_of_def r_def K_def)
  have cpR: "cpmap (CpR i # cp) = (G, E.ecpR_ptr i x)" by (rule cpmap_Cons_cases(1)[OF c])
  have rR: "cpring G (E.ecpR_ptr i x) = rot i r" by (simp add: E.cpring_ecpR r_def)
  have xp: "fconnect (node G) x (E.ecpR_ptr i x)" by (simp add: E.ecpR_ptr_def fconnect_funpow)
  have "mask mr (rot i r) = mask (rot i (rotr i mr)) (rot i r)" by (simp add: rot_rotr)
  also have "\<dots> = rot (count_list (take i (rotr i mr)) True) (mask (rotr i mr) r)"
    by (rule mask_rot) (simp add: lmr)
  finally have "mset (map (edge G) (mask mr (rot i r))) = mset (map (edge G) (mask (rotr i mr) r))"
    by (simp only: map_rot mset_rot)
  then have "mset (x # map (edge G) (mask mr (rot i r)) @ K) = mset (x # map (edge G) (mask (rotr i mr) r) @ K)"
    by simp
  then have "sparse G (x # map (edge G) (mask mr (rot i r)) @ K)" using sp0 sparse_mset by blast
  then have "sparse G (E.ecpR_ptr i x # map (edge G) (mask mr (rot i r)) @ K)"
    using sparse_head_cnode[OF E.hypermap_axioms xp] by simp
  then show "sparse (cpG (CpR i # cp)) (ctrlist mr mc (CpR i # cp))"
    unfolding ctrlist_def cpR fst_conv snd_conv cpring_of_def rR K_def ctrenum.simps .
qed

lemma sparse_Y0: "sp_ok [CpY]"
  unfolding sp_ok_def
proof (intro allI impI)
  fix mr mc
  assume l1: "length mr = cprsize [CpY]" and l2: "length mc = ctrmsize [CpY]"
    and cf: "cfctr mr mc [CpY] \<noteq> None"
  define o1 where "o1 = (1::nat)"
  have c: "cpmap [] = (cpmap0, o1)" by (simp add: o1_def)
  interpret E: ecp cpmap0 o1 by (rule ecp_intro[OF hypermap_cpmap0]) (simp add: o1_def)
  have r0: "cpring cpmap0 o1 = [0, o1]" using cpring0 by (simp add: o1_def)
  interpret E2: ecp2 cpmap0 o1 unfolding ecp2_def by (rule E.ecp_axioms)
  have hY: "hypermap E2.GY" by (rule E2.T.NN.hypermap_axioms)
  have cpY: "cpmap [CpY] = (E2.GY, E2.XY)" using cpmap_Cons_cases(4)[OF c E2.ecp2_axioms] by simp
  have ringY: "cpring E2.GY E2.XY = [E.Xe, E2.XY, o1]" using E2.cpring_GY r0 by simp
  obtain b1 b2 b3 where mr: "mr = [b1, b2, b3]" using l1 by (auto simp: numeral_eq_Suc length_Suc_conv)
  have mc: "mc = []" using l2 by simp
  have nspF: "\<not> nsp b1 b2 b3" using cf by (auto simp: mr split: if_splits)
  have n0: "node cpmap0 o1 = 0" by (simp add: o1_def sw01_def)
  have e1: "edge E2.GY o1 = 0" using E2.face_GY_old[of o1] by (simp add: o1_def sw01_def)
  have eX: "edge E2.GY E.Xe = E.X" and eXY: "edge E2.GY E2.XY = E2.T.Xe" by simp_all
  define N where "N = (if b1 then [E.X] else []) @ (if b2 then [E2.T.Xe] else []) @ (if b3 then [0::nat] else [])"
  have N1: "length N \<le> 1" unfolding N_def by (rule nsp_atmost1[OF nspF])
  have NS: "set N \<subseteq> {E.X, E2.T.Xe, 0}" by (cases b1; cases b2; cases b3) (simp_all add: N_def)
  have lst: "ctrlist mr mc [CpY] = E2.XY # N"
    unfolding ctrlist_def cpY fst_conv snd_conv cpring_of_def ringY mr mc N_def
    by (cases b1; cases b2; cases b3; simp only: mask.simps if_True if_False list.map eX eXY e1 ctrenum.simps
        insertE.simps append.simps append_Nil2; simp)
  have XYnD: "E2.XY \<notin> E.D" and TXenD: "E2.T.Xe \<notin> E.D" using E2.D_neq_XY by blast+
  have offY: "y \<notin> set [E.Xe, E2.XY, o1]" if "y \<in> set N" for y
  proof -
    have "y = E.X \<or> y = E2.T.Xe \<or> y = 0" using that NS by blast
    moreover have "E.X \<noteq> E.Xe" "E.X \<noteq> E2.XY" "E2.T.Xe \<noteq> E.Xe" "E2.T.Xe \<noteq> E2.XY"
      by (simp_all only: E2.XY_neq E.X_neq not_False_eq_True)
    moreover have "E.X \<noteq> o1" "E2.T.Xe \<noteq> o1" "(0::nat) \<noteq> E.Xe" "(0::nat) \<noteq> E2.XY" "(0::nat) \<noteq> o1"
      using E.D_neq_X(3)[of o1] TXenD XYnD E.D_neq_X(2)[of 0] by (auto simp: o1_def)
    ultimately show ?thesis by (elim disjE) (simp_all only: list.set insert_iff empty_iff simp_thms)
  qed
  have "sparse E2.GY (E2.XY # N)"
    unfolding sparse_Cons[OF hY]
  proof
    show "\<not> (\<exists>y \<in> set N. fconnect (node E2.GY) E2.XY y)"
    proof
      assume "\<exists>y \<in> set N. fconnect (node E2.GY) E2.XY y"
      then obtain y where yN: "y \<in> set N" and c: "fconnect (node E2.GY) E2.XY y" by blast
      have "y \<in> set (cpring E2.GY E2.XY)" using E2.T.NN.mem_cpring c by blast
      then show False using offY[OF yN] unfolding ringY by blast
    qed
    show "sparse E2.GY N" unfolding sparse_iff[OF hY] using N1 by (cases N) auto
  qed
  then show "sparse (cpG [CpY]) (ctrlist mr mc [CpY])" using lst cpY by simp
qed

lemma sparse_H:
  assumes c: "cpmap cp = (G, x)" and h: "config_prog cp" and IH: "sp_ok cp"
  shows "sp_ok (CpH # cp)"
  unfolding sp_ok_def
proof (intro allI impI)
  fix mr mc
  assume l1: "length mr = cprsize (CpH # cp)" and l2: "length mc = ctrmsize (CpH # cp)"
    and cf: "cfctr mr mc (CpH # cp) \<noteq> None"
  have cq: "cubic_prog cp" by (rule config_prog_cubic[OF h])
  have pr: "proper_cpring G x" using cpmap_proper[OF cq] c by simp
  interpret E: ecp3 G x using hypermap_cpmap[of cp] cpx_in[of cp] c pr by (intro ecp3_intro) simp_all
  have hH: "hypermap E.GH" by (rule E.T2.NN.hypermap_axioms)
  define r2 where "r2 = drop 2 (cpring G x)"
  have hr: "cpring G x = node G x # x # r2" using E.head_proper_cpring[OF pr] by (simp add: r2_def)
  have r2D: "set r2 \<subseteq> E.D" using E.ringD hr by auto
  have dr: "distinct (node G x # x # r2)" using E.cpring_distinct[of x] hr by simp
  have cpH: "cpmap (CpH # cp) = (E.GH, E.XH)" using cpmap_H[OF c E.ecp2h_axioms] by simp
  have ringH: "cpring E.GH E.XH = E.Xe # E.XH # r2" using E.cpring_GH by (simp add: r2_def)
  define En where "En = ctrenum cp"
  have EnD: "set En \<subseteq> E.D" using ctrenum_darts[of cp] h c by (simp add: En_def)
  have enH: "ctrenum (CpH # cp) = E.XY # node G x # x # En"
    using cpH c E.face_GH_cycle(1) by (simp add: En_def)
  have lr: "cprsize cp = Suc (Suc (length r2))" using size_ring_cpmap[of cp] c hr by (simp add: cpring_of_def)
  obtain b1 b2 mr' where mr: "mr = b1 # b2 # mr'" and lmr': "length mr' = length r2"
  proof -
    have "length mr = Suc (Suc (length r2))" using l1 lr by simp
    then show thesis using that by (auto simp: length_Suc_conv)
  qed
  obtain b3 b4 b5 mc' where mc: "mc = b3 # b4 # b5 # mc'" and lmc': "length mc' = ctrmsize cp"
    using l2 by (auto simp: numeral_eq_Suc length_Suc_conv)
  have nsp1: "\<not> nsp b3 b1 b4" and nsp2: "\<not> nsp b3 b2 b5" and cf0: "cfctr (b4 # b5 # mr') mc' cp \<noteq> None"
    using cf unfolding mr mc by (auto split: if_splits option.splits)
  define pG where "pG = map (edge G) (mask (b4 # b5 # mr') (node G x # x # r2)) @ insertE G (mask mc' En)"
  have spG0: "sparse G (x # pG)"
    using IH[unfolded sp_ok_def, rule_format, of "b4 # b5 # mr'" mc'] lmr' lr lmc' cf0 c hr
    by (simp add: ctrlist_def cpring_of_def pG_def En_def)
  have nr: "\<not> fconnect (node G) x y" if "y \<in> set pG" for y
    using spG0 that sparse_Cons[OF E.hypermap_axioms] by blast
  have spG: "sparse G pG" using spG0 sparse_Cons[OF E.hypermap_axioms] by blast
  have pGD: "set pG \<subseteq> E.D"
  proof -
    have a1: "set (mask (b4 # b5 # mr') (node G x # x # r2)) \<subseteq> E.D"
      using set_mask_subset[of "b4 # b5 # mr'" "node G x # x # r2"] r2D E.x0D set_mask_subset[of mr' r2]
      by (auto split: if_splits)
    have a2: "set (mask mc' En) \<subseteq> E.D" using set_mask_subset[of mc' En] EnD by auto
    show ?thesis using a1 E.insertE_D[OF a2] by (auto simp: pG_def simp del: mask.simps)
  qed
  have ringG: "y \<in> set (cpring G x) \<longleftrightarrow> fconnect (node G) x y" for y by (rule E.mem_cpring)
  have pG_off: "y \<notin> set (cpring G x)" if "y \<in> set pG" for y using nr[OF that] ringG by blast
  have pG_off2: "y \<noteq> node G x \<and> y \<noteq> x \<and> y \<notin> set r2" if "y \<in> set pG" for y
    using pG_off[OF that] hr by auto
  define NA where "NA = (if b3 then [E.T.Xe] else []) @ (if b1 then [E.X] else []) @ (if b4 then [node G x] else [])"
  define NB where "NB = (if b3 then [E.XY] else []) @ (if b2 then [E.T2.Xe] else []) @ (if b5 then [x] else [])"
  have NA1: "length NA \<le> 1" unfolding NA_def by (rule nsp_atmost1[OF nsp1])
  have NB1: "length NB \<le> 1" unfolding NB_def by (rule nsp_atmost1[OF nsp2])
  have NAS: "set NA \<subseteq> {node G x, E.X, E.T.Xe}" by (cases b1; cases b3; cases b4) (simp_all add: NA_def)
  have NBS: "set NB \<subseteq> {x, E.XY, E.T2.Xe}" by (cases b2; cases b3; cases b5) (simp_all add: NB_def)
  have newnD: "E.XY \<notin> E.D" "E.XH \<notin> E.D" "E.T.Xe \<notin> E.D" "E.T2.Xe \<notin> E.D"
    using E.D_neq_XY E.D_neq_XH by blast+
  have eHold: "edge E.GH y = edge G y" if "y \<in> E.D" for y using that by simp
  have l_eq: "mset (ctrlist mr mc (CpH # cp)) = mset (E.XH # NA @ NB @ pG)"
  proof -
    have m1: "map (edge E.GH) (mask mr' r2) = map (edge G) (mask mr' r2)"
      using set_mask_subset[of mr' r2] r2D eHold by (intro map_cong[OF refl]) blast
    have m2: "insertE E.GH (mask mc' En) = insertE G (mask mc' En)"
      using set_mask_subset[of mc' En] EnD eHold by (intro insertE_cong) blast
    have eX: "edge E.GH E.Xe = E.X" and eXH: "edge E.GH E.XH = E.T2.Xe" and eXY: "edge E.GH E.XY = E.T.Xe"
      by simp_all
    have enx: "edge E.GH (node G x) = edge G (node G x)" using eHold E.nx0D by simp
    have ex: "edge E.GH x = edge G x" using eHold E.x0D by simp
    show ?thesis
      unfolding ctrlist_def cpH fst_conv snd_conv cpring_of_def ringH enH mr mc NA_def NB_def pG_def
      by (cases b1; cases b2; cases b3; cases b4; cases b5;
          simp only: mask.simps if_True if_False list.map insertE.simps insertE_app m1 m2 eX eXH eXY enx ex
            append.simps append_Nil2 mset.simps mset_append;
          simp add: ac_simps)
  qed
  have cXH: "fconnect (node E.GH) E.XH z \<longleftrightarrow> z \<in> set (E.Xe # E.XH # r2)" for z
    using E.T2.NN.mem_cpring[of z E.XH] ringH by simp
  have clsA: "fconnect (node E.GH) a z \<longleftrightarrow> z = node G x \<or> z = E.X \<or> z = E.T.Xe"
    if aA: "a \<in> {node G x, E.X, E.T.Xe}" for a z
  proof -
    have aX: "fconnect (node E.GH) (node G x) a" using aA E.cnodeH_nx0 by auto
    have "fconnect (node E.GH) a z \<longleftrightarrow> fconnect (node E.GH) (node G x) z"
      using fconnect_trans[OF aX] fconnect_trans[OF E.T2.NN.N.fconnect_sym[OF aX]] by blast
    then show ?thesis using E.cnodeH_nx0 by simp
  qed
  have clsB: "fconnect (node E.GH) a z \<longleftrightarrow> z = x \<or> z = E.XY \<or> z = E.T2.Xe"
    if aB: "a \<in> {x, E.XY, E.T2.Xe}" for a z
  proof -
    have aX: "fconnect (node E.GH) x a" using aB E.cnodeH_x0 by auto
    have "fconnect (node E.GH) a z \<longleftrightarrow> fconnect (node E.GH) x z"
      using fconnect_trans[OF aX] fconnect_trans[OF E.T2.NN.N.fconnect_sym[OF aX]] by blast
    then show ?thesis using E.cnodeH_x0 by simp
  qed
  have cold: "fconnect (node E.GH) a z \<longleftrightarrow> fconnect (node G) a z" if "a \<in> set pG" for a z
  proof -
    have "a \<in> darts (cpG cp)" "a \<notin> set (cpring_of cp)" using that pGD pG_off c by (auto simp: cpring_of_def)
    from cnode_injcp[of "[CpH]", OF _ this] show ?thesis using cpH c by simp
  qed
  have spGi: "distinct pG" "\<And>a b. a \<in> set pG \<Longrightarrow> b \<in> set pG \<Longrightarrow> fconnect (node G) a b \<Longrightarrow> a = b"
    using spG sparse_iff[OF E.hypermap_axioms] by blast+
  have xnx: "x \<noteq> node G x" by (rule E.x0_ne_n)
  have XnD: "E.X \<notin> E.D" by simp
  \<comment> \<open>membership facts for the new darts\<close>
  have sA: "y = node G x \<or> y = E.X \<or> y = E.T.Xe" if "y \<in> set NA" for y using that NAS by blast
  have sB: "y = x \<or> y = E.XY \<or> y = E.T2.Xe" if "y \<in> set NB" for y using that NBS by blast
  have ne_new: "E.X \<noteq> E.Xe" "E.X \<noteq> E.XH" "E.T.Xe \<noteq> E.Xe" "E.T.Xe \<noteq> E.XH" "E.XY \<noteq> E.Xe"
    "E.XY \<noteq> E.XH" "E.T2.Xe \<noteq> E.Xe" "E.T2.Xe \<noteq> E.XH" "E.X \<noteq> E.XY" "E.X \<noteq> E.T2.Xe"
    "E.T.Xe \<noteq> E.XY" "E.T.Xe \<noteq> E.T2.Xe"
    by (simp_all only: E.XY_neq E.XH_neq E.X_neq E.neqs_H not_False_eq_True)
  have nxD: "node G x \<in> E.D" and xD: "x \<in> E.D" using E.x0D by simp_all
  have d9: "node G x \<noteq> x" "node G x \<noteq> E.XY" "node G x \<noteq> E.T2.Xe" "E.X \<noteq> x"
      "E.X \<noteq> E.XY" "E.X \<noteq> E.T2.Xe" "E.T.Xe \<noteq> x" "E.T.Xe \<noteq> E.XY" "E.T.Xe \<noteq> E.T2.Xe"
      using ne_new xnx nxD xD newnD XnD by (blast | metis)+
  have AnotB: "a \<noteq> b" if "a \<in> set NA" "b \<in> set NB" for a b
    using sA[OF that(1)] sB[OF that(2)] by (elim disjE) (simp_all only: d9 not_False_eq_True)
  have AnotpG: "a \<notin> set pG" if "a \<in> set NA" for a
    using sA[OF that] pG_off2 pGD newnD using XnD by auto
  have BnotpG: "a \<notin> set pG" if "a \<in> set NB" for a
    using sB[OF that] pG_off2 pGD newnD by auto
  have offH: "y \<notin> set (E.Xe # E.XH # r2)" if "y \<in> set NA \<union> set NB \<union> set pG" for y
  proof -
    have "y \<noteq> E.Xe \<and> y \<noteq> E.XH \<and> y \<notin> set r2"
    proof (cases "y \<in> set pG")
      case True
      then have "y \<in> E.D" using pGD by blast
      then show ?thesis using pG_off2[OF True] newnD by auto
    next
      case False
      then have "y \<in> set NA \<or> y \<in> set NB" using that by blast
      then have "y = node G x \<or> y = E.X \<or> y = E.T.Xe \<or> y = x \<or> y = E.XY \<or> y = E.T2.Xe"
        using sA sB by blast
      moreover have "node G x \<notin> set r2" "x \<notin> set r2" using dr by auto
      moreover have "E.X \<notin> set r2" "E.T.Xe \<notin> set r2" "E.XY \<notin> set r2" "E.T2.Xe \<notin> set r2"
        using r2D newnD E.X_notin by blast+
      moreover have "node G x \<noteq> E.Xe" "node G x \<noteq> E.XH" "x \<noteq> E.Xe" "x \<noteq> E.XH"
        using nxD xD newnD by auto
      ultimately show ?thesis using ne_new by (elim disjE) (simp_all only: simp_thms)
    qed
    then show ?thesis by simp
  qed
  have AB_old: "\<not> fconnect (node G) a' y" if "a' \<in> set pG" "y \<in> set NA \<union> set NB" for a' y
  proof
    assume ay: "fconnect (node G) a' y"
    have yD: "y \<in> E.D" using ay pGD that(1) E.N.fconnect_in_D by blast
    have yne: "y \<noteq> E.X" "y \<noteq> E.T.Xe" "y \<noteq> E.XY" "y \<noteq> E.T2.Xe" using yD newnD XnD by blast+
    have "y = node G x \<or> y = x"
    proof (cases "y \<in> set NA")
      case True then show ?thesis using sA[OF True] yne by blast
    next
      case False then have "y \<in> set NB" using that(2) by blast
      then show ?thesis using sB yne by blast
    qed
    then have "fconnect (node G) x y" using ringG hr by auto
    then have "fconnect (node G) x a'" by (rule fconnect_trans[OF _ E.N.fconnect_sym[OF ay]])
    then show False using pG_off[OF that(1)] ringG by blast
  qed
  have NAd: "distinct NA" using NA1 by (cases NA) auto
  have NBd: "distinct NB" using NB1 by (cases NB) auto
  have NAsing: "a = b" if "a \<in> set NA" "b \<in> set NA" for a b using that NA1 by (cases NA) auto
  have NBsing: "a = b" if "a \<in> set NB" "b \<in> set NB" for a b using that NB1 by (cases NB) auto
  have XHn: "E.XH \<notin> set NA \<union> set NB \<union> set pG"
    using offH by auto
  have sp: "sparse E.GH (E.XH # NA @ NB @ pG)"
    unfolding sparse_iff[OF hH]
  proof (intro conjI ballI impI)
    show "distinct (E.XH # NA @ NB @ pG)"
      using NAd NBd spGi(1) AnotB AnotpG BnotpG XHn by auto
    fix a b assume a: "a \<in> set (E.XH # NA @ NB @ pG)" and b: "b \<in> set (E.XH # NA @ NB @ pG)"
      and ab: "fconnect (node E.GH) a b"
    have ba: "fconnect (node E.GH) b a" by (rule E.T2.NN.N.fconnect_sym[OF ab])
    have cA: "b = node G x \<or> b = E.X \<or> b = E.T.Xe" if "a \<in> set NA" using clsA[of a b] sA[OF that] ab by auto
    have cB: "b = x \<or> b = E.XY \<or> b = E.T2.Xe" if "a \<in> set NB" using clsB[of a b] sB[OF that] ab by auto
    consider "a = E.XH" | "a \<in> set NA" | "a \<in> set NB" | "a \<in> set pG" using a by auto
    then show "a = b"
    proof cases
      case 1
      then have "b \<in> set (E.Xe # E.XH # r2)" using ab cXH by simp
      then have bm: "b \<in> set (E.Xe # E.XH # r2)" .
      show ?thesis
      proof (cases "b = E.XH")
        case True then show ?thesis using 1 by simp
      next
        case False
        then have "b \<in> set NA \<union> set NB \<union> set pG" using b by simp
        then show ?thesis using offH bm by blast
      qed
    next
      case 2
      consider "b = E.XH" | "b \<in> set NA" | "b \<in> set NB" | "b \<in> set pG" using b by auto
      then show ?thesis
      proof cases
        case 1
        then have "a \<in> set (E.Xe # E.XH # r2)" using ba cXH by simp
        then show ?thesis using offH[of a] 2 by blast
      next
        case 3
        have "b = x \<or> b = E.XY \<or> b = E.T2.Xe" using sB[OF 3] .
        then show ?thesis using cA[OF 2] by (elim disjE) (simp_all only: d9 simp_thms)
      next
        case 4
        have "fconnect (node G) b a" using ba cold[OF 4] by simp
        then show ?thesis using AB_old[OF 4] 2 by blast
      qed (use 2 NAsing in blast)
    next
      case 3
      consider "b = E.XH" | "b \<in> set NA" | "b \<in> set NB" | "b \<in> set pG" using b by auto
      then show ?thesis
      proof cases
        case 1
        then have "a \<in> set (E.Xe # E.XH # r2)" using ba cXH by simp
        then show ?thesis using offH[of a] 3 by blast
      next
        case 2
        have "b = node G x \<or> b = E.X \<or> b = E.T.Xe" using sA[OF 2] .
        then show ?thesis using cB[OF 3] by (elim disjE) (simp_all only: d9[symmetric] simp_thms)
      next
        case 4
        have "fconnect (node G) b a" using ba cold[OF 4] by simp
        then show ?thesis using AB_old[OF 4] 3 by blast
      qed (use 3 NBsing in blast)
    next
      case 4
      have abG: "fconnect (node G) a b" using ab cold[OF 4] by simp
      consider "b = E.XH" | "b \<in> set NA \<union> set NB" | "b \<in> set pG" using b by auto
      then show ?thesis
      proof cases
        case 1
        have "b \<in> E.D" using abG pGD 4 E.N.fconnect_in_D by blast
        then show ?thesis using 1 newnD by simp
      next
        case 2 then show ?thesis using AB_old[OF 4 2] abG by simp
      next
        case 3 then show ?thesis using spGi(2) 4 abG by blast
      qed
    qed
  qed
  show "sparse (cpG (CpH # cp)) (ctrlist mr mc (CpH # cp))"
    using sp sparse_mset[OF l_eq] cpH by simp
qed

lemma sp_ok_all: "sp_ok cp"
proof (induction cp)
  case Nil then show ?case by (simp add: sp_ok_def)
next
  case (Cons s cp)
  obtain G x where c: "cpmap cp = (G, x)" by (cases "cpmap cp")
  show ?case
  proof (cases s)
    case (CpR i) then show ?thesis using sparse_R[OF c Cons.IH] by simp
  next
    case CpY
    show ?thesis
    proof (cases "config_prog cp")
      case True then show ?thesis using sparse_Y[OF c True Cons.IH] CpY by simp
    next
      case False
      show ?thesis
      proof (cases "cp = []")
        case True then show ?thesis using sparse_Y0 CpY by simp
      next
        case nil: False
        have "cfctr mr mc (CpY # cp) = None" for mr mc
          using cfctr_config_prog[of mr mc "CpY # cp"] False nil by (cases cp) (auto, metis option.exhaust)
        then show ?thesis using CpY by (simp add: sp_ok_def)
      qed
    qed
  next
    case CpH
    show ?thesis
    proof (cases "config_prog cp")
      case True then show ?thesis using sparse_H[OF c True Cons.IH] CpH by simp
    next
      case False
      have "cfctr mr mc (CpH # cp) = None" for mr mc
        using cfctr_config_prog[of mr mc "CpH # cp"] False by (auto, metis option.exhaust)
      then show ?thesis using CpH by (simp add: sp_ok_def)
    qed
  qed (simp_all add: sp_ok_def)
qed

theorem sparse_cfctr:
  "length mr = cprsize cp \<Longrightarrow> length mc = ctrmsize cp \<Longrightarrow> cfctr mr mc cp \<noteq> None \<Longrightarrow>
   sparse (cpG cp) (cpx cp # map (edge (cpG cp)) (mask mr (cpring_of cp)) @ insertE (cpG cp) (mask mc (ctrenum cp)))"
  using sp_ok_all[of cp] unfolding sp_ok_def ctrlist_def by blast

section \<open>Contract bands\<close>

fun ctrband :: "bool list \<Rightarrow> cprog \<Rightarrow> cfmask" where
  "ctrband cm (CpR k # cp) = (case ctrband cm cp of Cfmask mr mk \<Rightarrow> Cfmask (rot k mr) mk)"
| "ctrband cm [CpY] = Cfmask [False, False, False] []"
| "ctrband (b1 # cm') (CpY # cp) =
     (case ctrband cm' cp of
        Cfmask (a0 # a1 # mr) mk \<Rightarrow> Cfmask ((b1 \<or> a0) # False # (b1 \<or> a1) # mr) mk
      | _ \<Rightarrow> Cfmask [] [])"
| "ctrband (b1 # b0 # b2 # cm') (CpH # cp) =
     (case ctrband cm' cp of
        Cfmask (a0 # a1 # a2 # mr) mk \<Rightarrow> Cfmask ((b0 \<or> a0) # b1 # (b2 \<or> a2) # mr) ((b0 \<or> b1 \<or> b2 \<or> a1) # mk)
      | _ \<Rightarrow> Cfmask [] [])"
| "ctrband _ _ = Cfmask [] []"

definition cb_ok :: "cprog \<Rightarrow> bool" where
  "cb_ok cp \<longleftrightarrow> (\<forall>cm. length cm = ctrmsize cp \<longrightarrow> proper_cpmask cp (ctrband cm cp) \<and>
     (\<forall>u \<in> darts (cpG cp). fband (cpG cp) (insertE (cpG cp) (mask cm (ctrenum cp))) u \<longleftrightarrow>
        fband (cpG cp) (cpmask (ctrband cm cp) cp) u))"

lemma cb_R:
  assumes c: "cpmap cp = (G, x)" and IH: "cb_ok cp"
  shows "cb_ok (CpR i # cp)"
  unfolding cb_ok_def
proof (intro allI impI)
  fix cm :: "bool list" assume l: "length cm = ctrmsize (CpR i # cp)"
  interpret E: hypermap G using hypermap_cpmap[of cp] c by simp
  obtain mr mk where cb: "ctrband cm cp = Cfmask mr mk" by (cases "ctrband cm cp")
  have IH': "proper_cpmask cp (Cfmask mr mk)"
    "\<And>u. u \<in> E.D \<Longrightarrow> fband G (insertE G (mask cm (ctrenum cp))) u \<longleftrightarrow> fband G (cpmask (Cfmask mr mk) cp) u"
    using IH[unfolded cb_ok_def, rule_format, of cm] l c cb by auto
  have lmr: "length mr = length (cpring G x)" using IH'(1) size_ring_cpmap[of cp] c by (simp add: cpring_of_def)
  have cpR: "cpmap (CpR i # cp) = (G, E.ecpR_ptr i x)" by (rule cpmap_Cons_cases(1)[OF c])
  have rR: "cpring_of (CpR i # cp) = rot i (cpring G x)" using cpR by (simp add: cpring_of_def E.cpring_ecpR)
  have se: "set (mask (rot i mr) (rot i (cpring G x))) = set (mask mr (cpring G x))" by (rule set_mask_rot[OF lmr])
  show "proper_cpmask (CpR i # cp) (ctrband cm (CpR i # cp)) \<and>
     (\<forall>u \<in> darts (cpG (CpR i # cp)). fband (cpG (CpR i # cp)) (insertE (cpG (CpR i # cp)) (mask cm (ctrenum (CpR i # cp)))) u \<longleftrightarrow>
        fband (cpG (CpR i # cp)) (cpmask (ctrband cm (CpR i # cp)) (CpR i # cp)) u)"
    using IH' se cb cpR rR c by (auto simp: fband_def cpksize_def cpring_of_def)
qed

lemma mask_FFF [simp]: "mask [False, False, False] l = []"
  using mask_replicate_False[of 3 l] by (simp add: numeral_3_eq_3)

lemma cb_Y0: "cb_ok [CpY]"
  unfolding cb_ok_def by (auto simp: cpksize_def fband_def)

lemma cb_Y:
  assumes c: "cpmap cp = (G, x)" and h: "config_prog cp" and IH: "cb_ok cp"
  shows "cb_ok (CpY # cp)"
  unfolding cb_ok_def
proof (intro allI impI)
  fix cm :: "bool list" assume l: "length cm = ctrmsize (CpY # cp)"
  interpret E: ecp G x using hypermap_cpmap[of cp] cpx_in[of cp] c by (intro ecp_intro) simp_all
  interpret E2: ecp2 G x by (simp add: ecp2_def E.ecp_axioms)
  have cq: "cubic_prog cp" by (rule config_prog_cubic[OF h])
  have pr: "proper_cpring G x" using cpmap_proper[OF cq] c by simp
  define r2 where "r2 = drop 2 (cpring G x)"
  have hr: "cpring G x = node G x # x # r2" using E.head_proper_cpring[OF pr] by (simp add: r2_def)
  obtain s0 cp0 where cps: "cp = s0 # cp0" using h by (cases cp) auto
  obtain b1 cm' where cm: "cm = b1 # cm'" and lcm': "length cm' = ctrmsize cp"
    using l cps by (metis ctrmsize.simps(3) length_Suc_conv)
  define En where "En = ctrenum cp"
  define ker where "ker = cpker cp"
  have EnD: "set En \<subseteq> E.D" using ctrenum_darts[of cp] h c by (simp add: En_def)
  have kerD: "set ker \<subseteq> E.D" using cpker_darts[of cp] h c by (simp add: ker_def)
  have r2D: "set r2 \<subseteq> E.D" using E.ringD hr by auto
  have lr: "cprsize cp = Suc (Suc (length r2))" using size_ring_cpmap[of cp] c hr by (simp add: cpring_of_def)
  obtain ma mk where cb: "ctrband cm' cp = Cfmask ma mk" by (cases "ctrband cm' cp")
  have IH': "proper_cpmask cp (Cfmask ma mk)"
    "\<And>u. u \<in> E.D \<Longrightarrow> fband G (insertE G (mask cm' En)) u \<longleftrightarrow> fband G (mask ma (cpring G x) @ mask mk ker) u"
    using IH[unfolded cb_ok_def, rule_format, of cm'] lcm' c cb by (auto simp: En_def ker_def cpring_of_def)
  have "length ma = Suc (Suc (length r2))" using IH'(1) lr by simp
  then obtain a0 a1 mr where ma: "ma = a0 # a1 # mr" and lmr: "length mr = length r2"
    by (metis length_Suc_conv)
  have lmk: "length mk = cpksize cp" using IH'(1) by simp
  have cbY: "ctrband cm (CpY # cp) = Cfmask ((b1 \<or> a0) # False # (b1 \<or> a1) # mr) mk"
    using cb cps by (simp add: cm ma)
  have cpY: "cpmap (CpY # cp) = (E2.GY, E2.XY)" using cpmap_Cons_cases(4)[OF c E2.ecp2_axioms] by simp
  have ringY: "cpring E2.GY E2.XY = E.Xe # E2.XY # x # r2" using E2.cpring_GY hr by simp
  have enY: "ctrenum (CpY # cp) = node G x # En" using cps c by (simp add: En_def)
  have kerY: "cpker (CpY # cp) = ker" by (simp add: ker_def)
  have pcm: "proper_cpmask (CpY # cp) (ctrband cm (CpY # cp))"
    using lmr lr lmk cbY by (simp add: cpksize_def)
  have hY: "hypermap E2.GY" by (rule E2.T.NN.hypermap_axioms)
  have nYXY: "node E2.GY E2.XY = E.Xe" using E2.T.NN.head_cpring[of E2.XY] ringY by (metis list.inject)
  have XeN: "fconnect (face E2.GY) E.Xe (node G x)" using E2.cface_node_GY nYXY by simp
  have oldf: "fconnect (face E2.GY) a b \<longleftrightarrow> fconnect (face G) a b" if "a \<in> E.D" "b \<in> E.D" for a b
    by (rule E2.cface_GY_old[OF that])
  have eYold: "edge E2.GY y = edge G y" if "y \<in> E.D" for y using E2.face_GY_old[OF that] by simp
  have enxx: "fconnect (face G) (edge G (node G x)) x" using fconnect_step[of "face G" "edge G (node G x)"]
    by (simp only: E.nodeK)
  define IL where "IL = insertE G (mask cm' En)"
  have ILD: "set IL \<subseteq> E.D"
    using E.insertE_D[of "mask cm' En"] set_mask_subset[of cm' En] EnD by (auto simp: IL_def)
  have insY: "insertE E2.GY (mask (b1 # cm') (node G x # En)) =
      (if b1 then [node G x, edge G (node G x)] else []) @ IL"
  proof -
    have "insertE E2.GY (mask cm' En) = IL"
      unfolding IL_def using set_mask_subset[of cm' En] EnD eYold by (intro insertE_cong) blast
    then show ?thesis using eYold[OF E.nx0D] by (cases b1) simp_all
  qed
  define L where "L v \<longleftrightarrow> (b1 \<and> (fconnect (face E2.GY) v (node G x) \<or> fconnect (face E2.GY) v (edge G (node G x))))
      \<or> fband E2.GY IL v" for v
  define R where "R v \<longleftrightarrow> ((b1 \<or> a0) \<and> fconnect (face E2.GY) v E.Xe) \<or> ((b1 \<or> a1) \<and> fconnect (face E2.GY) v x)
      \<or> fband E2.GY (mask mr r2) v \<or> fband E2.GY (mask mk ker) v" for v
  have goal: "\<And>u. (fband E2.GY (insertE E2.GY (mask cm (node G x # En))) u \<longleftrightarrow>
       fband E2.GY (cpmask (Cfmask ((b1 \<or> a0) # False # (b1 \<or> a1) # mr) mk) (CpY # cp)) u) \<longleftrightarrow> (L u \<longleftrightarrow> R u)"
    unfolding cm insY cpmask.simps cpring_of_def cpY fst_conv snd_conv ringY kerY L_def R_def
    by (cases b1) (simp_all add: fband_app fband_mask_Cons E2.T.NN.fband_Cons del: mask.simps insertE.simps)
  have cY: "fconnect (face E2.GY) v t \<longleftrightarrow> fconnect (face E2.GY) w t" if "fconnect (face E2.GY) v w" for v w t
    using fconnect_trans[OF that] fconnect_trans[OF E2.T.NN.F.fconnect_sym[OF that]] by blast
  have invL: "L v \<longleftrightarrow> L w" if "fconnect (face E2.GY) v w" for v w
    using cY[OF that] E2.T.NN.fband_cface[OF that] unfolding L_def by simp
  have invR: "R v \<longleftrightarrow> R w" if "fconnect (face E2.GY) v w" for v w
    using cY[OF that] E2.T.NN.fband_cface[OF that] unfolding R_def by simp
  have XY_old: "\<not> fconnect (face E2.GY) E2.XY v" if "v \<in> E.D" for v using E2.cface_GY_XY that by auto
  have nob: "\<not> fband E2.GY l E2.XY" if "set l \<subseteq> E.D" for l using that XY_old by (auto simp: fband_def)
  have mD: "set (mask mr r2) \<subseteq> E.D" "set (mask mk ker) \<subseteq> E.D"
    using set_mask_subset[of mr r2] set_mask_subset[of mk ker] r2D kerD by auto
  have caseXY: "L E2.XY \<longleftrightarrow> R E2.XY"
  proof -
    have "\<not> fconnect (face E2.GY) E2.XY E.Xe" using E2.cface_GY_XY by simp
    moreover have "edge G (node G x) \<in> E.D" using E.x0D by simp
    ultimately show ?thesis unfolding L_def R_def using XY_old[OF E.nx0D] XY_old[OF E.x0D] XY_old nob[OF ILD]
      nob[OF mD(1)] nob[OF mD(2)] by blast
  qed
  have caseD: "L v \<longleftrightarrow> R v" if vD: "v \<in> E.D" for v
  proof -
    have enD: "edge G (node G x) \<in> E.D" using E.x0D by simp
    have f1: "fconnect (face E2.GY) v E.Xe \<longleftrightarrow> fconnect (face G) v (node G x)"
      using cY[OF XeN, of v] oldf[OF vD E.nx0D] E2.T.NN.F.fconnect_commute by metis
    have f2: "fconnect (face E2.GY) v (edge G (node G x)) \<longleftrightarrow> fconnect (face G) v x"
      using oldf[OF vD enD] fconnect_trans[OF _ enxx, of v] fconnect_trans[OF _ E.F.fconnect_sym[OF enxx], of v]
      by blast
    have f3: "fband E2.GY l v \<longleftrightarrow> fband G l v" if "set l \<subseteq> E.D" for l
      by (rule fband_transfer[OF that vD]) (rule oldf)
    have IHv: "fband G IL v \<longleftrightarrow> (a0 \<and> fconnect (face G) v (node G x)) \<or> (a1 \<and> fconnect (face G) v x) \<or>
        fband G (mask mr r2) v \<or> fband G (mask mk ker) v"
      using IH'(2)[OF vD] unfolding IL_def[symmetric] hr ma
      by (simp add: fband_app fband_mask_Cons del: mask.simps)
    show ?thesis unfolding L_def R_def
      using f1 f2 f3[OF ILD] f3[OF mD(1)] f3[OF mD(2)] oldf[OF vD E.nx0D] oldf[OF vD E.x0D] IHv by blast
  qed
  have "fband E2.GY (insertE E2.GY (mask cm (node G x # En))) u \<longleftrightarrow>
       fband E2.GY (cpmask (Cfmask ((b1 \<or> a0) # False # (b1 \<or> a1) # mr) mk) (CpY # cp)) u"
    if u: "u \<in> darts E2.GY" for u
  proof -
    have "L u \<longleftrightarrow> R u"
    proof (cases "\<exists>y \<in> E.D. fconnect (face E2.GY) u y")
      case True
      then obtain y where yD: "y \<in> E.D" and uy: "fconnect (face E2.GY) u y" by blast
      show ?thesis using invL[OF uy] invR[OF uy] caseD[OF yD] by simp
    next
      case False
      then have "fconnect (face E2.GY) E2.XY u" using E2.fband_GY[OF u] by blast
      then have uy: "fconnect (face E2.GY) u E2.XY" by (rule E2.T.NN.F.fconnect_sym)
      show ?thesis using invL[OF uy] invR[OF uy] caseXY by simp
    qed
    then show ?thesis using goal by simp
  qed
  then show "proper_cpmask (CpY # cp) (ctrband cm (CpY # cp)) \<and>
     (\<forall>u \<in> darts (cpG (CpY # cp)). fband (cpG (CpY # cp)) (insertE (cpG (CpY # cp)) (mask cm (ctrenum (CpY # cp)))) u \<longleftrightarrow>
        fband (cpG (CpY # cp)) (cpmask (ctrband cm (CpY # cp)) (CpY # cp)) u)"
    using pcm unfolding cbY cpY fst_conv enY by blast
qed

lemma cb_H:
  assumes c: "cpmap cp = (G, x)" and h: "config_prog cp" and IH: "cb_ok cp"
  shows "cb_ok (CpH # cp)"
  unfolding cb_ok_def
proof (intro allI impI)
  fix cm :: "bool list" assume l: "length cm = ctrmsize (CpH # cp)"
  have cq: "cubic_prog cp" by (rule config_prog_cubic[OF h])
  have pr: "proper_cpring G x" using cpmap_proper[OF cq] c by simp
  interpret E: ecp3 G x using hypermap_cpmap[of cp] cpx_in[of cp] c pr by (intro ecp3_intro) simp_all
  have lng: "long_cpring G x" using cfmap_long[OF h] c by simp
  define fex where "fex = face G (edge G x)"
  define r3 where "r3 = drop 3 (cpring G x)"
  have hr: "cpring G x = node G x # x # fex # r3"
    using E.head_long_cpring[OF lng] by (simp add: r3_def fex_def)
  obtain b1 b0 b2 cm' where cm: "cm = b1 # b0 # b2 # cm'" and lcm': "length cm' = ctrmsize cp"
    using l by (auto simp: numeral_eq_Suc length_Suc_conv)
  define En where "En = ctrenum cp"
  define ker where "ker = cpker cp"
  have EnD: "set En \<subseteq> E.D" using ctrenum_darts[of cp] h c by (simp add: En_def)
  have kerD: "set ker \<subseteq> E.D" using cpker_darts[of cp] h c by (simp add: ker_def)
  have r3D: "set r3 \<subseteq> E.D" using E.ringD hr by auto
  have fexD: "fex \<in> E.D" using E.x0D by (simp add: fex_def)
  have lr: "cprsize cp = Suc (Suc (Suc (length r3)))" using size_ring_cpmap[of cp] c hr by (simp add: cpring_of_def)
  obtain ma mk where cb: "ctrband cm' cp = Cfmask ma mk" by (cases "ctrband cm' cp")
  have IH': "proper_cpmask cp (Cfmask ma mk)"
    "\<And>u. u \<in> E.D \<Longrightarrow> fband G (insertE G (mask cm' En)) u \<longleftrightarrow> fband G (mask ma (cpring G x) @ mask mk ker) u"
    using IH[unfolded cb_ok_def, rule_format, of cm'] lcm' c cb by (auto simp: En_def ker_def cpring_of_def)
  have "length ma = Suc (Suc (Suc (length r3)))" using IH'(1) lr by simp
  then obtain a0 a1 a2 mr where ma: "ma = a0 # a1 # a2 # mr" and lmr: "length mr = length r3"
    by (metis length_Suc_conv)
  have lmk: "length mk = cpksize cp" using IH'(1) by simp
  have cbH: "ctrband cm (CpH # cp) = Cfmask ((b0 \<or> a0) # b1 # (b2 \<or> a2) # mr) ((b0 \<or> b1 \<or> b2 \<or> a1) # mk)"
    using cb by (simp add: cm ma)
  have cpH: "cpmap (CpH # cp) = (E.GH, E.XH)" using cpmap_H[OF c E.ecp2h_axioms] by simp
  have ringH: "cpring E.GH E.XH = E.Xe # E.XH # fex # r3" using E.cpring_GH hr by simp
  have enH: "ctrenum (CpH # cp) = E.XY # node G x # x # En"
    using cpH c E.face_GH_cycle(1) by (simp add: En_def)
  have kerH: "cpker (CpH # cp) = x # ker" using c by (simp add: ker_def)
  have pcm: "proper_cpmask (CpH # cp) (ctrband cm (CpH # cp))"
    using lmr lr lmk cbH by (simp add: cpksize_def)
  have nHXH: "node E.GH E.XH = E.Xe" using E.T2.NN.head_cpring[of E.XH] ringH by (metis list.inject)
  have XeN: "fconnect (face E.GH) E.Xe (node G x)" using E.cface_node_GH nHXH by simp
  have oldf: "fconnect (face E.GH) a b \<longleftrightarrow> fconnect (face G) a b" if "a \<in> E.D" "b \<in> E.D" for a b
    by (rule E.cface_GH_old[OF that])
  have eHold: "edge E.GH y = edge G y" if "y \<in> E.D" for y using that by simp
  have enxx: "fconnect (face G) (edge G (node G x)) x" using fconnect_step[of "face G" "edge G (node G x)"]
    by (simp only: E.nodeK)
  have exf: "fconnect (face G) (edge G x) fex" unfolding fex_def by (rule fconnect_step)
  have XYXH: "fconnect (face E.GH) E.XH E.XY" using E.cface_GH_XH by simp
  define IL where "IL = insertE G (mask cm' En)"
  have ILD: "set IL \<subseteq> E.D"
    using E.insertE_D[of "mask cm' En"] set_mask_subset[of cm' En] EnD by (auto simp: IL_def)
  have eXY: "edge E.GH E.XY = E.T.Xe" by simp
  have insH: "insertE E.GH (mask (b1 # b0 # b2 # cm') (E.XY # node G x # x # En)) =
      (if b1 then [E.XY, E.T.Xe] else []) @ (if b0 then [node G x, edge G (node G x)] else []) @
      (if b2 then [x, edge G x] else []) @ IL"
  proof -
    have "insertE E.GH (mask cm' En) = IL"
      unfolding IL_def using set_mask_subset[of cm' En] EnD eHold by (intro insertE_cong) blast
    then show ?thesis using eHold[OF E.nx0D] eHold[OF E.x0D] eXY by (cases b1; cases b0; cases b2) simp_all
  qed
  define L where "L v \<longleftrightarrow> (b1 \<and> (fconnect (face E.GH) v E.XY \<or> fconnect (face E.GH) v E.T.Xe)) \<or>
      (b0 \<and> (fconnect (face E.GH) v (node G x) \<or> fconnect (face E.GH) v (edge G (node G x)))) \<or>
      (b2 \<and> (fconnect (face E.GH) v x \<or> fconnect (face E.GH) v (edge G x))) \<or> fband E.GH IL v" for v
  define R where "R v \<longleftrightarrow> ((b0 \<or> a0) \<and> fconnect (face E.GH) v E.Xe) \<or> (b1 \<and> fconnect (face E.GH) v E.XH) \<or>
      ((b2 \<or> a2) \<and> fconnect (face E.GH) v fex) \<or> fband E.GH (mask mr r3) v \<or>
      ((b0 \<or> b1 \<or> b2 \<or> a1) \<and> fconnect (face E.GH) v x) \<or> fband E.GH (mask mk ker) v" for v
  have goal: "\<And>u. (fband E.GH (insertE E.GH (mask cm (E.XY # node G x # x # En))) u \<longleftrightarrow>
       fband E.GH (cpmask (Cfmask ((b0 \<or> a0) # b1 # (b2 \<or> a2) # mr) ((b0 \<or> b1 \<or> b2 \<or> a1) # mk)) (CpH # cp)) u)
       \<longleftrightarrow> (L u \<longleftrightarrow> R u)"
    unfolding cm insH cpmask.simps cpring_of_def cpH fst_conv snd_conv ringH kerH L_def R_def
    by (cases b1; cases b0; cases b2) (simp_all add: fband_app fband_mask_Cons E.T2.NN.fband_Cons del: mask.simps insertE.simps)
  have cH: "fconnect (face E.GH) v t \<longleftrightarrow> fconnect (face E.GH) w t" if "fconnect (face E.GH) v w" for v w t
    using fconnect_trans[OF that] fconnect_trans[OF E.T2.NN.F.fconnect_sym[OF that]] by blast
  have invL: "L v \<longleftrightarrow> L w" if "fconnect (face E.GH) v w" for v w
    using cH[OF that] E.T2.NN.fband_cface[OF that] unfolding L_def by simp
  have invR: "R v \<longleftrightarrow> R w" if "fconnect (face E.GH) v w" for v w
    using cH[OF that] E.T2.NN.fband_cface[OF that] unfolding R_def by simp
  have XH_old: "\<not> fconnect (face E.GH) E.XH v" if "v \<in> E.D" for v using E.cface_GH_XH that by auto
  have nob: "\<not> fband E.GH l E.XH" if "set l \<subseteq> E.D" for l using that XH_old by (auto simp: fband_def)
  have mD: "set (mask mr r3) \<subseteq> E.D" "set (mask mk ker) \<subseteq> E.D"
    using set_mask_subset[of mr r3] set_mask_subset[of mk ker] r3D kerD by auto
  have enD: "edge G (node G x) \<in> E.D" "edge G x \<in> E.D" using E.x0D by simp_all
  have caseXH: "L E.XH \<longleftrightarrow> R E.XH"
  proof -
    have "\<not> fconnect (face E.GH) E.XH E.T.Xe" "\<not> fconnect (face E.GH) E.XH E.Xe" using E.cface_GH_XH by simp_all
    then show ?thesis unfolding L_def R_def
      using XYXH XH_old[OF E.nx0D] XH_old[OF E.x0D] XH_old[OF fexD] XH_old[OF enD(1)] XH_old[OF enD(2)]
        nob[OF ILD] nob[OF mD(1)] nob[OF mD(2)] by blast
  qed
  have caseD: "L v \<longleftrightarrow> R v" if vD: "v \<in> E.D" for v
  proof -
    have f1: "fconnect (face E.GH) v E.Xe \<longleftrightarrow> fconnect (face G) v (node G x)"
      using cH[OF XeN, of v] oldf[OF vD E.nx0D] E.T2.NN.F.fconnect_commute by metis
    have f2: "fconnect (face E.GH) v (edge G (node G x)) \<longleftrightarrow> fconnect (face G) v x"
      using oldf[OF vD enD(1)] fconnect_trans[OF _ enxx, of v] fconnect_trans[OF _ E.F.fconnect_sym[OF enxx], of v]
      by blast
    have f3: "fconnect (face E.GH) v (edge G x) \<longleftrightarrow> fconnect (face G) v fex"
      using oldf[OF vD enD(2)] fconnect_trans[OF _ exf, of v] fconnect_trans[OF _ E.F.fconnect_sym[OF exf], of v]
      by blast
    have f4: "fconnect (face E.GH) v E.T.Xe \<longleftrightarrow> fconnect (face G) v x"
      using cH[OF E.cface_GH_TXe, of v] oldf[OF vD E.x0D] E.T2.NN.F.fconnect_commute by metis
    have f5: "\<not> fconnect (face E.GH) v E.XY" "\<not> fconnect (face E.GH) v E.XH"
      using XH_old[OF vD] cH[OF XYXH] E.T2.NN.F.fconnect_commute by metis+
    have fb: "fband E.GH l v \<longleftrightarrow> fband G l v" if "set l \<subseteq> E.D" for l
      by (rule fband_transfer[OF that vD]) (rule oldf)
    have IHv: "fband G IL v \<longleftrightarrow> (a0 \<and> fconnect (face G) v (node G x)) \<or> (a1 \<and> fconnect (face G) v x) \<or>
        (a2 \<and> fconnect (face G) v fex) \<or> fband G (mask mr r3) v \<or> fband G (mask mk ker) v"
      using IH'(2)[OF vD] unfolding IL_def[symmetric] hr ma
      by (simp add: fband_app fband_mask_Cons del: mask.simps)
    show ?thesis unfolding L_def R_def
      using f1 f2 f3 f4 f5 fb[OF ILD] fb[OF mD(1)] fb[OF mD(2)] oldf[OF vD E.nx0D] oldf[OF vD E.x0D]
        oldf[OF vD fexD] IHv by blast
  qed
  have "fband E.GH (insertE E.GH (mask cm (E.XY # node G x # x # En))) u \<longleftrightarrow>
       fband E.GH (cpmask (Cfmask ((b0 \<or> a0) # b1 # (b2 \<or> a2) # mr) ((b0 \<or> b1 \<or> b2 \<or> a1) # mk)) (CpH # cp)) u"
    if u: "u \<in> darts E.GH" for u
  proof -
    have "L u \<longleftrightarrow> R u"
    proof (cases "\<exists>y \<in> E.D. fconnect (face E.GH) u y")
      case True
      then obtain y where yD: "y \<in> E.D" and uy: "fconnect (face E.GH) u y" by blast
      show ?thesis using invL[OF uy] invR[OF uy] caseD[OF yD] by simp
    next
      case False
      then have "fconnect (face E.GH) E.XH u" using E.fband_GH[OF u] by blast
      then have uy: "fconnect (face E.GH) u E.XH" by (rule E.T2.NN.F.fconnect_sym)
      show ?thesis using invL[OF uy] invR[OF uy] caseXH by simp
    qed
    then show ?thesis using goal by simp
  qed
  then show "proper_cpmask (CpH # cp) (ctrband cm (CpH # cp)) \<and>
     (\<forall>u \<in> darts (cpG (CpH # cp)). fband (cpG (CpH # cp)) (insertE (cpG (CpH # cp)) (mask cm (ctrenum (CpH # cp)))) u \<longleftrightarrow>
        fband (cpG (CpH # cp)) (cpmask (ctrband cm (CpH # cp)) (CpH # cp)) u)"
    using pcm unfolding cbH cpH fst_conv enH by blast
qed

lemma cb_all: "config_prog cp \<Longrightarrow> cb_ok cp"
proof (induction cp)
  case Nil then show ?case by simp
next
  case (Cons s cp)
  obtain G x where c: "cpmap cp = (G, x)" by (cases "cpmap cp")
  have cpo: "config_prog (s # cp)" using Cons.prems by simp
  show ?case
  proof (cases s)
    case (CpR i) then show ?thesis using cb_R[OF c] Cons.IH cpo by simp
  next
    case CpY
    show ?thesis
    proof (cases "cp = []")
      case True then show ?thesis using cb_Y0 CpY by simp
    next
      case False
      then have h: "config_prog cp" using cpo CpY by (cases cp) auto
      show ?thesis using cb_Y[OF c h] Cons.IH h CpY by simp
    qed
  next
    case CpH
    then have h: "config_prog cp" using cpo by simp
    show ?thesis using cb_H[OF c h] Cons.IH h CpH by simp
  qed (use cpo in simp_all)
qed

theorem ctrband_correct:
  assumes "length cm = ctrmsize cp" "config_prog cp"
  shows "proper_cpmask cp (ctrband cm cp)"
    and "u \<in> darts (cpG cp) \<Longrightarrow> fband (cpG cp) (insertE (cpG cp) (mask cm (ctrenum cp))) u \<longleftrightarrow>
           fband (cpG cp) (cpmask (ctrband cm cp) cp) u"
  using cb_all[of cp] assms unfolding cb_ok_def by blast+

section \<open>The contract tree\<close>

definition cfcontract_mask :: "config \<Rightarrow> bool list" where
  "cfcontract_mask cf = ctrmask (cfprog cf) (cfcontract_ref cf)"

definition cfcontract :: "config \<Rightarrow> nat list" where
  "cfcontract cf = mask (cfcontract_mask cf) (ctrenum (cfprog cf))"

fun cptriad :: "cfmask \<Rightarrow> cprog \<Rightarrow> nat \<Rightarrow> bool" where
  "cptriad ccm cp 0 = False"
| "cptriad ccm cp (Suc i) =
     (case cpadj (cfmask1 cp i) cp of Cfmask mrt mkt \<Rightarrow>
        (case ccm of Cfmask mrc mkc \<Rightarrow>
           (let mct = mask mrc mrt @ mask mkc mkt in
            if (\<exists>b \<in> set mct. \<not> b) \<and> 2 < count_list mct True then True else cptriad ccm cp i)))"

definition valid_ctrm :: "bool list \<Rightarrow> cprog \<Rightarrow> bool" where
  "valid_ctrm cm cp = (let k = count_list cm True in
     if k = 4 then cptriad (ctrband cm cp) cp (cpksize cp) else 0 < k \<and> k \<le> 3)"

definition contract_ctree :: "config \<Rightarrow> ctree option" where
  "contract_ctree cf = (let cp = cfprog cf; cm = cfcontract_mask cf in
     case cfctr (replicate (cprsize cp) False) cm cp of
       Some cpc \<Rightarrow> if valid_ctrm cm cp then Some (cpcolor cpc) else None
     | None \<Rightarrow> None)"

lemma addc_eq0: "a +c b = Color0 \<longleftrightarrow> a = b"
  by (cases a; cases b) simp_all

lemma contract_ctree_trace:
  assumes ct: "contract_ctree cf = Some t"
    and tr: "cc_ring_trace (cpG (cfprog cf)) (cfcontract cf) (rev (cfring cf)) et"
  shows "ctree_mem t (etrace (tl et))"
proof -
  define cp where "cp = cfprog cf"
  define cm where "cm = cfcontract_mask cf"
  define mr0 where "mr0 = replicate (cprsize cp) False"
  define r where "r = cpring_of cp"
  obtain cpc where cf0: "cfctr mr0 cm cp = Some cpc" and tdef: "t = cpcolor cpc"
    using ct by (auto simp: contract_ctree_def Let_def cp_def cm_def mr0_def split: option.splits if_splits)
  obtain k where kc: "cc_coloring (cpG cp) (mask cm (ctrenum cp)) k" and et: "et = trace (map k r)"
    using tr by (auto simp: cc_ring_trace_def cfring_def cfcontract_def cp_def cm_def r_def)
  have l1: "length mr0 = cprsize cp" by (simp add: mr0_def)
  have l2: "length cm = ctrmsize cp" by (simp add: cm_def cfcontract_mask_def size_ctrmask cp_def)
  have kc': "cc_coloring (cpG cp) (mask mr0 (cpring_of cp) @ mask cm (ctrenum cp)) k"
    using kc by (simp add: mr0_def)
  obtain k' where col: "coloring (cpG cpc) k'"
    and Ek: "map k' (cpring_of cpc) = map k (mask (map Not mr0) (cpring_of cp))"
    using cfctr_correct[OF l1 l2 kc' cf0] by blast
  have lr: "length r = cprsize cp" by (simp add: r_def size_ring_cpmap)
  have "mask (map Not mr0) r = r" using lr by (intro mask_true) (simp_all add: mr0_def)
  then have Ek': "map k' (cpring_of cpc) = map k r" using Ek by (simp add: r_def)
  define e where "e = tl et"
  define h where "h = etrace_perm e"
  have rne: "r \<noteq> []" using hypermap.cpring_ne[OF hypermap_cpmap[of cp]] by (simp add: r_def cpring_of_def)
  have etne: "et \<noteq> []" using et rne length_trace[of "map k r"] by (metis length_0_conv length_map)
  then obtain c where etc: "et = c # e" by (cases et) (simp_all add: e_def)
  have "sumt (c # e) = Color0" unfolding etc[symmetric] et by (rule sumt_trace)
  then have "c +c sumt e = Color0" by simp
  then have cs: "c = sumt e" by (simp add: addc_eq0)
  have mm: "map (permc h \<circ> k') (cpring_of cpc) = permt h (map k r)"
    using arg_cong[OF Ek', of "map (permc h)"] by (simp add: permt_def)
  have "trace (map (permc h \<circ> k') (cpring_of cpc)) = permt h et"
    unfolding mm trace_permt et ..
  also have "\<dots> = sumt (etrace e) # etrace e"
    using etc cs by (simp add: permt_def etrace_def sumt_permt[symmetric] h_def)
  finally have trE: "trace (map (permc h \<circ> k') (cpring_of cpc)) = sumt (etrace e) # etrace e" .
  have rt: "ring_trace (cpG cpc) (cpring_of cpc) (sumt (etrace e) # etrace e)"
  proof -
    have "inj (permc h)" using permc_inj by (intro injI) simp
    then have "coloring (cpG cpc) (permc h \<circ> k')"
      by (rule hypermap.coloring_inj[OF hypermap_cpmap _ col])
    then show ?thesis unfolding ring_trace_def using trE by metis
  qed
  show ?thesis unfolding tdef e_def[symmetric] ctree_mem_cpcolor using even_etrace rt by simp
qed

lemma contract_ctree_basic:
  assumes ct: "contract_ctree cf = Some t"
  defines "cp \<equiv> cfprog cf" and "cm \<equiv> cfcontract_mask cf"
  shows "config_prog cp" and "length cm = ctrmsize cp" and "valid_ctrm cm cp"
    and "set (cfring cf) \<inter> set (insertE (cpG cp) (cfcontract cf)) = {}"
    and "sparse (cpG cp) (insertE (cpG cp) (cfcontract cf))"
    and "length (cfcontract cf) = count_list cm True"
proof -
  define mr0 where "mr0 = replicate (cprsize cp) False"
  obtain cpc where cf0: "cfctr mr0 cm cp = Some cpc" and vc: "valid_ctrm cm cp"
    using ct by (auto simp: contract_ctree_def Let_def cp_def cm_def mr0_def split: option.splits if_splits)
  show cpo: "config_prog cp" using cfctr_config_prog[of mr0 cm cp] cf0 by simp
  show l2: "length cm = ctrmsize cp" by (simp add: cm_def cfcontract_mask_def size_ctrmask cp_def)
  show "valid_ctrm cm cp" by (rule vc)
  have l1: "length mr0 = cprsize cp" by (simp add: mr0_def)
  have cc: "cfcontract cf = mask cm (ctrenum cp)" by (simp add: cfcontract_def cm_def cp_def)
  have sp: "sparse (cpG cp) (cpx cp # insertE (cpG cp) (cfcontract cf))"
    using sparse_cfctr[OF l1 l2] cf0 cc by (simp add: mr0_def)
  show "sparse (cpG cp) (insertE (cpG cp) (cfcontract cf))"
    using sp sparse_Cons[OF hypermap_cpmap[of cp]] by blast
  show "length (cfcontract cf) = count_list cm True"
    using cc length_mask[of cm "ctrenum cp"] l2 size_ctrenum[of cp] by simp
  have u: "distinct (insertE (cpG cp) (cpring_of cp) @ insertE (cpG cp) (ctrenum cp))"
    using uniq_ctrenum[OF cpo] by (simp add: insertE_app)
  have s1: "set (cpring_of cp) \<subseteq> set (insertE (cpG cp) (cpring_of cp))" by (auto simp: set_insertE)
  have s2: "set (insertE (cpG cp) (cfcontract cf)) \<subseteq> set (insertE (cpG cp) (ctrenum cp))"
    using set_mask_subset[of cm "ctrenum cp"] cc by (auto simp: set_insertE)
  show "set (cfring cf) \<inter> set (insertE (cpG cp) (cfcontract cf)) = {}"
    using u s1 s2 by (auto simp: cfring_def cp_def)
qed

section \<open>Triads\<close>

lemma distinct_mask: "distinct q \<Longrightarrow> distinct (mask m q)"
proof (induction m q rule: mask.induct)
  case (1 b m x s) then show ?case using set_mask_subset[of m s] by auto
qed simp_all

lemma mask_both:
  assumes "length mc = length q" "length mt = length q" "distinct q"
  shows "count_list (mask mc mt) True = length (mask (map2 (\<and>) mc mt) q)"
    and "set (mask (map2 (\<and>) mc mt) q) \<subseteq> set (mask mc q) \<inter> set (mask mt q)"
    and "(\<exists>b \<in> set (mask mc mt). \<not> b) \<Longrightarrow> \<exists>z \<in> set (mask mc q). z \<notin> set (mask mt q)"
  using assms
proof (induction q arbitrary: mc mt)
  case Nil
  { case 1 then show ?case by simp }
  { case 2 then show ?case by simp }
  { case 3 then show ?case by simp }
next
  case (Cons a q)
  { case 1
    then obtain b mc' c mt' where "mc = b # mc'" "mt = c # mt'" "length mc' = length q" "length mt' = length q"
      by (metis length_Suc_conv)
    then show ?case using Cons.IH(1)[of mc' mt'] 1 by (cases b; cases c) simp_all }
  { case 2
    then obtain b mc' c mt' where m: "mc = b # mc'" "mt = c # mt'" "length mc' = length q" "length mt' = length q"
      by (metis length_Suc_conv)
    then show ?case using Cons.IH(2)[of mc' mt'] 2 by (cases b; cases c) auto }
  { case 3
    then obtain b mc' c mt' where m: "mc = b # mc'" "mt = c # mt'" "length mc' = length q" "length mt' = length q"
      by (metis length_Suc_conv)
    have aq: "a \<notin> set q" using 3 by simp
    show ?case
    proof (cases "b \<and> \<not> c")
      case True
      then show ?thesis using m aq set_mask_subset[of mt' q] by auto
    next
      case False
      then have "\<exists>b \<in> set (mask mc' mt'). \<not> b" using 3(1) m by (cases b; cases c) auto
      then obtain z where z: "z \<in> set (mask mc' q)" "z \<notin> set (mask mt' q)" using Cons.IH(3)[of mc' mt'] m 3 by auto
      have "z \<noteq> a" using z(1) set_mask_subset[of mc' q] aq by auto
      then show ?thesis using z m by (cases b; cases c) auto
    qed }
qed

lemma cptriad_triad:
  assumes cpo: "config_prog cp" and l: "length cm = ctrmsize cp"
  shows "cptriad (ctrband cm cp) cp i \<Longrightarrow> i \<le> cpksize cp \<Longrightarrow>
    \<exists>x \<in> darts (cpG cp). kernel (cpG cp) (rev (cpring_of cp)) x \<and>
      triad (cpG cp) (insertE (cpG cp) (mask cm (ctrenum cp))) x"
proof (induction i)
  case 0 then show ?case by simp
next
  case (Suc i)
  define G where "G = cpG cp"
  interpret H: hypermap G unfolding G_def by (rule hypermap_cpmap)
  have plG: "plain G" using cpmap_plain[OF config_prog_cubic[OF cpo]] by (simp add: G_def)
  define r where "r = cpring_of cp"
  define ker where "ker = cpker cp"
  define q where "q = r @ ker"
  define cc where "cc = mask cm (ctrenum cp)"
  have simq: "simple G q" using cpmap_simple[of cp] cpo by (simp add: q_def r_def ker_def G_def)
  have dq: "distinct q" by (rule H.simple_distinct[OF simq])
  have ik: "i < cpksize cp" using Suc.prems(2) by simp
  have lker: "length ker = cpksize cp" using size_cpker[OF cpo] by (simp add: ker_def)
  have lr: "length r = cprsize cp" by (simp add: r_def size_ring_cpmap)
  define x where "x = ker ! i"
  have xk: "x \<in> set ker" using ik lker by (simp add: x_def)
  have qD: "set q \<subseteq> darts G"
    using cpker_darts[of cp] cpo hypermap.ringD_gen[OF hypermap_cpmap cpx_in[of cp]]
    by (auto simp: q_def r_def ker_def G_def cpring_of_def)
  have xD: "x \<in> darts G" using xk qD by (auto simp: q_def)
  have pr1: "proper_cpmask cp (cfmask1 cp i)" by (rule proper_cpmask1)
  obtain mrt mkt where ca: "cpadj (cfmask1 cp i) cp = Cfmask mrt mkt" by (cases "cpadj (cfmask1 cp i) cp")
  obtain mrc mkc where cb: "ctrband cm cp = Cfmask mrc mkc" by (cases "ctrband cm cp")
  have lt: "length mrt = length r" "length mkt = length ker" using cpadj_proper[OF pr1] ca lr lker by simp_all
  have lc: "length mrc = length r" "length mkc = length ker"
    using ctrband_correct(1)[OF l cpo] cb lr lker by simp_all
  define mt where "mt = mrt @ mkt"
  define mc where "mc = mrc @ mkc"
  have lmt: "length mt = length q" and lmc: "length mc = length q" using lt lc by (simp_all add: mt_def mc_def q_def)
  have mtq: "mask mt q = cpmask (Cfmask mrt mkt) cp" using lt by (simp add: mt_def q_def mask_append r_def ker_def)
  have mcq: "mask mc q = cpmask (Cfmask mrc mkc) cp" using lc by (simp add: mc_def q_def mask_append r_def ker_def)
  have A1: "fband G (mask mt q) u \<longleftrightarrow> adj G u x" if "u \<in> darts G" for u
  proof -
    have "cpmask (cfmask1 cp i) cp = [x]" using cpmask1[OF ik cpo] by (simp add: x_def ker_def)
    then show ?thesis using cpmask_adj[of cp "cfmask1 cp i" u] cpo pr1 that ca mtq by (simp add: G_def)
  qed
  have A2: "fband G (insertE G cc) u \<longleftrightarrow> fband G (mask mc q) u" if "u \<in> darts G" for u
    using ctrband_correct(2)[OF l cpo, of u] that cb mcq by (simp add: G_def cc_def)
  have mcmt: "mask (mrc @ mkc) (mrt @ mkt) = mask mrc mrt @ mask mkc mkt" using lt lc by (simp add: mask_append)
  show ?case
  proof (cases "(\<exists>b \<in> set (mask mrc mrt @ mask mkc mkt). \<not> b) \<and> 2 < count_list (mask mrc mrt @ mask mkc mkt) True")
    case False
    then have "cptriad (ctrband cm cp) cp i" using Suc.prems(1) ca cb by (simp add: Let_def)
    then show ?thesis using Suc.IH Suc.prems(2) by simp
  next
    case True
    then have hasF: "\<exists>b \<in> set (mask mc mt). \<not> b" and cnt: "2 < count_list (mask mc mt) True"
      using mcmt by (simp_all add: mc_def mt_def)
    \<comment> \<open>x is in the kernel\<close>
    have kx: "kernel G (rev r) x"
    proof -
      have "\<forall>y \<in> set ker. \<not> fband G r y" using simq by (simp add: q_def H.simple_append)
      then show ?thesis using xk by (simp add: kernel_def fband_def)
    qed
    have simp_eq: "a = b" if "a \<in> set q" "b \<in> set q" "fconnect (face G) a b" for a b
      by (rule H.simple_cface[OF simq that])
    \<comment> \<open>a contract face not adjacent to x\<close>
    have nall: "\<not> (\<forall>y \<in> set (insertE G cc). adj G x y)"
    proof
      assume all: "\<forall>y \<in> set (insertE G cc). adj G x y"
      obtain z where zc: "z \<in> set (mask mc q)" and zt: "z \<notin> set (mask mt q)"
        using mask_both(3)[OF lmc lmt dq hasF] by blast
      have zq: "z \<in> set q" using zc set_mask_subset[of mc q] by blast
      have zD: "z \<in> darts G" using zq qD by blast
      have "fband G (insertE G cc) z" using A2[OF zD] zc by (auto simp: fband_def)
      then obtain y where yc: "y \<in> set (insertE G cc)" and zy: "fconnect (face G) z y" by (auto simp: fband_def)
      have "adj G x y" using all yc by blast
      then have "adj G x z" using H.adj_cface_r[OF zy] by simp
      then have "adj G z x" by (rule H.adj_sym[OF plG])
      then have "fband G (mask mt q) z" using A1[OF zD] by simp
      then obtain w where wt: "w \<in> set (mask mt q)" and zw: "fconnect (face G) z w" by (auto simp: fband_def)
      have "z = w" using simp_eq[OF zq _ zw] wt set_mask_subset[of mt q] by blast
      then show False using zt wt by simp
    qed
    \<comment> \<open>at least three contract faces adjacent to x\<close>
    define Z where "Z = set (mask (map2 (\<and>) mc mt) q)"
    have dZ: "distinct (mask (map2 (\<and>) mc mt) q)" by (rule distinct_mask[OF dq])
    have cZ: "2 < card Z" using mask_both(1)[OF lmc lmt dq] cnt dZ distinct_card by (metis Z_def)
    have Zsub: "Z \<subseteq> set (mask mc q) \<inter> set (mask mt q)" using mask_both(2)[OF lmc lmt dq] by (simp add: Z_def)
    define P where "P y \<longleftrightarrow> fband G (insertE G cc) (edge G y)" for y
    define W where "W z = (SOME w. fconnect (face G) x w \<and> fconnect (face G) (edge G w) z)" for z
    have Wz: "fconnect (face G) x (W z) \<and> fconnect (face G) (edge G (W z)) z" if zZ: "z \<in> Z" for z
    proof -
      have zq: "z \<in> set q" using zZ Zsub set_mask_subset[of mc q] by blast
      have zD: "z \<in> darts G" using zq qD by blast
      have "fband G (mask mt q) z" using zZ Zsub by (auto simp: fband_def)
      then have "adj G z x" using A1[OF zD] by simp
      then have "adj G x z" by (rule H.adj_sym[OF plG])
      then have "\<exists>w. fconnect (face G) x w \<and> fconnect (face G) (edge G w) z" by (auto simp: H.adj_iff)
      then show ?thesis unfolding W_def by (rule someI_ex)
    qed
    have WP: "W z \<in> set (filter P (orb (face G) x))" if zZ: "z \<in> Z" for z
    proof -
      have zq: "z \<in> set q" using zZ Zsub set_mask_subset[of mc q] by blast
      have zD: "z \<in> darts G" using zq qD by blast
      have "fband G (insertE G cc) z" using A2[OF zD] zZ Zsub by (auto simp: fband_def)
      then have "P (W z)" unfolding P_def using H.fband_cface[OF conjunct2[OF Wz[OF zZ]]] by simp
      moreover have "W z \<in> set (orb (face G) x)" using Wz[OF zZ] by (simp add: H.F.set_orb H.F.in_cyc_iff)
      ultimately show ?thesis by simp
    qed
    have injW: "inj_on W Z"
    proof (rule inj_onI)
      fix z1 z2 assume z1: "z1 \<in> Z" and z2: "z2 \<in> Z" and eq: "W z1 = W z2"
      have a: "fconnect (face G) (edge G (W z1)) z1" and b: "fconnect (face G) (edge G (W z1)) z2"
        using Wz[OF z1] Wz[OF z2] eq by simp_all
      have "fconnect (face G) z1 z2" by (rule fconnect_trans[OF H.F.fconnect_sym[OF a] b])
      then show "z1 = z2" using simp_eq z1 z2 Zsub set_mask_subset[of mc q] by blast
    qed
    have "card Z = card (W ` Z)" using card_image[OF injW] by simp
    also have "\<dots> \<le> card (set (filter P (orb (face G) x)))"
      using WP by (intro card_mono) auto
    also have "\<dots> \<le> length (filter P (orb (face G) x))" by (rule card_length)
    finally have "2 < length (filter P (orb (face G) x))" using cZ by simp
    then have "triad G (insertE G cc) x" using nall by (simp add: triad_def P_def[abs_def])
    then show ?thesis using xD kx by (auto simp: G_def r_def cc_def)
  qed
qed

theorem contract_ctreeP:
  assumes ct: "contract_ctree cf = Some t"
  shows "valid_contract (cpG (cfprog cf)) (cfring cf) (cfcontract cf)"
    and "cc_ring_trace (cpG (cfprog cf)) (cfcontract cf) (rev (cfring cf)) et \<Longrightarrow> ctree_mem t (etrace (tl et))"
proof -
  define cp where "cp = cfprog cf"
  define cm where "cm = cfcontract_mask cf"
  note B = contract_ctree_basic[OF ct, folded cp_def cm_def]
  have lc: "length (cfcontract cf) \<in> {1, 2, 3, 4}"
    using B(3) B(6) by (auto simp: valid_ctrm_def Let_def split: if_splits)
  have tri: "length (cfcontract cf) = 4 \<longrightarrow>
      (\<exists>x \<in> darts (cpG cp). kernel (cpG cp) (cfring cf) x \<and> triad (cpG cp) (insertE (cpG cp) (cfcontract cf)) x)"
  proof
    assume "length (cfcontract cf) = 4"
    then have "cptriad (ctrband cm cp) cp (cpksize cp)" using B(3) B(6) by (simp add: valid_ctrm_def Let_def)
    from cptriad_triad[OF B(1) B(2) this le_refl] show
      "\<exists>x \<in> darts (cpG cp). kernel (cpG cp) (cfring cf) x \<and> triad (cpG cp) (insertE (cpG cp) (cfcontract cf)) x"
      by (simp add: cfring_def cfcontract_def cp_def cm_def)
  qed
  show "valid_contract (cpG (cfprog cf)) (cfring cf) (cfcontract cf)"
    unfolding valid_contract_def using B(4) B(5) lc tri by (simp add: cp_def)
  show "cc_ring_trace (cpG (cfprog cf)) (cfcontract cf) (rev (cfring cf)) et \<Longrightarrow> ctree_mem t (etrace (tl et))"
    by (rule contract_ctree_trace[OF ct])
qed

end
