(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Snip.thy
    Cutting a planar hypermap along a ring (simple R-cycle) into a disk map and
    a remainder map that patch together.
    Ported from G. Gonthier's Coq development (snip.v).
*)
theory Snip
  imports Four_Colour_Base.Patch Four_Colour_Base.Euler_Tree
begin

section \<open>Auxiliary list lemmas\<close>

lemma path_seg: "path (frel g) ((g ^^ i) x) (map (\<lambda>j. (g ^^ j) x) [Suc i..<Suc i + d])"
proof (induction d arbitrary: i)
  case 0
  then show ?case by simp
next
  case (Suc d)
  have "[Suc i..<Suc i + Suc d] = Suc i # [Suc (Suc i)..<Suc (Suc i) + d]"
    by (simp add: upt_conv_Cons)
  then show ?case using Suc.IH[of "Suc i"] by simp
qed

lemma path_fun_succ:
  "path (\<lambda>a b. g a = b) a p \<Longrightarrow> w \<in> set (a # p) \<Longrightarrow> w \<noteq> lastd a p \<Longrightarrow> g w \<in> set p"
proof (induction p arbitrary: a)
  case Nil
  then show ?case by simp
next
  case (Cons u p)
  show ?case
  proof (cases "w = a")
    case True
    then show ?thesis using Cons.prems(1) by simp
  next
    case False
    then have "w \<in> set (u # p)" using Cons.prems(2) by simp
    moreover have "w \<noteq> lastd u p" using Cons.prems(3) by simp
    moreover have "path (\<lambda>a b. g a = b) u p" using Cons.prems(1) by simp
    ultimately have "g w \<in> set p" using Cons.IH by blast
    then show ?thesis by simp
  qed
qed

lemma cycle_fun_closed:
  assumes "path (\<lambda>a b. g a = b) a p" "g (lastd a p) = a" "w \<in> set (a # p)"
  shows "g w \<in> set (a # p)"
proof (cases "w = lastd a p")
  case True
  then show ?thesis using assms(2) by simp
next
  case False
  then show ?thesis using path_fun_succ[OF assms(1,3)] by simp
qed

lemma split_last_in:
  assumes aC: "a \<in> C"
  shows "\<exists>p1 w p2. a # p = p1 @ w # p2 \<and> w \<in> C \<and> set p2 \<inter> C = {}"
proof (induction p rule: rev_induct)
  case Nil
  show ?case by (intro exI[of _ "[]"] exI[of _ a] exI[of _ "[]"]) (simp add: aC)
next
  case (snoc v p)
  show ?case
  proof (cases "v \<in> C")
    case True
    show ?thesis by (intro exI[of _ "a # p"] exI[of _ v] exI[of _ "[]"]) (simp add: True)
  next
    case False
    obtain p1 w p2 where h: "a # p = p1 @ w # p2" "w \<in> C" "set p2 \<inter> C = {}"
      using snoc.IH by (elim exE conjE) simp
    show ?thesis by (intro exI[of _ p1] exI[of _ w] exI[of _ "p2 @ [v]"]) (use h False in simp)
  qed
qed

lemma hypermap_cancel3:
  assumes fin: "finite A"
    and cl: "\<And>x. x \<in> A \<Longrightarrow> E x \<in> A \<and> N x \<in> A \<and> F x \<in> A"
    and out: "\<And>x. x \<notin> A \<Longrightarrow> E x = x \<and> N x = x \<and> F x = x"
    and c3: "\<And>x. N (F (E x)) = x"
  shows "hypermap \<lparr>darts = A, edge = E, node = N, face = F\<rparr>"
proof -
  have injE: "inj_on E A"
  proof (rule inj_onI)
    fix x y assume "E x = E y"
    then have "N (F (E x)) = N (F (E y))" by simp
    then show "x = y" by (simp only: c3)
  qed
  have pE: "E permutes A" by (rule perm_of_inj[OF fin _ injE]) (use cl out in auto)
  have surjE: "E ` A = A" using endo_inj_surj[OF fin _ injE] cl by blast
  have surjN: "N ` A = A"
  proof
    show "N ` A \<subseteq> A" using cl by blast
    show "A \<subseteq> N ` A"
    proof
      fix w assume w: "w \<in> A"
      have "F (E w) \<in> A" using cl w by blast
      then show "w \<in> N ` A" using c3[of w] by (metis image_eqI)
    qed
  qed
  have injN: "inj_on N A" using surjN fin by (simp add: eq_card_imp_inj_on)
  have pN: "N permutes A" by (rule perm_of_inj[OF fin _ injN]) (use cl out in auto)
  have injF: "inj_on F A"
  proof (rule inj_onI)
    fix x y assume x: "x \<in> A" and y: "y \<in> A" and eq: "F x = F y"
    obtain x0 where x0: "x0 \<in> A" "x = E x0" using x surjE by blast
    obtain y0 where y0: "y0 \<in> A" "y = E y0" using y surjE by blast
    have "x0 = N (F (E x0))" by (simp only: c3)
    also have "\<dots> = N (F (E y0))" using eq x0 y0 by simp
    also have "\<dots> = y0" by (simp only: c3)
    finally show "x = y" using x0 y0 by simp
  qed
  have pF: "F permutes A" by (rule perm_of_inj[OF fin _ injF]) (use cl out in auto)
  show ?thesis by unfold_locales (simp_all add: fin pE pN pF c3)
qed

lemma cycle_from_next:
  assumes d: "distinct p" and nx: "\<And>x. x \<in> set p \<Longrightarrow> g x = next_in p x"
  shows "cycle (frel g) p"
  unfolding cycle_nth
proof (intro allI impI)
  fix i assume i: "i < length p"
  have pi: "p ! i \<in> set p" using i by simp
  have "lindex p (p ! i) = i" by (rule lindex_nth_distinct[OF d i])
  then show "g (p ! i) = p ! (Suc i mod length p)" using nx[OF pi] pi by (simp add: next_in_def)
qed

lemma cycle_next_in_rel:
  assumes c: "cycle R p" and x: "x \<in> set p"
  shows "R x (next_in p x)"
proof -
  have i: "lindex p x < length p" by (rule lindex_less[OF x])
  have "R (p ! lindex p x) (p ! (Suc (lindex p x) mod length p))" using c i by (simp add: cycle_nth)
  then show ?thesis using x by (simp add: nth_lindex next_in_def)
qed

locale snip_ring = hypermap +
  fixes r :: "'a list"
  assumes planarG: "planar G"
    and scycle_r: "scycle G (rlink G) r"
    and r_D: "set r \<subseteq> D"
begin

lemma cycle_r: "cycle (rlink G) r" using scycle_r by (simp add: scycle_def)
lemma simple_r: "simple G r" using scycle_r by (simp add: scycle_def)
lemma distinct_r: "distinct r" using simple_r simple_distinct by blast

lemma r_cface: "x \<in> set r \<Longrightarrow> y \<in> set r \<Longrightarrow> cface x y \<Longrightarrow> x = y"
  using simple_cface[OF simple_r] by blast

definition dlink :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "dlink x y \<longleftrightarrow> x \<notin> set r \<and> clink G x y"

definition dconnect :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "dconnect x y \<longleftrightarrow> connect dlink (inv n y) x"

definition diskN :: "'a set" where
  "diskN = {x \<in> D. \<exists>y \<in> set r. dconnect x y}"

definition diskE :: "'a set" where
  "diskE = diskN - set r"

definition diskF :: "'a set" where
  "diskF = diskN - {x. fband G r x}"

definition diskFC :: "'a set" where
  "diskFC = (D - diskN) - {x. fband G r x}"

lemma diskN_D: "diskN \<subseteq> D" by (auto simp: diskN_def)

lemma diskN_inv_node:
  assumes x: "x \<in> diskN"
  shows "inv n x \<in> diskN"
proof -
  have xD: "x \<in> D" using x by (simp add: diskN_def)
  have ixD: "inv n x \<in> D" using xD by (metis N.closed N.f_inv)
  show ?thesis
  proof (cases "x \<in> set r")
    case True
    then show ?thesis using ixD by (auto simp: diskN_def dconnect_def)
  next
    case False
    obtain y where y: "y \<in> set r" "connect dlink (inv n y) x" using x by (auto simp: diskN_def dconnect_def)
    have "dlink x (inv n x)" using False by (simp add: dlink_def clink_def)
    then have "connect dlink (inv n y) (inv n x)" by (rule rtranclp.rtrancl_into_rtrancl[OF y(2)])
    then show ?thesis using y(1) ixD by (auto simp: diskN_def dconnect_def)
  qed
qed

lemma diskN_node: "x \<in> D \<Longrightarrow> n x \<in> diskN \<longleftrightarrow> x \<in> diskN"
proof
  assume xD: "x \<in> D" and "n x \<in> diskN"
  have "inv n (n x) \<in> diskN" by (rule diskN_inv_node[OF \<open>n x \<in> diskN\<close>])
  then show "x \<in> diskN" by simp
next
  assume xD: "x \<in> D" and x: "x \<in> diskN"
  have cl: "\<And>w. w \<in> diskN \<Longrightarrow> inv n w \<in> diskN" by (rule diskN_inv_node)
  interpret NI: fperm "inv n" D by (rule fperm_inv[OF N.fperm_axioms])
  have "inv (inv n) x \<in> diskN" by (rule NI.closed_inv[OF cl x])
  moreover have "inv (inv n) = n" using N.bij by (simp add: inv_inv_eq)
  ultimately show "n x \<in> diskN" by simp
qed

lemma r_diskN: "x \<in> set r \<Longrightarrow> x \<in> diskN"
proof -
  assume xr: "x \<in> set r"
  have xD: "x \<in> D" using xr r_D by blast
  have ixD: "inv n x \<in> D" using xD by (metis N.closed N.f_inv)
  have "inv n x \<in> diskN" using xr ixD by (auto simp: diskN_def dconnect_def)
  then have "n (inv n x) \<in> diskN" using diskN_node[OF ixD] by simp
  then show ?thesis by simp
qed

lemma diskN_E: "x \<in> diskN \<longleftrightarrow> x \<in> set r \<or> x \<in> diskE"
  using r_diskN by (auto simp: diskE_def)

lemma diskF_face_aux: "x \<in> diskN \<Longrightarrow> x \<notin> set r \<Longrightarrow> f x \<in> diskN"
proof -
  assume xN: "x \<in> diskN" and xr: "x \<notin> set r"
  have xD: "x \<in> D" using xN diskN_D by blast
  obtain y where y: "y \<in> set r" "connect dlink (inv n y) x" using xN by (auto simp: diskN_def dconnect_def)
  have "dlink x (f x)" using xr by (simp add: dlink_def clink_def)
  then have "connect dlink (inv n y) (f x)" by (rule rtranclp.rtrancl_into_rtrancl[OF y(2)])
  then show ?thesis using y(1) xD by (auto simp: diskN_def dconnect_def)
qed

lemma diskF_face: "x \<in> diskF \<Longrightarrow> f x \<in> diskF"
proof -
  assume x: "x \<in> diskF"
  have xN: "x \<in> diskN" and nb: "\<not> fband G r x" using x by (auto simp: diskF_def)
  have xr: "x \<notin> set r" using nb fband_ring by blast
  have xD: "x \<in> D" using xN diskN_D by blast
  obtain y where y: "y \<in> set r" "connect dlink (inv n y) x" using xN by (auto simp: diskN_def dconnect_def)
  have "dlink x (f x)" using xr by (simp add: dlink_def clink_def)
  then have "connect dlink (inv n y) (f x)" by (rule rtranclp.rtrancl_into_rtrancl[OF y(2)])
  then have "f x \<in> diskN" using y(1) xD by (auto simp: diskN_def dconnect_def)
  moreover have "\<not> fband G r (f x)" using nb by simp
  ultimately show ?thesis by (simp add: diskF_def)
qed

lemma diskN_face_step: "w \<in> diskN \<Longrightarrow> w \<notin> set r \<Longrightarrow> f w \<in> diskN"
  using diskF_face_aux by blast

lemma diskN_walk:
  "w \<in> diskN \<Longrightarrow> (\<forall>j<k. (f ^^ j) w \<notin> set r) \<Longrightarrow> (f ^^ k) w \<in> diskN"
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  have "\<forall>j<k. (f ^^ j) w \<notin> set r" using Suc.prems(2) by simp
  then have "(f ^^ k) w \<in> diskN" using Suc.IH Suc.prems(1) by blast
  moreover have "(f ^^ k) w \<notin> set r" using Suc.prems(2) by simp
  ultimately show ?case using diskN_face_step by simp
qed

definition rcl :: "'a \<Rightarrow> 'a" where
  "rcl t = f (if t \<in> set r then e t else t)"

lemma path_face_rcl:
  "distinct (t # c) \<Longrightarrow> lastd t c \<in> set r \<Longrightarrow> path (frel f) t c \<Longrightarrow> path (\<lambda>a b. rcl a = b) t c"
proof (induction c arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons u c)
  have ft: "f t = u" and pu: "path (frel f) u c" using Cons.prems(3) by simp_all
  have tL: "t \<noteq> lastd u c" using Cons.prems(1) lastd_in[of u c] by auto
  have "lastd u c \<in> set (u # c)" by (rule lastd_in)
  then have "cface t (lastd u c)" using path_fconnect[of f t "u # c"] Cons.prems(3) by blast
  moreover have "lastd u c \<in> set r" using Cons.prems(2) by simp
  ultimately have "t \<notin> set r" using r_cface[of t "lastd u c"] tL by blast
  then have "rcl t = u" using ft by (simp add: rcl_def)
  moreover have "path (\<lambda>a b. rcl a = b) u c"
    using Cons.IH[of u] Cons.prems(1,2) pu by simp
  ultimately show ?case by simp
qed

lemma ring_arc:
  "y \<in> set r \<Longrightarrow> set r1 \<subseteq> set r \<Longrightarrow> path (rlink G) y r1 \<Longrightarrow> distinct (y # r1) \<Longrightarrow>
   \<exists>c2. path (\<lambda>a b. rcl a = b) y c2 \<and> distinct c2 \<and> lastd y c2 = lastd y r1 \<and>
        set r1 \<subseteq> set c2 \<and> (\<forall>t\<in>set c2. fband G r1 t)"
proof (induction r1 arbitrary: y)
  case Nil
  then show ?case by (intro exI[of _ "[]"]) simp
next
  case (Cons z r1)
  have zr: "z \<in> set r" and r1r: "set r1 \<subseteq> set r" using Cons.prems(2) by auto
  have yz: "rlink G y z" and pz: "path (rlink G) z r1" using Cons.prems(3) by simp_all
  have dz: "distinct (z # r1)" and zr1: "z \<notin> set r1" using Cons.prems(4) by auto
  obtain c2 where c2: "path (\<lambda>a b. rcl a = b) z c2" "distinct c2" "lastd z c2 = lastd z r1"
     "set r1 \<subseteq> set c2" "\<forall>t\<in>set c2. fband G r1 t"
    using Cons.IH[OF zr r1r pz dz] by blast
  define w where "w = f (e y)"
  have "cface (e y) z" using yz by (simp add: rlink_def)
  then have wz: "cface w z" by (simp add: w_def)
  obtain c1 where c1: "path (frel f) w c1" "lastd w c1 = z" "distinct (w # c1)"
    using connect_shortest[OF fconnect_connect[OF wz]] by blast
  have c1z: "cface t z" if "t \<in> set (w # c1)" for t
  proof -
    have "cface w t" using that path_fconnect[OF c1(1)] by auto
    show ?thesis using fconnect_trans[OF F.fconnect_sym[OF \<open>cface w t\<close>] wz] .
  qed
  have disj: "t \<notin> set c2" if "t \<in> set (w # c1)" for t
  proof
    assume tc2: "t \<in> set c2"
    then obtain u where u: "u \<in> set r1" "cface t u" using c2(5) by (auto simp: fband_def)
    have "cface z u" using fconnect_trans[OF F.fconnect_sym[OF c1z[OF that]] u(2)] .
    then have "z = u" using r_cface[of z u] zr u(1) r1r by blast
    then show False using zr1 u(1) by simp
  qed
  have "rcl y = w" using Cons.prems(1) by (simp add: rcl_def w_def)
  moreover have "path (\<lambda>a b. rcl a = b) w c1" using path_face_rcl[OF c1(3)] c1(1,2) zr by simp
  ultimately have p: "path (\<lambda>a b. rcl a = b) y ((w # c1) @ c2)" using c2(1) c1(2) by simp
  have d: "distinct ((w # c1) @ c2)" using c1(3) c2(2) disj by auto
  have l: "lastd y ((w # c1) @ c2) = lastd y (z # r1)"
    using c2(3) c1(2) lastd_append[of y "w # c1" c2] by simp
  have zin: "z \<in> set (w # c1)" using c1(2) lastd_in[of w c1] by simp
  have s: "set (z # r1) \<subseteq> set ((w # c1) @ c2)" using zin c2(4) by auto
  have b: "\<forall>t\<in>set ((w # c1) @ c2). fband G (z # r1) t"
  proof
    fix t assume "t \<in> set ((w # c1) @ c2)"
    then consider "t \<in> set (w # c1)" | "t \<in> set c2" by auto
    then show "fband G (z # r1) t"
    proof cases
      case 1
      then show ?thesis using c1z[OF 1] by (auto simp: fband_def)
    next
      case 2
      then show ?thesis using c2(5) by (auto simp: fband_def)
    qed
  qed
  show ?case using p d l s b by blast
qed

lemma clink_rcl: "clink G t (rcl t)"
  by (cases "t \<in> set r") (simp_all add: rcl_def clink_def edgeK)

lemma diskE_edge_fwd:
  assumes xE: "x \<in> diskE"
  shows "e x \<in> diskE"
proof -
  have xN: "x \<in> diskN" and xr: "x \<notin> set r" using xE by (auto simp: diskE_def)
  have xD: "x \<in> D" using xN diskN_D by blast
  define x' where "x' = f (e x)"
  have x'D: "x' \<in> D" using xD by (simp add: x'_def)
  have nx': "n x' = x" by (simp add: x'_def edgeK)
  have x'N: "x' \<in> diskN" using diskN_node[OF x'D] xN nx' by simp
  define m where "m = order f x'"
  have m0: "0 < m" by (simp add: m_def)
  have ex: "e x = (f ^^ (m - 1)) x'"
  proof -
    have "inv f x' = (f ^^ (m - 1)) x'" unfolding m_def by (rule F.inv_funpow_order)
    then show ?thesis by (simp add: x'_def)
  qed
  have idx: "i = j" if "(f ^^ i) x' = (f ^^ j) x'" "i < m" "j < m" for i j
    using F.funpow_inj_order[of i x' j] that by (simp add: m_def)
  show ?thesis
  proof (cases "\<exists>b<m. (f ^^ b) x' \<in> set r")
    case False
    then have "(f ^^ (m - 1)) x' \<in> diskN" using diskN_walk[OF x'N, of "m - 1"] m0 by auto
    moreover have "(f ^^ (m - 1)) x' \<notin> set r" using False m0 by auto
    ultimately show ?thesis using ex by (simp add: diskE_def)
  next
    case True
    then obtain b where b: "b < m" "(f ^^ b) x' \<in> set r" by blast
    define y where "y = (f ^^ b) x'"
    have yr: "y \<in> set r" using b by (simp add: y_def)
    have x'y: "cface x' y" by (simp add: y_def fconnect_funpow)
    obtain i where i: "i < length r" "r ! i = y" using yr by (meson in_set_conv_nth)
    define r1 where "r1 = drop (Suc i) r @ take i r"
    have dri: "drop i r = y # drop (Suc i) r" using i by (metis Cons_nth_drop_Suc)
    have rot: "rot i r = y # r1" by (simp add: rot_def r1_def dri)
    have cyc': "cycle (rlink G) (y # r1)"
      using cycle_r rot rot_rotate[of i r] i(1) cycle_rotate[of "rlink G" i r] by simp
    have dyr1: "distinct (y # r1)" using distinct_r distinct_rot[of i r] rot by simp
    have set_yr1: "set (y # r1) = set r" using set_rot[of i r] rot by simp
    have r1r: "set r1 \<subseteq> set r" using set_yr1 by auto
    have yr1: "y \<notin> set r1" using dyr1 by simp
    have pr1: "path (rlink G) y r1" and zy: "rlink G (lastd y r1) y"
      using cyc' by (simp_all add: cycle_Cons)
    define z where "z = lastd y r1"
    have "z \<in> set (y # r1)" unfolding z_def by (rule lastd_in)
    then have zr: "z \<in> set r" using set_yr1 by blast
    define z' where "z' = f (e z)"
    have nz': "n z' = z" by (simp add: z'_def edgeK)
    have z'D: "z' \<in> D" using zr r_D by (auto simp: z'_def)
    have "cface (e z) y" using zy by (simp add: rlink_def z_def)
    then have z'y: "cface z' y" by (simp add: z'_def)
    have x'z': "cface x' z'" using fconnect_trans[OF x'y F.fconnect_sym[OF z'y]] .
    then obtain a where a: "a < m" "(f ^^ a) x' = z'" using F.fconnect_order by (auto simp: m_def)
    have a0: "a \<noteq> 0"
    proof
      assume "a = 0"
      then have "f (e z) = f (e x)" using a(2) by (simp add: x'_def z'_def)
      then have "z = x" by simp
      then show False using xr zr by simp
    qed
    have ring_idx: "j = b" if "(f ^^ j) x' \<in> set r" "j < m" for j
    proof -
      have "cface y ((f ^^ j) x')" using F.fconnect_sym[OF x'y] by simp
      then have "y = (f ^^ j) x'" using r_cface[OF yr that(1)] by blast
      then show ?thesis using idx[of b j] b(1) that(2) by (simp add: y_def)
    qed
    have cy: "cface y ((f ^^ j) x')" for j using F.fconnect_sym[OF x'y] by simp
    have c2F'y: "\<not> cface y t" if ft: "fband G r1 t" for t
    proof
      assume yt: "cface y t"
      obtain u where u: "u \<in> set r1" "cface t u" using ft by (auto simp: fband_def)
      have "y = u" using r_cface[OF yr _ fconnect_trans[OF yt u(2)]] u(1) r1r by blast
      then show False using u(1) yr1 by simp
    qed
    show ?thesis
    proof (cases "b < a")
      case True
      define k where "k = m - 1 - a"
      have z'N: "z' \<in> diskN" using diskN_node[OF z'D] r_diskN[OF zr] nz' by simp
      have shift: "(f ^^ j) z' = (f ^^ (j + a)) x'" for j
        using a(2) by (simp add: funpow_add_apply)
      have nr: "(f ^^ j) z' \<notin> set r" if "j \<le> k" for j
      proof
        assume "(f ^^ j) z' \<in> set r"
        moreover have "j + a < m" using that a(1) by (simp add: k_def)
        ultimately have "j + a = b" using ring_idx[of "j + a"] shift by simp
        then show False using True by simp
      qed
      have "(f ^^ k) z' \<in> diskN" using diskN_walk[OF z'N] nr by auto
      moreover have "(f ^^ k) z' = e x"
      proof -
        have "k + a = m - 1" using a(1) by (simp add: k_def)
        then show ?thesis using shift[of k] ex by simp
      qed
      ultimately show ?thesis using nr[of k] by (simp add: diskE_def)
    next
      case False
      then have ab: "a \<le> b" by simp
      define c1 where "c1 = map (\<lambda>j. (f ^^ j) x') [Suc a..<Suc a + (b - a)]"
      have pc1: "path (frel f) z' c1" using path_seg[of f a x' "b - a"] a(2) by (simp add: c1_def)
      have lc1: "lastd z' c1 = y"
      proof -
        have lenc1: "length c1 = b - a" unfolding c1_def length_map length_upt by simp
        have "lastd z' c1 = (f ^^ length c1) z'" by (rule path_frel_last[OF pc1])
        then have "lastd z' c1 = (f ^^ (b - a)) z'" by (simp only: lenc1)
        also have "\<dots> = (f ^^ (b - a + a)) x'" using a(2) by (simp add: funpow_add_apply)
        finally show ?thesis using ab by (simp add: y_def)
      qed
      have Z: "z' # c1 = map (\<lambda>j. (f ^^ j) x') [a..<Suc b]"
      proof -
        have e1: "Suc a + (b - a) = Suc b" using ab by simp
        have e2: "[a..<Suc b] = a # [Suc a..<Suc b]" using ab by (simp add: upt_conv_Cons)
        show ?thesis unfolding c1_def e1 e2 list.map(2) using a(2) by simp
      qed
      have inj_x': "inj_on (\<lambda>j. (f ^^ j) x') {..<m}"
        by (auto intro!: inj_onI dest: idx)
      have dZ: "distinct (z' # c1)"
      proof -
        have "set [a..<Suc b] \<subseteq> {..<m}" using b(1) by auto
        then show ?thesis unfolding Z distinct_map using inj_on_subset[OF inj_x'] by simp
      qed
      have Zidx: "\<exists>j. a \<le> j \<and> j \<le> b \<and> t = (f ^^ j) x'" if "t \<in> set (z' # c1)" for t
        using that unfolding Z by auto
      obtain c2 where c2: "path (\<lambda>a b. rcl a = b) y c2" "distinct c2" "lastd y c2 = z"
        "set r1 \<subseteq> set c2" "\<forall>t\<in>set c2. fband G r1 t"
        using ring_arc[OF yr r1r pr1 dyr1] by (auto simp: z_def)
      define c where "c = c1 @ c2"
      have pc: "path (\<lambda>a b. rcl a = b) z' c"
        using path_face_rcl[OF dZ] lc1 yr pc1 c2(1) by (simp add: c_def)
      have c2nZ: "t \<notin> set (z' # c1)" if "t \<in> set c2" for t
      proof
        assume "t \<in> set (z' # c1)"
        then obtain j where "t = (f ^^ j) x'" using Zidx by blast
        then have "cface y t" using cy by simp
        then show False using c2F'y c2(5) that by blast
      qed
      have dc: "distinct (z' # c)" using dZ c2(2) c2nZ by (auto simp: c_def)
      have lc: "lastd z' c = z" using lc1 c2(3) lastd_append[of z' c1 c2] by (simp add: c_def)
      define C where "C = set (z' # c)"
      have rC: "set r \<subseteq> C"
      proof -
        have "y \<in> set (z' # c1)" using lc1 lastd_in[of z' c1] by simp
        then show ?thesis using set_yr1 c2(4) by (auto simp: C_def c_def)
      qed
      have rcl_closed: "rcl w \<in> C" if "w \<in> C" for w
        using cycle_fun_closed[OF pc _ that[unfolded C_def]] lc zr by (simp add: C_def rcl_def z'_def)
      have P0C: "(f ^^ j) x' \<notin> C" if "j < a" for j
      proof
        assume jC: "(f ^^ j) x' \<in> C"
        show False
        proof (cases "(f ^^ j) x' \<in> set (z' # c1)")
          case True
          then obtain j' where j': "a \<le> j'" "j' \<le> b" "(f ^^ j) x' = (f ^^ j') x'" using Zidx by blast
          then have "j = j'" using idx[of j j'] that a(1) b(1) by simp
          then show False using that j'(1) by simp
        next
          case False
          then have "(f ^^ j) x' \<in> set c2" using jC by (auto simp: C_def c_def)
          then show False using c2F'y c2(5) cy by blast
        qed
      qed
      have x'C: "x' \<notin> C" using P0C[of 0] a0 by simp
      have CD: "C \<subseteq> D"
      proof -
        have "path (clink G) z' c" using path_mono[OF _ pc] clink_rcl by blast
        then show ?thesis using clink_path_closed z'D by (auto simp: C_def)
      qed
      text \<open>A clink path from outside the contour, ending at @{term x'}.\<close>
      obtain x0 where x0: "x0 \<in> set r" "connect dlink (inv n x0) x"
        using xN by (auto simp: diskN_def dconnect_def)
      obtain p where p: "path dlink (inv n x0) p" "lastd (inv n x0) p = x"
        using x0(2) connect_path by metis
      have ix0C: "inv n x0 \<in> C"
      proof -
        have "rcl x0 = inv n x0" using x0(1) by (simp add: rcl_def inv_node_apply)
        then show ?thesis using rcl_closed[of x0] rC x0(1) by auto
      qed
      obtain p1 w p2 where sp: "inv n x0 # p = p1 @ w # p2" "w \<in> C" "set p2 \<inter> C = {}"
        using split_last_in[OF ix0C] by blast
      have pw: "path dlink w p2" and lw: "lastd w p2 = x"
      proof -
        have "path dlink (inv n x0) p" by (fact p(1))
        then have "path dlink (lastd (inv n x0) (tl (p1 @ [w]))) p2"
          using sp(1) path_append[of dlink "inv n x0" "tl (p1 @ [w])" p2]
          by (cases p1) auto
        moreover have "lastd (inv n x0) (tl (p1 @ [w])) = w" using sp(1) by (cases p1) auto
        ultimately show "path dlink w p2" by simp
        have "lastd (inv n x0) p = last (p1 @ w # p2)" using sp(1) by (metis last_ConsL list.distinct(1) last.simps)
        then show "lastd w p2 = x" using p(2) by (simp add: last_append split: if_splits)
      qed
      obtain x1 pth where x1: "n x1 \<in> C" "path (clink G) x1 pth" "lastd x1 pth = x'"
        "set (x1 # pth) \<inter> C = {}"
      proof (cases p2)
        case Nil
        then have "w = x" using lw by simp
        then show ?thesis using that[of x' "[]"] sp(2) nx' x'C by simp
      next
        case (Cons v p3)
        have wv: "dlink w v" and pv: "path dlink v p3" using pw Cons by simp_all
        have wr: "w \<notin> set r" and cl: "clink G w v" using wv by (simp_all add: dlink_def)
        have vC: "v \<notin> C" and p3C: "set p3 \<inter> C = {}" using sp(3) Cons by auto
        have wnv: "w = n v"
        proof -
          have "f w \<noteq> v"
          proof
            assume "f w = v"
            then have "rcl w = v" using wr by (simp add: rcl_def)
            then show False using rcl_closed[OF sp(2)] vC by simp
          qed
          then show ?thesis using cl by (simp add: clink_def)
        qed
        have "path (clink G) v p3" using path_mono[OF _ pv] by (auto simp: dlink_def)
        moreover have "clink G (lastd v p3) x'" using lw Cons nx' by (simp add: clink_def)
        ultimately have "path (clink G) v (p3 @ [x'])" by simp
        moreover have "set (v # p3 @ [x']) \<inter> C = {}" using vC p3C x'C by auto
        ultimately show ?thesis using that[of v "p3 @ [x']"] sp(2) wnv by simp
      qed
      define q1 where "q1 = map (\<lambda>j. (f ^^ j) x') [Suc 0..<Suc 0 + (a - 1)]"
      have pq1: "path (frel f) x' q1" using path_seg[of f 0 x' "a - 1"] by (simp add: q1_def)
      have lq1: "f (lastd x' q1) = z'"
      proof -
        have lenq1: "length q1 = a - 1" unfolding q1_def length_map length_upt by simp
        have "lastd x' q1 = (f ^^ length q1) x'" by (rule path_frel_last[OF pq1])
        then have "lastd x' q1 = (f ^^ (a - 1)) x'" by (simp only: lenq1)
        then have "f (lastd x' q1) = (f ^^ Suc (a - 1)) x'" by simp
        then show ?thesis using a0 a(2) by simp
      qed
      have q1C: "set q1 \<inter> C = {}"
      proof -
        have "j < a" if "j \<in> set [Suc 0..<Suc 0 + (a - 1)]" for j using that a0 by auto
        then show ?thesis using P0C by (auto simp: q1_def)
      qed
      define c0 where "c0 = pth @ q1"
      have pc0: "path (clink G) x1 c0"
      proof -
        have "path (clink G) x' q1" using path_mono[OF _ pq1] by (auto simp: clink_def)
        then show ?thesis using x1(2,3) by (simp add: c0_def)
      qed
      have lc0: "clink G (lastd x1 c0) z'"
      proof -
        have "lastd x1 c0 = lastd x' q1" using x1(3) lastd_append[of x1 pth q1] by (simp add: c0_def)
        then show ?thesis using lq1 by (simp add: clink_def)
      qed
      have c0C: "set (x1 # c0) \<inter> C = {}" using x1(4) q1C by (auto simp: c0_def)
      obtain c1' where c1': "path (clink G) x1 c1'" "lastd x1 c1' = lastd x1 c0"
        "distinct (x1 # c1')" "set c1' \<subseteq> set c0"
        using path_shorten[OF pc0] by blast
      have c1'C: "set (x1 # c1') \<inter> C = {}" using c0C c1'(4) by auto
      have x1D: "x1 \<in> D" using x1(1) CD by (metis N.closed subsetD)
      let ?M = "x1 # c1' @ z' # c"
      have "Moebius_path G ?M"
      proof (rule Moebius_pathI[OF hypermap_axioms])
        show "distinct (x1 # c1' @ z' # c)"
          using c1'(3) dc c1'C by (auto simp: C_def)
        have "path (clink G) z' c" using path_mono[OF _ pc] clink_rcl by blast
        then show "path (clink G) x1 (c1' @ z' # c)"
          using c1'(1,2) lc0 by simp
        show "n z' = lastd x1 (c1' @ z' # c)" using nz' lc by (simp add: lastd_append)
        have "z' \<notin> set c1'" using c1'C by (auto simp: C_def)
        moreover have "n x1 \<in> set (z' # c)" using x1(1) by (simp add: C_def)
        ultimately show "mem2 (c1' @ z' # c) z' (n x1)" by (simp add: mem2_split_iff)
      qed
      moreover have "set ?M \<subseteq> D"
      proof -
        have "set c1' \<subseteq> D" using clink_path_closed[OF c1'(1) x1D] .
        then show ?thesis using CD x1D by (auto simp: C_def)
      qed
      ultimately show ?thesis using planar_Jordan[OF hypermap_axioms planarG]
        unfolding Jordan_def by blast
    qed
  qed
qed

lemma diskE_edge: "x \<in> D \<Longrightarrow> e x \<in> diskE \<longleftrightarrow> x \<in> diskE"
proof
  assume "x \<in> diskE"
  then show "e x \<in> diskE" by (rule diskE_edge_fwd)
next
  assume xD: "x \<in> D" and ex: "e x \<in> diskE"
  have "inv e (e x) \<in> diskE" by (rule E.closed_inv[OF diskE_edge_fwd ex])
  then show "x \<in> diskE" by simp
qed


lemma r_diskE: "x \<in> set r \<Longrightarrow> x \<notin> diskE" by (simp add: diskE_def)

lemma diskE_D: "diskE \<subseteq> D" using diskN_D by (auto simp: diskE_def)

lemma rlink_prev: "x \<in> set r \<Longrightarrow> rlink G (prev_in r x) x"
  using cycle_next_in_rel[OF cycle_r prev_in_mem[of x r]] next_prev_in[OF distinct_r] by simp

section \<open>The disk map\<close>

definition snipd_edge :: "'a \<Rightarrow> 'a" where
  "snipd_edge x = (if x \<in> diskN then (if x \<in> set r then next_in r x else e x) else x)"

definition snipd_node :: "'a \<Rightarrow> 'a" where
  "snipd_node x = (if x \<in> diskN then n x else x)"

definition snipd_face :: "'a \<Rightarrow> 'a" where
  "snipd_face x = (if x \<in> diskN then (if x \<in> set r then f (e (prev_in r x)) else f x) else x)"

definition snipd :: "'a hypermap" where
  "snipd = \<lparr>darts = diskN, edge = snipd_edge, node = snipd_node, face = snipd_face\<rparr>"

lemma snipd_simps [simp]:
  "darts snipd = diskN" "edge snipd = snipd_edge" "node snipd = snipd_node" "face snipd = snipd_face"
  by (simp_all add: snipd_def)

lemma diskE_inN: "x \<in> diskE \<Longrightarrow> x \<in> diskN" by (simp add: diskE_def)

lemma diskN_notr_E: "x \<in> diskN \<Longrightarrow> x \<notin> set r \<Longrightarrow> x \<in> diskE" by (simp add: diskE_def)

lemma snipd_edge_cl: "x \<in> diskN \<Longrightarrow> snipd_edge x \<in> diskN"
proof -
  assume x: "x \<in> diskN"
  have xD: "x \<in> D" using x diskN_D by blast
  show ?thesis
  proof (cases "x \<in> set r")
    case True
    then show ?thesis using x r_diskN next_in_mem[OF True] by (simp add: snipd_edge_def)
  next
    case False
    have "e x \<in> diskE" using diskE_edge[OF xD] diskN_notr_E[OF x False] by blast
    then show ?thesis using x False diskE_inN by (simp add: snipd_edge_def)
  qed
qed

lemma snipd_node_cl: "x \<in> diskN \<Longrightarrow> snipd_node x \<in> diskN"
  using diskN_node diskN_D by (auto simp: snipd_node_def)

lemma face_in_diskN: "x \<in> diskE \<Longrightarrow> f x \<in> diskN"
proof -
  assume x: "x \<in> diskE"
  have fxD: "f x \<in> D" using x diskE_D by auto
  have nfxD: "n (f x) \<in> D" using fxD by simp
  have "e (n (f x)) \<in> diskE" using x by (simp add: faceK)
  then have "n (f x) \<in> diskE" using diskE_edge[OF nfxD] by blast
  then have "n (f x) \<in> diskN" by (rule diskE_inN)
  then show ?thesis using diskN_node[OF fxD] by blast
qed

lemma fe_in_diskN: "y \<in> diskN \<Longrightarrow> f (e y) \<in> diskN"
proof -
  assume y: "y \<in> diskN"
  have "f (e y) \<in> D" using y diskN_D by auto
  then show ?thesis using diskN_node[of "f (e y)"] y by (simp add: edgeK)
qed

lemma snipd_face_cl: "x \<in> diskN \<Longrightarrow> snipd_face x \<in> diskN"
proof -
  assume x: "x \<in> diskN"
  show ?thesis
  proof (cases "x \<in> set r")
    case True
    have "prev_in r x \<in> diskN" using r_diskN prev_in_mem[OF True] by blast
    then show ?thesis using x True fe_in_diskN by (simp add: snipd_face_def)
  next
    case False
    then show ?thesis using x face_in_diskN diskN_notr_E by (simp add: snipd_face_def)
  qed
qed

lemma snipd_cancel3: "snipd_node (snipd_face (snipd_edge x)) = x"
proof (cases "x \<in> diskN")
  case False
  show ?thesis by (simp only: snipd_edge_def snipd_face_def snipd_node_def if_not_P[OF False])
next
  case x: True
  have xD: "x \<in> D" using x diskN_D by blast
  have E: "snipd_edge x \<in> diskN" by (rule snipd_edge_cl[OF x])
  have FE: "snipd_face (snipd_edge x) \<in> diskN" by (rule snipd_face_cl[OF E])
  show ?thesis
  proof (cases "x \<in> set r")
    case True
    have nx: "next_in r x \<in> set r" by (rule next_in_mem[OF True])
    have "snipd_face (snipd_edge x) = f (e x)"
      using x True E nx prev_next_in[OF distinct_r True] by (simp add: snipd_edge_def snipd_face_def)
    then show ?thesis using FE by (simp add: snipd_node_def edgeK)
  next
    case False
    have ex: "e x \<in> diskE" using diskE_edge[OF xD] diskN_notr_E[OF x False] by blast
    have exr: "e x \<notin> set r" using ex by (simp add: diskE_def)
    have "snipd_face (snipd_edge x) = f (e x)"
      using x False ex exr diskE_inN by (simp add: snipd_edge_def snipd_face_def)
    then show ?thesis using FE by (simp add: snipd_node_def edgeK)
  qed
qed

lemma hypermap_snipd: "hypermap snipd"
proof -
  have "hypermap \<lparr>darts = diskN, edge = snipd_edge, node = snipd_node, face = snipd_face\<rparr>"
  proof (rule hypermap_cancel3)
    show "finite diskN" using diskN_D finite_darts by (rule finite_subset)
    fix x
    show "snipd_edge x \<in> diskN \<and> snipd_node x \<in> diskN \<and> snipd_face x \<in> diskN" if "x \<in> diskN"
      using snipd_edge_cl[OF that] snipd_node_cl[OF that] snipd_face_cl[OF that] by blast
    show "snipd_edge x = x \<and> snipd_node x = x \<and> snipd_face x = x" if "x \<notin> diskN"
      by (simp only: snipd_edge_def snipd_node_def snipd_face_def if_not_P[OF that] simp_thms)
    show "snipd_node (snipd_face (snipd_edge x)) = x" by (rule snipd_cancel3)
  qed
  then show ?thesis by (simp add: snipd_def)
qed

section \<open>The remainder map\<close>

abbreviation diskR :: "'a set" where "diskR \<equiv> D - diskE"

definition snipr_edge :: "'a \<Rightarrow> 'a" where
  "snipr_edge z = (if z \<in> diskR then e z else z)"

definition snipr_node :: "'a \<Rightarrow> 'a" where
  "snipr_node z = (if z \<in> diskR then (if z \<in> set r then prev_in r z else n z) else z)"

definition snipr_face :: "'a \<Rightarrow> 'a" where
  "snipr_face z = (if z \<in> diskR then (if n (f z) \<in> set r then next_in r (n (f z)) else f z) else z)"

definition snipr :: "'a hypermap" where
  "snipr = \<lparr>darts = diskR, edge = snipr_edge, node = snipr_node, face = snipr_face\<rparr>"

lemma snipr_simps [simp]:
  "darts snipr = diskR" "edge snipr = snipr_edge" "node snipr = snipr_node" "face snipr = snipr_face"
  by (simp_all add: snipr_def)

lemma r_diskR: "x \<in> set r \<Longrightarrow> x \<in> diskR" using r_D r_diskE by blast

lemma snipr_edge_cl: "z \<in> diskR \<Longrightarrow> snipr_edge z \<in> diskR"
  using diskE_edge by (auto simp: snipr_edge_def)

lemma snipr_node_cl: "z \<in> diskR \<Longrightarrow> snipr_node z \<in> diskR"
proof -
  assume z: "z \<in> diskR"
  then have zD: "z \<in> D" by blast
  show ?thesis
  proof (cases "z \<in> set r")
    case True
    then show ?thesis using z r_diskR[OF prev_in_mem[OF True]] by (simp add: snipr_node_def)
  next
    case False
    have "n z \<notin> diskE"
    proof
      assume "n z \<in> diskE"
      then have "z \<in> diskN" using diskN_node[OF zD] diskE_inN by blast
      then show False using z False diskN_notr_E by blast
    qed
    then show ?thesis using z False zD by (simp add: snipr_node_def)
  qed
qed

lemma snipr_face_cl: "z \<in> diskR \<Longrightarrow> snipr_face z \<in> diskR"
proof -
  assume z: "z \<in> diskR"
  then have zD: "z \<in> D" by blast
  show ?thesis
  proof (cases "n (f z) \<in> set r")
    case True
    then show ?thesis using z r_diskR[OF next_in_mem[OF True]] by (simp add: snipr_face_def)
  next
    case False
    have fzD: "f z \<in> D" using zD by simp
    have "f z \<notin> diskE"
    proof
      assume "f z \<in> diskE"
      then have "n (f z) \<in> diskN" using diskN_node[OF fzD] diskE_inN by blast
      then have "n (f z) \<in> diskE" using False diskN_notr_E by blast
      then have "e (n (f z)) \<in> diskE" using diskE_edge fzD by simp
      then show False using z by (simp add: faceK)
    qed
    then show ?thesis using z False fzD by (simp add: snipr_face_def)
  qed
qed

lemma snipr_cancel3: "snipr_node (snipr_face (snipr_edge z)) = z"
proof (cases "z \<in> diskR")
  case False
  then show ?thesis by (simp only: snipr_edge_def snipr_face_def snipr_node_def if_False)
next
  case z: True
  have zD: "z \<in> D" using z by blast
  have E: "snipr_edge z = e z" using z by (simp add: snipr_edge_def)
  have ER: "e z \<in> diskR" using snipr_edge_cl[OF z] E by simp
  show ?thesis
  proof (cases "z \<in> set r")
    case True
    have F: "snipr_face (e z) = next_in r z" using ER True by (simp add: snipr_face_def edgeK)
    have "next_in r z \<in> set r" by (rule next_in_mem[OF True])
    then show ?thesis using E F r_diskR prev_next_in[OF distinct_r True] by (simp add: snipr_node_def)
  next
    case False
    have fer: "f (e z) \<notin> set r"
    proof
      assume "f (e z) \<in> set r"
      then have "f (e z) \<in> diskN" by (rule r_diskN)
      moreover have "f (e z) \<in> D" using zD by simp
      ultimately have "z \<in> diskN" using diskN_node[of "f (e z)"] by (simp add: edgeK)
      then show False using z False diskN_notr_E by blast
    qed
    have F: "snipr_face (e z) = f (e z)" using ER False by (simp add: snipr_face_def edgeK)
    have FR: "f (e z) \<in> diskR" using snipr_face_cl[OF ER] F by simp
    show ?thesis using E F FR fer by (simp add: snipr_node_def edgeK)
  qed
qed

lemma hypermap_snipr: "hypermap snipr"
proof -
  have "hypermap \<lparr>darts = diskR, edge = snipr_edge, node = snipr_node, face = snipr_face\<rparr>"
  proof (rule hypermap_cancel3)
    show "finite diskR" using finite_darts by simp
    fix x
    show "snipr_edge x \<in> diskR \<and> snipr_node x \<in> diskR \<and> snipr_face x \<in> diskR" if "x \<in> diskR"
      using snipr_edge_cl[OF that] snipr_node_cl[OF that] snipr_face_cl[OF that] by blast
    show "snipr_edge x = x \<and> snipr_node x = x \<and> snipr_face x = x" if "x \<notin> diskR"
      by (simp only: snipr_edge_def snipr_node_def snipr_face_def if_not_P[OF that] simp_thms)
    show "snipr_node (snipr_face (snipr_edge x)) = x" by (rule snipr_cancel3)
  qed
  then show ?thesis by (simp add: snipr_def)
qed

section \<open>The snip patch\<close>

lemma snipd_face_cface: "x \<in> diskN \<Longrightarrow> cface x (snipd_face x)"
proof -
  assume x: "x \<in> diskN"
  show ?thesis
  proof (cases "x \<in> set r")
    case True
    have "cface (e (prev_in r x)) x" using rlink_prev[OF True] by (simp add: rlink_def)
    then have "cface x (f (e (prev_in r x)))" using F.fconnect_sym by simp
    then show ?thesis using x True by (simp add: snipd_face_def)
  next
    case False
    then show ?thesis using x by (simp add: snipd_face_def)
  qed
qed

lemma snipd_cface_hom:
  assumes "fconnect snipd_face x y"
  shows "cface x y"
proof -
  obtain k where y: "y = (snipd_face ^^ k) x" using assms by (auto simp: fconnect_def)
  have "cface x ((snipd_face ^^ k) x)"
  proof (induction k)
    case 0
    then show ?case by simp
  next
    case (Suc k)
    show ?case
    proof (cases "(snipd_face ^^ k) x \<in> diskN")
      case True
      then show ?thesis using fconnect_trans[OF Suc.IH snipd_face_cface[OF True]] by simp
    next
      case False
      then have "snipd_face ((snipd_face ^^ k) x) = (snipd_face ^^ k) x" by (simp add: snipd_face_def)
      then show ?thesis using Suc.IH by simp
    qed
  qed
  then show ?thesis using y by simp
qed

lemma snip_patch: "patch G snipd snipr id id r (rev r)"
proof -
  interpret Sd: hypermap snipd by (rule hypermap_snipd)
  interpret Sr: hypermap snipr by (rule hypermap_snipr)
  show ?thesis
  proof unfold_locales
    show "cycle (frel (edge snipd)) r"
      by (rule cycle_from_next[OF distinct_r]) (simp add: snipd_edge_def r_diskN)
    show "simple snipd r"
      unfolding simple_def distinct_map
    proof
      show "distinct r" by (rule distinct_r)
      show "inj_on (cyc (face snipd)) (set r)"
      proof (rule inj_onI)
        fix x y assume x: "x \<in> set r" and y: "y \<in> set r" and eq: "cyc (face snipd) x = cyc (face snipd) y"
        have "fconnect snipd_face x y" using eq Sd.F.cyc_eq_iff by simp
        then have "cface x y" by (rule snipd_cface_hom)
        then show "x = y" using r_cface x y by blast
      qed
    qed
    show "set r \<subseteq> darts snipd" using r_diskN by auto
    show "cycle (frel (node snipr)) (rev r)"
    proof (rule cycle_from_next)
      show "distinct (rev r)" using distinct_r by simp
      fix x assume "x \<in> set (rev r)"
      then have x: "x \<in> set r" by simp
      then show "node snipr x = next_in (rev r) x"
        using r_diskR[OF x] next_in_rev[OF distinct_r x] by (simp add: snipr_node_def)
    qed
    show "distinct (rev r)" using distinct_r by simp
    show "set (rev r) \<subseteq> darts snipr" using r_diskR by auto
    show "map id (rev r) = rev (map id r)" by simp
    show "id ` darts snipd \<subseteq> D" using diskN_D by simp
    show "id ` darts snipr = (D - id ` darts snipd) \<union> set (map id r)"
      using diskN_D r_D by (auto simp: diskE_def)
  qed (auto simp: snipd_edge_def snipd_node_def snipr_edge_def snipr_node_def)
qed

lemma planar_snipd: "planar snipd"
  using patch.planar_patch[OF snip_patch] planarG by simp

lemma planar_snipr: "planar snipr"
  using patch.planar_patch[OF snip_patch] planarG by simp

end

end
