(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Cfmap_ext.thy
    Configuration maps, part 2: the composite steps Y = N o U, H = N o Y (and K, A).
    Ported from G. Gonthier's Coq development (cfmap.v).
*)
theory Cfmap_ext
  imports Four_Colour_Maps.Cfmap
begin

section \<open>The Y step: N after U\<close>

locale ecp2 = ecp
begin

lemma XU_in: "X \<in> darts GU" by simp

sublocale T: ecp GU X
  by unfold_locales (simp add: XU_in)

abbreviation GY where "GY \<equiv> T.GN"
abbreviation XY where "XY \<equiv> T.X"

lemma long_GU: "long_cpring GU X"
  using U.size_long_cpring[of X] length_cpring_GU cpring_ne[of x0] by (cases "cpring G x0") simp_all

lemma cpring_GY: "cpring GY XY = Xe # XY # tl (cpring G x0)"
proof -
  have "cpring GY XY = node GU X # XY # drop 3 (cpring GU X)"
    by (rule T.cpring_GN_long[OF long_GU])
  also have "drop 3 (cpring GU X) = tl (cpring G x0)" by (simp add: cpring_GU drop_Suc)
  finally show ?thesis by simp
qed

lemma length_cpring_GY: "length (cpring GY XY) = Suc (length (cpring G x0))"
  using cpring_GY cpring_ne[of x0] by (cases "cpring G x0") simp_all

lemma darts_GY: "darts GY = D \<union> {X, Xe, XY, T.Xe}" by auto

lemma XY_neq [simp]: "XY \<noteq> X" "XY \<noteq> Xe" "T.Xe \<noteq> X" "T.Xe \<noteq> Xe"
  "X \<noteq> XY" "Xe \<noteq> XY" "X \<noteq> T.Xe" "Xe \<noteq> T.Xe"
  using T.X_notin T.Xe_notin by auto

lemma D_neq_XY [simp]: "y \<in> D \<Longrightarrow> y \<noteq> XY" "y \<in> D \<Longrightarrow> y \<noteq> T.Xe"
  using T.X_notin T.Xe_notin by auto

lemma plain_GY: "plain G \<Longrightarrow> plain GY"
  by (intro T.plain_GN plain_GU)

lemma quasicubic_GY: "quasicubic G (rev (cpring G x0)) \<Longrightarrow> quasicubic GY (rev (cpring GY XY))"
  using T.quasicubic_GN[OF quasicubic_GU] long_GU U.size_long_cpring U.size_proper_cpring
  by simp

lemma connected_GY: "connected G \<Longrightarrow> connected GY"
  by (intro T.connected_GN connected_GU)

lemma planar_GY:
  assumes "planar G" "plain G" "quasicubic G (rev (cpring G x0))" "connected G"
  shows "planar GY"
proof -
  have pr: "proper_cpring GU X" using long_GU U.size_long_cpring U.size_proper_cpring by simp
  show ?thesis
    using T.planar_GN[OF planar_GU[OF assms] plain_GU[OF assms(2)] quasicubic_GU[OF assms(3)]
        connected_GU[OF assms(4)] pr] .
qed

lemma cface_GY_old:
  assumes "x \<in> D" "y \<in> D"
  shows "fconnect (face GY) x y \<longleftrightarrow> cface x y"
  using T.cface_GN_old[of x y] cface_GU_old[OF assms] assms by simp

lemma adj_GY_old:
  assumes x: "x \<in> D" and y: "y \<in> D"
  shows "adj GY x y \<longleftrightarrow> adj G x y"
proof -
  have xX: "\<not> fconnect (face GU) X x" "\<not> fconnect (face GU) X y" using cface_GU_X x y by auto
  have "adj GY x y \<longleftrightarrow> adj GU x y" using T.adj_GN_old[of x y] x y xX by auto
  then show ?thesis using adj_GU_old[OF x y] by simp
qed

lemma face_GY_X: "face GY XY = X" "face GY X = XY"
proof -
  show "face GY XY = X" by simp
  have "X = edge GU (node GU X)" by simp
  then show "face GY X = XY" by (simp del: GU_simps) (simp add: T.GN_simps)
qed

lemma cface_node_GY: "fconnect (face GY) (node GY XY) (n x0)"
proof -
  have "node GY XY = Xe" using long_GU by simp
  moreover have "fconnect (face GY) Xe (n x0)"
    using T.cface_GN_old[of Xe "n x0"] cface_GU_Xe x0D by simp
  ultimately show ?thesis by simp
qed

lemma cface_GY_XY: "fconnect (face GY) XY u \<longleftrightarrow> u = XY \<or> u = X"
proof
  assume "fconnect (face GY) XY u"
  then show "u = XY \<or> u = X"
    by (induction rule: fconnect_induct) (auto simp: face_GY_X)
next
  assume "u = XY \<or> u = X"
  then show "fconnect (face GY) XY u"
    using fconnect_step[of "face GY" XY] by (auto simp: face_GY_X)
qed

lemma cface_GY_TXe: "fconnect (face GY) T.Xe x0"
proof -
  have a: "fconnect (face GY) T.Xe (e (n x0))"
    using T.cface_GN_Xe by simp
  have "fconnect (face GY) (e (n x0)) x0"
    using T.cface_GN_old[of "e (n x0)" x0] fconnect_step[of f "e (n x0)"] cface_GU_old[of "e (n x0)" x0]
      x0D by (simp add: nodeK)
  then show ?thesis by (rule fconnect_trans[OF a])
qed

lemma adj_GY_XY: "adj GY XY u \<longleftrightarrow> fband GY [n x0, x0] u"
proof -
  have nXY: "edge GY XY = T.Xe" "edge GY X = Xe" by simp_all
  have cXe: "fconnect (face GY) Xe (n x0)" using cface_node_GY long_GU by simp
  have "adj GY XY u \<longleftrightarrow> (\<exists>z. (z = XY \<or> z = X) \<and> fconnect (face GY) (edge GY z) u)"
    unfolding adj_def rlink_def cface_GY_XY ..
  also have "\<dots> \<longleftrightarrow> fconnect (face GY) (edge GY XY) u \<or> fconnect (face GY) (edge GY X) u" by blast
  also have "\<dots> \<longleftrightarrow> fconnect (face GY) T.Xe u \<or> fconnect (face GY) Xe u" by (simp only: nXY)
  also have "\<dots> \<longleftrightarrow> fconnect (face GY) x0 u \<or> fconnect (face GY) (n x0) u"
  proof -
    have "fconnect (face GY) T.Xe u \<longleftrightarrow> fconnect (face GY) x0 u"
      using fconnect_trans[OF cface_GY_TXe] fconnect_trans[OF T.NN.F.fconnect_sym[OF cface_GY_TXe]] by blast
    moreover have "fconnect (face GY) Xe u \<longleftrightarrow> fconnect (face GY) (n x0) u"
      using fconnect_trans[OF cXe] fconnect_trans[OF T.NN.F.fconnect_sym[OF cXe]] by blast
    ultimately show ?thesis by blast
  qed
  finally show ?thesis
    unfolding fband_def using T.NN.F.fconnect_commute by auto
qed

lemma fband_GY: "u \<in> darts GY \<Longrightarrow> (\<exists>x \<in> D. fconnect (face GY) u x) \<or> fconnect (face GY) XY u"
proof -
  assume u: "u \<in> darts GY"
  have cXe: "fconnect (face GY) Xe (n x0)" using cface_node_GY long_GU by simp
  consider "u \<in> D" | "u = X" | "u = Xe" | "u = XY" | "u = T.Xe" using u darts_GY by blast
  then show ?thesis
  proof cases
    case 1 then show ?thesis by blast
  next
    case 2 then show ?thesis using cface_GY_XY by simp
  next
    case 3 then show ?thesis using cXe x0D by auto
  next
    case 4 then show ?thesis using cface_GY_XY by simp
  next
    case 5 then show ?thesis using cface_GY_TXe x0D by auto
  qed
qed

lemma bridgeless_GY:
  assumes b: "bridgeless G"
  shows "bridgeless GY"
  unfolding bridgeless_def
proof
  fix x assume x: "x \<in> darts GY"
  consider "x \<in> D" | "x = X" | "x = Xe" | "x = XY" | "x = T.Xe" using x darts_GY by blast
  then show "\<not> fconnect (face GY) x (edge GY x)"
  proof cases
    case 1
    then show ?thesis using b cface_GY_old[of x "e x"] by (simp add: bridgeless_def)
  next
    case 2
    have "\<not> fconnect (face GY) X Xe"
    proof
      assume "fconnect (face GY) X Xe"
      then have "fconnect (face GY) XY Xe"
        by (rule fconnect_trans[OF fconnect_step[of "face GY" XY, unfolded face_GY_X(1)]])
      then show False using cface_GY_XY by simp
    qed
    then show ?thesis using 2 by simp
  next
    case 3
    have "\<not> fconnect (face GY) Xe X"
    proof
      assume "fconnect (face GY) Xe X"
      then have "fconnect (face GY) X Xe" by (rule T.NN.F.fconnect_sym)
      then have "fconnect (face GY) XY Xe"
        by (rule fconnect_trans[OF fconnect_step[of "face GY" XY, unfolded face_GY_X(1)]])
      then show False using cface_GY_XY by simp
    qed
    then show ?thesis using 3 by simp
  next
    case 4 then show ?thesis using cface_GY_XY by simp
  next
    case 5
    have "\<not> fconnect (face GY) T.Xe XY"
      using T.NN.F.fconnect_sym cface_GY_XY by force
    then show ?thesis using 5 by simp
  qed
qed

lemma node_GY_old: "x \<in> D \<Longrightarrow> x \<noteq> n x0 \<Longrightarrow> x \<noteq> x0 \<Longrightarrow> node GY x = n x"
  by simp

lemma face_GY_old: "x \<in> D \<Longrightarrow> edge GY x = e x"
  by simp

end


section \<open>The H step: N after Y\<close>

locale ecp2h = ecp2
begin

lemma XY_in: "XY \<in> darts GY" by simp

sublocale T2: ecp GY XY
  by unfold_locales (simp add: XY_in)

abbreviation GH where "GH \<equiv> T2.GN"
abbreviation XH where "XH \<equiv> T2.X"

lemma node_GY_XY: "node GY XY = Xe" using long_GU by simp

lemma darts_GH: "darts GH = D \<union> {X, Xe, XY, T.Xe, XH, T2.Xe}" by auto

lemma XH_neq [simp]: "XH \<noteq> X" "XH \<noteq> Xe" "XH \<noteq> XY" "XH \<noteq> T.Xe"
  "T2.Xe \<noteq> X" "T2.Xe \<noteq> Xe" "T2.Xe \<noteq> XY" "T2.Xe \<noteq> T.Xe"
  "X \<noteq> XH" "Xe \<noteq> XH" "XY \<noteq> XH" "T.Xe \<noteq> XH"
  "X \<noteq> T2.Xe" "Xe \<noteq> T2.Xe" "XY \<noteq> T2.Xe" "T.Xe \<noteq> T2.Xe"
  using T2.X_notin T2.Xe_notin by auto

lemma D_neq_XH [simp]: "y \<in> D \<Longrightarrow> y \<noteq> XH" "y \<in> D \<Longrightarrow> y \<noteq> T2.Xe"
  using T2.X_notin T2.Xe_notin by auto

lemma plain_GH: "plain G \<Longrightarrow> plain GH"
  by (intro T2.plain_GN plain_GY)

lemma connected_GH: "connected G \<Longrightarrow> connected GH"
  by (intro T2.connected_GN connected_GY)

lemma cface_GH_old:
  assumes "x \<in> D" "y \<in> D"
  shows "fconnect (face GH) x y \<longleftrightarrow> cface x y"
  using T2.cface_GN_old[of x y] cface_GY_old[OF assms] assms by simp

lemma adj_GH_old:
  assumes x: "x \<in> D" and y: "y \<in> D"
  shows "adj GH x y \<longleftrightarrow> adj G x y"
proof -
  have xX: "\<not> fconnect (face GY) XY x" "\<not> fconnect (face GY) XY y" using cface_GY_XY x y by auto
  have "adj GH x y \<longleftrightarrow> adj GY x y" using T2.adj_GN_old[of x y] x y xX by auto
  then show ?thesis using adj_GY_old[OF x y] by simp
qed

lemma node_GH_old:
  assumes "x \<in> D" "x \<noteq> n x0" "x \<noteq> x0" "x \<noteq> f (e x0)"
  shows "node GH x = n x"
proof -
  have nx: "n x \<noteq> x0" using assms(4) by (metis nodeK)
  have a: "node GY x = n x" using assms by (intro node_GY_old)
  have nxD: "n x \<in> D" using assms(1) by simp
  have "n x \<noteq> n x0" using assms(3) by simp
  then have b: "node GY (n x) = n (n x)" using nxD nx by (intro node_GY_old)
  have c: "node GY (node GY x) \<noteq> XY" using a b assms(1) by simp
  have d: "x \<noteq> XH" "x \<noteq> T2.Xe" "x \<noteq> XY" using assms(1) by simp_all
  have "node GH x = node GY x"
    by (simp only: T2.GN_simps d c if_False)
  then show ?thesis using a by simp
qed


end

locale ecp3 = ecp2h +
  assumes prop0: "proper_cpring G x0"
begin

lemma x0_ne_n: "x0 \<noteq> n x0" using prop0 by (simp add: proper_cpring_def)

lemma long_GY: "long_cpring GY XY"
  using T.NN.size_long_cpring[of XY] length_cpring_GY prop0 size_proper_cpring by simp

lemma cpring_GH: "cpring GH XH = Xe # XH # drop 2 (cpring G x0)"
proof -
  have "cpring GH XH = node GY XY # XH # drop 3 (cpring GY XY)"
    by (rule T2.cpring_GN_long[OF long_GY])
  also have "drop 3 (cpring GY XY) = drop 2 (cpring G x0)"
    by (simp add: cpring_GY drop_Suc drop_tl numeral_3_eq_3 numeral_2_eq_2)
  finally show ?thesis using node_GY_XY by simp
qed

lemma length_cpring_GH: "length (cpring GH XH) = length (cpring G x0)"
  using cpring_GH prop0 size_proper_cpring by simp

lemma proper_GY: "proper_cpring GY XY"
  using long_GY T.NN.size_long_cpring T.NN.size_proper_cpring by simp

lemma quasicubic_GH: "quasicubic G (rev (cpring G x0)) \<Longrightarrow> quasicubic GH (rev (cpring GH XH))"
  using T2.quasicubic_GN[OF quasicubic_GY proper_GY] by simp

lemma planar_GH:
  assumes "planar G" "plain G" "quasicubic G (rev (cpring G x0))" "connected G"
  shows "planar GH"
  using T2.planar_GN[OF planar_GY[OF assms] plain_GY[OF assms(2)] quasicubic_GY[OF assms(3)]
      connected_GY[OF assms(4)] proper_GY] .

lemma fY_TXe: "face GY T.Xe = x0"
proof -
  have "f (e (n x0)) = x0" by (simp add: nodeK)
  then show ?thesis using x0_ne_n long_GU by (simp add: T.GN_simps)
qed

lemma face_GH_cycle: "face GH XH = XY" "face GH XY = X" "face GH X = XH"
proof -
  show "face GH XH = XY" by simp
  have a: "edge GY XY = T.Xe" "node GY XY = Xe" "edge GY Xe = X" using long_GU by simp_all
  have b: "edge GY (face GY (edge GY XY)) = e x0" using fY_TXe x0D by simp
  show "face GH XY = X"
  proof -
    have "XY \<noteq> edge GY (face GY (edge GY XY))" using b x0D by simp
    moreover have "XY \<noteq> edge GY (node GY XY)" using a by simp
    ultimately show ?thesis by (simp only: T2.GN_simps) (simp add: face_GY_X)
  qed
  show "face GH X = XH"
  proof -
    have "X \<noteq> edge GY (face GY (edge GY XY))" using b x0D by simp
    moreover have "X = edge GY (node GY XY)" using a by simp
    ultimately show ?thesis by (simp only: T2.GN_simps) simp
  qed
qed

lemma cface_GH_XH: "fconnect (face GH) XH u \<longleftrightarrow> u = XH \<or> u = XY \<or> u = X"
proof
  assume "fconnect (face GH) XH u"
  then show "u = XH \<or> u = XY \<or> u = X"
  proof (induction rule: fconnect_induct)
    case (step z)
    then consider "z = XH" | "z = XY" | "z = X" by blast
    then show ?case by cases (simp_all only: face_GH_cycle simp_thms)
  qed simp
next
  have s1: "fconnect (face GH) XH XY" using fconnect_step[of "face GH" XH, unfolded face_GH_cycle(1)] .
  have s2: "fconnect (face GH) XY X" using fconnect_step[of "face GH" XY, unfolded face_GH_cycle(2)] .
  assume "u = XH \<or> u = XY \<or> u = X"
  then consider "u = XH" | "u = XY" | "u = X" by blast
  then show "fconnect (face GH) XH u"
  proof cases
    case 1 then show ?thesis by (simp only: fconnect_refl)
  next
    case 2 then show ?thesis using s1 by (simp only:)
  next
    case 3 then show ?thesis using fconnect_trans[OF s1 s2] by (simp only:)
  qed
qed

lemma cface_node_GH: "fconnect (face GH) (node GH XH) (n x0)"
proof -
  have "node GH XH = Xe" using long_GY node_GY_XY by simp
  moreover have "fconnect (face GH) Xe (n x0)"
    using T2.cface_GN_old[of Xe "n x0"] cface_node_GY node_GY_XY x0D by simp
  ultimately show ?thesis by simp
qed

lemma cface_GH_TXe: "fconnect (face GH) T.Xe x0"
  using T2.cface_GN_old[of "T.Xe" x0] cface_GY_TXe x0D by simp

lemma cface_GH_T2Xe: "fconnect (face GH) T2.Xe (f (e x0))"
proof -
  have b: "edge GY (face GY (edge GY XY)) = e x0" using fY_TXe x0D by simp
  have a: "fconnect (face GH) T2.Xe (e x0)" using T2.cface_GN_Xe b by simp
  have "fconnect (face GY) (e x0) (f (e x0))"
    using cface_GY_old[of "e x0" "f (e x0)"] x0D fconnect_step[of f "e x0"] by simp
  then have "fconnect (face GH) (e x0) (f (e x0))" using T2.cface_GN_old[of "e x0" "f (e x0)"] x0D by simp
  then show ?thesis by (rule fconnect_trans[OF a])
qed

lemma adj_GH_XH: "adj GH XH u \<longleftrightarrow> fband GH [n x0, x0, f (e x0)] u"
proof -
  have nX: "edge GH XH = T2.Xe" "edge GH XY = T.Xe" "edge GH X = Xe" by simp_all
  have cXe: "fconnect (face GH) Xe (n x0)" using cface_node_GH long_GY node_GY_XY by simp
  have tr: "fconnect (face GH) a b \<Longrightarrow> fconnect (face GH) a u \<longleftrightarrow> fconnect (face GH) b u" for a b
    using fconnect_trans T2.NN.F.fconnect_sym by metis
  have "adj GH XH u \<longleftrightarrow> (\<exists>z. (z = XH \<or> z = XY \<or> z = X) \<and> fconnect (face GH) (edge GH z) u)"
    unfolding adj_def rlink_def cface_GH_XH ..
  also have "\<dots> \<longleftrightarrow> fconnect (face GH) (edge GH XH) u \<or> fconnect (face GH) (edge GH XY) u
                     \<or> fconnect (face GH) (edge GH X) u" by blast
  also have "\<dots> \<longleftrightarrow> fconnect (face GH) T2.Xe u \<or> fconnect (face GH) T.Xe u \<or> fconnect (face GH) Xe u"
    by (simp only: nX)
  also have "\<dots> \<longleftrightarrow> fconnect (face GH) (f (e x0)) u \<or> fconnect (face GH) x0 u \<or> fconnect (face GH) (n x0) u"
    using tr[OF cface_GH_T2Xe] tr[OF cface_GH_TXe] tr[OF cXe] by blast
  finally show ?thesis unfolding fband_def using T2.NN.F.fconnect_commute by auto
qed

lemma fband_GH: "u \<in> darts GH \<Longrightarrow> (\<exists>x \<in> D. fconnect (face GH) u x) \<or> fconnect (face GH) XH u"
proof -
  assume u: "u \<in> darts GH"
  have cXe: "fconnect (face GH) Xe (n x0)" using cface_node_GH long_GY node_GY_XY by simp
  consider "u \<in> D" | "u = X" | "u = Xe" | "u = XY" | "u = T.Xe" | "u = XH" | "u = T2.Xe"
    using u darts_GH by blast
  then show ?thesis
  proof cases
    case 1 then show ?thesis by blast
  next
    case 2 then show ?thesis using cface_GH_XH by simp
  next
    case 3 then show ?thesis using cXe x0D by auto
  next
    case 4 then show ?thesis using cface_GH_XH by simp
  next
    case 5 then show ?thesis using cface_GH_TXe x0D by auto
  next
    case 6 then show ?thesis using cface_GH_XH by simp
  next
    case 7 then show ?thesis using cface_GH_T2Xe x0D by (metis efe_D(3))
  qed
qed

lemma bridgeless_GH:
  assumes b: "bridgeless G"
  shows "bridgeless GH"
  unfolding bridgeless_def
proof
  fix x assume x: "x \<in> darts GH"
  have inF: "fconnect (face GH) a c \<Longrightarrow> a \<in> {XH, XY, X} \<Longrightarrow> c \<in> {XH, XY, X}" for a c
  proof -
    assume ac: "fconnect (face GH) a c" and a: "a \<in> {XH, XY, X}"
    have "fconnect (face GH) XH a" using a unfolding cface_GH_XH by blast
    then have "fconnect (face GH) XH c" by (rule fconnect_trans[OF _ ac])
    then show ?thesis unfolding cface_GH_XH by blast
  qed
  consider "x \<in> D" | "x \<in> {XH, XY, X}" | "x \<in> {T2.Xe, T.Xe, Xe}" using x darts_GH by blast
  then show "\<not> fconnect (face GH) x (edge GH x)"
  proof cases
    case 1
    then show ?thesis using b cface_GH_old[of x "e x"] by (simp add: bridgeless_def)
  next
    case 2
    then have "edge GH x \<notin> {XH, XY, X}" by auto
    then show ?thesis using inF 2 by blast
  next
    case 3
    then have ex: "edge GH x \<in> {XH, XY, X}" by auto
    show ?thesis
    proof
      assume "fconnect (face GH) x (edge GH x)"
      then have "fconnect (face GH) (edge GH x) x" by (rule T2.NN.F.fconnect_sym)
      then have "x \<in> {XH, XY, X}" using inF ex by blast
      then show False using 3 by auto
    qed
  qed
qed

end

end
