(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Cube.thy
    Reduction of the colouring problem to plain cubic maps.
    Ported from G. Gonthier's Coq development (cube.v).
*)
theory Cube
  imports Coloring
begin

datatype cube_tag = CTn | CTen | CTf | CTnf | CTe | CTfe

lemma UNIV_cube_tag: "UNIV = {CTn, CTen, CTf, CTnf, CTe, CTfe}"
  by (auto intro: cube_tag.exhaust)

instance cube_tag :: finite
  by standard (simp add: UNIV_cube_tag)

definition cube_edge :: "'a hypermap \<Rightarrow> cube_tag \<times> 'a \<Rightarrow> cube_tag \<times> 'a" where
  "cube_edge G u = (case u of (t, x) \<Rightarrow> if x \<notin> darts G then u else (case t of
       CTen \<Rightarrow> (CTnf, edge G x) | CTf \<Rightarrow> (CTe, node G (face G x))
     | CTnf \<Rightarrow> (CTen, node G (face G x)) | CTe \<Rightarrow> (CTf, edge G x)
     | CTfe \<Rightarrow> (CTn, x) | CTn \<Rightarrow> (CTfe, x)))"

definition cube_node :: "'a hypermap \<Rightarrow> cube_tag \<times> 'a \<Rightarrow> cube_tag \<times> 'a" where
  "cube_node G u = (case u of (t, x) \<Rightarrow> if x \<notin> darts G then u else (case t of
       CTn \<Rightarrow> (CTen, node G x) | CTen \<Rightarrow> (CTfe, x)
     | CTf \<Rightarrow> (CTnf, edge G x) | CTnf \<Rightarrow> (CTe, node G (face G x))
     | CTe \<Rightarrow> (CTf, x) | CTfe \<Rightarrow> (CTn, face G (edge G x))))"

definition cube_face :: "'a hypermap \<Rightarrow> cube_tag \<times> 'a \<Rightarrow> cube_tag \<times> 'a" where
  "cube_face G u = (case u of (t, x) \<Rightarrow> if x \<notin> darts G then u else (case t of
       CTn \<Rightarrow> (CTen, x) | CTen \<Rightarrow> (CTf, x) | CTf \<Rightarrow> (CTnf, x)
     | CTnf \<Rightarrow> (CTn, face G x) | CTe \<Rightarrow> (CTe, edge G x) | CTfe \<Rightarrow> (CTfe, node G x)))"

definition cube :: "'a hypermap \<Rightarrow> (cube_tag \<times> 'a) hypermap" where
  "cube G = \<lparr>darts = UNIV \<times> darts G, edge = cube_edge G, node = cube_node G,
             face = cube_face G\<rparr>"

lemma cube_simps [simp]:
  "darts (cube G) = UNIV \<times> darts G" "edge (cube G) = cube_edge G"
  "node (cube G) = cube_node G" "face (cube G) = cube_face G"
  by (simp_all add: cube_def)

lemma perm_of_inj:
  assumes "finite S" "\<And>x. x \<in> S \<Longrightarrow> g x \<in> S" "inj_on g S" "\<And>x. x \<notin> S \<Longrightarrow> g x = x"
  shows "g permutes S"
proof -
  have sub: "g ` S \<subseteq> S" using assms(2) by blast
  have "g ` S = S" by (rule endo_inj_surj[OF assms(1) sub assms(3)])
  then have "bij_betw g S S" using assms(3) by (simp add: bij_betw_def)
  then show ?thesis by (rule bij_imp_permutes) (rule assms(4))
qed

context hypermap
begin

lemma cube_edgeK: "cube_node G (cube_face G (cube_edge G u)) = u"
  by (cases u; rename_tac t x; case_tac t)
     (auto simp: cube_edge_def cube_node_def cube_face_def edgeK faceK nodeK)

lemma cube_edge_D: "u \<in> UNIV \<times> D \<Longrightarrow> cube_edge G u \<in> UNIV \<times> D"
  and cube_node_D: "u \<in> UNIV \<times> D \<Longrightarrow> cube_node G u \<in> UNIV \<times> D"
  and cube_face_D: "u \<in> UNIV \<times> D \<Longrightarrow> cube_face G u \<in> UNIV \<times> D"
  by (cases u; rename_tac t x; case_tac t; simp add: cube_edge_def cube_node_def cube_face_def)+

lemma cube_out: "u \<notin> UNIV \<times> D \<Longrightarrow> cube_edge G u = u \<and> cube_node G u = u \<and> cube_face G u = u"
  by (cases u) (simp add: cube_edge_def cube_node_def cube_face_def)

lemma hypermap_cube: "hypermap (cube G)"
proof -
  have fin: "finite (UNIV \<times> D :: (cube_tag \<times> 'a) set)" using finite_darts by simp
  have injE: "inj_on (cube_edge G) (UNIV \<times> D)"
    by (rule inj_onI) (auto simp: cube_edge_def split: cube_tag.splits)
  have injN: "inj_on (cube_node G) (UNIV \<times> D)"
    by (rule inj_onI) (auto simp: cube_node_def split: cube_tag.splits)
  have injF: "inj_on (cube_face G) (UNIV \<times> D)"
    by (rule inj_onI) (auto simp: cube_face_def split: cube_tag.splits)
  show ?thesis
  proof unfold_locales
    show "finite (darts (cube G))" using fin by simp
    show "edge (cube G) permutes darts (cube G)"
      using perm_of_inj[OF fin cube_edge_D injE] cube_out by simp
    show "node (cube G) permutes darts (cube G)"
      using perm_of_inj[OF fin cube_node_D injN] cube_out by simp
    show "face (cube G) permutes darts (cube G)"
      using perm_of_inj[OF fin cube_face_D injF] cube_out by simp
    fix u show "node (cube G) (face (cube G) (edge (cube G) u)) = u" by (simp add: cube_edgeK)
  qed
qed

lemma plain_cube: "plain (cube G)"
proof -
  interpret Q: hypermap "cube G" by (rule hypermap_cube)
  show ?thesis unfolding plain_def Q.plainP
    by (auto simp: cube_edge_def faceK edgeK split: cube_tag.splits)
qed

lemma cubic_cube: "cubic (cube G)"
proof -
  interpret Q: hypermap "cube G" by (rule hypermap_cube)
  show ?thesis unfolding cubic_def Q.cubicP
    by (auto simp: cube_node_def edgeK faceK nodeK split: cube_tag.splits)
qed

lemma cube_colorable: "four_colorable (cube G) \<Longrightarrow> four_colorable G"
proof -
  interpret Q: hypermap "cube G" by (rule hypermap_cube)
  assume "four_colorable (cube G)"
  then obtain k where k: "coloring (cube G) k" by (auto simp: four_colorable_def)
  have kE: "\<forall>u \<in> UNIV \<times> D. k (cube_edge G u) \<noteq> k u"
    and kF: "\<forall>u \<in> UNIV \<times> D. k (cube_face G u) = k u" using k by (auto simp: coloring_def)
  define k' where "k' x = k (CTnf, x)" for x
  have "coloring G k'"
    unfolding coloring_def
  proof (intro conjI ballI)
    fix x assume xD: "x \<in> D"
    have kF': "k (cube_face G (t, y)) = k (t, y)" if "y \<in> D" for t y using kF that by blast
    have a: "k (CTn, f x) = k (CTnf, x)" using kF'[OF xD, of CTnf] xD by (simp add: cube_face_def)
    have b1: "k (CTen, y) = k (CTn, y)" if "y \<in> D" for y
      using kF'[OF that, of CTn] that by (simp add: cube_face_def)
    have b2: "k (CTf, y) = k (CTen, y)" if "y \<in> D" for y
      using kF'[OF that, of CTen] that by (simp add: cube_face_def)
    have b3: "k (CTnf, y) = k (CTf, y)" if "y \<in> D" for y
      using kF'[OF that, of CTf] that by (simp add: cube_face_def)
    show "k' (f x) = k' x"
      using a b1 b2 b3 xD unfolding k'_def by simp
    have "k (cube_edge G (CTen, x)) \<noteq> k (CTen, x)" using kE xD by blast
    then have e: "k (CTnf, e x) \<noteq> k (CTen, x)" using xD by (simp add: cube_edge_def)
    show "k' (e x) \<noteq> k' x"
      using e b1 b2 b3 xD unfolding k'_def by simp
  qed
  then show ?thesis by (auto simp: four_colorable_def)
qed

subsection \<open>Faces of the cube\<close>

definition T4 :: "cube_tag set" where "T4 = {CTn, CTen, CTf, CTnf}"

fun t4 :: "nat \<Rightarrow> cube_tag" where
  "t4 j = (if j = 0 then CTn else if j = 1 then CTen else if j = 2 then CTf else CTnf)"

declare t4.simps [simp del]

lemma cube_face_pow_e: "x \<in> D \<Longrightarrow> (cube_face G ^^ k) (CTe, x) = (CTe, (e ^^ k) x)"
  by (induction k) (simp_all add: cube_face_def)

lemma cube_face_pow_n: "x \<in> D \<Longrightarrow> (cube_face G ^^ k) (CTfe, x) = (CTfe, (n ^^ k) x)"
  by (induction k) (simp_all add: cube_face_def)

lemma cube_face_pow_f:
  "x \<in> D \<Longrightarrow> (cube_face G ^^ m) (CTn, x) = (t4 (m mod 4), (f ^^ (m div 4)) x)"
proof (induction m)
  case 0
  then show ?case by (simp add: t4.simps)
next
  case (Suc m)
  have fD: "(f ^^ (m div 4)) x \<in> D" using Suc.prems by simp
  consider "m mod 4 = 0" | "m mod 4 = 1" | "m mod 4 = 2" | "m mod 4 = 3" by linarith
  then show ?case
  proof cases
    case 1
    then have "Suc m mod 4 = 1" "Suc m div 4 = m div 4" by presburger+
    then show ?thesis using Suc 1 fD by (simp add: cube_face_def t4.simps)
  next
    case 2
    then have "Suc m mod 4 = 2" "Suc m div 4 = m div 4" by presburger+
    then show ?thesis using Suc 2 fD by (simp add: cube_face_def t4.simps)
  next
    case 3
    then have "Suc m mod 4 = 3" "Suc m div 4 = m div 4" by presburger+
    then show ?thesis using Suc 3 fD by (simp add: cube_face_def t4.simps)
  next
    case 4
    then have "Suc m mod 4 = 0" "Suc m div 4 = Suc (m div 4)" by presburger+
    then show ?thesis using Suc 4 fD by (simp add: cube_face_def t4.simps)
  qed
qed

lemma t4_T4: "t4 j \<in> T4"
  by (simp add: T4_def t4.simps)

lemma t4_onto: "t \<in> T4 \<Longrightarrow> \<exists>j < 4. t4 j = t"
proof -
  assume "t \<in> T4"
  then consider "t = CTn" | "t = CTen" | "t = CTf" | "t = CTnf" by (auto simp: T4_def)
  then show ?thesis
  proof cases
    case 1 then show ?thesis by (intro exI[of _ 0]) (simp add: t4.simps)
  next
    case 2 then show ?thesis by (intro exI[of _ 1]) (simp add: t4.simps)
  next
    case 3 then show ?thesis by (intro exI[of _ 2]) (simp add: t4.simps)
  next
    case 4 then show ?thesis by (intro exI[of _ 3]) (simp add: t4.simps)
  qed
qed

lemma cyc_cube_e: "x \<in> D \<Longrightarrow> cyc (cube_face G) (CTe, x) = {CTe} \<times> cyc e x"
  by (auto simp: cyc_def fconnect_def cube_face_pow_e)

lemma cyc_cube_n: "x \<in> D \<Longrightarrow> cyc (cube_face G) (CTfe, x) = {CTfe} \<times> cyc n x"
  by (auto simp: cyc_def fconnect_def cube_face_pow_n)

lemma cyc_cube_f: "x \<in> D \<Longrightarrow> cyc (cube_face G) (CTn, x) = T4 \<times> cyc f x"
proof
  assume xD: "x \<in> D"
  show "cyc (cube_face G) (CTn, x) \<subseteq> T4 \<times> cyc f x"
    using xD t4_T4 by (auto simp: cyc_def fconnect_def cube_face_pow_f)
  show "T4 \<times> cyc f x \<subseteq> cyc (cube_face G) (CTn, x)"
  proof
    fix u assume "u \<in> T4 \<times> cyc f x"
    then obtain t k where u: "u = (t, (f ^^ k) x)" "t \<in> T4" by (auto simp: cyc_def fconnect_def)
    obtain j where j: "j < 4" "t4 j = t" using t4_onto[OF u(2)] by blast
    have "(cube_face G ^^ (4 * k + j)) (CTn, x) = u"
      using cube_face_pow_f[OF xD, of "4 * k + j"] j u by simp
    then show "u \<in> cyc (cube_face G) (CTn, x)" unfolding cyc_def fconnect_def by blast
  qed
qed

lemma cyc_cube_f': "x \<in> D \<Longrightarrow> t \<in> T4 \<Longrightarrow> cyc (cube_face G) (t, x) = T4 \<times> cyc f x"
proof -
  assume xD: "x \<in> D" and t: "t \<in> T4"
  interpret Q: hypermap "cube G" by (rule hypermap_cube)
  have "(t, x) \<in> cyc (cube_face G) (CTn, x)" using cyc_cube_f[OF xD] t by simp
  then have "cyc (cube_face G) (CTn, x) = cyc (cube_face G) (t, x)"
    using Q.F.cyc_eq Q.F.in_cyc_iff by simp
  then show ?thesis using cyc_cube_f[OF xD] by simp
qed

lemma fcard_cube_face: "fcard (cube_face G) (UNIV \<times> D) = fcard e D + fcard n D + fcard f D"
proof -
  let ?q = "cyc (cube_face G)"
  have split: "UNIV \<times> D = ({CTe} \<times> D) \<union> ({CTfe} \<times> D) \<union> (T4 \<times> D)"
    using UNIV_cube_tag by (auto simp: T4_def)
  have iE: "?q ` ({CTe} \<times> D) = (\<lambda>C. {CTe} \<times> C) ` (cyc e ` D)"
  proof -
    have "?q ` ({CTe} \<times> D) = (\<lambda>x. ?q (CTe, x)) ` D" by auto
    also have "\<dots> = (\<lambda>x. {CTe} \<times> cyc e x) ` D" using cyc_cube_e by (intro image_cong) simp_all
    also have "\<dots> = (\<lambda>C. {CTe} \<times> C) ` (cyc e ` D)" by (simp add: image_image)
    finally show ?thesis .
  qed
  have iN: "?q ` ({CTfe} \<times> D) = (\<lambda>C. {CTfe} \<times> C) ` (cyc n ` D)"
  proof -
    have "?q ` ({CTfe} \<times> D) = (\<lambda>x. ?q (CTfe, x)) ` D" by auto
    also have "\<dots> = (\<lambda>x. {CTfe} \<times> cyc n x) ` D" using cyc_cube_n by (intro image_cong) simp_all
    also have "\<dots> = (\<lambda>C. {CTfe} \<times> C) ` (cyc n ` D)" by (simp add: image_image)
    finally show ?thesis .
  qed
  have iF: "?q ` (T4 \<times> D) = (\<lambda>C. T4 \<times> C) ` (cyc f ` D)"
  proof
    show "?q ` (T4 \<times> D) \<subseteq> (\<lambda>C. T4 \<times> C) ` (cyc f ` D)"
    proof
    fix S assume "S \<in> ?q ` (T4 \<times> D)"
    then obtain t x where "t \<in> T4" "x \<in> D" "S = ?q (t, x)" by blast
    then have "S = T4 \<times> cyc f x" using cyc_cube_f' by simp
    then show "S \<in> (\<lambda>C. T4 \<times> C) ` (cyc f ` D)" using \<open>x \<in> D\<close> by blast
  qed
    show "(\<lambda>C. T4 \<times> C) ` (cyc f ` D) \<subseteq> ?q ` (T4 \<times> D)"
    proof
      fix S assume "S \<in> (\<lambda>C. T4 \<times> C) ` (cyc f ` D)"
      then obtain x where x: "x \<in> D" "S = T4 \<times> cyc f x" by blast
      then have "S = ?q (CTn, x)" using cyc_cube_f by simp
      moreover have "(CTn, x) \<in> T4 \<times> D" using x by (simp add: T4_def)
      ultimately show "S \<in> ?q ` (T4 \<times> D)" by blast
    qed
  qed
  have injE: "inj_on (\<lambda>C. {CTe} \<times> C) X" for X :: "'a set set"
  proof (rule inj_onI)
    fix A B :: "'a set" assume "{CTe} \<times> A = {CTe} \<times> B"
    then have "snd ` ({CTe} \<times> A) = snd ` ({CTe} \<times> B)" by simp
    then show "A = B" by (simp add: snd_image_times)
  qed
  have injN: "inj_on (\<lambda>C. {CTfe} \<times> C) X" for X :: "'a set set"
  proof (rule inj_onI)
    fix A B :: "'a set" assume "{CTfe} \<times> A = {CTfe} \<times> B"
    then have "snd ` ({CTfe} \<times> A) = snd ` ({CTfe} \<times> B)" by simp
    then show "A = B" by (simp add: snd_image_times)
  qed
  have CTnT4: "CTn \<in> T4" by (simp add: T4_def)
  have injF: "inj_on (\<lambda>C. T4 \<times> C) X" for X :: "'a set set"
  proof (rule inj_onI)
    fix A B :: "'a set" assume "T4 \<times> A = T4 \<times> B"
    then have "snd ` (T4 \<times> A) = snd ` (T4 \<times> B)" by simp
    moreover have "T4 \<noteq> {}" using CTnT4 by blast
    ultimately show "A = B" by (simp add: snd_image_times)
  qed
  have fin: "finite (cyc e ` D)" "finite (cyc n ` D)" "finite (cyc f ` D)" using finite_darts by simp_all
  have tagE: "S \<subseteq> {CTe} \<times> UNIV \<and> S \<noteq> {}" if Sin: "S \<in> ?q ` ({CTe} \<times> D)" for S
  proof -
    obtain x where x: "x \<in> D" "S = ?q (CTe, x)" using Sin by blast
    then have Sx: "S = {CTe} \<times> cyc e x" using cyc_cube_e by simp
    have "x \<in> cyc e x" by simp
    then have "(CTe, x) \<in> S" using Sx by simp
    then show ?thesis using Sx by blast
  qed
  have tagN: "S \<subseteq> {CTfe} \<times> UNIV \<and> S \<noteq> {}" if Sin: "S \<in> ?q ` ({CTfe} \<times> D)" for S
  proof -
    obtain x where x: "x \<in> D" "S = ?q (CTfe, x)" using Sin by blast
    then have Sx: "S = {CTfe} \<times> cyc n x" using cyc_cube_n by simp
    have "x \<in> cyc n x" by simp
    then have "(CTfe, x) \<in> S" using Sx by simp
    then show ?thesis using Sx by blast
  qed
  have tagF: "S \<subseteq> T4 \<times> UNIV \<and> S \<noteq> {}" if Sin: "S \<in> ?q ` (T4 \<times> D)" for S
  proof -
    obtain t x where tx: "t \<in> T4" "x \<in> D" "S = ?q (t, x)" using Sin by blast
    then have "S = T4 \<times> cyc f x" using cyc_cube_f' by simp
    moreover have "x \<in> cyc f x" by simp
    ultimately show ?thesis using CTnT4 by blast
  qed
  have d1: "?q ` ({CTe} \<times> D) \<inter> ?q ` ({CTfe} \<times> D) = {}"
  proof -
    { fix S assume "S \<in> ?q ` ({CTe} \<times> D)" "S \<in> ?q ` ({CTfe} \<times> D)"
      then have "S \<subseteq> {CTe} \<times> UNIV" "S \<subseteq> {CTfe} \<times> UNIV" "S \<noteq> {}" using tagE tagN by blast+
      then have False by blast }
    then show ?thesis by blast
  qed
  have d2: "(?q ` ({CTe} \<times> D) \<union> ?q ` ({CTfe} \<times> D)) \<inter> ?q ` (T4 \<times> D) = {}"
  proof -
    { fix S assume S1: "S \<in> ?q ` ({CTe} \<times> D) \<union> ?q ` ({CTfe} \<times> D)" and S2: "S \<in> ?q ` (T4 \<times> D)"
      have "S \<subseteq> T4 \<times> UNIV" "S \<noteq> {}" using tagF[OF S2] by blast+
      moreover have "S \<subseteq> {CTe} \<times> UNIV \<or> S \<subseteq> {CTfe} \<times> UNIV" using S1 tagE tagN by blast
      ultimately have False by (auto simp: T4_def) }
    then show ?thesis by blast
  qed
  have fA: "finite (?q ` ({CTe} \<times> D))" "finite (?q ` ({CTfe} \<times> D))" "finite (?q ` (T4 \<times> D))"
    using finite_darts by simp_all
  have U: "?q ` (UNIV \<times> D) = (?q ` ({CTe} \<times> D) \<union> ?q ` ({CTfe} \<times> D)) \<union> ?q ` (T4 \<times> D)"
    by (subst split) (simp only: image_Un)
  have "card (?q ` (UNIV \<times> D)) = card (?q ` ({CTe} \<times> D) \<union> ?q ` ({CTfe} \<times> D)) + card (?q ` (T4 \<times> D))"
    unfolding U by (rule card_Un_disjoint[OF _ fA(3) d2]) (use fA in simp)
  also have "card (?q ` ({CTe} \<times> D) \<union> ?q ` ({CTfe} \<times> D)) = card (?q ` ({CTe} \<times> D)) + card (?q ` ({CTfe} \<times> D))"
    by (rule card_Un_disjoint[OF fA(1) fA(2) d1])
  finally have "card (?q ` (UNIV \<times> D)) = card (?q ` ({CTe} \<times> D)) + card (?q ` ({CTfe} \<times> D)) + card (?q ` (T4 \<times> D))" .
  also have "\<dots> = fcard e D + fcard n D + fcard f D"
    unfolding iE iN iF fcard_def
    by (simp add: card_image[OF injE] card_image[OF injN] card_image[OF injF])
  finally show ?thesis by (simp add: fcard_def)
qed

subsection \<open>Components of the cube\<close>

lemma glink_cube_proj:
  assumes "glink (cube G) u v"
  shows "gcomp G (snd u) (snd v)"
proof -
  obtain t x where u: "u = (t, x)" by (cases u)
  have g1: "glink G a b \<Longrightarrow> gcomp G a b" for a b by (rule r_into_rtranclp)
  have gf: "gcomp G a (f a)" "gcomp G a (e a)" "gcomp G a (n a)" for a by (simp_all add: g1)
  have gnf: "gcomp G a (n (f a))" for a by (rule rtranclp_trans[OF gf(1) gf(3)])
  have gfe: "gcomp G a (f (e a))" for a by (rule rtranclp_trans[OF gf(2) gf(1)])
  show ?thesis
  proof (cases "x \<in> D")
    case False
    then have "v = u" using assms u cube_out[of u] by (auto simp: glink_def)
    then show ?thesis by simp
  next
    case True
    consider "cube_edge G u = v" | "cube_node G u = v" | "cube_face G u = v"
      using assms by (auto simp: glink_def)
    then show ?thesis
      by cases (cases t; auto simp: u True cube_edge_def cube_node_def cube_face_def gf gnf gfe)+
  qed
qed

lemma gcomp_cube_proj: "gcomp (cube G) u v \<Longrightarrow> gcomp G (snd u) (snd v)"
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step v w)
  show ?case by (rule rtranclp_trans[OF step(3) glink_cube_proj[OF step(2)]])
qed

lemma gcomp_cube_tags:
  assumes xD: "x \<in> D"
  shows "gcomp (cube G) (t, x) (t', x)"
proof -
  interpret Q: hypermap "cube G" by (rule hypermap_cube)
  have l: "glink (cube G) u v \<Longrightarrow> gcomp (cube G) u v" for u v by (rule r_into_rtranclp)
  have c1: "gcomp (cube G) (CTn, x) (CTen, x)" using l[of "(CTn, x)" "(CTen, x)"] xD
    by (simp add: glink_def cube_face_def)
  have c2: "gcomp (cube G) (CTen, x) (CTf, x)" using l[of "(CTen, x)" "(CTf, x)"] xD
    by (simp add: glink_def cube_face_def)
  have c3: "gcomp (cube G) (CTf, x) (CTnf, x)" using l[of "(CTf, x)" "(CTnf, x)"] xD
    by (simp add: glink_def cube_face_def)
  have c4: "gcomp (cube G) (CTn, x) (CTfe, x)" using l[of "(CTn, x)" "(CTfe, x)"] xD
    by (simp add: glink_def cube_edge_def)
  have c5: "gcomp (cube G) (CTe, x) (CTf, x)" using l[of "(CTe, x)" "(CTf, x)"] xD
    by (simp add: glink_def cube_node_def)
  have all: "gcomp (cube G) (CTn, x) (s, x)" for s
  proof (cases s)
    case CTn then show ?thesis by simp
  next
    case CTen then show ?thesis using c1 by simp
  next
    case CTf then show ?thesis using rtranclp_trans[OF c1 c2] by simp
  next
    case CTnf then show ?thesis using rtranclp_trans[OF rtranclp_trans[OF c1 c2] c3] by simp
  next
    case CTe then show ?thesis using rtranclp_trans[OF rtranclp_trans[OF c1 c2] Q.gcomp_sym[OF c5]] by simp
  next
    case CTfe then show ?thesis using c4 by simp
  qed
  show ?thesis by (rule rtranclp_trans[OF Q.gcomp_sym[OF all[of t]] all[of t']])
qed

lemma gcomp_cube_lift:
  assumes "gcomp G x y" "x \<in> D"
  shows "gcomp (cube G) (t, x) (t', y)"
  using assms
proof (induction arbitrary: t' rule: rtranclp_induct)
  case base
  then show ?case using gcomp_cube_tags by simp
next
  case (step y z)
  have yD: "y \<in> D" using step(1) step(4) gcomp_closed by blast
  have l: "glink (cube G) u v \<Longrightarrow> gcomp (cube G) u v" for u v by (rule r_into_rtranclp)
  have yz: "gcomp (cube G) (CTnf, y) (t', z)"
  proof -
    have zD: "z \<in> D" using step(2) yD glink_closed by blast
    consider "e y = z" | "n y = z" | "f y = z" using step(2) by (auto simp: glink_def)
    then show ?thesis
    proof cases
      case 1
      have m: "gcomp (cube G) (CTe, y) (CTe, z)" using l[of "(CTe, y)" "(CTe, z)"] yD 1
        by (simp add: glink_def cube_face_def)
      show ?thesis
        by (rule rtranclp_trans[OF rtranclp_trans[OF gcomp_cube_tags[OF yD] m] gcomp_cube_tags[OF zD]])
    next
      case 2
      have m: "gcomp (cube G) (CTfe, y) (CTfe, z)" using l[of "(CTfe, y)" "(CTfe, z)"] yD 2
        by (simp add: glink_def cube_face_def)
      show ?thesis
        by (rule rtranclp_trans[OF rtranclp_trans[OF gcomp_cube_tags[OF yD] m] gcomp_cube_tags[OF zD]])
    next
      case 3
      have m: "gcomp (cube G) (CTnf, y) (CTn, z)" using l[of "(CTnf, y)" "(CTn, z)"] yD 3
        by (simp add: glink_def cube_face_def)
      show ?thesis by (rule rtranclp_trans[OF m gcomp_cube_tags[OF zD]])
    qed
  qed
  show ?case by (rule rtranclp_trans[OF step(3)[of CTnf] yz]) (rule step(4))
qed

lemma comp_cube: "x \<in> D \<Longrightarrow> comp_of (glink (cube G)) (t, x) = UNIV \<times> comp_of (glink G) x"
proof (intro set_eqI iffI)
  fix u :: "cube_tag \<times> 'a" assume xD: "x \<in> D" and "u \<in> comp_of (glink (cube G)) (t, x)"
  then have "gcomp (cube G) (t, x) u" by (simp add: comp_of_def)
  then have "gcomp G x (snd u)" using gcomp_cube_proj by fastforce
  then show "u \<in> UNIV \<times> comp_of (glink G) x" by (cases u) (simp add: comp_of_def)
next
  fix u :: "cube_tag \<times> 'a" assume xD: "x \<in> D" and "u \<in> UNIV \<times> comp_of (glink G) x"
  then obtain t' y where u: "u = (t', y)" "gcomp G x y" by (auto simp: comp_of_def)
  then have "gcomp (cube G) (t, x) (t', y)" using gcomp_cube_lift xD by blast
  then show "u \<in> comp_of (glink (cube G)) (t, x)" using u by (simp add: comp_of_def)
qed

lemma n_comp_cube: "n_comp (glink (cube G)) (UNIV \<times> D) = n_comp (glink G) D"
proof -
  have "comp_of (glink (cube G)) ` (UNIV \<times> D) = (\<lambda>C. UNIV \<times> C) ` (comp_of (glink G) ` D)"
  proof
    show "comp_of (glink (cube G)) ` (UNIV \<times> D) \<subseteq> (\<lambda>C. UNIV \<times> C) ` (comp_of (glink G) ` D)"
      using comp_cube by fastforce
    show "(\<lambda>C. UNIV \<times> C) ` (comp_of (glink G) ` D) \<subseteq> comp_of (glink (cube G)) ` (UNIV \<times> D)"
    proof
      fix S :: "(cube_tag \<times> 'a) set" assume "S \<in> (\<lambda>C. UNIV \<times> C) ` (comp_of (glink G) ` D)"
      then obtain x where x: "x \<in> D" "S = UNIV \<times> comp_of (glink G) x" by blast
      then have "S = comp_of (glink (cube G)) (CTn, x)" using comp_cube by simp
      then show "S \<in> comp_of (glink (cube G)) ` (UNIV \<times> D)" using x by blast
    qed
  qed
  moreover have "inj_on (\<lambda>C. (UNIV :: cube_tag set) \<times> C) X" for X :: "'a set set"
  proof (rule inj_onI)
    fix A B :: "'a set" assume "UNIV \<times> A = (UNIV :: cube_tag set) \<times> B"
    then have "snd ` ((UNIV :: cube_tag set) \<times> A) = snd ` ((UNIV :: cube_tag set) \<times> B)" by (rule arg_cong)
    then show "A = B" by (simp add: snd_image_times)
  qed
  ultimately show ?thesis by (simp add: n_comp_def card_image)
qed

theorem genus_cube: "genus (cube G) = genus G"
proof -
  interpret Q: hypermap "cube G" by (rule hypermap_cube)
  have cQ: "card (UNIV \<times> D :: (cube_tag \<times> 'a) set) = 6 * card D"
    by (simp add: card_cartesian_product UNIV_cube_tag)
  have eQ: "card (darts (cube G)) = 2 * fcard (edge (cube G)) (darts (cube G))"
  proof (rule Q.E.card_uniform_orbits)
    show "\<And>u. u \<in> darts (cube G) \<Longrightarrow> edge (cube G) u \<in> darts (cube G)" by (simp add: cube_edge_D)
    show "\<And>u. u \<in> darts (cube G) \<Longrightarrow> order (edge (cube G)) u = 2"
      using Q.plain_order[OF plain_cube] by simp
  qed simp
  have nQ: "card (darts (cube G)) = 3 * fcard (node (cube G)) (darts (cube G))"
  proof (rule Q.N.card_uniform_orbits)
    show "\<And>u. u \<in> darts (cube G) \<Longrightarrow> node (cube G) u \<in> darts (cube G)" by (simp add: cube_node_D)
    show "\<And>u. u \<in> darts (cube G) \<Longrightarrow> order (node (cube G)) u = 3"
      using Q.cubic_order[OF cubic_cube] by simp
  qed simp
  have "Euler_lhs (cube G) = 2 * n_comp (glink G) D + 6 * card D"
    using cQ n_comp_cube by (simp add: Euler_lhs_def)
  moreover have "Euler_rhs (cube G) = 5 * card D + Euler_rhs G"
    using cQ eQ nQ fcard_cube_face by (simp add: Euler_rhs_def)
  ultimately show ?thesis by (simp add: genus_def Euler_lhs_def)
qed

lemma planar_cube: "planar (cube G) \<longleftrightarrow> planar G"
  by (simp add: planar_def genus_cube)

lemma bridgeless_cube: "bridgeless (cube G) \<longleftrightarrow> bridgeless G"
proof
  assume bQ: "bridgeless (cube G)"
  show "bridgeless G" unfolding bridgeless_def
  proof (intro ballI notI)
    fix x assume xD: "x \<in> D" and xe: "cface x (e x)"
    have "(CTnf, e x) \<in> cyc (cube_face G) (CTen, x)"
      using cyc_cube_f'[OF xD, of CTen] xe by (simp add: T4_def F.in_cyc_iff)
    then have "fconnect (cube_face G) (CTen, x) (cube_edge G (CTen, x))"
      using xD by (simp add: cube_edge_def cyc_def)
    then show False using bQ xD by (simp add: bridgeless_def)
  qed
next
  assume bG: "bridgeless G"
  show "bridgeless (cube G)" unfolding bridgeless_def
  proof (intro ballI notI)
    fix u assume uD: "u \<in> darts (cube G)" and br: "fconnect (face (cube G)) u (edge (cube G) u)"
    obtain t x where u: "u = (t, x)" and xD: "x \<in> D" using uD by auto
    have mem: "cube_edge G u \<in> cyc (cube_face G) u" using br by (simp add: cyc_def)
    show False
    proof (cases t)
      case CTe
      then show False using mem u xD cyc_cube_e by (simp add: cube_edge_def)
    next
      case CTfe
      then show False using mem u xD cyc_cube_n by (simp add: cube_edge_def)
    next
      case CTn
      then show False using mem u xD cyc_cube_f by (simp add: cube_edge_def T4_def)
    next
      case CTf
      then show False using mem u xD cyc_cube_f'[OF xD, of CTf] by (simp add: cube_edge_def T4_def)
    next
      case CTen
      then have "e x \<in> cyc f x" using mem u xD cyc_cube_f'[OF xD, of CTen]
        by (simp add: cube_edge_def T4_def)
      then show False using bG xD by (simp add: bridgeless_def F.in_cyc_iff)
    next
      case CTnf
      then have "n (f x) \<in> cyc f x" using mem u xD cyc_cube_f'[OF xD, of CTnf]
        by (simp add: cube_edge_def T4_def)
      then have c: "cface x (n (f x))" by (simp add: F.in_cyc_iff)
      define y where "y = n (f x)"
      have yD: "y \<in> D" using xD by (simp add: y_def)
      have "e y = x" unfolding y_def by (rule faceK)
      then have "cface y (e y)" using F.fconnect_sym[OF c] unfolding y_def by simp
      then show False using bG yD by (simp add: bridgeless_def)
    qed
  qed
qed

end

end
