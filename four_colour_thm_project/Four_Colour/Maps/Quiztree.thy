(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Quiztree.thy
    Quiz trees: the quizzes of all configurations, indexed by the arities of a triangle of
    faces, so that a reducibility search can do a single lookup per triangle (quiztree.v).
    Ported from G. Gonthier's Coq development (quiztree.v).
*)
theory Quiztree
  imports Four_Colour_Maps.Cfquiz
begin

datatype quiz_tree =
    QztNil
  | QztLeaf question question question quiz_tree
  | QztNode quiz_tree quiz_tree quiz_tree quiz_tree
  | QztHubNode quiz_tree quiz_tree quiz_tree quiz_tree

fun qzt_proper :: "quiz_tree \<Rightarrow> bool" where
  "qzt_proper QztNil = False" | "qzt_proper _ = True"

fun qzt_put1 :: "qarity \<Rightarrow> (quiz_tree \<Rightarrow> quiz_tree) \<Rightarrow> quiz_tree \<Rightarrow> quiz_tree" where
  "qzt_put1 qa qr (QztNode t5 t6 t7 t8) = (case qa of
       Qa5 \<Rightarrow> QztNode (qr t5) t6 t7 t8 | Qa6 \<Rightarrow> QztNode t5 (qr t6) t7 t8
     | Qa7 \<Rightarrow> QztNode t5 t6 (qr t7) t8 | Qa8 \<Rightarrow> QztNode t5 t6 t7 (qr t8)
     | _ \<Rightarrow> QztNode t5 t6 t7 t8)"
| "qzt_put1 qa qr (QztHubNode t58 t9 t10 t11) = (case qa of
       Qa9 \<Rightarrow> QztHubNode t58 (qr t9) t10 t11 | Qa10 \<Rightarrow> QztHubNode t58 t9 (qr t10) t11
     | Qa11 \<Rightarrow> QztHubNode t58 t9 t10 (qr t11)
     | _ \<Rightarrow> QztHubNode (qzt_put1 qa qr t58) t9 t10 t11)"
| "qzt_put1 qa qr t = t"

definition qzt_put3 where
  "qzt_put3 qa1 qa2 qa3 q1 q2 q3 = qzt_put1 qa1 (qzt_put1 qa2 (qzt_put1 qa3 (QztLeaf q1 q2 q3)))"

definition qzt_put3rot where
  "qzt_put3rot qa1 qa2 qa3 q1 q2 q3 t =
     qzt_put3 qa1 qa2 qa3 q1 q2 q3 (qzt_put3 qa2 qa3 qa1 q2 q3 q1 (qzt_put3 qa3 qa1 qa2 q3 q1 q2 t))"

definition qzt_put where
  "qzt_put qa1 qa2 qa3 q1 q2 q3 =
     (if 8 < nat_of_qarity qa1 then qzt_put3 qa1 qa2 qa3 q1 q2 q3 else qzt_put3rot qa1 qa2 qa3 q1 q2 q3)"

definition qzt_empty :: quiz_tree where
  "qzt_empty = (let mkn = (\<lambda>t. QztNode t t t t); n2 = mkn (mkn QztNil) in QztHubNode (mkn n2) n2 n2 n2)"

fun normq :: "question \<Rightarrow> question" where
  "normq (Qask1 qa) = QaskLR qa Qask0 Qask0"
| "normq (QaskL qa ql) = QaskLR qa ql Qask0"
| "normq (QaskR qa qr) = QaskLR qa Qask0 qr"
| "normq q = q"

fun store_qz :: "quiz \<Rightarrow> quiz_tree \<Rightarrow> quiz_tree" where
  "store_qz (Quiz (QaskR qa1 q1) (QaskR qa2 q2)) =
     (case (normq q1, normq q2) of
        (QaskLR qa1r q1l q1r, QaskLR qa2r q2l q2r) \<Rightarrow>
          if nat_of_qarity qa1r < nat_of_qarity qa2r then qzt_put qa1 qa2 qa1r q1l q2 q1r
          else qzt_put qa1 qa2r qa2 q1 q2r q2l
      | (QaskLR qa1r q1l q1r, _) \<Rightarrow> qzt_put qa1 qa2 qa1r q1l q2 q1r
      | (_, QaskLR qa2r q2l q2r) \<Rightarrow> qzt_put qa1 qa2r qa2 q1 q2r q2l
      | _ \<Rightarrow> (\<lambda>t. t))"
| "store_qz _ = (\<lambda>t. t)"

definition store_cf_qz :: "quiz \<Rightarrow> bool \<Rightarrow> quiz_tree \<Rightarrow> quiz_tree" where
  "store_cf_qz qz sy t = store_qz qz (if sy then t else store_qz (flipqz qz) t)"

fun cfquiz_tree_rec :: "quiz_tree \<Rightarrow> config list \<Rightarrow> quiz_tree" where
  "cfquiz_tree_rec qt [] = qt"
| "cfquiz_tree_rec qt (cf # cfs') =
    (case store_cf_qz (cfquiz cf) (cfsym cf) qt of
       QztHubNode a b c d \<Rightarrow> cfquiz_tree_rec (QztHubNode a b c d) cfs'
     | _ \<Rightarrow> QztNil)"

definition cfquiz_tree :: "config list \<Rightarrow> quiz_tree" where
  "cfquiz_tree = cfquiz_tree_rec qzt_empty"

fun qzt_size :: "quiz_tree \<Rightarrow> nat" where
  "qzt_size (QztLeaf _ _ _ t') = Suc (qzt_size t')"
| "qzt_size (QztNode t5 t6 t7 t8) = qzt_size t5 + (qzt_size t6 + (qzt_size t7 + qzt_size t8))"
| "qzt_size (QztHubNode t58 t9 t10 t11) = qzt_size t58 + (qzt_size t9 + (qzt_size t10 + qzt_size t11))"
| "qzt_size QztNil = 0"

fun qzt_get1 :: "qarity \<Rightarrow> quiz_tree \<Rightarrow> quiz_tree" where
  "qzt_get1 qa (QztNode t5 t6 t7 t8) = (case qa of
       Qa5 \<Rightarrow> t5 | Qa6 \<Rightarrow> t6 | Qa7 \<Rightarrow> t7 | Qa8 \<Rightarrow> t8 | _ \<Rightarrow> QztNil)"
| "qzt_get1 qa (QztHubNode t58 t9 t10 t11) = (case qa of
       Qa9 \<Rightarrow> t9 | Qa10 \<Rightarrow> t10 | Qa11 \<Rightarrow> t11 | _ \<Rightarrow> qzt_get1 qa t58)"
| "qzt_get1 qa _ = QztNil"

definition qzt_get2 where "qzt_get2 qa2 qa3 t = qzt_get1 qa3 (qzt_get1 qa2 t)"
definition qzt_get3 where "qzt_get3 qa1 qa2 qa3 t = qzt_get2 qa2 qa3 (qzt_get1 qa1 t)"

lemma qzt_get_put1:
  "(qa = qa' \<and> qr (qzt_get1 qa t) = qzt_get1 qa (qzt_put1 qa' qr t)) \<or>
   qzt_get1 qa t = qzt_get1 qa (qzt_put1 qa' qr t)"
  by (induction t) (cases qa; cases qa'; auto)+

fun qzt_truncate :: "quiz_tree \<Rightarrow> quiz_tree" where
  "qzt_truncate (QztHubNode (QztNode a b c d) t9 t10 t11) = QztNode a b c d"
| "qzt_truncate t = t"

lemma qzt_get1_truncate:
  "qzt_proper (qzt_get1 qa (qzt_truncate t)) \<Longrightarrow> qzt_get1 qa (qzt_truncate t) = qzt_get1 qa t"
  by (cases t rule: qzt_truncate.cases) (cases qa; auto)+

abbreviation quiz3 :: "qarity \<Rightarrow> qarity \<Rightarrow> qarity \<Rightarrow> question \<Rightarrow> question \<Rightarrow> question \<Rightarrow> quiz" where
  "quiz3 qa1 qa2 qa3 q1 q2 q3 \<equiv> Quiz (QaskR qa1 (QaskLR qa3 q1 q3)) (QaskR qa2 q2)"

section \<open>Fitting quiz trees\<close>

locale qzt_ctx = hypermap G for G :: "'a hypermap" +
  fixes x1 :: 'a
  assumes plainG: "plain G" and cubicG: "cubic G"
begin

lemma ee [simp]: "e (e x) = x" using plain_eq[OF plainG] .

lemma nnn [simp]: "n (n (n x)) = x"
proof (cases "x \<in> D")
  case True
  then show ?thesis using cubic_eq[OF cubicG] by blast
next
  case False
  then show ?thesis by simp
qed

lemma f_ne: "f x = n (n (e x))"
proof -
  have "n (f (e (e x))) = e x" by (rule edgeK)
  then have "n (f x) = e x" by simp
  then have "n (n (n (f x))) = n (n (e x))" by simp
  then show ?thesis by simp
qed

lemma ar_nne [simp]: "arity G (n (n (e x))) = arity G x"
proof -
  have "arity G (f x) = arity G x" by simp
  then show ?thesis unfolding f_ne .
qed

lemma ar_en [simp]: "arity G (e (n x)) = arity G x"
  using ar_nne[of "e (n x)"] by simp

abbreviation "x2 \<equiv> n x1"
abbreviation "x3 \<equiv> n x2"

definition "ax1 = qarity_of_nat (arity G x1)"
definition "ax2 = qarity_of_nat (arity G x2)"
definition "ax3 = qarity_of_nat (arity G x3)"

definition qzt_fita :: bool where
  "qzt_fita \<longleftrightarrow> nat_of_qarity ax1 = arity G x1 \<and> nat_of_qarity ax2 = arity G x2 \<and>
     nat_of_qarity ax3 = arity G x3"

fun qzt_fitl :: "quiz_tree \<Rightarrow> bool" where
  "qzt_fitl (QztLeaf q1 q2 q3 t') \<longleftrightarrow>
     (fitq G (qstepR G x1) q1 \<and> fitq G (qstepR G x2) q2 \<and> fitq G (qstepR G x3) q3) \<or> qzt_fitl t'"
| "qzt_fitl _ = False"

definition qzt_fit :: "quiz_tree \<Rightarrow> bool" where
  "qzt_fit t \<longleftrightarrow> qzt_fita \<and> qzt_fitl (qzt_get3 ax1 ax2 ax3 t)"

lemma fit_normq: "fitq G x (normq q) \<longleftrightarrow> fitq G x q"
  by (cases q) (simp_all add: fitq_def)

lemma fitqz3:
  "fitqz G y (quiz3 qa1 qa2 qa3 q1 q2 q3) \<longleftrightarrow>
     nat_of_qarity qa1 = arity G y \<and> nat_of_qarity qa3 = arity G (qstepR G y) \<and>
     fitq G (qstepL G (qstepR G y)) q1 \<and> fitq G (qstepR G (qstepR G y)) q3 \<and>
     nat_of_qarity qa2 = arity G (e y) \<and> fitq G (qstepR G (e y)) q2"
  by (simp add: fitqz_def fitq_def append_eq_append_conv length_walkq)

lemma qzt_fit_put3:
  assumes "qzt_fit (qzt_put3 qa1 qa2 qa3 q1 q2 q3 t)"
  shows "fitqz G (e x2) (quiz3 qa1 qa2 qa3 q1 q2 q3) \<or> qzt_fit t"
proof -
  have fa: "qzt_fita" and fl: "qzt_fitl (qzt_get3 ax1 ax2 ax3 (qzt_put3 qa1 qa2 qa3 q1 q2 q3 t))"
    using assms by (simp_all add: qzt_fit_def)
  let ?r = "QztLeaf q1 q2 q3"
  consider (hit) "ax1 = qa1" "ax2 = qa2" "ax3 = qa3"
      "qzt_get3 ax1 ax2 ax3 (qzt_put3 qa1 qa2 qa3 q1 q2 q3 t) = ?r (qzt_get3 ax1 ax2 ax3 t)"
    | (miss) "qzt_get3 ax1 ax2 ax3 (qzt_put3 qa1 qa2 qa3 q1 q2 q3 t) = qzt_get3 ax1 ax2 ax3 t"
  proof -
    note g1 = qzt_get_put1[of ax1 qa1 "qzt_put1 qa2 (qzt_put1 qa3 ?r)" t]
    note g2 = qzt_get_put1[of ax2 qa2 "qzt_put1 qa3 ?r" "qzt_get1 ax1 t"]
    note g3 = qzt_get_put1[of ax3 qa3 ?r "qzt_get1 ax2 (qzt_get1 ax1 t)"]
    show ?thesis using g1 g2 g3 that unfolding qzt_get3_def qzt_get2_def qzt_put3_def by metis
  qed
  then show ?thesis
  proof cases
    case hit
    show ?thesis
    proof (cases "fitq G (qstepR G x1) q1 \<and> fitq G (qstepR G x2) q2 \<and> fitq G (qstepR G x3) q3")
      case True
      have "fitqz G (e x2) (quiz3 qa1 qa2 qa3 q1 q2 q3)"
        unfolding fitqz3 using True fa hit(1-3)
        by (simp add: qzt_fita_def qstepL_def qstepR_def)
      then show ?thesis by simp
    next
      case False
      then have "qzt_fitl (qzt_get3 ax1 ax2 ax3 t)" using fl hit(4) by auto
      then show ?thesis using fa by (simp add: qzt_fit_def)
    qed
  next
    case miss
    then show ?thesis using fa fl by (simp add: qzt_fit_def)
  qed
qed

lemma fitqz_rot:
  "fitqz G y (quiz3 qa1 qa2 qa3 q1 q2 q3) \<longleftrightarrow> fitqz G (e (f y)) (quiz3 qa3 qa1 qa2 q3 q1 q2)"
  unfolding fitqz3 by (auto simp: f_ne qstepL_def qstepR_def)

lemma qzt_fit_put:
  assumes "qzt_fit (qzt_put qa1 qa2 qa3 q1 q2 q3 t)"
  shows "(\<exists>y. fitqz G y (quiz3 qa1 qa2 qa3 q1 q2 q3)) \<or> qzt_fit t"
proof (cases "8 < nat_of_qarity qa1")
  case True
  then have "qzt_fit (qzt_put3 qa1 qa2 qa3 q1 q2 q3 t)" using assms by (simp add: qzt_put_def)
  then show ?thesis using qzt_fit_put3 by blast
next
  case False
  have r: "qzt_fit (qzt_put3 qa1 qa2 qa3 q1 q2 q3
             (qzt_put3 qa2 qa3 qa1 q2 q3 q1 (qzt_put3 qa3 qa1 qa2 q3 q1 q2 t)))"
    using assms False by (simp add: qzt_put_def qzt_put3rot_def)
  show ?thesis
  proof (cases "fitqz G (e x2) (quiz3 qa1 qa2 qa3 q1 q2 q3)")
    case True
    then show ?thesis by blast
  next
    case n1: False
    then have r2: "qzt_fit (qzt_put3 qa2 qa3 qa1 q2 q3 q1 (qzt_put3 qa3 qa1 qa2 q3 q1 q2 t))"
      using qzt_fit_put3[OF r] by blast
    show ?thesis
    proof (cases "fitqz G (e x2) (quiz3 qa2 qa3 qa1 q2 q3 q1)")
      case True
      then have "fitqz G (e (f (e x2))) (quiz3 qa1 qa2 qa3 q1 q2 q3)"
        using fitqz_rot[of "e x2" qa2 qa1 q2 q1 qa3 q3] by simp
      then show ?thesis by blast
    next
      case n2: False
      then have r3: "qzt_fit (qzt_put3 qa3 qa1 qa2 q3 q1 q2 t)" using qzt_fit_put3[OF r2] by blast
      show ?thesis
      proof (cases "fitqz G (e x2) (quiz3 qa3 qa1 qa2 q3 q1 q2)")
        case True
        then have "fitqz G (e (f (e x2))) (quiz3 qa2 qa3 qa1 q2 q3 q1)"
          using fitqz_rot[of "e x2" qa3 qa2 q3 q2 qa1 q1] by simp
        then have "fitqz G (e (f (e (f (e x2))))) (quiz3 qa1 qa2 qa3 q1 q2 q3)"
          using fitqz_rot[of "e (f (e x2))" qa2 qa1 q2 q1 qa3 q3] by simp
        then show ?thesis by blast
      next
        case False
        then show ?thesis using qzt_fit_put3[OF r3] by blast
      qed
    qed
  qed
qed

lemma fitqz_swap:
  "fitqz G y (quiz3 qa1 qa2 qa3 q1 q2 q3) \<longleftrightarrow>
   fitqz G (f y) (Quiz (QaskR qa1 q1) (QaskR qa3 (QaskLR qa2 q3 q2)))"
  by (auto simp: fitqz_def fitq_def append_eq_append_conv length_walkq f_ne qstepL_def qstepR_def)

lemma qzt_fit_store:
  assumes "qzt_fit (store_qz qz t)"
  shows "(isQuizR qz \<and> (\<exists>y. fitqz G y qz)) \<or> qzt_fit t"
proof (cases "\<exists>qa1 q1 qa2 q2. qz = Quiz (QaskR qa1 q1) (QaskR qa2 q2)")
  case False
  then have "store_qz qz t = t" by (cases qz rule: store_qz.cases) auto
  then show ?thesis using assms by simp
next
  case True
  then obtain qa1 q1 qa2 q2 where qz: "qz = Quiz (QaskR qa1 q1) (QaskR qa2 q2)" by blast
  have R: "isQuizR qz" by (simp add: qz)
  have c1: "(\<exists>y. fitqz G y qz) \<or> qzt_fit t"
    if n1: "normq q1 = QaskLR qa1r q1l q1r" and ft: "qzt_fit (qzt_put qa1 qa2 qa1r q1l q2 q1r t)"
    for qa1r q1l q1r
  proof -
    from qzt_fit_put[OF ft] show ?thesis
    proof
      assume "\<exists>y. fitqz G y (quiz3 qa1 qa2 qa1r q1l q2 q1r)"
      then obtain y where "fitqz G y (quiz3 qa1 qa2 qa1r q1l q2 q1r)" by blast
      then have "fitqz G y qz"
        using fit_normq[of "qstepR G y" q1] n1
        by (simp add: qz fitqz_def fitq_def append_eq_append_conv length_walkq)
      then show ?thesis by blast
    qed blast
  qed
  have c2: "(\<exists>y. fitqz G y qz) \<or> qzt_fit t"
    if n2: "normq q2 = QaskLR qa2r q2l q2r" and ft: "qzt_fit (qzt_put qa1 qa2r qa2 q1 q2r q2l t)"
    for qa2r q2l q2r
  proof -
    from qzt_fit_put[OF ft] show ?thesis
    proof
      assume "\<exists>y. fitqz G y (quiz3 qa1 qa2r qa2 q1 q2r q2l)"
      then obtain y where "fitqz G y (quiz3 qa1 qa2r qa2 q1 q2r q2l)" by blast
      then have "fitqz G (f y) (Quiz (QaskR qa1 q1) (QaskR qa2 (QaskLR qa2r q2l q2r)))"
        using fitqz_swap by blast
      then have "fitqz G (f y) qz"
        using fit_normq[of "qstepR G (e (f y))" q2] n2
        by (simp add: qz fitqz_def fitq_def append_eq_append_conv length_walkq)
      then show ?thesis by blast
    qed blast
  qed
  have "(\<exists>y. fitqz G y qz) \<or> qzt_fit t"
  proof (cases "normq q1")
    case (QaskLR qa1r q1l q1r)
    note n1 = this
    show ?thesis
    proof (cases "normq q2")
      case (QaskLR qa2r q2l q2r)
      then show ?thesis using assms n1 c1[OF n1] c2[OF QaskLR]
        by (simp add: qz split: if_splits)
    qed (use assms n1 c1[OF n1] in \<open>simp_all add: qz\<close>)
  next
    case Qask0
    then show ?thesis using assms c2 by (cases "normq q2") (simp_all add: qz)
  next
    case (Qask1 x) then show ?thesis by (cases q1) simp_all
  next
    case (QaskL x y) then show ?thesis by (cases q1) simp_all
  next
    case (QaskR x y) then show ?thesis by (cases q1) simp_all
  next
    case (QaskLL x y)
    then show ?thesis using assms c2 by (cases "normq q2") (simp_all add: qz)
  next
    case (QaskRR x y)
    then show ?thesis using assms c2 by (cases "normq q2") (simp_all add: qz)
  qed
  then show ?thesis using R by blast
qed

lemma isQuizR_flip: "isQuizR (flipqz qz) \<Longrightarrow> isQuizR qz"
  by (cases qz rule: flipqz.cases) auto

lemma qzt_fit_store_cf:
  assumes "qzt_fit (store_cf_qz qz sy t)"
  shows "(isQuizR qz \<and> ((\<exists>y. fitqz G y qz) \<or> (\<exists>y. fitqz (mirror G) y qz))) \<or> qzt_fit t"
proof (cases sy)
  case True
  then show ?thesis using qzt_fit_store assms by (auto simp: store_cf_qz_def)
next
  case False
  then have "qzt_fit (store_qz qz (store_qz (flipqz qz) t))" using assms by (simp add: store_cf_qz_def)
  then have "(isQuizR qz \<and> (\<exists>y. fitqz G y qz)) \<or> qzt_fit (store_qz (flipqz qz) t)"
    by (rule qzt_fit_store)
  then show ?thesis
  proof
    assume "qzt_fit (store_qz (flipqz qz) t)"
    then have "(isQuizR (flipqz qz) \<and> (\<exists>y. fitqz G y (flipqz qz))) \<or> qzt_fit t" by (rule qzt_fit_store)
    then show ?thesis
    proof
      assume a: "isQuizR (flipqz qz) \<and> (\<exists>y. fitqz G y (flipqz qz))"
      then have R: "isQuizR qz" using isQuizR_flip by blast
      obtain y where "fitqz G y (flipqz qz)" using a by blast
      then have "fitqz (mirror G) (f y) qz" using fitqz_flip[OF plainG cubicG R] by simp
      then show ?thesis using R by blast
    qed simp
  qed blast
qed

lemma qzt_fit_Nil: "\<not> qzt_fit QztNil"
  by (simp add: qzt_fit_def qzt_get3_def qzt_get2_def)

lemma qzt_fit_empty: "\<not> qzt_fit qzt_empty"
  unfolding qzt_fit_def qzt_get3_def qzt_get2_def qzt_empty_def
  by (cases ax1; cases ax2; cases ax3) (simp_all add: Let_def)

definition cf_fits :: "config \<Rightarrow> bool" where
  "cf_fits cf \<longleftrightarrow> isQuizR (cfquiz cf) \<and>
     ((\<exists>y. fitqz G y (cfquiz cf)) \<or> (\<exists>y. fitqz (mirror G) y (cfquiz cf)))"

lemma qzt_fit_cfquiz_rec:
  "\<not> qzt_fit qt0 \<Longrightarrow> qzt_fit (cfquiz_tree_rec qt0 cfs) \<Longrightarrow> \<exists>i < length cfs. cf_fits (cfs ! i)"
proof (induction cfs arbitrary: qt0)
  case Nil
  then show ?case by simp
next
  case (Cons cf cfs)
  define qt where "qt = store_cf_qz (cfquiz cf) (cfsym cf) qt0"
  show ?case
  proof (cases qt)
    case (QztHubNode a b c d)
    then have rec: "qzt_fit (cfquiz_tree_rec qt cfs)" using Cons.prems(2) by (simp add: qt_def)
    show ?thesis
    proof (cases "qzt_fit qt")
      case True
      then have "cf_fits cf \<or> qzt_fit qt0"
        using qzt_fit_store_cf[of "cfquiz cf" "cfsym cf" qt0] by (auto simp: qt_def cf_fits_def)
      then have "cf_fits cf" using Cons.prems(1) by blast
      then show ?thesis by force
    next
      case False
      then obtain i where "i < length cfs" "cf_fits (cfs ! i)" using Cons.IH[OF False rec] by blast
      then show ?thesis by (intro exI[of _ "Suc i"]) simp
    qed
  qed (use Cons.prems(2) qzt_fit_Nil in \<open>simp_all add: qt_def[symmetric]\<close>)
qed

theorem qzt_fit_cfquiz:
  "qzt_fit (cfquiz_tree cfs) \<Longrightarrow> \<exists>i < length cfs. cf_fits (cfs ! i)"
  unfolding cfquiz_tree_def by (rule qzt_fit_cfquiz_rec[OF qzt_fit_empty])

end

end
