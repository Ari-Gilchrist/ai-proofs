(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Quiz.thy
    Quizzes: pairs of question trees that cover the kernel of a configuration and record its
    face arities; a quiz that fits a plain cubic map yields a preembedding (quiz.v).
    Ported from G. Gonthier's Coq development (quiz.v).
*)
theory Quiz
  imports Four_Colour_Maps.Embed2
begin

section \<open>Arities and questions\<close>

datatype qarity = Qa5 | Qa6 | Qa7 | Qa8 | Qa9 | Qa10 | Qa11

fun nat_of_qarity :: "qarity \<Rightarrow> nat" where
  "nat_of_qarity Qa5 = 5" | "nat_of_qarity Qa6 = 6" | "nat_of_qarity Qa7 = 7"
| "nat_of_qarity Qa8 = 8" | "nat_of_qarity Qa9 = 9" | "nat_of_qarity Qa10 = 10"
| "nat_of_qarity Qa11 = 11"

definition qarity_of_nat :: "nat \<Rightarrow> qarity" where
  "qarity_of_nat n = (if n = 5 then Qa5 else if n = 6 then Qa6 else if n = 7 then Qa7
     else if n = 8 then Qa8 else if n = 9 then Qa9 else if n = 10 then Qa10 else Qa11)"

lemma qarity_of_qarity: "qarity_of_nat (nat_of_qarity qa) = qa"
  by (cases qa) (simp_all add: qarity_of_nat_def)

datatype question =
    Qask0
  | Qask1 qarity
  | QaskL qarity question
  | QaskR qarity question
  | QaskLR qarity question question
  | QaskLL qarity question
  | QaskRR qarity question

fun isQaskR :: "question \<Rightarrow> bool" where
  "isQaskR (QaskR _ _) = True" | "isQaskR _ = False"

fun flatq :: "question \<Rightarrow> nat list" where
  "flatq Qask0 = []"
| "flatq (Qask1 qa) = [nat_of_qarity qa]"
| "flatq (QaskL qa ql) = nat_of_qarity qa # flatq ql"
| "flatq (QaskR qa qr) = nat_of_qarity qa # flatq qr"
| "flatq (QaskLR qa ql qr) = nat_of_qarity qa # flatq ql @ flatq qr"
| "flatq (QaskLL qa q) = nat_of_qarity qa # flatq q"
| "flatq (QaskRR qa q) = nat_of_qarity qa # flatq q"

fun flipq :: "question \<Rightarrow> question" where
  "flipq (QaskL qa ql) = QaskR qa (flipq ql)"
| "flipq (QaskR qa qr) = QaskL qa (flipq qr)"
| "flipq (QaskLR qa ql qr) = QaskLR qa (flipq qr) (flipq ql)"
| "flipq (QaskLL qa q) = QaskRR qa (flipq q)"
| "flipq (QaskRR qa q) = QaskLL qa (flipq q)"
| "flipq q = q"

definition qstepL :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> 'a" where
  "qstepL G x = node G (edge G (node G x))"

definition qstepR :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> 'a" where
  "qstepR G x = node G (edge G x)"

datatype quiz = Quiz question question

fun isQuizR :: "quiz \<Rightarrow> bool" where
  "isQuizR (Quiz q0 q1) \<longleftrightarrow> isQaskR q0 \<and> isQaskR q1"

fun flatqz :: "quiz \<Rightarrow> nat list" where
  "flatqz (Quiz q0 q1) = flatq q0 @ flatq q1"

fun flipqz :: "quiz \<Rightarrow> quiz" where
  "flipqz (Quiz (QaskR qa0 q01) (QaskR qa1 q10)) = Quiz (QaskR qa0 (flipq q10)) (QaskR qa1 (flipq q01))"
| "flipqz qz = qz"

fun walkq :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> question \<Rightarrow> 'a list" where
  "walkq G x Qask0 = []"
| "walkq G x (Qask1 qa) = [x]"
| "walkq G x (QaskL qa ql) = x # walkq G (qstepL G x) ql"
| "walkq G x (QaskR qa qr) = x # walkq G (qstepR G x) qr"
| "walkq G x (QaskLR qa ql qr) = x # walkq G (qstepL G x) ql @ walkq G (qstepR G x) qr"
| "walkq G x (QaskLL qa q) =
     edge G (node G (qstepL G x)) # walkq G (qstepL G (qstepL G x)) q"
| "walkq G x (QaskRR qa q) = qstepR G x # walkq G (qstepR G (qstepR G x)) q"

definition fitq :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> question \<Rightarrow> bool" where
  "fitq G x q \<longleftrightarrow> flatq q = map (arity G) (walkq G x q)"

lemma length_walkq: "length (walkq G x q) = length (flatq q)"
  by (induction q arbitrary: x) simp_all

fun walkqz :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> quiz \<Rightarrow> 'a list" where
  "walkqz G x (Quiz q0 q1) = walkq G x q0 @ walkq G (edge G x) q1"

lemma length_walkqz: "length (walkqz G x qz) = length (flatqz qz)"
  by (cases qz) (simp add: length_walkq)

definition fitqz :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> quiz \<Rightarrow> bool" where
  "fitqz G x qz \<longleftrightarrow> flatqz qz = map (arity G) (walkqz G x qz)"

lemma (in hypermap) walkq_D: "x \<in> D \<Longrightarrow> set (walkq G x q) \<subseteq> D"
  by (induction q arbitrary: x) (auto simp: qstepL_def qstepR_def)

lemma (in hypermap) walkqz_D: "x \<in> D \<Longrightarrow> set (walkqz G x qz) \<subseteq> D"
proof -
  assume x: "x \<in> D"
  have ex: "e x \<in> D" using x by simp
  show ?thesis using walkq_D[OF x] walkq_D[OF ex] by (cases qz) auto
qed

definition valid_quiz :: "'a hypermap \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> quiz \<Rightarrow> bool" where
  "valid_quiz G rc x0 qz \<longleftrightarrow> isQuizR qz \<and> fitqz G x0 qz \<and> simple G (walkqz G x0 qz) \<and>
     (\<forall>x \<in> darts G. fband G (walkqz G x0 qz) x \<longleftrightarrow> kernel G rc x)"

section \<open>Face indices\<close>

definition findex :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat" where
  "findex f y x = (LEAST k. (f ^^ k) y = x)"

context fperm
begin

lemma findex_mod: assumes n: "(f ^^ n) y = x" shows "findex f y x = n mod order f y"
proof -
  define m where "m = n mod order f y"
  have m: "(f ^^ m) y = x" using n by (simp add: m_def funpow_mod_order)
  have le: "findex f y x \<le> m" unfolding findex_def by (rule Least_le) (rule m)
  have k: "(f ^^ findex f y x) y = x" unfolding findex_def by (rule LeastI[of _ m]) (rule m)
  have "m < order f y" by (simp add: m_def)
  then show ?thesis using funpow_inj_order[of "findex f y x" y m] le k m by (simp add: m_def)
qed

lemma findex_iter: "fconnect f y x \<Longrightarrow> (f ^^ findex f y x) y = x"
  unfolding fconnect_def findex_def by (rule LeastI_ex)

lemma findex_lt: "fconnect f y x \<Longrightarrow> findex f y x < order f y"
proof -
  assume "fconnect f y x"
  then obtain n where "(f ^^ n) y = x" by (auto simp: fconnect_def)
  then show ?thesis by (simp add: findex_mod)
qed

lemma findex0: "findex f x x = 0"
  using findex_mod[of 0 x x] by simp

end

section \<open>Mirror image quizzes\<close>

lemma length_flatq_flip: "length (flatq (flipq q)) = length (flatq q)"
  by (induction q) simp_all

lemma fitq_append:
  "length l1 = length l2 \<Longrightarrow> (a1 @ b1 = map g (l1' @ l2')) \<longleftrightarrow> (a1 = map g l1' \<and> b1 = map g l2')"
  if "length a1 = length l1'" for a1 b1 l1 l2 l1' l2'
  using that by (auto simp: append_eq_append_conv)

context hypermap
begin

context
  assumes plainG: "plain G" and cubicG: "cubic G"
begin

lemma ee': "e (e x) = x" using plain_eq[OF plainG] .

lemma nnn': "n (n (n x)) = x"
proof (cases "x \<in> D")
  case True
  then show ?thesis using cubic_eq[OF cubicG] by blast
next
  case False
  then show ?thesis by simp
qed

lemma inv_n: "inv n x = n (n x)"
  using N.inv_f[of "n (n x)"] nnn'[of x] by simp

lemma nf: "n (f x) = e x"
  using edgeK[of "e x"] ee' by simp

lemma qstepL_mirror: "qstepL (mirror G) x = qstepR G x"
proof -
  have "qstepL (mirror G) x = inv n (f (n (inv n x)))" by (simp add: qstepL_def)
  also have "\<dots> = n (n (f x))" by (simp add: inv_n[symmetric])
  also have "\<dots> = n (e x)" by (simp add: nf)
  finally show ?thesis by (simp add: qstepR_def)
qed

lemma qstepR_mirror: "qstepR (mirror G) x = qstepL G x"
proof -
  have "qstepR (mirror G) x = inv n (f (n x))" by (simp add: qstepR_def)
  also have "\<dots> = n (n (f (n x)))" by (simp add: inv_n)
  also have "\<dots> = n (e (n x))" by (simp add: nf)
  finally show ?thesis by (simp add: qstepL_def)
qed

lemma arity_mirror': "arity (mirror G) x = arity G x"
  by (simp add: F.order_inv)

lemma arity_en: "arity G (e (n x)) = arity G x"
proof -
  have "cface (e (n x)) x" using fconnect_step[of f "e (n x)"] by (simp add: nodeK)
  then show ?thesis by (rule arity_cface)
qed

lemma fit_flip: "fitq G x (flipq q) \<longleftrightarrow> fitq (mirror G) x q"
proof (induction q arbitrary: x)
  case Qask0
  then show ?case by (simp add: fitq_def)
next
  case (Qask1 qa)
  then show ?case by (simp add: fitq_def arity_mirror' F.order_inv)
next
  case (QaskL qa ql)
  then show ?case by (simp add: fitq_def arity_mirror' F.order_inv qstepL_mirror)
next
  case (QaskR qa qr)
  then show ?case by (simp add: fitq_def arity_mirror' F.order_inv qstepR_mirror)
next
  case (QaskLR qa ql qr)
  have l1: "length (flatq (flipq qr)) = length (walkq G (qstepL G x) (flipq qr))"
    by (simp add: length_walkq)
  have l2: "length (flatq ql) = length (walkq (mirror G) (qstepL (mirror G) x) ql)"
    by (simp add: length_walkq)
  have "fitq G x (flipq (QaskLR qa ql qr)) \<longleftrightarrow>
        nat_of_qarity qa = arity G x \<and> fitq G (qstepL G x) (flipq qr) \<and> fitq G (qstepR G x) (flipq ql)"
    using l1 by (simp add: fitq_def append_eq_append_conv)
  also have "\<dots> \<longleftrightarrow> nat_of_qarity qa = arity G x \<and> fitq (mirror G) (qstepL G x) qr \<and>
        fitq (mirror G) (qstepR G x) ql"
    using QaskLR.IH by simp
  also have "\<dots> \<longleftrightarrow> fitq (mirror G) x (QaskLR qa ql qr)"
    using l2 by (auto simp: fitq_def append_eq_append_conv arity_mirror' F.order_inv qstepL_mirror qstepR_mirror)
  finally show ?case .
next
  case (QaskLL qa q)
  have "arity G (f (qstepR G x)) = arity G (qstepR G x)" by simp
  then show ?case using QaskLL.IH
    by (simp add: fitq_def arity_mirror' F.order_inv qstepL_mirror inv_n[symmetric])
next
  case (QaskRR qa q)
  have "arity G (e (n (qstepL G x))) = arity G (qstepL G x)" by (rule arity_en)
  then show ?case using QaskRR.IH
    by (simp add: fitq_def arity_mirror' F.order_inv qstepR_mirror)
qed

lemma fitqz_flip:
  assumes R: "isQuizR qz"
  shows "fitqz G x (flipqz qz) \<longleftrightarrow> fitqz (mirror G) (f x) qz"
proof -
  obtain qa0 q01 qa1 q10 where qz: "qz = Quiz (QaskR qa0 q01) (QaskR qa1 q10)"
  proof -
    obtain q0 q1 where qz0: "qz = Quiz q0 q1" by (cases qz)
    obtain qa0 q01 where "q0 = QaskR qa0 q01" using R qz0 by (cases q0) auto
    moreover obtain qa1 q10 where "q1 = QaskR qa1 q10" using R qz0 by (cases q1) auto
    ultimately show ?thesis using that qz0 by blast
  qed
  have s1: "qstepR (mirror G) (f x) = qstepR G (e x)"
  proof -
    have "qstepR (mirror G) (f x) = qstepL G (f x)" by (rule qstepR_mirror)
    also have "\<dots> = qstepR G (e x)" by (simp add: qstepL_def qstepR_def nf ee')
    finally show ?thesis .
  qed
  have s2: "qstepR (mirror G) (edge (mirror G) (f x)) = qstepR G x"
  proof -
    have "qstepR (mirror G) (edge (mirror G) (f x)) = qstepL G (edge (mirror G) (f x))"
      by (rule qstepR_mirror)
    also have "\<dots> = qstepR G x" by (simp add: qstepL_def qstepR_def nf edgeK ee')
    finally show ?thesis .
  qed
  have a1: "arity G (f (e x)) = arity G (e x)" by simp
  have l1: "length (flatq (flipq q10)) = length (walkq G (qstepR G x) (flipq q10))"
    by (simp add: length_walkq)
  have l2: "length (flatq q01) = length (walkq (mirror G) (qstepR G (e x)) q01)"
    by (simp add: length_walkq)
  have "fitqz G x (flipqz qz) \<longleftrightarrow> nat_of_qarity qa0 = arity G x \<and> fitq G (qstepR G x) (flipq q10) \<and>
     nat_of_qarity qa1 = arity G (e x) \<and> fitq G (qstepR G (e x)) (flipq q01)"
    using l1 by (simp add: qz fitqz_def fitq_def append_eq_append_conv)
  also have "\<dots> \<longleftrightarrow> nat_of_qarity qa0 = arity G x \<and> fitq (mirror G) (qstepR G x) q10 \<and>
     nat_of_qarity qa1 = arity G (e x) \<and> fitq (mirror G) (qstepR G (e x)) q01"
    by (simp add: fit_flip)
  also have "\<dots> \<longleftrightarrow> fitqz (mirror G) (f x) qz"
    using l2 s1 s2 a1 by (auto simp: qz fitqz_def fitq_def append_eq_append_conv arity_mirror' F.order_inv nf)
  finally show ?thesis .
qed

end

end

section \<open>The quiz embedding\<close>

definition nthd :: "'a \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a" where
  "nthd d l i = (if i < length l then l ! i else d)"

locale quiz_ctx =
  fixes Gm :: "'b hypermap" and Gc :: "'a hypermap" and rc :: "'a list"
    and x0m :: 'b and x0c :: 'a and qz :: quiz
  assumes hypGm: "hypermap Gm" and plainGm: "plain Gm" and cubicGm: "cubic Gm"
    and hypGc: "hypermap Gc" and plainGc: "plain Gc" and qcubicGc: "quasicubic Gc rc"
    and x0mD: "x0m \<in> darts Gm" and x0cD: "x0c \<in> darts Gc"
    and qz_ok: "valid_quiz Gc rc x0c qz" and qz_x0m: "fitqz Gm x0m qz"
begin

sublocale M: hypermap Gm by (rule hypGm)
sublocale C: hypermap Gc by (rule hypGc)

definition ac :: "'a set" where "ac = {x \<in> C.D. kernel Gc rc x}"

abbreviation s0c where "s0c \<equiv> walkqz Gc x0c qz"
abbreviation s0m where "s0m \<equiv> walkqz Gm x0m qz"

lemma e2c [simp]: "C.e (C.e x) = x" using C.plain_eq[OF plainGc] .
lemma e2m [simp]: "M.e (M.e x) = x" using M.plain_eq[OF plainGm] .
lemma n3m: "x \<in> M.D \<Longrightarrow> M.n (M.n (M.n x)) = x" using M.cubic_eq[OF cubicGm] .
lemma n3c: "x \<in> C.D \<Longrightarrow> x \<notin> set rc \<Longrightarrow> C.n (C.n (C.n x)) = x"
  using C.quasicubic_eq[OF qcubicGc] .

lemma qzR: "isQuizR qz" and fit_c: "fitqz Gc x0c qz" and simple_s0: "simple Gc s0c"
  and Dac: "x \<in> C.D \<Longrightarrow> fband Gc s0c x \<longleftrightarrow> x \<in> ac"
  using qz_ok by (auto simp: valid_quiz_def ac_def)

lemma s0c_D: "set s0c \<subseteq> C.D" by (rule C.walkqz_D[OF x0cD])
lemma s0m_D: "set s0m \<subseteq> M.D" by (rule M.walkqz_D[OF x0mD])
lemma len_s0: "length s0m = length s0c" by (simp add: length_walkqz)
lemma distinct_s0: "distinct s0c" using simple_s0 C.simple_distinct by blast

lemma ac_D: "x \<in> ac \<Longrightarrow> x \<in> C.D" by (simp add: ac_def)
lemma ac_rc: "x \<in> ac \<Longrightarrow> x \<notin> set rc" using C.kernel_off_ring by (simp add: ac_def)

lemma acF: "C.f x \<in> ac \<longleftrightarrow> x \<in> ac" by (simp add: ac_def kernel_def)

lemma ac_cface: "x \<in> ac \<Longrightarrow> C.cface x y \<Longrightarrow> y \<in> ac"
proof -
  assume x: "x \<in> ac" and xy: "C.cface x y"
  then obtain k where "y = (C.f ^^ k) x" by (auto simp: fconnect_def)
  then show ?thesis using x by (induction k arbitrary: y) (auto simp: acF)
qed

lemma s0_ac: "set s0c \<subseteq> ac"
  using Dac s0c_D C.fband_ring by blast

lemma arity_s0: "i < length s0c \<Longrightarrow> arity Gm (s0m ! i) = arity Gc (s0c ! i)"
proof -
  assume i: "i < length s0c"
  have "flatqz qz ! i = arity Gc (s0c ! i)" using fit_c i by (simp add: fitqz_def)
  moreover have "flatqz qz ! i = arity Gm (s0m ! i)" using qz_x0m i len_s0 by (simp add: fitqz_def)
  ultimately show ?thesis by simp
qed

definition idx :: "'a \<Rightarrow> nat" where
  "idx x = (if \<exists>i < length s0c. C.cface x (s0c ! i) then LEAST i. i < length s0c \<and> C.cface x (s0c ! i)
            else length s0c)"

definition h :: "'a \<Rightarrow> 'b" where
  "h x = (M.f ^^ findex C.f (nthd x0c s0c (idx x)) x) (nthd x0m s0m (idx x))"

lemma idx_ac: assumes x: "x \<in> ac"
  shows "idx x < length s0c" and "C.cface x (s0c ! idx x)"
proof -
  have "fband Gc s0c x" using Dac ac_D[OF x] x by simp
  then obtain y where "y \<in> set s0c" "C.cface x y" by (auto simp: fband_def)
  then have ex: "\<exists>i < length s0c. C.cface x (s0c ! i)" by (auto simp: in_set_conv_nth)
  have "idx x < length s0c \<and> C.cface x (s0c ! idx x)"
    unfolding idx_def using ex LeastI_ex[OF ex] by simp
  then show "idx x < length s0c" and "C.cface x (s0c ! idx x)" by simp_all
qed

lemma idx_cface: "C.cface x y \<Longrightarrow> idx x = idx y"
proof -
  assume xy: "C.cface x y"
  have "C.cface x z \<longleftrightarrow> C.cface y z" for z
    using fconnect_trans[OF xy] fconnect_trans[OF C.F.fconnect_sym[OF xy]] by blast
  then have "C.cface x = C.cface y" by (rule ext)
  then show ?thesis unfolding idx_def by (simp only:)
qed

lemma idx_s0: assumes i: "i < length s0c" shows "idx (s0c ! i) = i"
proof -
  have own: "C.cface (s0c ! i) (s0c ! i)" by simp
  have ex: "\<exists>j < length s0c. C.cface (s0c ! i) (s0c ! j)" using i own by blast
  have le: "(LEAST j. j < length s0c \<and> C.cface (s0c ! i) (s0c ! j)) \<le> i"
    by (rule Least_le) (simp add: i)
  define j where "j = (LEAST j. j < length s0c \<and> C.cface (s0c ! i) (s0c ! j))"
  have j: "j < length s0c \<and> C.cface (s0c ! i) (s0c ! j)" unfolding j_def by (rule LeastI_ex[OF ex])
  have "s0c ! i = s0c ! j"
    by (rule C.simple_cface[OF simple_s0]) (use i j in auto)
  then have "j = i" using distinct_s0 i j nth_eq_iff_index_eq by blast
  then show ?thesis unfolding idx_def using ex j_def by simp
qed

lemma Dhs0: assumes i: "i < length s0c" shows "h (s0c ! i) = s0m ! i"
  using i len_s0 by (simp add: h_def idx_s0 nthd_def C.F.findex0)

lemma Dhx0: "h x0c = x0m"
proof -
  obtain q0 q1 where qz: "qz = Quiz q0 q1" by (cases qz)
  obtain qa q where q0: "q0 = QaskR qa q" using qzR qz by (cases q0) auto
  have "0 < length s0c" "s0c ! 0 = x0c" "s0m ! 0 = x0m" by (simp_all add: qz q0)
  then show ?thesis using Dhs0[of 0] by simp
qed

lemma Dhex0: "h (C.e x0c) = M.e x0m"
proof -
  obtain q0 q1 where qz: "qz = Quiz q0 q1" by (cases qz)
  obtain qa q where q0: "q0 = QaskR qa q" using qzR qz by (cases q0) auto
  obtain qa' q' where q1: "q1 = QaskR qa' q'" using qzR qz by (cases q1) auto
  define i where "i = length (walkq Gc x0c q0)"
  have i: "i < length s0c" by (simp add: qz q1 i_def)
  have "s0c ! i = C.e x0c" by (simp add: qz q1 i_def nth_append)
  moreover have "s0m ! i = M.e x0m" by (simp add: qz q1 i_def nth_append length_walkq)
  ultimately show ?thesis using Dhs0[OF i] by simp
qed

lemma h_ac: assumes x: "x \<in> ac"
  shows "h x = (M.f ^^ findex C.f (s0c ! idx x) x) (s0m ! idx x)"
  using idx_ac[OF x] len_s0 by (simp add: h_def nthd_def)

lemma embedqz_arity: assumes x: "x \<in> ac" shows "arity Gm (h x) = arity Gc x"
proof -
  have i: "idx x < length s0c" and xy: "C.cface x (s0c ! idx x)" using idx_ac[OF x] by simp_all
  have "arity Gm (h x) = arity Gm (s0m ! idx x)" by (simp add: h_ac[OF x])
  also have "\<dots> = arity Gc (s0c ! idx x)" by (rule arity_s0[OF i])
  also have "\<dots> = arity Gc x" using C.arity_cface[OF xy] by simp
  finally show ?thesis .
qed

lemma embedqz_face: assumes x: "x \<in> ac" shows "h (C.f x) = M.f (h x)"
proof -
  define y where "y = s0c ! idx x"
  have i: "idx x < length s0c" and xy: "C.cface x y" using idx_ac[OF x] by (simp_all add: y_def)
  have yx: "C.cface y x" by (rule C.F.fconnect_sym[OF xy])
  have ifx: "idx (C.f x) = idx x" using idx_cface[of "C.f x" x] by simp
  have fx: "C.f x \<in> ac" using x acF by simp
  define k where "k = findex C.f y x"
  have k: "(C.f ^^ k) y = x" unfolding k_def by (rule C.F.findex_iter[OF yx])
  have "(C.f ^^ Suc k) y = C.f x" using k by simp
  then have k1: "findex C.f y (C.f x) = Suc k mod order C.f y" by (rule C.F.findex_mod)
  have ord: "order M.f (s0m ! idx x) = order C.f y" using arity_s0[OF i] by (simp add: y_def)
  have "h (C.f x) = (M.f ^^ (Suc k mod order C.f y)) (s0m ! idx x)"
    using h_ac[OF fx] ifx k1 by (simp add: y_def)
  also have "\<dots> = (M.f ^^ Suc k) (s0m ! idx x)" using M.F.funpow_mod_order ord by metis
  also have "\<dots> = M.f (h x)" using h_ac[OF x] by (simp add: k_def y_def)
  finally show ?thesis .
qed

section \<open>Edge centrality along the quiz walk\<close>

abbreviation hc :: "'a \<Rightarrow> bool" where "hc \<equiv> edge_central Gc Gm h"

lemma hcE: "hc (C.e x) \<longleftrightarrow> hc x"
  using edge_central_edge[OF hypGc hypGm plainGc plainGm] .

lemma h_D: assumes x: "x \<in> ac" shows "h x \<in> M.D"
proof -
  have "s0m ! idx x \<in> M.D" using idx_ac[OF x] len_s0 s0m_D by auto
  then show ?thesis by (simp add: h_ac[OF x])
qed

lemma ac_en: "z \<in> ac \<Longrightarrow> C.e (C.n z) \<in> ac"
  using acF[of "C.e (C.n z)"] by (simp add: C.nodeK)

lemma hEN: assumes z: "z \<in> ac" shows "h (C.e (C.n z)) = M.e (M.n (h z))"
proof -
  have "M.f (h (C.e (C.n z))) = h z" using embedqz_face[OF ac_en[OF z]] by (simp add: C.nodeK)
  also have "\<dots> = M.f (M.e (M.n (h z)))" by (simp add: M.nodeK)
  finally show ?thesis by simp
qed

lemma fe_C: assumes x: "x \<in> ac" shows "C.f (C.e x) = C.n (C.n x)"
proof -
  have "C.f (C.e (C.n (C.n (C.n x)))) = C.n (C.n x)" by (rule C.nodeK)
  then show ?thesis using n3c[OF ac_D[OF x] ac_rc[OF x]] by simp
qed

lemma fe_M: assumes y: "y \<in> M.D" shows "M.f (M.e y) = M.n (M.n y)"
proof -
  have "M.f (M.e (M.n (M.n (M.n y)))) = M.n (M.n y)" by (rule M.nodeK)
  then show ?thesis using n3m[OF y] by simp
qed

lemma hN2: assumes x: "x \<in> ac" and ex: "C.e x \<in> ac" and hx: "hc x"
  shows "h (C.n (C.n x)) = M.n (M.n (h x))"
proof -
  have "h (C.n (C.n x)) = h (C.f (C.e x))" using fe_C[OF x] by simp
  also have "\<dots> = M.f (M.e (h x))" using embedqz_face[OF ex] hx by (simp add: edge_central_def)
  also have "\<dots> = M.n (M.n (h x))" by (rule fe_M[OF h_D[OF x]])
  finally show ?thesis .
qed

lemma L1: assumes x: "x \<in> ac" and hnx: "h (C.n x) = M.n (h x)" shows "hc (C.n x)"
  using hEN[OF x] hnx by (simp add: edge_central_def)

lemma nn_ac: "x \<in> ac \<Longrightarrow> C.e x \<in> ac \<Longrightarrow> C.n (C.n x) \<in> ac"
  using fe_C acF by metis

lemma hc_walk:
  "x \<in> ac \<Longrightarrow> C.e x \<in> ac \<Longrightarrow> hc x \<Longrightarrow> set (walkq Gc (C.n x) q) \<subseteq> ac \<Longrightarrow>
   map h (walkq Gc (C.n x) q) = walkq Gm (M.n (h x)) q \<Longrightarrow> \<forall>z \<in> set (walkq Gc (C.n x) q). hc z"
proof (induction q arbitrary: x)
  case Qask0
  then show ?case by simp
next
  case (Qask1 qa)
  then show ?case using L1 by simp
next
  case (QaskL qa ql)
  note x = QaskL.prems(1) and ex = QaskL.prems(2) and hx = QaskL.prems(3)
  have nx: "C.n x \<in> ac" using QaskL.prems(4) by simp
  have hnx: "h (C.n x) = M.n (h x)" using QaskL.prems(5) by simp
  define x' where "x' = C.e (C.n (C.n x))"
  have nnx: "C.n (C.n x) \<in> ac" by (rule nn_ac[OF x ex])
  have x': "x' \<in> ac" unfolding x'_def by (rule ac_en[OF nx])
  have ex': "C.e x' \<in> ac" using nnx by (simp add: x'_def)
  have hnn: "h (C.n (C.n x)) = M.n (M.n (h x))" by (rule hN2[OF x ex hx])
  have hx'v: "h x' = M.e (M.n (M.n (h x)))" using hEN[OF nx] hnx by (simp add: x'_def)
  have hx': "hc x'" using hx'v hnn by (simp add: edge_central_def x'_def)
  have st: "qstepL Gc (C.n x) = C.n x'" by (simp add: qstepL_def x'_def)
  have stm: "qstepL Gm (M.n (h x)) = M.n (h x')" by (simp add: qstepL_def hx'v)
  have IH: "\<forall>z \<in> set (walkq Gc (C.n x') ql). hc z"
    by (rule QaskL.IH[OF x' ex' hx']) (use QaskL.prems(4,5) st stm in simp_all)
  show ?case using IH L1[OF x hnx] st by simp
next
  case (QaskR qa qr)
  note x = QaskR.prems(1) and ex = QaskR.prems(2) and hx = QaskR.prems(3)
  have nx: "C.n x \<in> ac" using QaskR.prems(4) by simp
  have hnx: "h (C.n x) = M.n (h x)" using QaskR.prems(5) by simp
  define x' where "x' = C.e (C.n x)"
  have x': "x' \<in> ac" unfolding x'_def by (rule ac_en[OF x])
  have ex': "C.e x' \<in> ac" using nx by (simp add: x'_def)
  have hcn: "hc (C.n x)" by (rule L1[OF x hnx])
  have hx': "hc x'" using hcn hcE by (simp add: x'_def)
  have hx'v: "h x' = M.e (M.n (h x))" using hEN[OF x] by (simp add: x'_def)
  have st: "qstepR Gc (C.n x) = C.n x'" by (simp add: qstepR_def x'_def)
  have stm: "qstepR Gm (M.n (h x)) = M.n (h x')" by (simp add: qstepR_def hx'v)
  have IH: "\<forall>z \<in> set (walkq Gc (C.n x') qr). hc z"
    by (rule QaskR.IH[OF x' ex' hx']) (use QaskR.prems(4,5) st stm in simp_all)
  show ?case using IH hcn st by simp
next
  case (QaskLR qa ql qr)
  note x = QaskLR.prems(1) and ex = QaskLR.prems(2) and hx = QaskLR.prems(3)
  have nx: "C.n x \<in> ac" using QaskLR.prems(4) by simp
  have hnx: "h (C.n x) = M.n (h x)" using QaskLR.prems(5) by simp
  have hcn: "hc (C.n x)" by (rule L1[OF x hnx])
  have eqs: "map h (walkq Gc (qstepL Gc (C.n x)) ql) = walkq Gm (qstepL Gm (M.n (h x))) ql \<and>
             map h (walkq Gc (qstepR Gc (C.n x)) qr) = walkq Gm (qstepR Gm (M.n (h x))) qr"
    using QaskLR.prems(5) by (simp add: map_append append_eq_append_conv length_walkq)
  define xl where "xl = C.e (C.n (C.n x))"
  have nnx: "C.n (C.n x) \<in> ac" by (rule nn_ac[OF x ex])
  have xl: "xl \<in> ac" unfolding xl_def by (rule ac_en[OF nx])
  have exl: "C.e xl \<in> ac" using nnx by (simp add: xl_def)
  have hnn: "h (C.n (C.n x)) = M.n (M.n (h x))" by (rule hN2[OF x ex hx])
  have hxlv: "h xl = M.e (M.n (M.n (h x)))" using hEN[OF nx] hnx by (simp add: xl_def)
  have hxl: "hc xl" using hxlv hnn by (simp add: edge_central_def xl_def)
  have stl: "qstepL Gc (C.n x) = C.n xl" by (simp add: qstepL_def xl_def)
  have stlm: "qstepL Gm (M.n (h x)) = M.n (h xl)" by (simp add: qstepL_def hxlv)
  have IHl: "\<forall>z \<in> set (walkq Gc (C.n xl) ql). hc z"
    by (rule QaskLR.IH(1)[OF xl exl hxl]) (use QaskLR.prems(4) eqs stl stlm in simp_all)
  define xr where "xr = C.e (C.n x)"
  have xr: "xr \<in> ac" unfolding xr_def by (rule ac_en[OF x])
  have exr: "C.e xr \<in> ac" using nx by (simp add: xr_def)
  have hxr: "hc xr" using hcn hcE by (simp add: xr_def)
  have hxrv: "h xr = M.e (M.n (h x))" using hEN[OF x] by (simp add: xr_def)
  have str: "qstepR Gc (C.n x) = C.n xr" by (simp add: qstepR_def xr_def)
  have strm: "qstepR Gm (M.n (h x)) = M.n (h xr)" by (simp add: qstepR_def hxrv)
  have IHr: "\<forall>z \<in> set (walkq Gc (C.n xr) qr). hc z"
    by (rule QaskLR.IH(2)[OF xr exr hxr]) (use QaskLR.prems(4) eqs str strm in simp_all)
  show ?case using IHl IHr hcn stl str by auto
next
  case (QaskLL qa q)
  note x = QaskLL.prems(1) and ex = QaskLL.prems(2) and hx = QaskLL.prems(3)
  define z where "z = C.f (C.e x)"
  have zac: "z \<in> ac" using ex acF by (simp add: z_def)
  have nnx: "C.n (C.n x) = z" using fe_C[OF x] by (simp add: z_def)
  define x' where "x' = C.e (C.n (qstepL Gc (C.n x)))"
  have x': "x' \<in> ac" using QaskLL.prems(4) by (simp add: x'_def)
  have nfz: "C.n (C.f z) = C.e z" using C.edgeK[of "C.e z"] by simp
  have fzac: "C.f z \<in> ac" using zac acF by simp
  have "C.n (C.n (C.e z)) = C.n (C.n (C.n (C.f z)))" using nfz by simp
  also have "\<dots> = C.f z" by (rule n3c[OF ac_D[OF fzac] ac_rc[OF fzac]])
  finally have nnez: "C.n (C.n (C.e z)) = C.f z" .
  have ex'v: "C.e x' = C.f z" using nnx nnez by (simp add: x'_def qstepL_def)
  have ex': "C.e x' \<in> ac" using ex'v fzac by simp
  have hx'v: "h x' = M.e (M.n (qstepL Gm (M.n (h x))))" using QaskLL.prems(5) by (simp add: x'_def)
  have hxD: "h x \<in> M.D" by (rule h_D[OF x])
  have "h (C.e x') = M.f (M.f (M.e (h x)))"
    using ex'v embedqz_face[OF zac] embedqz_face[OF ex] hx by (simp add: z_def edge_central_def)
  also have "\<dots> = M.n (qstepL Gm (M.n (h x)))"
  proof -
    define y where "y = M.f (M.e (h x))"
    have yD: "y \<in> M.D" using hxD by (simp add: y_def)
    have ny: "M.n (M.n (h x)) = y" using fe_M[OF hxD] by (simp add: y_def)
    have nfy: "M.n (M.f y) = M.e y" using M.edgeK[of "M.e y"] by simp
    have fyD: "M.f y \<in> M.D" using yD by simp
    have "M.n (M.n (M.e y)) = M.n (M.n (M.n (M.f y)))" using nfy by simp
    also have "\<dots> = M.f y" by (rule n3m[OF fyD])
    finally have "M.n (M.n (M.e y)) = M.f y" .
    then show ?thesis using ny by (simp add: qstepL_def y_def)
  qed
  finally have hx': "hc x'" using hx'v by (simp add: edge_central_def)
  have st: "qstepL Gc (qstepL Gc (C.n x)) = C.n x'" by (simp add: qstepL_def x'_def)
  have stm: "qstepL Gm (qstepL Gm (M.n (h x))) = M.n (h x')" by (simp add: qstepL_def hx'v)
  have IH: "\<forall>z \<in> set (walkq Gc (C.n x') q). hc z"
    by (rule QaskLL.IH[OF x' ex' hx']) (use QaskLL.prems(4,5) st stm in simp_all)
  show ?case using IH hx' st by (simp add: x'_def)
next
  case (QaskRR qa q)
  note x = QaskRR.prems(1) and ex = QaskRR.prems(2) and hx = QaskRR.prems(3)
  define x' where "x' = qstepR Gc (C.n x)"
  have x': "x' \<in> ac" using QaskRR.prems(4) by (simp add: x'_def)
  have hx'v: "h x' = qstepR Gm (M.n (h x))" using QaskRR.prems(5) by (simp add: x'_def)
  define x'' where "x'' = C.e x'"
  have enx: "C.e (C.n x) \<in> ac" by (rule ac_en[OF x])
  have x'': "x'' \<in> ac" using acF[of x''] enx by (simp add: x''_def x'_def qstepR_def C.nodeK)
  have ex'': "C.e x'' \<in> ac" using x' by (simp add: x''_def)
  have hxD: "h x \<in> M.D" by (rule h_D[OF x])
  have "M.f (h (C.e x')) = h (C.e (C.n x))"
    using embedqz_face[OF x''] by (simp add: x''_def x'_def qstepR_def C.nodeK)
  also have "\<dots> = M.e (M.n (h x))" by (rule hEN[OF x])
  also have "\<dots> = M.f (M.e (h x'))" using M.nodeK[of "M.e (M.n (h x))"] hx'v by (simp add: qstepR_def)
  finally have hcx': "hc x'" by (simp add: edge_central_def)
  have hx'': "hc x''" using hcx' hcE by (simp add: x''_def)
  have hx''v: "h x'' = M.e (h x')" using hcx' by (simp add: edge_central_def x''_def)
  have st: "qstepR Gc (qstepR Gc (C.n x)) = C.n x''" by (simp add: qstepR_def x''_def x'_def)
  have stm: "qstepR Gm (qstepR Gm (M.n (h x))) = M.n (h x'')" by (simp add: qstepR_def hx''v hx'v)
  have IH: "\<forall>z \<in> set (walkq Gc (C.n x'') q). hc z"
    by (rule QaskRR.IH[OF x'' ex'' hx'']) (use QaskRR.prems(4,5) st stm in simp_all)
  show ?case using IH hcx' st by (simp add: x'_def)
qed

lemma Ehs0: "map h s0c = s0m"
  by (rule nth_equalityI) (simp_all add: len_s0 Dhs0)

lemma embedqz_central: "z \<in> set s0c \<Longrightarrow> hc z"
proof -
  assume zs: "z \<in> set s0c"
  obtain q0 q1 where qz: "qz = Quiz q0 q1" by (cases qz)
  obtain qa0 q01 where q0: "q0 = QaskR qa0 q01" using qzR qz by (cases q0) auto
  obtain qa1 q10 where q1: "q1 = QaskR qa1 q10" using qzR qz by (cases q1) auto
  have x0: "x0c \<in> ac" and ex0: "C.e x0c \<in> ac" using s0_ac by (auto simp: qz q0 q1)
  have hc0: "hc x0c" using Dhx0 Dhex0 by (simp add: edge_central_def)
  have hce0: "hc (C.e x0c)" using hc0 hcE by simp
  have s0: "s0c = x0c # walkq Gc (C.n (C.e x0c)) q01 @ C.e x0c # walkq Gc (C.n x0c) q10"
    by (simp add: qz q0 q1 qstepR_def)
  have m0: "s0m = x0m # walkq Gm (M.n (M.e x0m)) q01 @ M.e x0m # walkq Gm (M.n x0m) q10"
    by (simp add: qz q0 q1 qstepR_def)
  have eqs: "map h (walkq Gc (C.n (C.e x0c)) q01) = walkq Gm (M.n (h (C.e x0c))) q01 \<and>
             map h (walkq Gc (C.n x0c) q10) = walkq Gm (M.n (h x0c)) q10"
    using Ehs0 Dhx0 Dhex0 unfolding s0 m0 by (simp add: append_eq_append_conv length_walkq)
  have A: "\<forall>z \<in> set (walkq Gc (C.n (C.e x0c)) q01). hc z"
    by (rule hc_walk[OF ex0]) (use x0 hce0 eqs s0_ac s0 in auto)
  have B: "\<forall>z \<in> set (walkq Gc (C.n x0c) q10). hc z"
    by (rule hc_walk[OF x0]) (use ex0 hc0 eqs s0_ac s0 in auto)
  show ?thesis using zs A B hc0 hce0 s0 by auto
qed

section \<open>Rlink connectivity of the central kernel\<close>

definition A :: "'a \<Rightarrow> bool" where "A z \<longleftrightarrow> z \<in> ac \<and> hc z"

definition rl :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "rl x y \<longleftrightarrow> (\<exists>p. path (rlink Gc) (C.n (C.f x)) (p @ [y]) \<and> (\<forall>z \<in> set p. A z))"

lemma rlink_cface: "rlink Gc a y \<Longrightarrow> C.cface y w \<Longrightarrow> rlink Gc a w"
  unfolding rlink_def by (rule fconnect_trans)

lemma rl_face: "C.cface x y \<Longrightarrow> rl x y"
  unfolding rl_def by (intro exI[of _ "[]"]) (simp add: rlink_def C.faceK)

lemma rl_trans: assumes xy: "rl x y" and yz: "rl y z" shows "rl x z"
proof -
  obtain p1 where p1: "path (rlink Gc) (C.n (C.f x)) (p1 @ [y])" and a1: "\<forall>w \<in> set p1. A w"
    using xy by (auto simp: rl_def)
  obtain p2 where p2: "path (rlink Gc) (C.n (C.f y)) (p2 @ [z])" and a2: "\<forall>w \<in> set p2. A w"
    using yz by (auto simp: rl_def)
  have pa: "path (rlink Gc) (C.n (C.f x)) p1" and ly: "rlink Gc (lastd (C.n (C.f x)) p1) y"
    using p1 by simp_all
  show ?thesis
  proof (cases p2)
    case Nil
    then have "C.cface y z" using p2 by (simp add: rlink_def C.faceK)
    then have "rlink Gc (lastd (C.n (C.f x)) p1) z" by (rule rlink_cface[OF ly])
    then show ?thesis unfolding rl_def using pa a1 by (intro exI[of _ p1]) simp
  next
    case (Cons q1 q2)
    have "C.cface y q1" using p2 Cons by (simp add: rlink_def C.faceK)
    then have j: "rlink Gc (lastd (C.n (C.f x)) p1) q1" by (rule rlink_cface[OF ly])
    have rest: "path (rlink Gc) q1 (q2 @ [z])" using p2 Cons by simp
    show ?thesis unfolding rl_def
      by (intro exI[of _ "p1 @ p2"]) (use pa j rest a1 a2 Cons in auto)
  qed
qed

lemma rl_edge: "A x \<Longrightarrow> rl x (C.e x)"
  unfolding rl_def by (intro exI[of _ "[x]"]) (simp add: rlink_def C.faceK)

definition conn :: "'a \<Rightarrow> bool" where "conn z \<longleftrightarrow> rl x0c z \<and> rl z x0c"

lemma conn_face: "C.cface u v \<Longrightarrow> conn u \<Longrightarrow> conn v"
  unfolding conn_def using rl_face rl_trans C.F.fconnect_sym by metis

lemma conn_edge: assumes "A u" "A (C.e u)" "conn u" shows "conn (C.e u)"
proof -
  have "rl (C.e u) (C.e (C.e u))" by (rule rl_edge[OF assms(2)])
  then have "rl (C.e u) u" by simp
  then show ?thesis using assms rl_edge rl_trans unfolding conn_def by metis
qed

lemma conn_node: assumes u: "u \<in> ac" and nu: "A (C.n u)" and cu: "conn u" shows "conn (C.n u)"
proof -
  define w where "w = C.e (C.n u)"
  have wac: "w \<in> ac" unfolding w_def by (rule ac_en[OF u])
  have Aw: "A w" using wac nu hcE by (simp add: A_def w_def)
  have "C.cface w u" using fconnect_step[of C.f w] by (simp add: w_def C.nodeK)
  then have "C.cface u w" by (rule C.F.fconnect_sym)
  then have cw: "conn w" by (rule conn_face[OF _ cu])
  have Aew: "A (C.e w)" using nu by (simp add: w_def)
  have "conn (C.e w)" by (rule conn_edge[OF Aw Aew cw])
  then show ?thesis by (simp add: w_def)
qed

lemma A_walk:
  "x \<in> ac \<Longrightarrow> C.e x \<in> ac \<Longrightarrow> hc x \<Longrightarrow> set (walkq Gc (C.n x) q) \<subseteq> ac \<Longrightarrow>
   map h (walkq Gc (C.n x) q) = walkq Gm (M.n (h x)) q \<Longrightarrow> \<forall>z \<in> set (walkq Gc (C.n x) q). A z"
proof -
  assume a: "x \<in> ac" "C.e x \<in> ac" "hc x" and s: "set (walkq Gc (C.n x) q) \<subseteq> ac"
    and m: "map h (walkq Gc (C.n x) q) = walkq Gm (M.n (h x)) q"
  have "\<forall>z \<in> set (walkq Gc (C.n x) q). hc z" by (rule hc_walk[OF a s m])
  then show ?thesis using s unfolding A_def by blast
qed

lemma conn_walk:
  "x \<in> ac \<Longrightarrow> C.e x \<in> ac \<Longrightarrow> hc x \<Longrightarrow> conn x \<Longrightarrow> set (walkq Gc (C.n x) q) \<subseteq> ac \<Longrightarrow>
   map h (walkq Gc (C.n x) q) = walkq Gm (M.n (h x)) q \<Longrightarrow> \<forall>z \<in> set (walkq Gc (C.n x) q). conn z"
proof (induction q arbitrary: x)
  case Qask0
  then show ?case by simp
next
  case (Qask1 qa)
  have "A (C.n x)" using A_walk[OF Qask1.prems(1,2,3,5,6)] by simp
  then show ?case using conn_node[OF Qask1.prems(1) _ Qask1.prems(4)] by simp
next
  case (QaskL qa ql)
  note x = QaskL.prems(1) and ex = QaskL.prems(2) and hx = QaskL.prems(3) and cx = QaskL.prems(4)
  have Aw: "\<forall>z \<in> set (walkq Gc (C.n x) (QaskL qa ql)). A z" by (rule A_walk[OF x ex hx QaskL.prems(5,6)])
  have nx: "C.n x \<in> ac" using QaskL.prems(5) by simp
  have hnx: "h (C.n x) = M.n (h x)" using QaskL.prems(6) by simp
  have cnx: "conn (C.n x)" using conn_node[OF x _ cx] Aw by simp
  define x' where "x' = C.e (C.n (C.n x))"
  have nnx: "C.n (C.n x) \<in> ac" by (rule nn_ac[OF x ex])
  have x': "x' \<in> ac" unfolding x'_def by (rule ac_en[OF nx])
  have ex': "C.e x' \<in> ac" using nnx by (simp add: x'_def)
  have hnn: "h (C.n (C.n x)) = M.n (M.n (h x))" by (rule hN2[OF x ex hx])
  have hx'v: "h x' = M.e (M.n (M.n (h x)))" using hEN[OF nx] hnx by (simp add: x'_def)
  have hx': "hc x'" using hx'v hnn by (simp add: edge_central_def x'_def)
  have "C.cface x' (C.n x)" using fconnect_step[of C.f x'] by (simp add: x'_def C.nodeK)
  then have cx': "conn x'" using conn_face C.F.fconnect_sym cnx by metis
  have st: "qstepL Gc (C.n x) = C.n x'" by (simp add: qstepL_def x'_def)
  have stm: "qstepL Gm (M.n (h x)) = M.n (h x')" by (simp add: qstepL_def hx'v)
  have IH: "\<forall>z \<in> set (walkq Gc (C.n x') ql). conn z"
    by (rule QaskL.IH[OF x' ex' hx' cx']) (use QaskL.prems(5,6) st stm in simp_all)
  show ?case using IH cnx st by simp
next
  case (QaskR qa qr)
  note x = QaskR.prems(1) and ex = QaskR.prems(2) and hx = QaskR.prems(3) and cx = QaskR.prems(4)
  have Aw: "\<forall>z \<in> set (walkq Gc (C.n x) (QaskR qa qr)). A z" by (rule A_walk[OF x ex hx QaskR.prems(5,6)])
  have nx: "C.n x \<in> ac" using QaskR.prems(5) by simp
  have hnx: "h (C.n x) = M.n (h x)" using QaskR.prems(6) by simp
  have cnx: "conn (C.n x)" using conn_node[OF x _ cx] Aw by simp
  define x' where "x' = C.e (C.n x)"
  have x': "x' \<in> ac" unfolding x'_def by (rule ac_en[OF x])
  have ex': "C.e x' \<in> ac" using nx by (simp add: x'_def)
  have hcn: "hc (C.n x)" by (rule L1[OF x hnx])
  have hx': "hc x'" using hcn hcE by (simp add: x'_def)
  have hx'v: "h x' = M.e (M.n (h x))" using hEN[OF x] by (simp add: x'_def)
  have "C.cface x' x" using fconnect_step[of C.f x'] by (simp add: x'_def C.nodeK)
  then have cx': "conn x'" using conn_face C.F.fconnect_sym cx by metis
  have st: "qstepR Gc (C.n x) = C.n x'" by (simp add: qstepR_def x'_def)
  have stm: "qstepR Gm (M.n (h x)) = M.n (h x')" by (simp add: qstepR_def hx'v)
  have IH: "\<forall>z \<in> set (walkq Gc (C.n x') qr). conn z"
    by (rule QaskR.IH[OF x' ex' hx' cx']) (use QaskR.prems(5,6) st stm in simp_all)
  show ?case using IH cnx st by simp
next
  case (QaskLR qa ql qr)
  note x = QaskLR.prems(1) and ex = QaskLR.prems(2) and hx = QaskLR.prems(3) and cx = QaskLR.prems(4)
  have Aw: "\<forall>z \<in> set (walkq Gc (C.n x) (QaskLR qa ql qr)). A z"
    by (rule A_walk[OF x ex hx QaskLR.prems(5,6)])
  have nx: "C.n x \<in> ac" using QaskLR.prems(5) by simp
  have hnx: "h (C.n x) = M.n (h x)" using QaskLR.prems(6) by simp
  have cnx: "conn (C.n x)" using conn_node[OF x _ cx] Aw by simp
  have hcn: "hc (C.n x)" by (rule L1[OF x hnx])
  have eqs: "map h (walkq Gc (qstepL Gc (C.n x)) ql) = walkq Gm (qstepL Gm (M.n (h x))) ql \<and>
             map h (walkq Gc (qstepR Gc (C.n x)) qr) = walkq Gm (qstepR Gm (M.n (h x))) qr"
    using QaskLR.prems(6) by (simp add: map_append append_eq_append_conv length_walkq)
  define xl where "xl = C.e (C.n (C.n x))"
  have nnx: "C.n (C.n x) \<in> ac" by (rule nn_ac[OF x ex])
  have xl: "xl \<in> ac" unfolding xl_def by (rule ac_en[OF nx])
  have exl: "C.e xl \<in> ac" using nnx by (simp add: xl_def)
  have hnn: "h (C.n (C.n x)) = M.n (M.n (h x))" by (rule hN2[OF x ex hx])
  have hxlv: "h xl = M.e (M.n (M.n (h x)))" using hEN[OF nx] hnx by (simp add: xl_def)
  have hxl: "hc xl" using hxlv hnn by (simp add: edge_central_def xl_def)
  have "C.cface xl (C.n x)" using fconnect_step[of C.f xl] by (simp add: xl_def C.nodeK)
  then have cxl: "conn xl" using conn_face C.F.fconnect_sym cnx by metis
  have stl: "qstepL Gc (C.n x) = C.n xl" by (simp add: qstepL_def xl_def)
  have stlm: "qstepL Gm (M.n (h x)) = M.n (h xl)" by (simp add: qstepL_def hxlv)
  have IHl: "\<forall>z \<in> set (walkq Gc (C.n xl) ql). conn z"
    by (rule QaskLR.IH(1)[OF xl exl hxl cxl]) (use QaskLR.prems(5) eqs stl stlm in simp_all)
  define xr where "xr = C.e (C.n x)"
  have xr: "xr \<in> ac" unfolding xr_def by (rule ac_en[OF x])
  have exr: "C.e xr \<in> ac" using nx by (simp add: xr_def)
  have hxr: "hc xr" using hcn hcE by (simp add: xr_def)
  have hxrv: "h xr = M.e (M.n (h x))" using hEN[OF x] by (simp add: xr_def)
  have "C.cface xr x" using fconnect_step[of C.f xr] by (simp add: xr_def C.nodeK)
  then have cxr: "conn xr" using conn_face C.F.fconnect_sym cx by metis
  have str: "qstepR Gc (C.n x) = C.n xr" by (simp add: qstepR_def xr_def)
  have strm: "qstepR Gm (M.n (h x)) = M.n (h xr)" by (simp add: qstepR_def hxrv)
  have IHr: "\<forall>z \<in> set (walkq Gc (C.n xr) qr). conn z"
    by (rule QaskLR.IH(2)[OF xr exr hxr cxr]) (use QaskLR.prems(5) eqs str strm in simp_all)
  show ?case using IHl IHr cnx stl str by auto
next
  case (QaskLL qa q)
  note x = QaskLL.prems(1) and ex = QaskLL.prems(2) and hx = QaskLL.prems(3) and cx = QaskLL.prems(4)
  have Aw: "\<forall>z \<in> set (walkq Gc (C.n x) (QaskLL qa q)). A z"
    by (rule A_walk[OF x ex hx QaskLL.prems(5,6)])
  define z where "z = C.f (C.e x)"
  have zac: "z \<in> ac" using ex acF by (simp add: z_def)
  have nnx: "C.n (C.n x) = z" using fe_C[OF x] by (simp add: z_def)
  define x' where "x' = C.e (C.n (qstepL Gc (C.n x)))"
  have x': "x' \<in> ac" using QaskLL.prems(5) by (simp add: x'_def)
  have Ax': "A x'" using Aw by (simp add: x'_def)
  have nfz: "C.n (C.f z) = C.e z" using C.edgeK[of "C.e z"] by simp
  have fzac: "C.f z \<in> ac" using zac acF by simp
  have "C.n (C.n (C.e z)) = C.n (C.n (C.n (C.f z)))" using nfz by simp
  also have "\<dots> = C.f z" by (rule n3c[OF ac_D[OF fzac] ac_rc[OF fzac]])
  finally have nnez: "C.n (C.n (C.e z)) = C.f z" .
  have ex'v: "C.e x' = C.f z" using nnx nnez by (simp add: x'_def qstepL_def)
  have ex': "C.e x' \<in> ac" using ex'v fzac by simp
  have hx'v: "h x' = M.e (M.n (qstepL Gm (M.n (h x))))" using QaskLL.prems(6) by (simp add: x'_def)
  have hx': "hc x'" using Ax' by (simp add: A_def)
  \<comment> \<open>connectivity: x -> e x -> f (f (e x)) = e x' -> x'\<close>
  have Aex: "A (C.e x)" using ex hx hcE by (simp add: A_def)
  have Ax: "A x" using x hx by (simp add: A_def)
  have cex: "conn (C.e x)" by (rule conn_edge[OF Ax Aex cx])
  have "C.cface (C.e x) (C.f z)" by (simp add: z_def)
  then have cfz: "conn (C.e x')" using ex'v conn_face cex by metis
  have Aex': "A (C.e x')" using ex' hx' hcE by (simp add: A_def)
  have "conn (C.e (C.e x'))" by (rule conn_edge[OF Aex' _ cfz]) (simp add: Ax')
  then have cx': "conn x'" by simp
  have st: "qstepL Gc (qstepL Gc (C.n x)) = C.n x'" by (simp add: qstepL_def x'_def)
  have stm: "qstepL Gm (qstepL Gm (M.n (h x))) = M.n (h x')" by (simp add: qstepL_def hx'v)
  have IH: "\<forall>z \<in> set (walkq Gc (C.n x') q). conn z"
    by (rule QaskLL.IH[OF x' ex' hx' cx']) (use QaskLL.prems(5,6) st stm in simp_all)
  show ?case using IH cx' st by (simp add: x'_def)
next
  case (QaskRR qa q)
  note x = QaskRR.prems(1) and ex = QaskRR.prems(2) and hx = QaskRR.prems(3) and cx = QaskRR.prems(4)
  have Aw: "\<forall>z \<in> set (walkq Gc (C.n x) (QaskRR qa q)). A z"
    by (rule A_walk[OF x ex hx QaskRR.prems(5,6)])
  define x' where "x' = qstepR Gc (C.n x)"
  have x': "x' \<in> ac" using QaskRR.prems(5) by (simp add: x'_def)
  have Ax': "A x'" using Aw by (simp add: x'_def)
  have hx'v: "h x' = qstepR Gm (M.n (h x))" using QaskRR.prems(6) by (simp add: x'_def)
  define u where "u = C.e (C.n x)"
  have uac: "u \<in> ac" unfolding u_def by (rule ac_en[OF x])
  have "C.cface u x" using fconnect_step[of C.f u] by (simp add: u_def C.nodeK)
  then have cu: "conn u" using conn_face C.F.fconnect_sym cx by metis
  have nu: "C.n u = x'" by (simp add: u_def x'_def qstepR_def)
  have cx': "conn x'" using conn_node[OF uac _ cu] Ax' nu by simp
  define x'' where "x'' = C.e x'"
  have x'': "x'' \<in> ac" using acF[of x''] uac by (simp add: x''_def x'_def qstepR_def C.nodeK u_def)
  have ex'': "C.e x'' \<in> ac" using x' by (simp add: x''_def)
  have hcx': "hc x'" using Ax' by (simp add: A_def)
  have hx'': "hc x''" using hcx' hcE by (simp add: x''_def)
  have Ax'': "A x''" using x'' hx'' by (simp add: A_def)
  have cx'': "conn x''" unfolding x''_def by (rule conn_edge[OF Ax' _ cx']) (use Ax'' in \<open>simp add: x''_def\<close>)
  have hx''v: "h x'' = M.e (h x')" using hcx' by (simp add: edge_central_def x''_def)
  have st: "qstepR Gc (qstepR Gc (C.n x)) = C.n x''" by (simp add: qstepR_def x''_def x'_def)
  have stm: "qstepR Gm (qstepR Gm (M.n (h x))) = M.n (h x'')" by (simp add: qstepR_def hx''v hx'v)
  have IH: "\<forall>z \<in> set (walkq Gc (C.n x'') q). conn z"
    by (rule QaskRR.IH[OF x'' ex'' hx'' cx'']) (use QaskRR.prems(5,6) st stm in simp_all)
  show ?case using IH cx' st by (simp add: x'_def)
qed

lemma conn_s0: "z \<in> set s0c \<Longrightarrow> conn z"
proof -
  assume zs: "z \<in> set s0c"
  obtain q0 q1 where qz: "qz = Quiz q0 q1" by (cases qz)
  obtain qa0 q01 where q0: "q0 = QaskR qa0 q01" using qzR qz by (cases q0) auto
  obtain qa1 q10 where q1: "q1 = QaskR qa1 q10" using qzR qz by (cases q1) auto
  have x0: "x0c \<in> ac" and ex0: "C.e x0c \<in> ac" using s0_ac by (auto simp: qz q0 q1)
  have hc0: "hc x0c" using Dhx0 Dhex0 by (simp add: edge_central_def)
  have hce0: "hc (C.e x0c)" using hc0 hcE by simp
  have c0: "conn x0c" by (simp add: conn_def rl_face)
  have A0: "A x0c" and Ae0: "A (C.e x0c)" using x0 ex0 hc0 hce0 by (simp_all add: A_def)
  have ce0: "conn (C.e x0c)" by (rule conn_edge[OF A0 Ae0 c0])
  have s0: "s0c = x0c # walkq Gc (C.n (C.e x0c)) q01 @ C.e x0c # walkq Gc (C.n x0c) q10"
    by (simp add: qz q0 q1 qstepR_def)
  have m0: "s0m = x0m # walkq Gm (M.n (M.e x0m)) q01 @ M.e x0m # walkq Gm (M.n x0m) q10"
    by (simp add: qz q0 q1 qstepR_def)
  have eqs: "map h (walkq Gc (C.n (C.e x0c)) q01) = walkq Gm (M.n (h (C.e x0c))) q01 \<and>
             map h (walkq Gc (C.n x0c) q10) = walkq Gm (M.n (h x0c)) q10"
    using Ehs0 Dhx0 Dhex0 unfolding s0 m0 by (simp add: append_eq_append_conv length_walkq)
  have a: "\<forall>z \<in> set (walkq Gc (C.n (C.e x0c)) q01). conn z"
    by (rule conn_walk[OF ex0]) (use x0 hce0 ce0 eqs s0_ac s0 in auto)
  have b: "\<forall>z \<in> set (walkq Gc (C.n x0c) q10). conn z"
    by (rule conn_walk[OF x0]) (use ex0 hc0 c0 eqs s0_ac s0 in auto)
  show ?thesis using zs a b c0 ce0 s0 by auto
qed

lemma embedqz_rlinked: "C.rlink_connected (\<lambda>z. z \<in> ac \<and> hc z)"
  unfolding C.rlink_connected_def
proof (intro allI impI)
  fix x y assume x: "x \<in> ac \<and> hc x" and y: "y \<in> ac \<and> hc y"
  obtain u where u: "u \<in> set s0c" "C.cface x u"
    using Dac[of x] x ac_D by (auto simp: fband_def)
  obtain v where v: "v \<in> set s0c" "C.cface y v"
    using Dac[of y] y ac_D by (auto simp: fband_def)
  have "rl x u" by (rule rl_face[OF u(2)])
  moreover have "rl u x0c" using conn_s0[OF u(1)] by (simp add: conn_def)
  moreover have "rl x0c v" using conn_s0[OF v(1)] by (simp add: conn_def)
  moreover have "rl v y" by (rule rl_face[OF C.F.fconnect_sym[OF v(2)]])
  ultimately have "rl x y" using rl_trans by metis
  then show "\<exists>p. path (rlink Gc) (C.n (C.f x)) (p @ [y]) \<and> (\<forall>z \<in> set p. z \<in> ac \<and> hc z)"
    by (simp add: rl_def A_def)
qed

theorem quiz_preembedding: "preembedding Gc Gm ac h"
  unfolding preembedding_def
proof (intro conjI ballI)
  fix x assume x: "x \<in> ac"
  show "h (face Gc x) = face Gm (h x)" by (rule embedqz_face[OF x])
  show "order (face Gm) (h x) = order (face Gc) x" by (rule embedqz_arity[OF x])
  obtain u where "u \<in> set s0c" "C.cface x u" using Dac[of x] x ac_D by (auto simp: fband_def)
  then show "\<exists>y. C.cface x y \<and> edge_central Gc Gm h y" using embedqz_central by blast
next
  show "C.rlink_connected (\<lambda>x. x \<in> ac \<and> edge_central Gc Gm h x)" by (rule embedqz_rlinked)
qed

lemma h_darts: "h ` C.D \<subseteq> M.D"
proof
  fix y assume "y \<in> h ` C.D"
  then obtain x where y: "y = h x" by blast
  have "nthd x0m s0m (idx x) \<in> M.D" using s0m_D x0mD by (auto simp: nthd_def)
  then show "y \<in> M.D" by (simp add: y h_def)
qed

end

end
