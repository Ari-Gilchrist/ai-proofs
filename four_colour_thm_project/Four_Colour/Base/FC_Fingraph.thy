(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      FC_Fingraph.thy
    Orbits of permutations of finite sets, and connected components of
    relations, in the style of the SSReflect fingraph library.
*)
theory FC_Fingraph
  imports FC_Seq "HOL-Combinatorics.Permutations"
begin

section \<open>Function connectivity\<close>

definition fconnect :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "fconnect f x y \<longleftrightarrow> (\<exists>n. (f ^^ n) x = y)"

definition cyc :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "cyc f x = {y. fconnect f x y}"

definition order :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> nat" where
  "order f x = card (cyc f x)"

definition fcard :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> nat" where
  "fcard f A = card (cyc f ` A)"

definition traject :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a list" where
  "traject f x n = map (\<lambda>i. (f ^^ i) x) [0..<n]"

definition orb :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "orb f x = traject f x (order f x)"

abbreviation (input) frel :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "frel f x y \<equiv> f x = y"

lemma funpow_add_apply: "(f ^^ (m + n)) x = (f ^^ m) ((f ^^ n) x)"
  by (simp add: funpow_add)

lemma fconnect_refl [simp, intro]: "fconnect f x x"
  unfolding fconnect_def by (metis funpow_0)

lemma fconnect_step [intro]: "fconnect f x (f x)"
  unfolding fconnect_def by (intro exI[of _ 1]) simp

lemma fconnect_funpow: "fconnect f x ((f ^^ n) x)"
  unfolding fconnect_def by blast

lemma fconnect_trans [trans]: "fconnect f x y \<Longrightarrow> fconnect f y z \<Longrightarrow> fconnect f x z"
  unfolding fconnect_def by (metis funpow_add o_apply)

lemma fconnect_stepI: "fconnect f (f x) y \<Longrightarrow> fconnect f x y"
  by (meson fconnect_step fconnect_trans)

lemma fconnect_stepI_r: "fconnect f x y \<Longrightarrow> fconnect f x (f y)"
  by (meson fconnect_step fconnect_trans)

lemma fconnect_cases:
  "fconnect f x y \<longleftrightarrow> y = x \<or> fconnect f (f x) y"
  unfolding fconnect_def
  by (metis funpow_0 funpow_Suc_right not0_implies_Suc o_apply)

lemma fconnect_induct [consumes 1, case_names refl step]:
  assumes "fconnect f x y" "P x" "\<And>z. fconnect f x z \<Longrightarrow> P z \<Longrightarrow> P (f z)"
  shows "P y"
proof -
  obtain n where "y = (f ^^ n) x" using assms(1) unfolding fconnect_def by blast
  moreover have "P ((f ^^ n) x)"
    by (induction n) (auto intro: assms(2) assms(3) fconnect_funpow)
  ultimately show ?thesis by simp
qed

lemma path_fconnect:
  "path (frel f) x p \<Longrightarrow> y \<in> set p \<Longrightarrow> fconnect f x y"
  by (induction p arbitrary: x) (auto intro: fconnect_stepI)

lemma fconnect_path:
  assumes "fconnect f x y"
  obtains p where "path (frel f) x p" "lastd x p = y"
proof -
  obtain n where "y = (f ^^ n) x" using assms unfolding fconnect_def by blast
  have "\<exists>p. path (frel f) x p \<and> lastd x p = (f ^^ n) x"
  proof (induction n)
    case 0
    then show ?case by (intro exI[of _ "[]"]) simp
  next
    case (Suc n)
    then obtain p where "path (frel f) x p" "lastd x p = (f ^^ n) x" by blast
    then show ?case by (intro exI[of _ "p @ [(f ^^ Suc n) x]"]) simp
  qed
  then show ?thesis using that \<open>y = _\<close> by blast
qed

lemma traject_Suc: "traject f x (Suc n) = x # traject f (f x) n"
  unfolding traject_def
  by (simp add: map_upt_Suc funpow_swap1 del: upt_Suc)

lemma traject_0 [simp]: "traject f x 0 = []"
  by (simp add: traject_def)

lemma length_traject [simp]: "length (traject f x n) = n"
  by (simp add: traject_def)

lemma nth_traject [simp]: "i < n \<Longrightarrow> traject f x n ! i = (f ^^ i) x"
  by (simp add: traject_def)

lemma set_traject: "set (traject f x n) = (\<lambda>i. (f ^^ i) x) ` {..<n}"
  by (auto simp: traject_def)

section \<open>Permutations of a finite set\<close>

locale fperm =
  fixes f :: "'a \<Rightarrow> 'a" and D :: "'a set"
  assumes perm: "f permutes D" and fin: "finite D"
begin

lemma inj: "inj f"
  using perm by (rule permutes_inj)

lemma bij: "bij f"
  using perm by (rule permutes_bij)

lemma surj: "surj f"
  using bij by (rule bij_is_surj)

lemma out [simp]: "x \<notin> D \<Longrightarrow> f x = x"
  using perm by (simp add: permutes_not_in)

lemma closed [simp]: "f x \<in> D \<longleftrightarrow> x \<in> D"
  using perm by (rule permutes_in_image)

lemma eq_iff [simp]: "f x = f y \<longleftrightarrow> x = y"
  using inj by (meson injD)

lemma inv_f [simp]: "inv f (f x) = x"
  using inj by simp

lemma f_inv [simp]: "f (inv f x) = x"
  using surj by (simp add: surj_f_inv_f)

lemma img_neq:
  assumes "f c = b" "a \<noteq> c"
  shows "f a \<noteq> b"
proof
  assume "f a = b"
  then have "f a = f c" using assms(1) by simp
  then show False using assms(2) by simp
qed

lemma inv_perm: "inv f permutes D"
  using perm by (rule permutes_inv)

lemma funpow_closed [simp]: "(f ^^ n) x \<in> D \<longleftrightarrow> x \<in> D"
  by (induction n) auto

lemma funpow_out [simp]: "x \<notin> D \<Longrightarrow> (f ^^ n) x = x"
  by (induction n) auto

lemma funpow_inj: "(f ^^ n) x = (f ^^ n) y \<longleftrightarrow> x = y"
  by (induction n) auto

lemma cyc_subset: "x \<in> D \<Longrightarrow> cyc f x \<subseteq> D"
  unfolding cyc_def fconnect_def by auto

lemma cyc_out: "x \<notin> D \<Longrightarrow> cyc f x = {x}"
  unfolding cyc_def fconnect_def by auto

lemma finite_cyc [simp, intro]: "finite (cyc f x)"
  by (cases "x \<in> D") (auto intro: finite_subset[OF cyc_subset fin] simp: cyc_out)

lemma x_in_cyc [simp, intro]: "x \<in> cyc f x"
  by (simp add: cyc_def)

lemma period_exists: "\<exists>n>0. (f ^^ n) x = x"
proof -
  have "finite ((\<lambda>i. (f ^^ i) x) ` UNIV)"
    by (rule finite_subset[OF _ finite_cyc[of x]]) (auto simp: cyc_def fconnect_def)
  then have "\<not> inj (\<lambda>i::nat. (f ^^ i) x)"
    using finite_imageD infinite_UNIV_nat by blast
  then obtain i j :: nat where ij: "i \<noteq> j" "(f ^^ i) x = (f ^^ j) x"
    unfolding inj_def by blast
  show ?thesis
  proof (cases "i < j")
    case True
    then have "(f ^^ i) ((f ^^ (j - i)) x) = (f ^^ i) x"
      using ij funpow_add_apply[where f=f and m=i and n="j - i" and x=x] by simp
    then show ?thesis using True by (intro exI[of _ "j - i"]) (simp add: funpow_inj)
  next
    case False
    then have "j < i" using ij by simp
    then have "(f ^^ j) ((f ^^ (i - j)) x) = (f ^^ j) x"
      using ij funpow_add_apply[where f=f and m=j and n="i - j" and x=x] by simp
    then show ?thesis using \<open>j < i\<close> by (intro exI[of _ "i - j"]) (simp add: funpow_inj)
  qed
qed

definition period :: "'a \<Rightarrow> nat" where
  "period x = (LEAST n. n > 0 \<and> (f ^^ n) x = x)"

lemma period_pos: "period x > 0" and funpow_period: "(f ^^ period x) x = x"
  using LeastI_ex[OF period_exists[of x]] unfolding period_def by auto

lemma period_least: "0 < n \<Longrightarrow> n < period x \<Longrightarrow> (f ^^ n) x \<noteq> x"
  using not_less_Least unfolding period_def by blast

lemma funpow_mod_period: "(f ^^ (n mod period x)) x = (f ^^ n) x"
proof -
  have "(f ^^ (k * period x)) x = x" for k
    by (induction k) (simp_all add: funpow_add funpow_period)
  then have "(f ^^ (n mod period x)) ((f ^^ (n div period x * period x)) x) = (f ^^ n) x"
    using funpow_add_apply[where f=f and m="n mod period x" and n="n div period x * period x" and x=x]
    by (simp add: mod_div_mult_eq)
  then show ?thesis
    using \<open>\<And>k. (f ^^ (k * period x)) x = x\<close> by simp
qed

lemma funpow_inj_period:
  assumes "i < period x" "j < period x" "(f ^^ i) x = (f ^^ j) x"
  shows "i = j"
proof (rule ccontr)
  assume "i \<noteq> j"
  then consider "i < j" | "j < i" by linarith
  then show False
  proof cases
    case 1
    then have "(f ^^ i) ((f ^^ (j - i)) x) = (f ^^ i) x"
      using assms funpow_add_apply[where f=f and m=i and n="j - i" and x=x] by simp
    then have "(f ^^ (j - i)) x = x" by (simp add: funpow_inj)
    then show False using period_least[of "j - i" x] 1 assms by simp
  next
    case 2
    then have "(f ^^ j) ((f ^^ (i - j)) x) = (f ^^ j) x"
      using assms funpow_add_apply[where f=f and m=j and n="i - j" and x=x] by simp
    then have "(f ^^ (i - j)) x = x" by (simp add: funpow_inj)
    then show False using period_least[of "i - j" x] 2 assms by simp
  qed
qed

lemma cyc_period: "cyc f x = (\<lambda>i. (f ^^ i) x) ` {..<period x}"
proof -
  have "(f ^^ n) x \<in> (\<lambda>i. (f ^^ i) x) ` {..<period x}" for n
  proof -
    have "n mod period x < period x" using period_pos[of x] by simp
    then show ?thesis using funpow_mod_period[of n x] by (metis image_eqI lessThan_iff)
  qed
  then show ?thesis
    unfolding cyc_def fconnect_def by auto
qed

lemma order_period: "order f x = period x"
proof -
  have "inj_on (\<lambda>i. (f ^^ i) x) {..<period x}"
    by (auto intro!: inj_onI funpow_inj_period)
  then show ?thesis
    unfolding order_def cyc_period by (simp add: card_image)
qed

lemma order_pos [simp]: "0 < order f x"
  by (simp add: order_period period_pos)

lemma funpow_order [simp]: "(f ^^ order f x) x = x"
  by (simp add: order_period funpow_period)

lemma funpow_mod_order: "(f ^^ (n mod order f x)) x = (f ^^ n) x"
  by (simp add: order_period funpow_mod_period)

lemma funpow_inj_order:
  "i < order f x \<Longrightarrow> j < order f x \<Longrightarrow> (f ^^ i) x = (f ^^ j) x \<Longrightarrow> i = j"
  by (simp add: order_period funpow_inj_period)

lemma order_least: "0 < n \<Longrightarrow> n < order f x \<Longrightarrow> (f ^^ n) x \<noteq> x"
  by (simp add: order_period period_least)

lemma order_dvd: "(f ^^ n) x = x \<longleftrightarrow> order f x dvd n"
proof
  assume "(f ^^ n) x = x"
  then have "(f ^^ (n mod order f x)) x = x" by (simp add: funpow_mod_order)
  then have "n mod order f x = 0"
    using order_least[of "n mod order f x" x] order_pos[of x]
    by (metis bot_nat_0.not_eq_extremum mod_less_divisor)
  then show "order f x dvd n" by auto
next
  assume "order f x dvd n"
  then show "(f ^^ n) x = x"
    using funpow_mod_order[of n x] by (simp add: dvd_imp_mod_0)
qed

lemma cyc_order: "cyc f x = (\<lambda>i. (f ^^ i) x) ` {..<order f x}"
  by (simp add: order_period cyc_period)

lemma fconnect_order: "fconnect f x y \<longleftrightarrow> (\<exists>i < order f x. (f ^^ i) x = y)"
  using cyc_order[of x] unfolding cyc_def by (auto simp: set_eq_iff)

lemma fconnect_sym: "fconnect f x y \<Longrightarrow> fconnect f y x"
proof -
  assume "fconnect f x y"
  then obtain i where i: "y = (f ^^ i) x" unfolding fconnect_def by blast
  let ?r = "i mod order f x"
  have "y = (f ^^ ?r) x" by (simp add: i funpow_mod_order)
  then have "(f ^^ (order f x - ?r)) y = (f ^^ (order f x - ?r + ?r)) x"
    by (simp only: funpow_add_apply)
  also have "order f x - ?r + ?r = order f x"
    using order_pos[of x] by (simp add: less_imp_le_nat)
  also have "(f ^^ order f x) x = x" by simp
  finally show ?thesis unfolding fconnect_def by blast
qed

lemma fconnect_commute: "fconnect f x y \<longleftrightarrow> fconnect f y x"
  by (blast intro: fconnect_sym)

lemma cyc_eq:
  assumes xy: "fconnect f x y"
  shows "cyc f x = cyc f y"
proof -
  have yx: "fconnect f y x" using xy by (rule fconnect_sym)
  show ?thesis
    unfolding cyc_def
  proof (intro Collect_cong iffI)
    fix z
    assume "fconnect f x z"
    then show "fconnect f y z" by (rule fconnect_trans[OF yx])
  next
    fix z
    assume "fconnect f y z"
    then show "fconnect f x z" by (rule fconnect_trans[OF xy])
  qed
qed

lemma cyc_eq_iff: "cyc f x = cyc f y \<longleftrightarrow> fconnect f x y"
  by (metis cyc_def cyc_eq mem_Collect_eq x_in_cyc)

lemma in_cyc_iff: "y \<in> cyc f x \<longleftrightarrow> fconnect f x y"
  by (simp add: cyc_def)

lemma order_eq: "fconnect f x y \<Longrightarrow> order f x = order f y"
  by (simp add: order_def cyc_eq)

lemma cyc_f [simp]: "cyc f (f x) = cyc f x"
  by (metis cyc_eq fconnect_step)

lemma order_f [simp]: "order f (f x) = order f x"
  by (simp add: order_def)

lemma fconnect_f_left [simp]: "fconnect f (f x) y \<longleftrightarrow> fconnect f x y"
  by (metis cyc_eq_iff cyc_f)

lemma fconnect_f_right [simp]: "fconnect f x (f y) \<longleftrightarrow> fconnect f x y"
  by (metis cyc_eq_iff cyc_f)

lemma fconnect_funpow_left [simp]: "fconnect f ((f ^^ n) x) y \<longleftrightarrow> fconnect f x y"
  by (induction n) auto

lemma fconnect_funpow_right [simp]: "fconnect f x ((f ^^ n) y) \<longleftrightarrow> fconnect f x y"
  by (induction n) auto

lemma fconnect_inv_left [simp]: "fconnect f (inv f x) y \<longleftrightarrow> fconnect f x y"
  by (metis f_inv fconnect_f_left)

lemma fconnect_inv_right [simp]: "fconnect f x (inv f y) \<longleftrightarrow> fconnect f x y"
  by (metis f_inv fconnect_f_right)

lemma fconnect_in_D: "fconnect f x y \<Longrightarrow> x \<in> D \<longleftrightarrow> y \<in> D"
  unfolding fconnect_def by auto

lemma fconnect_out: "x \<notin> D \<Longrightarrow> fconnect f x y \<longleftrightarrow> y = x"
  unfolding fconnect_def by auto

lemma order_out: "x \<notin> D \<Longrightarrow> order f x = 1"
  by (simp add: order_def cyc_out)

lemma order_1_iff: "order f x = 1 \<longleftrightarrow> f x = x"
proof
  assume "order f x = 1"
  then show "f x = x" using funpow_order[of x] by simp
next
  assume "f x = x"
  then have "(f ^^ k) x = x" for k by (induction k) simp_all
  then have "cyc f x = {x}"
    unfolding cyc_def fconnect_def by auto
  then show "order f x = 1" by (simp add: order_def)
qed

lemma inv_funpow_order:
  "inv f x = (f ^^ (order f x - 1)) x"
proof -
  have o: "Suc (order f x - 1) = order f x" using order_pos[of x] by simp
  have "f ((f ^^ (order f x - 1)) x) = (f ^^ Suc (order f x - 1)) x"
    by (simp only: funpow.simps(2) o_apply)
  also have "\<dots> = x" by (simp only: o funpow_order)
  finally have "f ((f ^^ (order f x - 1)) x) = x" .
  then have "inv f (f ((f ^^ (order f x - 1)) x)) = inv f x" by simp
  then show ?thesis by simp
qed

lemma fconnect_inv: "fconnect (inv f) x y \<longleftrightarrow> fconnect f x y"
proof
  assume "fconnect (inv f) x y"
  then have "fconnect f y x"
  proof (induction rule: fconnect_induct)
    case refl
    then show ?case by simp
  next
    case (step z)
    have "fconnect f (inv f z) z" using fconnect_step[of f "inv f z"] by simp
    then show ?case by (rule fconnect_trans[OF _ step.IH])
  qed
  then show "fconnect f x y" by (rule fconnect_sym)
next
  assume "fconnect f x y"
  then have "fconnect f y x" by (rule fconnect_sym)
  then show "fconnect (inv f) x y"
  proof (induction rule: fconnect_induct)
    case refl
    then show ?case by simp
  next
    case (step z)
    have "fconnect (inv f) (f z) z" using fconnect_step[of "inv f" "f z"] by simp
    then show ?case by (rule fconnect_trans[OF _ step.IH])
  qed
qed

lemma cyc_inv: "cyc (inv f) x = cyc f x"
  by (simp add: cyc_def fconnect_inv)

lemma order_inv: "order (inv f) x = order f x"
  by (simp add: order_def cyc_inv)

lemma fcard_inv: "fcard (inv f) A = fcard f A"
  by (simp add: fcard_def cyc_inv[abs_def])

lemma distinct_orb: "distinct (orb f x)"
  unfolding orb_def traject_def distinct_map
  by (auto intro!: inj_onI funpow_inj_order)

lemma set_orb: "set (orb f x) = cyc f x"
  by (simp add: orb_def set_traject cyc_order)

lemma length_orb [simp]: "length (orb f x) = order f x"
  by (simp add: orb_def)

lemma orb_Cons: "orb f x = x # tl (orb f x)"
proof -
  obtain k where "order f x = Suc k" using order_pos[of x] gr0_implies_Suc by blast
  then show ?thesis by (simp add: orb_def traject_Suc)
qed

lemma cycle_orb: "cycle (frel f) (orb f x)"
proof -
  have "cycle (frel f) (orb f x) = (\<forall>i<order f x. f ((f ^^ i) x) = (f ^^ (Suc i mod order f x)) x)"
    unfolding cycle_nth by (simp add: orb_def)
  also have "\<dots>"
    by (simp add: funpow_mod_order)
  finally show ?thesis .
qed

lemma fcard_out_union:
  assumes "finite A"
  shows "fcard f A = card (cyc f ` A)"
  by (simp add: fcard_def)

end

lemma fperm_inv: "fperm f D \<Longrightarrow> fperm (inv f) D"
  unfolding fperm_def using permutes_inv by blast

section \<open>Fixed-point-free and cycle lemmas\<close>

lemma (in fperm) fcycle_fconnect:
  assumes cyc: "cycle (frel f) p" and dp: "distinct p" and xp: "x \<in> set p"
  shows "fconnect f x y \<longleftrightarrow> y \<in> set p"
proof
  assume "y \<in> set p"
  obtain i j where i: "i < length p" "p ! i = x" and j: "j < length p" "p ! j = y"
    using xp \<open>y \<in> set p\<close> by (auto simp: in_set_conv_nth)
  have step: "f (p ! k) = p ! (Suc k mod length p)" if "k < length p" for k
    using cyc that by (simp add: cycle_nth)
  have "(f ^^ n) (p ! i) = p ! ((i + n) mod length p)" for n
  proof (induction n)
    case 0
    then show ?case using i by auto
  next
    case (Suc n)
    have "length p > 0" using i(1) by linarith
    then show ?case
      using Suc step[of "(i + n) mod length p"] by (simp add: mod_Suc_eq)
  qed
  moreover have "(i + (j + length p - i) mod length p) mod length p = j"
  proof -
    have "(i + (j + length p - i) mod length p) mod length p = (i + (j + length p - i)) mod length p"
      by (simp add: mod_add_right_eq)
    also have "i + (j + length p - i) = j + length p" using i by simp
    finally show ?thesis using j by simp
  qed
  ultimately have "(f ^^ ((j + length p - i) mod length p)) x = y"
    using i j by metis
  then show "fconnect f x y" unfolding fconnect_def by blast
next
  assume "fconnect f x y"
  then show "y \<in> set p"
  proof (induction rule: fconnect_induct)
    case refl
    then show ?case using xp .
  next
    case (step z)
    then obtain k where k: "k < length p" "p ! k = z" by (auto simp: in_set_conv_nth)
    have "f (p ! k) = p ! (Suc k mod length p)" using cyc k(1) by (simp add: cycle_nth)
    then have "f z = p ! (Suc k mod length p)" using k(2) by simp
    moreover have "Suc k mod length p < length p"
    proof -
      have "0 < length p" using k(1) by linarith
      then show ?thesis by (rule mod_less_divisor)
    qed
    ultimately show ?case by simp
  qed
qed

section \<open>Connectivity for relations\<close>

abbreviation connect :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "connect r \<equiv> r\<^sup>*\<^sup>*"

definition comp_of :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "comp_of r x = {y. connect r x y}"

definition n_comp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> nat" where
  "n_comp r A = card (comp_of r ` A)"

lemma connect_path:
  "connect r x y \<longleftrightarrow> (\<exists>p. path r x p \<and> lastd x p = y)"
proof
  assume "connect r x y"
  then show "\<exists>p. path r x p \<and> lastd x p = y"
  proof (induction rule: rtranclp_induct)
    case base
    then show ?case by (intro exI[of _ "[]"]) simp
  next
    case (step y z)
    then obtain p where "path r x p" "lastd x p = y" by blast
    then show ?case using step by (intro exI[of _ "p @ [z]"]) simp
  qed
next
  assume "\<exists>p. path r x p \<and> lastd x p = y"
  then obtain p where "path r x p" "lastd x p = y" by blast
  then show "connect r x y"
    by (induction p arbitrary: x) (auto intro: converse_rtranclp_into_rtranclp)
qed

lemma path_connect:
  "path r x p \<Longrightarrow> y \<in> set (x # p) \<Longrightarrow> connect r x y"
  by (induction p arbitrary: x) (auto intro: converse_rtranclp_into_rtranclp)

lemma connect_shortest:
  assumes "connect r x y"
  obtains p where "path r x p" "lastd x p = y" "distinct (x # p)"
proof -
  obtain p where p: "path r x p" "lastd x p = y"
    using assms connect_path by metis
  have "\<exists>q. path r x q \<and> lastd x q = y \<and> distinct (x # q)"
    using p
  proof (induction "length p" arbitrary: p rule: less_induct)
    case less
    show ?case
    proof (cases "distinct (x # p)")
      case True
      then show ?thesis using less by blast
    next
      case False
      then obtain a q1 q2 q3 where split: "x # p = q1 @ [a] @ q2 @ [a] @ q3"
        using not_distinct_decomp by blast
      show ?thesis
      proof (cases q1)
        case Nil
        then have x: "x = a" and pp: "p = q2 @ [a] @ q3" using split by auto
        have "path r x q3" "lastd x q3 = y"
          using less.prems x pp by (auto simp: lastd_append)
        moreover have "length q3 < length p" using pp by simp
        ultimately show ?thesis using less.hyps by blast
      next
        case (Cons b q1')
        then have x: "x = b" and pp: "p = q1' @ [a] @ q2 @ [a] @ q3" using split by auto
        let ?p' = "q1' @ [a] @ q3"
        have "path r x ?p'" using less.prems pp x by (auto simp: lastd_append)
        moreover have "lastd x ?p' = y"
          using less.prems pp x by (simp add: lastd_append)
        moreover have "length ?p' < length p" using pp by simp
        ultimately show ?thesis using less.hyps by blast
      qed
    qed
  qed
  then show ?thesis using that by blast
qed

section \<open>More path utilities\<close>

lemma path_take: "path r x p \<Longrightarrow> path r x (take k p)"
  by (metis append_take_drop_id path_append)

lemma path_drop:
  "path r x p \<Longrightarrow> k < length p \<Longrightarrow> path r (p ! k) (drop (Suc k) p)"
proof (induction p arbitrary: x k)
  case Nil
  then show ?case by simp
next
  case (Cons y p)
  then show ?case by (cases k) auto
qed

lemma lastd_take: "k \<le> length p \<Longrightarrow> lastd x (take k p) = (x # p) ! k"
proof (induction p arbitrary: x k)
  case Nil
  then show ?case by simp
next
  case (Cons y p)
  then show ?case by (cases k) auto
qed

lemma path_shorten:
  assumes "path r x p"
  obtains p' where "path r x p'" "lastd x p' = lastd x p" "distinct (x # p')" "set p' \<subseteq> set p"
proof -
  have "\<exists>p'. path r x p' \<and> lastd x p' = lastd x p \<and> distinct (x # p') \<and> set p' \<subseteq> set p"
    using assms
  proof (induction "length p" arbitrary: p rule: less_induct)
    case less
    show ?case
    proof (cases "distinct (x # p)")
      case True
      then show ?thesis using less.prems by blast
    next
      case False
      then obtain a q1 q2 q3 where split: "x # p = q1 @ [a] @ q2 @ [a] @ q3"
        using not_distinct_decomp by blast
      show ?thesis
      proof (cases q1)
        case Nil
        then have x: "x = a" and pp: "p = q2 @ [a] @ q3" using split by auto
        have h: "path r x q3" using less.prems x pp by (simp add: lastd_append)
        have l: "lastd x q3 = lastd x p" using x pp by (simp add: lastd_append)
        have "length q3 < length p" using pp by simp
        then obtain p' where p': "path r x p'" "lastd x p' = lastd x q3" "distinct (x # p')" "set p' \<subseteq> set q3"
          using less.hyps h by blast
        show ?thesis by (rule exI[of _ p']) (use p' l pp in auto)
      next
        case (Cons b q1')
        then have x: "x = b" and pp: "p = q1' @ [a] @ q2 @ [a] @ q3" using split by auto
        let ?p' = "q1' @ [a] @ q3"
        have h: "path r x ?p'" using less.prems pp x by (simp add: lastd_append)
        have l: "lastd x ?p' = lastd x p" using pp by (simp add: lastd_append)
        have "length ?p' < length p" using pp by simp
        then obtain p' where p': "path r x p'" "lastd x p' = lastd x ?p'" "distinct (x # p')" "set p' \<subseteq> set ?p'"
          using less.hyps h by blast
        show ?thesis by (rule exI[of _ p']) (use p' l pp in auto)
      qed
    qed
  qed
  then show ?thesis using that by blast
qed

lemma fconnect_connect: "fconnect f x y \<Longrightarrow> connect (frel f) x y"
  by (metis connect_path fconnect_path)

lemma path_frel_nth: "path (frel f) x l \<Longrightarrow> i < length l \<Longrightarrow> l ! i = (f ^^ Suc i) x"
proof (induction l arbitrary: x i)
  case Nil
  then show ?case by simp
next
  case (Cons y l)
  then show ?case by (cases i) (auto simp: funpow_swap1)
qed

lemma path_frel_last: "path (frel f) x l \<Longrightarrow> lastd x l = (f ^^ length l) x"
proof (induction l arbitrary: x)
  case Nil
  then show ?case by simp
next
  case (Cons y l)
  then show ?case by (simp add: funpow_swap1)
qed

lemma path_frel_set: "path (frel f) x l \<Longrightarrow> i \<le> length l \<Longrightarrow> (f ^^ i) x \<in> set (x # l)"
proof -
  assume p: "path (frel f) x l" and i: "i \<le> length l"
  show ?thesis
  proof (cases i)
    case 0
    then show ?thesis by simp
  next
    case (Suc j)
    then have "l ! j = (f ^^ i) x" using path_frel_nth[OF p, of j] i by simp
    moreover have "j < length l" using Suc i by simp
    ultimately show ?thesis by (metis nth_mem list.set_intros(2))
  qed
qed

lemma path_frel_butlast:
  assumes p: "path (frel f) a q" and inj: "inj f" and fy: "f y \<in> set q"
  shows "y \<in> set (butlast (a # q))"
proof -
  obtain i where i: "i < length q" "q ! i = f y" using fy by (auto simp: in_set_conv_nth)
  have "f ((a # q) ! i) = q ! i" using p i(1) by (simp add: path_nth)
  then have "(a # q) ! i = y" using i(2) inj by (simp add: inj_eq)
  moreover have il: "i < length (butlast (a # q))" using i(1) by (cases q) auto
  moreover have "butlast (a # q) ! i = (a # q) ! i" by (rule nth_butlast[OF il])
  ultimately show ?thesis by (metis nth_mem)
qed

context fperm
begin

lemma path_cyc_cover:
  assumes p: "path (frel f) x l" and bk: "f (lastd x l) = x"
  shows "cyc f x \<subseteq> set (x # l)"
proof
  fix y assume "y \<in> cyc f x"
  then obtain i where i: "i < order f x" "y = (f ^^ i) x" using cyc_order by auto
  have "(f ^^ Suc (length l)) x = x" using bk path_frel_last[OF p] by simp
  then have "order f x dvd Suc (length l)" using order_dvd by blast
  then have "order f x \<le> Suc (length l)" by (simp add: dvd_imp_le)
  then have "i \<le> length l" using i(1) by simp
  then show "y \<in> set (x # l)" using path_frel_set[OF p] i(2) by simp
qed

lemma face_orbit_path:
  obtains q where "path (frel f) (f x) q" "lastd (f x) q = x" "distinct (f x # q)"
    "set (f x # q) = cyc f x"
proof -
  define T where "T = tl (orb f x)"
  have o: "orb f x = x # T" unfolding T_def by (rule orb_Cons)
  have pt: "path (frel f) x (T @ [x])" using cycle_orb[of x] o by (simp add: cycle_Cons)
  have dT: "distinct (x # T)" using distinct_orb[of x] o by simp
  have sT: "set (x # T) = cyc f x" using set_orb[of x] o by simp
  obtain h q where L: "T @ [x] = h # q" by (cases "T @ [x]") auto
  have hfx: "h = f x" using pt L by simp
  have "path (frel f) (f x) q" using pt L hfx by simp
  moreover have "lastd (f x) q = x" using L hfx by (metis last.simps last_snoc list.distinct(1))
  moreover have "distinct (f x # q)"
  proof -
    have "distinct (T @ [x])" using dT by simp
    then show ?thesis using L hfx by simp
  qed
  moreover have "set (f x # q) = cyc f x"
  proof -
    have "set (T @ [x]) = set (x # T)" by simp
    then show ?thesis using L hfx sT by simp
  qed
  ultimately show ?thesis by (rule that)
qed

lemma closed_funpow:
  assumes cl: "\<And>w. w \<in> S \<Longrightarrow> f w \<in> S" and w: "w \<in> S"
  shows "(f ^^ k) w \<in> S"
  by (induction k) (simp_all add: w cl)

lemma closed_inv:
  assumes cl: "\<And>w. w \<in> S \<Longrightarrow> f w \<in> S" and w: "w \<in> S"
  shows "inv f w \<in> S"
  using closed_funpow[OF cl w, of "order f w - 1"] inv_funpow_order[of w] by simp

end

end
