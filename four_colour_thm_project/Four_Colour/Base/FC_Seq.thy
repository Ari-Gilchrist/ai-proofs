(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      FC_Seq.thy
    Sequence (list) utilities in the style of the SSReflect seq/path libraries,
    used throughout the Four Colour Theorem development.
*)
theory FC_Seq
  imports Main
begin

section \<open>Paths and cycles over lists\<close>

text \<open>
  We follow the conventions of the SSReflect @{text path} library: a path
  @{term "path r x p"} starts at the explicit head @{term x} and visits the
  elements of @{term p} in order; @{term "lastd x p"} is the last element of the
  non-empty list @{term "x # p"}.
\<close>

fun path :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "path r x [] = True"
| "path r x (y # p) = (r x y \<and> path r y p)"

abbreviation lastd :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a" where
  "lastd x p \<equiv> last (x # p)"

abbreviation belast :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "belast x p \<equiv> butlast (x # p)"

definition cycle :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "cycle r p = (case p of [] \<Rightarrow> True | x # q \<Rightarrow> path r x (q @ [x]))"

lemma cycle_Nil [simp]: "cycle r []"
  by (simp add: cycle_def)

lemma cycle_Cons: "cycle r (x # q) = path r x (q @ [x])"
  by (simp add: cycle_def)

lemma path_append [simp]:
  "path r x (p @ q) = (path r x p \<and> path r (lastd x p) q)"
  by (induction p arbitrary: x) auto

lemma path_snoc:
  "path r x (p @ [y]) = (path r x p \<and> r (lastd x p) y)"
  by simp

lemma path_mono:
  assumes "\<And>a b. r a b \<Longrightarrow> s a b" "path r x p"
  shows "path s x p"
  using assms(2) by (induction p arbitrary: x) (auto intro: assms(1))

lemma path_cong_in:
  assumes "\<And>a b. a \<in> set (x # p) \<Longrightarrow> b \<in> set p \<Longrightarrow> r a b = s a b"
  shows "path r x p = path s x p"
  using assms by (induction p arbitrary: x) auto

lemma path_mono_in:
  assumes "\<And>a b. a \<in> set (x # p) \<Longrightarrow> b \<in> set p \<Longrightarrow> r a b \<Longrightarrow> s a b"
    "path r x p"
  shows "path s x p"
  using assms by (induction p arbitrary: x) auto

lemma path_nth:
  "path r x p = (\<forall>i < length p. r ((x # p) ! i) (p ! i))"
proof (induction p arbitrary: x)
  case Nil
  then show ?case by simp
next
  case (Cons y p)
  show ?case
    by (simp add: Cons.IH All_less_Suc2)
qed

lemma path_map:
  "path r (f x) (map f p) = path (\<lambda>a b. r (f a) (f b)) x p"
  by (induction p arbitrary: x) auto

lemma path_rev:
  "path r (lastd x p) (rev (belast x p)) = path (\<lambda>a b. r b a) x p"
proof (induction p arbitrary: x)
  case Nil
  then show ?case by simp
next
  case (Cons y p)
  have "path r (lastd y p) (rev (belast y p) @ [x]) = (path r (lastd y p) (rev (belast y p)) \<and> r (lastd (lastd y p) (rev (belast y p))) x)"
    by simp
  moreover have "lastd (lastd y p) (rev (belast y p)) = y"
    by (induction p arbitrary: y) (auto simp: last_append)
  ultimately show ?case
    using Cons.IH[of y] by auto
qed

lemma lastd_append: "lastd x (p @ q) = lastd (lastd x p) q"
  by (induction p arbitrary: x) auto

lemma lastd_snoc [simp]: "lastd x (p @ [y]) = y"
  by simp

lemma lastd_in: "lastd x p \<in> set (x # p)"
  by simp

lemma lastd_in_p: "p \<noteq> [] \<Longrightarrow> lastd x p \<in> set p"
  by simp

lemma belast_snoc: "belast x p @ [lastd x p] = x # p"
  by simp

lemma set_belast: "set (x # p) = set (belast x p) \<union> {lastd x p}"
  by (metis append_butlast_last_id list.distinct(1) set_append set_simps(1) set_simps(2))

lemma length_belast [simp]: "length (belast x p) = length p"
  by simp

lemma path_rcons_cycle:
  "cycle r (x # p) = (path r x p \<and> r (lastd x p) x)"
  by (simp add: cycle_Cons)

section \<open>The @{text mem2} predicate\<close>

text \<open>@{term "mem2 p x y"}: @{term y} occurs in @{term p} at or after the first
  occurrence of @{term x}.\<close>

fun lindex :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "lindex [] x = 0"
| "lindex (a # p) x = (if a = x then 0 else Suc (lindex p x))"

lemma lindex_le: "lindex p x \<le> length p"
  by (induction p) auto

lemma lindex_less: "x \<in> set p \<Longrightarrow> lindex p x < length p"
  by (induction p) auto

lemma nth_lindex: "x \<in> set p \<Longrightarrow> p ! lindex p x = x"
  by (induction p) auto

lemma lindex_nth_distinct: "distinct p \<Longrightarrow> i < length p \<Longrightarrow> lindex p (p ! i) = i"
  by (induction p arbitrary: i) (auto simp: nth_Cons split: nat.splits)

lemma lindex_append:
  "lindex (p @ q) x = (if x \<in> set p then lindex p x else length p + lindex q x)"
  by (induction p) auto

definition mem2 :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "mem2 p x y = (y \<in> set (drop (lindex p x) p))"

lemma mem2_Nil [simp]: "\<not> mem2 [] x y"
  by (simp add: mem2_def)

lemma mem2_Cons:
  "mem2 (a # p) x y = (if a = x then y \<in> set (a # p) else mem2 p x y)"
  by (simp add: mem2_def)

lemma mem2_l: "mem2 p x y \<Longrightarrow> x \<in> set p"
  by (induction p) (auto simp: mem2_Cons split: if_splits)

lemma mem2_r: "mem2 p x y \<Longrightarrow> y \<in> set p"
  by (induction p) (auto simp: mem2_Cons split: if_splits)

lemma mem2_refl [simp]: "mem2 p x x = (x \<in> set p)"
  by (induction p) (auto simp: mem2_Cons)

lemma mem2_append:
  "mem2 (p @ q) x y =
     (if x \<in> set p then y \<in> set (drop (lindex p x) p) \<or> y \<in> set q else mem2 q x y)"
  by (induction p) (auto simp: mem2_Cons)

lemma mem2_splitI:
  "x \<in> set (p1 @ x # p2) \<Longrightarrow> x \<notin> set p1 \<Longrightarrow> y \<in> set (x # p2) \<Longrightarrow> mem2 (p1 @ x # p2) x y"
  by (induction p1) (auto simp: mem2_Cons)

lemma mem2_split_iff:
  assumes "x \<notin> set p1"
  shows "mem2 (p1 @ x # p2) x y = (y \<in> set (x # p2))"
  using assms by (induction p1) (auto simp: mem2_Cons)

lemma mem2E:
  assumes "mem2 p x y"
  obtains p1 p2 where "p = p1 @ x # p2" "x \<notin> set p1" "y \<in> set (x # p2)"
proof -
  from assms have "x \<in> set p" by (rule mem2_l)
  then obtain p1 p2 where p: "p = p1 @ x # p2" "x \<notin> set p1"
    using split_list_first by metis
  with assms mem2_split_iff[of x p1 p2 y] show ?thesis
    using that by auto
qed

lemma mem2_distinctE:
  assumes "mem2 p x y" "distinct p"
  obtains p1 p2 p3 where "p = p1 @ x # p2 @ y # p3 \<or> (x = y \<and> p = p1 @ x # p3)"
proof -
  obtain p1 p2 where p: "p = p1 @ x # p2" "y \<in> set (x # p2)"
    using assms(1) by (rule mem2E)
  show thesis
  proof (cases "y = x")
    case True
    then show ?thesis using that p by blast
  next
    case False
    with p obtain q1 q2 where "p2 = q1 @ y # q2"
      by (auto dest: split_list)
    with p show ?thesis using that by blast
  qed
qed

lemma mem2_lindex:
  "distinct p \<Longrightarrow> mem2 p x y = (x \<in> set p \<and> y \<in> set p \<and> lindex p x \<le> lindex p y)"
  by (induction p) (auto simp: mem2_Cons)

lemma lindex_rev:
  "distinct p \<Longrightarrow> x \<in> set p \<Longrightarrow> lindex (rev p) x = length p - 1 - lindex p x"
proof (induction p)
  case Nil
  then show ?case by simp
next
  case (Cons a p)
  then show ?case
    by (auto simp: lindex_append dest: lindex_less)
qed

lemma mem2_rev_distinct:
  assumes "distinct p" "x \<noteq> y"
  shows "mem2 (rev p) x y = (x \<in> set p \<and> y \<in> set p \<and> \<not> mem2 p x y)"
proof (cases "x \<in> set p \<and> y \<in> set p")
  case True
  then have "lindex p x \<noteq> lindex p y"
    using assms by (metis nth_lindex)
  moreover have "lindex p x < length p" "lindex p y < length p"
    using True by (auto intro: lindex_less)
  ultimately show ?thesis
    using True assms by (auto simp: mem2_lindex lindex_rev)
next
  case False
  then show ?thesis
    by (metis mem2_l mem2_r set_rev)
qed

section \<open>Rotation\<close>

lemma rotate1_Cons: "rotate1 (x # p) = p @ [x]"
  by simp

lemma distinct_rotate_iff: "distinct (rotate n p) = distinct p"
  by simp

lemma cycle_rotate1:
  "cycle r (rotate1 p) = cycle r p"
proof (cases p)
  case Nil
  then show ?thesis by simp
next
  case (Cons x q)
  show ?thesis
  proof (cases q)
    case Nil
    then show ?thesis using Cons by (simp add: cycle_Cons)
  next
    case (Cons y q')
    show ?thesis
      using \<open>p = x # q\<close> Cons by (auto simp: cycle_Cons)
  qed
qed

lemma cycle_rotate: "cycle r (rotate n p) = cycle r p"
  by (induction n) (simp_all add: cycle_rotate1)

lemma cycle_nth:
  "cycle r p = (\<forall>i < length p. r (p ! i) (p ! (Suc i mod length p)))"
proof (cases p)
  case Nil
  then show ?thesis by simp
next
  case (Cons x q)
  have "cycle r p = path r x (q @ [x])" using Cons by (simp add: cycle_Cons)
  also have "\<dots> = (\<forall>i < Suc (length q). r ((x # q @ [x]) ! i) ((q @ [x]) ! i))"
    by (subst path_nth) simp
  also have "\<dots> = (\<forall>i < length p. r (p ! i) (p ! (Suc i mod length p)))"
  proof -
    have "(x # q @ [x]) ! i = p ! i" if "i < Suc (length q)" for i
      using Cons that by (auto simp: nth_append nth_Cons split: nat.splits)
    moreover have "(q @ [x]) ! i = p ! (Suc i mod length p)" if "i < Suc (length q)" for i
      using Cons that by (cases "Suc i = Suc (length q)") (auto simp: nth_append)
    ultimately show ?thesis using Cons by auto
  qed
  finally show ?thesis .
qed

lemma cycle_map:
  "cycle r (map f p) = cycle (\<lambda>a b. r (f a) (f b)) p"
  by (cases p) (simp_all add: cycle_Cons path_map[symmetric])

lemma cycle_mono:
  assumes "\<And>a b. r a b \<Longrightarrow> s a b" "cycle r p"
  shows "cycle s p"
  using assms by (cases p) (auto simp: cycle_Cons intro: path_mono)

lemma cycle_rev:
  "cycle r (rev p) = cycle (\<lambda>a b. r b a) p"
proof (cases p)
  case Nil
  then show ?thesis by simp
next
  case (Cons x q)
  have "rotate (length q) (rev q @ [x]) = x # rev q"
    by (metis length_rev rotate_append append_Cons append_Nil)
  then have "cycle r (rev p) = cycle r (x # rev q)"
    using Cons cycle_rotate[of r "length q" "rev q @ [x]"] by simp
  also have "\<dots> = path r x (rev q @ [x])"
    by (simp add: cycle_Cons)
  also have "\<dots> = path r (lastd x (q @ [x])) (rev (belast x (q @ [x])))"
    by simp
  also have "\<dots> = path (\<lambda>a b. r b a) x (q @ [x])"
    by (rule path_rev)
  also have "\<dots> = cycle (\<lambda>a b. r b a) p"
    using Cons by (simp add: cycle_Cons)
  finally show ?thesis .
qed

lemma cycle_ConsD: "cycle r (x # p) \<Longrightarrow> path r x p"
  by (simp add: cycle_Cons)

section \<open>SSReflect-style rotation and pairwise maps\<close>

text \<open>@{term "rot n s"} rotates left by @{term n}, and is the identity when
  @{term n} is at least the length of @{term s} (unlike @{const rotate}).\<close>

definition rot :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rot n s = drop n s @ take n s"

lemma rot0 [simp]: "rot 0 s = s"
  by (simp add: rot_def)

lemma rot_oversize: "length s \<le> n \<Longrightarrow> rot n s = s"
  by (simp add: rot_def)

lemma length_rot [simp]: "length (rot n s) = length s"
  by (simp add: rot_def)

lemma set_rot [simp]: "set (rot n s) = set s"
  by (metis append_take_drop_id rot_def set_append sup_commute)

lemma rot_rotate: "n \<le> length s \<Longrightarrow> rot n s = rotate n s"
proof (cases "n = length s")
  case True
  then show ?thesis by (simp add: rot_def)
next
  case False
  assume "n \<le> length s"
  then have "n < length s" using False by simp
  then show ?thesis by (simp add: rot_def rotate_drop_take)
qed

lemma rot1_Cons: "rot 1 (x # s) = s @ [x]"
  by (simp add: rot_def)

lemma distinct_rot [simp]: "distinct (rot n s) \<longleftrightarrow> distinct s"
  by (metis append_take_drop_id distinct_append inf_commute rot_def)

lemma rot_add: "n + m \<le> length s \<Longrightarrow> rot (n + m) s = rot m (rot n s)"
  by (simp add: rot_rotate rotate_rotate add.commute)

fun pairmap :: "('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "pairmap f x [] = []"
| "pairmap f x (y # s) = f x y # pairmap f y s"

lemma length_pairmap [simp]: "length (pairmap f x s) = length s"
  by (induction s arbitrary: x) auto

fun scanl' :: "('a \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a list" where
  "scanl' f x [] = []"
| "scanl' f x (y # s) = f x y # scanl' f (f x y) s"

lemma length_scanl' [simp]: "length (scanl' f x s) = length s"
  by (induction s arbitrary: x) auto

end
