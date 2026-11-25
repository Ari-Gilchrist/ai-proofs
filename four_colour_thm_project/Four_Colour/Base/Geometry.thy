(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Geometry.thy
    The geometrical interpretation of hypermaps: bridgeless, plain, cubic maps,
    face bands, simple paths, rings, adjacency, and the special Euler formulae.
    Ported from G. Gonthier's Coq development (geometry.v).
*)
theory Geometry
  imports Jordan
begin

section \<open>Bridges and loops\<close>

definition bridgeless :: "'a hypermap \<Rightarrow> bool" where
  "bridgeless G \<longleftrightarrow> (\<forall>x \<in> darts G. \<not> fconnect (face G) x (edge G x))"

definition loopless :: "'a hypermap \<Rightarrow> bool" where
  "loopless G \<longleftrightarrow> (\<forall>x \<in> darts G. \<not> fconnect (node G) x (edge G x))"

abbreviation arity :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> nat" where
  "arity G x \<equiv> order (face G) x"

section \<open>Special maps\<close>

definition plainb :: "'a hypermap \<Rightarrow> 'a set \<Rightarrow> bool" where
  "plainb G A \<longleftrightarrow> (\<forall>x \<in> A. order (edge G) x = 2)"

definition plain :: "'a hypermap \<Rightarrow> bool" where
  "plain G \<longleftrightarrow> plainb G (darts G)"

definition cubicb :: "'a hypermap \<Rightarrow> 'a set \<Rightarrow> bool" where
  "cubicb G A \<longleftrightarrow> (\<forall>x \<in> A. order (node G) x = 3)"

definition cubic :: "'a hypermap \<Rightarrow> bool" where
  "cubic G \<longleftrightarrow> cubicb G (darts G)"

definition precubic :: "'a hypermap \<Rightarrow> bool" where
  "precubic G \<longleftrightarrow> (\<forall>x \<in> darts G. order (node G) x \<le> 3)"

definition pentagonal :: "'a hypermap \<Rightarrow> bool" where
  "pentagonal G \<longleftrightarrow> (\<forall>x \<in> darts G. 4 < arity G x)"

definition quasicubic :: "'a hypermap \<Rightarrow> 'a list \<Rightarrow> bool" where
  "quasicubic G r \<longleftrightarrow> cubicb G (darts G - set r)"

definition ucycle :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "ucycle rel p \<longleftrightarrow> cycle rel p \<and> distinct p"

text \<open>Gonthier's record types of geometrical assumptions become conjunctions.\<close>

definition planar_bridgeless :: "'a hypermap \<Rightarrow> bool" where
  "planar_bridgeless G \<longleftrightarrow> hypermap G \<and> planar G \<and> bridgeless G"

definition plain_cubic :: "'a hypermap \<Rightarrow> bool" where
  "plain_cubic G \<longleftrightarrow> hypermap G \<and> plain G \<and> cubic G"

definition plain_cubic_connected :: "'a hypermap \<Rightarrow> bool" where
  "plain_cubic_connected G \<longleftrightarrow> plain_cubic G \<and> connected G"

definition planar_plain_cubic_connected :: "'a hypermap \<Rightarrow> bool" where
  "planar_plain_cubic_connected G \<longleftrightarrow> plain_cubic_connected G \<and> planar G"

definition plain_cubic_pentagonal :: "'a hypermap \<Rightarrow> bool" where
  "plain_cubic_pentagonal G \<longleftrightarrow> plain_cubic G \<and> pentagonal G"

definition planar_bridgeless_plain :: "'a hypermap \<Rightarrow> bool" where
  "planar_bridgeless_plain G \<longleftrightarrow> planar_bridgeless G \<and> plain G"

definition planar_bridgeless_plain_connected :: "'a hypermap \<Rightarrow> bool" where
  "planar_bridgeless_plain_connected G \<longleftrightarrow> planar_bridgeless_plain G \<and> connected G"

definition planar_bridgeless_plain_precubic :: "'a hypermap \<Rightarrow> bool" where
  "planar_bridgeless_plain_precubic G \<longleftrightarrow> planar_bridgeless_plain G \<and> precubic G"

definition plain_quasicubic :: "'a hypermap \<Rightarrow> 'a list \<Rightarrow> bool" where
  "plain_quasicubic G r \<longleftrightarrow> hypermap G \<and> plain G \<and> quasicubic G r"

definition ucycle_plain_quasicubic :: "'a hypermap \<Rightarrow> 'a list \<Rightarrow> bool" where
  "ucycle_plain_quasicubic G r \<longleftrightarrow>
     plain_quasicubic G r \<and> ucycle (frel (node G)) r \<and> set r \<subseteq> darts G"

definition ucycle_planar_plain_quasicubic :: "'a hypermap \<Rightarrow> 'a list \<Rightarrow> bool" where
  "ucycle_planar_plain_quasicubic G r \<longleftrightarrow> ucycle_plain_quasicubic G r \<and> planar G"

definition ucycle_plain_quasicubic_connected :: "'a hypermap \<Rightarrow> 'a list \<Rightarrow> bool" where
  "ucycle_plain_quasicubic_connected G r \<longleftrightarrow> ucycle_plain_quasicubic G r \<and> connected G"

section \<open>Face bands, simple paths and kernels\<close>

definition fband :: "'a hypermap \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> bool" where
  "fband G p x \<longleftrightarrow> (\<exists>y \<in> set p. fconnect (face G) x y)"

definition kernel :: "'a hypermap \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> bool" where
  "kernel G p x \<longleftrightarrow> \<not> fband G p x"

definition simple :: "'a hypermap \<Rightarrow> 'a list \<Rightarrow> bool" where
  "simple G p \<longleftrightarrow> distinct (map (cyc (face G)) p)"

definition scycle :: "'a hypermap \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "scycle G rel p \<longleftrightarrow> cycle rel p \<and> simple G p"

definition fproj :: "'a hypermap \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a" where
  "fproj G p x = (case find (fconnect (face G) x) p of Some y \<Rightarrow> y | None \<Rightarrow> x)"

definition scycle_planar_bridgeless_plain_quasicubic_connected ::
  "'a hypermap \<Rightarrow> 'a list \<Rightarrow> bool" where
  "scycle_planar_bridgeless_plain_quasicubic_connected G r \<longleftrightarrow>
     ucycle_plain_quasicubic_connected G r \<and> simple G r \<and> planar G \<and> bridgeless G"

section \<open>Ring links and adjacency\<close>

definition rlink :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "rlink G x y \<longleftrightarrow> fconnect (face G) (edge G x) y"

definition adj :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "adj G x y \<longleftrightarrow> (\<exists>z. fconnect (face G) x z \<and> rlink G z y)"

definition next_in :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a" where
  "next_in r x = (if x \<in> set r then r ! (Suc (lindex r x) mod length r) else x)"

definition prev_in :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a" where
  "prev_in r x = (if x \<in> set r then r ! ((lindex r x + length r - 1) mod length r) else x)"

definition chordless :: "'a hypermap \<Rightarrow> 'a list \<Rightarrow> bool" where
  "chordless G r \<longleftrightarrow> (\<forall>x \<in> set r. \<forall>y \<in> set r. y \<noteq> prev_in r x \<longrightarrow> y \<noteq> next_in r x \<longrightarrow>
                       \<not> adj G x y)"

fun insertE :: "'a hypermap \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "insertE G [] = []"
| "insertE G (x # p) = x # edge G x # insertE G p"

section \<open>Basic properties\<close>

context hypermap
begin

lemma bridgeless_cface: "bridgeless G \<Longrightarrow> x \<in> D \<Longrightarrow> \<not> cface x (e x)"
  by (simp add: bridgeless_def)

lemma arity_cface: "cface x y \<Longrightarrow> arity G x = arity G y"
  by (rule F.order_eq)

lemma arity_face [simp]: "arity G (f x) = arity G x"
  by simp

lemma arity_funpow_face [simp]: "arity G ((f ^^ k) x) = arity G x"
  using F.order_eq[OF fconnect_funpow[of f x k]] by simp

lemma funpow_face_arity [simp]: "(f ^^ arity G x) x = x"
  by simp

subsection \<open>Plain and cubic maps\<close>

lemma plain_order: "plain G \<Longrightarrow> x \<in> D \<Longrightarrow> order e x = 2"
  by (simp add: plain_def plainb_def)

lemma plain_eq [simp]: "plain G \<Longrightarrow> e (e x) = x"
proof (cases "x \<in> D")
  case True
  assume p: "plain G"
  have "(e ^^ 2) x = x" using plain_order[OF p True] E.funpow_order[of x] by simp
  then show ?thesis by (simp add: numeral_2_eq_2)
next
  case False
  then show ?thesis by simp
qed

lemma plain_neq:
  assumes "plain G" "x \<in> D"
  shows "e x \<noteq> x"
proof
  assume "e x = x"
  then have "order e x = 1" by (rule E.order_1_iff[THEN iffD2])
  then show False using plain_order[OF assms] by simp
qed

lemma plain_eq': "plain G \<Longrightarrow> n (f x) = e x"
proof -
  assume p: "plain G"
  have "n (f (e (e x))) = e x" by (rule edgeK)
  then show ?thesis using plain_eq[OF p] by simp
qed

lemma plain_orbit: "plain G \<Longrightarrow> cedge x y \<longleftrightarrow> y = x \<or> y = e x"
proof -
  assume p: "plain G"
  have k: "(e ^^ k) x = x \<or> (e ^^ k) x = e x" for k
    by (induction k) (auto simp: plain_eq[OF p])
  show ?thesis
  proof
    assume "cedge x y"
    then obtain k where "(e ^^ k) x = y" unfolding fconnect_def by blast
    then show "y = x \<or> y = e x" using k[of k] by auto
  next
    assume "y = x \<or> y = e x"
    then show "cedge x y" using fconnect_step[of e x] by auto
  qed
qed

lemma plainP:
  "plainb G A \<longleftrightarrow> (\<forall>x \<in> A. e (e x) = x \<and> e x \<noteq> x)"
proof
  assume pA: "plainb G A"
  show "\<forall>x \<in> A. e (e x) = x \<and> e x \<noteq> x"
  proof
    fix x assume xA: "x \<in> A"
    have o: "order e x = 2" using pA xA by (simp add: plainb_def)
    have "(e ^^ 2) x = x" using o E.funpow_order[of x] by simp
    moreover have "e x \<noteq> x" using o E.order_1_iff[of x] by simp
    ultimately show "e (e x) = x \<and> e x \<noteq> x" by (simp add: numeral_2_eq_2)
  qed
next
  assume h: "\<forall>x \<in> A. e (e x) = x \<and> e x \<noteq> x"
  show "plainb G A" unfolding plainb_def
  proof
    fix x assume xA: "x \<in> A"
    have c: "cycle (frel e) [x, e x]" using h xA by (simp add: cycle_Cons)
    have d: "distinct [x, e x]" using h xA by auto
    have "cyc e x = set [x, e x]" by (rule F.distinct_cycle_cyc[OF E.fperm_axioms c d]) simp
    then show "order e x = 2" using d by (simp add: order_def)
  qed
qed

lemma cubic_order: "cubic G \<Longrightarrow> x \<in> D \<Longrightarrow> order n x = 3"
  by (simp add: cubic_def cubicb_def)

lemma cubicP:
  "cubicb G A \<longleftrightarrow> (\<forall>x \<in> A. n (n (n x)) = x \<and> n x \<noteq> x)"
proof
  assume cA: "cubicb G A"
  show "\<forall>x \<in> A. n (n (n x)) = x \<and> n x \<noteq> x"
  proof
    fix x assume xA: "x \<in> A"
    have o: "order n x = 3" using cA xA by (simp add: cubicb_def)
    have "(n ^^ 3) x = x" using o N.funpow_order[of x] by simp
    moreover have "n x \<noteq> x" using o N.order_1_iff[of x] by simp
    ultimately show "n (n (n x)) = x \<and> n x \<noteq> x" by (simp add: numeral_3_eq_3)
  qed
next
  assume h: "\<forall>x \<in> A. n (n (n x)) = x \<and> n x \<noteq> x"
  show "cubicb G A" unfolding cubicb_def
  proof
    fix x assume xA: "x \<in> A"
    have n3: "n (n (n x)) = x" and n1: "n x \<noteq> x" using h xA by auto
    have n2: "n (n x) \<noteq> x"
    proof
      assume "n (n x) = x"
      then have "n x = x" using n3 by simp
      then show False using n1 by simp
    qed
    have n21: "n (n x) \<noteq> n x" using n1 by simp
    have c: "cycle (frel n) [x, n x, n (n x)]" using n3 by (simp add: cycle_Cons)
    have d: "distinct [x, n x, n (n x)]" using n1 n2 n21 by auto
    have "cyc n x = set [x, n x, n (n x)]" by (rule F.distinct_cycle_cyc[OF N.fperm_axioms c d]) simp
    then show "order n x = 3" using d by (simp add: order_def)
  qed
qed

lemma cubic_eq: "cubic G \<Longrightarrow> x \<in> D \<Longrightarrow> n (n (n x)) = x"
  using cubicP by (simp add: cubic_def)

lemma cubic_neq: "cubic G \<Longrightarrow> x \<in> D \<Longrightarrow> n x \<noteq> x"
  using cubicP by (simp add: cubic_def)

lemma cubic_eq': "cubic G \<Longrightarrow> x \<in> D \<Longrightarrow> n (n x) = f (e x)"
proof -
  assume c: "cubic G" and xD: "x \<in> D"
  have "n (n (n (f (e x)))) = f (e x)" using cubic_eq[OF c] xD by simp
  moreover have "n (f (e x)) = x" by (rule edgeK)
  ultimately show ?thesis by simp
qed

lemma quasicubic_eq: "quasicubic G r \<Longrightarrow> x \<in> D \<Longrightarrow> x \<notin> set r \<Longrightarrow> n (n (n x)) = x"
  using cubicP by (simp add: quasicubic_def)

lemma cubic_precubic: "cubic G \<Longrightarrow> precubic G"
  by (simp add: cubic_def cubicb_def precubic_def)

subsection \<open>Face bands and simple paths\<close>

lemma fband_Cons: "fband G (x # p) y \<longleftrightarrow> cface y x \<or> fband G p y"
  by (simp add: fband_def)

lemma fband_append: "fband G (p1 @ p2) y \<longleftrightarrow> fband G p1 y \<or> fband G p2 y"
  by (auto simp: fband_def)

lemma fband_ring: "x \<in> set p \<Longrightarrow> fband G p x"
  by (auto simp: fband_def)

lemma fband_cface:
  assumes xy: "cface x y"
  shows "fband G p x \<longleftrightarrow> fband G p y"
proof -
  have yx: "cface y x" by (rule F.fconnect_sym[OF xy])
  show ?thesis unfolding fband_def
    using fconnect_trans[OF xy] fconnect_trans[OF yx] by blast
qed

lemma fband_face [simp]: "fband G p (f x) \<longleftrightarrow> fband G p x"
  by (rule fband_cface[symmetric]) simp

lemma simple_Cons: "simple G (x # p) \<longleftrightarrow> \<not> fband G p x \<and> simple G p"
proof -
  have "cyc f x \<in> cyc f ` set p \<longleftrightarrow> fband G p x"
    unfolding fband_def by (auto simp: F.cyc_eq_iff)
  then show ?thesis by (simp add: simple_def)
qed

lemma simple_append:
  "simple G (p1 @ p2) \<longleftrightarrow> simple G p1 \<and> (\<forall>x \<in> set p2. \<not> fband G p1 x) \<and> simple G p2"
proof -
  have "(cyc f ` set p1 \<inter> cyc f ` set p2 = {}) \<longleftrightarrow> (\<forall>x \<in> set p2. \<not> fband G p1 x)"
  proof -
    have "(\<exists>x \<in> set p2. \<exists>y \<in> set p1. cyc f y = cyc f x) \<longleftrightarrow> (\<exists>x \<in> set p2. fband G p1 x)"
      unfolding fband_def using F.cyc_eq_iff F.fconnect_commute by metis
    then show ?thesis by blast
  qed
  then show ?thesis by (auto simp: simple_def)
qed

lemma simple_distinct: "simple G p \<Longrightarrow> distinct p"
  by (simp add: simple_def distinct_map)

lemma simple_cface:
  assumes "simple G p" "x \<in> set p" "y \<in> set p" "cface x y"
  shows "x = y"
proof -
  have "inj_on (cyc f) (set p)" using assms(1) by (simp add: simple_def distinct_map)
  moreover have "cyc f x = cyc f y" using assms(4) by (simp add: F.cyc_eq)
  ultimately show ?thesis using assms(2,3) by (simp add: inj_on_def)
qed

lemma simple_rev: "simple G (rev p) \<longleftrightarrow> simple G p"
  by (simp add: simple_def rev_map[symmetric])

lemma simple_rotate: "simple G (rotate k p) \<longleftrightarrow> simple G p"
  by (simp add: simple_def rotate_map[symmetric])

lemma kernel_off_ring: "kernel G p x \<Longrightarrow> x \<notin> set p"
  by (auto simp: kernel_def fband_def)

lemma simple_fcard_fband:
  assumes "simple G p" "set p \<subseteq> D"
  shows "fcard f {x \<in> D. fband G p x} = length p"
proof -
  have "cyc f ` {x \<in> D. fband G p x} = cyc f ` set p"
  proof
    show "cyc f ` {x \<in> D. fband G p x} \<subseteq> cyc f ` set p"
      unfolding fband_def by (auto simp: F.cyc_eq_iff)
    show "cyc f ` set p \<subseteq> cyc f ` {x \<in> D. fband G p x}"
      using assms(2) by (auto simp: fband_def)
  qed
  moreover have "card (cyc f ` set p) = length p"
  proof -
    have "distinct (map (cyc f) p)" using assms(1) by (simp add: simple_def)
    then have "card (set (map (cyc f) p)) = length (map (cyc f) p)" by (rule distinct_card)
    then show ?thesis by simp
  qed
  ultimately show ?thesis by (simp add: fcard_def)
qed

subsection \<open>Ring links and adjacency\<close>

lemma rlinkE [simp]: "rlink G x (e x)"
  by (simp add: rlink_def)

lemma rlink_cface:
  assumes y12: "cface y1 y2"
  shows "rlink G x y1 \<longleftrightarrow> rlink G x y2"
proof -
  have y21: "cface y2 y1" by (rule F.fconnect_sym[OF y12])
  show ?thesis unfolding rlink_def
    using fconnect_trans[OF _ y12, of "e x"] fconnect_trans[OF _ y21, of "e x"] by blast
qed

lemma adj_iff: "adj G x y \<longleftrightarrow> (\<exists>z. cface x z \<and> cface (e z) y)"
  by (simp add: adj_def rlink_def)

lemma rlink_adj: "rlink G x y \<Longrightarrow> adj G x y"
  by (auto simp: adj_def)

lemma adjE [simp]: "adj G x (e x)"
  by (rule rlink_adj) simp

lemma adj_cface:
  assumes x12: "cface x1 x2"
  shows "adj G x1 y \<longleftrightarrow> adj G x2 y"
proof -
  have x21: "cface x2 x1" by (rule F.fconnect_sym[OF x12])
  show ?thesis unfolding adj_def
    using fconnect_trans[OF x12] fconnect_trans[OF x21] by blast
qed

lemma adj_cface_r: "cface y1 y2 \<Longrightarrow> adj G x y1 \<longleftrightarrow> adj G x y2"
  unfolding adj_def using rlink_cface by blast

lemma adj_face [simp]: "adj G (f x) y \<longleftrightarrow> adj G x y"
  by (rule adj_cface[symmetric]) simp

lemma adj_face_r [simp]: "adj G x (f y) \<longleftrightarrow> adj G x y"
  by (rule adj_cface_r[symmetric]) simp

lemma adjN [simp]: "adj G (n x) x"
proof -
  have "adj G (n x) (e (n x))" by simp
  then have "adj G (n x) (f (e (n x)))" by simp
  then show ?thesis by (simp add: nodeK)
qed

lemma adj_sym: "plain G \<Longrightarrow> adj G x y \<Longrightarrow> adj G y x"
proof -
  assume p: "plain G" and "adj G x y"
  then obtain z where z: "cface x z" "cface (e z) y" by (auto simp: adj_iff)
  have "cface y (e z)" using z(2) by (rule F.fconnect_sym)
  moreover have "cface (e (e z)) x" using z(1) plain_eq[OF p] F.fconnect_sym by simp
  ultimately show "adj G y x" by (auto simp: adj_iff)
qed

lemma adj_no_cface: "bridgeless G \<Longrightarrow> x \<in> D \<Longrightarrow> adj G x y \<Longrightarrow> \<not> cface x y"
proof
  assume b: "bridgeless G" and xD: "x \<in> D" and "adj G x y" and xy: "cface x y"
  then obtain z where z: "cface x z" "cface (e z) y" by (auto simp: adj_iff)
  have "cface z (e z)"
    using fconnect_trans[OF F.fconnect_sym[OF z(1)] fconnect_trans[OF xy F.fconnect_sym[OF z(2)]]] .
  moreover have "z \<in> D" using z(1) xD F.fconnect_in_D by blast
  ultimately show False using b by (simp add: bridgeless_def)
qed

lemma mem_insertE: "plain G \<Longrightarrow> x \<in> set (insertE G p) \<longleftrightarrow> (\<exists>y \<in> set p. cedge x y)"
proof (induction p)
  case Nil
  then show ?case by simp
next
  case (Cons y p)
  have "cedge x y \<longleftrightarrow> cedge y x" by (rule E.fconnect_commute)
  also have "\<dots> \<longleftrightarrow> x = y \<or> x = e y" using plain_orbit[OF Cons.prems] by blast
  finally have "cedge x y \<longleftrightarrow> x = y \<or> x = e y" .
  then show ?case using Cons by auto
qed

lemma length_insertE [simp]: "length (insertE G p) = 2 * length p"
  by (induction p) auto

lemma insertE_append: "insertE G (p1 @ p2) = insertE G p1 @ insertE G p2"
  by (induction p1) auto

end

section \<open>Counting with uniform orbits\<close>

lemma (in fperm) card_uniform_orbits:
  assumes AD: "A \<subseteq> D" and cl: "\<And>x. x \<in> A \<Longrightarrow> f x \<in> A" and o: "\<And>x. x \<in> A \<Longrightarrow> order f x = k"
  shows "card A = k * fcard f A"
proof -
  have cycA: "cyc f x \<subseteq> A" if "x \<in> A" for x
  proof
    fix y assume "y \<in> cyc f x"
    then have "fconnect f x y" by (simp add: in_cyc_iff)
    then show "y \<in> A"
      by (induction rule: fconnect_induct) (use that cl in auto)
  qed
  have U: "\<Union> (cyc f ` A) = A" using cycA by auto
  have finA: "finite A" using AD fin by (rule finite_subset)
  have "k * card (cyc f ` A) = card (\<Union> (cyc f ` A))"
  proof (rule card_partition)
    show "finite (cyc f ` A)" using finA by simp
    show "finite (\<Union> (cyc f ` A))" using U finA by simp
    show "\<And>c. c \<in> cyc f ` A \<Longrightarrow> card c = k" using o by (auto simp: order_def)
    show "\<And>c1 c2. c1 \<in> cyc f ` A \<Longrightarrow> c2 \<in> cyc f ` A \<Longrightarrow> c1 \<noteq> c2 \<Longrightarrow> c1 \<inter> c2 = {}"
      using cyc_disjoint_or_eq by blast
  qed
  then show ?thesis using U by (simp add: fcard_def)
qed

section \<open>The special Euler formulae\<close>

context hypermap
begin

theorem quasicubic_Euler:
  assumes h: "ucycle_plain_quasicubic_connected G r"
  shows "planar G \<longleftrightarrow>
         6 * ((if r = [] then 0 else 1) + fcard f D) = card D + (2 * length r + 12)"
proof -
  have plainG: "plain G" and qc: "quasicubic G r" and cyr: "cycle (frel n) r"
    and dr: "distinct r" and rD: "set r \<subseteq> D" and cc: "connected G"
    using h by (auto simp: ucycle_plain_quasicubic_connected_def ucycle_plain_quasicubic_def
        plain_quasicubic_def ucycle_def)
  define nbE where "nbE = fcard e D"
  define nbN where "nbN = fcard n D"
  define nbF where "nbF = fcard f D"
  define nn where "nn = fcard n (D - set r)"
  have eg: "Euler_lhs G = 2 * genus G + Euler_rhs G"
    using even_genusP[OF hypermap_axioms] by (simp add: even_genus_def)
  have pl: "planar G \<longleftrightarrow> Euler_lhs G = Euler_rhs G"
    using eg by (simp add: planar_def)
  have DE: "card D = 2 * nbE"
    unfolding nbE_def
    by (rule E.card_uniform_orbits) (use plainG in \<open>auto simp: plain_order\<close>)
  have rcl: "x \<in> set r \<Longrightarrow> cyc n x = set r" for x
    using F.distinct_cycle_cyc[OF N.fperm_axioms cyr dr] by simp
  have notr: "n x \<notin> set r" if "x \<in> D - set r" for x
  proof
    assume "n x \<in> set r"
    then have "cyc n (n x) = set r" by (rule rcl)
    then have cx: "cyc n x = set r" by simp
    have "x \<in> cyc n x" by (rule N.x_in_cyc)
    then have "x \<in> set r" using cx by blast
    then show False using that by simp
  qed
  have Dr: "card (D - set r) = 3 * nn"
    unfolding nn_def
  proof (rule N.card_uniform_orbits)
    show "D - set r \<subseteq> D" by blast
    show "\<And>x. x \<in> D - set r \<Longrightarrow> n x \<in> D - set r" using notr by simp
    show "\<And>x. x \<in> D - set r \<Longrightarrow> order n x = 3"
      using qc by (simp add: quasicubic_def cubicb_def)
  qed
  have cD: "card D = length r + card (D - set r)"
  proof -
    have "card (D - set r) = card D - card (set r)"
      using rD finite_darts by (simp add: card_Diff_subset)
    moreover have "card (set r) \<le> card D" using rD finite_darts by (simp add: card_mono)
    moreover have "card (set r) = length r" using dr by (simp add: distinct_card)
    ultimately show ?thesis by simp
  qed
  have NN: "nbN = (if r = [] then 0 else 1) + nn"
  proof -
    have img: "cyc n ` D = cyc n ` (D - set r) \<union> cyc n ` set r" using rD by blast
    have disj: "cyc n ` (D - set r) \<inter> cyc n ` set r = {}"
    proof -
      { fix x y assume x: "x \<in> D - set r" and y: "y \<in> set r" and eq: "cyc n x = cyc n y"
        then have "x \<in> cyc n y" by (metis N.x_in_cyc)
        then have "x \<in> set r" using rcl[OF y] by simp
        then have False using x by simp }
      then show ?thesis by blast
    qed
    have one: "cyc n ` set r = (if r = [] then {} else {set r})"
      using rcl by (cases r) auto
    have "card (cyc n ` D) = card (cyc n ` (D - set r)) + card (cyc n ` set r)"
      unfolding img by (rule card_Un_disjoint) (use finite_darts disj in auto)
    then show ?thesis unfolding nbN_def nn_def fcard_def using one by simp
  qed
  have nc1: "n_comp (glink G) D = 1" using cc by (simp add: connected_def)
  have "Euler_lhs G = 2 + card D" using nc1 by (simp add: Euler_lhs_def)
  moreover have "Euler_rhs G = nbE + nbN + nbF" by (simp add: Euler_rhs_def nbE_def nbN_def nbF_def)
  ultimately have "planar G \<longleftrightarrow> 2 + card D = nbE + nbN + nbF" using pl by simp
  also have "\<dots> \<longleftrightarrow> 6 * ((if r = [] then 0 else 1) + nbF) = card D + (2 * length r + 12)"
  proof -
    define b :: nat where "b = (if r = [] then 0 else 1)"
    have NN': "nbN = b + nn" using NN unfolding b_def .
    have "2 + card D = nbE + nbN + nbF \<longleftrightarrow> 6 * (b + nbF) = card D + (2 * length r + 12)"
    proof
      assume "2 + card D = nbE + nbN + nbF"
      then show "6 * (b + nbF) = card D + (2 * length r + 12)" using DE Dr cD NN' by presburger
    next
      assume "6 * (b + nbF) = card D + (2 * length r + 12)"
      then show "2 + card D = nbE + nbN + nbF" using DE Dr cD NN' by presburger
    qed
    then show ?thesis unfolding b_def .
  qed
  finally show ?thesis unfolding nbF_def .
qed

corollary cubic_Euler:
  assumes "plain_cubic_connected G"
  shows "planar G \<longleftrightarrow> 6 * fcard f D = card D + 12"
proof -
  have "ucycle_plain_quasicubic_connected G []"
    using assms by (simp add: plain_cubic_connected_def plain_cubic_def
        ucycle_plain_quasicubic_connected_def ucycle_plain_quasicubic_def plain_quasicubic_def
        quasicubic_def cubic_def ucycle_def)
  then show ?thesis using quasicubic_Euler[of "[]"] by simp
qed

end

end
