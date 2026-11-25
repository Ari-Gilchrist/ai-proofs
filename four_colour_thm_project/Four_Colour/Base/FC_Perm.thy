(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      FC_Perm.thy
    Cycle counting for permutations: composing with a transposition splits
    or merges cycles.
*)
theory FC_Perm
  imports FC_Fingraph
begin

lemma path_cong_src:
  assumes "\<And>y z. y \<in> set (belast x p) \<Longrightarrow> r y z = s y z"
  shows "path r x p = path s x p"
  using assms
proof (induction p arbitrary: x)
  case Nil
  then show ?case by simp
next
  case (Cons y p)
  have "r x y = s x y" using Cons.prems by simp
  moreover have "path r y p = path s y p"
    using Cons.prems by (intro Cons.IH) (cases p; auto)
  ultimately show ?case by simp
qed

lemma fconnect_eq_on:
  assumes eq: "\<And>y. fconnect f x y \<Longrightarrow> g y = f y"
  shows "fconnect g x y \<longleftrightarrow> fconnect f x y"
proof
  assume "fconnect g x y"
  then show "fconnect f x y"
  proof (induction rule: fconnect_induct)
    case refl
    then show ?case by simp
  next
    case (step w)
    have "g w = f w" by (rule eq[OF step(2)])
    then show ?case using fconnect_stepI_r[OF step(2)] by simp
  qed
next
  assume "fconnect f x y"
  then show "fconnect g x y"
  proof (induction rule: fconnect_induct)
    case refl
    then show ?case by simp
  next
    case (step w)
    have "g w = f w" by (rule eq[OF step(1)])
    then show ?case using fconnect_stepI_r[OF step(2)] by simp
  qed
qed

lemma cyc_eq_on:
  assumes "\<And>y. fconnect f x y \<Longrightarrow> g y = f y"
  shows "cyc g x = cyc f x"
  using fconnect_eq_on[OF assms] by (auto simp: cyc_def)

context fperm
begin

lemma orb_split2:
  assumes "fconnect f a b" "a \<noteq> b"
  obtains L1 L2 where "orb f a = a # L1 @ b # L2"
proof -
  define L where "L = tl (orb f a)"
  have L: "orb f a = a # L" unfolding L_def by (rule orb_Cons)
  have "b \<in> set (orb f a)" using assms(1) by (simp add: set_orb in_cyc_iff)
  then have bL: "b \<in> set L" using assms(2) L by simp
  from split_list[OF bL] obtain L1 L2 where t: "L = L1 @ b # L2" by (elim exE)
  have "orb f a = a # L1 @ b # L2" using L t by simp
  then show ?thesis by (rule that)
qed

lemma orb_path:
  "orb f a = a # L \<Longrightarrow> path (frel f) a (L @ [a])"
  using cycle_orb[of a] by (simp add: cycle_Cons)

lemma distinct_cycle_cyc:
  assumes "fperm g S" "cycle (frel g) l" "distinct l" "x \<in> set l"
  shows "cyc g x = set l"
  using fperm.fcycle_fconnect[OF assms] by (auto simp: cyc_def)

end

lemma cyc_transpose_merge:
  assumes fp: "fperm f S" and ab: "a \<in> S" "b \<in> S" "a \<noteq> b" and nc: "\<not> fconnect f a b"
  shows "cyc (f \<circ> Transposition.transpose a b) a = cyc f a \<union> cyc f b"
proof -
  interpret fperm f S by (rule fp)
  let ?q = "f \<circ> Transposition.transpose a b"
  have qp: "fperm ?q S"
  proof unfold_locales
    show "?q permutes S"
      using permutes_compose[OF permutes_swap_id[OF ab(1,2)] perm]
      by (simp add: Transposition.transpose_def swap_id_eq comp_def)
  qed (rule fin)
  have qa: "?q a = f b" and qb: "?q b = f a"
    by (auto simp: Transposition.transpose_def)
  have qx: "x \<noteq> a \<Longrightarrow> x \<noteq> b \<Longrightarrow> ?q x = f x" for x
    by (simp add: Transposition.transpose_def)
  define La where "La = tl (orb f a)"
  define Lb where "Lb = tl (orb f b)"
  have oa: "orb f a = a # La" unfolding La_def by (rule orb_Cons)
  have ob: "orb f b = b # Lb" unfolding Lb_def by (rule orb_Cons)
  have pa: "path (frel f) a (La @ [a])" using orb_path[OF oa] .
  have pb: "path (frel f) b (Lb @ [b])" using orb_path[OF ob] .
  have Cfa: "cyc f a = set (a # La)" using set_orb[of a] oa by simp
  have Cfb: "cyc f b = set (b # Lb)" using set_orb[of b] ob by simp
  have disj: "cyc f a \<inter> cyc f b = {}"
  proof -
    { fix z assume "z \<in> cyc f a" "z \<in> cyc f b"
      then have az: "fconnect f a z" and bz: "fconnect f b z" by (simp_all add: in_cyc_iff)
      have "fconnect f a b" by (rule fconnect_trans[OF az fconnect_sym[OF bz]])
      then have False using nc by simp }
    then show ?thesis by blast
  qed
  have da: "distinct (a # La)" using distinct_orb[of a] oa by simp
  have db: "distinct (b # Lb)" using distinct_orb[of b] ob by simp
  let ?l = "a # Lb @ b # La"
  have dl: "distinct ?l" using da db disj Cfa Cfb by auto
  have A: "path (frel ?q) a (Lb @ [b]) = path (frel f) b (Lb @ [b])"
  proof (cases Lb)
    case Nil
    then show ?thesis by (simp add: qa)
  next
    case (Cons y Lb')
    have "path (frel ?q) y (Lb' @ [b]) = path (frel f) y (Lb' @ [b])"
      by (rule path_cong_src) (use dl Cons qx in \<open>auto simp: butlast_append Transposition.transpose_def\<close>)
    then show ?thesis using Cons qa by simp
  qed
  have B: "path (frel ?q) b (La @ [a]) = path (frel f) a (La @ [a])"
  proof (cases La)
    case Nil
    then show ?thesis by (simp add: qb)
  next
    case (Cons y La')
    have "path (frel ?q) y (La' @ [a]) = path (frel f) y (La' @ [a])"
      by (rule path_cong_src) (use dl Cons qx in \<open>auto simp: butlast_append Transposition.transpose_def\<close>)
    then show ?thesis using Cons qb by simp
  qed
  have "path (frel ?q) a ((Lb @ [b]) @ La @ [a])"
    using A B pa pb by (simp only: path_append) simp
  then have c: "cycle (frel ?q) ?l" by (simp add: cycle_Cons)
  have "cyc ?q a = set ?l"
    by (rule distinct_cycle_cyc[OF qp c dl]) simp
  then show ?thesis using Cfa Cfb by auto
qed

context fperm
begin

lemma cyc_disjoint_or_eq: "cyc f x = cyc f y \<or> cyc f x \<inter> cyc f y = {}"
proof (cases "fconnect f x y")
  case True
  then show ?thesis by (simp add: cyc_eq)
next
  case False
  have "z \<in> cyc f x \<Longrightarrow> z \<in> cyc f y \<Longrightarrow> False" for z
  proof -
    assume "z \<in> cyc f x" "z \<in> cyc f y"
    then have xz: "fconnect f x z" and yz: "fconnect f y z" by (simp_all add: in_cyc_iff)
    have "fconnect f x y" by (rule fconnect_trans[OF xz fconnect_sym[OF yz]])
    then show False using False by simp
  qed
  then show ?thesis by blast
qed

lemma cyc_unique: "z \<in> cyc f x \<Longrightarrow> cyc f x = cyc f z"
  by (simp add: cyc_eq in_cyc_iff)

lemma in_cyc_sym: "y \<in> cyc f x \<longleftrightarrow> x \<in> cyc f y"
  by (simp add: in_cyc_iff fconnect_commute)

end

lemma fperm_transpose:
  assumes "fperm f S" "a \<in> S" "b \<in> S"
  shows "fperm (f \<circ> Transposition.transpose a b) S"
proof -
  interpret fperm f S by fact
  show ?thesis
  proof unfold_locales
    show "f \<circ> Transposition.transpose a b permutes S"
      using permutes_compose[OF permutes_swap_id[OF assms(2,3)] perm]
      by (simp add: Transposition.transpose_def swap_id_eq comp_def)
  qed (rule fin)
qed

lemma cyc_transpose_split:
  assumes fp: "fperm f S" and ab: "a \<in> S" "b \<in> S" "a \<noteq> b" and c: "fconnect f a b"
  obtains A B where "cyc (f \<circ> Transposition.transpose a b) a = A"
    "cyc (f \<circ> Transposition.transpose a b) b = B" "A \<union> B = cyc f a" "A \<inter> B = {}"
proof -
  interpret fperm f S by (rule fp)
  let ?q = "f \<circ> Transposition.transpose a b"
  have qp: "fperm ?q S" by (rule fperm_transpose[OF fp ab(1,2)])
  have qa: "?q a = f b" and qb: "?q b = f a"
    by (auto simp: Transposition.transpose_def)
  have qx: "x \<noteq> a \<Longrightarrow> x \<noteq> b \<Longrightarrow> ?q x = f x" for x
    by (simp add: Transposition.transpose_def)
  obtain L1 L2 where o: "orb f a = a # L1 @ b # L2"
    by (rule orb_split2[OF c ab(3)])
  have dist: "distinct (a # L1 @ b # L2)" using distinct_orb[of a] o by simp
  have pth: "path (frel f) a (L1 @ b # L2 @ [a])" using orb_path[OF o] by simp
  have p1: "path (frel f) a (L1 @ [b])" and p2: "path (frel f) b (L2 @ [a])"
    using pth by (simp_all add: lastd_append)
  have c1: "cycle (frel ?q) (a # L2)"
  proof -
    have "path (frel ?q) a (L2 @ [a]) = path (frel f) b (L2 @ [a])"
    proof (cases L2)
      case Nil
      then show ?thesis by (simp add: qa)
    next
      case (Cons y L2')
      have "path (frel ?q) y (L2' @ [a]) = path (frel f) y (L2' @ [a])"
        by (rule path_cong_src) (use dist Cons in \<open>auto simp: butlast_append Transposition.transpose_def\<close>)
      then show ?thesis using Cons qa by simp
    qed
    then show ?thesis using p2 by (simp add: cycle_Cons)
  qed
  have c2: "cycle (frel ?q) (b # L1)"
  proof -
    have "path (frel ?q) b (L1 @ [b]) = path (frel f) a (L1 @ [b])"
    proof (cases L1)
      case Nil
      then show ?thesis by (simp add: qb)
    next
      case (Cons y L1')
      have "path (frel ?q) y (L1' @ [b]) = path (frel f) y (L1' @ [b])"
        by (rule path_cong_src) (use dist Cons in \<open>auto simp: butlast_append Transposition.transpose_def\<close>)
      then show ?thesis using Cons qb by simp
    qed
    then show ?thesis using p1 by (simp add: cycle_Cons)
  qed
  have Ca: "cyc ?q a = set (a # L2)"
    by (rule distinct_cycle_cyc[OF qp c1]) (use dist in auto)
  have Cb: "cyc ?q b = set (b # L1)"
    by (rule distinct_cycle_cyc[OF qp c2]) (use dist in auto)
  have Cf: "cyc f a = set (a # L1 @ b # L2)" using set_orb[of a] o by simp
  show ?thesis
    by (rule that[OF Ca Cb]) (use Cf dist in auto)
qed

text \<open>The main counting lemma: composing a permutation with a transposition
  either splits a cycle (if both points are on it) or merges two cycles.\<close>

lemma fcard_transpose:
  assumes fp: "fperm f S" and ab: "a \<in> S" "b \<in> S" "a \<noteq> b"
  shows "int (fcard (f \<circ> Transposition.transpose a b) S) =
           int (fcard f S) + (if fconnect f a b then 1 else -1)"
proof -
  interpret fperm f S by (rule fp)
  let ?q = "f \<circ> Transposition.transpose a b"
  have qp: "fperm ?q S" by (rule fperm_transpose[OF fp ab(1,2)])
  interpret Q: fperm ?q S by (rule qp)
  have qx: "x \<noteq> a \<Longrightarrow> x \<noteq> b \<Longrightarrow> ?q x = f x" for x
    by (simp add: Transposition.transpose_def)
  have other: "cyc ?q x = cyc f x" if "a \<notin> cyc f x" "b \<notin> cyc f x" for x
    by (rule cyc_eq_on) (use that in \<open>auto simp: in_cyc_iff Transposition.transpose_def\<close>)
  have finA: "finite (cyc f ` S)" using fin by simp
  \<comment> \<open>Cycles of @{term f} avoiding @{term a} and @{term b} are unchanged.\<close>
  have keep: "C \<in> cyc ?q ` S \<longleftrightarrow> C \<in> cyc f ` S"
    if C1: "C \<inter> (cyc f a \<union> cyc f b) = {}" and C2: "C \<noteq> {}" and C3: "C \<subseteq> S" for C
  proof -
    obtain x where x: "x \<in> C" using C2 by blast
    have xS: "x \<in> S" using x C3 by blast
    have "x \<notin> cyc f a" "x \<notin> cyc f b" using C1 x by blast+
    then have "a \<notin> cyc f x" "b \<notin> cyc f x" using in_cyc_sym by blast+
    then have eqx: "cyc ?q x = cyc f x" by (rule other)
    show ?thesis
    proof
      assume "C \<in> cyc ?q ` S"
      then obtain y where "C = cyc ?q y" by blast
      then have "C = cyc ?q x" using x Q.cyc_unique by simp
      then show "C \<in> cyc f ` S" using eqx xS by simp
    next
      assume "C \<in> cyc f ` S"
      then obtain y where "C = cyc f y" by blast
      then have "C = cyc f x" using x cyc_unique by simp
      then show "C \<in> cyc ?q ` S" using eqx xS by (metis image_eqI)
    qed
  qed
  have qcyc_sub: "cyc ?q x \<subseteq> cyc f a \<union> cyc f b \<or> cyc ?q x \<inter> (cyc f a \<union> cyc f b) = {}" for x
  proof (cases "x \<in> cyc f a \<union> cyc f b")
    case True
    have "fconnect ?q x y \<Longrightarrow> y \<in> cyc f a \<union> cyc f b" for y
    proof (induction rule: fconnect_induct)
      case refl
      then show ?case using True .
    next
      case (step z)
      have "?q z \<in> cyc f z \<union> {f a, f b}"
        by (auto simp: Transposition.transpose_def in_cyc_iff)
      moreover have "cyc f z \<subseteq> cyc f a \<union> cyc f b" using step.IH cyc_unique by auto
      moreover have "f a \<in> cyc f a" "f b \<in> cyc f b" by (auto simp: in_cyc_iff)
      ultimately show ?case by auto
    qed
    then have "cyc ?q x \<subseteq> cyc f a \<union> cyc f b" unfolding cyc_def by blast
    then show ?thesis by blast
  next
    case False
    then have "a \<notin> cyc f x" "b \<notin> cyc f x" using in_cyc_sym by blast+
    then have "cyc ?q x = cyc f x" by (rule other)
    moreover have "cyc f x \<inter> (cyc f a \<union> cyc f b) = {}"
      using False cyc_disjoint_or_eq[of x a] cyc_disjoint_or_eq[of x b] by auto
    ultimately show ?thesis by simp
  qed
  let ?U = "cyc f a \<union> cyc f b"
  have splitimg: "X ` S = (X ` S - {C. C \<subseteq> ?U}) \<union> {C \<in> X ` S. C \<subseteq> ?U}" for X :: "'a \<Rightarrow> 'a set"
    by blast
  have same_out: "cyc ?q ` S - {C. C \<subseteq> ?U} = cyc f ` S - {C. C \<subseteq> ?U}"
  proof (intro set_eqI iffI)
    fix C assume C: "C \<in> cyc ?q ` S - {C. C \<subseteq> ?U}"
    then obtain x where x: "x \<in> S" "C = cyc ?q x" by blast
    then have "C \<inter> ?U = {}" using qcyc_sub C by blast
    moreover have "C \<noteq> {}" "C \<subseteq> S" using x Q.cyc_subset by auto
    ultimately show "C \<in> cyc f ` S - {C. C \<subseteq> ?U}" using keep C by blast
  next
    fix C assume C: "C \<in> cyc f ` S - {C. C \<subseteq> ?U}"
    then obtain x where x: "x \<in> S" "C = cyc f x" by blast
    have "C \<inter> ?U = {}" using C x cyc_disjoint_or_eq[of x a] cyc_disjoint_or_eq[of x b] by auto
    moreover have "C \<noteq> {}" "C \<subseteq> S" using x cyc_subset by auto
    ultimately show "C \<in> cyc ?q ` S - {C. C \<subseteq> ?U}" using keep C by blast
  qed
  have inner_f: "{C \<in> cyc f ` S. C \<subseteq> ?U} = {cyc f a, cyc f b}"
  proof (intro set_eqI iffI)
    fix C assume "C \<in> {C \<in> cyc f ` S. C \<subseteq> ?U}"
    then obtain x where x: "x \<in> S" "C = cyc f x" "C \<subseteq> ?U" by blast
    then have "x \<in> ?U" by auto
    then show "C \<in> {cyc f a, cyc f b}" using x cyc_unique by auto
  next
    fix C assume "C \<in> {cyc f a, cyc f b}"
    then show "C \<in> {C \<in> cyc f ` S. C \<subseteq> ?U}" using ab by auto
  qed
  have fin_inner: "finite {C \<in> cyc ?q ` S. C \<subseteq> ?U}" using fin by simp
  have card_eq: "int (fcard ?q S) = int (fcard f S) - int (card {cyc f a, cyc f b}) + int (card {C \<in> cyc ?q ` S. C \<subseteq> ?U})"
  proof -
    have "card (cyc ?q ` S) = card (cyc ?q ` S - {C. C \<subseteq> ?U}) + card {C \<in> cyc ?q ` S. C \<subseteq> ?U}"
      by (subst splitimg[of "cyc ?q"], rule card_Un_disjoint) (use fin in auto)
    moreover have "card (cyc f ` S) = card (cyc f ` S - {C. C \<subseteq> ?U}) + card {cyc f a, cyc f b}"
      by (subst splitimg[of "cyc f"], subst inner_f[symmetric], rule card_Un_disjoint) (use fin in auto)
    ultimately show ?thesis using same_out by (simp add: fcard_def)
  qed
  show ?thesis
  proof (cases "fconnect f a b")
    case True
    then have ab_eq: "cyc f b = cyc f a" using cyc_eq by simp
    obtain A B where AB: "cyc ?q a = A" "cyc ?q b = B" "A \<union> B = cyc f a" "A \<inter> B = {}"
      by (rule cyc_transpose_split[OF fp ab True])
    have aA: "a \<in> A" and bB: "b \<in> B" using AB by auto
    have inner_q: "{C \<in> cyc ?q ` S. C \<subseteq> ?U} = {A, B}"
    proof (intro set_eqI iffI)
      fix C assume "C \<in> {C \<in> cyc ?q ` S. C \<subseteq> ?U}"
      then obtain x where x: "x \<in> S" "C = cyc ?q x" "C \<subseteq> ?U" by blast
      then have xAB: "x \<in> A \<union> B" using AB ab_eq by auto
      have "C = A \<or> C = B"
      proof (cases "x \<in> A")
        case True
        then have "cyc ?q a = cyc ?q x" using AB(1) Q.cyc_unique by blast
        then show ?thesis using x AB by simp
      next
        case False
        then have "x \<in> B" using xAB by blast
        then have "cyc ?q b = cyc ?q x" using AB(2) Q.cyc_unique by blast
        then show ?thesis using x AB by simp
      qed
      then show "C \<in> {A, B}" by blast
    next
      fix C assume "C \<in> {A, B}"
      then show "C \<in> {C \<in> cyc ?q ` S. C \<subseteq> ?U}" using AB ab ab_eq by auto
    qed
    have "A \<noteq> B" using AB aA by auto
    then show ?thesis using card_eq inner_q ab_eq True by simp
  next
    case False
    have M: "cyc ?q a = ?U" by (rule cyc_transpose_merge[OF fp ab False])
    have inner_q: "{C \<in> cyc ?q ` S. C \<subseteq> ?U} = {?U}"
    proof (intro set_eqI iffI)
      fix C assume "C \<in> {C \<in> cyc ?q ` S. C \<subseteq> ?U}"
      then obtain x where x: "x \<in> S" "C = cyc ?q x" "C \<subseteq> ?U" by blast
      then have "x \<in> cyc ?q a" using M by auto
      then have "cyc ?q a = cyc ?q x" by (rule Q.cyc_unique)
      then show "C \<in> {?U}" using x M by simp
    next
      fix C assume "C \<in> {?U}"
      then show "C \<in> {C \<in> cyc ?q ` S. C \<subseteq> ?U}" using M ab by auto
    qed
    have "cyc f a \<noteq> cyc f b" using False by (simp add: cyc_eq_iff)
    then show ?thesis using card_eq inner_q False by simp
  qed
qed

end
