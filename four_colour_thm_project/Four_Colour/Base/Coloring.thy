(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Coloring.thy
    Map colourings, ring traces, contract colourings, and configuration
    properties.  Ported from G. Gonthier's Coq development (coloring.v).
*)
theory Coloring
  imports Geometry Color
begin

section \<open>Colourings\<close>

text \<open>A colouring assigns the same colour to the darts of a face, and different
  colours to the two ends of each edge link.  Only darts are constrained.\<close>

definition coloring :: "'a hypermap \<Rightarrow> ('a \<Rightarrow> color) \<Rightarrow> bool" where
  "coloring G k \<longleftrightarrow> (\<forall>x \<in> darts G. k (edge G x) \<noteq> k x) \<and> (\<forall>x \<in> darts G. k (face G x) = k x)"

definition ring_trace :: "'a hypermap \<Rightarrow> 'a list \<Rightarrow> colseq \<Rightarrow> bool" where
  "ring_trace G r et \<longleftrightarrow> (\<exists>k. coloring G k \<and> et = trace (map k r))"

definition four_colorable :: "'a hypermap \<Rightarrow> bool" where
  "four_colorable G \<longleftrightarrow> (\<exists>k. coloring G k)"

definition graph_coloring :: "'a hypermap \<Rightarrow> ('a \<Rightarrow> color) \<Rightarrow> bool" where
  "graph_coloring G k \<longleftrightarrow> (\<forall>x \<in> darts G. k (edge G x) \<noteq> k x) \<and> (\<forall>x \<in> darts G. k (node G x) = k x)"

definition graph_four_colorable :: "'a hypermap \<Rightarrow> bool" where
  "graph_four_colorable G \<longleftrightarrow> (\<exists>k. graph_coloring G k)"

definition cc_coloring :: "'a hypermap \<Rightarrow> 'a list \<Rightarrow> ('a \<Rightarrow> color) \<Rightarrow> bool" where
  "cc_coloring G cc k \<longleftrightarrow>
     (\<forall>x \<in> darts G. (k (edge G x) = k x) \<longleftrightarrow> x \<in> set (insertE G cc)) \<and>
     (\<forall>x \<in> darts G. k (face G x) = k x)"

definition cc_colorable :: "'a hypermap \<Rightarrow> 'a list \<Rightarrow> bool" where
  "cc_colorable G cc \<longleftrightarrow> (\<exists>k. cc_coloring G cc k)"

definition cc_ring_trace :: "'a hypermap \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> colseq \<Rightarrow> bool" where
  "cc_ring_trace G cc r et \<longleftrightarrow> (\<exists>k. cc_coloring G cc k \<and> et = trace (map k r))"

context hypermap
begin

lemma coloring_cface:
  assumes "coloring G k" "cface x y" "x \<in> D"
  shows "k y = k x"
  using assms(2,3)
proof (induction rule: fconnect_induct)
  case refl
  then show ?case by simp
next
  case (step z)
  have "z \<in> D" using step(1) assms(3) F.fconnect_in_D by blast
  then have "k (f z) = k z" using assms(1) by (simp add: coloring_def)
  then show ?case using step by simp
qed

lemma coloring_inj:
  "inj h \<Longrightarrow> coloring G k \<Longrightarrow> coloring G (h \<circ> k)"
  by (auto simp: coloring_def inj_eq)

lemma colorable_bridgeless: "four_colorable G \<Longrightarrow> bridgeless G"
proof -
  assume "four_colorable G"
  then obtain k where k: "coloring G k" by (auto simp: four_colorable_def)
  show "bridgeless G" unfolding bridgeless_def
  proof (intro ballI notI)
    fix x assume xD: "x \<in> D" and xe: "cface x (e x)"
    have "k (e x) = k x" using coloring_cface[OF k xe xD] .
    then show False using k xD by (simp add: coloring_def)
  qed
qed

lemma coloring_dual: "coloring (dual G) k \<longleftrightarrow> graph_coloring G k"
proof -
  have e1: "(\<forall>x \<in> D. k (inv e x) \<noteq> k x) \<longleftrightarrow> (\<forall>x \<in> D. k (e x) \<noteq> k x)"
  proof
    assume h: "\<forall>x \<in> D. k (inv e x) \<noteq> k x"
    show "\<forall>x \<in> D. k (e x) \<noteq> k x"
    proof
      fix x assume "x \<in> D"
      then have "e x \<in> D" by simp
      then show "k (e x) \<noteq> k x" using h by fastforce
    qed
  next
    assume h: "\<forall>x \<in> D. k (e x) \<noteq> k x"
    show "\<forall>x \<in> D. k (inv e x) \<noteq> k x"
    proof
      fix x assume "x \<in> D"
      then have "inv e x \<in> D" by (metis E.closed E.f_inv)
      then show "k (inv e x) \<noteq> k x" using h by fastforce
    qed
  qed
  have n1: "(\<forall>x \<in> D. k (inv n x) = k x) \<longleftrightarrow> (\<forall>x \<in> D. k (n x) = k x)"
  proof
    assume h: "\<forall>x \<in> D. k (inv n x) = k x"
    show "\<forall>x \<in> D. k (n x) = k x"
    proof
      fix x assume "x \<in> D"
      then have "n x \<in> D" by simp
      then show "k (n x) = k x" using h by fastforce
    qed
  next
    assume h: "\<forall>x \<in> D. k (n x) = k x"
    show "\<forall>x \<in> D. k (inv n x) = k x"
    proof
      fix x assume "x \<in> D"
      then have "inv n x \<in> D" by (metis N.closed N.f_inv)
      then show "k (inv n x) = k x" using h by fastforce
    qed
  qed
  show ?thesis using e1 n1 by (simp add: coloring_def graph_coloring_def)
qed

lemma four_colorable_dual: "four_colorable (dual G) \<longleftrightarrow> graph_four_colorable G"
  by (simp add: four_colorable_def graph_four_colorable_def coloring_dual)

lemma coloring_mirror: "coloring (mirror G) k \<Longrightarrow> coloring G k"
proof -
  assume h: "coloring (mirror G) k"
  have kF: "k (f x) = k x" if "x \<in> D" for x
  proof -
    have fxD: "f x \<in> D" using that by simp
    have "\<forall>y \<in> D. k (inv f y) = k y" using h by (simp add: coloring_def)
    then have "k (inv f (f x)) = k (f x)" using fxD by blast
    then show ?thesis by simp
  qed
  have kE: "k (e x) \<noteq> k x" if xD: "x \<in> D" for x
  proof -
    have yD: "f (e x) \<in> D" using xD by simp
    have "\<forall>y \<in> D. k (f (n y)) \<noteq> k y" using h by (simp add: coloring_def)
    then have "k (f (n (f (e x)))) \<noteq> k (f (e x))" using yD by blast
    then have "k (f x) \<noteq> k (f (e x))" by (simp add: edgeK)
    moreover have "k (f x) = k x" by (rule kF[OF xD])
    moreover have "k (f (e x)) = k (e x)" using kF[of "e x"] xD by simp
    ultimately show ?thesis by simp
  qed
  show ?thesis using kE kF by (simp add: coloring_def)
qed

lemma colorable_mirror: "four_colorable (mirror G) \<Longrightarrow> four_colorable G"
  using coloring_mirror by (auto simp: four_colorable_def)

end

section \<open>Configuration properties\<close>

definition good_ring_arity :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> bool" where
  "good_ring_arity G x \<longleftrightarrow> arity G x \<in> {3, 4, 5, 6}"

definition at_radius2 :: "'a hypermap \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "at_radius2 G A x y \<longleftrightarrow> (\<exists>z. adj G y z \<and> adj G x z \<and> A z)"

definition radius2 :: "'a hypermap \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "radius2 G A \<longleftrightarrow> (\<exists>x \<in> darts G. A x \<and> (\<forall>y \<in> darts G. A y \<longrightarrow> at_radius2 G A x y))"

definition embeddable :: "'a hypermap \<Rightarrow> 'a list \<Rightarrow> bool" where
  "embeddable G r \<longleftrightarrow> scycle_planar_bridgeless_plain_quasicubic_connected G r \<and>
     (\<forall>x \<in> set r. good_ring_arity G x) \<and> radius2 G (kernel G r)"

definition sparse :: "'a hypermap \<Rightarrow> 'a list \<Rightarrow> bool" where
  "sparse G p \<longleftrightarrow> simple (permF G) p"

definition triad :: "'a hypermap \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> bool" where
  "triad G p x \<longleftrightarrow> 2 < length (filter (\<lambda>y. fband G p (edge G y)) (orb (face G) x)) \<and>
                    \<not> (\<forall>y \<in> set p. adj G x y)"

definition valid_contract :: "'a hypermap \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "valid_contract G r cc \<longleftrightarrow>
     set r \<inter> set (insertE G cc) = {} \<and> sparse G (insertE G cc) \<and>
     length cc \<in> {1, 2, 3, 4} \<and>
     (length cc = 4 \<longrightarrow> (\<exists>x \<in> darts G. kernel G r x \<and> triad G (insertE G cc) x))"

lemma sparse_Cons:
  "hypermap G \<Longrightarrow> sparse G (x # p) \<longleftrightarrow> \<not> (\<exists>y \<in> set p. fconnect (node G) x y) \<and> sparse G p"
proof -
  assume "hypermap G"
  then interpret P: hypermap "permF G" by (rule hypermap.hypermap_permF)
  show ?thesis using P.simple_Cons[of x p] by (simp add: sparse_def fband_def)
qed

end
