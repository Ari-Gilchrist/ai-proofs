(* Compactness step underlying finitize.v, using HOL's Tychonoff theorem.
   Unlike the reference's constructive enumeration argument, this proof uses
   the choice principle already available in Isabelle/HOL. Codex, 2026-11-25. *)
theory Colour_Compactness
  imports "HOL-Analysis.Function_Topology"
begin

lemma closed_finite_colour_constraint:
  fixes C :: "'c set" and x y :: 'a and R :: "('c \<times> 'c) set"
  assumes fin: "finite C"
  shows "closedin (product_topology (\<lambda>_. discrete_topology C) UNIV)
    {f \<in> topspace (product_topology (\<lambda>_. discrete_topology C) UNIV). (f x, f y) \<in> R}"
proof -
  let ?X = "product_topology (\<lambda>_. discrete_topology C) (UNIV :: 'a set)"
  let ?S = "topspace ?X"
  have coord: "closedin ?X {f \<in> ?S. f v = a}" if "a \<in> C" for v a
  proof -
    have co: "continuous_map ?X (discrete_topology C) (\<lambda>f. f v)"
      by (rule continuous_map_product_projection) simp
    have cl: "closedin (discrete_topology C) {a}" using that by simp
    show ?thesis using closedin_continuous_map_preimage[OF co cl] by simp
  qed
  let ?A = "\<lambda>(a,b). {f \<in> ?S. f x = a} \<inter> {f \<in> ?S. f y = b}"
  have eq: "{f \<in> ?S. (f x, f y) \<in> R} = \<Union>(?A ` ((C \<times> C) \<inter> R))"
    by (auto simp: topspace_product_topology PiE_iff)
  have "finite ((C \<times> C) \<inter> R)" using fin by simp
  moreover have "closedin ?X (?A p)" if "p \<in> (C \<times> C) \<inter> R" for p
  proof -
    have a: "fst p \<in> C" and b: "snd p \<in> C" using that by auto
    have cx: "closedin ?X {f \<in> ?S. f x = fst p}" by (rule coord[OF a])
    have cy: "closedin ?X {f \<in> ?S. f y = snd p}" by (rule coord[OF b])
    show ?thesis using closedin_Int[OF cx cy] by (cases p) simp
  qed
  ultimately show ?thesis unfolding eq
    by (intro closedin_Union) auto
qed

theorem finite_colour_constraint_compactness:
  fixes C :: "'c set" and x y :: "'i \<Rightarrow> 'a" and R :: "'i \<Rightarrow> ('c \<times> 'c) set"
  assumes fin: "finite C"
    and local: "\<And>J. finite J \<Longrightarrow> \<exists>f :: 'a \<Rightarrow> 'c.
      (\<forall>v. f v \<in> C) \<and> (\<forall>j\<in>J. (f (x j), f (y j)) \<in> R j)"
  shows "\<exists>f :: 'a \<Rightarrow> 'c. (\<forall>v. f v \<in> C) \<and>
    (\<forall>j. (f (x j), f (y j)) \<in> R j)"
proof -
  let ?X = "product_topology (\<lambda>_. discrete_topology C) (UNIV :: 'a set)"
  define K where "K = (\<lambda>j. {f \<in> topspace ?X. (f (x j), f (y j)) \<in> R j})"
  have compact: "compact_space ?X"
    using fin by (simp add: compact_space_product_topology compact_space_discrete_topology)
  have closed: "closedin ?X (K j)" for j
    unfolding K_def by (rule closed_finite_colour_constraint[OF fin])
  have fip: "\<Inter>F \<noteq> {}" if h: "finite F" "F \<subseteq> K ` UNIV" for F
  proof -
    define pick where "pick = (\<lambda>A. SOME j. A = K j)"
    have pk: "A = K (pick A)" if "A \<in> F" for A
      unfolding pick_def by (rule someI_ex) (use that h(2) in blast)
    have fj: "finite (pick ` F)" using h(1) by simp
    obtain f where b: "\<forall>v. f v \<in> C" and r: "\<forall>j\<in>pick ` F. (f (x j), f (y j)) \<in> R j"
      using local[OF fj] by blast
    have "f \<in> A" if a: "A \<in> F" for A
      using r a b pk[OF a]
      by (auto simp: K_def topspace_product_topology PiE_iff)
    then show ?thesis by blast
  qed
  have "\<Inter>(K ` UNIV) \<noteq> {}"
    using compact closed fip unfolding compact_space_fip by blast
  then obtain f where f: "\<forall>j. f \<in> K j" by blast
  have b: "\<forall>v. f v \<in> C"
    using f[rule_format, of undefined] by (simp add: K_def topspace_product_topology PiE_iff)
  have "\<forall>j. (f (x j), f (y j)) \<in> R j" using f by (simp add: K_def)
  then show ?thesis using b by blast
qed

end
