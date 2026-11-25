(* Port of realplane.v and the elementary map lemmas in finitize.v.
   Original: G. Gonthier et al., CeCILL-B. Isabelle port: Codex, 2026-11-25.
   The reference's real model is instantiated by Isabelle/HOL's real numbers. *)
theory Realplane
  imports "HOL-Analysis.Connected" "HOL-Analysis.Convex"
    "HOL-Analysis.Elementary_Metric_Spaces"
begin

type_synonym rp_point = "real \<times> real"
type_synonym 'a region_map = "'a \<Rightarrow> 'a \<Rightarrow> bool"

definition rp_rectangle :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> rp_point set" where
  "rp_rectangle a b c d = {a<..<b} \<times> {c<..<d}"

definition rp_open :: "rp_point set \<Rightarrow> bool" where
  "rp_open S \<longleftrightarrow> (\<forall>z\<in>S. \<exists>a b c d.
    z \<in> rp_rectangle a b c d \<and> rp_rectangle a b c d \<subseteq> S)"

definition rp_plain :: "'a region_map \<Rightarrow> bool" where
  "rp_plain m \<longleftrightarrow> (\<forall>x y. m x y \<longrightarrow> m y x) \<and>
    (\<forall>x y z. m x y \<longrightarrow> m y z \<longrightarrow> m x z)"

definition rp_cover :: "'a region_map \<Rightarrow> 'a set" where
  "rp_cover m = {x. m x x}"

definition rp_region :: "'a region_map \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "rp_region m x = {y. m x y}"

definition rp_submap :: "'a region_map \<Rightarrow> 'a region_map \<Rightarrow> bool" where
  "rp_submap m k \<longleftrightarrow> (\<forall>x y. m x y \<longrightarrow> k x y)"

definition rp_at_most_regions :: "nat \<Rightarrow> 'a region_map \<Rightarrow> bool" where
  "rp_at_most_regions n m \<longleftrightarrow>
    (\<exists>f :: nat \<Rightarrow> 'a. \<forall>x\<in>rp_cover m. \<exists>i<n. m (f i) x)"

definition rp_closure :: "'a::topological_space set \<Rightarrow> 'a set" where
  "rp_closure S = {x. \<forall>U. open U \<longrightarrow> x \<in> U \<longrightarrow> S \<inter> U \<noteq> {}}"

definition rp_connected :: "'a::topological_space set \<Rightarrow> bool" where
  "rp_connected S \<longleftrightarrow> (\<forall>U V. open U \<longrightarrow> open V \<longrightarrow>
    S \<subseteq> U \<union> V \<longrightarrow> U \<inter> S \<noteq> {} \<longrightarrow> V \<inter> S \<noteq> {} \<longrightarrow> U \<inter> V \<noteq> {})"

definition rp_simple_map :: "'a::topological_space region_map \<Rightarrow> bool" where
  "rp_simple_map m \<longleftrightarrow> rp_plain m \<and>
    (\<forall>x. open (rp_region m x) \<and> rp_connected (rp_region m x))"

definition rp_finite_simple_map :: "'a::topological_space region_map \<Rightarrow> bool" where
  "rp_finite_simple_map m \<longleftrightarrow> rp_simple_map m \<and> (\<exists>n. rp_at_most_regions n m)"

definition rp_border :: "'a::topological_space region_map \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "rp_border m x y = rp_closure (rp_region m x) \<inter> rp_closure (rp_region m y)"

definition rp_corner_map :: "'a::topological_space region_map \<Rightarrow> 'a \<Rightarrow> 'a region_map" where
  "rp_corner_map m z x y \<longleftrightarrow> m x y \<and> z \<in> rp_closure (rp_region m x)"

definition rp_not_corner :: "'a::topological_space region_map \<Rightarrow> 'a set" where
  "rp_not_corner m = {z. rp_at_most_regions 2 (rp_corner_map m z)}"

definition rp_adjacent :: "'a::topological_space region_map \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "rp_adjacent m x y \<longleftrightarrow> \<not> m x y \<and> rp_not_corner m \<inter> rp_border m x y \<noteq> {}"

definition rp_coloring :: "'a::topological_space region_map \<Rightarrow> 'a region_map \<Rightarrow> bool" where
  "rp_coloring m k \<longleftrightarrow> rp_plain k \<and> rp_cover k \<subseteq> rp_cover m \<and>
    rp_submap m k \<and> (\<forall>x y. rp_adjacent m x y \<longrightarrow> \<not> k x y)"

definition rp_colorable_with :: "nat \<Rightarrow> 'a::topological_space region_map \<Rightarrow> bool" where
  "rp_colorable_with n m \<longleftrightarrow> (\<exists>k. rp_coloring m k \<and> rp_at_most_regions n k)"

text \<open>The reference's elementary rectangle and neighbourhood definitions agree
  with the usual topology; its connectedness predicate agrees on open regions.\<close>

lemma rp_real_interval_neighbourhood:
  fixes U :: "real set"
  assumes "open U" "x \<in> U"
  obtains a b where "x \<in> {a<..<b}" "{a<..<b} \<subseteq> U"
proof -
  obtain e where e: "0 < e" "ball x e \<subseteq> U"
    using assms open_contains_ball by blast
  have "x \<in> {x-e<..<x+e}" using e(1) by auto
  moreover have "{x-e<..<x+e} \<subseteq> U"
    using e(2) by (auto simp: dist_real_def abs_less_iff subset_iff)
  ultimately show thesis by (rule that)
qed

lemma rp_open_eq: "rp_open S \<longleftrightarrow> open S"
proof
  assume p: "rp_open S"
  have "S = \<Union>{R. (\<exists>a b c d. R = rp_rectangle a b c d) \<and> R \<subseteq> S}"
  proof (rule equalityI)
    show "S \<subseteq> \<Union>{R. (\<exists>a b c d. R = rp_rectangle a b c d) \<and> R \<subseteq> S}"
    proof (rule subsetI)
      fix z assume z: "z\<in>S"
      obtain a b c d where point: "z\<in>rp_rectangle a b c d"
        and contain: "rp_rectangle a b c d\<subseteq>S"
        using p z unfolding rp_open_def by blast
      have shape: "\<exists>u v w t. rp_rectangle a b c d = rp_rectangle u v w t"
        by (rule exI[of _ a], rule exI[of _ b], rule exI[of _ c], rule exI[of _ d], rule refl)
      have rectangle: "rp_rectangle a b c d\<in>
          {R. (\<exists>a b c d. R = rp_rectangle a b c d) \<and> R \<subseteq> S}"
        using shape contain by simp
      show "z\<in>\<Union>{R. (\<exists>a b c d. R = rp_rectangle a b c d) \<and> R \<subseteq> S}"
        using rectangle point by blast
    qed
    show "\<Union>{R. (\<exists>a b c d. R = rp_rectangle a b c d) \<and> R \<subseteq> S} \<subseteq> S"
      by auto
  qed
  moreover have "open (\<Union>{R. (\<exists>a b c d. R = rp_rectangle a b c d) \<and> R \<subseteq> S})"
    by (rule open_Union) (auto simp: rp_rectangle_def intro: open_Times)
  ultimately show "open S" by simp
next
  assume o: "open S"
  show "rp_open S" unfolding rp_open_def
  proof (intro ballI)
    fix z assume z: "z \<in> S"
    obtain U V where uv: "open U" "open V" "z \<in> U \<times> V" "U \<times> V \<subseteq> S"
      by (rule open_prod_elim[OF o z])
    obtain a b where ab: "fst z \<in> {a<..<b}" "{a<..<b} \<subseteq> U"
      by (rule rp_real_interval_neighbourhood[OF uv(1), where x="fst z"]) (use uv(3) in auto)
    obtain c d where cd: "snd z \<in> {c<..<d}" "{c<..<d} \<subseteq> V"
      by (rule rp_real_interval_neighbourhood[OF uv(2), where x="snd z"]) (use uv(3) in auto)
    have "z \<in> rp_rectangle a b c d \<and> rp_rectangle a b c d \<subseteq> S"
      using ab cd uv(4) by (cases z) (auto simp: rp_rectangle_def)
    then show "\<exists>a b c d. z \<in> rp_rectangle a b c d \<and> rp_rectangle a b c d \<subseteq> S"
      by blast
  qed
qed

lemma rp_closure_eq: "rp_closure S = closure S"
  unfolding rp_closure_def
  by (auto simp: closure_iff_nhds_not_empty) blast+

lemma rp_connected_of_connected: "connected S \<Longrightarrow> rp_connected S"
  unfolding rp_connected_def using connectedD by blast

lemma rp_connected_open:
  assumes o: "open S"
  shows "rp_connected S \<longleftrightarrow> connected S"
proof
  assume c: "rp_connected S"
  show "connected S"
  proof (rule connectedI)
    fix U V
    assume uv: "open U" "open V" "U \<inter> S \<noteq> {}" "V \<inter> S \<noteq> {}"
      "U \<inter> V \<inter> S = {}" "S \<subseteq> U \<union> V"
    have "(U \<inter> S) \<inter> (V \<inter> S) \<noteq> {}"
      using c o uv by (auto simp: rp_connected_def)
    then show False using uv(5) by auto
  qed
qed (rule rp_connected_of_connected)

lemma rp_open_connected_iff:
  "open S \<and> rp_connected S \<longleftrightarrow> open S \<and> connected S"
  by (cases "open S") (simp_all add: rp_connected_open)

lemma rp_simple_map_iff:
  "rp_simple_map m \<longleftrightarrow> rp_plain m \<and> (\<forall>x. open (rp_region m x) \<and> connected (rp_region m x))"
  by (simp only: rp_simple_map_def rp_open_connected_iff)

lemma rp_map_sym:
  assumes p: "rp_plain m" and xy: "m x y"
  shows "m y x"
  using conjunct1[OF p[unfolded rp_plain_def]] xy by blast

lemma rp_map_trans:
  assumes p: "rp_plain m" and xy: "m x y" and yz: "m y z"
  shows "m x z"
  by (rule conjunct2[OF p[unfolded rp_plain_def], rule_format, OF xy yz])

lemma rp_map_cover:
  assumes p: "rp_plain m" and xy: "m x y"
  shows "x \<in> rp_cover m \<and> y \<in> rp_cover m"
proof -
  have yx: "m y x" by (rule rp_map_sym[OF p xy])
  have "m x x" by (rule rp_map_trans[OF p xy yx])
  moreover have "m y y" by (rule rp_map_trans[OF p yx xy])
  ultimately show ?thesis by (simp add: rp_cover_def)
qed

lemma rp_map_transl:
  assumes p: "rp_plain m" and xy: "m x y"
  shows "m x z \<longleftrightarrow> m y z"
proof
  assume "m x z"
  then show "m y z" by (rule rp_map_trans[OF p rp_map_sym[OF p xy]])
next
  assume "m y z"
  then show "m x z" by (rule rp_map_trans[OF p xy])
qed

lemma rp_map_transr:
  assumes p: "rp_plain m" and xy: "m x y"
  shows "m z x \<longleftrightarrow> m z y"
proof
  assume "m z x"
  then show "m z y" by (rule rp_map_trans[OF p _ xy])
next
  assume "m z y"
  then show "m z x" by (rule rp_map_trans[OF p _ rp_map_sym[OF p xy]])
qed

lemma rp_region_eq:
  assumes p: "rp_plain m" and xy: "m x y"
  shows "rp_region m x = rp_region m y"
  using rp_map_transl[OF p xy] by (auto simp: rp_region_def)

lemma rp_region_empty:
  assumes p: "rp_plain m" and out: "x \<notin> rp_cover m"
  shows "rp_region m x = {}"
proof (rule equals0I)
  fix y assume "y \<in> rp_region m x"
  then have "m x y" by (simp add: rp_region_def)
  then show False using rp_map_cover[OF p] out by blast
qed

lemma rp_adjacent_sym:
  assumes p: "rp_plain m" and ad: "rp_adjacent m x y"
  shows "rp_adjacent m y x"
  using rp_map_sym[OF p, of y x] ad
  by (auto simp: rp_adjacent_def rp_border_def Int_commute)

lemma rp_adjacent_irrefl: "rp_plain m \<Longrightarrow> \<not> rp_adjacent m x x"
  by (cases "x \<in> rp_cover m")
     (auto simp: rp_adjacent_def rp_cover_def rp_border_def rp_region_empty rp_closure_eq)

lemma rp_adjacent_cover:
  "rp_plain m \<Longrightarrow> rp_adjacent m x y \<Longrightarrow> x \<in> rp_cover m \<and> y \<in> rp_cover m"
  by (cases "x \<in> rp_cover m"; cases "y \<in> rp_cover m")
     (auto simp: rp_adjacent_def rp_border_def rp_region_empty rp_closure_eq)

lemma rp_coloring_cover: "rp_coloring m k \<Longrightarrow> rp_cover k = rp_cover m"
  by (auto simp: rp_coloring_def rp_submap_def rp_cover_def)

end
