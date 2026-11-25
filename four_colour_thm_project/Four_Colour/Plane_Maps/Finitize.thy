(* Port of finitize.v: map colourings, finite restrictions, and compactness.
   Original G. Gonthier et al., CeCILL-B; Isabelle/HOL port by Codex. *)
theory Finitize
  imports Four_Colour_Plane.Realplane Four_Colour_Plane.Colour_Compactness
begin

definition rp_function_coloring :: "'c set \<Rightarrow> 'a::topological_space region_map \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> bool" where
  "rp_function_coloring C m f \<longleftrightarrow> (\<forall>x. f x \<in> C) \<and>
    (\<forall>x y. m x y \<longrightarrow> f x = f y) \<and>
    (\<forall>x y. rp_adjacent m x y \<longrightarrow> f x \<noteq> f y)"

lemma rp_colorable_zero:
  assumes p: "rp_plain m" and c: "rp_colorable_with 0 m"
  shows "rp_cover m = {}"
  using c rp_coloring_cover
  by (auto simp: rp_colorable_with_def rp_at_most_regions_def)

lemma rp_colorable_function:
  assumes p: "rp_plain m" and n: "0 < n"
  shows "rp_colorable_with n m \<longleftrightarrow> (\<exists>f. rp_function_coloring {..<n} m f)"
proof
  assume col: "rp_colorable_with n m"
  obtain k where k: "rp_coloring m k" and kn: "rp_at_most_regions n k"
    using col by (auto simp: rp_colorable_with_def)
  have kp: "rp_plain k" and mk: "rp_submap m k"
    using k by (simp_all add: rp_coloring_def)
  have cov: "rp_cover k = rp_cover m" by (rule rp_coloring_cover[OF k])
  obtain a where a: "\<forall>x\<in>rp_cover k. \<exists>i<n. k (a i) x"
    using kn by (auto simp: rp_at_most_regions_def)
  define ix where "ix = (\<lambda>x. SOME i. i < n \<and> k (a i) x)"
  have ix: "ix x < n \<and> k (a (ix x)) x" if "x \<in> rp_cover k" for x
    unfolding ix_def by (rule someI_ex) (use a that in blast)
  have ixeq: "ix x = ix y" if xy: "k x y" for x y
  proof -
    have "k (a i) x = k (a i) y" for i by (rule rp_map_transr[OF kp xy])
    then show ?thesis by (simp add: ix_def)
  qed
  define f where "f = (\<lambda>x. if x \<in> rp_cover m then ix x else 0)"
  have b: "\<forall>x. f x < n" using ix n cov by (auto simp: f_def)
  have same: "f x = f y" if xy: "m x y" for x y
  proof -
    have kxy: "k x y" using mk xy by (auto simp: rp_submap_def)
    show ?thesis using rp_map_cover[OF p xy] ixeq[OF kxy] by (simp add: f_def)
  qed
  have diff: "f x \<noteq> f y" if ad: "rp_adjacent m x y" for x y
  proof
    assume eq: "f x = f y"
    have xc: "x \<in> rp_cover m" and yc: "y \<in> rp_cover m"
      using rp_adjacent_cover[OF p ad] by auto
    have ei: "ix x = ix y" using eq xc yc by (simp add: f_def)
    have xk: "x \<in> rp_cover k" and yk: "y \<in> rp_cover k" using xc yc cov by simp_all
    have kx: "k (a (ix x)) x" using ix[OF xk] by simp
    have ky: "k (a (ix x)) y" using ix[OF yk] ei by simp
    have "k x y" by (rule rp_map_trans[OF kp rp_map_sym[OF kp kx] ky])
    then show False using k ad by (auto simp: rp_coloring_def)
  qed
  show "\<exists>f. rp_function_coloring {..<n} m f"
    using b same diff by (auto simp: rp_function_coloring_def)
next
  assume "\<exists>f. rp_function_coloring {..<n} m f"
  then obtain f where b: "\<forall>x. f x < n" and sm: "\<forall>x y. m x y \<longrightarrow> f x = f y"
    and df: "\<forall>x y. rp_adjacent m x y \<longrightarrow> f x \<noteq> f y"
    by (auto simp: rp_function_coloring_def)
  define k where "k = (\<lambda>x y. x \<in> rp_cover m \<and> y \<in> rp_cover m \<and> f x = f y)"
  have kp: "rp_plain k" by (auto simp: k_def rp_plain_def)
  have kc: "rp_cover k = rp_cover m" by (auto simp: k_def rp_cover_def)
  have km: "rp_submap m k" using rp_map_cover[OF p] sm by (auto simp: rp_submap_def k_def)
  have kcol: "rp_coloring m k" using kp kc km df by (auto simp: rp_coloring_def k_def)
  define a where "a = (\<lambda>i. SOME x. x \<in> rp_cover m \<and> f x = i)"
  have ax: "a (f x) \<in> rp_cover m \<and> f (a (f x)) = f x" if "x \<in> rp_cover m" for x
    unfolding a_def by (rule someI_ex) (use that in blast)
  have "rp_at_most_regions n k"
    unfolding rp_at_most_regions_def
    by (rule exI[of _ a]) (use ax b kc in \<open>auto simp: k_def\<close>)
  then show "rp_colorable_with n m" using kcol by (auto simp: rp_colorable_with_def)
qed

definition rp_restrict :: "'a region_map \<Rightarrow> 'a set \<Rightarrow> 'a region_map" where
  "rp_restrict m S x y \<longleftrightarrow> x \<in> S \<and> y \<in> S \<and> m x y"

definition rp_saturated :: "'a region_map \<Rightarrow> 'a set \<Rightarrow> bool" where
  "rp_saturated m S \<longleftrightarrow> (\<forall>x y. x \<in> S \<longrightarrow> m x y \<longrightarrow> y \<in> S)"

definition rp_selection :: "'a region_map \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "rp_selection m F = \<Union>(rp_region m ` F)"

lemma rp_plain_restrict:
  assumes p: "rp_plain m"
  shows "rp_plain (rp_restrict m S)"
  unfolding rp_plain_def
proof (intro conjI)
  show "\<forall>x y. rp_restrict m S x y \<longrightarrow> rp_restrict m S y x"
  proof (intro allI impI)
    fix x y assume h: "rp_restrict m S x y"
    have xy: "m x y" using h by (simp add: rp_restrict_def)
    show "rp_restrict m S y x" using rp_map_sym[OF p xy] h by (simp add: rp_restrict_def)
  qed
  show "\<forall>x y z. rp_restrict m S x y \<longrightarrow> rp_restrict m S y z \<longrightarrow> rp_restrict m S x z"
  proof (intro allI impI)
    fix x y z assume xy: "rp_restrict m S x y" and yz: "rp_restrict m S y z"
    have a: "m x y" and b: "m y z" using xy yz by (simp_all add: rp_restrict_def)
    show "rp_restrict m S x z" using rp_map_trans[OF p a b] xy yz by (simp add: rp_restrict_def)
  qed
qed

lemma rp_restrict_cover: "rp_cover (rp_restrict m S) = S \<inter> rp_cover m"
  by (auto simp: rp_cover_def rp_restrict_def)

lemma rp_restrict_region:
  "rp_saturated m S \<Longrightarrow> rp_region (rp_restrict m S) x = (if x \<in> S then rp_region m x else {})"
  by (auto simp: rp_saturated_def rp_region_def rp_restrict_def)

lemma rp_simple_restrict:
  "rp_simple_map m \<Longrightarrow> rp_saturated m S \<Longrightarrow> rp_simple_map (rp_restrict m S)"
  by (auto simp: rp_simple_map_iff rp_plain_restrict rp_restrict_region)

lemma rp_selection_saturated:
  assumes p: "rp_plain m"
  shows "rp_saturated m (rp_selection m F)"
  unfolding rp_saturated_def
proof (intro allI impI)
  fix x y assume xs: "x \<in> rp_selection m F" and xy: "m x y"
  obtain a where a: "a \<in> F" "m a x" using xs by (auto simp: rp_selection_def rp_region_def)
  have "m a y" by (rule rp_map_trans[OF p a(2) xy])
  then show "y \<in> rp_selection m F" using a(1) by (auto simp: rp_selection_def rp_region_def)
qed

lemma rp_selection_cover:
  assumes p: "rp_plain m"
  shows "rp_selection m F \<subseteq> rp_cover m"
proof
  fix x assume "x \<in> rp_selection m F"
  then obtain a where "m a x" by (auto simp: rp_selection_def rp_region_def)
  then show "x \<in> rp_cover m" using rp_map_cover[OF p] by blast
qed

lemma rp_in_selection:
  "x \<in> F \<Longrightarrow> x \<in> rp_cover m \<Longrightarrow> x \<in> rp_selection m F"
  by (auto simp: rp_selection_def rp_region_def rp_cover_def)

lemma rp_finite_restriction:
  assumes sm: "rp_simple_map m" and fin: "finite F"
  shows "rp_finite_simple_map (rp_restrict m (rp_selection m F))"
proof -
  have p: "rp_plain m" using sm by (simp add: rp_simple_map_def)
  have sat: "rp_saturated m (rp_selection m F)" by (rule rp_selection_saturated[OF p])
  have simple: "rp_simple_map (rp_restrict m (rp_selection m F))" by (rule rp_simple_restrict[OF sm sat])
  obtain xs where xs: "set xs = F" using finite_list[OF fin] by blast
  have bound: "rp_at_most_regions (length xs) (rp_restrict m (rp_selection m F))"
    unfolding rp_at_most_regions_def
  proof (intro exI[of _ "\<lambda>i. xs ! i"] ballI)
    fix x assume xc: "x \<in> rp_cover (rp_restrict m (rp_selection m F))"
    then obtain a where a: "a \<in> F" "m a x"
      by (auto simp: rp_restrict_cover rp_selection_def rp_region_def)
    obtain i where i: "i < length xs" "xs ! i = a" using a(1) xs by (auto simp: in_set_conv_nth)
    have ac: "a \<in> rp_cover m" using rp_map_cover[OF p a(2)] by blast
    have "a \<in> rp_selection m F" by (rule rp_in_selection[OF a(1) ac])
    then show "\<exists>i<length xs. rp_restrict m (rp_selection m F) (xs ! i) x"
      using i a(2) xc by (auto simp: rp_restrict_def rp_restrict_cover)
  qed
  show ?thesis using simple bound by (auto simp: rp_finite_simple_map_def)
qed

lemma rp_at_most_restrict:
  assumes p: "rp_plain m" and sat: "rp_saturated m S" and n: "rp_at_most_regions n m"
  shows "rp_at_most_regions n (rp_restrict m S)"
proof -
  obtain f where f: "\<forall>x\<in>rp_cover m. \<exists>i<n. m (f i) x" using n by (auto simp: rp_at_most_regions_def)
  show ?thesis unfolding rp_at_most_regions_def
  proof (intro exI[of _ f] ballI)
    fix x assume "x \<in> rp_cover (rp_restrict m S)"
    then have x: "x \<in> S" "x \<in> rp_cover m" by (auto simp: rp_restrict_cover)
    obtain i where i: "i < n" "m (f i) x" using f x(2) by blast
    have "f i \<in> S" using sat x(1) rp_map_sym[OF p i(2)] by (auto simp: rp_saturated_def)
    then show "\<exists>i<n. rp_restrict m S (f i) x" using i x(1) by (auto simp: rp_restrict_def)
  qed
qed


lemma rp_plain_corner:
  assumes p: "rp_plain m"
  shows "rp_plain (rp_corner_map m z)"
  unfolding rp_plain_def
proof (intro conjI)
  show "\<forall>x y. rp_corner_map m z x y \<longrightarrow> rp_corner_map m z y x"
  proof (intro allI impI)
    fix x y assume h: "rp_corner_map m z x y"
    have xy: "m x y" and cl: "z \<in> rp_closure (rp_region m x)"
      using h by (simp_all add: rp_corner_map_def)
    show "rp_corner_map m z y x"
      using rp_map_sym[OF p xy] cl rp_region_eq[OF p xy]
      by (simp add: rp_corner_map_def)
  qed
  show "\<forall>x y w. rp_corner_map m z x y \<longrightarrow> rp_corner_map m z y w \<longrightarrow> rp_corner_map m z x w"
  proof (intro allI impI)
    fix x y w assume xy: "rp_corner_map m z x y" and yw: "rp_corner_map m z y w"
    have a: "m x y" and b: "m y w" using xy yw by (simp_all add: rp_corner_map_def)
    show "rp_corner_map m z x w" using rp_map_trans[OF p a b] xy by (simp add: rp_corner_map_def)
  qed
qed

lemma rp_corner_saturated:
  "rp_saturated m S \<Longrightarrow> rp_saturated (rp_corner_map m z) S"
  by (auto simp: rp_saturated_def rp_corner_map_def)

lemma rp_restrict_corner:
  assumes sat: "rp_saturated m S"
  shows "rp_corner_map (rp_restrict m S) z = rp_restrict (rp_corner_map m z) S"
  by (rule ext, rule ext)
     (auto simp: rp_corner_map_def rp_restrict_def rp_restrict_region[OF sat] rp_closure_eq)

lemma rp_restrict_not_corner:
  assumes p: "rp_plain m" and sat: "rp_saturated m S" and z: "z \<in> rp_not_corner m"
  shows "z \<in> rp_not_corner (rp_restrict m S)"
proof -
  have nc: "rp_at_most_regions 2 (rp_corner_map m z)" using z by (simp add: rp_not_corner_def)
  have satc: "rp_saturated (rp_corner_map m z) S" by (rule rp_corner_saturated[OF sat])
  have "rp_at_most_regions 2 (rp_restrict (rp_corner_map m z) S)"
    by (rule rp_at_most_restrict[OF rp_plain_corner[OF p] satc nc])
  then show ?thesis by (simp add: rp_not_corner_def rp_restrict_corner[OF sat])
qed

lemma rp_restrict_adjacent:
  assumes p: "rp_plain m" and sat: "rp_saturated m S"
    and x: "x \<in> S" and y: "y \<in> S" and ad: "rp_adjacent m x y"
  shows "rp_adjacent (rp_restrict m S) x y"
proof -
  obtain z where z: "z \<in> rp_not_corner m" "z \<in> rp_border m x y"
    using ad by (auto simp: rp_adjacent_def)
  have nc: "z \<in> rp_not_corner (rp_restrict m S)"
    by (rule rp_restrict_not_corner[OF p sat z(1)])
  have bd: "z \<in> rp_border (rp_restrict m S) x y"
    using z(2) x y by (simp add: rp_border_def rp_restrict_region[OF sat])
  show ?thesis using nc bd ad x y by (auto simp: rp_adjacent_def rp_restrict_def)
qed

text \<open>This is the compactness extension used by fourcolor.v. A finite set of
  colour constraints mentions finitely many map regions; restrict to their union,
  colour that finite simple map, and apply finite-palette compactness.\<close>

theorem rp_compactness_extension_positive:
  fixes m :: "'a::topological_space region_map"
  assumes n: "0 < n" and sm: "rp_simple_map m"
    and finite_case: "\<And>q :: 'a region_map. rp_finite_simple_map q \<Longrightarrow> rp_colorable_with n q"
  shows "rp_colorable_with n m"
proof -
  have p: "rp_plain m" using sm by (simp add: rp_simple_map_def)
  let ?x = "\<lambda>j :: bool \<times> ('a \<times> 'a). fst (snd j)"
  let ?y = "\<lambda>j :: bool \<times> ('a \<times> 'a). snd (snd j)"
  define R where "R = (\<lambda>j :: bool \<times> ('a \<times> 'a).
    {p :: nat \<times> nat. if fst j then (rp_adjacent m (?x j) (?y j) \<longrightarrow> fst p \<noteq> snd p)
      else (m (?x j) (?y j) \<longrightarrow> fst p = snd p)})"
  have loc: "\<exists>f :: 'a \<Rightarrow> nat. (\<forall>v. f v \<in> {..<n}) \<and>
      (\<forall>j\<in>J. (f (?x j), f (?y j)) \<in> R j)" if fj: "finite J" for J
  proof -
    let ?F = "?x ` J \<union> ?y ` J"
    let ?S = "rp_selection m ?F"
    let ?q = "rp_restrict m ?S"
    have fin: "finite ?F" using fj by simp
    have sat: "rp_saturated m ?S" by (rule rp_selection_saturated[OF p])
    have fp: "rp_finite_simple_map ?q" by (rule rp_finite_restriction[OF sm fin])
    have qp: "rp_plain ?q" by (rule rp_plain_restrict[OF p])
    obtain f where fc: "rp_function_coloring {..<n} ?q f"
      using rp_colorable_function[OF qp n] finite_case[OF fp] by blast
    have equal: "f (?x j) = f (?y j)" if j: "j \<in> J" and xy: "m (?x j) (?y j)" for j
    proof -
      have cv: "?x j \<in> rp_cover m \<and> ?y j \<in> rp_cover m" by (rule rp_map_cover[OF p xy])
      have xs: "?x j \<in> ?S" and ys: "?y j \<in> ?S"
        by (rule rp_in_selection; use j cv in auto)+
      have "?q (?x j) (?y j)" using xs ys xy by (simp add: rp_restrict_def)
      then show ?thesis using fc by (auto simp: rp_function_coloring_def)
    qed
    have different: "f (?x j) \<noteq> f (?y j)" if j: "j \<in> J" and ad: "rp_adjacent m (?x j) (?y j)" for j
    proof -
      have cv: "?x j \<in> rp_cover m \<and> ?y j \<in> rp_cover m" by (rule rp_adjacent_cover[OF p ad])
      have xs: "?x j \<in> ?S" and ys: "?y j \<in> ?S"
        by (rule rp_in_selection; use j cv in auto)+
      have "rp_adjacent ?q (?x j) (?y j)" by (rule rp_restrict_adjacent[OF p sat xs ys ad])
      then show ?thesis using fc by (auto simp: rp_function_coloring_def)
    qed
    have "\<forall>j\<in>J. (f (?x j), f (?y j)) \<in> R j"
      using equal different by (auto simp: R_def)
    then show ?thesis using fc by (auto simp: rp_function_coloring_def)
  qed
  have finc: "finite {..<n}" by simp
  obtain f where b: "\<forall>v. f v \<in> {..<n}" and r: "\<forall>j. (f (?x j), f (?y j)) \<in> R j"
    using finite_colour_constraint_compactness[OF finc loc] by blast
  have equal: "m x y \<Longrightarrow> f x = f y" for x y
    using r[rule_format, of "(False,(x,y))"] by (simp add: R_def)
  have different: "rp_adjacent m x y \<Longrightarrow> f x \<noteq> f y" for x y
    using r[rule_format, of "(True,(x,y))"] by (simp add: R_def)
  have "rp_function_coloring {..<n} m f" using b equal different by (auto simp: rp_function_coloring_def)
  then show ?thesis using rp_colorable_function[OF p n] by blast
qed


lemma rp_colorable_empty: "rp_colorable_with n (\<lambda>_ _. False)"
proof -
  have col: "rp_coloring (\<lambda>_ _. False) (\<lambda>_ _. False)"
    by (simp add: rp_coloring_def rp_plain_def rp_submap_def rp_cover_def)
  have fin: "rp_at_most_regions n (\<lambda>_ _. False)"
    by (simp add: rp_at_most_regions_def rp_cover_def)
  show ?thesis using col fin by (auto simp: rp_colorable_with_def)
qed

theorem rp_compactness_extension:
  fixes m :: "'a::topological_space region_map"
  assumes sm: "rp_simple_map m"
    and finite_case: "\<And>q :: 'a region_map. rp_finite_simple_map q \<Longrightarrow> rp_colorable_with n q"
  shows "rp_colorable_with n m"
proof (cases "n = 0")
  case False
  then have "0 < n" by simp
  then show ?thesis by (rule rp_compactness_extension_positive[OF _ sm finite_case])
next
  case True
  have p: "rp_plain m" using sm by (simp add: rp_simple_map_def)
  have empty: "rp_cover m = {}"
  proof (rule ccontr)
    assume "rp_cover m \<noteq> {}"
    then obtain x where xc: "x \<in> rp_cover m" by blast
    let ?q = "rp_restrict m (rp_selection m {x})"
    have fq: "rp_finite_simple_map ?q" by (rule rp_finite_restriction[OF sm]) simp
    have col: "rp_colorable_with 0 ?q" using finite_case[OF fq] True by simp
    have eq: "rp_cover ?q = {}" by (rule rp_colorable_zero[OF rp_plain_restrict[OF p] col])
    have "x \<in> rp_selection m {x}" by (rule rp_in_selection) (simp_all add: xc)
    then have "x \<in> rp_cover ?q" using xc by (simp add: rp_restrict_cover)
    then show False using eq by simp
  qed
  have no: "\<not> m x y" for x y
  proof
    assume "m x y"
    then show False using rp_map_cover[OF p] empty by blast
  qed
  have "m = (\<lambda>_ _. False)" using no by (auto simp: fun_eq_iff)
  then show ?thesis using rp_colorable_empty[of n] by simp
qed

end
