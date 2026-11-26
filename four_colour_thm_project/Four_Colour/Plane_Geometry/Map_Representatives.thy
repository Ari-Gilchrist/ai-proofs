(* Region transversals and adjacency neighbourhoods from discretize.v.
   Original G. Gonthier et al., CeCILL-B. Isabelle/HOL port: Codex. *)
theory Map_Representatives
  imports Four_Colour_Plane_Maps.Finitize
begin

definition rp_regions :: "'a region_map \<Rightarrow> 'a set set" where
  "rp_regions m = rp_region m ` rp_cover m"

lemma rp_finite_regions:
  assumes p: "rp_plain m" and n: "rp_at_most_regions n m"
  shows "finite (rp_regions m)"
proof -
  obtain f where f: "\<forall>x\<in>rp_cover m. \<exists>i<n. m (f i) x"
    using n by (auto simp: rp_at_most_regions_def)
  have sub: "rp_regions m \<subseteq> rp_region m ` f ` {..<n}"
  proof
    fix A assume "A \<in> rp_regions m"
    then obtain x where x: "x \<in> rp_cover m" "A=rp_region m x"
      by (auto simp: rp_regions_def)
    obtain i where i: "i<n" "m (f i) x" using f x by blast
    have "A = rp_region m (f i)" using x rp_region_eq[OF p i(2)] by simp
    then show "A \<in> rp_region m ` f ` {..<n}" using i by blast
  qed
  show ?thesis by (rule finite_subset[OF sub]) simp
qed

lemma rp_exists_map_repr:
  assumes p: "rp_plain m" and n: "rp_at_most_regions n m"
  shows "\<exists>R. finite R \<and> R \<subseteq> rp_cover m \<and>
    (\<forall>x\<in>rp_cover m. \<exists>r\<in>R. m r x) \<and>
    (\<forall>r\<in>R. \<forall>s\<in>R. m r s \<longrightarrow> r=s)"
proof -
  define rep where "rep = (\<lambda>A. SOME x. x\<in>rp_cover m \<and> rp_region m x=A)"
  have rep: "rep A \<in> rp_cover m \<and> rp_region m (rep A)=A" if "A\<in>rp_regions m" for A
    unfolding rep_def by (rule someI_ex) (use that in \<open>auto simp: rp_regions_def\<close>)
  let ?R = "rep ` rp_regions m"
  have fin: "finite ?R" by (rule finite_imageI[OF rp_finite_regions[OF p n]])
  have cov: "?R \<subseteq> rp_cover m" using rep by blast
  have cover: "\<exists>r\<in>?R. m r x" if x: "x\<in>rp_cover m" for x
  proof -
    have A: "rp_region m x\<in>rp_regions m" using x by (auto simp: rp_regions_def)
    have xx: "x\<in>rp_region m x" using x by (simp add: rp_region_def rp_cover_def)
    have "m (rep (rp_region m x)) x" using rep[OF A] xx by (auto simp: rp_region_def)
    then show ?thesis using A by blast
  qed
  have unique: "r=s" if r: "r\<in>?R" and s: "s\<in>?R" and rs: "m r s" for r s
  proof -
    obtain A B where A: "A\<in>rp_regions m" "r=rep A" and B: "B\<in>rp_regions m" "s=rep B"
      using r s by blast
    have "A=B" using rep[OF A(1)] rep[OF B(1)] rp_region_eq[OF p rs] A B by simp
    then show ?thesis using A B by simp
  qed
  have C: "\<forall>x\<in>rp_cover m. \<exists>r\<in>?R. m r x" by (intro ballI) (rule cover)
  have U: "\<forall>r\<in>?R. \<forall>s\<in>?R. m r s \<longrightarrow> r=s" by (intro ballI impI) (rule unique)
  show ?thesis by (rule exI[of _ ?R]) (use fin cov C U in blast)
qed

lemma rp_at_most_two_regions:
  assumes p: "rp_plain m" and n: "rp_at_most_regions 2 m"
    and a: "a\<in>rp_cover m" and b: "b\<in>rp_cover m" and c: "c\<in>rp_cover m"
    and ab: "\<not>m a b"
  shows "m a c \<or> m b c"
proof -
  obtain f where f: "\<forall>x\<in>rp_cover m. \<exists>i<(2::nat). m (f i) x"
    using n by (auto simp: rp_at_most_regions_def)
  obtain i j k where i: "i<2" "m (f i) a" and j: "j<2" "m (f j) b"
    and k: "k<2" "m (f k) c" using f a b c by blast
  have eq: "m x y" if "m (f q) x" "m (f q) y" for q x y
    by (rule rp_map_trans[OF p rp_map_sym[OF p that(1)] that(2)])
  have ij: "i\<noteq>j" using eq[OF i(2)] j(2) ab by auto
  have "k=i \<or> k=j" using i(1) j(1) k(1) ij by presburger
  then show ?thesis using eq[OF i(2)] eq[OF j(2)] k(2) by auto
qed

lemma rp_closure_region_cover:
  assumes p: "rp_plain m" and z: "z\<in>closure (rp_region m x)"
  shows "x\<in>rp_cover m"
  using z rp_region_empty[OF p, of x] by (cases "x\<in>rp_cover m") auto

lemma rp_noncorner_two_regions:
  assumes p: "rp_plain m" and nc: "z\<in>rp_not_corner m" and ab: "\<not>m a b"
    and za: "z\<in>closure (rp_region m a)" and zb: "z\<in>closure (rp_region m b)"
    and zc: "z\<in>closure (rp_region m c)"
  shows "m a c \<or> m b c"
proof -
  have cover: "x\<in>rp_cover (rp_corner_map m z)" if "z\<in>closure (rp_region m x)" for x
    using rp_closure_region_cover[OF p that] that
    by (simp add: rp_cover_def rp_corner_map_def rp_closure_eq)
  have n: "rp_at_most_regions 2 (rp_corner_map m z)" using nc by (simp add: rp_not_corner_def)
  have ab': "\<not>rp_corner_map m z a b" using ab by (simp add: rp_corner_map_def)
  have "rp_corner_map m z a c \<or> rp_corner_map m z b c"
    by (rule rp_at_most_two_regions[OF rp_plain_corner[OF p] n cover[OF za] cover[OF zb] cover[OF zc] ab'])
  then show ?thesis by (auto simp: rp_corner_map_def)
qed

text \<open>A non-corner adjacency point has a neighbourhood avoiding any
  prescribed finite collection of other regions. This is the local step used
  by @{text exists_adjbox} in discretize.v.\<close>
lemma rp_adjacency_neighbourhood:
  fixes m :: "rp_point region_map"
  assumes p: "rp_plain m" and fin: "finite R" and ad: "rp_adjacent m a b"
    and z: "z\<in>rp_not_corner m \<inter> rp_border m a b"
  shows "\<exists>u v w t. z\<in>rp_rectangle u v w t \<and>
    (\<forall>r\<in>R. \<not>m a r \<and> \<not>m b r \<longrightarrow>
      rp_rectangle u v w t \<inter> closure (rp_region m r) = {})"
proof -
  let ?S = "{r\<in>R. \<not>m a r \<and> \<not>m b r}"
  let ?C = "\<Union>r\<in>?S. closure (rp_region m r)"
  have cls: "closed ?C" by (rule closed_UN) (use fin in auto)
  have za: "z\<in>closure (rp_region m a)" and zb: "z\<in>closure (rp_region m b)"
    and nc: "z\<in>rp_not_corner m" using z by (auto simp: rp_border_def rp_closure_eq)
  have ab: "\<not>m a b" using ad by (simp add: rp_adjacent_def)
  have out: "z\<notin>?C"
    using rp_noncorner_two_regions[OF p nc ab za zb] by blast
  have op: "rp_open (-?C)" unfolding rp_open_eq by (rule open_Compl[OF cls])
  have zin: "z\<in>-?C" by (rule ComplI) (use out in blast)
  obtain u v w t where zz: "z\<in>rp_rectangle u v w t" and sub: "rp_rectangle u v w t\<subseteq>-?C"
    using bspec[OF op[unfolded rp_open_def] zin] by blast
  show ?thesis
    apply (rule exI[of _ u])
    apply (rule exI[of _ v])
    apply (rule exI[of _ w])
    apply (rule exI[of _ t])
    using zz sub by auto
qed

definition rp_map_repr :: "'a region_map \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool" where
  "rp_map_repr m n f \<longleftrightarrow>
    (\<forall>i<n. f i\<in>rp_cover m) \<and>
    (\<forall>i<n. \<forall>j<n. m (f i) (f j) \<longrightarrow> i=j) \<and>
    (\<forall>x\<in>rp_cover m. \<exists>i<n. m (f i) x)"

lemma rp_exists_indexed_map_repr:
  assumes p: "rp_plain m" and n: "rp_at_most_regions n m"
  shows "\<exists>k f. rp_map_repr m k f"
proof -
  obtain R where R: "finite R" "R\<subseteq>rp_cover m"
    "\<forall>x\<in>rp_cover m. \<exists>r\<in>R. m r x" "\<forall>r\<in>R. \<forall>s\<in>R. m r s \<longrightarrow> r=s"
    using rp_exists_map_repr[OF p n] by blast
  obtain xs where xs: "set xs=R" "distinct xs" using finite_distinct_list[OF R(1)] by blast
  have cov: "xs!i\<in>rp_cover m" if "i<length xs" for i using R(2) xs that by auto
  have uniq: "i=j" if "i<length xs" "j<length xs" "m (xs!i) (xs!j)" for i j
  proof -
    have "xs!i=xs!j" using R(4) xs(1) that by auto
    then show ?thesis using xs(2) that by (simp add: nth_eq_iff_index_eq)
  qed
  have cover: "\<exists>i<length xs. m (xs!i) x" if xc: "x\<in>rp_cover m" for x
  proof -
    obtain r where r: "r\<in>R" "m r x" using bspec[OF R(3) xc] by blast
    have rx: "r\<in>set xs" using r(1) xs(1) by simp
    obtain i where i: "i<length xs" "r=xs!i" using rx by (auto simp only: in_set_conv_nth)
    show ?thesis by (rule exI[of _ i]) (use i r(2) in simp)
  qed
  have CV: "\<forall>i<length xs. xs!i\<in>rp_cover m" by (intro allI impI) (rule cov)
  have UN: "\<forall>i<length xs. \<forall>j<length xs. m (xs!i) (xs!j) \<longrightarrow> i=j"
    by (intro allI impI) (rule uniq)
  have CO: "\<forall>x\<in>rp_cover m. \<exists>i<length xs. m (xs!i) x" by (intro ballI) (rule cover)
  have rv: "rp_map_repr m (length xs) (\<lambda>i. xs!i)"
    using CV UN CO unfolding rp_map_repr_def by blast
  show ?thesis
    apply (rule exI[of _ "length xs"])
    apply (rule exI[of _ "\<lambda>i. xs!i"])
    by (rule rv)
qed

lemma rp_representative_colour_transfer:
  assumes p: "rp_plain m" and repr: "rp_map_repr m k r" and n: "0<n"
    and colours: "\<And>i. i<k \<Longrightarrow> c i<n"
    and proper: "\<And>i j. i<k \<Longrightarrow> j<k \<Longrightarrow> rp_adjacent m (r i) (r j) \<Longrightarrow> c i\<noteq>c j"
  shows "rp_colorable_with n m"
proof -
  define ix where "ix = (\<lambda>x. SOME i. i<k \<and> m (r i) x)"
  have ix: "ix x<k \<and> m (r (ix x)) x" if "x\<in>rp_cover m" for x
    unfolding ix_def by (rule someI_ex) (use repr that in \<open>auto simp: rp_map_repr_def\<close>)
  have same: "ix x=ix y" if xy: "m x y" for x y
  proof -
    have "m (r i) x \<longleftrightarrow> m (r i) y" for i by (rule rp_map_transr[OF p xy])
    then show ?thesis by (simp add: ix_def)
  qed
  have adjacent: "rp_adjacent m (r (ix x)) (r (ix y))" if ad: "rp_adjacent m x y" for x y
  proof -
    have xc: "x\<in>rp_cover m" and yc: "y\<in>rp_cover m" using rp_adjacent_cover[OF p ad] by auto
    have ex: "rp_region m (r (ix x)) = rp_region m x" by (rule rp_region_eq[OF p]) (use ix[OF xc] in simp)
    have ey: "rp_region m (r (ix y)) = rp_region m y" by (rule rp_region_eq[OF p]) (use ix[OF yc] in simp)
    have rel: "m (r (ix x)) (r (ix y)) \<longleftrightarrow> m x y"
      using rp_map_transl[OF p conjunct2[OF ix[OF xc]], of "r (ix y)"]
        rp_map_transr[OF p conjunct2[OF ix[OF yc]], of x] by simp
    show ?thesis using ad rel ex ey by (simp add: rp_adjacent_def rp_border_def)
  qed
  define f where "f=(\<lambda>x. if x\<in>rp_cover m then c (ix x) else 0)"
  have b: "\<forall>x. f x<n" using colours ix n by (auto simp: f_def)
  have sm: "f x=f y" if "m x y" for x y
    using same[OF that] rp_map_cover[OF p that] by (simp add: f_def)
  have df: "f x\<noteq>f y" if ad: "rp_adjacent m x y" for x y
    using proper[OF _ _ adjacent[OF ad]] ix rp_adjacent_cover[OF p ad]
    by (auto simp: f_def)
  have "rp_function_coloring {..<n} m f" using b sm df
    by (auto simp: rp_function_coloring_def)
  then show ?thesis using rp_colorable_function[OF p n] by blast
qed

lemma rp_repr_relation:
  assumes repr: "rp_map_repr m k r" and i: "i<k" and j: "j<k"
  shows "m (r i) (r j) \<longleftrightarrow> i=j"
  using repr i j by (auto simp: rp_map_repr_def rp_cover_def)

lemma rp_noncorner_index_pairs:
  assumes p: "rp_plain m" and repr: "rp_map_repr m k r"
    and bounds: "i<k" "j<k" "u<k" "v<k" and sort: "i<j" "u<v"
    and z: "z\<in>rp_not_corner m \<inter> rp_border m (r i) (r j)"
      "z\<in>rp_border m (r u) (r v)"
  shows "(i,j)=(u,v)"
proof -
  have nc: "z\<in>rp_not_corner m" and zi: "z\<in>closure (rp_region m (r i))"
    and zj: "z\<in>closure (rp_region m (r j))"
    and zu: "z\<in>closure (rp_region m (r u))" and zv: "z\<in>closure (rp_region m (r v))"
    using z by (auto simp: rp_border_def rp_closure_eq)
  have ne: "\<not>m (r i) (r j)" using rp_repr_relation[OF repr bounds(1,2)] sort by simp
  have u: "i=u \<or> j=u"
    using rp_noncorner_two_regions[OF p nc ne zi zj zu]
      rp_repr_relation[OF repr bounds(1,3)] rp_repr_relation[OF repr bounds(2,3)] by simp
  have v: "i=v \<or> j=v"
    using rp_noncorner_two_regions[OF p nc ne zi zj zv]
      rp_repr_relation[OF repr bounds(1,4)] rp_repr_relation[OF repr bounds(2,4)] by simp
  show ?thesis using u v sort by (auto; presburger)
qed

definition rp_adj_indices :: "'a::topological_space region_map \<Rightarrow> nat \<Rightarrow> (nat\<Rightarrow>'a) \<Rightarrow> (nat\<times>nat) set" where
  "rp_adj_indices m k r = {(i,j). i<k \<and> j<k \<and> i<j \<and> rp_adjacent m (r i) (r j)}"
lemma finite_rp_adj_indices [simp]: "finite (rp_adj_indices m k r)"
proof (rule finite_subset[of _ "{..<k}\<times>{..<k}"])
  show "rp_adj_indices m k r \<subseteq> {..<k}\<times>{..<k}" by (auto simp: rp_adj_indices_def)
qed simp

lemma rp_exists_adjacency_witnesses:
  assumes p: "rp_plain m" and repr: "rp_map_repr m k r"
  shows "\<exists>w. inj_on w (rp_adj_indices m k r) \<and>
    (\<forall>e\<in>rp_adj_indices m k r.
      w e\<in>rp_not_corner m \<inter> rp_border m (r (fst e)) (r (snd e)))"
proof -
  let ?E = "rp_adj_indices m k r"
  define w where "w=(\<lambda>e. SOME z. z\<in>rp_not_corner m \<inter> rp_border m (r (fst e)) (r (snd e)))"
  have w: "w e\<in>rp_not_corner m \<inter> rp_border m (r (fst e)) (r (snd e))" if "e\<in>?E" for e
    unfolding w_def by (rule someI_ex) (use that in \<open>auto simp: rp_adj_indices_def rp_adjacent_def\<close>)
  have inj: "inj_on w ?E"
  proof (rule inj_onI)
    fix e f assume e: "e\<in>?E" and f: "f\<in>?E" and eq: "w e=w f"
    obtain i j u v where ef: "e=(i,j)" "f=(u,v)" by (cases e; cases f) auto
    have "(i,j)=(u,v)"
      by (rule rp_noncorner_index_pairs[OF p repr])
        (use e f w[OF e] w[OF f] eq in \<open>auto simp: ef rp_adj_indices_def\<close>)
    then show "e=f" by (simp add: ef)
  qed
  show ?thesis by (rule exI[of _ w]) (use inj w in blast)
qed

end
