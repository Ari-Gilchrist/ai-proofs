(* Vertex rotations of the framed grid, following gridmap.v.
   Original G. Gonthier et al., CeCILL-B. Isabelle/HOL port: Codex. *)
theory Grid_Rotations
  imports Four_Colour_Grid_Hypermap.Grid_Permutations
begin

lemma skip_list_apply:
  assumes "x\<notin>set xs" "f x\<notin>set xs"
  shows "foldl (\<lambda>g z. skip z g) f xs x = f x"
  using assms
proof (induction xs arbitrary: f)
  case Nil then show ?case by simp
next
  case (Cons z xs)
  have first: "skip z f x = f x" using Cons.prems by (auto simp: skip_def)
  have xo: "x\<notin>set xs" and fo: "skip z f x\<notin>set xs" using Cons.prems first by auto
  have "foldl (\<lambda>g z. skip z g) (skip z f) xs x = skip z f x"
    by (rule Cons.IH[where f="skip z f", OF xo fo])
  then show ?case by (simp add: first)
qed

definition gm_vertex_set :: "grect \<Rightarrow> gpoint set" where
  "gm_vertex_set r = gmgrid r \<union> gnode ` gmgrid r \<union>
    (\<lambda>d. gnode (gnode d)) ` gmgrid r \<union>
    (\<lambda>d. gnode (gnode (gnode d))) ` gmgrid r"

lemma finite_gm_vertex_set [simp]: "finite (gm_vertex_set r)"
  by (simp add: gm_vertex_set_def)

lemma gmgrid_vertex_subset: "gmgrid r \<subseteq> gm_vertex_set r"
  by (auto simp: gm_vertex_set_def)

lemma gm_vertex_node [simp]: "gnode d\<in>gm_vertex_set r \<longleftrightarrow> d\<in>gm_vertex_set r"
proof -
  have image: "gnode ` gm_vertex_set r = gm_vertex_set r"
    by (simp add: gm_vertex_set_def image_Un image_image o_def gnode4 Un_assoc Un_commute Un_left_commute)
  have forward: "gnode x\<in>gm_vertex_set r" if "x\<in>gm_vertex_set r" for x
  proof -
    have "gnode x\<in>gnode ` gm_vertex_set r" by (rule imageI[OF that])
    then show ?thesis by (simp only: image)
  qed
  have backward: "d\<in>gm_vertex_set r" if "gnode d\<in>gm_vertex_set r"
  proof -
    have "gnode (gnode (gnode (gnode d)))\<in>gm_vertex_set r"
      by (rule forward, rule forward, rule forward, rule that)
    then show ?thesis by (simp only: gnode4)
  qed
  show ?thesis using forward backward by blast
qed

definition gmrotation :: "grect \<Rightarrow> gpoint \<Rightarrow> gpoint" where
  "gmrotation r d = (if d\<in>gm_vertex_set r then gnode d else d)"

lemma gmrotation4 [simp]: "gmrotation r (gmrotation r (gmrotation r (gmrotation r d)))=d"
  by (cases "d\<in>gm_vertex_set r") (auto simp: gmrotation_def gnode4)

lemma gmrotation_permutes: "gmrotation r permutes gm_vertex_set r"
proof -
  have inj: "inj_on (gmrotation r) (gm_vertex_set r)"
    by (rule inj_onI) (metis gmrotation4)
  have sub: "gmrotation r ` gm_vertex_set r \<subseteq> gm_vertex_set r"
    by (rule image_subsetI) (simp add: gmrotation_def)
  have image: "gmrotation r ` gm_vertex_set r = gm_vertex_set r"
    by (rule endo_inj_surj[OF finite_gm_vertex_set sub inj])
  have bij: "bij_betw (gmrotation r) (gm_vertex_set r) (gm_vertex_set r)"
    using inj image by (simp only: bij_betw_def)
  show ?thesis by (rule bij_imp_permutes[OF bij]) (simp add: gmrotation_def)
qed

lemma gnode_fconnect_end0:
  "fconnect gnode x y \<longleftrightarrow> end0g x=end0g y"
proof
  assume "fconnect gnode x y"
  then show "end0g x=end0g y" by (induction rule: fconnect_induct) (simp_all add: end0g_node)
next
  assume eq: "end0g x=end0g y"
  have cases: "y\<in>set [x,gnode x,gnode (gnode x),gnode (gnode (gnode x))]"
    by (rule same_end0g[OF eq])
  have c0: "fconnect gnode x x" by (rule fconnect_refl)
  have c1: "fconnect gnode x (gnode x)" by (rule fconnect_step)
  have c2: "fconnect gnode x (gnode (gnode x))" by (rule fconnect_stepI_r[OF c1])
  have c3: "fconnect gnode x (gnode (gnode (gnode x)))" by (rule fconnect_stepI_r[OF c2])
  show "fconnect gnode x y" using cases c0 c1 c2 c3 by auto
qed

lemma gmrotation_fconnect:
  assumes x: "x\<in>gm_vertex_set r"
  shows "fconnect (gmrotation r) x y \<longleftrightarrow> fconnect gnode x y"
proof (rule fconnect_eq_on)
  fix z assume con: "fconnect gnode x z"
  have "z\<in>gm_vertex_set r" using con x
    by (induction rule: fconnect_induct) auto
  then show "gmrotation r z=gnode z" by (simp add: gmrotation_def)
qed

definition deleted_vertex_darts :: "grect \<Rightarrow> gpoint list" where
  "deleted_vertex_darts r = (SOME xs. set xs=gm_vertex_set r - gmgrid r \<and> distinct xs)"

lemma deleted_vertex_darts_props:
  "set (deleted_vertex_darts r)=gm_vertex_set r - gmgrid r \<and> distinct (deleted_vertex_darts r)"
  unfolding deleted_vertex_darts_def
  by (rule someI_ex, rule finite_distinct_list) simp

definition gmnext :: "grect \<Rightarrow> gpoint \<Rightarrow> gpoint" where
  "gmnext r = foldl (\<lambda>g z. skip z g) (gmrotation r) (deleted_vertex_darts r)"

lemma gmnext_permutes: "gmnext r permutes gmgrid r"
proof -
  have eq: "gm_vertex_set r - set (deleted_vertex_darts r) = gmgrid r"
    using deleted_vertex_darts_props[of r] gmgrid_vertex_subset[of r] by blast
  have "foldl (\<lambda>g z. skip z g) (gmrotation r) (deleted_vertex_darts r)
      permutes (gm_vertex_set r - set (deleted_vertex_darts r))"
    by (rule skip_list_permutes[OF finite_gm_vertex_set gmrotation_permutes])
  then show ?thesis by (simp only: gmnext_def eq)
qed

definition gmface :: "grect \<Rightarrow> gpoint \<Rightarrow> gpoint" where
  "gmface r = inv (gmnext r)"

lemma gmface_permutes: "gmface r permutes gmgrid r"
  unfolding gmface_def by (rule permutes_inv[OF gmnext_permutes])

lemma gmnext_apply:
  assumes x: "x\<in>gmgrid r" and nx: "gnode x\<in>gmgrid r"
  shows "gmnext r x=gnode x"
proof -
  have xr: "gmrotation r x=gnode x"
    using gmgrid_vertex_subset[of r] x by (auto simp: gmrotation_def)
  have xo: "x\<notin>set (deleted_vertex_darts r)" and no: "gnode x\<notin>set (deleted_vertex_darts r)"
    using x nx deleted_vertex_darts_props[of r] by auto
  have fo: "gmrotation r x\<notin>set (deleted_vertex_darts r)" using xr no by simp
  show ?thesis using skip_list_apply[where f="gmrotation r", OF xo fo] xr by (simp only: gmnext_def)
qed

lemma gmface_fconnect_end0:
  assumes x: "x\<in>gmgrid r" and y: "y\<in>gmgrid r"
  shows "fconnect (gmface r) x y \<longleftrightarrow> end0g x=end0g y"
proof -
  have xo: "x\<notin>set (deleted_vertex_darts r)" and yo: "y\<notin>set (deleted_vertex_darts r)"
    using x y deleted_vertex_darts_props[of r] by auto
  have xs: "x\<in>gm_vertex_set r" using gmgrid_vertex_subset[of r] x by blast
  have connection: "fconnect (gmnext r) x y \<longleftrightarrow> fconnect (gmrotation r) x y"
    using skip_list_fconnect[where S="gm_vertex_set r" and f="gmrotation r"
      and xs="deleted_vertex_darts r" and x=x and y=y,
      OF finite_gm_vertex_set gmrotation_permutes xo] yo
    by (simp add: gmnext_def)
  interpret N: fperm "gmnext r" "gmgrid r"
    by unfold_locales (rule gmnext_permutes, rule finite_gmgrid)
  have inverse: "fconnect (gmface r) x y \<longleftrightarrow> fconnect (gmnext r) x y"
    by (simp only: gmface_def N.fconnect_inv)
  show ?thesis using inverse connection gmrotation_fconnect[OF xs, of y] gnode_fconnect_end0[of x y] by blast
qed

end
