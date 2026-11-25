(* Vertex classes of the framed rectangular grid, from gridmap.v.
   Original G. Gonthier et al., CeCILL-B. Isabelle/HOL port: Codex. *)
theory Grid_Vertices
  imports Four_Colour_Grid_Hypermap.Grid_Counting
begin

fun gvertices :: "grect \<Rightarrow> grect" where
  "gvertices (Grect a b c d) = Grect a (b+1) c (d+1)"

lemma gr_proper_Grect:
  "gr_proper (Grect a b c d) \<longleftrightarrow> a<b \<and> c<d"
  by (simp add: gr_proper_def garea_def zwidth_def)

lemma grid_nat_width_step:
  fixes a b :: int
  assumes "a\<le>b"
  shows "nat (b+1-a)=nat (b-a)+1"
proof -
  have nonnegative: "0\<le>b-a" using assms by linarith
  show ?thesis using nat_add_distrib[OF nonnegative zero_le_one]
    by (simp add: algebra_simps)
qed

lemma end0_inner_vertex:
  assumes "halfg x\<in>grect_set r"
  shows "end0g x\<in>grect_set (gvertices r)"
  using assms oddg_corners[of x]
  by (cases r; cases "halfg x"; auto simp: end0g_def gcorners_def; presburger)

lemma end1_inner_vertex:
  assumes "halfg x\<in>grect_set r"
  shows "end1g x\<in>grect_set (gvertices r)"
  using end0_inner_vertex[of "gface x" r] assms by (simp add: end0g_face)

lemma gmgrid_end0_vertex:
  assumes "x\<in>gmgrid r"
  shows "end0g x\<in>grect_set (gvertices r)"
proof -
  have cases: "halfg x\<in>grect_set r \<or> halfg (gedge x)\<in>grect_set r"
    using assms by (simp only: gmgrid_iff)
  then show ?thesis
  proof
    assume "halfg x\<in>grect_set r"
    then show ?thesis by (rule end0_inner_vertex)
  next
    assume "halfg (gedge x)\<in>grect_set r"
    then have "end1g (gedge x)\<in>grect_set (gvertices r)" by (rule end1_inner_vertex)
    then show ?thesis by (simp only: end1g_edge)
  qed
qed

lemma vertex_has_gmdart:
  assumes proper: "gr_proper r" and p: "p\<in>grect_set (gvertices r)"
  shows "p\<in>end0g ` gmgrid r"
proof -
  obtain a b c d where r: "r=Grect a b c d" by (cases r) auto
  obtain x y where point: "p=(x,y)" by (cases p) auto
  have bounds: "a<b" "c<d" using proper by (simp_all add: r gr_proper_Grect)
  let ?q = "(if x=b then x-1 else x, if y=d then y-1 else y)"
  let ?corner = "((if x=b then 1 else 0, if y=d then 1 else 0)::gpoint)"
  let ?dart = "doubleg ?q + ?corner"
  have corner: "?corner\<in>gcorners" by (auto simp: gcorners_def split: if_splits)
  have half: "halfg ?dart=?q" by (rule halfg_eq[OF corner])
  have odd: "oddg ?dart=?corner" by (rule oddg_eq[OF corner])
  have inner: "halfg ?dart\<in>grect_set r"
    using p bounds by (auto simp: half r point split: if_splits; presburger)
  have dart: "?dart\<in>gmgrid r" using inner by (simp only: gmgrid_iff; blast)
  have eq: "end0g ?dart=p" by (auto simp: end0g_def half odd point prod_eq_iff split: if_splits)
  show ?thesis using dart eq by blast
qed

lemma gmgrid_vertex_image:
  assumes "gr_proper r"
  shows "end0g ` gmgrid r = grect_set (gvertices r)"
proof (rule equalityI)
  show "end0g ` gmgrid r \<subseteq> grect_set (gvertices r)"
    by (rule image_subsetI, rule gmgrid_end0_vertex, assumption)
  show "grect_set (gvertices r) \<subseteq> end0g ` gmgrid r"
    by (rule subsetI, rule vertex_has_gmdart[OF assms], assumption)
qed

lemma card_gvertices:
  assumes "gr_proper r"
  shows "card (grect_set (gvertices r)) = (gwidth r+1) * (gheight r+1)"
proof -
  obtain a b c d where r: "r=Grect a b c d" by (cases r) auto
  have bounds: "a<b" "c<d" using assms by (simp_all add: r gr_proper_Grect)
  have width: "nat (b+1-a)=nat (b-a)+1" by (rule grid_nat_width_step) (use bounds(1) in linarith)
  have height: "nat (d+1-c)=nat (d-c)+1" by (rule grid_nat_width_step) (use bounds(2) in linarith)
  show ?thesis by (simp add: garea_card[symmetric] r garea_def zwidth_def width height)
qed

lemma fcard_gmface:
  assumes "gr_proper r"
  shows "fcard (gmface r) (gmgrid r) = (gwidth r+1) * (gheight r+1)"
  by (simp only: gmface_fcard gmgrid_vertex_image[OF assms] card_gvertices[OF assms])

end
