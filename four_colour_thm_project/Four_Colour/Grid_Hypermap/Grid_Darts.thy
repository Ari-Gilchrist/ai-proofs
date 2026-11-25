(* Dart counts for the framed grid, from gridmap.v.
   Original G. Gonthier et al., CeCILL-B. Isabelle/HOL port: Codex. *)
theory Grid_Darts
  imports Grid_Vertices
begin

definition gm_fibre :: "grect \<Rightarrow> gpoint \<Rightarrow> gpoint set" where
  "gm_fibre r c = {d\<in>gmgrid r. oddg d=c}"

lemma finite_gm_fibre [simp]: "finite (gm_fibre r c)"
  by (simp add: gm_fibre_def)

lemma gm_fibre_disjoint [simp]:
  "gm_fibre r c \<inter> gm_fibre r d = (if c=d then gm_fibre r c else {})"
  by (auto simp: gm_fibre_def)

lemma gm_fibre_image:
  assumes corner: "c\<in>gcorners"
  shows "gm_fibre r c = (\<lambda>p. doubleg p+c) `
    {p. p\<in>grect_set r \<or> p-arcg (ccw c)\<in>grect_set r}"
proof (rule equalityI)
  show "gm_fibre r c \<subseteq> (\<lambda>p. doubleg p+c) `
      {p. p\<in>grect_set r \<or> p-arcg (ccw c)\<in>grect_set r}"
  proof (rule subsetI)
    fix d assume d: "d\<in>gm_fibre r c"
    have odd: "oddg d=c" and inD: "d\<in>gmgrid r" using d by (auto simp: gm_fibre_def)
    have pixels: "halfg d\<in>{p. p\<in>grect_set r \<or> p-arcg (ccw c)\<in>grect_set r}"
      using inD by (simp add: gmgrid_iff odd)
    have eq: "doubleg (halfg d)+c=d" using halfgK[of d] by (simp only: odd)
    show "d\<in>(\<lambda>p. doubleg p+c) ` {p. p\<in>grect_set r \<or> p-arcg (ccw c)\<in>grect_set r}"
      by (rule image_eqI[where x="halfg d"]) (use pixels eq in auto)
  qed
  show "(\<lambda>p. doubleg p+c) ` {p. p\<in>grect_set r \<or> p-arcg (ccw c)\<in>grect_set r}
      \<subseteq> gm_fibre r c"
    using corner by (auto simp: gm_fibre_def gmgrid_iff halfg_eq oddg_eq)
qed

lemma card_gm_fibre_image:
  assumes corner: "c\<in>gcorners"
  shows "card (gm_fibre r c) = card {p. p\<in>grect_set r \<or> p-arcg (ccw c)\<in>grect_set r}"
proof -
  have inj: "inj_on (\<lambda>p. doubleg p+c) {p. p\<in>grect_set r \<or> p-arcg (ccw c)\<in>grect_set r}"
    by (rule inj_onI) (metis halfg_eq[OF corner])
  show ?thesis unfolding gm_fibre_image[OF corner] by (rule card_image[OF inj])
qed

lemma card_gmgrid_fibres:
  "card (gmgrid r) = card (gm_fibre r (0,0)) + card (gm_fibre r (0,1)) +
    card (gm_fibre r (1,1)) + card (gm_fibre r (1,0))"
proof -
  have cover: "gmgrid r = gm_fibre r (0,0) \<union> gm_fibre r (0,1) \<union>
      gm_fibre r (1,1) \<union> gm_fibre r (1,0)"
    using oddg_corners unfolding gm_fibre_def gcorners_def by auto
  show ?thesis by (simp add: cover card_Un_disjoint Int_Un_distrib Int_Un_distrib2 prod_eq_iff)
qed

lemma card_gmgrid:
  assumes proper: "gr_proper r"
  shows "card (gmgrid r) = 4 * gwidth r * gheight r + 2 * gwidth r + 2 * gheight r"
proof -
  obtain a b c d where r: "r=Grect a b c d" by (cases r) auto
  have bounds: "a<b" "c<d" using proper by (simp_all add: r gr_proper_Grect)
  have corners: "(0,0)\<in>gcorners" "(0,1)\<in>gcorners" "(1,1)\<in>gcorners" "(1,0)\<in>gcorners"
    by (simp_all add: gcorners_def)
  have px0: "{p. p\<in>grect_set r \<or> p-arcg (ccw (0,0))\<in>grect_set r} = grect_set (Grect a b c (d+1))"
    using bounds by (auto simp: r arcg_def ccw_def prod_eq_iff; presburger)
  have px1: "{p. p\<in>grect_set r \<or> p-arcg (ccw (0,1))\<in>grect_set r} = grect_set (Grect a (b+1) c d)"
    using bounds by (auto simp: r arcg_def ccw_def prod_eq_iff; presburger)
  have px2: "{p. p\<in>grect_set r \<or> p-arcg (ccw (1,1))\<in>grect_set r} = grect_set (Grect a b (c-1) d)"
    using bounds by (auto simp: r arcg_def ccw_def prod_eq_iff; presburger)
  have px3: "{p. p\<in>grect_set r \<or> p-arcg (ccw (1,0))\<in>grect_set r} = grect_set (Grect (a-1) b c d)"
    using bounds by (auto simp: r arcg_def ccw_def prod_eq_iff; presburger)
  have wp: "nat (b+1-a)=nat (b-a)+1" by (rule grid_nat_width_step) (use bounds(1) in linarith)
  have wm: "nat (b-(a-1))=nat (b-a)+1" using wp by (simp add: algebra_simps)
  have hp: "nat (d+1-c)=nat (d-c)+1" by (rule grid_nat_width_step) (use bounds(2) in linarith)
  have hm: "nat (d-(c-1))=nat (d-c)+1" using hp by (simp add: algebra_simps)
  have c0: "card (gm_fibre r (0,0)) = gwidth r * (gheight r+1)"
    using card_gm_fibre_image[OF corners(1), where r=r]
    by (simp only: px0; simp add: garea_card[symmetric] r garea_def zwidth_def hp)
  have c1: "card (gm_fibre r (0,1)) = (gwidth r+1) * gheight r"
    using card_gm_fibre_image[OF corners(2), where r=r]
    by (simp only: px1; simp add: garea_card[symmetric] r garea_def zwidth_def wp)
  have c2: "card (gm_fibre r (1,1)) = gwidth r * (gheight r+1)"
    using card_gm_fibre_image[OF corners(3), where r=r]
    by (simp only: px2; simp add: garea_card[symmetric] r garea_def zwidth_def hm)
  have c3: "card (gm_fibre r (1,0)) = (gwidth r+1) * gheight r"
    using card_gm_fibre_image[OF corners(4), where r=r]
    by (simp only: px3; simp add: garea_card[symmetric] r garea_def zwidth_def wm)
  show ?thesis by (simp only: card_gmgrid_fibres c0 c1 c2 c3) (simp add: algebra_simps)
qed

lemma fcard_gmedge:
  assumes "gr_proper r"
  shows "fcard (gmedge r) (gmgrid r) = 2 * gwidth r * gheight r + gwidth r + gheight r"
  using gmedge_fcard[of r] card_gmgrid[OF assms] by arith

end
