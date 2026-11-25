(* Cycle counting for the framed grid in gridmap.v.
   Original G. Gonthier et al., CeCILL-B. Isabelle/HOL port: Codex. *)
theory Grid_Counting
  imports Framed_Grid
begin

lemma card_images_same_kernel:
  assumes finite: "finite A"
    and kernel: "\<forall>x\<in>A. \<forall>y\<in>A. (f x=f y \<longleftrightarrow> g x=g y)"
  shows "card (f ` A)=card (g ` A)"
  using finite kernel
proof (induction A rule: finite_induct)
  case empty then show ?case by simp
next
  case (insert x A)
  have kernel: "\<forall>a\<in>A. \<forall>b\<in>A. (f a=f b \<longleftrightarrow> g a=g b)"
    using insert.prems by blast
  have ih: "card (f ` A)=card (g ` A)" by (rule insert.IH[OF kernel])
  have appear: "f x\<in>f ` A \<longleftrightarrow> g x\<in>g ` A"
  proof
    assume "f x\<in>f ` A"
    then obtain y where y: "y\<in>A" "f x=f y" by blast
    have "g x=g y" using insert.prems y by blast
    then show "g x\<in>g ` A" using y(1) by blast
  next
    assume "g x\<in>g ` A"
    then obtain y where y: "y\<in>A" "g x=g y" by blast
    have "f x=f y" using insert.prems y by blast
    then show "f x\<in>f ` A" using y(1) by blast
  qed
  show ?case using insert.hyps ih appear by (simp add: card_insert_if)
qed

lemma fcard_image_kernel:
  assumes perm: "fperm f D"
    and kernel: "\<forall>x\<in>D. \<forall>y\<in>D. (fconnect f x y \<longleftrightarrow> h x=h y)"
  shows "fcard f D=card (h ` D)"
proof -
  interpret P: fperm f D by (rule perm)
  have eq: "cyc f x=cyc f y \<longleftrightarrow> h x=h y" if "x\<in>D" "y\<in>D" for x y
    using P.cyc_eq_iff kernel that by blast
  show ?thesis unfolding fcard_def
    by (rule card_images_same_kernel[OF P.fin]) (use eq in blast)
qed

lemma gmface_fcard:
  "fcard (gmface r) (gmgrid r)=card (end0g ` gmgrid r)"
proof -
  have perm: "fperm (gmface r) (gmgrid r)"
    by unfold_locales (rule gmface_permutes, rule finite_gmgrid)
  show ?thesis by (rule fcard_image_kernel[OF perm])
    (intro ballI, rule gmface_fconnect_end0, assumption+)
qed

lemma gmedge_fcard:
  "card (gmgrid r)=2 * fcard (gmedge r) (gmgrid r)"
proof -
  interpret G: hypermap "gmdart_map r" by (rule hypermap_gmdart_map)
  have eq: "card (darts (gmdart_map r)) =
      2 * fcard (edge (gmdart_map r)) (darts (gmdart_map r))"
  proof (rule G.E.card_uniform_orbits)
    show "darts (gmdart_map r) \<subseteq> darts (gmdart_map r)" by simp
    fix x assume x: "x\<in>darts (gmdart_map r)"
    show "edge (gmdart_map r) x\<in>darts (gmdart_map r)" by (rule iffD2[OF G.E.closed x])
  next
    fix x assume x: "x\<in>darts (gmdart_map r)"
    show "order (edge (gmdart_map r)) x=2" by (rule G.plain_order[OF gmdart_plain x])
  qed
  show ?thesis using eq by simp
qed

end
