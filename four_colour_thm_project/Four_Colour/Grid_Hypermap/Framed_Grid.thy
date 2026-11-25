(* The finite framed grid hypermap from gridmap.v.
   Original G. Gonthier et al., CeCILL-B. Isabelle/HOL port: Codex. *)
theory Framed_Grid
  imports Grid_Rotations Four_Colour_Base.Geometry
begin

definition gmnode :: "grect \<Rightarrow> gpoint \<Rightarrow> gpoint" where
  "gmnode r = inv (gmface r \<circ> gmedge r)"

lemma gmnode_permutes: "gmnode r permutes gmgrid r"
  unfolding gmnode_def
  by (rule permutes_inv, rule permutes_compose[OF gmedge_permutes gmface_permutes])

lemma gmnode_cancel: "gmnode r (gmface r (gmedge r d))=d"
proof -
  have perm: "(gmface r \<circ> gmedge r) permutes gmgrid r"
    by (rule permutes_compose[OF gmedge_permutes gmface_permutes])
  have inj: "inj (gmface r \<circ> gmedge r)" by (rule permutes_inj[OF perm])
  have "gmnode r (gmface r (gmedge r d)) = inv (gmface r \<circ> gmedge r) ((gmface r \<circ> gmedge r) d)"
    by (simp only: gmnode_def o_apply)
  also have "\<dots> = d" by (rule inv_f_f[OF inj])
  finally show ?thesis .
qed

definition gmdart_map :: "grect \<Rightarrow> gpoint hypermap" where
  "gmdart_map r = \<lparr>darts=gmgrid r, edge=gmedge r, node=gmnode r, face=gmface r\<rparr>"

lemma gmdart_map_simps [simp]:
  "darts (gmdart_map r)=gmgrid r" "edge (gmdart_map r)=gmedge r"
  "node (gmdart_map r)=gmnode r" "face (gmdart_map r)=gmface r"
  by (simp_all add: gmdart_map_def)

lemma hypermap_gmdart_map: "hypermap (gmdart_map r)"
proof unfold_locales
  show "finite (darts (gmdart_map r))" by simp
  show "edge (gmdart_map r) permutes darts (gmdart_map r)" by (simp add: gmedge_permutes)
  show "node (gmdart_map r) permutes darts (gmdart_map r)" by (simp add: gmnode_permutes)
  show "face (gmdart_map r) permutes darts (gmdart_map r)" by (simp add: gmface_permutes)
  fix d
  show "node (gmdart_map r) (face (gmdart_map r) (edge (gmdart_map r) d))=d"
    by (simp add: gmnode_cancel)
qed

lemma gmdart_plain: "plain (gmdart_map r)"
proof -
  interpret G: hypermap "gmdart_map r" by (rule hypermap_gmdart_map)
  show ?thesis unfolding plain_def by (subst G.plainP) (auto dest: gmedge_no_fixed)
qed

lemma gmdart_face_end0:
  assumes "x\<in>darts (gmdart_map r)" "y\<in>darts (gmdart_map r)"
  shows "fconnect (face (gmdart_map r)) x y \<longleftrightarrow> end0g x=end0g y"
  using assms gmface_fconnect_end0[of x r y] by simp

lemma gmnode_inner:
  assumes inner: "halfg d\<in>grect_set r"
  shows "gmnode r d=gedge (gnode d)"
proof -
  have dD: "d\<in>gmgrid r" using inner by (simp only: gmgrid_iff; blast)
  have half: "halfg (gedge (gnode d))=halfg d" using gnodeK[of d] by (metis halfg_face)
  have ndD: "gnode d\<in>gmgrid r" using inner by (simp only: gmgrid_iff half; blast)
  have next_eq: "gmnext r d=gnode d" by (rule gmnext_apply[OF dD ndD])
  have inv: "inv (gmnext r) (gmnext r d)=d" by (rule inv_f_f[OF permutes_inj[OF gmnext_permutes]])
  have face: "gmface r (gnode d)=d" using inv by (simp only: gmface_def next_eq)
  have "gmnode r d=gmedge r (gnode d)"
    using gmnode_cancel[of r "gmedge r (gnode d)"] by (simp only: gmedge2 face)
  also have "\<dots>=gedge (gnode d)" using ndD by (simp add: gmedge_def)
  finally show ?thesis .
qed

lemma gmnode_inner_halfg:
  assumes "halfg d\<in>grect_set r"
  shows "halfg (gmnode r d)=halfg d"
  using gmnode_inner[OF assms] gnodeK[of d] by (metis halfg_face)

end
