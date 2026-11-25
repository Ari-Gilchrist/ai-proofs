(* Euler planarity of the framed grid, following gridmap.v.
   Original G. Gonthier et al., CeCILL-B. Isabelle/HOL port: Codex. *)
theory Grid_Planarity
  imports Grid_Connectivity
begin

lemma gm_outer_nonempty:
  assumes proper: "gr_proper r"
  shows "\<exists>q\<in>gmgrid r. q\<notin>gm_inner r"
proof -
  obtain a b c d where rect: "r=Grect a b c d" by (cases r) auto
  let ?p = "doubleg (a,c)"
  let ?q = "gedge ?p"
  have origin: "(a,c)\<in>grect_set r" using gm_origin_inner[OF proper] by (simp add: rect)
  have pin: "?p\<in>gmgrid r" using origin by (simp add: gmgrid_iff)
  have qin: "?q\<in>gmgrid r" using pin by simp
  have half: "halfg ?q=(a,c-1)" by (simp add: arcg_def ccw_def)
  have outside: "?q\<notin>gm_inner r" by (simp only: gm_inner_iff half; simp add: rect)
  show ?thesis by (rule bexI[where x="?q"]) (use qin outside in auto)
qed

lemma gm_outer_node_class:
  assumes outside: "q\<notin>gm_inner r"
  shows "cyc (gmnode r) q\<notin>cyc (gmnode r) ` gm_inner r"
proof
  assume "cyc (gmnode r) q\<in>cyc (gmnode r) ` gm_inner r"
  then obtain p where p: "p\<in>gm_inner r" "cyc (gmnode r) q=cyc (gmnode r) p" by blast
  interpret N: fperm "gmnode r" "gmgrid r"
    by unfold_locales (rule gmnode_permutes, rule finite_gmgrid)
  have eq: "cyc (gmnode r) p=cyc (gmnode r) q" by (rule sym[OF p(2)])
  have con: "fconnect (gmnode r) p q" by (rule iffD1[OF N.cyc_eq_iff eq])
  have inner: "halfg p\<in>grect_set r" using p(1) by simp
  have "halfg p=halfg q" using con by (simp only: gmnode_fconnect_halfg[OF inner])
  then have "q\<in>gm_inner r" using p(1) by simp
  then show False using outside by contradiction
qed

lemma fcard_gmnode_lower:
  assumes proper: "gr_proper r"
  shows "garea r+1 \<le> fcard (gmnode r) (gmgrid r)"
proof -
  obtain q where q: "q\<in>gmgrid r" "q\<notin>gm_inner r" using gm_outer_nonempty[OF proper] by blast
  let ?A = "cyc (gmnode r) ` gm_inner r"
  let ?B = "cyc (gmnode r) ` gmgrid r"
  let ?C = "cyc (gmnode r) q"
  have outside: "?C\<notin>?A" by (rule gm_outer_node_class[OF q(2)])
  have sub: "insert ?C ?A \<subseteq> ?B" using gm_inner_subset[of r] q(1) by blast
  have finite: "finite ?B" by simp
  have mono: "card (insert ?C ?A) \<le> card ?B" by (rule card_mono[OF finite sub])
  have inner: "card ?A=garea r" using fcard_gmnode_inner[of r] by (simp only: fcard_def)
  have card: "card (insert ?C ?A)=garea r+1" using outside inner by simp
  show ?thesis using mono by (simp only: card fcard_def)
qed

theorem planar_gmdart_map:
  assumes proper: "gr_proper r"
  shows "planar (gmdart_map r)"
proof -
  have component: "n_comp (glink (gmdart_map r)) (gmgrid r)=1"
    using connected_gmdart_map[OF proper] by (simp add: connected_def)
  have nodebound: "gwidth r * gheight r+1 \<le> fcard (gmnode r) (gmgrid r)"
    using fcard_gmnode_lower[OF proper] by (simp only: garea_def)
  have euler: "Euler_lhs (gmdart_map r) \<le> Euler_rhs (gmdart_map r)"
    using nodebound
    by (simp add: Euler_lhs_def Euler_rhs_def component card_gmgrid[OF proper]
        fcard_gmedge[OF proper] fcard_gmface[OF proper] algebra_simps; linarith)
  have zero: "Euler_lhs (gmdart_map r) - Euler_rhs (gmdart_map r)=0" using euler by arith
  show ?thesis by (simp add: planar_def genus_def zero)
qed

end
