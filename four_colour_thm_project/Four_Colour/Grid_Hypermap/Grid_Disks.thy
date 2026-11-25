(* Disjoint interiors of matte contours in the framed grid, from gridmap.v.
   Original G. Gonthier et al., CeCILL-B. Isabelle/HOL port: Codex. *)
theory Grid_Disks
  imports Grid_Rings Four_Colour_Maps.Snip
begin

lemma (in snip_ring) diskN_subset_invariant:
  assumes ring: "set r\<subseteq>A"
    and nodes: "\<And>x. x\<in>A \<Longrightarrow> node G x\<in>A"
    and faces: "\<And>x. x\<in>A \<Longrightarrow> x\<notin>set r \<Longrightarrow> face G x\<in>A"
  shows "diskN\<subseteq>A"
proof (rule subsetI)
  fix x assume x: "x\<in>diskN"
  obtain y where y: "y\<in>set r" and walk: "connect dlink (inv (node G) y) x"
    using x by (auto simp: diskN_def dconnect_def)
  have yA: "y\<in>A" using ring y by blast
  have seed: "inv (node G) y\<in>A" by (rule N.closed_inv[OF nodes yA])
  show "x\<in>A" using walk
  proof (induction rule: rtranclp_induct)
    case base show ?case by (rule seed)
  next
    case (step u v)
    have outside: "u\<notin>set r" and link: "clink G u v"
      using step.hyps(2) by (auto simp only: dlink_def)
    show ?case
    proof (cases "u=node G v")
      case True
      have "inv (node G) u\<in>A" by (rule N.closed_inv[OF nodes step.IH])
      then show ?thesis using True by simp
    next
      case False
      have "v=face G u" using link False by (simp add: clink_def)
      then show ?thesis using faces[OF step.IH outside] by simp
    qed
  qed
qed

lemma gmnode_inv_inner_halfg:
  assumes inner: "halfg x\<in>grect_set r"
  shows "halfg (inv (gmnode r) x)=halfg x"
proof -
  interpret G: hypermap "gmdart_map r" by (rule hypermap_gmdart_map)
  have con: "fconnect (gmnode r) x (inv (gmnode r) x)"
    using G.N.fconnect_inv_right[of x x] by simp
  have "halfg x=halfg (inv (gmnode r) x)"
    by (rule iffD1[OF gmnode_fconnect_halfg[OF inner, of "inv (gmnode r) x"] con])
  then show ?thesis by simp
qed

lemma matte_grid_dlink_closed:
  assumes valid: "valid_matte m" and sub: "set (mdisk m)\<subseteq>grect_set r"
    and cell: "halfg x\<in>set (mdisk m)" and outside: "x\<notin>set (mring m)"
    and step: "clink (gmdart_map r) x y"
  shows "halfg y\<in>set (mdisk m)"
proof -
  interpret G: hypermap "gmdart_map r" by (rule hypermap_gmdart_map)
  have inner: "halfg x\<in>grect_set r" using cell sub by blast
  have xD: "x\<in>gmgrid r" using inner by (simp only: gmgrid_iff; blast)
  show ?thesis
  proof (cases "x=gmnode r y")
    case True
    have inverse: "y=inv (gmnode r) x" using True G.N.inv_f[of y] by simp
    show ?thesis using cell gmnode_inv_inner_halfg[OF inner] by (simp only: inverse)
  next
    case False
    have face: "y=gmface r x" using step False by (simp add: clink_def)
    have other: "halfg (gedge x)\<in>set (mdisk m)"
      using outside cell by (simp only: in_mring[OF valid] gborder_def mem_Collect_eq; blast)
    have other_inner: "halfg (gedge x)\<in>grect_set r" using other sub by blast
    have cancel: "gmnode r (gmface r x)=gedge x"
      using G.edgeK[of "gedge x"] xD by (simp add: gmedge_def)
    have inverse: "gmface r x=inv (gmnode r) (gedge x)"
      using G.N.inv_f[of "gmface r x"] cancel by simp
    show ?thesis using other gmnode_inv_inner_halfg[OF other_inner]
      by (simp only: face inverse)
  qed
qed

theorem gm_disk_def:
  assumes proper: "gr_proper r" and valid: "valid_matte m"
    and sub: "set (mdisk m)\<subseteq>grect_set r"
  shows "snip_ring.diskN (gmdart_map r) (mring m) \<subseteq> halfg -` set (mdisk m)"
proof -
  interpret G: hypermap "gmdart_map r" by (rule hypermap_gmdart_map)
  interpret S: snip_ring "gmdart_map r" "mring m"
    by unfold_locales (rule planar_gmdart_map[OF proper],
      rule gmring_scycle[OF valid sub], use matte_ring_in_gmgrid[OF valid sub] in simp)
  show ?thesis
  proof (rule subsetI)
    fix x assume x: "x\<in>S.diskN"
    obtain z where z: "z\<in>set (mring m)"
      and walk: "connect S.dlink (inv (gmnode r) z) x"
      using x by (auto simp: S.diskN_def S.dconnect_def)
    have cell: "halfg z\<in>set (mdisk m)"
      using z by (simp only: in_mring[OF valid] gborder_def mem_Collect_eq; blast)
    have inner: "halfg z\<in>grect_set r" using cell sub by blast
    have seed: "halfg (inv (gmnode r) z)\<in>set (mdisk m)"
      using cell by (simp only: gmnode_inv_inner_halfg[OF inner])
    have "halfg x\<in>set (mdisk m)" using walk
    proof (induction rule: rtranclp_induct)
      case base show ?case by (rule seed)
    next
      case (step y w)
      have outside: "y\<notin>set (mring m)" and link: "clink (gmdart_map r) y w"
        using step.hyps(2) by (auto simp only: S.dlink_def)
      show ?case by (rule matte_grid_dlink_closed[OF valid sub step.IH outside link])
    qed
    then show "x\<in>halfg -` set (mdisk m)" by simp
  qed
qed

corollary disjoint_gmdisk:
  assumes proper: "gr_proper r" and cm: "grid_cm_proper k cm"
    and sub: "\<And>i. i<k \<Longrightarrow> set (mdisk (cm i))\<subseteq>grect_set r"
    and i: "i<k" and j: "j<k" and ne: "i\<noteq>j"
  shows "snip_ring.diskN (gmdart_map r) (mring (cm i)) \<inter>
    snip_ring.diskN (gmdart_map r) (mring (cm j)) = {}"
proof -
  have vi: "valid_matte (cm i)" and vj: "valid_matte (cm j)"
    and disjoint: "set (mdisk (cm i)) \<inter> set (mdisk (cm j)) = {}"
    using cm i j ne unfolding grid_cm_proper_def by blast+
  have left: "snip_ring.diskN (gmdart_map r) (mring (cm i)) \<subseteq> halfg -` set (mdisk (cm i))"
    by (rule gm_disk_def[OF proper vi sub[OF i]])
  have right: "snip_ring.diskN (gmdart_map r) (mring (cm j)) \<subseteq> halfg -` set (mdisk (cm j))"
    by (rule gm_disk_def[OF proper vj sub[OF j]])
  show ?thesis using left right disjoint by blast
qed

end
