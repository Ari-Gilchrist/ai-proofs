(* Successive removal of matte interiors, following gridmap.v.
   Original G. Gonthier et al., CeCILL-B. Isabelle/HOL port: Codex. *)
theory Grid_Cutout
  imports Grid_Disks
begin

locale grid_mattes =
  fixes r :: grect and k :: nat and cm :: "nat\<Rightarrow>matte"
  assumes proper: "gr_proper r"
    and cm: "grid_cm_proper k cm"
    and bounded: "\<And>i. i<k \<Longrightarrow> set (mdisk (cm i))\<subseteq>grect_set r"
begin

abbreviation contour where "contour i \<equiv> mring (cm i)"
abbreviation pixels where "pixels i \<equiv> set (mdisk (cm i))"

lemma valid: "i<k \<Longrightarrow> valid_matte (cm i)"
  using cm unfolding grid_cm_proper_def by blast

lemma apart: "i<k \<Longrightarrow> j<k \<Longrightarrow> i\<noteq>j \<Longrightarrow> pixels i \<inter> pixels j = {}"
  using cm unfolding grid_cm_proper_def by blast

lemma contour_pixel: "i<k \<Longrightarrow> x\<in>set (contour i) \<Longrightarrow> halfg x\<in>pixels i"
  by (simp only: in_mring[OF valid] gborder_def mem_Collect_eq; blast)

lemma contours_apart:
  "i<k \<Longrightarrow> j<k \<Longrightarrow> i\<noteq>j \<Longrightarrow> set (contour i) \<inter> set (contour j) = {}"
  using contour_pixel apart by blast

definition cutout :: "nat set \<Rightarrow> gpoint hypermap \<Rightarrow> bool" where
  "cutout E G \<longleftrightarrow> E\<subseteq>{..<k} \<and> hypermap G \<and> planar G \<and>
    darts G\<subseteq>gmgrid r \<and> (\<forall>i<k. set (contour i)\<subseteq>darts G) \<and>
    (\<forall>x\<in>darts G. edge G x=gedge x) \<and>
    (\<forall>x\<in>darts G. \<forall>y\<in>darts G.
      (fconnect (face G) x y \<longleftrightarrow> end0g x=end0g y)) \<and>
    (\<forall>x\<in>darts G. (\<forall>i\<in>E. x\<notin>set (contour i)) \<longrightarrow> node G x=gmnode r x) \<and>
    (\<forall>i\<in>E. ucycle (frel (node G)) (rev (contour i)))"

lemma cutout_empty: "cutout {} (gmdart_map r)"
  unfolding cutout_def
  using hypermap_gmdart_map planar_gmdart_map[OF proper]
    matte_ring_in_gmgrid[OF valid bounded] gmdart_face_end0
  by (auto simp: gmedge_def)

lemma cutout_scycle:
  assumes cut: "cutout E G" and i: "i<k"
  shows "scycle G (rlink G) (contour i)"
proof -
  interpret H: hypermap G using cut by (simp add: cutout_def)
  have ringD: "set (contour i)\<subseteq>darts G" using cut i by (simp only: cutout_def; blast)
  have endpoints: "fconnect (face G) a b \<longleftrightarrow> end0g a=end0g b"
    if "a\<in>darts G" "b\<in>darts G" for a b
    using cut that by (simp only: cutout_def; blast)
  have edge: "edge G a=gedge a" if "a\<in>darts G" for a
    using cut that by (simp only: cutout_def; blast)
  have rel: "rlink G a b=mrlink a b"
    if a: "a\<in>set (contour i)" and b: "b\<in>set (contour i)" for a b
  proof -
    have aD: "a\<in>darts G" and bD: "b\<in>darts G" using ringD a b by blast+
    have eD: "edge G a\<in>darts G" using aD by simp
    show ?thesis using endpoints[OF eD bD]
      by (simp add: rlink_def mrlink_def edge[OF aD] end0g_edge)
  qed
  have eq: "cycle (rlink G) (contour i) = cycle mrlink (contour i)"
    by (rule cycle_cong_on) (rule rel; assumption)
  have cyc: "cycle (rlink G) (contour i)"
    using eq mring_cycle[OF valid[OF i]] by (simp only: grid_cycle_cycle; blast)
  have injend: "inj_on end0g (set (contour i))"
    using mring_simple[OF valid[OF i]] by (simp add: distinct_map)
  have injcyc: "inj_on (cyc (face G)) (set (contour i))"
  proof (rule inj_onI)
    fix a b assume a: "a\<in>set (contour i)" and b: "b\<in>set (contour i)"
      and eq: "cyc (face G) a=cyc (face G) b"
    have aD: "a\<in>darts G" and bD: "b\<in>darts G" using ringD a b by blast+
    have "fconnect (face G) a b" by (rule iffD1[OF H.F.cyc_eq_iff eq])
    then have "end0g a=end0g b" using endpoints[OF aD bD] by blast
    then show "a=b" by (rule inj_onD[OF injend _ a b])
  qed
  have "simple G (contour i)" using injcyc mring_uniq[OF valid[OF i]]
    by (simp add: simple_def distinct_map)
  then show ?thesis using cyc by (simp add: scycle_def)
qed

lemma cutout_disk_subset:
  assumes cut: "cutout E G" and j: "j<k" and fresh: "j\<notin>E"
  shows "snip_ring.diskN G (contour j)\<subseteq>halfg -` pixels j"
proof -
  interpret H: hypermap G using cut by (simp add: cutout_def)
  have planar: "planar G" and ringD: "set (contour j)\<subseteq>darts G"
    using cut j by (simp only: cutout_def; blast)+
  interpret S: snip_ring G "contour j"
    by unfold_locales (rule planar, rule cutout_scycle[OF cut j], rule ringD)
  let ?A = "darts G \<inter> halfg -` pixels j"
  have edge: "edge G x=gedge x" if "x\<in>darts G" for x
    using cut that by (simp only: cutout_def; blast)
  have nodes: "node G x\<in>?A" if x: "x\<in>?A" for x
  proof -
    have xD: "x\<in>darts G" and px: "halfg x\<in>pixels j" using x by auto
    have outside: "x\<notin>set (contour i)" if ei: "i\<in>E" for i
    proof -
      have i: "i<k" and ne: "i\<noteq>j" using cut ei fresh by (auto simp: cutout_def)
      show ?thesis using apart[OF i j ne] contour_pixel[OF i] px by blast
    qed
    have node: "node G x=gmnode r x" using cut xD outside by (simp only: cutout_def; blast)
    have inner: "halfg x\<in>grect_set r" using bounded[OF j] px by blast
    have half: "halfg (node G x)=halfg x" by (simp only: node gmnode_inner_halfg[OF inner])
    show ?thesis using xD px half by auto
  qed
  have faces: "face G x\<in>?A" if x: "x\<in>?A" and nr: "x\<notin>set (contour j)" for x
  proof -
    have xD: "x\<in>darts G" and px: "halfg x\<in>pixels j" using x by auto
    have other: "halfg (gedge x)\<in>pixels j"
      using nr px by (simp only: in_mring[OF valid[OF j]] gborder_def mem_Collect_eq; blast)
    have eD: "edge G x\<in>darts G" using xD by simp
    have ep: "halfg (edge G x)\<in>pixels j" using other by (simp only: edge[OF xD])
    have eA: "edge G x\<in>?A" using eD ep by simp
    have inv: "inv (node G) (edge G x)\<in>?A" by (rule H.N.closed_inv[OF nodes eA])
    have ee: "edge G (edge G x)=x"
      by (metis edge[OF eD] edge[OF xD] gedge2[of x])
    have cancel: "node G (face G x)=edge G x" using H.edgeK[of "edge G x"] ee by simp
    have eq: "inv (node G) (edge G x)=face G x" using H.N.inv_f[of "face G x"] cancel by simp
    show ?thesis using inv by (simp only: eq)
  qed
  have ring: "set (contour j)\<subseteq>?A" using ringD contour_pixel[OF j] by auto
  have "S.diskN\<subseteq>?A" by (rule S.diskN_subset_invariant[OF ring nodes faces])
  then show ?thesis by blast
qed

lemma cutout_insert:
  assumes cut: "cutout E G" and j: "j<k" and fresh: "j\<notin>E"
  shows "cutout (insert j E) (snip_ring.snipr G (contour j))"
proof -
  interpret H: hypermap G using cut by (simp add: cutout_def)
  have planar: "planar G" and ringD: "set (contour j)\<subseteq>darts G"
    using cut j by (simp only: cutout_def; blast)+
  interpret S: snip_ring G "contour j"
    by unfold_locales (rule planar, rule cutout_scycle[OF cut j], rule ringD)
  interpret P: patch G S.snipd S.snipr id id "contour j" "rev (contour j)"
    by (rule S.snip_patch)
  let ?G = "S.snipr"
  have disk: "S.diskN\<subseteq>halfg -` pixels j"
    by (rule cutout_disk_subset[OF cut j fresh])
  have contours: "set (contour i)\<subseteq>darts ?G" if i: "i<k" for i
  proof (rule subsetI)
    fix x assume x: "x\<in>set (contour i)"
    have xD: "x\<in>darts G" using cut i x by (simp only: cutout_def; blast)
    have keep: "x\<notin>S.diskE"
    proof (cases "i=j")
      case True then show ?thesis using S.r_diskE x by simp
    next
      case False
      have px: "halfg x\<in>pixels i" by (rule contour_pixel[OF i x])
      have "x\<notin>S.diskN" using apart[OF i j False] disk px by blast
      then show ?thesis by (simp add: S.diskE_def)
    qed
    show "x\<in>darts ?G" using xD keep by simp
  qed
  have carrier: "darts ?G\<subseteq>darts G" by auto
  have edges: "edge ?G x=gedge x" if x: "x\<in>darts ?G" for x
  proof -
    have xD: "x\<in>darts G" using carrier x by blast
    have old: "edge G x=gedge x" using cut xD by (simp only: cutout_def; blast)
    show ?thesis using P.edge_r[OF x] by (simp add: old)
  qed
  have faces: "fconnect (face ?G) x y \<longleftrightarrow> end0g x=end0g y"
    if x: "x\<in>darts ?G" and y: "y\<in>darts ?G" for x y
  proof -
    have xD: "x\<in>darts G" and yD: "y\<in>darts G" using carrier x y by blast+
    have old: "fconnect (face G) x y \<longleftrightarrow> end0g x=end0g y"
      using cut xD yD by (simp only: cutout_def; blast)
    show ?thesis using P.patch_face_r[OF x y] by (simp add: old)
  qed
  have nodes: "node ?G x=gmnode r x"
    if x: "x\<in>darts ?G" and outside: "\<forall>i\<in>insert j E. x\<notin>set (contour i)" for x
  proof -
    have xD: "x\<in>darts G" using carrier x by blast
    have old: "node G x=gmnode r x" using cut xD outside by (simp only: cutout_def; blast)
    have nr: "x\<notin>set (rev (contour j))" using outside by simp
    show ?thesis using P.node_r[OF x nr] by (simp add: old)
  qed
  have cycles: "ucycle (frel (node ?G)) (rev (contour i))" if ei: "i\<in>insert j E" for i
  proof (cases "i=j")
    case True
    then show ?thesis using P.cycle_r P.distinct_r by (simp add: ucycle_def)
  next
    case False
    have iE: "i\<in>E" using ei False by simp
    have i: "i<k" using cut iE by (auto simp: cutout_def)
    have old: "ucycle (frel (node G)) (rev (contour i))"
      using cut iE by (simp only: cutout_def; blast)
    have node_eq: "node ?G x=node G x" if x: "x\<in>set (rev (contour i))" for x
    proof -
      have xD: "x\<in>darts ?G" using contours[OF i] x by auto
      have nr: "x\<notin>set (rev (contour j))" using contours_apart[OF i j False] x by auto
      show ?thesis using P.node_r[OF xD nr] by simp
    qed
    have rel: "frel (node ?G) a b=frel (node G) a b"
      if "a\<in>set (rev (contour i))" "b\<in>set (rev (contour i))" for a b
      by (simp only: node_eq[OF that(1)])
    have eq: "cycle (frel (node ?G)) (rev (contour i)) =
        cycle (frel (node G)) (rev (contour i))"
      by (rule cycle_cong_on) (rule rel; assumption)
    show ?thesis using old by (simp only: ucycle_def eq)
  qed
  have sub: "darts ?G\<subseteq>gmgrid r" using cut carrier by (simp only: cutout_def; blast)
  show ?thesis unfolding cutout_def
    using cut j S.hypermap_snipr S.planar_snipr sub contours edges faces nodes cycles
    by (simp only: cutout_def; blast)
qed

theorem has_cutout:
  "\<exists>G. cutout {..<k} G"
proof -
  have construct: "\<exists>G. cutout E G" if "finite E" "E\<subseteq>{..<k}" for E
    using that
  proof (induction E rule: finite_induct)
    case empty show ?case using cutout_empty by blast
  next
    case (insert j E)
    have sub: "E\<subseteq>{..<k}" and j: "j<k" using insert.prems by auto
    obtain G where cut: "cutout E G" using insert.IH[OF sub] by blast
    show ?case using cutout_insert[OF cut j insert.hyps(2)] by blast
  qed
  show ?thesis by (rule construct[OF finite_lessThan subset_refl])
qed

lemma cutout_loopless:
  assumes cut: "cutout {..<k} G"
  shows "loopless G"
proof -
  interpret H: hypermap G using cut by (simp add: cutout_def)
  have edge: "edge G x=gedge x" if "x\<in>darts G" for x
    using cut that by (simp only: cutout_def; blast)
  have cycles: "cycle (frel (node G)) (rev (contour i))" "distinct (rev (contour i))"
    if "i<k" for i
    using cut that by (simp only: cutout_def ucycle_def; blast)+
  have no_inner: "\<not>fconnect (node G) x (edge G x)"
    if xD: "x\<in>darts G" and inner: "halfg x\<in>grect_set r" for x
  proof
    assume connection: "fconnect (node G) x (edge G x)"
    show False
    proof (cases "\<exists>i<k. x\<in>set (contour i)")
      case True
      then obtain i where i: "i<k" and xi: "x\<in>set (contour i)" by blast
      have xr: "x\<in>set (rev (contour i))" using xi by simp
      have er: "edge G x\<in>set (rev (contour i))"
        using H.N.fcycle_fconnect[OF cycles[OF i] xr, of "edge G x"] connection by blast
      have "gedge x\<in>set (contour i)" using er by (simp add: edge[OF xD])
      then show False using mring_edge[OF valid[OF i] xi] by contradiction
    next
      case False
      have outside: "\<forall>i<k. x\<notin>set (contour i)" using False by blast
      have orbit: "halfg y=halfg x \<and> y\<in>darts G \<and> (\<forall>i<k. y\<notin>set (contour i))"
        if con: "fconnect (node G) x y" for y
        using con
      proof (induction rule: fconnect_induct)
        case refl then show ?case using xD outside by blast
      next
        case (step z)
        have zD: "z\<in>darts G" and half: "halfg z=halfg x"
          and off: "\<forall>i<k. z\<notin>set (contour i)" using step.IH by blast+
        have node: "node G z=gmnode r z" using cut zD off by (simp only: cutout_def; blast)
        have zin: "halfg z\<in>grect_set r" using half inner by simp
        have next_half: "halfg (node G z)=halfg x" by (simp only: node gmnode_inner_halfg[OF zin] half)
        have next_off: "node G z\<notin>set (contour i)" if i: "i<k" for i
        proof
          assume successor: "node G z\<in>set (contour i)"
          have nr: "node G z\<in>set (rev (contour i))" using successor by simp
          have reverse_con: "fconnect (node G) (node G z) z" by simp
          have "z\<in>set (rev (contour i))"
            using H.N.fcycle_fconnect[OF cycles[OF i] nr, of z] reverse_con by blast
          then show False using off i by simp
        qed
        show ?case using next_half zD next_off by auto
      qed
      have "halfg (edge G x)=halfg x" using orbit[OF connection] by blast
      then show False using neq_halfg_edge[of x] by (simp add: edge[OF xD])
    qed
  qed
  show ?thesis unfolding loopless_def
  proof (intro ballI)
    fix x assume xD: "x\<in>darts G"
    have grid: "x\<in>gmgrid r" using cut xD by (simp only: cutout_def; blast)
    show "\<not>fconnect (node G) x (edge G x)"
    proof (cases "halfg x\<in>grect_set r")
      case True show ?thesis by (rule no_inner[OF xD True])
    next
      case False
      have inner: "halfg (edge G x)\<in>grect_set r"
        using grid False by (simp only: edge[OF xD] gmgrid_iff; blast)
      have eD: "edge G x\<in>darts G" using xD by simp
      have ee: "edge G (edge G x)=x"
        by (metis edge[OF eD] edge[OF xD] gedge2[of x])
      have no: "\<not>fconnect (node G) (edge G x) x"
        using no_inner[OF eD inner] by (simp only: ee; blast)
      show ?thesis
      proof
        assume con: "fconnect (node G) x (edge G x)"
        have "fconnect (node G) (edge G x) x" by (rule H.N.fconnect_sym[OF con])
        then show False using no by contradiction
      qed
    qed
  qed
qed

theorem planar_loopless_cutout:
  "\<exists>G. cutout {..<k} G \<and> hypermap G \<and> planar G \<and> loopless G"
  using has_cutout cutout_loopless unfolding cutout_def by blast

end

end
