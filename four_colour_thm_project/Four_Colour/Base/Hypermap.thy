(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Hypermap.thy
    Finite hypermaps: three mutually inverse permutations of a finite set of
    darts.  Ported from G. Gonthier's Coq development (hypermap.v).
*)
theory Hypermap
  imports FC_Fingraph
begin

section \<open>Hypermaps\<close>

text \<open>
  A hypermap consists of a finite set of darts with three permutations
  @{text edge}, @{text node}, @{text face} whose composite is the identity:
  @{text "node (face (edge x)) = x"}.  Unlike Gonthier, who uses a finite
  type of darts, we use an explicit carrier set; the permutations are
  required to be the identity outside it.  This lets derived hypermaps
  (Walkup transforms, patches, \ldots) share the dart type of the original.
\<close>

record 'a hypermap =
  darts :: "'a set"
  edge :: "'a \<Rightarrow> 'a"
  node :: "'a \<Rightarrow> 'a"
  face :: "'a \<Rightarrow> 'a"

locale hypermap =
  fixes G :: "'a hypermap"
  assumes finite_darts: "finite (darts G)"
    and edge_perm: "edge G permutes darts G"
    and node_perm: "node G permutes darts G"
    and face_perm: "face G permutes darts G"
    and edgeK: "node G (face G (edge G x)) = x"
begin

abbreviation D where "D \<equiv> darts G"
abbreviation e where "e \<equiv> edge G"
abbreviation n where "n \<equiv> node G"
abbreviation f where "f \<equiv> face G"

sublocale E: fperm e D using edge_perm finite_darts by unfold_locales
sublocale N: fperm n D using node_perm finite_darts by unfold_locales
sublocale F: fperm f D using face_perm finite_darts by unfold_locales

lemma faceK: "e (n (f x)) = x"
  by (metis E.f_inv edgeK)

lemma nodeK: "f (e (n x)) = x"
  by (metis F.f_inv faceK)

lemmas cancel3 = edgeK faceK nodeK

lemma inv_edge: "inv e = n \<circ> f"
  by (rule inv_unique_comp) (auto simp: fun_eq_iff edgeK faceK)

lemma inv_face: "inv f = e \<circ> n"
  by (rule inv_unique_comp) (auto simp: fun_eq_iff nodeK faceK)

lemma inv_node: "inv n = f \<circ> e"
  by (rule inv_unique_comp) (auto simp: fun_eq_iff nodeK edgeK)

lemma inv_edge_apply: "inv e x = n (f x)"
  by (simp add: inv_edge)

lemma inv_face_apply: "inv f x = e (n x)"
  by (simp add: inv_face)

lemma inv_node_apply: "inv n x = f (e x)"
  by (simp add: inv_node)

lemma edge_eq_iff: "e x = y \<longleftrightarrow> x = n (f y)"
  by (metis edgeK faceK)

lemma face_eq_iff: "f x = y \<longleftrightarrow> x = e (n y)"
  by (metis faceK nodeK)

lemma node_eq_iff: "n x = y \<longleftrightarrow> x = f (e y)"
  by (metis edgeK nodeK)

abbreviation cedge where "cedge \<equiv> fconnect e"
abbreviation cnode where "cnode \<equiv> fconnect n"
abbreviation cface where "cface \<equiv> fconnect f"

end

section \<open>Components\<close>

definition glink :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "glink G x y \<longleftrightarrow> edge G x = y \<or> node G x = y \<or> face G x = y"

abbreviation gcomp :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "gcomp G \<equiv> connect (glink G)"

definition clink :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "clink G x y \<longleftrightarrow> x = node G y \<or> face G x = y"

definition connected :: "'a hypermap \<Rightarrow> bool" where
  "connected G \<longleftrightarrow> n_comp (glink G) (darts G) = 1"

section \<open>Genus and planarity\<close>

definition Euler_lhs :: "'a hypermap \<Rightarrow> nat" where
  "Euler_lhs G = 2 * n_comp (glink G) (darts G) + card (darts G)"

definition Euler_rhs :: "'a hypermap \<Rightarrow> nat" where
  "Euler_rhs G = fcard (edge G) (darts G) + fcard (node G) (darts G) + fcard (face G) (darts G)"

definition genus :: "'a hypermap \<Rightarrow> nat" where
  "genus G = (Euler_lhs G - Euler_rhs G) div 2"

definition even_genus :: "'a hypermap \<Rightarrow> bool" where
  "even_genus G \<longleftrightarrow> Euler_lhs G = 2 * genus G + Euler_rhs G"

definition planar :: "'a hypermap \<Rightarrow> bool" where
  "planar G \<longleftrightarrow> genus G = 0"

section \<open>The Jordan property\<close>

text \<open>A Moebius path is a duplicate-free C-path @{text "x # p"} with two
  additional crossing N-links.\<close>

definition Moebius_path :: "'a hypermap \<Rightarrow> 'a list \<Rightarrow> bool" where
  "Moebius_path G q = (case q of [] \<Rightarrow> False | x # p \<Rightarrow>
      distinct q \<and> path (clink G) x p \<and>
      mem2 p (inv (node G) (lastd x p)) (node G x))"

definition Jordan :: "'a hypermap \<Rightarrow> bool" where
  "Jordan G \<longleftrightarrow> (\<forall>q. set q \<subseteq> darts G \<longrightarrow> \<not> Moebius_path G q)"

context hypermap
begin

lemma glinkE [simp]: "glink G x (e x)"
  and glinkN [simp]: "glink G x (n x)"
  and glinkF [simp]: "glink G x (f x)"
  by (simp_all add: glink_def)

lemma fconnect_gcomp:
  assumes "\<And>x. glink G x (g x)" "fconnect g x y"
  shows "gcomp G x y"
  using assms(2)
proof (induction rule: fconnect_induct)
  case refl
  then show ?case by simp
next
  case (step z)
  show ?case by (rule rtranclp.rtrancl_into_rtrancl[OF step(2) assms(1)])
qed

lemma cedge_gcomp: "cedge x y \<Longrightarrow> gcomp G x y"
  using fconnect_gcomp[of e x y] by simp

lemma cnode_gcomp: "cnode x y \<Longrightarrow> gcomp G x y"
  using fconnect_gcomp[of n x y] by simp

lemma cface_gcomp: "cface x y \<Longrightarrow> gcomp G x y"
  using fconnect_gcomp[of f x y] by simp

lemma glink_sym: "glink G x y \<Longrightarrow> gcomp G y x"
proof -
  assume "glink G x y"
  then consider "e x = y" | "n x = y" | "f x = y" by (auto simp: glink_def)
  then show ?thesis
  proof cases
    case 1
    then have "cedge y x" using E.fconnect_sym[OF fconnect_step[of e x]] by simp
    then show ?thesis by (rule cedge_gcomp)
  next
    case 2
    then have "cnode y x" using N.fconnect_sym[OF fconnect_step[of n x]] by simp
    then show ?thesis by (rule cnode_gcomp)
  next
    case 3
    then have "cface y x" using F.fconnect_sym[OF fconnect_step[of f x]] by simp
    then show ?thesis by (rule cface_gcomp)
  qed
qed

lemma gcomp_sym: "gcomp G x y \<Longrightarrow> gcomp G y x"
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  have "gcomp G z y" using step(2) by (rule glink_sym)
  then show ?case using step(3) by (rule rtranclp_trans)
qed

lemma comp_eq:
  assumes xy: "gcomp G x y"
  shows "comp_of (glink G) x = comp_of (glink G) y"
proof -
  have yx: "gcomp G y x" by (rule gcomp_sym[OF xy])
  show ?thesis
    by (auto simp: comp_of_def intro: rtranclp_trans[OF yx] rtranclp_trans[OF xy])
qed

lemma gcomp_commute: "gcomp G x y \<longleftrightarrow> gcomp G y x"
  by (blast intro: gcomp_sym)

lemma glink_closed: "glink G x y \<Longrightarrow> x \<in> D \<longleftrightarrow> y \<in> D"
  by (auto simp: glink_def)

lemma gcomp_closed: "gcomp G x y \<Longrightarrow> x \<in> D \<longleftrightarrow> y \<in> D"
  by (induction rule: rtranclp_induct) (auto dest: glink_closed)

lemma gcomp_out: "x \<notin> D \<Longrightarrow> gcomp G x y \<longleftrightarrow> y = x"
proof
  assume xD: "x \<notin> D"
  assume "gcomp G x y"
  then show "y = x"
    by (induction rule: rtranclp_induct) (use xD in \<open>auto simp: glink_def\<close>)
qed simp

lemma clinkN [simp]: "clink G (n x) x"
  and clinkF [simp]: "clink G x (f x)"
  by (simp_all add: clink_def)

lemma clink_iff: "clink G x y \<longleftrightarrow> x = n y \<or> f x = y"
  by (simp add: clink_def)

lemma clink_closed: "clink G x y \<Longrightarrow> x \<in> D \<longleftrightarrow> y \<in> D"
  by (auto simp: clink_def)

lemma clink_gcomp: "clink G x y \<Longrightarrow> gcomp G x y"
proof -
  assume "clink G x y"
  then consider "x = n y" | "f x = y" by (auto simp: clink_def)
  then show ?thesis
  proof cases
    case 1
    then have "glink G y x" by simp
    then show ?thesis by (rule glink_sym)
  next
    case 2
    then have "glink G x y" by (simp add: glink_def)
    then show ?thesis by (rule r_into_rtranclp)
  qed
qed

lemma connect_clink_gcomp: "connect (clink G) x y \<Longrightarrow> gcomp G x y"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp_trans clink_gcomp)

lemma clink_connect_rev: "clink G x y \<Longrightarrow> connect (clink G) y x"
proof -
  assume "clink G x y"
  then consider "x = n y" | "f x = y" by (auto simp: clink_def)
  then show ?thesis
  proof cases
    case 1
    have "fconnect n y x" using 1 by auto
    then have "fconnect (inv n) y x" by (simp add: N.fconnect_inv)
    then show ?thesis
    proof (induction rule: fconnect_induct)
      case refl
      then show ?case by simp
    next
      case (step z)
      have "clink G z (inv n z)" using clinkN[of "inv n z"] by simp
      then show ?case using step(2) by (rule rtranclp.rtrancl_into_rtrancl[rotated])
    qed
  next
    case 2
    have "cface y x" using 2 F.fconnect_sym by blast
    then show ?thesis
    proof (induction rule: fconnect_induct)
      case refl
      then show ?case by simp
    next
      case (step z)
      have "clink G z (f z)" by simp
      then show ?case using step(2) by (rule rtranclp.rtrancl_into_rtrancl[rotated])
    qed
  qed
qed

lemma connect_clink_sym: "connect (clink G) x y \<Longrightarrow> connect (clink G) y x"
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  have "connect (clink G) z y" using step(2) by (rule clink_connect_rev)
  then show ?case using step(3) by (rule rtranclp_trans)
qed

lemma gcomp_connect_clink: "gcomp G x y \<Longrightarrow> connect (clink G) x y"
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  have "connect (clink G) y z"
  proof -
    consider "e y = z" | "n y = z" | "f y = z" using step(2) by (auto simp: glink_def)
    then show ?thesis
    proof cases
      case 1
      have "y = n (f z)" using 1 edgeK[of y] by simp
      then have "clink G y (f z)" by simp
      moreover have "connect (clink G) (f z) z"
        by (rule clink_connect_rev) simp
      ultimately show ?thesis by (rule converse_rtranclp_into_rtranclp)
    next
      case 2
      then have "clink G z y" by (simp add: clink_def)
      then show ?thesis by (rule clink_connect_rev)
    next
      case 3
      then have "clink G y z" by (simp add: clink_def)
      then show ?thesis by (rule r_into_rtranclp)
    qed
  qed
  then show ?case using step(3) by (rule rtranclp_trans[rotated])
qed

lemma clink_glink: "connect (clink G) x y \<longleftrightarrow> gcomp G x y"
  using connect_clink_gcomp gcomp_connect_clink by blast

end

section \<open>Counting components\<close>

lemma n_comp_eq:
  assumes "\<And>x y. x \<in> A \<Longrightarrow> connect r x y \<longleftrightarrow> connect s x y"
  shows "n_comp r A = n_comp s A"
proof -
  have "comp_of r ` A = comp_of s ` A"
    using assms by (auto simp: comp_of_def image_def)
  then show ?thesis by (simp add: n_comp_def)
qed

lemma fcard_eq:
  assumes "\<And>x y. x \<in> A \<Longrightarrow> fconnect g x y \<longleftrightarrow> fconnect h x y"
  shows "fcard g A = fcard h A"
proof -
  have "cyc g ` A = cyc h ` A"
    using assms by (auto simp: cyc_def image_def)
  then show ?thesis by (simp add: fcard_def)
qed

lemma fcard_conj:
  assumes "fperm h D" "bij g" "g ` D = D"
  shows "fcard (g \<circ> h \<circ> inv g) D = fcard h D"
proof -
  have ginv: "g (inv g x) = x" "inv g (g x) = x" for x
    using surj_f_inv_f[OF bij_is_surj[OF assms(2)]] inv_f_f[OF bij_is_inj[OF assms(2)]] by auto
  have pow: "((g \<circ> h \<circ> inv g) ^^ k) x = g ((h ^^ k) (inv g x))" for k x
    by (induction k) (simp_all add: ginv)
  have cyc: "cyc (g \<circ> h \<circ> inv g) (g x) = g ` cyc h x" for x
    unfolding cyc_def fconnect_def pow by (auto simp: ginv image_def)
  have "cyc (g \<circ> h \<circ> inv g) ` D = cyc (g \<circ> h \<circ> inv g) ` (g ` D)"
    using assms(3) by simp
  also have "\<dots> = (\<lambda>x. g ` cyc h x) ` D"
    by (simp add: image_image cyc)
  also have "\<dots> = (\<lambda>C. g ` C) ` (cyc h ` D)"
    by (simp add: image_image)
  finally have "card (cyc (g \<circ> h \<circ> inv g) ` D) = card ((\<lambda>C. g ` C) ` (cyc h ` D))"
    by simp
  also have "\<dots> = card (cyc h ` D)"
  proof (rule card_image)
    show "inj_on ((`) g) (cyc h ` D)"
      using assms(2) by (meson bij_def inj_image_eq_iff inj_onI)
  qed
  finally show ?thesis by (simp add: fcard_def)
qed

section \<open>Derived hypermaps\<close>

definition permN :: "'a hypermap \<Rightarrow> 'a hypermap" where
  "permN G = \<lparr>darts = darts G, edge = node G, node = face G, face = edge G\<rparr>"

definition permF :: "'a hypermap \<Rightarrow> 'a hypermap" where
  "permF G = \<lparr>darts = darts G, edge = face G, node = edge G, face = node G\<rparr>"

definition dual :: "'a hypermap \<Rightarrow> 'a hypermap" where
  "dual G = \<lparr>darts = darts G, edge = inv (edge G), node = inv (face G), face = inv (node G)\<rparr>"

definition mirror :: "'a hypermap \<Rightarrow> 'a hypermap" where
  "mirror G = \<lparr>darts = darts G, edge = face G \<circ> node G, node = inv (node G),
                face = inv (face G)\<rparr>"

lemma permN_simps [simp]:
  "darts (permN G) = darts G" "edge (permN G) = node G" "node (permN G) = face G"
  "face (permN G) = edge G"
  by (simp_all add: permN_def)

lemma permF_simps [simp]:
  "darts (permF G) = darts G" "edge (permF G) = face G" "node (permF G) = edge G"
  "face (permF G) = node G"
  by (simp_all add: permF_def)

lemma dual_simps [simp]:
  "darts (dual G) = darts G" "edge (dual G) = inv (edge G)" "node (dual G) = inv (face G)"
  "face (dual G) = inv (node G)"
  by (simp_all add: dual_def)

lemma mirror_simps [simp]:
  "darts (mirror G) = darts G" "edge (mirror G) = face G \<circ> node G"
  "node (mirror G) = inv (node G)" "face (mirror G) = inv (face G)"
  by (simp_all add: mirror_def)

context hypermap
begin

lemma hypermap_permN: "hypermap (permN G)"
  by unfold_locales (simp_all add: finite_darts node_perm face_perm edge_perm nodeK)

lemma hypermap_permF: "hypermap (permF G)"
  by unfold_locales (simp_all add: finite_darts node_perm face_perm edge_perm faceK)

lemma hypermap_dual: "hypermap (dual G)"
proof unfold_locales
  show "finite (darts (dual G))" using finite_darts by simp
  show "edge (dual G) permutes darts (dual G)" using E.inv_perm by simp
  show "node (dual G) permutes darts (dual G)" using F.inv_perm by simp
  show "face (dual G) permutes darts (dual G)" using N.inv_perm by simp
  fix x
  show "node (dual G) (face (dual G) (edge (dual G) x)) = x"
    by (simp add: inv_edge inv_face inv_node faceK)
qed

lemma hypermap_mirror: "hypermap (mirror G)"
proof unfold_locales
  show "finite (darts (mirror G))" using finite_darts by simp
  show "edge (mirror G) permutes darts (mirror G)"
    using permutes_compose[OF node_perm face_perm] by simp
  show "node (mirror G) permutes darts (mirror G)" using N.inv_perm by simp
  show "face (mirror G) permutes darts (mirror G)" using F.inv_perm by simp
  fix x
  show "node (mirror G) (face (mirror G) (edge (mirror G) x)) = x"
    by simp
qed

lemma glink_permN: "glink (permN G) x y \<longleftrightarrow> glink G x y"
  and glink_permF: "glink (permF G) x y \<longleftrightarrow> glink G x y"
  by (auto simp: glink_def)

lemma n_comp_permN: "n_comp (glink (permN G)) D = n_comp (glink G) D"
  and n_comp_permF: "n_comp (glink (permF G)) D = n_comp (glink G) D"
  by (simp_all add: glink_permN glink_permF[abs_def] glink_permN[abs_def])

lemma genus_permN: "genus (permN G) = genus G"
  and genus_permF: "genus (permF G) = genus G"
  by (simp_all add: genus_def Euler_lhs_def Euler_rhs_def n_comp_permN n_comp_permF
      add.commute add.left_commute)

lemma planar_permN: "planar (permN G) \<longleftrightarrow> planar G"
  and planar_permF: "planar (permF G) \<longleftrightarrow> planar G"
  by (simp_all add: planar_def genus_permN genus_permF)

lemma connected_permN: "connected (permN G) \<longleftrightarrow> connected G"
  and connected_permF: "connected (permF G) \<longleftrightarrow> connected G"
  by (simp_all add: connected_def n_comp_permN n_comp_permF)

lemma clink_dual: "clink (dual G) x y \<longleftrightarrow> clink G x y"
  unfolding clink_def dual_simps
  by (metis F.f_inv F.inv_f N.f_inv N.inv_f)

lemma gcomp_dual: "gcomp (dual G) x y \<longleftrightarrow> gcomp G x y"
proof -
  interpret H: hypermap "dual G" by (rule hypermap_dual)
  have "clink (dual G) = clink G" by (simp add: fun_eq_iff clink_dual)
  then show ?thesis
    using H.clink_glink[of x y] clink_glink[of x y] by simp
qed

lemma genus_dual: "genus (dual G) = genus G"
proof -
  have "n_comp (glink (dual G)) D = n_comp (glink G) D"
    by (rule n_comp_eq) (simp add: gcomp_dual)
  then show ?thesis
    by (simp add: genus_def Euler_lhs_def Euler_rhs_def E.fcard_inv N.fcard_inv F.fcard_inv
        add.commute add.left_commute)
qed

lemma planar_dual: "planar (dual G) \<longleftrightarrow> planar G"
  by (simp add: planar_def genus_dual)

lemma connected_dual: "connected (dual G) \<longleftrightarrow> connected G"
  unfolding connected_def using n_comp_eq[of D "glink (dual G)" "glink G"] gcomp_dual by simp

lemma clink_mirror: "clink (mirror G) x y \<longleftrightarrow> clink G y x"
  unfolding clink_def mirror_simps
  by (metis F.f_inv F.inv_f N.f_inv N.inv_f)

lemma gcomp_mirror: "gcomp (mirror G) x y \<longleftrightarrow> gcomp G x y"
proof -
  interpret H: hypermap "mirror G" by (rule hypermap_mirror)
  have "clink (mirror G) = (clink G)\<inverse>\<inverse>" by (simp add: fun_eq_iff clink_mirror)
  then have "connect (clink (mirror G)) x y \<longleftrightarrow> connect (clink G) y x"
    by (simp add: rtranclp_conversep)
  then show ?thesis
    using H.clink_glink[of x y] clink_glink[of y x] gcomp_commute by simp
qed

lemma fcard_mirror_edge: "fcard (face G \<circ> node G) D = fcard e D"
proof -
  have "f \<circ> n = f \<circ> inv e \<circ> inv f"
    by (simp add: fun_eq_iff inv_edge_apply inv_face_apply nodeK)
  then have "fcard (f \<circ> n) D = fcard (inv e) D"
    using fcard_conj[OF fperm_inv[OF E.fperm_axioms] F.bij] permutes_image[OF face_perm]
    by simp
  then show ?thesis by (simp add: E.fcard_inv)
qed

lemma genus_mirror: "genus (mirror G) = genus G"
proof -
  have "n_comp (glink (mirror G)) D = n_comp (glink G) D"
    by (rule n_comp_eq) (simp add: gcomp_mirror)
  then show ?thesis
    by (simp add: genus_def Euler_lhs_def Euler_rhs_def fcard_mirror_edge N.fcard_inv F.fcard_inv)
qed

lemma planar_mirror: "planar (mirror G) \<longleftrightarrow> planar G"
  by (simp add: planar_def genus_mirror)

lemma connected_mirror: "connected (mirror G) \<longleftrightarrow> connected G"
  unfolding connected_def using n_comp_eq[of D "glink (mirror G)" "glink G"] gcomp_mirror by simp

end

end
