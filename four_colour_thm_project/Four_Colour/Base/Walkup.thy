(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Walkup.thy
    The Walkup construction: removing a dart from a hypermap.
    Ported from G. Gonthier's Coq development (walkup.v).
*)
theory Walkup
  imports Hypermap FC_Perm
begin

section \<open>Skipping a point in a permutation\<close>

definition skip :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "skip z g x = (if x = z then z else if g x = z then g z else g x)"

lemma skip_z [simp]: "skip z g z = z"
  by (simp add: skip_def)

lemma skip_neq: "x \<noteq> z \<Longrightarrow> skip z g x = (if g x = z then g z else g x)"
  by (simp add: skip_def)

context fperm
begin

lemma skip_ne_z:
  assumes xz: "x \<noteq> z"
  shows "skip z f x \<noteq> z"
proof (cases "f x = z")
  case True
  have "f z \<noteq> z"
  proof
    assume "f z = z"
    then have "f x = f z" using True by simp
    then show False using xz by simp
  qed
  then show ?thesis using True xz by (simp add: skip_def)
next
  case False
  then show ?thesis using xz by (simp add: skip_def)
qed

lemma skip_out:
  assumes "x \<notin> D - {z}"
  shows "skip z f x = x"
proof (cases "x = z")
  case True
  then show ?thesis by simp
next
  case False
  then have xD: "x \<notin> D" using assms by simp
  then have "f x = x" by simp
  then show ?thesis using False by (simp add: skip_def)
qed

lemma skip_inj: "inj (skip z f)"
proof (rule injI)
  fix x y assume eq: "skip z f x = skip z f y"
  show "x = y"
  proof (cases "x = z \<or> y = z")
    case True
    then show ?thesis using eq skip_ne_z[of x z] skip_ne_z[of y z] by (cases "x = z") auto
  next
    case False
    then have xz: "x \<noteq> z" and yz: "y \<noteq> z" by auto
    have sx: "skip z f x = (if f x = z then f z else f x)" using xz by (rule skip_neq)
    have sy: "skip z f y = (if f y = z then f z else f y)" using yz by (rule skip_neq)
    show ?thesis
    proof (cases "f x = z")
      case fx: True
      show ?thesis
      proof (cases "f y = z")
        case True
        then have "f x = f y" using fx by simp
        then show ?thesis by simp
      next
        case False
        then have "f z = f y" using eq sx sy fx by simp
        then have "z = y" by simp
        then show ?thesis using yz by simp
      qed
    next
      case fx: False
      show ?thesis
      proof (cases "f y = z")
        case True
        then have "f x = f z" using eq sx sy fx by simp
        then have "x = z" by simp
        then show ?thesis using xz by simp
      next
        case False
        then have "f x = f y" using eq sx sy fx by simp
        then show ?thesis by simp
      qed
    qed
  qed
qed

lemma skip_closed: "x \<in> D - {z} \<Longrightarrow> skip z f x \<in> D - {z}"
proof -
  assume x: "x \<in> D - {z}"
  show ?thesis
  proof (cases "f x = z")
    case True
    then have "f z \<noteq> z" using x eq_iff[of x z] by auto
    moreover have "z \<in> D" using True x closed[of x] by auto
    ultimately show ?thesis using True x by (simp add: skip_def)
  next
    case False
    then show ?thesis using x by (simp add: skip_def)
  qed
qed

lemma skip_perm: "skip z f permutes (D - {z})"
proof -
  have inj: "inj_on (skip z f) (D - {z})"
    by (rule inj_on_subset[OF skip_inj]) (rule subset_UNIV)
  have sub: "skip z f ` (D - {z}) \<subseteq> D - {z}"
    by (rule image_subsetI) (rule skip_closed)
  have finD: "finite (D - {z})" using fin by (rule finite_Diff)
  have "skip z f ` (D - {z}) = D - {z}" by (rule endo_inj_surj[OF finD sub inj])
  then have bb: "bij_betw (skip z f) (D - {z}) (D - {z})"
    using inj by (simp only: bij_betw_def)
  show ?thesis by (rule bij_imp_permutes[OF bb skip_out])
qed

lemma fperm_skip: "fperm (skip z f) (D - {z})"
  using skip_perm fin by unfold_locales auto

lemma fconnect_skip:
  assumes "x \<noteq> z"
  shows "fconnect (skip z f) x y \<longleftrightarrow> fconnect f x y \<and> y \<noteq> z"
proof
  assume "fconnect (skip z f) x y"
  then show "fconnect f x y \<and> y \<noteq> z"
  proof (induction rule: fconnect_induct)
    case refl
    then show ?case using assms by simp
  next
    case (step w)
    have wz: "w \<noteq> z" using step(2) by simp
    have "fconnect f w (skip z f w)"
    proof (cases "f w = z")
      case True
      then have "skip z f w = f (f w)" using wz by (simp add: skip_def)
      then show ?thesis using fconnect_stepI_r[OF fconnect_step[of f w]] by simp
    next
      case False
      then show ?thesis using wz by (simp add: skip_def fconnect_step)
    qed
    then have "fconnect f x (skip z f w)" by (rule fconnect_trans[OF conjunct1[OF step(2)]])
    then show ?case using skip_ne_z[OF wz] by simp
  qed
next
  assume "fconnect f x y \<and> y \<noteq> z"
  then obtain k where k: "(f ^^ k) x = y" "y \<noteq> z" unfolding fconnect_def by blast
  have "\<And>y. (f ^^ k) x = y \<Longrightarrow> y \<noteq> z \<Longrightarrow> fconnect (skip z f) x y"
  proof (induction k rule: less_induct)
    case (less k)
    show ?case
    proof (cases k)
      case 0
      then show ?thesis using less by simp
    next
      case (Suc k')
      show ?thesis
      proof (cases "(f ^^ k') x = z")
        case False
        then have "fconnect (skip z f) x ((f ^^ k') x)"
          using less.IH[of k' "(f ^^ k') x"] Suc by simp
        moreover have "skip z f ((f ^^ k') x) = y"
          using False less.prems Suc by (simp add: skip_def)
        ultimately show ?thesis using fconnect_stepI_r[of "skip z f" x "(f ^^ k') x"] by simp
      next
        case True
        then have "k' \<noteq> 0" using assms by (cases k') auto
        then obtain k'' where k'': "k' = Suc k''" by (cases k') auto
        have fz: "f z = y" using True less.prems Suc by simp
        have w: "(f ^^ k'') x \<noteq> z"
          using True k'' fz less.prems(2) by auto
        then have "fconnect (skip z f) x ((f ^^ k'') x)"
          using less.IH[of k'' "(f ^^ k'') x"] Suc k'' by simp
        moreover have "skip z f ((f ^^ k'') x) = y"
          using w True k'' fz by (simp add: skip_def)
        ultimately show ?thesis using fconnect_stepI_r[of "skip z f" x "(f ^^ k'') x"] by simp
      qed
    qed
  qed
  then show "fconnect (skip z f) x y" using k by blast
qed

lemma cyc_skip: "x \<noteq> z \<Longrightarrow> cyc (skip z f) x = cyc f x - {z}"
  by (auto simp: cyc_def fconnect_skip)

lemma fcard_skip:
  assumes z: "z \<in> D"
  shows "fcard (skip z f) (D - {z}) + (if f z = z then 1 else 0) = fcard f D"
proof (cases "f z = z")
  case True
  have "(f ^^ k) z = z" for k by (induction k) (simp_all add: True)
  then have cz: "cyc f z = {z}" by (auto simp: cyc_def fconnect_def)
  have nz: "z \<notin> cyc f x" if "x \<noteq> z" for x
    using that cz cyc_unique[of z x] x_in_cyc[of x] by auto
  have "cyc (skip z f) ` (D - {z}) = cyc f ` (D - {z})"
    using nz by (auto simp: cyc_skip image_def)
  moreover have "cyc f ` D = insert {z} (cyc f ` (D - {z}))"
    using z cz by auto
  moreover have "{z} \<notin> cyc f ` (D - {z})"
    using nz by auto
  moreover have "finite (cyc f ` (D - {z}))" using fin by simp
  ultimately show ?thesis
    using True by (simp add: fcard_def)
next
  case False
  let ?h = "\<lambda>S. S - {z}"
  have img: "cyc (skip z f) ` (D - {z}) = ?h ` (cyc f ` D)"
  proof
    show "cyc (skip z f) ` (D - {z}) \<subseteq> ?h ` (cyc f ` D)"
      by (auto simp: cyc_skip)
    show "?h ` (cyc f ` D) \<subseteq> cyc (skip z f) ` (D - {z})"
    proof
      fix S assume "S \<in> ?h ` (cyc f ` D)"
      then obtain a where a: "a \<in> D" "S = cyc f a - {z}" by blast
      show "S \<in> cyc (skip z f) ` (D - {z})"
      proof (cases "a = z")
        case True
        then have "S = cyc (skip z f) (f z)"
          using a False by (simp add: cyc_skip)
        moreover have "f z \<in> D - {z}" using z False by simp
        ultimately show ?thesis by blast
      next
        case False
        then show ?thesis using a by (auto simp: cyc_skip)
      qed
    qed
  qed
  have ne: "\<exists>w. w \<in> cyc f a - {z}" if "a \<in> D" for a
  proof (cases "a = z")
    case True
    then show ?thesis using False by (intro exI[of _ "f z"]) (auto simp: in_cyc_iff)
  next
    case False
    then show ?thesis by (intro exI[of _ a]) simp
  qed
  have inj: "inj_on ?h (cyc f ` D)"
  proof (rule inj_onI)
    fix S T assume S: "S \<in> cyc f ` D" and T: "T \<in> cyc f ` D" and eq: "S - {z} = T - {z}"
    obtain a b where ab: "a \<in> D" "b \<in> D" "S = cyc f a" "T = cyc f b" using S T by blast
    obtain w where w: "w \<in> cyc f a - {z}" using ne[OF ab(1)] by blast
    then have "w \<in> cyc f b" using eq ab by blast
    then show "S = T" using cyc_unique[of w a] cyc_unique[of w b] w ab by auto
  qed
  show ?thesis
    using False by (simp add: fcard_def img card_image[OF inj])
qed

end

section \<open>The WalkupE transform\<close>

definition skip_edge :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "skip_edge G z x =
     (if x = z then z
      else if edge G z = z then edge G x
      else if face G (edge G x) = z then edge G z
      else if edge G x = z then edge G (node G z)
      else edge G x)"

definition WalkupE :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> 'a hypermap" where
  "WalkupE G z = \<lparr>darts = darts G - {z}, edge = skip_edge G z,
                   node = skip z (node G), face = skip z (face G)\<rparr>"

definition WalkupN :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> 'a hypermap" where
  "WalkupN G z = permF (WalkupE (permN G) z)"

definition WalkupF :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> 'a hypermap" where
  "WalkupF G z = permN (WalkupE (permF G) z)"

lemma WalkupE_simps [simp]:
  "darts (WalkupE G z) = darts G - {z}" "edge (WalkupE G z) = skip_edge G z"
  "node (WalkupE G z) = skip z (node G)" "face (WalkupE G z) = skip z (face G)"
  by (simp_all add: WalkupE_def)

definition cross_edge :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> bool" where
  "cross_edge G z \<longleftrightarrow> fconnect (edge G) z (node G z)"

context hypermap
begin

lemma WalkupE_edgeK: "skip z n (skip z f (skip_edge G z x)) = x"
proof (cases "x = z")
  case True
  then show ?thesis by (simp add: skip_edge_def)
next
  case xz: False
  consider (A) "e z = z" | (B) "e z \<noteq> z" "f (e x) = z"
    | (C) "e z \<noteq> z" "f (e x) \<noteq> z" "e x = z" | (D) "e z \<noteq> z" "f (e x) \<noteq> z" "e x \<noteq> z"
    by blast
  then show ?thesis
  proof cases
    case A
    have exz: "e x \<noteq> z" using A xz E.eq_iff[of x z] by auto
    show ?thesis
    proof (cases "f (e x) = z")
      case True
      have "f z \<noteq> z" using True exz F.eq_iff[of "e x" z] by auto
      moreover have "n (f z) = z" using A edgeK[of z] by simp
      moreover have "n z = x" using True edgeK[of x] by simp
      ultimately show ?thesis using A xz exz True by (simp add: skip_edge_def skip_def)
    next
      case False
      then show ?thesis using A xz exz by (simp add: skip_edge_def skip_def edgeK)
    qed
  next
    case B
    have "f (e z) \<noteq> z" using B xz F.eq_iff[of "e z" "e x"] E.eq_iff[of z x] by auto
    moreover have "n (f (e z)) = z" by (rule edgeK)
    moreover have "n z = x" using B edgeK[of x] by simp
    ultimately show ?thesis using B xz by (simp add: skip_edge_def skip_def)
  next
    case C
    have fz: "f z \<noteq> z" using C by auto
    have enz: "e (n z) \<noteq> z" using fz nodeK[of z] by auto
    have fenz: "f (e (n z)) = z" by (rule nodeK)
    have nfz: "n (f z) \<noteq> z" using C faceK[of z] by auto
    have "n (f z) = x" using C edgeK[of x] by simp
    then show ?thesis using C xz fz enz fenz nfz by (simp add: skip_edge_def skip_def)
  next
    case D
    then show ?thesis using xz by (simp add: skip_edge_def skip_def edgeK)
  qed
qed

lemma skip_edge_out: "x \<notin> D - {z} \<Longrightarrow> skip_edge G z x = x"
  by (cases "x = z") (auto simp: skip_edge_def)

lemma hypermap_WalkupE: "hypermap (WalkupE G z)"
proof -
  interpret N': fperm "skip z n" "D - {z}" by (rule N.fperm_skip)
  interpret F': fperm "skip z f" "D - {z}" by (rule F.fperm_skip)
  let ?h = "skip z n \<circ> skip z f"
  have hp: "?h permutes D - {z}"
    by (rule permutes_compose[OF F'.perm N'.perm])
  have hb: "bij ?h" using hp by (rule permutes_bij)
  have eq: "skip_edge G z = inv ?h"
  proof
    fix x
    have "?h (skip_edge G z x) = x" by (simp add: WalkupE_edgeK)
    then show "skip_edge G z x = inv ?h x"
      using bij_inv_eq_iff[OF hb] by simp
  qed
  show ?thesis
  proof unfold_locales
    show "finite (darts (WalkupE G z))" using finite_darts by simp
    show "edge (WalkupE G z) permutes darts (WalkupE G z)"
      using permutes_inv[OF hp] eq by simp
    show "node (WalkupE G z) permutes darts (WalkupE G z)" using N'.perm by simp
    show "face (WalkupE G z) permutes darts (WalkupE G z)" using F'.perm by simp
    fix x
    show "node (WalkupE G z) (face (WalkupE G z) (edge (WalkupE G z) x)) = x"
      by (simp add: WalkupE_edgeK)
  qed
qed

lemma hypermap_WalkupN: "hypermap (WalkupN G z)"
proof -
  interpret P: hypermap "permN G" by (rule hypermap_permN)
  interpret W: hypermap "WalkupE (permN G) z" by (rule P.hypermap_WalkupE)
  show ?thesis unfolding WalkupN_def by (rule W.hypermap_permF)
qed

lemma hypermap_WalkupF: "hypermap (WalkupF G z)"
proof -
  interpret P: hypermap "permF G" by (rule hypermap_permF)
  interpret W: hypermap "WalkupE (permF G) z" by (rule P.hypermap_WalkupE)
  show ?thesis unfolding WalkupF_def by (rule W.hypermap_permN)
qed

lemma card_WalkupE: "z \<in> D \<Longrightarrow> card (darts (WalkupE G z)) = card D - 1"
  by (simp add: finite_darts)

subsection \<open>Edge cycles of the Walkup transform\<close>

lemma glink_fp_skip_edge: "glink G z z \<Longrightarrow> skip_edge G z x = skip z e x"
proof -
  assume g: "glink G z z"
  show ?thesis
  proof (cases "x = z")
    case True
    then show ?thesis by (simp add: skip_edge_def)
  next
    case xz: False
    consider "e z = z" | "e z \<noteq> z" "n z = z" | "e z \<noteq> z" "n z \<noteq> z" "f z = z"
      using g by (auto simp: glink_def)
    then show ?thesis
    proof cases
      case 1
      then show ?thesis using xz by (auto simp: skip_edge_def skip_def dest: E.eq_iff[THEN iffD1])
    next
      case 2
      have "f (e x) \<noteq> z"
      proof
        assume "f (e x) = z"
        then have "x = n z" using edgeK[of x] by simp
        then show False using 2 xz by simp
      qed
      then show ?thesis using 2 xz by (simp add: skip_edge_def skip_def)
    next
      case 3
      have "f (e x) = z \<longleftrightarrow> e x = z" using 3 F.eq_iff[of "e x" z] by simp
      then show ?thesis using 3 xz by (auto simp: skip_edge_def skip_def)
    qed
  qed
qed

lemma skip_edge_transpose:
  assumes nd: "\<not> glink G z z"
  shows "skip_edge G z = skip z e \<circ> Transposition.transpose (n z) (inv e z)"
proof
  fix x
  have ez: "e z \<noteq> z" and nz: "n z \<noteq> z" and fz: "f z \<noteq> z"
    using nd by (auto simp: glink_def)
  have ie: "inv e z = n (f z)" by (simp add: inv_edge_apply)
  have iez: "inv e z \<noteq> z" using ez by (metis E.f_inv)
  have nie: "n z \<noteq> inv e z" using fz ie N.eq_iff[of z "f z"] by auto
  have enz: "e (n z) \<noteq> z" using fz nodeK[of z] by auto
  show "skip_edge G z x = (skip z e \<circ> Transposition.transpose (n z) (inv e z)) x"
  proof (cases "x = z")
    case True
    then show ?thesis using nz iez by (simp add: skip_edge_def Transposition.transpose_def)
  next
    case xz: False
    show ?thesis
    proof (cases "x = n z")
      case True
      have "f (e x) = z" using True nodeK[of z] by simp
      then show ?thesis using True xz ez nie iez by (simp add: skip_edge_def skip_def Transposition.transpose_def)
    next
      case xnz: False
      show ?thesis
      proof (cases "x = inv e z")
        case True
        have exz: "e x = z" using True by simp
        have "f (e x) \<noteq> z" using exz fz by simp
        then show ?thesis using True xz ez exz nie enz nz
          by (simp add: skip_edge_def skip_def Transposition.transpose_def)
      next
        case False
        have "e x \<noteq> z" using False E.inv_f[of x] by auto
        moreover have "f (e x) \<noteq> z"
        proof
          assume "f (e x) = z"
          then have "x = n z" using edgeK[of x] by simp
          then show False using xnz by simp
        qed
        ultimately show ?thesis using False xz xnz ez
          by (simp add: skip_edge_def skip_def Transposition.transpose_def)
      qed
    qed
  qed
qed

lemma fcard_WalkupE_edge:
  assumes z: "z \<in> D"
  shows "int (fcard (skip_edge G z) (D - {z})) =
           (if glink G z z then int (fcard e D) - (if e z = z then 1 else 0)
            else int (fcard e D) + (if cross_edge G z then 1 else -1))"
proof (cases "glink G z z")
  case True
  then have "skip_edge G z = skip z e" using glink_fp_skip_edge[OF True] by (simp add: fun_eq_iff)
  then show ?thesis using True E.fcard_skip[OF z] by (simp split: if_splits)
next
  case False
  have ez: "e z \<noteq> z" and fz: "f z \<noteq> z" using False by (auto simp: glink_def)
  interpret S: fperm "skip z e" "D - {z}" by (rule E.fperm_skip)
  have a: "n z \<in> D - {z}" using False z by (auto simp: glink_def)
  have iez: "inv e z \<noteq> z" using ez by (metis E.f_inv)
  have b: "inv e z \<in> D - {z}" using z iez E.closed[of "inv e z"] by simp
  have ab: "n z \<noteq> inv e z" using fz N.eq_iff[of z "f z"] by (simp add: inv_edge_apply)
  have "fconnect (skip z e) (n z) (inv e z) \<longleftrightarrow> cedge (n z) (inv e z)"
    using b a by (simp add: E.fconnect_skip)
  also have "\<dots> \<longleftrightarrow> cross_edge G z"
    unfolding cross_edge_def using E.fconnect_commute[of "n z" z] by simp
  finally have conn: "fconnect (skip z e) (n z) (inv e z) \<longleftrightarrow> cross_edge G z" .
  have "int (fcard (skip_edge G z) (D - {z})) = int (fcard (skip z e) (D - {z})) + (if cross_edge G z then 1 else -1)"
    unfolding skip_edge_transpose[OF False]
    using fcard_transpose[OF S.fperm_axioms a b ab] conn by simp
  moreover have "fcard (skip z e) (D - {z}) = fcard e D"
    using E.fcard_skip[OF z] ez by simp
  ultimately show ?thesis using False by simp
qed

subsection \<open>Components of the Walkup transform\<close>

lemma glink_WalkupE_gcomp: "glink (WalkupE G z) x y \<Longrightarrow> gcomp G x y"
proof -
  assume l: "glink (WalkupE G z) x y"
  have g1: "glink G a b \<Longrightarrow> gcomp G a b" for a b by (rule r_into_rtranclp)
  have zn: "gcomp G z (n z)" "gcomp G z (e z)" "gcomp G z (f z)" by (simp_all add: g1)
  have zen: "gcomp G z (e (n z))" by (rule rtranclp_trans[OF zn(1) g1[OF glinkE]])
  consider (E) "skip_edge G z x = y" | (N) "skip z n x = y" | (F) "skip z f x = y"
    using l by (auto simp: glink_def)
  then show ?thesis
  proof cases
    case E
    show ?thesis
    proof (cases "x = z")
      case True
      then show ?thesis using E by (simp add: skip_edge_def)
    next
      case xz: False
      show ?thesis
      proof (cases "e z = z \<or> (f (e x) \<noteq> z \<and> e x \<noteq> z)")
        case True
        then have "y = e x" using E xz by (auto simp: skip_edge_def)
        then show ?thesis using g1[OF glinkE[of x]] by simp
      next
        case False
        then consider "e z \<noteq> z" "f (e x) = z" | "e z \<noteq> z" "f (e x) \<noteq> z" "e x = z" by blast
        then show ?thesis
        proof cases
          case 1
          then have y: "y = e z" using E xz by (simp add: skip_edge_def)
          have "gcomp G x (f (e x))" by (rule rtranclp_trans[OF g1[OF glinkE[of x]] g1[OF glinkF]])
          then have "gcomp G x z" using 1 by simp
          then show ?thesis using rtranclp_trans[OF _ zn(2)] y by simp
        next
          case 2
          then have y: "y = e (n z)" using E xz by (simp add: skip_edge_def)
          have "gcomp G x z" using g1[OF glinkE[of x]] 2 by simp
          then show ?thesis using rtranclp_trans[OF _ zen] y by simp
        qed
      qed
    qed
  next
    case N
    show ?thesis
    proof (cases "x \<noteq> z \<and> n x = z")
      case True
      then have y: "y = n z" using N by (simp add: skip_def)
      have "gcomp G x z" using g1[OF glinkN[of x]] True by simp
      then show ?thesis using rtranclp_trans[OF _ zn(1)] y by simp
    next
      case False
      then have "y = n x \<or> (x = z \<and> y = z)" using N by (cases "x = z") (auto simp: skip_def)
      then show ?thesis using g1[OF glinkN[of x]] by auto
    qed
  next
    case F
    show ?thesis
    proof (cases "x \<noteq> z \<and> f x = z")
      case True
      then have y: "y = f z" using F by (simp add: skip_def)
      have "gcomp G x z" using g1[OF glinkF[of x]] True by simp
      then show ?thesis using rtranclp_trans[OF _ zn(3)] y by simp
    next
      case False
      then have "y = f x \<or> (x = z \<and> y = z)" using F by (cases "x = z") (auto simp: skip_def)
      then show ?thesis using g1[OF glinkF[of x]] by auto
    qed
  qed
qed

lemma gcomp_WalkupE_gcomp: "gcomp (WalkupE G z) x y \<Longrightarrow> gcomp G x y"
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step y w)
  show ?case by (rule rtranclp_trans[OF step(3) glink_WalkupE_gcomp[OF step(2)]])
qed

lemma glink_WalkupE_outside:
  assumes nzx: "\<not> gcomp G z x" and l: "glink G x y"
  shows "glink (WalkupE G z) x y"
proof -
  have xz: "x \<noteq> z" using nzx by auto
  have nx: "n x \<noteq> z" using nzx glink_sym[OF glinkN[of x]] by auto
  have fx: "f x \<noteq> z" using nzx glink_sym[OF glinkF[of x]] by auto
  have ex: "e x \<noteq> z" using nzx glink_sym[OF glinkE[of x]] by auto
  have fex: "f (e x) \<noteq> z"
  proof
    assume h: "f (e x) = z"
    have "gcomp G (f (e x)) x"
      by (rule rtranclp_trans[OF glink_sym[OF glinkF[of "e x"]] glink_sym[OF glinkE[of x]]])
    then show False using nzx h by simp
  qed
  have "skip_edge G z x = e x" "skip z n x = n x" "skip z f x = f x"
    using xz nx fx ex fex by (auto simp: skip_edge_def skip_def)
  then show ?thesis using l by (auto simp: glink_def)
qed

lemma gcomp_WalkupE_outside:
  assumes nzx: "\<not> gcomp G z x"
  shows "gcomp (WalkupE G z) x y \<longleftrightarrow> gcomp G x y"
proof
  assume "gcomp G x y"
  then show "gcomp (WalkupE G z) x y"
  proof (induction rule: rtranclp_induct)
    case base
    then show ?case by simp
  next
    case (step y w)
    have "\<not> gcomp G z y"
    proof
      assume "gcomp G z y"
      then have "gcomp G z x" by (rule rtranclp_trans[OF _ gcomp_sym[OF step(1)]])
      then show False using nzx by simp
    qed
    then show ?case
      by (rule rtranclp.rtrancl_into_rtrancl[OF step(3) glink_WalkupE_outside[OF _ step(2)]])
  qed
qed (rule gcomp_WalkupE_gcomp)

lemma clink_WalkupE:
  assumes "clink G a b" "a \<noteq> z" "b \<noteq> z"
  shows "gcomp (WalkupE G z) a b"
proof -
  interpret W: hypermap "WalkupE G z" by (rule hypermap_WalkupE)
  consider "a = n b" | "f a = b" using assms(1) by (auto simp: clink_def)
  then show ?thesis
  proof cases
    case 1
    then have "skip z n b = a" using assms by (simp add: skip_def)
    then have "glink (WalkupE G z) b a" by (simp add: glink_def)
    then show ?thesis by (rule W.glink_sym)
  next
    case 2
    then have "skip z f a = b" using assms by (simp add: skip_def)
    then show ?thesis by (simp add: glink_def r_into_rtranclp)
  qed
qed

text \<open>Every dart of the component of @{term z} other than @{term z} is connected in
  the Walkup transform to @{term "n z"} or @{term "inv f z"}.\<close>

lemma WalkupE_comp_neighbour:
  assumes w: "gcomp G z w" "w \<noteq> z"
  shows "\<exists>v \<in> {n z, inv f z} - {z}. gcomp (WalkupE G z) w v"
proof -
  have "gcomp G w z" by (rule gcomp_sym[OF w(1)])
  then have "connect (clink G) w z" using clink_glink by simp
  then obtain p where p: "path (clink G) w p" "lastd w p = z" "distinct (w # p)"
    by (rule connect_shortest)
  have "p \<noteq> []" using p w by auto
  define q where "q = butlast p"
  have "last p = z" using p(2) \<open>p \<noteq> []\<close> by simp
  then have q: "p = q @ [z]" using \<open>p \<noteq> []\<close> unfolding q_def by (metis append_butlast_last_id)
  let ?v = "lastd w q"
  have vz: "?v \<noteq> z" using p q by (cases q rule: rev_cases) auto
  have nz: "z \<notin> set (w # q)" using p q by auto
  have pq: "path (clink G) w q" "clink G ?v z" using p q by simp_all
  have "gcomp (WalkupE G z) w ?v"
    using pq(1) nz
  proof (induction q arbitrary: w)
    case Nil
    then show ?case by simp
  next
    case (Cons y q)
    then have "gcomp (WalkupE G z) w y" using clink_WalkupE[of w y z] by auto
    moreover have "gcomp (WalkupE G z) y (lastd y q)" using Cons by simp
    ultimately show ?case by (simp add: rtranclp_trans[of _ w y])
  qed
  moreover have "?v \<in> {n z, inv f z}"
    using pq(2) F.inv_f[of ?v] by (auto simp: clink_def)
  ultimately show ?thesis using vz by blast
qed

subsection \<open>Edge cycles away from, and around, the removed dart\<close>

definition edom :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "edom z x \<longleftrightarrow> cedge x z \<or> cedge x (n z)"

lemma same_cskip_edge:
  assumes x: "\<not> edom z x" "x \<noteq> z"
  shows "fconnect (skip_edge G z) x y \<longleftrightarrow> cedge x y"
proof (rule fconnect_eq_on)
  fix w assume xw: "cedge x w"
  have wz: "w \<noteq> z" using x xw by (auto simp: edom_def)
  have ewz: "e w \<noteq> z"
  proof
    assume "e w = z"
    then have "cedge w z" using fconnect_step[of e w] by simp
    then show False using x xw by (auto simp: edom_def intro: fconnect_trans)
  qed
  have fewz: "f (e w) \<noteq> z"
  proof
    assume "f (e w) = z"
    then have "w = n z" using edgeK[of w] by simp
    then show False using x xw by (auto simp: edom_def)
  qed
  show "skip_edge G z w = e w" using wz ewz fewz by (simp add: skip_edge_def)
qed

lemma cskip_edge_merge:
  assumes nc: "\<not> cross_edge G z" and z: "z \<in> D" and x: "edom z x" "x \<noteq> z" and y: "y \<noteq> z"
  shows "fconnect (skip_edge G z) x y \<longleftrightarrow> edom z y"
proof -
  have nz: "n z \<noteq> z" using nc by (auto simp: cross_edge_def)
  have edom_cyc: "edom z w \<longleftrightarrow> w \<in> cyc e z \<union> cyc e (n z)" for w
    by (auto simp: edom_def E.in_cyc_iff E.fconnect_commute)
  have disj: "cyc e z \<inter> cyc e (n z) = {}"
    using nc E.cyc_disjoint_or_eq[of z "n z"] E.cyc_eq_iff by (auto simp: cross_edge_def)
  have target: "cyc (skip_edge G z) x = (cyc e z \<union> cyc e (n z)) - {z}"
  proof (cases "glink G z z")
    case True
    have ez: "e z = z"
    proof (rule ccontr)
      assume ez: "e z \<noteq> z"
      have fz: "f z = z" using True nz ez by (auto simp: glink_def)
      have "e (n z) = z" using faceK[of z] fz by simp
      then have "cedge (n z) z" using fconnect_step[of e "n z"] by simp
      then show False using nc E.fconnect_sym by (auto simp: cross_edge_def)
    qed
    have cz: "cyc e z = {z}" using ez E.order_1_iff[of z] E.cyc_order[of z] by auto
    have se: "skip_edge G z = skip z e" using glink_fp_skip_edge[OF True] by (simp add: fun_eq_iff)
    have xn: "x \<in> cyc e (n z)" using x edom_cyc cz by auto
    have zn: "z \<notin> cyc e (n z)" using disj cz by auto
    have "cyc (skip z e) x = cyc e x - {z}" by (rule E.cyc_skip[OF x(2)])
    also have "cyc e x = cyc e (n z)" using xn E.cyc_unique by simp
    finally have "cyc (skip z e) x = cyc e (n z)" using zn by simp
    moreover have "(cyc e z \<union> cyc e (n z)) - {z} = cyc e (n z)" using cz zn by auto
    ultimately show ?thesis using se by simp
  next
    case False
    interpret S: fperm "skip z e" "D - {z}" by (rule E.fperm_skip)
    have ez: "e z \<noteq> z" and fz: "f z \<noteq> z" using False by (auto simp: glink_def)
    have a: "n z \<in> D - {z}" using nz z by simp
    have iez: "inv e z \<noteq> z" using ez by (metis E.f_inv)
    have b: "inv e z \<in> D - {z}" using z iez E.closed[of "inv e z"] by simp
    have ab: "n z \<noteq> inv e z" using fz N.eq_iff[of z "f z"] by (simp add: inv_edge_apply)
    have "\<not> fconnect (skip z e) (n z) (inv e z)"
      using nc a b E.fconnect_commute[of "n z" z] by (simp add: E.fconnect_skip cross_edge_def)
    then have m: "cyc (skip_edge G z) (n z) = cyc (skip z e) (n z) \<union> cyc (skip z e) (inv e z)"
      unfolding skip_edge_transpose[OF False] by (rule cyc_transpose_merge[OF S.fperm_axioms a b ab])
    have c1: "cyc (skip z e) (n z) = cyc e (n z) - {z}" using E.cyc_skip[OF nz] .
    have c2: "cyc (skip z e) (inv e z) = cyc e z - {z}"
      using E.cyc_skip[OF iez] E.cyc_inv E.cyc_unique by (metis E.f_inv E.x_in_cyc E.in_cyc_iff fconnect_step E.cyc_eq)
    have mm: "cyc (skip_edge G z) (n z) = (cyc e z \<union> cyc e (n z)) - {z}" using m c1 c2 by auto
    interpret W: hypermap "WalkupE G z" by (rule hypermap_WalkupE)
    have "x \<in> cyc (skip_edge G z) (n z)" using mm x edom_cyc by auto
    then have "cyc (skip_edge G z) (n z) = cyc (skip_edge G z) x"
      using W.E.cyc_unique[of x "n z"] by simp
    then show ?thesis using mm by simp
  qed
  have "fconnect (skip_edge G z) x y \<longleftrightarrow> y \<in> cyc (skip_edge G z) x" by (simp add: cyc_def)
  also have "\<dots> \<longleftrightarrow> edom z y" using target y edom_cyc by auto
  finally show ?thesis .
qed

lemma n_comp_WalkupE:
  assumes z: "z \<in> D"
  shows "n_comp (glink (WalkupE G z)) (D - {z}) + 1 =
           n_comp (glink G) D + card (comp_of (glink (WalkupE G z)) ` (comp_of (glink G) z - {z}))"
proof -
  let ?W = "WalkupE G z"
  let ?C = "comp_of (glink G) z"
  let ?cG = "comp_of (glink G)" and ?cW = "comp_of (glink ?W)"
  have CD: "?C \<subseteq> D" using z gcomp_closed by (auto simp: comp_of_def)
  have zC: "z \<in> ?C" by (simp add: comp_of_def)
  have outside: "?cW x = ?cG x" if "x \<in> D - ?C" for x
    using that gcomp_WalkupE_outside by (auto simp: comp_of_def)
  have split: "D - {z} = (D - ?C) \<union> (?C - {z})" using CD zC by blast
  have img: "?cW ` (D - {z}) = ?cG ` (D - ?C) \<union> ?cW ` (?C - {z})"
    unfolding split image_Un using outside by (auto simp: image_def)
  have sub: "?cW w \<subseteq> ?C" if "w \<in> ?C" for w
  proof
    fix y assume "y \<in> ?cW w"
    then have "gcomp G w y" using gcomp_WalkupE_gcomp by (simp add: comp_of_def)
    then show "y \<in> ?C" using rtranclp_trans[of "glink G" z w y] that by (simp add: comp_of_def)
  qed
  have disj: "?cG ` (D - ?C) \<inter> ?cW ` (?C - {z}) = {}"
  proof -
    { fix x w assume x: "x \<in> D - ?C" and w: "w \<in> ?C - {z}" and eq: "?cG x = ?cW w"
      have "x \<in> ?cG x" by (simp add: comp_of_def)
      then have "x \<in> ?C" using eq sub w by auto
      then have False using x by simp }
    then show ?thesis by blast
  qed
  have Cnot: "?C \<notin> ?cG ` (D - ?C)"
  proof
    assume "?C \<in> ?cG ` (D - ?C)"
    then obtain x where x: "x \<in> D - ?C" "?C = ?cG x" by blast
    then have "gcomp G x z" using zC by (simp add: comp_of_def)
    then have "x \<in> ?C" using gcomp_sym[OF \<open>gcomp G x z\<close>] by (simp add: comp_of_def)
    then show False using x by simp
  qed
  have CC: "?cG ` ?C = {?C}"
  proof -
    have "?cG x = ?C" if "x \<in> ?C" for x
      using comp_eq[of z x] that by (simp add: comp_of_def)
    then show ?thesis using zC by blast
  qed
  have "D = (D - ?C) \<union> ?C" using CD by blast
  then have imgG: "?cG ` D = insert ?C (?cG ` (D - ?C))"
    using CC by (metis image_Un insert_is_Un sup_commute)
  have fin: "finite (?cG ` (D - ?C))" "finite (?cW ` (?C - {z}))"
    using finite_darts CD by (auto intro: finite_subset)
  show ?thesis
    unfolding n_comp_def img imgG
    using card_Un_disjoint[OF fin disj] Cnot fin by simp
qed

lemma WalkupE_K_subset:
  "comp_of (glink (WalkupE G z)) ` (comp_of (glink G) z - {z}) \<subseteq>
     comp_of (glink (WalkupE G z)) ` ({n z, inv f z} - {z})"
proof
  interpret W: hypermap "WalkupE G z" by (rule hypermap_WalkupE)
  fix K assume "K \<in> comp_of (glink (WalkupE G z)) ` (comp_of (glink G) z - {z})"
  then obtain w where w: "gcomp G z w" "w \<noteq> z" "K = comp_of (glink (WalkupE G z)) w"
    by (auto simp: comp_of_def)
  obtain v where v: "v \<in> {n z, inv f z} - {z}" "gcomp (WalkupE G z) w v"
    using WalkupE_comp_neighbour[OF w(1,2)] by blast
  have "comp_of (glink (WalkupE G z)) w = comp_of (glink (WalkupE G z)) v"
    by (rule W.comp_eq[OF v(2)])
  then show "K \<in> comp_of (glink (WalkupE G z)) ` ({n z, inv f z} - {z})"
    using v(1) w(3) by blast
qed

lemma WalkupE_nz_ifz:
  assumes "e z = z \<or> (\<not> glink G z z \<and> \<not> cross_edge G z)" "n z \<noteq> z"
  shows "gcomp (WalkupE G z) (n z) (inv f z)"
proof -
  interpret W: hypermap "WalkupE G z" by (rule hypermap_WalkupE)
  have ifz: "inv f z = e (n z)" by (simp add: inv_face_apply)
  show ?thesis
  proof (cases "e z = z")
    case True
    then have "skip_edge G z (n z) = e (n z)" using assms(2) by (simp add: skip_edge_def)
    then have "glink (WalkupE G z) (n z) (inv f z)" using ifz by (simp add: glink_def)
    then show ?thesis by (rule r_into_rtranclp)
  next
    case False
    then have nd: "\<not> glink G z z" and nc: "\<not> cross_edge G z" using assms by auto
    have ez: "e z \<noteq> z" and fz: "f z \<noteq> z" using nd by (auto simp: glink_def)
    interpret S: fperm "skip z e" "D - {z}" by (rule E.fperm_skip)
    have zD: "z \<in> D" using ez by (metis E.out)
    have a: "n z \<in> D - {z}" using assms(2) zD by simp
    have iez: "inv e z \<noteq> z" using ez by (metis E.f_inv)
    have b: "inv e z \<in> D - {z}" using zD iez E.closed[of "inv e z"] by simp
    have ab: "n z \<noteq> inv e z" using fz N.eq_iff[of z "f z"] by (simp add: inv_edge_apply)
    have "\<not> fconnect (skip z e) (n z) (inv e z)"
      using nc a b E.fconnect_commute[of "n z" z] by (simp add: E.fconnect_skip cross_edge_def)
    then have cy: "cyc (skip_edge G z) (n z) = cyc (skip z e) (n z) \<union> cyc (skip z e) (inv e z)"
      unfolding skip_edge_transpose[OF nd] by (rule cyc_transpose_merge[OF S.fperm_axioms a b ab])
    have enz: "e (n z) \<noteq> z" using fz nodeK[of z] by auto
    have "fconnect (skip z e) (n z) (e (n z))"
      using a enz by (simp add: E.fconnect_skip)
    then have "fconnect (skip_edge G z) (n z) (inv f z)"
      using cy ifz by (auto simp: cyc_def)
    then show ?thesis using W.cedge_gcomp by simp
  qed
qed

end

definition delta :: "'a hypermap \<Rightarrow> int" where
  "delta G = int (Euler_lhs G) - int (Euler_rhs G)"

lemma even_genus_delta: "even_genus G \<longleftrightarrow> delta G \<ge> 0 \<and> even (delta G)"
proof -
  define L where "L = Euler_lhs G"
  define R where "R = Euler_rhs G"
  have eg: "even_genus G \<longleftrightarrow> L = 2 * ((L - R) div 2) + R"
    by (simp add: even_genus_def genus_def L_def R_def)
  have dl: "delta G = int L - int R" by (simp add: delta_def L_def R_def)
  show ?thesis
  proof
    assume "even_genus G"
    then have h: "L = 2 * ((L - R) div 2) + R" using eg by simp
    then have le: "R \<le> L" by linarith
    have "L - R = 2 * ((L - R) div 2)" using h by linarith
    then have "even (L - R)" by (metis dvd_triv_left)
    then have "even (int (L - R))" by simp
    then show "delta G \<ge> 0 \<and> even (delta G)" using le dl by (simp add: of_nat_diff)
  next
    assume h: "delta G \<ge> 0 \<and> even (delta G)"
    then have le: "R \<le> L" using dl by simp
    then have "even (int (L - R))" using h dl by (simp add: of_nat_diff)
    then have "even (L - R)" by simp
    then have "2 * ((L - R) div 2) = L - R" by simp
    then have "L = 2 * ((L - R) div 2) + R" using le by simp
    then show "even_genus G" using eg by simp
  qed
qed

lemma genus_delta: "genus G = nat (delta G) div 2"
proof -
  have "nat (int (Euler_lhs G) - int (Euler_rhs G)) = Euler_lhs G - Euler_rhs G" by simp
  then show ?thesis unfolding genus_def delta_def by simp
qed

context hypermap
begin

lemma card_image_pair_le2: "card (h ` ({a, b} - {z})) \<le> 2"
proof -
  have "card (h ` ({a, b} - {z})) \<le> card ({a, b} - {z})" by (rule card_image_le) simp
  also have "\<dots> \<le> card {a, b}" by (rule card_mono) auto
  also have "\<dots> \<le> 2" by (simp add: card_insert_le_m1)
  finally show ?thesis .
qed

lemma card_image_pair_le1:
  assumes "a = z \<or> b = z \<or> h a = h b"
  shows "card (h ` ({a, b} - {z})) \<le> 1"
proof -
  have "h ` ({a, b} - {z}) \<subseteq> {h b} \<or> h ` ({a, b} - {z}) \<subseteq> {h a}"
    using assms by auto
  then show ?thesis by (metis card.empty card_insert_disjoint card_mono empty_iff finite.emptyI
        finite.insertI One_nat_def)
qed

lemma delta_WalkupE:
  assumes z: "z \<in> D"
  shows "delta (WalkupE G z) = delta G \<or>
         (delta (WalkupE G z) = delta G - 2 \<and> \<not> glink G z z \<and> cross_edge G z)"
proof -
  let ?W = "WalkupE G z"
  let ?C = "comp_of (glink G) z"
  let ?K = "comp_of (glink ?W) ` (?C - {z})"
  let ?k = "card ?K"
  let ?P = "comp_of (glink ?W) ` ({n z, inv f z} - {z})"
  have CD: "?C \<subseteq> D" using z gcomp_closed by (auto simp: comp_of_def)
  have finK: "finite ?K" using finite_subset[OF CD finite_darts] by simp
  have nc: "int (n_comp (glink ?W) (D - {z})) = int (n_comp (glink G) D) + int ?k - 1"
    using n_comp_WalkupE[OF z] by linarith
  have cpos: "card D > 0" using z finite_darts card_gt_0_iff by blast
  have cD: "int (card (D - {z})) = int (card D) - 1"
    using z finite_darts cpos by (simp add: of_nat_diff)
  have fn: "int (fcard (skip z n) (D - {z})) = int (fcard n D) - (if n z = z then 1 else 0)"
    using N.fcard_skip[OF z] by (simp split: if_splits)
  have ff: "int (fcard (skip z f) (D - {z})) = int (fcard f D) - (if f z = z then 1 else 0)"
    using F.fcard_skip[OF z] by (simp split: if_splits)
  have fe: "int (fcard (skip_edge G z) (D - {z})) =
           (if glink G z z then int (fcard e D) - (if e z = z then 1 else 0)
            else int (fcard e D) + (if cross_edge G z then 1 else -1))"
    by (rule fcard_WalkupE_edge[OF z])
  have dW: "delta ?W = 2 * int (n_comp (glink ?W) (D - {z})) + int (card (D - {z}))
       - int (fcard (skip_edge G z) (D - {z})) - int (fcard (skip z n) (D - {z}))
       - int (fcard (skip z f) (D - {z}))"
    by (simp add: delta_def Euler_lhs_def Euler_rhs_def)
  have dG: "delta G = 2 * int (n_comp (glink G) D) + int (card D) - int (fcard e D)
       - int (fcard n D) - int (fcard f D)"
    by (simp add: delta_def Euler_lhs_def Euler_rhs_def)
  have Ksub: "?K \<subseteq> ?P" by (rule WalkupE_K_subset)
  have kP: "?k \<le> card ?P" by (rule card_mono[OF _ Ksub]) simp
  have k2: "?k \<le> 2" using kP card_image_pair_le2[of "comp_of (glink ?W)" "n z" "inv f z" z] by linarith
  have isoK: "?K = {} \<longleftrightarrow> e z = z \<and> n z = z \<and> f z = z"
  proof
    assume K: "?K = {}"
    then have sub: "?C \<subseteq> {z}" by auto
    have "e z \<in> ?C" "n z \<in> ?C" "f z \<in> ?C"
      by (simp_all add: comp_of_def r_into_rtranclp)
    then show "e z = z \<and> n z = z \<and> f z = z" using sub by auto
  next
    assume iso: "e z = z \<and> n z = z \<and> f z = z"
    have "gcomp G z w \<Longrightarrow> w = z" for w
      by (induction rule: rtranclp_induct) (use iso in \<open>auto simp: glink_def\<close>)
    then show "?K = {}" by (auto simp: comp_of_def)
  qed
  have kpos: "?k \<ge> 1" if "\<not> (e z = z \<and> n z = z \<and> f z = z)"
  proof -
    have "?K \<noteq> {}" using isoK that by simp
    then show ?thesis using finK by (simp add: Suc_le_eq card_gt_0_iff)
  qed
  have k1: "?k \<le> 1" if "e z = z \<or> n z = z \<or> f z = z \<or> \<not> cross_edge G z"
    "e z = z \<or> n z = z \<or> f z = z \<or> \<not> glink G z z"
  proof -
    have "n z = z \<or> inv f z = z \<or> comp_of (glink ?W) (n z) = comp_of (glink ?W) (inv f z)"
    proof (cases "n z = z \<or> inv f z = z")
      case False
      then have nz: "n z \<noteq> z" and fz: "f z \<noteq> z" by (auto, metis F.inv_f)
      interpret W: hypermap ?W by (rule hypermap_WalkupE)
      have "e z = z \<or> (\<not> glink G z z \<and> \<not> cross_edge G z)"
        using that nz fz by auto
      then have "gcomp ?W (n z) (inv f z)" by (rule WalkupE_nz_ifz[OF _ nz])
      then show ?thesis using W.comp_eq by blast
    qed blast
    then have "card ?P \<le> 1" by (rule card_image_pair_le1)
    then show ?thesis using kP by linarith
  qed
  have one_fixed: "(if e z = z then 1 else 0) + (if n z = z then 1 else 0) + (if f z = z then 1 else 0) = (1::int)"
    if gz: "glink G z z" and ni: "\<not> (e z = z \<and> n z = z \<and> f z = z)"
  proof -
    have i1: "e z = z \<Longrightarrow> n z = z \<Longrightarrow> f z = z" using edgeK[of z] N.eq_iff[of "f z" z] by simp
    have i2: "e z = z \<Longrightarrow> f z = z \<Longrightarrow> n z = z" using edgeK[of z] by simp
    have i3: "n z = z \<Longrightarrow> f z = z \<Longrightarrow> e z = z" using faceK[of z] by simp
    have g: "e z = z \<or> n z = z \<or> f z = z" using gz by (simp add: glink_def)
    have "(e z = z \<and> n z \<noteq> z \<and> f z \<noteq> z) \<or> (e z \<noteq> z \<and> n z = z \<and> f z \<noteq> z)
          \<or> (e z \<noteq> z \<and> n z \<noteq> z \<and> f z = z)"
      using g i1 i2 i3 ni by blast
    then show ?thesis by auto
  qed
  define nW where "nW = int (n_comp (glink ?W) (D - {z}))"
  define nG where "nG = int (n_comp (glink G) D)"
  define cG where "cG = int (card D)"
  define eW where "eW = int (fcard (skip_edge G z) (D - {z}))"
  define eG where "eG = int (fcard e D)"
  define vW where "vW = int (fcard (skip z n) (D - {z}))"
  define vG where "vG = int (fcard n D)"
  define fW where "fW = int (fcard (skip z f) (D - {z}))"
  define fG where "fG = int (fcard f D)"
  have dW': "delta ?W = 2 * nW + (cG - 1) - eW - vW - fW"
    using dW cD unfolding nW_def cG_def eW_def vW_def fW_def by simp
  have dG': "delta G = 2 * nG + cG - eG - vG - fG"
    using dG unfolding nG_def cG_def eG_def vG_def fG_def by simp
  have nc': "nW = nG + int ?k - 1" using nc unfolding nW_def nG_def by simp
  show ?thesis
  proof (cases "glink G z z")
    case True
    have eW1: "eW = eG - (if e z = z then 1 else 0)"
      using fe True unfolding eW_def eG_def by simp
    have vW1: "vW = vG - (if n z = z then 1 else 0)" using fn unfolding vW_def vG_def by simp
    have fW1: "fW = fG - (if f z = z then 1 else 0)" using ff unfolding fW_def fG_def by simp
    show ?thesis
    proof (cases "e z = z \<and> n z = z \<and> f z = z")
      case iso: True
      then have "?K = {}" using isoK by blast
      then have k0: "?k = 0" by (simp only: card.empty)
      have "eW = eG - 1" "vW = vG - 1" "fW = fG - 1" using eW1 vW1 fW1 iso by simp_all
      then have "delta ?W = delta G" using dW' dG' nc' k0 by linarith
      then show ?thesis by simp
    next
      case False
      have "?k \<le> 1" using k1 True by (auto simp: glink_def)
      then have k1': "?k = 1" using kpos[OF False] by simp
      have "(eG - eW) + (vG - vW) + (fG - fW) = 1"
        using eW1 vW1 fW1 one_fixed[OF True False] by simp
      then have "delta ?W = delta G" using dW' dG' nc' k1' by linarith
      then show ?thesis by simp
    qed
  next
    case False
    have ez: "e z \<noteq> z" "n z \<noteq> z" "f z \<noteq> z" using False by (auto simp: glink_def)
    have kp: "?k \<ge> 1" using kpos ez by simp
    have vW1: "vW = vG" using fn ez unfolding vW_def vG_def by simp
    have fW1: "fW = fG" using ff ez unfolding fW_def fG_def by simp
    show ?thesis
    proof (cases "cross_edge G z")
      case True
      have eW1: "eW = eG + 1" using fe False True unfolding eW_def eG_def by simp
      have "?k = 1 \<or> ?k = 2" using kp k2 by linarith
      then show ?thesis
      proof
        assume "?k = 1"
        then have "delta ?W = delta G - 2" using dW' dG' nc' eW1 vW1 fW1 by linarith
        then show ?thesis using True False by simp
      next
        assume "?k = 2"
        then have "delta ?W = delta G" using dW' dG' nc' eW1 vW1 fW1 by linarith
        then show ?thesis by simp
      qed
    next
      case nc'': False
      have eW1: "eW = eG - 1" using fe False nc'' unfolding eW_def eG_def by simp
      have "?k \<le> 1" using k1 nc'' False by blast
      then have "?k = 1" using kp by linarith
      then have "delta ?W = delta G" using dW' dG' nc' eW1 vW1 fW1 by linarith
      then show ?thesis by simp
    qed
  qed
qed

lemma genus_WalkupE_le: "z \<in> D \<Longrightarrow> genus (WalkupE G z) \<le> genus G"
  using delta_WalkupE[of z] by (auto simp: genus_delta intro: div_le_mono nat_mono)

lemma genus_WalkupE_eq:
  "z \<in> D \<Longrightarrow> glink G z z \<or> \<not> cross_edge G z \<Longrightarrow> genus (WalkupE G z) = genus G"
  using delta_WalkupE[of z] by (auto simp: genus_delta)

lemma planar_WalkupE: "planar G \<Longrightarrow> z \<in> D \<Longrightarrow> planar (WalkupE G z)"
  using genus_WalkupE_le[of z] by (simp add: planar_def)

lemma even_genus_WalkupE: "z \<in> D \<Longrightarrow> even_genus (WalkupE G z) \<Longrightarrow> even_genus G"
  using delta_WalkupE[of z] by (auto simp: even_genus_delta)

lemma planar_WalkupN: "planar G \<Longrightarrow> z \<in> D \<Longrightarrow> planar (WalkupN G z)"
proof -
  interpret P: hypermap "permN G" by (rule hypermap_permN)
  interpret W: hypermap "WalkupE (permN G) z" by (rule P.hypermap_WalkupE)
  assume "planar G" "z \<in> D"
  then have "planar (permN G)" by (simp add: planar_permN)
  then have "planar (WalkupE (permN G) z)" using \<open>z \<in> D\<close> by (simp add: P.planar_WalkupE)
  then show ?thesis unfolding WalkupN_def by (simp add: W.planar_permF)
qed

lemma planar_WalkupF: "planar G \<Longrightarrow> z \<in> D \<Longrightarrow> planar (WalkupF G z)"
proof -
  interpret P: hypermap "permF G" by (rule hypermap_permF)
  interpret W: hypermap "WalkupE (permF G) z" by (rule P.hypermap_WalkupE)
  assume "planar G" "z \<in> D"
  then have "planar (permF G)" by (simp add: planar_permF)
  then have "planar (WalkupE (permF G) z)" using \<open>z \<in> D\<close> by (simp add: P.planar_WalkupE)
  then show ?thesis unfolding WalkupF_def by (simp add: W.planar_permN)
qed

end

end
