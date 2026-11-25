(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Contract2.thy
    Contract colourings exist for valid contracts (the theorem contract_coloring of contract.v).
    Ported from G. Gonthier's Coq development (contract.v).
*)
theory Contract2
  imports Four_Colour_Maps.Contract
begin

section \<open>List helpers\<close>

lemma cycle_rot: "cycle r (rot k s) = cycle r s"
  by (cases "k \<le> length s") (simp_all add: rot_rotate cycle_rotate rot_oversize)

lemma (in hypermap) simple_rot': "simple G (rot k s) = simple G s"
  by (cases "k \<le> length s") (simp_all add: rot_rotate simple_rotate rot_oversize)

lemma path_conv:
  "path R a l \<Longrightarrow> (\<And>c d. R c d \<Longrightarrow> \<not> P d \<Longrightarrow> c \<in> S \<Longrightarrow> d \<in> S \<Longrightarrow> R' c d) \<Longrightarrow>
   (\<forall>b \<in> set l. \<not> P b) \<Longrightarrow> a \<in> S \<Longrightarrow> set l \<subseteq> S \<Longrightarrow> path R' a l"
  by (induction l arbitrary: a) auto

lemma next_in_last:
  assumes d: "distinct (a # t)" and y: "y \<in> set (a # t)" and ny: "next_in (a # t) y = a"
  shows "y = last (a # t)"
proof -
  have "y = prev_in (a # t) a" using prev_next_in[OF d y] ny by simp
  also have "\<dots> = last (a # t)"
    by (simp add: prev_in_def last_conv_nth)
  finally show ?thesis .
qed

section \<open>Deleting an edge pair by two face Walkups\<close>

lemma WalkupF_simps:
  "darts (WalkupF G z) = darts G - {z}" "edge (WalkupF G z) = skip z (edge G)"
  "node (WalkupF G z) = skip z (node G)" "face (WalkupF G z) = skip_edge (permF G) z"
  by (simp_all add: WalkupF_def)

locale cw = hypermap H for H :: "'a hypermap" +
  fixes x :: 'a
  assumes xD: "x \<in> D" and plainH: "plain H" and bridgelessH: "bridgeless H"
begin

abbreviation G1 where "G1 \<equiv> WalkupF H x"
abbreviation G2 where "G2 \<equiv> WalkupF G1 (e x)"
abbreviation D2 where "D2 \<equiv> D - {x, e x}"

lemma ee [simp]: "e (e x) = x" using plainH by (rule plain_eq)
lemma ex_neq: "e x \<noteq> x" using plainH xD by (rule plain_neq)

lemma hG1: "hypermap G1" by (rule hypermap_WalkupF)
lemma hG2: "hypermap G2" by (rule hypermap.hypermap_WalkupF[OF hG1])

lemma darts2: "darts G2 = D2" by (auto simp: WalkupF_def)
lemma darts1: "darts G1 = D - {x}" by (rule WalkupF_simps(1))
lemma eeH [simp]: "e (e y) = y" using plainH by (rule plain_eq)

lemma edge2: "w \<in> D2 \<Longrightarrow> edge G2 w = e w"
proof -
  assume w: "w \<in> D2"
  have ew: "e w \<noteq> x" "e w \<noteq> e x" using w by (metis DiffE eeH insertCI)+
  have e1: "edge G1 = skip x e" by (simp add: WalkupF_def)
  have e2: "edge G2 = skip (e x) (edge G1)" by (simp add: WalkupF_def)
  have "edge G1 w = e w" using w ew by (simp add: e1 skip_def)
  then show ?thesis using w ew by (simp add: e2 skip_def)
qed

lemma node2_conn: "w \<in> D2 \<Longrightarrow> fconnect (node G2) w w' \<longleftrightarrow> cnode w w' \<and> w' \<noteq> x \<and> w' \<noteq> e x"
proof -
  assume w: "w \<in> D2"
  interpret P1: hypermap G1 by (rule hG1)
  have "fconnect (node G2) w w' \<longleftrightarrow> fconnect (node G1) w w' \<and> w' \<noteq> e x"
    using P1.N.fconnect_skip[of w "e x" w'] w by (simp add: WalkupF_simps)
  also have "fconnect (node G1) w w' \<longleftrightarrow> cnode w w' \<and> w' \<noteq> x"
    using N.fconnect_skip[of w x w'] w by (simp add: WalkupF_simps)
  finally show ?thesis by auto
qed

text \<open>Faces: the faces of x and e x merge.\<close>

definition xR :: "'a \<Rightarrow> bool" where "xR y \<longleftrightarrow> cface y x \<or> cface y (e x)"

lemma face1_conn:
  assumes y: "y \<in> D" "y \<noteq> x"
  shows "fconnect (face G1) y y' \<longleftrightarrow> y' \<noteq> x \<and> (if xR y then xR y' else cface y y')"
proof -
  interpret P: hypermap "permF H" by (rule hypermap_permF)
  have ed: "P.edom x w \<longleftrightarrow> xR w" for w
    unfolding P.edom_def xR_def by simp
  have nc: "\<not> cross_edge (permF H) x"
    using bridgelessH xD by (simp add: cross_edge_def bridgeless_def)
  interpret P1: hypermap G1 by (rule hG1)
  have yD1: "y \<in> darts G1" using y by (simp add: darts1)
  show ?thesis
  proof (cases "xR y")
    case True
    show ?thesis
    proof (cases "y' = x")
      case True
      have "\<not> fconnect (face G1) y x" using P1.F.fconnect_in_D[of y x] yD1 by (auto simp: darts1)
      then show ?thesis using True by simp
    next
      case False
      then show ?thesis using P.cskip_edge_merge[OF nc _ _ y(2) False] True ed xD
        by (simp add: WalkupF_simps)
    qed
  next
    case False
    have "fconnect (skip_edge (permF H) x) y y' \<longleftrightarrow> fconnect (face H) y y'"
      using P.same_cskip_edge[of x y y'] False ed y(2) by simp
    moreover have "\<not> (cface y x)" using False by (simp add: xR_def)
    ultimately show ?thesis using False by (auto simp: WalkupF_simps)
  qed
qed

lemma face2_eq: "face G2 = skip (e x) (face G1)"
proof -
  interpret P1: hypermap "permF G1" by (rule hypermap.hypermap_permF[OF hG1])
  have e1: "edge G1 (e x) = e x" using ex_neq by (simp add: WalkupF_def skip_def)
  have g: "glink (permF G1) (e x) (e x)" using e1 by (simp add: glink_def)
  have "face G2 = skip_edge (permF G1) (e x)" by (simp add: WalkupF_def)
  also have "\<dots> = skip (e x) (face G1)" using P1.glink_fp_skip_edge[OF g] by (simp add: fun_eq_iff)
  finally show ?thesis .
qed

lemma face2_conn:
  assumes w: "w \<in> D2"
  shows "fconnect (face G2) w w' \<longleftrightarrow> w' \<noteq> x \<and> w' \<noteq> e x \<and> (if xR w then xR w' else cface w w')"
proof -
  interpret P1: hypermap G1 by (rule hG1)
  have "fconnect (face G2) w w' \<longleftrightarrow> fconnect (face G1) w w' \<and> w' \<noteq> e x"
    unfolding face2_eq using P1.F.fconnect_skip[of w "e x" w'] w by simp
  also have "\<dots> \<longleftrightarrow> w' \<noteq> x \<and> (if xR w then xR w' else cface w w') \<and> w' \<noteq> e x"
    using face1_conn[of w w'] w by simp
  finally show ?thesis by auto
qed

lemma xR_face: "xR (f y) \<longleftrightarrow> xR y" by (simp add: xR_def)

lemma xR_cface: "cface y z \<Longrightarrow> xR y \<longleftrightarrow> xR z"
  unfolding xR_def using fconnect_trans F.fconnect_sym by metis

lemma cw_extend:
  assumes kc: "cc_coloring G2 (filter (\<lambda>y. y \<noteq> x \<and> y \<noteq> e x) cc) k" and ccD: "set cc \<subseteq> D"
  shows "cc_colorable H (x # cc)"
proof -
  interpret P2: hypermap G2 by (rule hG2)
  define cc2 where "cc2 = filter (\<lambda>y. y \<noteq> x \<and> y \<noteq> e x) cc"
  have kf2: "k a = k b" if "fconnect (face G2) a b" for a b by (rule cc_face[OF hG2 kc[folded cc2_def] that])
  have inv: "k a = k b" if a: "a \<in> D2" and b: "b \<in> D2" and ab: "cface a b" for a b
  proof -
    have "fconnect (face G2) a b"
      using face2_conn[OF a, of b] b ab xR_cface[OF ab] by auto
    then show ?thesis by (rule kf2)
  qed
  define cX where "cX = (if \<exists>w \<in> D2. xR w then k (SOME w. w \<in> D2 \<and> xR w) else Color0)"
  define k0 where "k0 y = (if xR y then cX else ext_col H D2 k Color0 y)" for y
  have k0D2: "k0 y = k y" if yD2: "y \<in> D2" for y
  proof (cases "xR y")
    case True
    have ex: "\<exists>w. w \<in> D2 \<and> xR w" using yD2 True by blast
    define w where "w = (SOME w. w \<in> D2 \<and> xR w)"
    have w: "w \<in> D2 \<and> xR w" unfolding w_def by (rule someI_ex[OF ex])
    have "fconnect (face G2) w y" using face2_conn[of w y] w yD2 True by auto
    then have "k w = k y" by (rule kf2)
    then show ?thesis using True yD2 w by (auto simp: k0_def cX_def w_def)
  next
    case False
    then show ?thesis using ext_col_old[OF inv yD2] by (simp add: k0_def)
  qed
  have "cc_coloring H (x # cc) k0"
    unfolding cc_coloring_def
  proof (intro conjI ballI)
    fix y assume yD: "y \<in> D"
    show "k0 (f y) = k0 y" using xR_face[of y] ext_col_face[of D2 k Color0 y] by (simp add: k0_def)
    show "(k0 (e y) = k0 y) \<longleftrightarrow> y \<in> set (insertE H (x # cc))"
    proof (cases "y = x \<or> y = e x")
      case True
      have "xR x" "xR (e x)" by (simp_all add: xR_def)
      then have "k0 (e y) = k0 y" using True by (auto simp: k0_def)
      then show ?thesis using True by (auto simp: set_insertE)
    next
      case False
      then have yD2: "y \<in> D2" using yD by simp
      have eyD2: "e y \<in> D2"
      proof -
        have "e y \<noteq> x" using False eeH[of y] by metis
        moreover have "e y \<noteq> e x" using False by simp
        ultimately show ?thesis using yD by simp
      qed
      have "k0 (e y) = k0 y \<longleftrightarrow> k (edge G2 y) = k y" using k0D2[OF yD2] k0D2[OF eyD2] edge2[OF yD2] by simp
      also have "\<dots> \<longleftrightarrow> y \<in> set cc2 \<union> edge G2 ` set cc2"
        using cc_edge[OF kc[folded cc2_def]] yD2 darts2 by simp
      also have "\<dots> \<longleftrightarrow> y \<in> set (insertE H (x # cc))"
      proof -
        have cc2D: "set cc2 \<subseteq> D2" using ccD by (auto simp: cc2_def)
        have img: "edge G2 ` set cc2 = e ` set cc2"
          by (rule image_cong[OF refl]) (use edge2 cc2D in blast)
        show ?thesis using False unfolding img by (auto simp: cc2_def set_insertE image_def)
      qed
      finally show ?thesis .
    qed
  qed
  then show ?thesis by (auto simp: cc_colorable_def)
qed

lemma edge2_D2: "w \<in> D2 \<Longrightarrow> e w \<in> D2"
proof -
  assume w: "w \<in> D2"
  have "e w \<noteq> x" using w eeH[of w] by (metis DiffE insertCI)
  moreover have "e w \<noteq> e x" using w by auto
  ultimately show ?thesis using w by simp
qed

lemma planar2: "planar H \<Longrightarrow> planar G2"
proof -
  assume pH: "planar H"
  have p1: "planar G1" by (rule planar_WalkupF[OF pH xD])
  have "e x \<in> darts G1" using ex_neq xD by (simp add: darts1)
  then show ?thesis by (rule hypermap.planar_WalkupF[OF hG1 p1])
qed

lemma plain2: "plain G2"
proof -
  interpret P2: hypermap G2 by (rule hG2)
  have "edge G2 (edge G2 w) = w \<and> edge G2 w \<noteq> w" if w: "w \<in> D2" for w
  proof -
    have a: "edge G2 w = e w" by (rule edge2[OF w])
    have b: "edge G2 (e w) = e (e w)" by (rule edge2[OF edge2_D2[OF w]])
    have "e w \<noteq> w" using plain_neq[OF plainH] w by simp
    then show ?thesis using a b by simp
  qed
  then show ?thesis unfolding plain_def P2.plainP darts2 by blast
qed

lemma precubic2: "precubic H \<Longrightarrow> precubic G2"
proof -
  assume pc: "precubic H"
  interpret P2: hypermap G2 by (rule hG2)
  show ?thesis unfolding precubic_def
  proof
    fix w assume w: "w \<in> darts G2"
    then have wD2: "w \<in> D2" by (simp add: darts2)
    have "cyc (node G2) w \<subseteq> cyc n w"
    proof
      fix y assume "y \<in> cyc (node G2) w"
      then have "fconnect (node G2) w y" by (simp only: P2.N.in_cyc_iff)
      then have "cnode w y" using node2_conn[OF wD2] by blast
      then show "y \<in> cyc n w" by (simp only: N.in_cyc_iff)
    qed
    then have "order (node G2) w \<le> order n w"
      by (simp add: order_def card_mono)
    also have "\<dots> \<le> 3" using pc wD2 by (simp add: precubic_def)
    finally show "order (node G2) w \<le> 3" .
  qed
qed

lemma scycle2H:
  assumes "a \<in> D" "b \<in> D"
  shows "scycle H (rlink H) [a, b] \<longleftrightarrow> rlink H a b \<and> rlink H b a \<and> \<not> cface a b"
  using assms by (auto simp: scycle_def cycle_Cons simple_def F.cyc_eq_iff)

lemma bridgeless2:
  assumes noring: "\<And>p. \<not> (contract_ring H (x # cc) p \<and> set p \<subseteq> D)"
  shows "bridgeless G2"
  unfolding bridgeless_def
proof (intro ballI notI)
  fix w assume w: "w \<in> darts G2" and wF: "fconnect (face G2) w (edge G2 w)"
  have wD2: "w \<in> D2" using w by (simp add: darts2)
  have wF': "e w \<noteq> x \<and> e w \<noteq> e x \<and> (if xR w then xR (e w) else cface w (e w))"
    using face2_conn[OF wD2, of "e w"] wF edge2[OF wD2] by simp
  have brH: "\<not> cface y (e y)" if "y \<in> D" for y using bridgelessH that by (simp add: bridgeless_def)
  have wD: "w \<in> D" using wD2 by simp
  have xex: "\<not> cface x (e x)" by (rule brH[OF xD])
  show False
  proof (cases "xR w")
    case False then show ?thesis using wF' brH[OF wD] by simp
  next
    case True
    then have xRe: "xR (e w)" using wF' by simp
    show ?thesis
    proof (cases "cface w x")
      case wx: True
      have "\<not> cface (e w) x"
      proof
        assume "cface (e w) x"
        then have "cface w (e w)" using fconnect_trans[OF wx F.fconnect_sym] by blast
        then show False using brH[OF wD] by simp
      qed
      then have ewex: "cface (e w) (e x)" using xRe by (simp add: xR_def)
      have "contract_ring H (x # cc) [w, e x]"
        unfolding contract_ring_def
      proof (intro conjI)
        have "rlink H w (e x)" "rlink H (e x) w" using ewex F.fconnect_sym[OF wx] by (simp_all add: rlink_def)
        moreover have "\<not> cface w (e x)"
        proof
          assume "cface w (e x)"
          then have "cface x (e x)" by (rule fconnect_trans[OF F.fconnect_sym[OF wx]])
          then show False using xex by simp
        qed
        ultimately show "scycle H (rlink H) [w, e x]" using scycle2H[OF wD] xD by simp
        show "proper_ring H [w, e x]" using wD2 by simp
        show "set (tl [w, e x]) \<subseteq> set (insertE H (x # cc))" by simp
      qed
      then show False using noring[of "[w, e x]"] wD xD by simp
    next
      case nwx: False
      then have wex: "cface w (e x)" using True by (simp add: xR_def)
      have "\<not> cface (e w) (e x)"
      proof
        assume "cface (e w) (e x)"
        then have "cface w (e w)" using fconnect_trans[OF wex F.fconnect_sym] by blast
        then show False using brH[OF wD] by simp
      qed
      then have ewx: "cface (e w) x" using xRe by (simp add: xR_def)
      have "contract_ring H (x # cc) [w, x]"
        unfolding contract_ring_def
      proof (intro conjI)
        have "rlink H w x" "rlink H x w" using ewx F.fconnect_sym[OF wex] by (simp_all add: rlink_def)
        then show "scycle H (rlink H) [w, x]" using scycle2H[OF wD xD] nwx by simp
        have "e w \<noteq> x"
        proof
          assume "e w = x"
          then have "w = e x" using eeH[of w] by simp
          then show False using wD2 by simp
        qed
        then show "proper_ring H [w, x]" by simp
        show "set (tl [w, x]) \<subseteq> set (insertE H (x # cc))" by simp
      qed
      then show False using noring[of "[w, x]"] wD xD by simp
    qed
  qed
qed

lemma contract_rot:
  assumes Ur: "scycle H (rlink H) r" and pr: "proper_ring H r" and rD: "set r \<subseteq> D"
    and w: "w \<in> set r" and cc: "\<And>y. y \<in> set r \<Longrightarrow> y \<noteq> w \<Longrightarrow> y \<in> set (insertE H cc0)"
  shows "\<exists>r'. contract_ring H cc0 r' \<and> set r' \<subseteq> D"
proof -
  have dr: "distinct r" using Ur simple_distinct by (simp add: scycle_def)
  obtain b where b: "b \<in> set r" "b \<noteq> w"
  proof -
    have "2 \<le> length r" using pr by (cases r rule: remdups_adj.cases) auto
    then obtain c1 c2 t where "r = c1 # c2 # t" by (cases r rule: remdups_adj.cases) auto
    then show thesis using that dr by (cases "c1 = w") auto
  qed
  obtain i p1 p2 where rt: "rot i r = w # p1 @ b # p2" using rot_to_arc[OF dr w b(1) b(2)[symmetric]] by blast
  have Ur': "scycle H (rlink H) (rot i r)" using Ur by (simp add: scycle_def cycle_rot simple_rot')
  have pr': "proper_ring H (rot i r)" using pr proper_ring_rot[OF plainH] by simp
  have dr': "distinct (w # p1 @ b # p2)" using rt dr by (metis distinct_rot)
  have "set (tl (rot i r)) \<subseteq> set (insertE H cc0)"
  proof
    fix y assume "y \<in> set (tl (rot i r))"
    then have yt: "y \<in> set (p1 @ b # p2)" using rt by simp
    have sr: "set r = set (w # p1 @ b # p2)" using rt by (metis set_rot)
    have "y \<in> set r" using yt sr by auto
    moreover have "y \<noteq> w" using dr' yt by auto
    ultimately show "y \<in> set (insertE H cc0)" by (rule cc)
  qed
  then show ?thesis using Ur' pr' rD by (intro exI[of _ "rot i r"]) (simp add: contract_ring_def)
qed

lemma lift_ring:
  assumes noring: "\<And>p. \<not> (contract_ring H (x # cc) p \<and> set p \<subseteq> D)"
    and ccD: "set cc \<subseteq> D"
    and cr: "contract_ring G2 (filter (\<lambda>y. y \<noteq> x \<and> y \<noteq> e x) cc) p" and pD: "set p \<subseteq> darts G2"
  shows False
proof -
  interpret P2: hypermap G2 by (rule hG2)
  define cc2 where "cc2 = filter (\<lambda>y. y \<noteq> x \<and> y \<noteq> e x) cc"
  have Up: "scycle G2 (rlink G2) p" and pr2: "proper_ring G2 p" and ccp: "set (tl p) \<subseteq> set (insertE G2 cc2)"
    using cr by (simp_all add: contract_ring_def cc2_def)
  have pD2: "set p \<subseteq> D2" using pD by (simp add: darts2)
  have pDH: "set p \<subseteq> D" using pD2 by auto
  have dp: "distinct p" using Up P2.simple_distinct by (simp add: scycle_def)
  have cycp: "cycle (rlink G2) p" using Up by (simp add: scycle_def)
  have simp2: "a = b" if "a \<in> set p" "b \<in> set p" "fconnect (face G2) a b" for a b
    using P2.simple_cface[of p a b] Up that by (simp add: scycle_def)
  have rl2: "rlink G2 a b \<longleftrightarrow> (if xR (e a) then xR b else rlink H a b)" if a: "a \<in> D2" and b: "b \<in> D2" for a b
    using face2_conn[OF edge2_D2[OF a], of b] b edge2[OF a] by (simp add: rlink_def)
  have simpH: "a = b" if a: "a \<in> set p" and b: "b \<in> set p" and ab: "cface a b" for a b
  proof -
    have aD2: "a \<in> D2" and bD2: "b \<in> D2" using a b pD2 by auto
    have "fconnect (face G2) a b \<longleftrightarrow> b \<noteq> x \<and> b \<noteq> e x \<and> (if xR a then xR b else cface a b)"
      by (rule face2_conn[OF aD2])
    then have "fconnect (face G2) a b" using bD2 ab xR_cface[OF ab] by auto
    then show ?thesis by (rule simp2[OF a b])
  qed
  have insH: "y \<in> set (insertE H (x # cc))" if "y \<in> set (insertE G2 cc2)" for y
  proof -
    have cc2D: "set cc2 \<subseteq> D2" using ccD by (auto simp: cc2_def)
    from that obtain z where z: "z \<in> set cc2" and "y = z \<or> y = edge G2 z" by (auto simp: set_insertE)
    then have "y = z \<or> y = e z" using edge2 cc2D by blast
    then show ?thesis using z by (auto simp: cc2_def set_insertE)
  qed
  have tlH: "y \<in> set (insertE H (x # cc))" if "y \<in> set p" "y \<noteq> hd p" for y
    using that ccp insH dp by (cases p) auto
  have brH: "\<not> cface y (e y)" if "y \<in> D" for y using bridgelessH that by (simp add: bridgeless_def)
  show False
  proof (cases "\<forall>a \<in> set p. rlink H a (next_in p a)")
    case True
    have "cycle (rlink H) p" by (rule cycle_from_next_rel[OF dp]) (use True in blast)
    moreover have "simple H p" unfolding simple_iff using dp simpH by blast
    ultimately have UpH: "scycle H (rlink H) p" by (simp add: scycle_def)
    have prH: "proper_ring H p"
    proof (cases p rule: remdups_adj.cases)
      case (3 a b t)
      then show ?thesis
      proof (cases t)
        case Nil then show ?thesis using pr2 3 edge2 pD2 by simp
      qed (simp_all add: proper_ring_def)
    qed (use pr2 in simp_all)
    have "p \<noteq> []" using pr2 by (cases p) auto
    then have "hd p \<in> set p" by simp
    then obtain r' where "contract_ring H (x # cc) r' \<and> set r' \<subseteq> D"
      using contract_rot[OF UpH prH pDH, of "hd p" "x # cc"] tlH by blast
    then show False using noring by blast
  next
    case False
    then obtain w0 where w0p: "w0 \<in> set p" and nl: "\<not> rlink H w0 (next_in p w0)" by blast
    define w1 where "w1 = next_in p w0"
    have w1p: "w1 \<in> set p" using next_in_mem[OF w0p] by (simp add: w1_def)
    have w0D2: "w0 \<in> D2" and w1D2: "w1 \<in> D2" using w0p w1p pD2 by auto
    have "rlink G2 w0 w1" using cycle_next_in_rel[OF cycp w0p] by (simp add: w1_def)
    then have xRe: "xR (e w0)" and xR1: "xR w1" using rl2[OF w0D2 w1D2] nl by (auto simp: w1_def split: if_splits)
    obtain x0 where x0: "x0 = x \<or> x0 = e x" and ex0: "cface (e w0) x0" using xRe by (auto simp: xR_def)
    have nl': "\<not> cface (e w0) w1" using nl by (simp add: rlink_def w1_def)
    have w1x1: "cface w1 (e x0)"
    proof -
      obtain x1 where x1: "x1 = x \<or> x1 = e x" and wx1: "cface w1 x1" using xR1 by (auto simp: xR_def)
      have "x1 \<noteq> x0"
      proof
        assume "x1 = x0"
        then have "cface (e w0) x1" using ex0 by simp
        then have "cface (e w0) w1" by (rule fconnect_trans[OF _ F.fconnect_sym[OF wx1]])
        then show False using nl' by simp
      qed
      then have "x1 = e x0" using x0 x1 by auto
      then show ?thesis using wx1 by simp
    qed
    have oth: "\<not> xR a" if "a \<in> set p" "a \<noteq> w1" for a
    proof
      assume "xR a"
      then have "fconnect (face G2) w1 a" using face2_conn[OF w1D2, of a] xR1 that pD2 by auto
      then show False using simp2[OF w1p that(1)] that(2) by simp
    qed
    obtain b where b: "b \<in> set p" "b \<noteq> w1"
    proof -
      have "2 \<le> length p" using pr2 by (cases p rule: remdups_adj.cases) auto
      then obtain c1 c2 t where "p = c1 # c2 # t" by (cases p rule: remdups_adj.cases) auto
      then show thesis using that dp by (cases "c1 = w1") auto
    qed
    obtain i p1 p2 where rt: "rot i p = w1 # p1 @ b # p2" using rot_to_arc[OF dp w1p b(1) b(2)[symmetric]] by blast
    define t where "t = p1 @ b # p2"
    have st: "rot i p = w1 # t" using rt by (simp add: t_def)
    have ds: "distinct (w1 # t)" using st dp by (metis distinct_rot)
    have ss: "set (w1 # t) = set p" using st by (metis set_rot)
    have w0last: "w0 = last (w1 # t)"
    proof -
      have "next_in (rot i p) w0 = w1" using next_in_rot[OF dp w0p, of i] by (simp add: w1_def)
      then have nw: "next_in (w1 # t) w0 = w1" using st by simp
      have w0s: "w0 \<in> set (w1 # t)" using w0p ss by simp
      show ?thesis by (rule next_in_last[OF ds w0s nw])
    qed
    have tx: "\<not> xR a" if "a \<in> set t" for a using oth that ss ds by auto
    have pth2: "path (rlink G2) w1 t"
      using cycp unfolding cycle_rot[of _ i p, symmetric] st by (simp add: cycle_Cons)
    have tD2: "set t \<subseteq> D2" using ss pD2 by auto
    have pthH: "path (rlink H) w1 t"
    proof (rule path_conv[OF pth2, where P = xR and S = D2])
      fix c d assume cd: "rlink G2 c d" and nd: "\<not> xR d" and cD: "c \<in> D2" and dD: "d \<in> D2"
      show "rlink H c d" using cd rl2[OF cD dD] nd by (auto split: if_splits)
    qed (use tx w1D2 tD2 in auto)
    define q where "q = x0 # w1 # t"
    have x0D: "x0 \<in> D" using x0 xD by auto
    have x0n: "x0 \<notin> set (w1 # t)" using x0 ss pD2 by auto
    have cycq: "cycle (rlink H) q"
    proof -
      have r1: "rlink H x0 w1" using w1x1 F.fconnect_sym by (simp add: rlink_def)
      have r2: "rlink H (last (w1 # t)) x0" using ex0 w0last by (simp add: rlink_def)
      show ?thesis using r1 r2 pthH by (simp add: q_def cycle_Cons)
    qed
    have simq: "simple H q" unfolding simple_iff
    proof
      show "distinct q" using ds x0n by (simp add: q_def)
      show "\<forall>a \<in> set q. \<forall>b \<in> set q. cface a b \<longrightarrow> a = b"
      proof (intro ballI impI)
        fix a b assume a: "a \<in> set q" and b: "b \<in> set q" and ab: "cface a b"
        have x0bad: "\<not> cface x0 c" if "c \<in> set (w1 # t)" for c
        proof
          assume xc: "cface x0 c"
          have "xR x0" using x0 by (auto simp: xR_def)
          then have "xR c" using xR_cface[OF xc] by simp
          then have "c = w1" using oth that ss by blast
          then have "cface x0 w1" using xc by simp
          then have "cface x0 (e x0)" by (rule fconnect_trans[OF _ w1x1])
          then show False using brH[OF x0D] by simp
        qed
        show "a = b"
        proof (cases "a = x0 \<or> b = x0")
          case True
          then show ?thesis using a b ab x0bad F.fconnect_sym by (auto simp: q_def)
        next
          case False
          then have "a \<in> set p" "b \<in> set p" using a b ss by (auto simp: q_def)
          then show ?thesis using simpH ab by blast
        qed
      qed
    qed
    have qD: "set q \<subseteq> D" using x0D ss pDH by (auto simp: q_def)
    have prq: "proper_ring H q" by (rule size_proper_ring) (simp add: q_def t_def)
    have "p \<noteq> []" using pr2 by (cases p) auto
    then have hp: "hd p \<in> set q" using ss by (simp add: q_def)
    have ccq: "y \<in> set (insertE H (x # cc))" if "y \<in> set q" "y \<noteq> hd p" for y
    proof (cases "y = x0")
      case True then show ?thesis using x0 by (auto simp: set_insertE)
    next
      case False then show ?thesis using that tlH ss by (auto simp: q_def)
    qed
    obtain r' where "contract_ring H (x # cc) r' \<and> set r' \<subseteq> D"
      using contract_rot[OF _ prq qD hp, of "x # cc"] cycq simq ccq by (auto simp: scycle_def)
    then show False using noring by blast
  qed
qed

end

section \<open>The contract colouring theorem\<close>

lemma sparse_darts:
  assumes hG: "hypermap G" and sp: "sparse G (insertE G cc)"
  shows "set cc \<subseteq> darts G"
proof
  fix z assume z: "z \<in> set cc"
  interpret hypermap G by (rule hG)
  show "z \<in> D"
  proof (rule ccontr)
    assume zD: "z \<notin> D"
    then have "e z = z" by simp
    moreover have "distinct (insertE G cc)" using sp sparse_iff[OF hG] by blast
    ultimately show False using z by (induction cc) auto
  qed
qed

lemma cc_col_gen:
  fixes H :: "'a hypermap"
  assumes "length cc \<le> m" "planar_bridgeless_plain_precubic H"
    "card (darts H) < (if cc = [] then 0 else 1) + N"
    "\<And>H' :: 'a hypermap. planar_bridgeless_plain_precubic H' \<Longrightarrow> card (darts H') < N \<Longrightarrow> four_colorable H'"
    "set cc \<subseteq> darts H" "\<And>p. \<not> (contract_ring H cc p \<and> set p \<subseteq> darts H)"
  shows "cc_colorable H cc"
  using assms
proof (induction m arbitrary: H cc)
  case 0
  then have cc: "cc = []" by simp
  then obtain k where "coloring H k" using 0 by (auto simp: four_colorable_def)
  then show ?case using cc by (auto simp: cc_colorable_def cc_coloring_def coloring_def)
next
  case (Suc m)
  show ?case
  proof (cases cc)
    case Nil
    obtain k where "coloring H k" using Suc.prems(2,3,4) Nil by (auto simp: four_colorable_def)
    then show ?thesis using Nil by (auto simp: cc_colorable_def cc_coloring_def coloring_def)
  next
    case (Cons x cc')
    have geo: "hypermap H" "planar H" "bridgeless H" "plain H" "precubic H"
      using Suc.prems(2) by (auto simp: planar_bridgeless_plain_precubic_def planar_bridgeless_plain_def
          planar_bridgeless_def)
    have xD: "x \<in> darts H" using Suc.prems(5) Cons by simp
    interpret W: cw H x using geo xD by (simp add: cw_def cw_axioms_def)
    define cc2 where "cc2 = filter (\<lambda>y. y \<noteq> x \<and> y \<noteq> edge H x) cc'"
    have noring: "\<And>p. \<not> (contract_ring H (x # cc') p \<and> set p \<subseteq> darts H)"
      using Suc.prems(6) Cons by simp
    have cc'D: "set cc' \<subseteq> darts H" using Suc.prems(5) Cons by simp
    have geo2: "planar_bridgeless_plain_precubic W.G2"
      using W.hG2 W.planar2[OF geo(2)] W.bridgeless2[OF noring] W.plain2 W.precubic2[OF geo(5)]
      by (simp add: planar_bridgeless_plain_precubic_def planar_bridgeless_plain_def planar_bridgeless_def)
    have cardH: "card (darts H) \<le> N" using Suc.prems(3) Cons by simp
    have card2: "card (darts W.G2) = card (darts H) - 2"
      using W.darts2 xD W.ex_neq W.finite_darts by (simp add: card_Diff_subset)
    have "2 \<le> card (darts H)"
    proof -
      have "{x, edge H x} \<subseteq> darts H" using xD by simp
      then have "card {x, edge H x} \<le> card (darts H)" by (rule card_mono[OF W.finite_darts])
      then show ?thesis using W.ex_neq by simp
    qed
    then have c2: "card (darts W.G2) < (if cc2 = [] then 0 else 1) + N" using card2 cardH by simp
    have cc2D: "set cc2 \<subseteq> darts W.G2" using cc'D by (auto simp: cc2_def W.darts2)
    have nr2: "\<not> (contract_ring W.G2 cc2 p \<and> set p \<subseteq> darts W.G2)" for p
      using W.lift_ring[OF noring cc'D, of p] by (auto simp: cc2_def)
    have l2: "length cc2 \<le> m" using Suc.prems(1) Cons by (simp add: cc2_def) (meson le_trans length_filter_le)
    have "cc_colorable W.G2 cc2" by (rule Suc.IH[OF l2 geo2 c2 Suc.prems(4) cc2D nr2])
    then obtain k where "cc_coloring W.G2 cc2 k" by (auto simp: cc_colorable_def)
    then show ?thesis using W.cw_extend[OF _ cc'D] Cons by (simp add: cc2_def)
  qed
qed

context birk
begin

theorem contract_coloring:
  assumes vc: "valid_contract G r cc"
  shows "cc_colorable G cc"
proof -
  have sp: "sparse G (insertE G cc)" and lc: "length cc \<in> {1, 2, 3, 4}"
    and tri: "length cc = 4 \<Longrightarrow> \<exists>x \<in> D. kernel G r x \<and> triad G (insertE G cc) x"
    using vc by (auto simp: valid_contract_def)
  have noring: "\<not> (contract_ring G cc p \<and> set p \<subseteq> D)" for p
  proof (cases "length cc = 4")
    case True
    then obtain x0 where "x0 \<in> D" "triad G (insertE G cc) x0" using tri by blast
    then show ?thesis using triad_valid[OF sp True] by blast
  next
    case False
    then show ?thesis using contract3_valid[OF sp] lc by auto
  qed
  have geo: "planar_bridgeless_plain_precubic G"
    using mce by (simp add: minimal_counter_example_def)
  have ccD: "set cc \<subseteq> D" by (rule sparse_darts[OF hypermap_axioms sp])
  have cne: "cc \<noteq> []" using lc by auto
  show ?thesis
    by (rule cc_col_gen[of cc "length cc" G "card D"]) (use geo cne minG ccD noring in auto)
qed

end

end
