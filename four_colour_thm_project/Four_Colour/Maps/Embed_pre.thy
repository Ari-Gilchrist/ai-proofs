(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Embed_pre.thy
    Preembeddings (coloring.v, section Preembedding) and rlink path simplification
    (geometry.v), needed for the embedding argument of embed.v.
    Ported from G. Gonthier's Coq development.
*)
theory Embed_pre
  imports Four_Colour_Maps.Contract2 Four_Colour_Maps.Cfreducible
begin

context hypermap
begin

definition rlink_connected :: "('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "rlink_connected a \<longleftrightarrow> (\<forall>x y. a x \<longrightarrow> a y \<longrightarrow>
     (\<exists>p. path (rlink G) (n (f x)) (p @ [y]) \<and> (\<forall>z \<in> set p. a z)))"

lemma simplify_rlink:
  "path (rlink G) x p \<Longrightarrow> \<exists>p'. path (rlink G) x p' \<and> simple G p' \<and>
     lastd x p' = lastd x p \<and> (p' = [] \<longleftrightarrow> p = []) \<and> set p' \<subseteq> set p"
proof (induction "length p" arbitrary: x p rule: less_induct)
  case less
  show ?case
  proof (cases p)
    case Nil then show ?thesis by (intro exI[of _ "[]"]) (simp add: simple_def)
  next
    case (Cons y p0)
    have xy: "rlink G x y" and yp: "path (rlink G) y p0" using less.prems Cons by simp_all
    show ?thesis
    proof (cases "fband G p0 y")
      case False
      obtain q where q: "path (rlink G) y q" "simple G q" "lastd y q = lastd y p0" "q = [] \<longleftrightarrow> p0 = []"
        "set q \<subseteq> set p0" using less.hyps[of p0 y] Cons yp by auto
      have "\<not> fband G q y" using False q(5) by (auto simp: fband_def)
      then have "simple G (y # q)" using q(2) by (simp add: simple_Cons)
      moreover have "lastd x (y # q) = lastd x p"
        using q(3,4) Cons by (cases q; cases p0) auto
      ultimately show ?thesis using xy q Cons by (intro exI[of _ "y # q"]) auto
    next
      case True
      then obtain z where z: "z \<in> set p0" and yz: "cface y z" by (auto simp: fband_def)
      obtain p1 p2 where p0: "p0 = p1 @ z # p2" using split_list[OF z] by blast
      have xz: "rlink G x z" using xy rlink_cface[OF yz] by simp
      have pz: "path (rlink G) z p2" using yp p0 by simp
      have "length (z # p2) < length p" using Cons p0 by simp
      then obtain q where q: "path (rlink G) x q" "simple G q" "lastd x q = lastd x (z # p2)"
        "q = [] \<longleftrightarrow> z # p2 = []" "set q \<subseteq> set (z # p2)"
        using less.hyps[of "z # p2" x] xz pz by auto
      have "lastd x (z # p2) = lastd x p" using Cons p0 by (cases p2) auto
      moreover have "set (z # p2) \<subseteq> set p" using Cons p0 by auto
      ultimately show ?thesis using q Cons by (intro exI[of _ q]) auto
    qed
  qed
qed

end

section \<open>Preembeddings\<close>

definition edge_central :: "'a hypermap \<Rightarrow> 'b hypermap \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> bool" where
  "edge_central G G' h x \<longleftrightarrow> h (edge G x) = edge G' (h x)"

lemma edge_central_edge:
  assumes "hypermap G" "hypermap G'" "plain G" "plain G'"
  shows "edge_central G G' h (edge G x) \<longleftrightarrow> edge_central G G' h x"
  unfolding edge_central_def
  using hypermap.plain_eq[OF assms(1,3)] hypermap.plain_eq[OF assms(2,4)] by metis

definition preembedding :: "'a hypermap \<Rightarrow> 'b hypermap \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "preembedding G G' A h \<longleftrightarrow>
     (\<forall>x \<in> A. h (face G x) = face G' (h x)) \<and>
     (\<forall>x \<in> A. order (face G') (h x) = order (face G) x) \<and>
     (\<forall>x \<in> A. \<exists>y. fconnect (face G) x y \<and> edge_central G G' h y) \<and>
     hypermap.rlink_connected G (\<lambda>x. x \<in> A \<and> edge_central G G' h x)"

lemma (in hypermap) preembedding_simple_path:
  assumes pe: "preembedding G G' A h" and Af: "\<And>u. u \<in> A \<longleftrightarrow> f u \<in> A"
    and exA: "e x \<in> A" and yA: "y \<in> A"
  shows "\<exists>p. path (rlink G) x p \<and> cface (lastd x p) y \<and> p \<noteq> [] \<and> simple G p \<and>
           (\<forall>z \<in> set p. z \<in> A \<and> edge_central G G' h z)"
proof -
  define B where "B z \<longleftrightarrow> z \<in> A \<and> edge_central G G' h z" for z
  have cov: "\<forall>u \<in> A. \<exists>v. cface u v \<and> edge_central G G' h v"
    and rc: "rlink_connected B" using pe by (simp_all add: preembedding_def B_def[abs_def])
  have Acl: "v \<in> A" if "u \<in> A" "cface u v" for u v
    using that(2,1) by (induction rule: fconnect_induct) (use Af in auto)
  obtain z where exz: "cface (e x) z" and zc: "edge_central G G' h z" using cov exA by blast
  obtain t where yt: "cface y t" and tc: "edge_central G G' h t" using cov yA by blast
  have Bz: "B z" using Acl[OF exA exz] zc by (simp add: B_def)
  have Bt: "B t" using Acl[OF yA yt] tc by (simp add: B_def)
  obtain p where pp: "path (rlink G) (n (f z)) (p @ [t])" and Bp: "\<forall>w \<in> set p. B w"
    using rc[unfolded rlink_connected_def, rule_format, OF Bz Bt] by blast
  have xpt: "path (rlink G) x (p @ [t])"
  proof (cases p)
    case Nil
    then have "rlink G (n (f z)) t" using pp by simp
    then have "cface z t" by (simp add: rlink_def faceK)
    then have "rlink G x t" using fconnect_trans[OF exz] by (simp add: rlink_def)
    then show ?thesis using Nil by simp
  next
    case (Cons w p')
    then have "rlink G (n (f z)) w" and rest: "path (rlink G) w (p' @ [t])" using pp by simp_all
    then have "cface z w" by (simp add: rlink_def faceK)
    then have "rlink G x w" using exz by (simp add: rlink_def) (rule fconnect_trans)
    then show ?thesis using Cons rest by simp
  qed
  obtain q where q: "path (rlink G) x q" "simple G q" "lastd x q = lastd x (p @ [t])"
    "q = [] \<longleftrightarrow> p @ [t] = []" "set q \<subseteq> set (p @ [t])"
    using simplify_rlink[OF xpt] by blast
  have "cface (lastd x q) y" using q(3) yt F.fconnect_sym by simp
  moreover have "\<forall>w \<in> set q. w \<in> A \<and> edge_central G G' h w" using q(5) Bp Bt by (auto simp: B_def)
  ultimately show ?thesis using q by (intro exI[of _ q]) simp
qed

section \<open>Disk lemmas for ring comparisons\<close>

context snip_ring
begin

lemma diskN_dlink: "y \<in> diskN \<Longrightarrow> dlink y z \<Longrightarrow> z \<in> D \<Longrightarrow> z \<in> diskN"
proof -
  assume y: "y \<in> diskN" and yz: "dlink y z" and zD: "z \<in> D"
  obtain w where w: "w \<in> set r" and c: "connect dlink (inv n w) y" using y by (auto simp: diskN_def dconnect_def)
  have "connect dlink (inv n w) z" using c yz by (rule rtranclp.rtrancl_into_rtrancl)
  then show ?thesis using w zD by (auto simp: diskN_def dconnect_def)
qed

lemma rlink_diskF:
  assumes y: "y \<in> diskN" and yz: "rlink G y z" and nb: "\<not> fband G r z"
  shows "z \<in> diskF"
proof -
  have yD: "y \<in> D" using y diskN_D by blast
  have "f (e y) \<in> diskN" using diskN_node[of "f (e y)"] y yD by (simp add: edgeK)
  moreover have "cface (f (e y)) z" using yz by (simp add: rlink_def)
  moreover have "\<not> fband G r (f (e y))" using nb fband_cface[OF \<open>cface (f (e y)) z\<close>] by simp
  ultimately have fF: "f (e y) \<in> diskF" by (simp add: diskF_def)
  have "cface (f (e y)) z" using yz by (simp add: rlink_def)
  then show ?thesis by (induction rule: fconnect_induct) (simp_all add: fF diskF_face)
qed

lemma diskF_cface: "x \<in> diskF \<Longrightarrow> cface x y \<Longrightarrow> y \<in> diskF"
proof -
  assume xF: "x \<in> diskF" and xy: "cface x y"
  from xy show ?thesis by (induction rule: fconnect_induct) (simp_all add: xF diskF_face)
qed

lemma rlink_back:
  assumes yz: "rlink G y z" and zN: "z \<in> diskN" and nb: "\<not> fband G r z" and yD: "y \<in> D"
  shows "y \<in> diskN"
proof -
  have zF: "z \<in> diskF" using zN nb by (simp add: diskF_def)
  have "cface z (e y)" using yz F.fconnect_sym by (simp add: rlink_def)
  then have "e y \<in> diskF" by (rule diskF_cface[OF zF])
  then have "f (e y) \<in> diskF" by (rule diskF_face)
  then have "f (e y) \<in> diskN" by (simp add: diskF_def)
  then show ?thesis using diskN_node[of "f (e y)"] yD by (simp add: edgeK)
qed

lemma walk_back:
  "path (rlink G) a l \<Longrightarrow> lastd a l \<in> diskN \<Longrightarrow> (\<forall>w \<in> set l. \<not> fband G r w) \<Longrightarrow> a \<in> D \<Longrightarrow> a \<in> diskN"
proof (induction l arbitrary: a)
  case Nil then show ?case by simp
next
  case (Cons b l)
  have ab: "rlink G a b" and bl: "path (rlink G) b l" using Cons.prems(1) by simp_all
  have bD: "b \<in> D" using ab Cons.prems(4) by (auto simp: rlink_def dest: F.fconnect_in_D)
  have bN: "b \<in> diskN" by (rule Cons.IH[OF bl]) (use Cons.prems bD in auto)
  show ?case by (rule rlink_back[OF ab bN _ Cons.prems(4)]) (use Cons.prems(3) in simp)
qed

lemma walk_diskN:
  "path (rlink G) y l \<Longrightarrow> y \<in> diskN \<Longrightarrow> (\<forall>w \<in> set l. \<not> fband G r w) \<Longrightarrow> \<forall>w \<in> set l. w \<in> diskN"
proof (induction l arbitrary: y)
  case Nil then show ?case by simp
next
  case (Cons w l)
  have "w \<in> diskF" using rlink_diskF[OF Cons.prems(2)] Cons.prems(1,3) by simp
  then have wN: "w \<in> diskN" by (simp add: diskF_def)
  then show ?case using Cons.IH[of w] Cons.prems by simp
qed

end

lemma disk_sub:
  assumes Q: "snip_ring G q" and X: "snip_ring G xp"
    and a: "\<And>z. z \<in> set q \<Longrightarrow> z \<in> snip_ring.diskN G xp"
    and b: "\<And>y. y \<in> set xp \<Longrightarrow> y \<in> snip_ring.diskN G q \<Longrightarrow> y \<in> set q"
  shows "snip_ring.diskN G q \<subseteq> snip_ring.diskN G xp"
proof
  interpret Q: snip_ring G q by (rule Q)
  interpret X: snip_ring G xp by (rule X)
  fix t assume t: "t \<in> Q.diskN"
  obtain z where z: "z \<in> set q" and c: "connect Q.dlink (inv Q.n z) t"
    using t by (auto simp: Q.diskN_def Q.dconnect_def)
  have zD: "z \<in> Q.D" using z Q.r_D by blast
  have "t \<in> Q.D" using t Q.diskN_D by blast
  have base: "inv Q.n z \<in> X.diskN \<and> inv Q.n z \<in> Q.diskN"
  proof -
    have izD: "inv Q.n z \<in> Q.D" using zD Q.N.closed[of "inv Q.n z"] by simp
    have "Q.n (inv Q.n z) = z" by simp
    then show ?thesis using a[OF z] Q.r_diskN[OF z] X.diskN_node[OF izD] Q.diskN_node[OF izD] by simp
  qed
  have "t \<in> X.diskN \<and> t \<in> Q.diskN" using c base
  proof (induction rule: rtranclp_induct)
    case base then show ?case by simp
  next
    case (step y w)
    have yq: "y \<notin> set q" and cl: "clink G y w" using step.hyps(2) by (simp_all add: Q.dlink_def)
    have yD: "y \<in> Q.D" using step.IH step.prems Q.diskN_D by blast
    have wD: "w \<in> Q.D" using cl yD by (auto simp: clink_def)
    have IH: "y \<in> X.diskN" "y \<in> Q.diskN" using step.IH step.prems by blast+
    have wQ: "w \<in> Q.diskN" by (rule Q.diskN_dlink[OF IH(2) step.hyps(2) wD])
    have "y \<notin> set xp" using b[of y] IH(2) yq by blast
    then have "X.dlink y w" using cl by (simp add: X.dlink_def)
    then have "w \<in> X.diskN" by (rule X.diskN_dlink[OF IH(1) _ wD])
    then show ?case using wQ by blast
  qed
  then show "t \<in> X.diskN" by blast
qed

end
