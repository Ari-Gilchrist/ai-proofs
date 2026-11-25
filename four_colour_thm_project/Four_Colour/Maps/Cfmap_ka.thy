(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Cfmap_ka.thy
    Configuration maps, part 3: the contract steps K (= R1 o N o R') and A (merge).
    Ported from G. Gonthier's Coq development (cfmap.v).
*)
theory Cfmap_ka
  imports Four_Colour_Maps.Cfmap
begin

context hypermap
begin

lemma ecpR1_eq: "ecpR_ptr 1 x = f (e x)"
proof -
  have "(n ^^ (order n x - 1)) x = inv n x"
    using N.inv_funpow_order[of x] by simp
  then show ?thesis by (simp add: ecpR_ptr_def inv_node_apply)
qed

lemma ecpR'_eq: "ecpR_ptr (order n x - 1) x = n x"
proof -
  have "order n x - (order n x - 1) = 1" using N.order_pos[of x] by linarith
  then show ?thesis by (simp add: ecpR_ptr_def)
qed

end

section \<open>The K step\<close>

locale ecpk = ecp
begin

lemma nx0_in: "n x0 \<in> darts G" using x0D by simp

sublocale K: ecp G "n x0"
  by unfold_locales (rule nx0_in)

abbreviation GK where "GK \<equiv> K.GN"

definition pK where "pK = K.NN.ecpR_ptr 1 X"

lemma long_nx0: "long_cpring G (n x0) \<longleftrightarrow> lng"
proof -
  have "long_cpring G (n x0) \<longleftrightarrow> n (n (n x0)) \<noteq> n x0"
    unfolding long_cpring_def using node_eq_iff[of "n (n x0)" "n x0"] by auto
  also have "\<dots> \<longleftrightarrow> n (n x0) \<noteq> x0" by simp
  also have "\<dots> \<longleftrightarrow> lng" unfolding long_cpring_def using node_eq_iff[of "n x0" x0] by auto
  finally show ?thesis .
qed

lemma pK_eq: "pK = (if lng then f (e x0) else X)"
proof -
  have "pK = face GK (edge GK X)" unfolding pK_def by (rule K.NN.ecpR1_eq)
  also have "\<dots> = (if lng then f (e (f (e (n x0)))) else X)" using long_nx0 by simp
  finally show ?thesis by (simp add: nodeK)
qed

lemma pK_in: "pK \<in> darts GK" using pK_eq x0D by simp

lemma node_GK_pK: "node GK pK = X"
proof (cases lng)
  case True
  have a: "f (e x0) \<noteq> n x0" using True by (simp add: long_cpring_def)
  have b: "n (n (f (e x0))) = n x0" by (simp add: edgeK)
  have c: "f (e x0) \<in> D" using x0D by simp
  have pk: "pK = f (e x0)" using pK_eq True by simp
  show ?thesis unfolding pk using a b c by simp
next
  case False
  have pk: "pK = X" using pK_eq False by simp
  show ?thesis unfolding pk using False long_nx0 by simp
qed

lemma cpring_GK: "cpring GK pK = X # drop 2 (cpring G x0)"
proof (rule K.NN.cpring_def_char)
  show "X # drop 2 (cpring G x0) = node GK pK # drop 2 (cpring G x0)" by (simp only: node_GK_pK)
  show "distinct (X # drop 2 (cpring G x0))"
    using cpring_distinct[of x0] ringD by (auto dest: in_set_dropD)
  show "cycle (frel (node GK)) (rev (X # drop 2 (cpring G x0)))"
  proof (cases lng)
    case False
    have "length (cpring G x0) \<le> 2" using False size_long_cpring by simp
    then have "drop 2 (cpring G x0) = []" by simp
    then show ?thesis using False long_nx0 by (simp add: cycle_Cons)
  next
    case True
    define fe where "fe = f (e x0)"
    obtain rest where r: "cpring G x0 = n x0 # x0 # fe # rest"
      using head_long_cpring[OF True] unfolding fe_def by blast
    have dr: "distinct (n x0 # x0 # fe # rest)" using cpring_distinct[of x0] r by simp
    have rD: "set (n x0 # x0 # fe # rest) \<subseteq> D" using ringD r by simp
    have cq: "cycle (frel n) (rev rest @ [fe, x0, n x0])" using cycle_rev_cpring[of x0] r by simp
    have d2: "drop 2 (cpring G x0) = fe # rest" using r by simp
    have nfe: "n fe = x0" by (simp add: fe_def edgeK)
    have prp: "x0 \<noteq> n x0" by (rule lng_proper[OF True])
    have nnfe: "n (n fe) = n x0" using nfe by simp
    have feN: "fe \<noteq> n x0" using True by (simp add: fe_def long_cpring_def)
    show ?thesis
    proof (cases "rev rest")
      case Nil
      have n3: "n (n x0) = fe" using cq Nil by (simp add: cycle_Cons)
      have g1: "node GK fe = X" using nnfe feN rD by simp
      have g2: "node GK X = fe" using long_nx0 True n3 by simp
      show ?thesis using Nil d2 g1 g2 by (simp add: cycle_Cons)
    next
      case (Cons b rr1)
      have pq: "path (frel n) b (rr1 @ [fe, x0, n x0, b])" using cq Cons by (simp add: cycle_Cons)
      have nb: "n (n x0) = b" using pq by simp
      have rr: "set (b # rr1) = set rest" using Cons by (metis set_rev)
      have bD: "set (b # rr1) \<subseteq> D" using rr rD by auto
      have nr: "n x0 \<notin> set (b # rr1)" "x0 \<notin> set (b # rr1)" "fe \<notin> set (b # rr1)" using rr dr by auto
      have p1: "path (frel (node GK)) b (rr1 @ [fe])"
      proof (rule path_frel_cong[of n])
        show "path (frel n) b (rr1 @ [fe])" using pq by simp
        fix a assume a: "a \<in> set (butlast (b # rr1 @ [fe]))"
        then have a': "a \<in> set (b # rr1)" by (metis butlast.simps(2) butlast_snoc append_Cons)
        have aD: "a \<in> D" "a \<noteq> n x0" using a' bD nr by auto
        have "n (n a) \<noteq> n x0"
        proof
          assume "n (n a) = n x0"
          then have "n a = x0" by simp
          then have "a = fe" by (metis fe_def nodeK)
          then show False using a' nr by simp
        qed
        then show "node GK a = n a" using aD by simp
      qed
      have g1: "node GK fe = X" using nnfe feN rD by simp
      have g2: "node GK X = b" using long_nx0 True nb by simp
      have "rev (X # drop 2 (cpring G x0)) = b # rr1 @ [fe, X]" using d2 Cons by simp
      moreover have "path (frel (node GK)) b (rr1 @ [fe, X, b])" using p1 g1 g2 by simp
      ultimately show ?thesis by (simp add: cycle_Cons)
    qed
  qed
qed

lemma length_cpring_GK:
  assumes "proper_cpring G x0"
  shows "length (cpring GK pK) = length (cpring G x0) - 1"
  using cpring_GK assms size_proper_cpring by simp

lemma cface_GK_old: "x \<in> D \<Longrightarrow> y \<in> D \<Longrightarrow> fconnect (face GK) x y \<longleftrightarrow> cface x y"
  by (rule K.cface_GN_old)

lemma adj_GK_old:
  assumes "x \<in> D" "y \<in> D"
  shows "adj GK x y \<longleftrightarrow> adj G x y \<or> (cface (e x0) x \<and> cface (n x0) y) \<or> (cface (e x0) y \<and> cface (n x0) x)"
  using K.adj_GN_old[OF assms] by (simp add: nodeK)

lemma cface_node_GK: "fconnect (face GK) (node GK pK) (n x0)"
  unfolding node_GK_pK by (rule K.cface_GN_X)

lemma cface_GK_pK: "fconnect (face GK) pK (f (e x0))"
proof (cases lng)
  case True
  then show ?thesis using pK_eq by simp
next
  case False
  then have "f (e x0) = n x0" by (simp add: long_cpring_def)
  then show ?thesis using pK_eq False K.cface_GN_X by simp
qed

lemma fband_GK: "u \<in> darts GK \<Longrightarrow> \<exists>x \<in> D. fconnect (face GK) u x"
  by (rule K.fband_GN)

lemma edge_GK_old: "x \<in> D \<Longrightarrow> edge GK x = e x" by simp

end

section \<open>The A step: merging the neighbours of the ring head\<close>

definition ecpA_edge :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "ecpA_edge G x0 x =
     (if \<not> fconnect (face G) (edge G x0) (node G x0) then edge G x
      else if x = x0 then edge G (node G (node G x0))
      else if x = node G (node G x0) then edge G x0 else edge G x)"

definition ecpA_node :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "ecpA_node G x0 x =
     (if x = node G x0 then x0 else if node G x = x0 then node G (node G x0) else node G x)"

definition ecpA_face :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "ecpA_face G x0 x =
     (if fconnect (face G) (edge G x0) (node G x0) then face G x
      else if x = edge G x0 then node G x0
      else if face G x = node G x0 then face G (edge G x0) else face G x)"

definition ecpA :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> 'a hypermap" where
  "ecpA G x0 = \<lparr>darts = darts G, edge = ecpA_edge G x0, node = ecpA_node G x0, face = ecpA_face G x0\<rparr>"

definition ecpA_ptr :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> 'a" where
  "ecpA_ptr G x0 = ecpA_face G x0 (ecpA_edge G x0 (face G (edge G x0)))"

locale ecpa = hypermap G for G :: "'a hypermap" +
  fixes x0 :: 'a
  assumes x0D: "x0 \<in> darts G"
begin

definition GA where "GA = ecpA G x0"

abbreviation cc where "cc \<equiv> cface (e x0) (n x0)"

lemma GA_simps [simp]:
  "darts GA = D"
  "edge GA x = (if \<not> cc then e x else if x = x0 then e (n (n x0)) else if x = n (n x0) then e x0 else e x)"
  "node GA x = (if x = n x0 then x0 else if n x = x0 then n (n x0) else n x)"
  "face GA x = (if cc then f x else if x = e x0 then n x0 else if f x = n x0 then f (e x0) else f x)"
  by (simp_all add: GA_def ecpA_def ecpA_edge_def ecpA_node_def ecpA_face_def)

lemma hypermap_GA: "hypermap GA"
proof -
  have eq: "GA = \<lparr>darts = D, edge = edge GA, node = node GA, face = face GA\<rparr>"
    by (simp add: GA_def ecpA_def)
  have nn: "n (n x0) = x0 \<longleftrightarrow> f (e x0) = n x0" using node_eq_iff[of "n x0" x0] by auto
  have c3: "node GA (face GA (edge GA x)) = x" for x
  proof (cases cc)
    case True
    show ?thesis
    proof (cases "x = x0")
      case True
      then show ?thesis using \<open>cc\<close> by (simp add: nodeK)
    next
      case nx: False
      show ?thesis
      proof (cases "x = n (n x0)")
        case True
        then have "f (e x0) \<noteq> n x0" using nx nn by simp
        moreover have "n (f (e x0)) = x0" by (simp add: edgeK)
        ultimately show ?thesis using True nx \<open>cc\<close> by simp
      next
        case False
        have a: "f (e x) \<noteq> n x0" using False by (metis edgeK)
        have b: "n (f (e x)) \<noteq> x0" using nx by (simp add: edgeK)
        show ?thesis using \<open>cc\<close> nx False a b by (simp add: edgeK)
      qed
    qed
  next
    case False
    show ?thesis
    proof (cases "x = x0")
      case True then show ?thesis using False by simp
    next
      case nx: False
      have ex: "e x \<noteq> e x0" using nx by simp
      show ?thesis
      proof (cases "f (e x) = n x0")
        case True
        then have xn: "x = n (n x0)" by (metis edgeK)
        then have "f (e x0) \<noteq> n x0" using nx nn by simp
        moreover have "n (f (e x0)) = x0" by (simp add: edgeK)
        ultimately show ?thesis using False ex True xn by simp
      next
        case nf: False
        have b: "n (f (e x)) \<noteq> x0" using nx by (simp add: edgeK)
        show ?thesis using False ex nf b by (simp add: edgeK)
      qed
    qed
  qed
  have cl: "edge GA x \<in> D \<and> node GA x \<in> D \<and> face GA x \<in> D" if h: "x \<in> D" for x
    using h x0D by simp
  have out: "edge GA x = x \<and> node GA x = x \<and> face GA x = x" if h: "x \<notin> D" for x
  proof -
    have a: "x \<noteq> x0" "x \<noteq> n x0" "x \<noteq> n (n x0)" "x \<noteq> e x0" using h x0D by auto
    have b: "n x \<noteq> x0" "f x \<noteq> n x0" using h a by (simp_all add: N.out F.out)
    show ?thesis using h a b by (simp add: E.out N.out F.out)
  qed
  have "hypermap \<lparr>darts = D, edge = edge GA, node = node GA, face = face GA\<rparr>"
    by (rule hypermap_cancel3[OF _ cl out c3]) (simp add: finite_darts)
  then show ?thesis unfolding eq[symmetric] .
qed

sublocale A: hypermap GA by (rule hypermap_GA)

definition pA where "pA = face GA (edge GA (f (e x0)))"

lemma pA_eq: "pA = ecpA_ptr G x0"
  by (simp add: pA_def ecpA_ptr_def GA_def ecpA_def)

lemma node_GA_pA: "node GA pA = f (e x0)"
  unfolding pA_def by (rule A.edgeK)

lemma pA_in: "pA \<in> D" unfolding pA_def using x0D by simp

lemma cpring_GA: "cpring GA pA = (if long_cpring G x0 then drop 2 (cpring G x0) else cpring G x0)"
proof (cases "long_cpring G x0")
  case True
  define fe where "fe = f (e x0)"
  obtain rest where r: "cpring G x0 = n x0 # x0 # fe # rest"
    using head_long_cpring[OF True] unfolding fe_def by blast
  have dr: "distinct (n x0 # x0 # fe # rest)" using cpring_distinct[of x0] r by simp
  have rD: "set (n x0 # x0 # fe # rest) \<subseteq> D" using ringD_gen[OF x0D] r by simp
  have cq: "cycle (frel n) (rev rest @ [fe, x0, n x0])" using cycle_rev_cpring[of x0] r by simp
  have nfe: "n fe = x0" by (simp add: fe_def edgeK)
  have feN: "fe \<noteq> n x0" using True by (simp add: fe_def long_cpring_def)
  have g0: "node GA fe = n (n x0)" using feN nfe by simp
  have "cpring GA pA = fe # rest"
  proof (rule A.cpring_def_char)
    show "fe # rest = node GA pA # rest" by (simp only: node_GA_pA fe_def)
    show "distinct (fe # rest)" using dr by simp
    show "cycle (frel (node GA)) (rev (fe # rest))"
    proof (cases "rev rest")
      case Nil
      have "n (n x0) = fe" using cq Nil by (simp add: cycle_Cons)
      then show ?thesis using Nil g0 by (simp add: cycle_Cons)
    next
      case (Cons b rr1)
      have pq: "path (frel n) b (rr1 @ [fe, x0, n x0, b])" using cq Cons by (simp add: cycle_Cons)
      have nb: "n (n x0) = b" using pq by simp
      have rr: "set (b # rr1) = set rest" using Cons by (metis set_rev)
      have nr: "n x0 \<notin> set (b # rr1)" "x0 \<notin> set (b # rr1)" "fe \<notin> set (b # rr1)" using rr dr by auto
      have p1: "path (frel (node GA)) b (rr1 @ [fe])"
      proof (rule path_frel_cong[of n])
        show "path (frel n) b (rr1 @ [fe])" using pq by simp
        fix a assume a: "a \<in> set (butlast (b # rr1 @ [fe]))"
        then have a': "a \<in> set (b # rr1)" by (metis butlast.simps(2) butlast_snoc append_Cons)
        have "n a \<noteq> x0"
        proof
          assume "n a = x0"
          then have "a = fe" by (metis fe_def nodeK)
          then show False using a' nr by simp
        qed
        moreover have "a \<noteq> n x0" using a' nr by auto
        ultimately show "node GA a = n a" by simp
      qed
      have "rev (fe # rest) = b # rr1 @ [fe]" using Cons by simp
      moreover have "path (frel (node GA)) b (rr1 @ [fe, b])" using p1 g0 nb by simp
      ultimately show ?thesis by (simp add: cycle_Cons)
    qed
  qed
  then show ?thesis using True r by simp
next
  case False
  have nfe: "f (e x0) = n x0" using False by (simp add: long_cpring_def)
  have nn: "n (n x0) = x0" using nfe node_eq_iff[of "n x0" x0] by auto
  have "cpring GA pA = cpring G x0"
  proof (cases "x0 = n x0")
    case True
    have r: "cpring G x0 = [x0]"
    proof (rule cpring_def_char)
      show "[x0] = n x0 # []" using True by simp
    qed (use True in \<open>simp_all add: cycle_Cons\<close>)
    show ?thesis unfolding r
    proof (rule A.cpring_def_char)
      show "[x0] = node GA pA # []" using node_GA_pA nfe True by simp
    qed (use True in \<open>simp_all add: cycle_Cons\<close>)
  next
    case nx: False
    have r: "cpring G x0 = [n x0, x0]"
    proof (rule cpring_def_char)
      show "[n x0, x0] = n x0 # [x0]" by simp
    qed (use nx nn in \<open>simp_all add: cycle_Cons\<close>)
    show ?thesis unfolding r
    proof (rule A.cpring_def_char)
      show "[n x0, x0] = node GA pA # [x0]" using node_GA_pA nfe by simp
      show "distinct [n x0, x0]" using nx by simp
      have "node GA x0 = n x0" using nx nn by auto
      moreover have "node GA (n x0) = x0" by simp
      ultimately show "cycle (frel (node GA)) (rev [n x0, x0])" by (simp add: cycle_Cons)
    qed
  qed
  then show ?thesis using False by simp
qed

lemma face_GA_transpose:
  assumes "\<not> cc"
  shows "face GA = f \<circ> Transposition.transpose (e x0) (e (n (n x0)))"
proof
  fix x
  have a: "f (e (n (n x0))) = n x0" by (simp add: nodeK)
  have b: "f x = n x0 \<longleftrightarrow> x = e (n (n x0))" by (metis a faceK)
  show "face GA x = (f \<circ> Transposition.transpose (e x0) (e (n (n x0)))) x"
    using assms a b by (auto simp: Transposition.transpose_def)
qed

lemma cface_GA:
  assumes x: "x \<in> D" and y: "y \<in> D"
  shows "fconnect (face GA) x y \<longleftrightarrow>
         cface x y \<or> (fband G [f (e x0), n x0] x \<and> fband G [f (e x0), n x0] y)"
proof (cases cc)
  case True
  have fa: "face GA = f" using True by (simp add: fun_eq_iff)
  have c2: "cface (f (e x0)) (n x0)" using True by simp
  show ?thesis
  proof
    assume "fconnect (face GA) x y"
    then show "cface x y \<or> (fband G [f (e x0), n x0] x \<and> fband G [f (e x0), n x0] y)" using fa by simp
  next
    assume h: "cface x y \<or> (fband G [f (e x0), n x0] x \<and> fband G [f (e x0), n x0] y)"
    have "cface x y"
    proof (cases "cface x y")
      case False
      then have bx: "cface x (f (e x0)) \<or> cface x (n x0)" and bY: "cface y (f (e x0)) \<or> cface y (n x0)"
        using h by (auto simp: fband_def)
      have bx': "cface x (n x0)"
      proof (cases "cface x (f (e x0))")
        case True then show ?thesis by (rule fconnect_trans[OF _ c2])
      qed (use bx in blast)
      have by': "cface y (n x0)"
      proof (cases "cface y (f (e x0))")
        case True then show ?thesis by (rule fconnect_trans[OF _ c2])
      qed (use bY in blast)
      show ?thesis by (rule fconnect_trans[OF bx' F.fconnect_sym[OF by']])
    qed simp
    then show "fconnect (face GA) x y" using fa by simp
  qed
next
  case False
  define a where "a = e x0"
  define b where "b = e (n (n x0))"
  have aD: "a \<in> D" and bD: "b \<in> D" using x0D by (simp_all add: a_def b_def)
  have fa: "face GA = f \<circ> Transposition.transpose a b"
    unfolding a_def b_def by (rule face_GA_transpose[OF False])
  have fb: "f b = n x0" by (simp add: b_def nodeK)
  have nab: "\<not> cface a b"
  proof
    assume "cface a b"
    then have "cface a (f b)" by (rule fconnect_trans[OF _ fconnect_step[of f b]])
    then have "cface a (n x0)" using fb by simp
    then show False using False a_def by simp
  qed
  have ab: "a \<noteq> b" using nab by auto
  have merge: "cyc (face GA) a = cyc f a \<union> cyc f b"
    unfolding fa by (rule cyc_transpose_merge[OF F.fperm_axioms aD bD ab nab])
  have band: "fband G [f (e x0), n x0] z \<longleftrightarrow> z \<in> cyc f a \<union> cyc f b" for z
  proof -
    have "cface z (f (e x0)) \<longleftrightarrow> z \<in> cyc f a"
      by (simp add: a_def F.in_cyc_iff F.fconnect_commute[of "e x0" z])
    moreover have "cface z (n x0) \<longleftrightarrow> z \<in> cyc f b"
      unfolding fb[symmetric] by (simp add: F.in_cyc_iff F.fconnect_commute[of b z])
    ultimately show ?thesis by (auto simp: fband_def)
  qed
  interpret AF: fperm "face GA" D using A.F.fperm_axioms by simp
  show ?thesis
  proof (cases "x \<in> cyc f a \<union> cyc f b")
    case True
    then have "x \<in> cyc (face GA) a" using merge by simp
    then have "cyc (face GA) x = cyc f a \<union> cyc f b" using merge AF.cyc_unique by blast
    then have "fconnect (face GA) x y \<longleftrightarrow> y \<in> cyc f a \<union> cyc f b" by (simp add: AF.in_cyc_iff[symmetric])
    moreover have "y \<in> cyc f a \<union> cyc f b" if cxy: "cface x y"
    proof -
      have yx: "y \<in> cyc f x" using cxy by (simp add: F.in_cyc_iff)
      consider "x \<in> cyc f a" | "x \<in> cyc f b" using True by blast
      then show ?thesis
      proof cases
        case 1 then show ?thesis using yx F.cyc_unique[OF 1] by simp
      next
        case 2 then show ?thesis using yx F.cyc_unique[OF 2] by simp
      qed
    qed
    ultimately show ?thesis using band True by blast
  next
    case nx: False
    have "cyc (face GA) x = cyc f x"
    proof (rule cyc_eq_on)
      fix z assume xz: "cface x z"
      have zx: "z \<in> cyc f x" using xz by (simp add: F.in_cyc_iff)
      have "z \<notin> cyc f a"
      proof
        assume "z \<in> cyc f a"
        then have "cyc f a = cyc f z" by (rule F.cyc_unique)
        also have "\<dots> = cyc f x" using F.cyc_unique[OF zx] by simp
        finally show False using nx F.x_in_cyc[of x] by blast
      qed
      moreover have "z \<notin> cyc f b"
      proof
        assume "z \<in> cyc f b"
        then have "cyc f b = cyc f z" by (rule F.cyc_unique)
        also have "\<dots> = cyc f x" using F.cyc_unique[OF zx] by simp
        finally show False using nx F.x_in_cyc[of x] by blast
      qed
      ultimately have "z \<notin> cyc f a" "z \<notin> cyc f b" by blast+
      then have "z \<noteq> a" "z \<noteq> b" by auto
      then show "face GA z = f z" unfolding fa by (simp add: Transposition.transpose_def)
    qed
    then have "fconnect (face GA) x y \<longleftrightarrow> cface x y"
      by (simp add: AF.in_cyc_iff[symmetric] F.in_cyc_iff[symmetric])
    then show ?thesis using band nx by blast
  qed
qed

lemma ecpA_merge: "fconnect (face GA) (f (e x0)) (n x0)"
  using cface_GA[of "f (e x0)" "n x0"] x0D by (simp add: fband_def)

end

end
