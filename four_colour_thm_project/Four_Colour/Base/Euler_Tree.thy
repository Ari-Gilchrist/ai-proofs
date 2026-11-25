(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Euler_Tree.thy
    The "Euler tree" lemma: in a hypermap with the Jordan property, every edge
    cycle contains a dart that is either degenerate or not a cross edge.
    Ported from G. Gonthier's Coq development (jordan.v, Euler_tree).
*)
theory Euler_Tree
  imports Jordan
begin

context hypermap
begin

lemma clink_path_closed:
  "path (clink G) a l \<Longrightarrow> a \<in> D \<Longrightarrow> set l \<subseteq> D"
proof (induction l arbitrary: a)
  case Nil
  then show ?case by simp
next
  case (Cons b l)
  then have bD: "b \<in> D" using clink_closed by auto
  have "set l \<subseteq> D" using Cons.IH[of b] Cons.prems(1) bD by simp
  then show ?case using bD by simp
qed

lemma face_path_clink: "path (frel f) a q \<Longrightarrow> path (clink G) a q"
  by (rule path_mono[of "frel f"]) (auto simp: clink_def)

text \<open>Step 1: a face-simple edge arc ending in the face of @{text "node (face x)"}.\<close>

lemma simple_edge_arc:
  assumes "path (frel e) x p" "\<not> distinct (map (cyc f) (x # p))"
  shows "\<exists>x' p1. cedge x x' \<and> path (frel e) x' p1 \<and> distinct (map (cyc f) (x' # p1)) \<and>
           cface (lastd x' p1) (n (f x'))"
  using assms
proof (induction p arbitrary: x)
  case Nil
  then show ?case by simp
next
  case (Cons y p)
  have exy: "e x = y" and py: "path (frel e) y p" using Cons.prems by auto
  have cxy: "cedge x y" using fconnect_step[of e x] exy by simp
  show ?case
  proof (cases "distinct (map (cyc f) (y # p))")
    case False
    then obtain x' p1 where h: "cedge y x'" "path (frel e) x' p1"
        "distinct (map (cyc f) (x' # p1))" "cface (lastd x' p1) (n (f x'))"
      using Cons.IH[OF py] by blast
    have "cedge x x'" by (rule fconnect_trans[OF cxy h(1)])
    then show ?thesis using h by blast
  next
    case True
    then have "cyc f x \<in> set (map (cyc f) (y # p))" using Cons.prems(2) by auto
    then obtain w where w: "w \<in> set (y # p)" "cyc f w = cyc f x" by auto
    define k where "k = lindex (y # p) w"
    have k1: "k < length (y # p)" unfolding k_def by (rule lindex_less[OF w(1)])
    have k2: "(y # p) ! k = w" unfolding k_def by (rule nth_lindex[OF w(1)])
    note k = k1 k2
    define p1 where "p1 = take k p"
    have pp1: "path (frel e) y p1" unfolding p1_def by (rule path_take[OF py])
    have kle: "k \<le> length p" using k1 by simp
    have lp1: "lastd y p1 = w" using lastd_take[OF kle, of y] k2 unfolding p1_def by simp
    have "y # p1 = take (Suc k) (y # p)" unfolding p1_def by simp
    then have dp1: "distinct (map (cyc f) (y # p1))"
      using True by (metis distinct_take take_map)
    have "n (f y) = x" using exy edgeK[of x] by simp
    moreover have "cface w x" using w(2) F.cyc_eq_iff by simp
    ultimately have "cface (lastd y p1) (n (f y))" using lp1 by simp
    then show ?thesis using cxy pp1 dp1 by blast
  qed
qed

text \<open>Step 2: the contour along a face-simple edge arc.\<close>

lemma face_contour:
  assumes "path (frel e) x p1" "distinct (map (cyc f) (x # p1))" "cface (lastd x p1) z"
  shows "\<exists>q1. path (clink G) (f x) q1 \<and> lastd (f x) q1 = z \<and> distinct (f x # q1) \<and>
           cyc f ` set (f x # q1) = cyc f ` set (x # p1) \<and>
           (\<forall>y. f y \<in> set (f x # q1) \<longrightarrow> y \<in> set (lastd x p1 # butlast (f x # q1)))"
  using assms
proof (induction p1 arbitrary: x)
  case Nil
  obtain Q where Q: "path (frel f) (f x) Q" "lastd (f x) Q = x" "distinct (f x # Q)"
    "set (f x # Q) = cyc f x" by (rule F.face_orbit_path)
  have zc: "z \<in> set (f x # Q)" using Nil.prems(3) Q(4) by (simp add: F.in_cyc_iff)
  define k where "k = lindex (f x # Q) z"
  have kl: "k < length (f x # Q)" unfolding k_def using zc by (rule lindex_less)
  have kz: "(f x # Q) ! k = z" unfolding k_def using zc by (rule nth_lindex)
  define q1 where "q1 = take k Q"
  have pq: "path (frel f) (f x) q1" unfolding q1_def by (rule path_take[OF Q(1)])
  have kle: "k \<le> length Q" using kl by simp
  have lq: "lastd (f x) q1 = z" using lastd_take[OF kle, of "f x"] kz unfolding q1_def by simp
  have pre: "f x # q1 = take (Suc k) (f x # Q)" unfolding q1_def by simp
  have dq: "distinct (f x # q1)" using Q(3) pre by (metis distinct_take)
  have sq: "set (f x # q1) \<subseteq> cyc f x" using Q(4) pre by (metis set_take_subset)
  have fx_cyc: "f x \<in> cyc f x" by (simp add: F.in_cyc_iff)
  have img: "cyc f ` set (f x # q1) = cyc f ` set [x]"
  proof -
    have "cyc f w = cyc f x" if "w \<in> set (f x # q1)" for w
      using sq that F.cyc_unique by blast
    then show ?thesis by auto
  qed
  have prp: "y \<in> set (lastd x [] # butlast (f x # q1))" if fy: "f y \<in> set (f x # q1)" for y
  proof (cases "f y = f x")
    case True
    then show ?thesis by simp
  next
    case False
    then have "f y \<in> set q1" using fy by simp
    then have "y \<in> set (butlast (f x # q1))" by (rule path_frel_butlast[OF pq F.inj])
    then show ?thesis by simp
  qed
  show ?case using face_path_clink[OF pq] lq dq img prp by blast
next
  case (Cons y p)
  have exy: "e x = y" and py: "path (frel e) y p" using Cons.prems(1) by auto
  have dyp: "distinct (map (cyc f) (y # p))" using Cons.prems(2) by simp
  have xnot: "cyc f x \<notin> cyc f ` set (y # p)" using Cons.prems(2) by auto
  have lz: "cface (lastd y p) z" using Cons.prems(3) by simp
  obtain q2 where q2: "path (clink G) (f y) q2" "lastd (f y) q2 = z" "distinct (f y # q2)"
    "cyc f ` set (f y # q2) = cyc f ` set (y # p)"
    "\<forall>w. f w \<in> set (f y # q2) \<longrightarrow> w \<in> set (lastd y p # butlast (f y # q2))"
    using Cons.IH[OF py dyp lz] by blast
  obtain Q where Q: "path (frel f) (f x) Q" "lastd (f x) Q = x" "distinct (f x # Q)"
    "set (f x # Q) = cyc f x" by (rule F.face_orbit_path)
  define q1 where "q1 = Q @ f y # q2"
  have nfy: "n (f y) = x" using exy edgeK[of x] by simp
  have pq: "path (clink G) (f x) q1"
    unfolding q1_def using face_path_clink[OF Q(1)] Q(2) q2(1) nfy by (simp add: clink_def)
  have lq: "lastd (f x) q1 = z" unfolding q1_def using q2(2) by (simp add: lastd_append)
  have disj: "set (f x # Q) \<inter> set (f y # q2) = {}"
  proof -
    { fix w assume w1: "w \<in> set (f x # Q)" and w2: "w \<in> set (f y # q2)"
      have "cyc f w = cyc f x" using w1 Q(4) F.cyc_unique by blast
      moreover have "cyc f w \<in> cyc f ` set (y # p)" using w2 q2(4) by blast
      ultimately have False using xnot by simp }
    then show ?thesis by blast
  qed
  have dq: "distinct (f x # q1)" unfolding q1_def using Q(3) q2(3) disj by auto
  have img: "cyc f ` set (f x # q1) = cyc f ` set (x # y # p)"
  proof -
    have "cyc f ` set (f x # Q) = {cyc f x}"
    proof -
      have "cyc f w = cyc f x" if "w \<in> set (f x # Q)" for w
        using that Q(4) F.cyc_unique by blast
      then show ?thesis by auto
    qed
    then show ?thesis unfolding q1_def using q2(4) by auto
  qed
  have bl: "butlast (f x # q1) = (f x # Q) @ butlast (f y # q2)"
    unfolding q1_def by (simp add: butlast_append)
  have prp: "w \<in> set (lastd x (y # p) # butlast (f x # q1))" if fw: "f w \<in> set (f x # q1)" for w
  proof (cases "f w \<in> set (f x # Q)")
    case True
    then have "f w \<in> cyc f x" by (simp only: Q(4))
    then have "w \<in> cyc f x" by (simp add: F.in_cyc_iff)
    then show ?thesis using Q(4) bl by auto
  next
    case False
    then have "f w \<in> set (f y # q2)" using fw unfolding q1_def by auto
    then have "w \<in> set (lastd y p # butlast (f y # q2))" using q2(5) by blast
    then show ?thesis using bl by auto
  qed
  show ?case using pq lq dq img prp by blast
qed

text \<open>The Euler tree lemma.\<close>

theorem Euler_tree:
  assumes J: "Jordan G" and x0D: "x0 \<in> D"
  shows "\<exists>y. cedge x0 y \<and> (clink G y y \<or> \<not> cross_edge G y)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have tree: "\<not> clink G y y" "cross_edge G y" if "cedge x0 y" for y
    using that by blast+
  \<comment> \<open>Step 1.\<close>
  define T where "T = tl (orb e x0)"
  have oT: "orb e x0 = x0 # T" unfolding T_def by (rule E.orb_Cons)
  have pT: "path (frel e) x0 (T @ [x0])" using E.cycle_orb[of x0] oT by (simp add: cycle_Cons)
  have "\<not> distinct (map (cyc f) (x0 # T @ [x0]))" by simp
  then obtain x p1 where x0x: "cedge x0 x" and pe: "path (frel e) x p1"
    and sp: "distinct (map (cyc f) (x # p1))" and lf: "cface (lastd x p1) (n (f x))"
    using simple_edge_arc[OF pT] by blast
  define z1 where "z1 = lastd x p1"
  define fx where "fx = f x"
  define nfx where "nfx = n fx"
  have xD: "x \<in> D" using x0x x0D E.fconnect_in_D by blast
  have treex: "\<not> clink G y y" "cross_edge G y" if "cedge x y" for y
    using tree fconnect_trans[OF x0x that] by auto
  \<comment> \<open>Step 2.\<close>
  obtain q1 where pq: "path (clink G) fx q1" and lq: "lastd fx q1 = nfx" and dq: "distinct (fx # q1)"
    and imq: "cyc f ` set (fx # q1) = cyc f ` set (x # p1)"
    and prq: "\<And>y. f y \<in> set (fx # q1) \<Longrightarrow> y \<in> set (z1 # butlast (fx # q1))"
    using face_contour[OF pe sp lf] unfolding fx_def nfx_def z1_def by blast
  define C where "C = set (fx # q1)"
  have fxC: "fx \<in> C" and nfxC: "nfx \<in> C" using lq unfolding C_def by (auto simp: last_in_set)
  have nfx_bl: "nfx \<notin> set (butlast (fx # q1))"
  proof -
    have "distinct (butlast (fx # q1) @ [lastd fx q1])" using dq by (metis append_butlast_last_id list.distinct(1))
    then show ?thesis using lq by simp
  qed
  \<comment> \<open>Step 3.\<close>
  have fx_notin: "fx \<notin> set (x # p1)"
  proof
    assume fxin: "fx \<in> set (x # p1)"
    show False
    proof (cases "fx = x")
      case True
      then have "clink G x x" by (simp add: clink_def fx_def)
      then show False using treex[of x] by simp
    next
      case False
      then have "fx \<in> set p1" using fxin by simp
      then have "cyc f fx \<in> set (map (cyc f) p1)" by simp
      moreover have "cyc f fx = cyc f x" unfolding fx_def by simp
      ultimately show False using sp by simp
    qed
  qed
  \<comment> \<open>Step 4: the edge cycle of x is node-closed and contains fx.\<close>
  have xnfx: "cedge x nfx"
  proof -
    have "e nfx = x" unfolding nfx_def fx_def by (rule faceK)
    then have "cedge nfx x" using fconnect_step[of e nfx] by simp
    then show ?thesis by (rule E.fconnect_sym)
  qed
  have ncl: "n w \<in> cyc e x" if "w \<in> cyc e x" for w
  proof -
    have xw: "cedge x w" using that by (simp add: E.in_cyc_iff)
    have "cedge w (n w)" using treex(2)[OF xw] by (simp add: cross_edge_def)
    then show ?thesis using fconnect_trans[OF xw] by (simp add: E.in_cyc_iff)
  qed
  have xfx: "cedge x fx"
  proof -
    have "nfx \<in> cyc e x" using xnfx by (simp add: E.in_cyc_iff)
    then have "inv n nfx \<in> cyc e x" using N.closed_inv[where S="cyc e x", OF ncl] by blast
    then show ?thesis unfolding nfx_def by (simp add: E.in_cyc_iff)
  qed
  \<comment> \<open>Step 5.\<close>
  have nfx_fx: "nfx \<noteq> fx"
  proof
    assume "nfx = fx"
    then have "clink G fx fx" unfolding nfx_def by (simp add: clink_def)
    then show False using treex(1)[OF xfx] by simp
  qed
  have q1ne: "q1 \<noteq> []" using lq nfx_fx by auto
  \<comment> \<open>Step 6: an edge arc from fx to nfx avoiding z1.\<close>
  obtain p2 where pp2: "path (frel e) fx p2" and lp2: "lastd fx p2 = nfx" and z1p2: "z1 \<notin> set p2"
  proof -
    have xz1: "cedge x z1"
    proof (cases "p1 = []")
      case True
      then show ?thesis unfolding z1_def by simp
    next
      case False
      then have "last p1 \<in> set p1" by simp
      then show ?thesis unfolding z1_def using path_fconnect[OF pe] False by simp
    qed
    have "cedge z1 nfx" by (rule fconnect_trans[OF E.fconnect_sym[OF xz1] xnfx])
    then have "connect (frel e) z1 nfx" by (rule fconnect_connect)
    then obtain P where pP: "path (frel e) z1 P" and lP: "lastd z1 P = nfx" and dP: "distinct (z1 # P)"
      by (rule connect_shortest)
    have pW: "path (frel e) x (p1 @ P)" using pe pP unfolding z1_def by simp
    have lW: "lastd x (p1 @ P) = nfx" using lP lastd_append[of x p1 P] unfolding z1_def by simp
    have "e nfx = x" unfolding nfx_def fx_def by (rule faceK)
    then have "cyc e x \<subseteq> set (x # p1 @ P)" using E.path_cyc_cover[OF pW] lW by simp
    moreover have "fx \<in> cyc e x" using xfx by (simp add: E.in_cyc_iff)
    ultimately have "fx \<in> set (x # p1 @ P)" by blast
    then have "fx \<in> set P" using fx_notin by auto
    then obtain A B where P: "P = A @ fx # B" by (meson split_list)
    have "path (frel e) fx B" using pP P by simp
    moreover have "lastd fx B = nfx" using lP P by (simp add: lastd_append)
    moreover have "z1 \<notin> set B" using dP P by simp
    ultimately show ?thesis by (rule that)
  qed
  \<comment> \<open>Step 7: grow a C-path from nfx avoiding the contour.\<close>
  have contourD: "set (fx # q1) \<subseteq> D"
  proof -
    have "fx \<in> D" unfolding fx_def using xD by simp
    then show ?thesis using clink_path_closed[OF pq] by simp
  qed
  have nfxD: "nfx \<in> D" using nfxC contourD unfolding C_def by blast
  have claimB:
    "w \<noteq> nfx \<and> (\<exists>q. path (clink G) nfx q \<and> lastd nfx q = w \<and> set q \<inter> C = {})"
    if pN: "path (frel n) w N" and lN: "lastd w N = f (e y)" and ey: "e y \<noteq> z1"
      and IHy: "\<exists>q. path (clink G) nfx q \<and> lastd nfx q = e y \<and> set q \<inter> C = {}"
    for w N y
    using pN lN
  proof (induction N arbitrary: w)
    case Nil
    then have wf: "w = f (e y)" by simp
    obtain q2 where q2: "path (clink G) nfx q2" "lastd nfx q2 = e y" "set q2 \<inter> C = {}"
      using IHy by blast
    have feyC: "f (e y) \<notin> C"
    proof
      assume "f (e y) \<in> C"
      then have "e y \<in> set (z1 # butlast (fx # q1))" using prq unfolding C_def by blast
      then have eyb: "e y \<in> set (butlast (fx # q1))" using ey by simp
      show False
      proof (cases "q2 = []")
        case True
        then have "e y = nfx" using q2(2) by simp
        then show False using eyb nfx_bl by simp
      next
        case False
        then have "e y \<in> set q2" using q2(2) by (metis last_ConsR last_in_set)
        moreover have "e y \<in> C" using eyb unfolding C_def by (meson in_set_butlastD)
        ultimately show False using q2(3) by blast
      qed
    qed
    have "path (clink G) nfx (q2 @ [f (e y)])" using q2(1,2) by (simp add: clink_def)
    moreover have "lastd nfx (q2 @ [f (e y)]) = w" using wf by simp
    moreover have "set (q2 @ [f (e y)]) \<inter> C = {}" using q2(3) feyC by auto
    moreover have "w \<noteq> nfx" using wf feyC nfxC by auto
    ultimately show ?case by blast
  next
    case (Cons v N)
    have nw: "n w = v" and pv: "path (frel n) v N" using Cons.prems(1) by auto
    have lv: "lastd v N = f (e y)" using Cons.prems(2) by simp
    have vn: "v \<noteq> nfx" using Cons.IH[OF pv lv] by blast
    obtain q3 where q3: "path (clink G) nfx q3" "lastd nfx q3 = v" "set q3 \<inter> C = {}"
      using Cons.IH[OF pv lv] by blast
    obtain q3' where q3': "path (clink G) nfx q3'" "lastd nfx q3' = v" "distinct (nfx # q3')"
      "set q3' \<subseteq> set q3"
      using path_shorten[OF q3(1)] q3(2) by metis
    have q3C: "set q3' \<inter> C = {}" using q3' q3(3) by blast
    have wC: "w \<notin> C"
    proof
      assume wCm: "w \<in> C"
      have wfx: "w \<noteq> fx"
      proof
        assume "w = fx"
        then have "v = nfx" using nw unfolding nfx_def by simp
        then show False using vn by simp
      qed
      then have wq1: "w \<in> set q1" using wCm unfolding C_def by simp
      let ?M = "fx # q1 @ q3'"
      have "Moebius_path G ?M"
      proof (rule Moebius_pathI[OF hypermap_axioms])
        show "distinct (fx # q1 @ q3')"
          using dq q3'(3) q3C unfolding C_def by auto
        show "path (clink G) fx (q1 @ q3')" using pq q3'(1) lq by simp
        show "n w = lastd fx (q1 @ q3')" using nw q3'(2) lq lastd_append[of fx q1 q3'] by simp
        have "lastd fx q1 = last q1" using q1ne by simp
        then have lastq1: "last q1 = n fx" using lq unfolding nfx_def by simp
        show "mem2 (q1 @ q3') w (n fx)"
        proof -
          obtain A B where q1s: "q1 = A @ w # B" "w \<notin> set A" using wq1 by (meson split_list_first)
          have "n fx \<in> set (w # B)" using lastq1 q1s(1) by (cases B rule: rev_cases) auto
          then show ?thesis using q1s mem2_split_iff[of w A "B @ q3'" "n fx"] by auto
        qed
      qed
      moreover have "set ?M \<subseteq> D"
      proof -
        have "set q3' \<subseteq> D" using clink_path_closed[OF q3'(1) nfxD] .
        then show ?thesis using contourD by auto
      qed
      ultimately show False using J unfolding Jordan_def by blast
    qed
    have "path (clink G) nfx (q3' @ [w])" using q3'(1,2) nw by (simp add: clink_def)
    moreover have "lastd nfx (q3' @ [w]) = w" by simp
    moreover have "set (q3' @ [w]) \<inter> C = {}" using q3C wC by auto
    moreover have "w \<noteq> nfx" using wC nfxC by auto
    ultimately show ?case by blast
  qed
  have claimA:
    "\<exists>q. path (clink G) nfx q \<and> lastd nfx q = y \<and> set q \<inter> C = {}"
    if "path (frel e) y P" "lastd y P = nfx" "z1 \<notin> set P" for y P
    using that
  proof (induction P arbitrary: y)
    case Nil
    then show ?case by (intro exI[of _ "[]"]) simp
  next
    case (Cons u P)
    have eyu: "e y = u" and pu: "path (frel e) u P" using Cons.prems(1) by auto
    have lu: "lastd u P = nfx" using Cons.prems(2) by simp
    have uz: "u \<noteq> z1" and z1P: "z1 \<notin> set P" using Cons.prems(3) by auto
    have IHu: "\<exists>q. path (clink G) nfx q \<and> lastd nfx q = e y \<and> set q \<inter> C = {}"
      using Cons.IH[OF pu lu z1P] eyu by simp
    have "cnode y (f (e y))"
    proof -
      have "n (f (e y)) = y" by (rule edgeK)
      then have "cnode (f (e y)) y" using fconnect_step[of n "f (e y)"] by simp
      then show ?thesis by (rule N.fconnect_sym)
    qed
    then obtain N where pN: "path (frel n) y N" and lN: "lastd y N = f (e y)"
      by (rule fconnect_path)
    have "e y \<noteq> z1" using uz eyu by simp
    then show ?case using claimB[OF pN lN _ IHu] by blast
  qed
  obtain q2 where q2: "path (clink G) nfx q2" "lastd nfx q2 = fx" "set q2 \<inter> C = {}"
    using claimA[OF pp2 lp2 z1p2] by blast
  show False
  proof (cases "q2 = []")
    case True
    then show False using q2(2) nfx_fx by simp
  next
    case False
    then have "fx \<in> set q2" using q2(2) by (metis last_ConsR last_in_set)
    then show False using q2(3) fxC by blast
  qed
qed

end

end
