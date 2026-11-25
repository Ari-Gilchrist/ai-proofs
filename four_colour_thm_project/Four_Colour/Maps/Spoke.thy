(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Spoke.thy
    Spoke rings in a minimal counterexample (section SpokeRing of birkhoff.v):
    the ring of faces around a face is a chordless simple ring with x alone inside,
    hence every face has arity at least 5; the map is plain, cubic and pentagonal.
    Ported from G. Gonthier's Coq development (birkhoff.v).
*)
theory Spoke
  imports Birkhoff
begin

lemma cycle_from_next_rel:
  assumes d: "distinct p" and nx: "\<And>y. y \<in> set p \<Longrightarrow> R y (next_in p y)"
  shows "cycle R p"
  unfolding cycle_nth
proof (intro allI impI)
  fix i assume i: "i < length p"
  have pi: "p ! i \<in> set p" using i by simp
  have "lindex p (p ! i) = i" by (rule lindex_nth_distinct[OF d i])
  then show "R (p ! i) (p ! (Suc i mod length p))" using nx[OF pi] pi by (simp add: next_in_def)
qed

lemma next_in_funpow:
  assumes d: "distinct p" and a: "a \<in> set p"
  shows "(next_in p ^^ k) a \<in> set p \<and> lindex p ((next_in p ^^ k) a) = (lindex p a + k) mod length p"
proof (induction k)
  case 0
  then show ?case using a lindex_less[OF a] by simp
next
  case (Suc k)
  then have m: "(next_in p ^^ k) a \<in> set p" by simp
  have "lindex p ((next_in p ^^ Suc k) a) = Suc (lindex p ((next_in p ^^ k) a)) mod length p"
    using next_in_lindex[OF d m] by simp
  also have "\<dots> = (lindex p a + Suc k) mod length p" using Suc by (simp add: mod_Suc_eq)
  finally show ?case using next_in_mem[OF m] by simp
qed

lemma next_in_funpow_period:
  assumes d: "distinct p" and a: "a \<in> set p" and k: "0 < k" and eq: "(next_in p ^^ k) a = a"
  shows "length p \<le> k"
proof -
  define i where "i = lindex p a"
  have i: "i < length p" using lindex_less[OF a] by (simp add: i_def)
  have "(i + k) mod length p = i" using next_in_funpow[OF d a, of k] eq by (simp add: i_def)
  then have "(i + k) mod length p = i mod length p" using i by simp
  then have "length p dvd k" using mod_eq_dvd_iff_nat[of i "i + k" "length p"] by simp
  then show ?thesis using k by (rule dvd_imp_le)
qed

lemma next_in_triangle:
  assumes d: "distinct p" and abc: "a \<in> set p" "b \<in> set p" "c \<in> set p"
    and ne: "a \<noteq> b" "a \<noteq> c" "b \<noteq> c"
    and ab: "next_in p a = b \<or> next_in p b = a" and ac: "next_in p a = c \<or> next_in p c = a"
    and bc: "next_in p b = c \<or> next_in p c = b"
  shows "length p \<le> 3"
proof -
  have "next_in p (next_in p (next_in p a)) = a" using ab ac bc ne by auto
  then have "(next_in p ^^ 3) a = a" by (simp add: numeral_eq_Suc)
  then show ?thesis using next_in_funpow_period[OF d abc(1), of 3] by simp
qed

lemma next_in_ne_prev:
  assumes d: "distinct p" and a: "a \<in> set p" and l: "2 < length p"
  shows "next_in p a \<noteq> prev_in p a"
proof
  assume eq: "next_in p a = prev_in p a"
  have "next_in p (next_in p a) = a" using next_prev_in[OF d a] eq by simp
  then have "(next_in p ^^ 2) a = a" by (simp add: numeral_eq_Suc)
  then have "length p \<le> 2" using next_in_funpow_period[OF d a, of 2] by simp
  then show False using l by simp
qed

context birk
begin

lemma scycle4:
  assumes "a \<in> D" "b \<in> D" "c \<in> D" "d \<in> D"
  shows "scycle G (rlink G) [a, b, c, d] \<longleftrightarrow>
    rlink G a b \<and> rlink G b c \<and> rlink G c d \<and> rlink G d a \<and>
    \<not> cface a b \<and> \<not> cface a c \<and> \<not> cface a d \<and> \<not> cface b c \<and> \<not> cface b d \<and> \<not> cface c d"
  using assms by (auto simp: scycle_def cycle_Cons simple_def F.cyc_eq_iff)

lemma cface_enK: "cface (e (n y)) y"
  using fconnect_step[of f "e (n y)"] by (simp only: nodeK)

lemma scycle3:
  assumes "a \<in> D" "b \<in> D" "c \<in> D"
  shows "scycle G (rlink G) [a, b, c] \<longleftrightarrow>
    rlink G a b \<and> rlink G b c \<and> rlink G c a \<and> \<not> cface a b \<and> \<not> cface a c \<and> \<not> cface b c"
  using assms by (auto simp: scycle_def cycle_Cons simple_def F.cyc_eq_iff)

lemma small_ring_trivial:
  assumes l: "length q \<le> 4" and Ur: "scycle G (rlink G) q" and qD: "set q \<subseteq> D"
    and F: "a \<in> snip_ring.diskF G q" and FC: "b \<in> snip_ring.diskFC G q"
  shows False
proof -
  interpret Q: snip_ring G q using planarG Ur qD by unfold_locales
  have "nontrivial_ring G 0 q" using Q.nontrivial0P F FC by blast
  moreover have "\<not> nontrivial_ring G (if length q = 5 then 1 else 0) q"
    by (rule Birkhoff[OF _ Ur qD]) (use l in simp)
  ultimately show False using l by simp
qed

lemma revsnipI: "scycle G (rlink G) q \<Longrightarrow> set q \<subseteq> D \<Longrightarrow> revsnip G q"
  using hypermap_axioms planarG bridgelessG plainG connectedG
  by (simp add: revsnip_def revsnip_axioms_def snip_ring_def snip_ring_axioms_def)

end

locale spoke_ctx = birk +
  fixes x :: 'a
  assumes xD: "x \<in> D"
begin

definition spoke :: "'a \<Rightarrow> 'a" where "spoke y = f (e y)"

definition px :: "'a list" where "px = orb f x"

definition sr :: "'a list" where "sr = map spoke (rev px)"

lemma spoke_node [simp]: "n (spoke y) = y"
  by (simp add: spoke_def edgeK)

lemma spoke_of_node: "spoke (n y) = y"
  by (simp add: spoke_def nodeK)

lemma inj_spoke: "inj spoke"
  by (rule injI) (metis spoke_node)

lemma nn_eq: "y \<in> D \<Longrightarrow> f (e y) = n (n y)"
proof -
  assume yD: "y \<in> D"
  have "f (e (n (n (n y)))) = n (n y)" by (rule nodeK)
  then show ?thesis using nnn[OF yD] by simp
qed

lemma inv_inv_node: "y \<in> D \<Longrightarrow> inv n (inv n y) = n y"
proof -
  assume yD: "y \<in> D"
  have "inv n y = n (n y)" using nn_eq[OF yD] by (simp add: inv_node_apply)
  then have "inv n (inv n y) = inv n (n (n y))" by (rule arg_cong)
  also have "\<dots> = n y" by (rule N.inv_f)
  finally show ?thesis .
qed

lemma mem_px: "y \<in> set px \<longleftrightarrow> cface x y"
  by (simp add: px_def F.set_orb F.in_cyc_iff)

lemma distinct_px: "distinct px"
  by (simp add: px_def F.distinct_orb)

lemma mem_sr: "y \<in> set sr \<longleftrightarrow> cface x (n y)"
proof -
  have "y \<in> set sr \<longleftrightarrow> spoke (n y) \<in> spoke ` set px"
    by (simp add: sr_def spoke_of_node)
  also have "\<dots> \<longleftrightarrow> n y \<in> set px" by (rule inj_image_mem_iff[OF inj_spoke])
  finally show ?thesis by (simp add: mem_px)
qed

lemma sr_D: "y \<in> set sr \<Longrightarrow> y \<in> D"
proof -
  assume "y \<in> set sr"
  then have "cface x (n y)" by (simp add: mem_sr)
  then have "n y \<in> D" using F.fconnect_in_D xD by blast
  then show ?thesis by simp
qed

lemma sr_subset: "set sr \<subseteq> D" using sr_D by blast

lemma distinct_sr: "distinct sr"
  using distinct_px inj_on_subset[OF inj_spoke subset_UNIV] by (simp add: sr_def distinct_map)

lemma length_sr: "length sr = arity G x"
  by (simp add: sr_def px_def)

lemma prev_px: "z \<in> set px \<Longrightarrow> prev_in px z = e (n z)"
proof -
  assume z: "z \<in> set px"
  have c: "cycle (frel f) px" by (simp add: px_def F.cycle_orb)
  have pz: "prev_in px z \<in> set px" by (rule prev_in_mem[OF z])
  have "f (prev_in px z) = next_in px (prev_in px z)" by (rule cycle_next_in[OF c pz])
  also have "\<dots> = z" by (rule next_prev_in[OF distinct_px z])
  finally have "f (prev_in px z) = f (e (n z))" by (simp add: nodeK)
  then show ?thesis by simp
qed

lemma next_sr: "y \<in> set sr \<Longrightarrow> next_in sr y = f (spoke y)"
proof -
  assume y: "y \<in> set sr"
  have yD: "y \<in> D" by (rule sr_D[OF y])
  define z where "z = n y"
  have zp: "z \<in> set px" using y by (simp add: mem_sr mem_px z_def)
  have yz: "y = spoke z" by (simp add: z_def spoke_of_node)
  have "next_in sr y = spoke (next_in (rev px) z)"
    unfolding sr_def yz by (rule next_in_map) (use inj_spoke zp in \<open>auto simp: inj_on_def inj_def\<close>)
  also have "\<dots> = spoke (prev_in px z)" by (simp add: next_in_rev[OF distinct_px zp])
  also have "\<dots> = f (n z)" by (simp add: prev_px[OF zp] spoke_def)
  also have "\<dots> = f (f (e y))" using nn_eq[OF yD] by (simp add: z_def)
  finally show ?thesis by (simp add: spoke_def)
qed

lemma scycle_sr: "scycle G (rlink G) sr"
  unfolding scycle_def
proof
  show "cycle (rlink G) sr"
    by (rule cycle_from_next_rel[OF distinct_sr]) (simp add: next_sr rlink_def spoke_def)
  show "simple G sr"
    unfolding simple_def distinct_map
  proof
    show "distinct sr" by (rule distinct_sr)
    show "inj_on (cyc f) (set sr)"
    proof (rule inj_onI)
      fix y1 y2 assume y1: "y1 \<in> set sr" and y2: "y2 \<in> set sr" and c: "cyc f y1 = cyc f y2"
      have c12: "cface y1 y2" using c by (simp add: F.cyc_eq_iff)
      have x1: "cface x (n y1)" and x2: "cface x (n y2)" using y1 y2 by (simp_all add: mem_sr)
      have nn12: "cface (n y1) (n y2)" by (rule fconnect_trans[OF F.fconnect_sym[OF x1] x2])
      have a1: "cface (e (n y1)) y1" using fconnect_step[of f "e (n y1)"] by (simp only: nodeK)
      have a2: "cface (e (n y2)) y2" using fconnect_step[of f "e (n y2)"] by (simp only: nodeK)
      have "cface (e (n y1)) y2" by (rule fconnect_trans[OF a1 c12])
      then have "cface (e (n y1)) (e (n y2))" by (rule fconnect_trans[OF _ F.fconnect_sym[OF a2]])
      then have "n y1 = n y2"
        by (rule double_dart[OF _ _ nn12, rotated 2]) (use sr_D y1 y2 in simp_all)
      then show "y1 = y2" by (metis spoke_of_node)
    qed
  qed
qed

lemma fband_sr: "fband G sr y \<longleftrightarrow> adj G x y"
proof
  assume "fband G sr y"
  then obtain z where z: "z \<in> set sr" and yz: "cface y z" by (auto simp: fband_def)
  have xz: "cface x (n z)" using z by (simp add: mem_sr)
  have "cface (e (n z)) z" using fconnect_step[of f "e (n z)"] by (simp only: nodeK)
  then have "cface (e (n z)) y" by (rule fconnect_trans[OF _ F.fconnect_sym[OF yz]])
  then show "adj G x y" using xz by (auto simp: adj_def rlink_def)
next
  assume "adj G x y"
  then obtain w where xw: "cface x w" and wy: "cface (e w) y" by (auto simp: adj_iff)
  have "spoke w \<in> set sr" using xw by (simp add: mem_sr)
  moreover have "cface y (spoke w)" using F.fconnect_sym[OF wy] by (simp add: spoke_def)
  ultimately show "fband G sr y" by (auto simp: fband_def)
qed

sublocale S: snip_ring G sr
  using planarG scycle_sr sr_subset by unfold_locales

lemma diskF_sr: "y \<in> S.diskF \<longleftrightarrow> cface x y"
proof
  assume yF: "y \<in> S.diskF"
  then have yN: "y \<in> S.diskN" and yb: "\<not> fband G sr y" by (auto simp: S.diskF_def)
  from yN obtain z where z: "z \<in> set sr" and dc: "connect S.dlink (inv n z) y"
    by (auto simp: S.diskN_def S.dconnect_def)
  have zD: "z \<in> D" by (rule sr_D[OF z])
  define z0 where "z0 = inv n z"
  have fz0: "f z0 \<in> set sr"
  proof -
    have "f z0 = f (spoke z)" by (simp add: z0_def inv_node_apply spoke_def)
    then show ?thesis using next_sr[OF z] next_in_mem[OF z] by simp
  qed
  have z0b: "fband G sr z0"
    using fz0 fconnect_step[of f z0] by (auto simp: fband_def)
  define P where "P w \<longleftrightarrow> cface x w \<or> w \<in> set sr \<or> w = z0" for w
  have stepP: "P w'" if Pw: "P w" and dl: "S.dlink w w'" for w w'
  proof -
    have wr: "w \<notin> set sr" and cl: "w = n w' \<or> f w = w'"
      using dl by (auto simp: S.dlink_def clink_def)
    consider "cface x w" | "w = z0" using Pw wr by (auto simp: P_def)
    then show ?thesis
    proof cases
      case 1
      from cl show ?thesis
      proof
        assume "w = n w'"
        then have "w' \<in> set sr" using 1 by (simp add: mem_sr)
        then show ?thesis by (simp add: P_def)
      next
        assume "f w = w'"
        then have "cface x w'" using fconnect_trans[OF 1 fconnect_step[of f w]] by simp
        then show ?thesis by (simp add: P_def)
      qed
    next
      case 2
      from cl show ?thesis
      proof
        assume "w = n w'"
        then have "w' = inv n w" by simp
        also have "\<dots> = n z" using 2 inv_inv_node[OF zD] by (simp add: z0_def)
        finally have "cface x w'" using z by (simp add: mem_sr)
        then show ?thesis by (simp add: P_def)
      next
        assume "f w = w'"
        then show ?thesis using 2 fz0 by (simp add: P_def)
      qed
    qed
  qed
  have "P y" using dc unfolding z0_def[symmetric]
  proof (induction rule: rtranclp_induct)
    case base then show ?case by (simp add: P_def)
  next
    case (step w w') then show ?case by (intro stepP[OF step.IH step.hyps(2)])
  qed
  moreover have "y \<notin> set sr" using yb fband_ring by blast
  moreover have "y \<noteq> z0" using yb z0b by blast
  ultimately show "cface x y" by (simp add: P_def)
next
  assume xy: "cface x y"
  have yD: "y \<in> D" using xy xD F.fconnect_in_D by blast
  have nb: "\<not> fband G sr y"
  proof
    assume "fband G sr y"
    then obtain z where z: "z \<in> set sr" and yz: "cface y z" by (auto simp: fband_def)
    have xz: "cface x (n z)" using z by (simp add: mem_sr)
    have zD: "n z \<in> D" using sr_D[OF z] by simp
    have "cface x z" by (rule fconnect_trans[OF xy yz])
    moreover have "cface (e (n z)) z" using fconnect_step[of f "e (n z)"] by (simp only: nodeK)
    ultimately have "cface x (e (n z))" by (rule fconnect_trans[OF _ F.fconnect_sym])
    then have "cface (n z) (e (n z))" by (rule fconnect_trans[OF F.fconnect_sym[OF xz]])
    then show False using bridgelessG zD unfolding bridgeless_def by blast
  qed
  have "spoke y \<in> set sr" using xy by (simp add: mem_sr)
  then have "spoke y \<in> S.diskN" by (rule S.r_diskN)
  then have "y \<in> S.diskN" using S.diskN_node[of "spoke y"] yD by (simp add: spoke_def edgeK)
  then show "y \<in> S.diskF" using nb by (simp add: S.diskF_def)
qed

lemma not_cface_x_sr: "y \<in> set sr \<Longrightarrow> \<not> cface x y"
proof
  assume y: "y \<in> set sr" and xy: "cface x y"
  have "cface x (n y)" using y by (simp add: mem_sr)
  then have "cface (n y) y" by (rule fconnect_trans[OF F.fconnect_sym xy])
  then show False using no_cface_node sr_D[OF y] by blast
qed

lemma chordless_sr: "chordless G sr"
  unfolding chordless_def
proof (intro ballI impI notI)
  fix y1 y2
  assume ry1: "y1 \<in> set sr" and ry2: "y2 \<in> set sr" and np: "y2 \<noteq> prev_in sr y1"
    and nx: "y2 \<noteq> next_in sr y1" and a: "adj G y1 y2"
  from a obtain z where y1z: "cface y1 z" and zy2: "cface (e z) y2" by (auto simp: adj_iff)
  have y1D: "y1 \<in> D" and y2D: "y2 \<in> D" using ry1 ry2 sr_D by auto
  have zD: "z \<in> D" using y1z y1D F.fconnect_in_D by blast
  have x1: "cface x (n y1)" and x2: "cface x (n y2)" using ry1 ry2 by (simp_all add: mem_sr)
  have f12: "\<not> cface y1 y2"
  proof
    assume c: "cface y1 y2"
    then have "y1 = y2" by (rule S.r_cface[OF ry1 ry2])
    then show False using adj_no_cface[OF bridgelessG y1D a] c by simp
  qed
  have xy1: "\<not> cface x y1" and xy2: "\<not> cface x y2" using not_cface_x_sr ry1 ry2 by auto
  define q where "q = [n y2, e z, e (n y1)]"
  have qD: "set q \<subseteq> D" using y1D y2D zD by (simp add: q_def)
  have r1: "rlink G (n y2) (e z)"
    unfolding rlink_def by (rule fconnect_trans[OF cface_enK F.fconnect_sym[OF zy2]])
  have r2: "rlink G (e z) (e (n y1))"
    unfolding rlink_def ee by (rule fconnect_trans[OF F.fconnect_sym[OF y1z] F.fconnect_sym[OF cface_enK]])
  have r3: "rlink G (e (n y1)) (n y2)"
    unfolding rlink_def ee by (rule fconnect_trans[OF F.fconnect_sym[OF x1] x2])
  have d1: "\<not> cface (n y2) (e z)"
  proof
    assume "cface (n y2) (e z)"
    then have "cface x (e z)" by (rule fconnect_trans[OF x2])
    then show False using xy2 fconnect_trans[OF _ zy2] by blast
  qed
  have d2: "\<not> cface (n y2) (e (n y1))"
  proof
    assume "cface (n y2) (e (n y1))"
    then have "cface x (e (n y1))" by (rule fconnect_trans[OF x2])
    then show False using xy1 fconnect_trans[OF _ cface_enK] by blast
  qed
  have d3: "\<not> cface (e z) (e (n y1))"
  proof
    assume "cface (e z) (e (n y1))"
    then have "cface y2 (e (n y1))" by (rule fconnect_trans[OF F.fconnect_sym[OF zy2]])
    then show False using f12 F.fconnect_sym fconnect_trans[OF _ cface_enK] by blast
  qed
  have Uq: "scycle G (rlink G) q"
    unfolding q_def using y1D y2D zD r1 r2 r3 d1 d2 d3 by (subst scycle3) simp_all
  interpret Q: revsnip G q by (rule revsnipI[OF Uq qD])
  \<comment> \<open>a dart inside the 3-ring: the spoke before y1\<close>
  define t where "t = n (e (n y1))"
  have tD: "t \<in> D" using y1D by (simp add: t_def)
  have nt: "n t = f (n y1)" using nn_eq[of "e (n y1)"] y1D by (simp add: t_def)
  have rt: "t \<in> set sr" using x1 by (simp add: mem_sr nt)
  have nxt: "next_in sr t = y1" using next_sr[OF rt] by (simp add: spoke_def t_def nodeK)
  have tp: "t = prev_in sr y1" using prev_next_in[OF distinct_sr rt] nxt by simp
  have tN: "t \<in> Q.diskN"
    using Q.diskN_node[of "e (n y1)"] Q.r_diskN[of "e (n y1)"] y1D by (simp add: t_def q_def)
  have tb: "\<not> fband G q t"
  proof
    assume "fband G q t"
    then consider "cface t (n y2)" | "cface t (e z)" | "cface t (e (n y1))"
      by (auto simp: fband_def q_def)
    then show False
    proof cases
      case 1
      then have "cface t x" by (rule fconnect_trans[OF _ F.fconnect_sym[OF x2]])
      then show False using not_cface_x_sr[OF rt] F.fconnect_sym by blast
    next
      case 2
      then have "cface t y2" by (rule fconnect_trans[OF _ zy2])
      then have "t = y2" by (rule S.r_cface[OF rt ry2])
      then show False using np tp by simp
    next
      case 3
      then have "cface t y1" by (rule fconnect_trans[OF _ cface_enK])
      then have "cface t (f (spoke t))" using next_sr[OF rt] nxt by simp
      then have "cface t (e t)" by (simp add: spoke_def)
      then show False using bridgelessG tD unfolding bridgeless_def by blast
    qed
  qed
  have tF: "t \<in> Q.diskF" using tN tb by (simp add: Q.diskF_def)
  \<comment> \<open>a dart outside the 3-ring\<close>
  define u where "u = n (n y1)"
  have uD: "u \<in> D" using y1D by (simp add: u_def)
  have u_eq: "u = f (e y1)" using nn_eq[OF y1D] by (simp add: u_def)
  have pq: "proper_ring G q" by (simp add: q_def)
  have "e (e (n y1)) \<notin> Q.diskN" by (rule Q.diskN_edge_ring[OF pq]) (simp add: q_def)
  then have uN: "u \<notin> Q.diskN" using Q.diskN_node[of "n y1"] y1D by (simp add: u_def)
  have ub: "\<not> fband G q u"
  proof
    assume "fband G q u"
    then consider "cface u (n y2)" | "cface u (e z)" | "cface u (e (n y1))"
      by (auto simp: fband_def q_def)
    then show False
    proof cases
      case 1
      then have "cface u x" by (rule fconnect_trans[OF _ F.fconnect_sym[OF x2]])
      then have "cface u (n y1)" by (rule fconnect_trans[OF _ x1])
      moreover have "n y1 = f (e u)" by (simp add: u_def nodeK)
      ultimately have "cface u (e u)" by simp
      then show False using bridgelessG uD unfolding bridgeless_def by blast
    next
      case 2
      then have "cface u y2" by (rule fconnect_trans[OF _ zy2])
      moreover have "next_in sr y1 = f u" using next_sr[OF ry1] by (simp add: spoke_def u_eq)
      ultimately have "cface (next_in sr y1) y2" by simp
      then have "next_in sr y1 = y2" by (rule S.r_cface[OF next_in_mem[OF ry1] ry2])
      then show False using nx by simp
    next
      case 3
      then have "cface (e y1) (e (n y1))" by (simp add: u_eq)
      then have "cface (e y1) y1" by (rule fconnect_trans[OF _ cface_enK])
      then have "cface y1 (e y1)" by (rule F.fconnect_sym)
      then show False using bridgelessG y1D unfolding bridgeless_def by blast
    qed
  qed
  have uFC: "u \<in> Q.diskFC" using uD uN ub by (simp add: Q.diskFC_def)
  show False by (rule small_ring_trivial[OF _ Uq qD tF uFC]) (simp add: q_def)
qed

lemma size_spoke_ring: "length sr = arity G x" by (rule length_sr)

subsection \<open>Faces have arity at least five\<close>

text \<open>The Birkhoff theorem only says that the spoke ring has an empty exterior; non-colourability
  is then used to rule out small maps, through an explicit colouring.\<close>

definition ccol :: "nat \<Rightarrow> nat \<Rightarrow> color" where
  "ccol L i = (if i = 2 \<and> L = 3 then Color3 else if i = 0 \<or> i = 2 then Color1 else Color2)"

lemma ccol_ne0 [simp]: "ccol L i \<noteq> Color0" "Color0 \<noteq> ccol L i"
  by (simp_all add: ccol_def)

lemma ccol_ne:
  assumes "L \<le> 4" "i < L" "j < L" "i \<noteq> j" "j = Suc i mod L \<or> i = Suc j mod L"
  shows "ccol L i \<noteq> ccol L j"
proof -
  have "L = 2 \<or> L = 3 \<or> L = 4" using assms(1-4) by linarith
  moreover have "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3" "j = 0 \<or> j = 1 \<or> j = 2 \<or> j = 3"
    using assms(1-3) by linarith+
  ultimately show ?thesis using assms(2-5) by (auto simp: ccol_def)
qed

definition colk :: "'a \<Rightarrow> color" where
  "colk y = (if cface x y then Color0 else ccol (length sr) (lindex sr (fproj G sr y)))"

lemma min_arity: "4 < arity G x"
proof (rule ccontr)
  assume "\<not> 4 < arity G x"
  then have L4: "length sr \<le> 4" by (simp add: length_sr)
  have xF: "x \<in> S.diskF" by (simp add: diskF_sr)
  have FC0: "S.diskFC = {}" using small_ring_trivial[OF L4 scycle_sr sr_subset xF] by blast
  have bandI: "fband G sr y" if yD: "y \<in> D" and xy: "\<not> cface x y" for y
  proof (rule ccontr)
    assume nb: "\<not> fband G sr y"
    have "y \<notin> S.diskN" using xy nb diskF_sr by (auto simp: S.diskF_def)
    then have "y \<in> S.diskFC" using yD nb by (simp add: S.diskFC_def)
    then show False using FC0 by simp
  qed
  have "coloring G colk"
    unfolding coloring_def
  proof (intro conjI ballI)
    fix y assume yD: "y \<in> D"
    show "colk (f y) = colk y"
    proof (cases "cface x y")
      case True then show ?thesis by (simp add: colk_def)
    next
      case False
      have "fproj G sr y = fproj G sr (f y)"
        by (rule fproj_cface[OF fconnect_step bandI[OF yD False]])
      then show ?thesis using False by (simp add: colk_def)
    qed
  next
    fix y assume yD: "y \<in> D"
    have eyD: "e y \<in> D" using yD by simp
    have nbr: "\<not> (cface x y \<and> cface x (e y))"
    proof
      assume "cface x y \<and> cface x (e y)"
      then have "cface y (e y)" using fconnect_trans[OF F.fconnect_sym] by blast
      then show False using bridgelessG yD unfolding bridgeless_def by blast
    qed
    show "colk (e y) \<noteq> colk y"
    proof (cases "cface x y \<or> cface x (e y)")
      case True then show ?thesis using nbr by (auto simp: colk_def)
    next
      case False
      then have b1: "fband G sr y" and b2: "fband G sr (e y)" using bandI yD eyD by auto
      define z1 where "z1 = fproj G sr y"
      define z2 where "z2 = fproj G sr (e y)"
      have rz1: "z1 \<in> set sr" and yz1: "cface y z1" using fprojP[OF b1] by (simp_all add: z1_def)
      have rz2: "z2 \<in> set sr" and yz2: "cface (e y) z2" using fprojP[OF b2] by (simp_all add: z2_def)
      have a12: "adj G z1 z2" unfolding adj_iff using F.fconnect_sym[OF yz1] yz2 by blast
      have ne: "z1 \<noteq> z2" using adj_no_cface[OF bridgelessG sr_D[OF rz1] a12] by auto
      have pn: "z2 = prev_in sr z1 \<or> z2 = next_in sr z1"
        using chordless_sr rz1 rz2 a12 unfolding chordless_def by blast
      define L where "L = length sr"
      define i1 where "i1 = lindex sr z1"
      define i2 where "i2 = lindex sr z2"
      have i1L: "i1 < L" and i2L: "i2 < L" using rz1 rz2 lindex_less by (auto simp: i1_def i2_def L_def)
      have i12: "i1 \<noteq> i2" using ne nth_lindex[OF rz1] nth_lindex[OF rz2] by (auto simp: i1_def i2_def)
      have "i2 = Suc i1 mod L \<or> i1 = Suc i2 mod L"
        using pn
      proof
        assume "z2 = prev_in sr z1"
        then have "z1 = next_in sr z2" using next_prev_in[OF distinct_sr rz1] by simp
        then show ?thesis using next_in_lindex[OF distinct_sr rz2] by (simp add: i1_def i2_def L_def)
      next
        assume "z2 = next_in sr z1"
        then show ?thesis using next_in_lindex[OF distinct_sr rz1] by (simp add: i1_def i2_def L_def)
      qed
      then have "ccol L i1 \<noteq> ccol L i2" using ccol_ne L4 i1L i2L i12 by (simp add: L_def)
      then show ?thesis using False by (simp add: colk_def z1_def z2_def i1_def i2_def L_def)
    qed
  qed
  then show False using noncolG by (auto simp: four_colorable_def)
qed

lemma length_sr_gt: "4 < length sr" using min_arity by (simp add: length_sr)

subsection \<open>Adjacency around a face\<close>

lemma adj_x_sr: "z \<in> set sr \<Longrightarrow> adj G x z"
  using fband_sr fband_ring by blast

lemma fband_srE:
  assumes "adj G x y"
  obtains z where "z \<in> set sr" "cface y z" "y \<in> D" "z \<in> D"
proof -
  obtain z where rz: "z \<in> set sr" and yz: "cface y z" using assms fband_sr by (auto simp: fband_def)
  have zD: "z \<in> D" by (rule sr_D[OF rz])
  then have "y \<in> D" using yz F.fconnect_in_D by blast
  then show thesis using that rz yz zD by blast
qed

lemma sr_adj_next_prev:
  assumes ru: "u \<in> set sr" and rv: "v \<in> set sr" and a: "adj G u v"
  shows "next_in sr u = v \<or> next_in sr v = u"
proof -
  have "v = prev_in sr u \<or> v = next_in sr u"
    using chordless_sr ru rv a unfolding chordless_def by blast
  then show ?thesis using next_prev_in[OF distinct_sr ru] by auto
qed

lemma adj11_edge:
  assumes xy: "adj G x y" and xey: "adj G x (e y)"
  shows "y \<in> set sr \<or> e y \<in> set sr"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have ny: "y \<notin> set sr" and ney: "e y \<notin> set sr" by auto
  obtain z where rz: "z \<in> set sr" and yz: "cface y z" and yD: "y \<in> D" and zD: "z \<in> D"
    using xy by (rule fband_srE)
  obtain t where rt: "t \<in> set sr" and eyt: "cface (e y) t" and eyD: "e y \<in> D" and tD: "t \<in> D"
    using xey by (rule fband_srE)
  have azt: "adj G z t" unfolding adj_iff using F.fconnect_sym[OF yz] eyt by blast
  have tn: "t \<noteq> next_in sr z"
  proof
    assume "t = next_in sr z"
    then have "t = f (f (e z))" using next_sr[OF rz] by (simp add: spoke_def)
    then have "cface (e y) (e z)" using eyt by simp
    then have "y = z" by (rule double_dart[OF yD zD yz])
    then show False using ny rz by simp
  qed
  have tp: "t \<noteq> prev_in sr z"
  proof
    assume "t = prev_in sr z"
    then have "z = next_in sr t" using next_prev_in[OF distinct_sr rz] by simp
    then have "z = f (f (e t))" using next_sr[OF rt] by (simp add: spoke_def)
    then have "cface y (e t)" using yz by simp
    then have "cface (e (e y)) (e t)" by simp
    then have "e y = t" by (rule double_dart[OF eyD tD eyt])
    then show False using ney rt by simp
  qed
  show False using chordless_sr rz rt tn tp azt unfolding chordless_def by blast
qed

lemma fcard_adj_adj:
  assumes xy: "adj G x y"
  shows "fcard f {t. adj G y t \<and> adj G x t} = 2"
proof -
  obtain y1 where ry1: "y1 \<in> set sr" and yy1: "cface y y1" and yD: "y \<in> D"
    using xy by (rule fband_srE)
  define z1 where "z1 = prev_in sr y1"
  define z2 where "z2 = next_in sr y1"
  have rz1: "z1 \<in> set sr" and rz2: "z2 \<in> set sr"
    using prev_in_mem[OF ry1] next_in_mem[OF ry1] by (simp_all add: z1_def z2_def)
  have nz: "\<not> cface z1 z2"
  proof
    assume "cface z1 z2"
    then have "z1 = z2" by (rule S.r_cface[OF rz1 rz2])
    then show False using next_in_ne_prev[OF distinct_sr ry1] length_sr_gt by (simp add: z1_def z2_def)
  qed
  have "rlink G z1 y1" unfolding z1_def by (rule S.rlink_prev[OF ry1])
  then have "adj G y1 z1" by (rule adj_sym[OF plainG rlink_adj])
  then have A1: "adj G y z1" using adj_cface[OF yy1] by simp
  have "rlink G y1 z2" unfolding z2_def by (rule cycle_next_in_rel[OF S.cycle_r ry1])
  then have A2: "adj G y z2" using adj_cface[OF yy1] rlink_adj by blast
  define A where "A = {t. adj G y t \<and> adj G x t}"
  have img: "cyc f ` A = {cyc f z1, cyc f z2}"
  proof
    show "cyc f ` A \<subseteq> {cyc f z1, cyc f z2}"
    proof
      fix c assume "c \<in> cyc f ` A"
      then obtain t where yt: "adj G y t" and xt: "adj G x t" and c: "c = cyc f t" by (auto simp: A_def)
      obtain t1 where rt1: "t1 \<in> set sr" and tt1: "cface t t1" using xt by (rule fband_srE)
      have "adj G y1 t1" using yt adj_cface[OF yy1] adj_cface_r[OF tt1] by simp
      then have "t1 = z1 \<or> t1 = z2"
        using chordless_sr ry1 rt1 unfolding chordless_def z1_def z2_def by blast
      moreover have "c = cyc f t1" using tt1 c by (simp add: F.cyc_eq_iff)
      ultimately show "c \<in> {cyc f z1, cyc f z2}" by auto
    qed
    show "{cyc f z1, cyc f z2} \<subseteq> cyc f ` A"
      using A1 A2 adj_x_sr[OF rz1] adj_x_sr[OF rz2] by (auto simp: A_def)
  qed
  have "cyc f z1 \<noteq> cyc f z2" using nz by (simp add: F.cyc_eq_iff)
  then show ?thesis using img by (simp add: fcard_def A_def[symmetric])
qed

lemma adj12_edge:
  assumes xy: "adj G x y" and xz: "adj G x z" and zey: "adj G z (e y)"
  shows "cface z y \<or> adj G z y \<or> cface x (e y) \<or> adj G x (e y)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have zFy: "\<not> cface z y" and zAy: "\<not> adj G z y" and xFey: "\<not> cface x (e y)"
    and xAey: "\<not> adj G x (e y)" by auto
  obtain y1 where ry1: "y1 \<in> set sr" and yy1: "cface y y1" and yD: "y \<in> D" and y1D: "y1 \<in> D"
    using xy by (rule fband_srE)
  obtain z1 where rz1: "z1 \<in> set sr" and zz1: "cface z z1" and zD: "z \<in> D" and z1D: "z1 \<in> D"
    using xz by (rule fband_srE)
  obtain x1 where zx1: "cface z x1" and ex1ey: "cface (e x1) (e y)" using zey by (auto simp: adj_iff)
  have x1D: "x1 \<in> D" using zx1 zD F.fconnect_in_D by blast
  have xn1: "cface x (n y1)" and xnz1: "cface x (n z1)" using ry1 rz1 by (simp_all add: mem_sr)
  have nxy: "\<not> cface x y" using not_cface_x_sr[OF ry1] fconnect_trans[OF _ yy1] by blast
  have nxz: "\<not> cface x z" using not_cface_x_sr[OF rz1] fconnect_trans[OF _ zz1] by blast
  have nzey: "\<not> cface z (e y)"
  proof
    assume "cface z (e y)"
    then have "cface (e y) z1" by (rule fconnect_trans[OF F.fconnect_sym zz1])
    then have "fband G sr (e y)" using rz1 by (auto simp: fband_def)
    then show False using xAey fband_sr by simp
  qed
  have ez1: "cface (e (n z1)) z" by (rule fconnect_trans[OF cface_enK F.fconnect_sym[OF zz1]])
  have adjxnn: "adj G x (n (n w))" if "cface x (n w)" for w
    using adj_sym[OF plainG adjN[of "n w"]] adj_cface[OF that] by simp
  define q where "q = [y, e x1, e (n z1), n y1]"
  have qD: "set q \<subseteq> D" using yD x1D z1D y1D by (simp add: q_def)
  have r1: "rlink G y (e x1)" unfolding rlink_def by (rule F.fconnect_sym[OF ex1ey])
  have r2: "rlink G (e x1) (e (n z1))"
    unfolding rlink_def ee by (rule fconnect_trans[OF F.fconnect_sym[OF zx1] F.fconnect_sym[OF ez1]])
  have r3: "rlink G (e (n z1)) (n y1)"
    unfolding rlink_def ee by (rule fconnect_trans[OF F.fconnect_sym[OF xnz1] xn1])
  have r4: "rlink G (n y1) y"
    unfolding rlink_def by (rule fconnect_trans[OF cface_enK F.fconnect_sym[OF yy1]])
  have d1: "\<not> cface y (e x1)"
  proof
    assume "cface y (e x1)"
    then have "cface y (e y)" by (rule fconnect_trans[OF _ ex1ey])
    then show False using bridgelessG yD unfolding bridgeless_def by blast
  qed
  have d2: "\<not> cface y (e (n z1))"
    using zFy fconnect_trans[OF _ ez1, of y] F.fconnect_sym by blast
  have d3: "\<not> cface y (n y1)"
  proof
    assume "cface y (n y1)"
    then have "cface y x" by (rule fconnect_trans[OF _ F.fconnect_sym[OF xn1]])
    then show False using nxy F.fconnect_sym by blast
  qed
  have d4: "\<not> cface (e x1) (e (n z1))"
  proof
    assume "cface (e x1) (e (n z1))"
    then have "cface (e x1) z" by (rule fconnect_trans[OF _ ez1])
    then have "cface (e y) z" by (rule fconnect_trans[OF F.fconnect_sym[OF ex1ey]])
    then show False using nzey F.fconnect_sym by blast
  qed
  have d5: "\<not> cface (e x1) (n y1)"
  proof
    assume "cface (e x1) (n y1)"
    then have "cface (e x1) x" by (rule fconnect_trans[OF _ F.fconnect_sym[OF xn1]])
    then have "cface (e y) x" by (rule fconnect_trans[OF F.fconnect_sym[OF ex1ey]])
    then show False using xFey F.fconnect_sym by blast
  qed
  have d6: "\<not> cface (e (n z1)) (n y1)"
  proof
    assume "cface (e (n z1)) (n y1)"
    then have "cface z (n y1)" by (rule fconnect_trans[OF F.fconnect_sym[OF ez1]])
    then have "cface z x" by (rule fconnect_trans[OF _ F.fconnect_sym[OF xn1]])
    then show False using nxz F.fconnect_sym by blast
  qed
  have Uq: "scycle G (rlink G) q"
    unfolding q_def using yD x1D z1D y1D r1 r2 r3 r4 d1 d2 d3 d4 d5 d6 by (subst scycle4) simp_all
  interpret Q: revsnip G q by (rule revsnipI[OF Uq qD])
  \<comment> \<open>inside: the third spoke at node y1\<close>
  define u where "u = n (n y1)"
  have uD: "u \<in> D" using y1D by (simp add: u_def)
  have u_eq: "u = f (e y1)" using nn_eq[OF y1D] by (simp add: u_def)
  have uN: "u \<in> Q.diskN"
    using Q.diskN_node[of "n y1"] Q.r_diskN[of "n y1"] y1D by (simp add: u_def q_def)
  have ub: "\<not> fband G q u"
  proof
    assume "fband G q u"
    then consider "cface u y" | "cface u (e x1)" | "cface u (e (n z1))" | "cface u (n y1)"
      by (auto simp: fband_def q_def)
    then show False
    proof cases
      case 1
      then have "cface (e y1) y1" using u_eq fconnect_trans[OF _ yy1] by simp
      then show False using bridgelessG y1D F.fconnect_sym unfolding bridgeless_def by blast
    next
      case 2
      then have "cface u (e y)" by (rule fconnect_trans[OF _ ex1ey])
      then have "adj G x (e y)" using adjxnn[OF xn1] adj_cface_r by (simp add: u_def)
      then show False using xAey by simp
    next
      case 3
      then have uz: "cface u z" by (rule fconnect_trans[OF _ ez1])
      have "adj G y1 u" using adjE[of y1] by (simp add: u_eq)
      then have "adj G y z" using adj_cface[OF yy1] adj_cface_r[OF uz] by simp
      then show False using zAy adj_sym[OF plainG] by blast
    next
      case 4
      moreover have "n y1 = f (e u)" by (simp add: u_def nodeK)
      ultimately have "cface u (e u)" by simp
      then show False using bridgelessG uD unfolding bridgeless_def by blast
    qed
  qed
  have uF: "u \<in> Q.diskF" using uN ub by (simp add: Q.diskF_def)
  \<comment> \<open>outside: the third spoke at node z1\<close>
  define v where "v = n (n z1)"
  have vD: "v \<in> D" using z1D by (simp add: v_def)
  have v_eq: "v = f (e z1)" using nn_eq[OF z1D] by (simp add: v_def)
  have pq: "proper_ring G q" by (simp add: q_def)
  have "e (e (n z1)) \<notin> Q.diskN" by (rule Q.diskN_edge_ring[OF pq]) (simp add: q_def)
  then have vN: "v \<notin> Q.diskN" using Q.diskN_node[of "n z1"] z1D by (simp add: v_def)
  have vb: "\<not> fband G q v"
  proof
    assume "fband G q v"
    then consider "cface v y" | "cface v (e x1)" | "cface v (e (n z1))" | "cface v (n y1)"
      by (auto simp: fband_def q_def)
    then show False
    proof cases
      case 1
      then have ez1y: "cface (e z1) y" by (simp add: v_eq)
      have "adj G z1 y" using adj_cface_r[OF ez1y, of z1] by simp
      then have "adj G z y" using adj_cface[OF zz1] by simp
      then show False using zAy by simp
    next
      case 2
      then have "cface v (e y)" by (rule fconnect_trans[OF _ ex1ey])
      then have "adj G x (e y)" using adjxnn[OF xnz1] adj_cface_r by (simp add: v_def)
      then show False using xAey by simp
    next
      case 3
      then have "cface (e z1) (e (n z1))" by (simp add: v_eq)
      then have "cface (e z1) z1" by (rule fconnect_trans[OF _ cface_enK])
      then show False using bridgelessG z1D F.fconnect_sym unfolding bridgeless_def by blast
    next
      case 4
      then have "cface v x" by (rule fconnect_trans[OF _ F.fconnect_sym[OF xn1]])
      then have "cface v (n z1)" by (rule fconnect_trans[OF _ xnz1])
      moreover have "n z1 = f (e v)" by (simp add: v_def nodeK)
      ultimately have "cface v (e v)" by simp
      then show False using bridgelessG vD unfolding bridgeless_def by blast
    qed
  qed
  have vFC: "v \<in> Q.diskFC" using vD vN vb by (simp add: Q.diskFC_def)
  show False by (rule small_ring_trivial[OF _ Uq qD uF vFC]) (simp add: q_def)
qed

lemma card_gt2E:
  assumes "2 < card S"
  obtains a b c where "a \<in> S" "b \<in> S" "c \<in> S" "a \<noteq> b" "a \<noteq> c" "b \<noteq> c"
proof -
  have fin: "finite S" using assms card.infinite by fastforce
  obtain a where a: "a \<in> S" using assms by fastforce
  have "1 < card (S - {a})" using assms a fin by (simp add: card_Diff_singleton)
  then have "S - {a} \<noteq> {}" by (cases "S - {a} = {}") auto
  then obtain b where b: "b \<in> S - {a}" by blast
  have "0 < card (S - {a} - {b})" using \<open>1 < card (S - {a})\<close> b fin by (simp add: card_Diff_singleton)
  then have "S - {a} - {b} \<noteq> {}" by (cases "S - {a} - {b} = {}") auto
  then obtain c where c: "c \<in> S - {a} - {b}" by blast
  show thesis using that a b c by blast
qed

lemma fcard_adj_max:
  assumes xFy: "\<not> cface x y"
  shows "fcard f {t. adj G y t \<and> adj G x t} \<le> 2"
proof (cases "adj G x y")
  case True then show ?thesis by (simp add: fcard_adj_adj)
next
  case xAy: False
  define A where "A = {t. adj G y t \<and> adj G x t}"
  show ?thesis
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have "2 < card (cyc f ` A)" by (simp add: fcard_def A_def)
    then obtain c1 c2 c3 where c: "c1 \<in> cyc f ` A" "c2 \<in> cyc f ` A" "c3 \<in> cyc f ` A"
      and cne: "c1 \<noteq> c2" "c1 \<noteq> c3" "c2 \<noteq> c3" by (rule card_gt2E)
    then obtain z1 z2 z3 where zA: "z1 \<in> A" "z2 \<in> A" "z3 \<in> A"
      and zc: "c1 = cyc f z1" "c2 = cyc f z2" "c3 = cyc f z3" by blast
    have zne: "\<not> cface z1 z2" "\<not> cface z1 z3" "\<not> cface z2 z3"
      using cne zc by (simp_all add: F.cyc_eq_iff)
    have cross: "adj G z t" if zA': "z \<in> A" and tA: "t \<in> A" and zt: "\<not> cface z t" for z t
    proof -
      have yz: "adj G y z" and xz: "adj G x z" using zA' by (simp_all add: A_def)
      have yt: "adj G y t" and xt: "adj G x t" using tA by (simp_all add: A_def)
      obtain w where yw: "cface y w" and ewt: "cface (e w) t" using yt by (auto simp: adj_iff)
      have xew: "adj G x (e w)" using xt adj_cface_r[OF ewt] by simp
      have "adj G w z" using yz adj_cface[OF yw] by simp
      then have zw: "adj G z (e (e w))" using adj_sym[OF plainG] by simp
      have "cface z (e w) \<or> adj G z (e w) \<or> cface x (e (e w)) \<or> adj G x (e (e w))"
        by (rule adj12_edge[OF xew xz zw])
      moreover have "\<not> cface x w" using xFy fconnect_trans[OF _ F.fconnect_sym[OF yw]] by blast
      moreover have "\<not> adj G x w" using xAy adj_cface_r[OF yw] by simp
      moreover have "\<not> cface z (e w)" using zt fconnect_trans[OF _ ewt] by blast
      ultimately have "adj G z (e w)" by simp
      then show ?thesis using adj_cface_r[OF ewt] by simp
    qed
    have a12: "adj G z1 z2" and a13: "adj G z1 z3" and a23: "adj G z2 z3"
      using cross zA zne by auto
    obtain t1 where rt1: "t1 \<in> set sr" and zt1: "cface z1 t1"
      using zA(1) by (auto simp: A_def elim: fband_srE)
    obtain t2 where rt2: "t2 \<in> set sr" and zt2: "cface z2 t2"
      using zA(2) by (auto simp: A_def elim: fband_srE)
    obtain t3 where rt3: "t3 \<in> set sr" and zt3: "cface z3 t3"
      using zA(3) by (auto simp: A_def elim: fband_srE)
    have ta: "adj G t1 t2" "adj G t1 t3" "adj G t2 t3"
      using a12 a13 a23 adj_cface[OF zt1] adj_cface[OF zt2] adj_cface_r[OF zt2] adj_cface_r[OF zt3]
      by simp_all
    have tne: "t1 \<noteq> t2" "t1 \<noteq> t3" "t2 \<noteq> t3"
      using ta adj_no_cface[OF bridgelessG sr_D[OF rt1]] adj_no_cface[OF bridgelessG sr_D[OF rt2]]
      by auto
    have "length sr \<le> 3"
      by (rule next_in_triangle[OF distinct_sr rt1 rt2 rt3 tne
            sr_adj_next_prev[OF rt1 rt2 ta(1)] sr_adj_next_prev[OF rt1 rt3 ta(2)]
            sr_adj_next_prev[OF rt2 rt3 ta(3)]])
    then show False using length_sr_gt by simp
  qed
qed

end

context birk
begin

lemma spoke_ctxI: "y \<in> D \<Longrightarrow> spoke_ctx G y"
  using hypermap_axioms mce by (simp add: spoke_ctx_def spoke_ctx_axioms_def birk_def birk_axioms_def)

theorem minimal_counter_example_is_pentagonal: "pentagonal G"
  unfolding pentagonal_def
proof
  fix y assume "y \<in> D"
  then interpret Sp: spoke_ctx G y by (rule spoke_ctxI)
  show "4 < arity G y" by (rule Sp.min_arity)
qed

theorem minimal_counter_example_is_plain_cubic_pentagonal: "plain_cubic_pentagonal G"
  using hypermap_axioms plainG cubicG minimal_counter_example_is_pentagonal
  by (simp add: plain_cubic_pentagonal_def plain_cubic_def)

end

end
