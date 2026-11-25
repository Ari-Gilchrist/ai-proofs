(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Revsnip.thy
    Proper and nontrivial rings, the reversed ring, chord rings, and the Kempe closure of
    disk ring traces.
    Ported from G. Gonthier's Coq development (revsnip.v).
*)
theory Revsnip
  imports Snip Kempe
begin

section \<open>Proper and nontrivial rings\<close>

definition proper_ring :: "'a hypermap \<Rightarrow> 'a list \<Rightarrow> bool" where
  "proper_ring G r = (case r of x # y # z # _ \<Rightarrow> True | [x, y] \<Rightarrow> edge G x \<noteq> y | _ \<Rightarrow> False)"

lemma proper_ring_simps [simp]:
  "\<not> proper_ring G []" "\<not> proper_ring G [x]" "proper_ring G [x, y] \<longleftrightarrow> edge G x \<noteq> y"
  "proper_ring G (x # y # z # p)"
  by (simp_all add: proper_ring_def)

lemma size_proper_ring: "2 < length r \<Longrightarrow> proper_ring G r"
  by (cases r rule: remdups_adj.cases) (auto simp: proper_ring_def split: list.splits)

definition nontrivial_ring :: "'a hypermap \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> bool" where
  "nontrivial_ring G m r \<longleftrightarrow>
     m < fcard (face G) (snip_ring.diskF G r) \<and> m < fcard (face G) (snip_ring.diskFC G r)"

definition rev_ring :: "'a hypermap \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rev_ring G r = rev (map (edge G) r)"

context hypermap
begin

lemma fprojP: "fband G p x \<Longrightarrow> fproj G p x \<in> set p \<and> cface x (fproj G p x)"
proof -
  assume "fband G p x"
  then have "find (fconnect f x) p \<noteq> None" by (auto simp: fband_def find_None_iff)
  then obtain y where y: "find (fconnect f x) p = Some y" by blast
  then have "y \<in> set p \<and> cface x y" by (auto simp: find_Some_iff)
  then show ?thesis using y by (simp add: fproj_def)
qed

lemma fproj_cface:
  assumes xy: "cface x y" and b: "fband G p x"
  shows "fproj G p x = fproj G p y"
proof -
  have fx: "fconnect f x = fconnect f y"
  proof
    fix w
    show "cface x w = cface y w"
      using fconnect_trans[OF xy, of w] fconnect_trans[OF F.fconnect_sym[OF xy], of w] by blast
  qed
  have "find (fconnect f x) p \<noteq> None" using b by (auto simp: fband_def find_None_iff)
  then obtain z where z: "find (fconnect f x) p = Some z" by blast
  then have "find (fconnect f y) p = Some z" using fx by simp
  then show ?thesis using z by (simp add: fproj_def)
qed

lemma simple_fproj: "simple G p \<Longrightarrow> x \<in> set p \<Longrightarrow> fproj G p x = x"
proof -
  assume s: "simple G p" and x: "x \<in> set p"
  have "fband G p x" using x by (rule fband_ring)
  then have "fproj G p x \<in> set p" "cface x (fproj G p x)" using fprojP by auto
  then show ?thesis using simple_cface[OF s x] by metis
qed

lemma connected_clink:
  assumes cc: "connected G" and x: "x \<in> D" and y: "y \<in> D"
  obtains p where "path (clink G) x p" "lastd x p = y"
proof -
  have "card (comp_of (glink G) ` D) = 1" using cc by (simp add: connected_def n_comp_def)
  then obtain C where C: "comp_of (glink G) ` D = {C}" by (auto simp: card_1_singleton_iff)
  then have "comp_of (glink G) x = comp_of (glink G) y" using x y by blast
  moreover have "y \<in> comp_of (glink G) y" by (simp add: comp_of_def)
  ultimately have "y \<in> comp_of (glink G) x" by simp
  then have "gcomp G x y" by (simp add: comp_of_def)
  then have "connect (clink G) x y" by (simp add: clink_glink)
  then show ?thesis using that connect_path by metis
qed

end

lemma next_next_in_size:
  assumes d: "distinct r" and x: "x \<in> set r" and nn: "next_in r (next_in r x) = x"
  shows "length r \<le> 2"
proof (rule ccontr)
  assume L: "\<not> length r \<le> 2"
  define i where "i = lindex r x"
  have i: "i < length r" "r ! i = x" using x by (simp_all add: i_def lindex_less nth_lindex)
  have n1: "next_in r x = r ! (Suc i mod length r)" using x by (simp add: next_in_def i_def)
  have L0: "0 < length r" using i(1) by linarith
  have j: "Suc i mod length r < length r" using L0 by simp
  have "lindex r (r ! (Suc i mod length r)) = Suc i mod length r" by (rule lindex_nth_distinct[OF d j])
  moreover have "r ! (Suc i mod length r) \<in> set r" using j by simp
  ultimately have "next_in r (next_in r x) = r ! (Suc (Suc i mod length r) mod length r)"
    using n1 by (simp add: next_in_def)
  also have "Suc (Suc i mod length r) mod length r = Suc (Suc i) mod length r" by (simp add: mod_Suc_eq)
  finally have hh: "r ! (Suc (Suc i) mod length r) = r ! i" using nn i by simp
  have j2: "Suc (Suc i) mod length r < length r" using L0 by simp
  have md: "Suc (Suc i) mod length r = i" using nth_eq_iff_index_eq[OF d j2 i(1)] hh by blast
  consider (a) "Suc (Suc i) < length r" | (b) "Suc (Suc i) = length r"
    | (c) "Suc (Suc i) = Suc (length r)" using i(1) by linarith
  then show False
  proof cases
    case a
    then show False using \<open>Suc (Suc i) mod length r = i\<close> by simp
  next
    case b
    then show False using \<open>Suc (Suc i) mod length r = i\<close> L by simp
  next
    case c
    have "Suc (Suc i) mod length r = Suc 0"
    proof -
      have "Suc (Suc i) = length r + 1" using c by simp
      then have "Suc (Suc i) mod length r = 1 mod length r" by (metis mod_add_self1 add.commute)
      then show ?thesis using L by simp
    qed
    then show False using \<open>Suc (Suc i) mod length r = i\<close> c L by simp
  qed
qed

section \<open>Arcs of a cyclic sequence\<close>

definition arc :: "'b list \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b list" where
  "arc s a b = (let t = rot (lindex s a) s in take (lindex t b) t)"

lemma nth_rot:
  assumes i: "i \<le> length s" and j: "j < length s"
  shows "rot i s ! j = s ! ((i + j) mod length s)"
proof (cases "j < length s - i")
  case True
  then have "rot i s ! j = s ! (i + j)" by (simp add: rot_def nth_append)
  moreover have "(i + j) mod length s = i + j" using True by simp
  ultimately show ?thesis by simp
next
  case False
  then have "rot i s ! j = s ! (j - (length s - i))" using i j by (simp add: rot_def nth_append)
  moreover have "(i + j) mod length s = j - (length s - i)"
  proof -
    have eq: "i + j = (j - (length s - i)) + length s" using False i by simp
    have "(i + j) mod length s = ((j - (length s - i)) + length s) mod length s" by (simp only: eq)
    also have "\<dots> = (j - (length s - i)) mod length s" by (rule mod_add_self2)
    finally have "(i + j) mod length s = (j - (length s - i)) mod length s" .
    also have "\<dots> = j - (length s - i)" using j by simp
    finally show ?thesis .
  qed
  ultimately show ?thesis by simp
qed

lemma rot_rot:
  assumes i: "i < length s" and j: "j < length s"
  shows "rot j (rot i s) = rot ((i + j) mod length s) s"
proof (rule nth_equalityI)
  show "length (rot j (rot i s)) = length (rot ((i + j) mod length s) s)" by simp
  fix k assume "k < length (rot j (rot i s))"
  then have k: "k < length s" by simp
  have L0: "0 < length s" using i by linarith
  have m: "(j + k) mod length s < length s" using L0 by simp
  have "rot j (rot i s) ! k = rot i s ! ((j + k) mod length s)" using nth_rot[of j "rot i s" k] j k by simp
  also have "\<dots> = s ! ((i + (j + k) mod length s) mod length s)" using nth_rot[OF _ m, of i] i by simp
  also have "(i + (j + k) mod length s) mod length s = ((i + j) mod length s + k) mod length s"
    by (simp add: mod_add_right_eq mod_add_left_eq add.assoc)
  also have "s ! \<dots> = rot ((i + j) mod length s) s ! k"
    using nth_rot[of "(i + j) mod length s" s k] L0 k by simp
  finally show "rot j (rot i s) ! k = rot ((i + j) mod length s) s ! k" .
qed

lemma rot_to_arc:
  assumes d: "distinct s" and a: "a \<in> set s" and b: "b \<in> set s" and ab: "a \<noteq> b"
  shows "\<exists>i p1 p2. i < length s \<and> arc s a b = a # p1 \<and> arc s b a = b # p2 \<and> rot i s = a # p1 @ b # p2"
proof -
  define L where "L = length s"
  define i where "i = lindex s a"
  define t where "t = rot i s"
  have i: "i < L" using a by (simp add: i_def L_def lindex_less)
  have L0: "0 < L" using i by linarith
  have dt: "distinct t" using d by (simp add: t_def)
  have lt: "length t = L" by (simp add: t_def L_def)
  have t0: "t ! 0 = a"
    using nth_rot[of i s 0] i L0 a by (simp add: t_def L_def i_def nth_lindex)
  have bt: "b \<in> set t" using b by (simp add: t_def)
  define j where "j = lindex t b"
  have j: "j < L" using lindex_less[OF bt] lt by (simp add: j_def)
  have tj: "t ! j = b" using bt by (simp add: j_def nth_lindex)
  have j0: "j \<noteq> 0"
  proof
    assume "j = 0"
    then show False using tj t0 ab by simp
  qed
  define p1 where "p1 = tl (take j t)"
  define p2 where "p2 = drop (Suc j) t"
  have tk: "take j t = a # p1"
  proof -
    have tne: "t \<noteq> []"
    proof
      assume "t = []"
      then show False using lt L0 by simp
    qed
    have ne: "take j t \<noteq> []" using j0 tne by simp
    have h: "hd (take j t) = a" using j0 t0 tne by (simp add: hd_conv_nth)
    have "take j t = hd (take j t) # tl (take j t)" by (rule hd_Cons_tl[symmetric, OF ne])
    then show ?thesis using h by (simp only: p1_def)
  qed
  have jt: "j < length t" using j lt by simp
  have dj: "drop j t = b # p2" using Cons_nth_drop_Suc[OF jt] tj by (simp add: p2_def)
  have rt: "t = a # p1 @ b # p2" using tk dj append_take_drop_id[of j t] by simp
  have arc1: "arc s a b = a # p1" using tk by (simp add: arc_def t_def i_def j_def)
  have "t ! j = s ! ((i + j) mod L)" using nth_rot[of i s j] i j by (simp add: t_def L_def)
  then have lb: "lindex s b = (i + j) mod L"
    using tj lindex_nth_distinct[OF d, of "(i + j) mod L"] L0 by (simp add: L_def)
  have u: "rot (lindex s b) s = b # p2 @ a # p1"
  proof -
    have "rot (lindex s b) s = rot j t" using rot_rot[of i s j] i j lb by (simp add: t_def L_def)
    also have "\<dots> = drop j t @ take j t" using j lt by (simp add: rot_def)
    finally show ?thesis using tk dj by simp
  qed
  have "a \<notin> set (b # p2)" using dt rt ab by auto
  then have "lindex (b # p2 @ a # p1) a = length (b # p2)"
    by (induction p2 arbitrary: b) (auto simp: lindex_append)
  then have arc2: "arc s b a = b # p2" using u by (simp add: arc_def)
  show ?thesis using arc1 arc2 rt i by (auto simp: t_def L_def)
qed

lemma next_in_rot:
  assumes d: "distinct s" and x: "x \<in> set s"
  shows "next_in (rot i s) x = next_in s x"
proof -
  have c: "cycle (frel (next_in s)) s" by (rule cycle_from_next[OF d]) simp
  then have cr: "cycle (frel (next_in s)) (rot i s)" by (simp add: cycle_rot)
  have "x \<in> set (rot i s)" using x by simp
  then have "next_in s x = next_in (rot i s) x" by (rule cycle_next_in[OF cr])
  then show ?thesis by simp
qed

definition chord_ring :: "'a hypermap \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "chord_ring G r x = x # arc r (fproj G r (edge G x)) (fproj G r x)"

lemma (in snip_ring) diskF_D: "diskF \<subseteq> D" using diskN_D by (auto simp: diskF_def)
lemma (in snip_ring) diskFC_D: "diskFC \<subseteq> D" by (auto simp: diskFC_def)

lemma (in snip_ring) diskFC_face: "x \<in> diskFC \<Longrightarrow> f x \<in> diskFC"
proof -
  assume x: "x \<in> diskFC"
  have xD: "x \<in> D" and xN: "x \<notin> diskN" and nb: "\<not> fband G r x" using x by (auto simp: diskFC_def)
  have fxD: "f x \<in> D" using xD by simp
  have "f x \<notin> diskN"
  proof
    assume fN: "f x \<in> diskN"
    then have nfN: "n (f x) \<in> diskN" using diskN_node[OF fxD] by simp
    show False
    proof (cases "n (f x) \<in> set r")
      case True
      have "cface (e (n (f x))) (next_in r (n (f x)))"
        using cycle_next_in_rel[OF cycle_r True] by (simp add: rlink_def)
      then have "cface x (next_in r (n (f x)))" by (simp add: faceK)
      then have "fband G r x" using next_in_mem[OF True] by (auto simp: fband_def)
      then show False using nb by simp
    next
      case False
      then have "n (f x) \<in> diskE" using nfN by (simp add: diskE_def)
      then have "e (n (f x)) \<in> diskE" using diskE_edge[of "n (f x)"] fxD by simp
      then show False using xN by (simp add: faceK diskE_def)
    qed
  qed
  then show ?thesis using fxD nb by (simp add: diskFC_def)
qed

lemma (in snip_ring) closed_cface:
  assumes cl: "\<And>w. w \<in> A \<Longrightarrow> f w \<in> A" and c: "cface y z"
  shows "y \<in> A \<longleftrightarrow> z \<in> A"
proof -
  obtain k where z: "z = (f ^^ k) y" using c by (auto simp: fconnect_def)
  have "y \<in> A \<Longrightarrow> z \<in> A" using F.closed_funpow[OF cl] z by simp
  moreover have "z \<in> A \<Longrightarrow> y \<in> A"
  proof -
    assume zA: "z \<in> A"
    have yz: "cface z y" by (rule F.fconnect_sym[OF c])
    then obtain k' where "y = (f ^^ k') z" by (auto simp: fconnect_def)
    then show ?thesis using F.closed_funpow[OF cl zA] by simp
  qed
  ultimately show ?thesis by blast
qed

lemma fcard0P: "finite A \<Longrightarrow> 0 < fcard g A \<longleftrightarrow> A \<noteq> {}"
  by (simp add: fcard_def card_gt_0_iff)

lemma (in fperm) fcard1P:
  "A \<subseteq> D \<Longrightarrow> 1 < fcard f A \<longleftrightarrow> (\<exists>x\<in>A. \<exists>y\<in>A. \<not> fconnect f x y)"
proof -
  assume AD: "A \<subseteq> D"
  have fin: "finite (cyc f ` A)" using AD fin by (meson finite_imageI finite_subset)
  have "1 < card (cyc f ` A) \<longleftrightarrow> (\<exists>x\<in>A. \<exists>y\<in>A. cyc f x \<noteq> cyc f y)"
  proof
    assume c: "1 < card (cyc f ` A)"
    have "\<not> (\<forall>X\<in>cyc f ` A. \<forall>Y\<in>cyc f ` A. X = Y)"
      using card_le_Suc0_iff_eq[OF fin] c by simp
    then show "\<exists>x\<in>A. \<exists>y\<in>A. cyc f x \<noteq> cyc f y" by blast
  next
    assume "\<exists>x\<in>A. \<exists>y\<in>A. cyc f x \<noteq> cyc f y"
    then obtain x y where "x \<in> A" "y \<in> A" "cyc f x \<noteq> cyc f y" by blast
    then have sub: "{cyc f x, cyc f y} \<subseteq> cyc f ` A" and c2: "card {cyc f x, cyc f y} = 2" by auto
    have "card {cyc f x, cyc f y} \<le> card (cyc f ` A)" by (rule card_mono[OF fin sub])
    then show "1 < card (cyc f ` A)" using c2 by simp
  qed
  then show ?thesis by (simp add: fcard_def cyc_eq_iff)
qed

lemma (in snip_ring) nontrivial0P:
  "nontrivial_ring G 0 r \<longleftrightarrow> diskF \<noteq> {} \<and> diskFC \<noteq> {}"
  using fcard0P[of diskF "face G"] fcard0P[of diskFC "face G"] diskF_D diskFC_D finite_darts
  by (simp add: nontrivial_ring_def finite_subset)

lemma (in snip_ring) nontrivial1P:
  "nontrivial_ring G 1 r \<longleftrightarrow> (\<exists>x\<in>diskF. \<exists>y\<in>diskF. \<not> cface x y) \<and> (\<exists>x\<in>diskFC. \<exists>y\<in>diskFC. \<not> cface x y)"
  using F.fcard1P[OF diskF_D] F.fcard1P[OF diskFC_D] by (simp add: nontrivial_ring_def)


section \<open>The reversed ring\<close>

locale revsnip = snip_ring +
  assumes bridgelessG: "bridgeless G" and plainG: "plain G" and connectedG: "connected G"
begin

lemma ee [simp]: "e (e x) = x" using plainG by (rule plain_eq)

lemma e'id: "x \<in> D \<Longrightarrow> e x \<noteq> x" using plainG by (rule plain_neq)

abbreviation rr :: "'a list" where "rr \<equiv> rev_ring G r"

lemma mem_rev_ring: "x \<in> set rr \<longleftrightarrow> e x \<in> set r"
proof
  assume "x \<in> set rr"
  then obtain y where "y \<in> set r" "x = e y" by (auto simp: rev_ring_def)
  then show "e x \<in> set r" by simp
next
  assume "e x \<in> set r"
  then have "e (e x) \<in> e ` set r" by blast
  then show "x \<in> set rr" by (simp add: rev_ring_def)
qed

lemma rr_D: "set rr \<subseteq> D" using r_D by (auto simp: rev_ring_def)

lemma cface_e_next: "x \<in> set r \<Longrightarrow> cface (e x) (next_in r x)"
  using cycle_next_in_rel[OF cycle_r] by (simp add: rlink_def)

lemma cycle_rev_ring: "cycle (rlink G) rr"
proof -
  have "cycle (\<lambda>a b. cface b (e a)) r"
    using cycle_mono[OF _ cycle_r] F.fconnect_sym by (simp add: rlink_def)
  then have "cycle (\<lambda>a b. rlink G (e b) (e a)) r" by (simp add: rlink_def)
  then show ?thesis by (simp add: rev_ring_def cycle_rev cycle_map)
qed

lemma next_inj: "x \<in> set r \<Longrightarrow> y \<in> set r \<Longrightarrow> next_in r x = next_in r y \<Longrightarrow> x = y"
  by (metis prev_next_in distinct_r)

lemma simple_rev_ring: "simple G rr"
proof -
  have inj: "inj_on (cyc f \<circ> e) (set r)"
  proof (rule inj_onI)
    fix x y assume x: "x \<in> set r" and y: "y \<in> set r" and eq: "(cyc f \<circ> e) x = (cyc f \<circ> e) y"
    have "cyc f (e x) = cyc f (e y)" using eq by simp
    then have "cface (e x) (e y)" by (simp only: F.cyc_eq_iff)
    then have "cface (next_in r x) (next_in r y)"
      using fconnect_trans[OF fconnect_trans[OF F.fconnect_sym[OF cface_e_next[OF x]]]
            cface_e_next[OF y]] by blast
    then have "next_in r x = next_in r y" by (rule r_cface[OF next_in_mem[OF x] next_in_mem[OF y]])
    then show "x = y" by (rule next_inj[OF x y])
  qed
  have "distinct (map (cyc f \<circ> e) r)" using distinct_r inj by (simp add: distinct_map)
  moreover have "map (cyc f) (rev (map e r)) = rev (map (cyc f \<circ> e) r)" by (simp add: rev_map)
  ultimately show ?thesis unfolding simple_def rev_ring_def by (simp only: distinct_rev)
qed

lemma scycle_rev_ring: "scycle G (rlink G) rr"
  using cycle_rev_ring simple_rev_ring by (simp add: scycle_def)

lemma fband_rev_ring: "fband G rr x \<longleftrightarrow> fband G r x"
proof
  assume "fband G rr x"
  then obtain y where y: "y \<in> set rr" "cface x y" by (auto simp: fband_def)
  have ey: "e y \<in> set r" using y(1) mem_rev_ring by blast
  have "cface y (next_in r (e y))" using cface_e_next[OF ey] by simp
  then show "fband G r x" using fconnect_trans[OF y(2)] next_in_mem[OF ey] by (auto simp: fband_def)
next
  assume "fband G r x"
  then obtain y where y: "y \<in> set r" "cface x y" by (auto simp: fband_def)
  have py: "prev_in r y \<in> set r" by (rule prev_in_mem[OF y(1)])
  have "cface (e (prev_in r y)) y" using cface_e_next[OF py] next_prev_in[OF distinct_r y(1)] by simp
  moreover have "e (prev_in r y) \<in> set rr" using py mem_rev_ring by simp
  ultimately show "fband G rr x" using fconnect_trans[OF y(2) F.fconnect_sym] by (auto simp: fband_def)
qed

sublocale R: snip_ring G rr
  using planarG scycle_rev_ring rr_D by unfold_locales auto

lemma diskE_edge': "x \<in> diskE \<Longrightarrow> e x \<in> diskE"
  using diskE_edge diskE_D by blast

lemma diskN_edge_ring:
  assumes pr: "proper_ring G r" and x: "x \<in> set r"
  shows "e x \<notin> diskN"
proof
  assume exN: "e x \<in> diskN"
  have xD: "x \<in> D" using x r_D by blast
  have exr: "e x \<in> set r"
  proof (rule ccontr)
    assume "e x \<notin> set r"
    then have "e x \<in> diskE" using exN by (simp add: diskE_def)
    then have "x \<in> diskE" using diskE_edge'[of "e x"] by simp
    then show False using x by (simp add: diskE_def)
  qed
  have n1: "e x = next_in r x"
    using r_cface[OF exr next_in_mem[OF x]] cface_e_next[OF x] by blast
  have n2: "x = next_in r (e x)"
    using r_cface[OF x next_in_mem[OF exr]] cface_e_next[OF exr] by simp
  have nn: "next_in r (next_in r x) = x" using n1 n2 by simp
  have L: "length r \<le> 2" by (rule next_next_in_size[OF distinct_r x nn])
  show False
  proof (cases r rule: remdups_adj.cases)
    case 1
    then show False using x by simp
  next
    case (2 a)
    then have "next_in r x = x" using x by (simp add: next_in_def)
    then show False using n1 e'id xD by simp
  next
    case (3 a b rest)
    then have rest: "rest = []" and r2: "r = [a, b]" using L by auto
    have ab: "a \<noteq> b" using distinct_r r2 by simp
    have "e a \<noteq> b" using pr r2 by simp
    moreover have "x = a \<or> x = b" using x r2 by simp
    moreover have "next_in r a = b" "next_in r b = a" using r2 ab by (simp_all add: next_in_def)
    ultimately show False using n1 r2 by (metis ee)
  qed
qed

lemma diskN_rev_ring:
  assumes pr: "proper_ring G r" and xD: "x \<in> D"
  shows "x \<in> R.diskN \<longleftrightarrow> x \<notin> diskN"
proof -
  obtain y0 where y0: "y0 \<in> set r" using pr by (cases r) auto
  have ty: "e y0 \<in> D" using y0 r_D by auto
  obtain p where p: "path (clink G) x p" "lastd x p = e y0"
    using connected_clink[OF connectedG xD ty] by blast
  show ?thesis using p xD
  proof (induction p arbitrary: x)
    case Nil
    then have "x = e y0" by simp
    then have xr: "x \<in> set rr" using y0 mem_rev_ring by simp
    have "x \<notin> diskN" using diskN_edge_ring[OF pr y0] \<open>x = e y0\<close> by simp
    then show ?case using R.r_diskN[OF xr] by simp
  next
    case (Cons y p)
    have cl: "clink G x y" and py: "path (clink G) y p" and ly: "lastd y p = e y0"
      using Cons.prems by simp_all
    have yD: "y \<in> D" using clink_closed[OF cl] Cons.prems(3) by simp
    have IH: "y \<in> R.diskN \<longleftrightarrow> y \<notin> diskN" using Cons.IH[OF py ly yD] .
    consider (N) "x = n y" | (F) "f x = y" using cl by (auto simp: clink_def)
    then show ?case
    proof cases
      case N
      then show ?thesis using IH diskN_node[OF yD] R.diskN_node[OF yD] by simp
    next
      case F
      show ?thesis
      proof (cases "e x \<in> set r")
        case True
        then have "x \<in> set rr" using mem_rev_ring by simp
        moreover have "x \<notin> diskN" using diskN_edge_ring[OF pr True] by simp
        ultimately show ?thesis using R.r_diskN by blast
      next
        case exr: False
        have exD: "e x \<in> D" using Cons.prems(3) by simp
        have exy: "e x = n y" using F edgeK[of "e x"] by simp
        have xrr: "x \<notin> set rr" using exr mem_rev_ring by simp
        have exrr: "e x \<notin> set rr \<longleftrightarrow> x \<notin> set r" using mem_rev_ring by simp
        have A: "x \<in> R.diskN \<longleftrightarrow> x \<notin> set r \<and> e x \<in> R.diskN"
        proof -
          have "x \<in> R.diskN \<longleftrightarrow> x \<in> R.diskE" using R.diskN_E xrr by blast
          also have "\<dots> \<longleftrightarrow> e x \<in> R.diskE" using R.diskE_edge[OF Cons.prems(3)] by simp
          also have "\<dots> \<longleftrightarrow> e x \<in> R.diskN \<and> x \<notin> set r" using exrr by (simp add: R.diskE_def)
          finally show ?thesis by blast
        qed
        have B: "x \<in> diskN \<longleftrightarrow> x \<in> set r \<or> e x \<in> diskN"
        proof -
          have "x \<in> diskN \<longleftrightarrow> x \<in> set r \<or> x \<in> diskE" by (rule diskN_E)
          also have "x \<in> diskE \<longleftrightarrow> e x \<in> diskE" using diskE_edge[OF Cons.prems(3)] by simp
          also have "e x \<in> diskE \<longleftrightarrow> e x \<in> diskN" using exr by (simp add: diskE_def)
          finally show ?thesis .
        qed
        have C1: "e x \<in> diskN \<longleftrightarrow> y \<in> diskN" using exy diskN_node[OF yD] by simp
        have C2: "e x \<in> R.diskN \<longleftrightarrow> y \<in> R.diskN" using exy R.diskN_node[OF yD] by simp
        show ?thesis using A B C1 C2 IH by blast
      qed
    qed
  qed
qed

lemma diskF_rev_ring:
  "proper_ring G r \<Longrightarrow> x \<in> R.diskF \<longleftrightarrow> x \<in> D \<and> x \<notin> diskN \<and> \<not> fband G r x"
  using diskN_rev_ring R.diskN_D fband_rev_ring by (auto simp: R.diskF_def)

lemma simple_rot: "simple G (rot i p) \<longleftrightarrow> simple G p"
proof (cases "i \<le> length p")
  case True
  then show ?thesis using simple_rotate rot_rotate by metis
next
  case False
  then show ?thesis by (simp add: rot_oversize)
qed

lemma diskN_all:
  assumes h: "\<And>w w'. w \<in> D \<Longrightarrow> f w = w' \<Longrightarrow> w' \<in> diskN \<Longrightarrow> w \<in> diskN"
    and x0: "x0 \<in> diskN"
  shows "D \<subseteq> diskN"
proof
  fix y assume yD: "y \<in> D"
  have x0D: "x0 \<in> D" using x0 diskN_D by blast
  obtain p where p: "path (clink G) y p" "lastd y p = x0"
    using connected_clink[OF connectedG yD x0D] by blast
  show "y \<in> diskN" using p yD
  proof (induction p arbitrary: y)
    case Nil
    then show ?case using x0 by simp
  next
    case (Cons y' p)
    have cl: "clink G y y'" and py: "path (clink G) y' p" and ly: "lastd y' p = x0"
      using Cons.prems by simp_all
    have y'D: "y' \<in> D" using clink_closed[OF cl] Cons.prems(3) by simp
    have IH: "y' \<in> diskN" using Cons.IH[OF py ly y'D] .
    consider (N) "y = n y'" | (F) "f y = y'" using cl by (auto simp: clink_def)
    then show ?case
    proof cases
      case N
      then show ?thesis using IH diskN_node[OF y'D] by simp
    next
      case F
      show ?thesis by (rule h[OF Cons.prems(3) F IH])
    qed
  qed
qed

lemma nontrivial_ring_proper:
  assumes nt: "nontrivial_ring G m r"
  shows "proper_ring G r"
proof (cases r rule: remdups_adj.cases)
  case 1
  have "diskF = {}" unfolding diskF_def diskN_def using 1 by simp
  then show ?thesis using nt by (simp add: nontrivial_ring_def fcard_def)
next
  case (2 x)
  have "rlink G x x" using cycle_r 2 by (simp add: cycle_Cons)
  then have "cface (e x) x" by (simp add: rlink_def)
  moreover have xD: "x \<in> D" using r_D 2 by simp
  ultimately show ?thesis using bridgeless_cface[OF bridgelessG xD] F.fconnect_sym by blast
next
  case (3 x y rest)
  show ?thesis
  proof (cases rest)
    case (Cons z rest')
    then show ?thesis using 3 by simp
  next
    case Nil
    then have r2: "r = [x, y]" using 3 by simp
    show ?thesis
    proof (rule ccontr)
      assume "\<not> proper_ring G r"
      then have exy: "e x = y" using r2 by simp
      have rset: "w \<in> set r \<longleftrightarrow> e w \<in> set r" for w using r2 exy by auto
      have "D \<subseteq> diskN"
      proof (rule diskN_all)
        show "x \<in> diskN" using r_diskN r2 by simp
        fix w w' assume wD: "w \<in> D" and fw: "f w = w'" and w'N: "w' \<in> diskN"
        have w'D: "w' \<in> D" using wD fw by auto
        have "e w = n w'" using fw edgeK[of "e w"] by simp
        then have ewN: "e w \<in> diskN" using diskN_node[OF w'D] w'N by simp
        show "w \<in> diskN"
        proof (cases "e w \<in> set r")
          case True
          then show ?thesis using rset r_diskN by blast
        next
          case False
          then have "e w \<in> diskE" using ewN by (simp add: diskE_def)
          then have "w \<in> diskE" using diskE_edge[of "e w"] wD by simp
          then show ?thesis by (simp add: diskE_def)
        qed
      qed
      then have "diskFC = {}" by (auto simp: diskFC_def)
      then show False using nt by (simp add: nontrivial_ring_def fcard_def)
    qed
  qed
qed

lemma nontrivial_rev_ring:
  assumes nt: "nontrivial_ring G m r"
  shows "nontrivial_ring G m rr"
proof -
  have pr: "proper_ring G r" by (rule nontrivial_ring_proper[OF nt])
  have F1: "R.diskF = diskFC"
    using diskF_rev_ring[OF pr] by (auto simp: diskFC_def)
  have F2: "R.diskFC = diskF"
  proof -
    have "x \<in> R.diskFC \<longleftrightarrow> x \<in> diskF" for x
    proof (cases "x \<in> D")
      case True
      then show ?thesis using diskN_rev_ring[OF pr True] fband_rev_ring
        by (auto simp: R.diskFC_def diskF_def)
    next
      case False
      then show ?thesis using diskF_D by (auto simp: R.diskFC_def)
    qed
    then show ?thesis by auto
  qed
  show ?thesis using nt F1 F2 by (auto simp: nontrivial_ring_def)
qed

lemma fband_D: "fband G r y \<Longrightarrow> y \<in> D"
proof -
  assume "fband G r y"
  then obtain z where "z \<in> set r" "cface y z" by (auto simp: fband_def)
  then show ?thesis using F.fconnect_in_D r_D by blast
qed

lemma chord_neq:
  assumes rFy: "fband G r y" and rFey: "fband G r (e y)"
  shows "fproj G r (e y) \<noteq> fproj G r y"
proof
  assume eq: "fproj G r (e y) = fproj G r y"
  have yD: "y \<in> D" by (rule fband_D[OF rFy])
  have "cface y (fproj G r y)" and "cface (e y) (fproj G r (e y))" using fprojP rFy rFey by auto
  then have "cface y (e y)" using eq fconnect_trans F.fconnect_sym by metis
  then show False using bridgeless_cface[OF bridgelessG yD] by simp
qed

lemma scycle_chord_ring:
  assumes rFy: "fband G r y" and rFey: "fband G r (e y)"
  shows "scycle G (rlink G) (chord_ring G r y) \<and> set (chord_ring G r y) \<subseteq> D"
proof -
  define y1 where "y1 = fproj G r y"
  define y2 where "y2 = fproj G r (e y)"
  have y1: "y1 \<in> set r" "cface y y1" using fprojP[OF rFy] by (auto simp: y1_def)
  have y2: "y2 \<in> set r" "cface (e y) y2" using fprojP[OF rFey] by (auto simp: y2_def)
  have ne: "y2 \<noteq> y1" using chord_neq[OF rFy rFey] by (simp add: y1_def y2_def)
  obtain i p1 p2 where i: "i < length r" and a1: "arc r y1 y2 = y1 # p1" and a2: "arc r y2 y1 = y2 # p2"
    and rt: "rot i r = y1 # p1 @ y2 # p2"
    using rot_to_arc[OF distinct_r y1(1) y2(1) ne[symmetric]] by blast
  have cr: "chord_ring G r y = y # y2 # p2" using a2 by (simp add: chord_ring_def y1_def y2_def)
  have cyc: "cycle (rlink G) (y1 # p1 @ y2 # p2)" using cycle_r rt cycle_rot[of "rlink G" i r] by simp
  then have p2: "path (rlink G) y2 p2" and l2: "rlink G (lastd y2 p2) y1"
    by (simp_all add: cycle_Cons)
  have "cface (e (lastd y2 p2)) y" using l2 y1(2) fconnect_trans F.fconnect_sym
    by (metis rlink_def)
  then have l: "rlink G (lastd y2 p2) y" by (simp add: rlink_def)
  have c: "cycle (rlink G) (y # y2 # p2)" using p2 l y2(2) by (simp add: cycle_Cons rlink_def)
  have sr: "simple G (y1 # p1 @ y2 # p2)" using simple_r rt simple_rot[of i r] by simp
  then have s2: "simple G (y2 # p2)" and nb: "\<forall>w\<in>set (y2 # p2). \<not> fband G (y1 # p1) w"
    using simple_append[of "y1 # p1" "y2 # p2"] by auto
  have "\<not> fband G (y2 # p2) y"
  proof
    assume "fband G (y2 # p2) y"
    then obtain w where w: "w \<in> set (y2 # p2)" "cface y w" by (auto simp: fband_def)
    have "cface w y1" using fconnect_trans[OF F.fconnect_sym[OF w(2)] y1(2)] .
    then have "fband G (y1 # p1) w" by (auto simp: fband_def)
    then show False using nb w(1) by blast
  qed
  then have "simple G (y # y2 # p2)" using s2 simple_Cons by blast
  moreover have "set (y # y2 # p2) \<subseteq> D"
  proof -
    have "set (y2 # p2) \<subseteq> set (rot i r)" using rt by auto
    then show ?thesis using r_D fband_D[OF rFy] by auto
  qed
  ultimately show ?thesis using c cr by (simp add: scycle_def)
qed

end

lemma rotr1_prev:
  assumes d: "distinct l"
  shows "map (prev_in l) l = rotr1 l"
proof (cases "l = []")
  case True
  then show ?thesis by (simp add: rotr1_def rot_def)
next
  case False
  define L where "L = length l"
  have L0: "0 < L" using False by (simp add: L_def)
  show ?thesis
  proof (rule nth_equalityI)
    show "length (map (prev_in l) l) = length (rotr1 l)" by (simp add: rotr1_def)
    fix i assume "i < length (map (prev_in l) l)"
    then have i: "i < L" by (simp add: L_def)
    have li: "lindex l (l ! i) = i" using lindex_nth_distinct[OF d] i by (simp add: L_def)
    have lhs: "map (prev_in l) l ! i = l ! ((i + L - 1) mod L)"
      using i li by (simp add: prev_in_def L_def)
    have rhs: "rotr1 l ! i = (if i = 0 then l ! (L - 1) else l ! (i - 1))"
    proof -
      have r: "rotr1 l = drop (L - 1) l @ take (L - 1) l" by (simp add: rotr1_def rot_def L_def)
      have ld: "length (drop (L - 1) l) = 1"
      proof -
        have "length (drop (L - 1) l) = L - (L - 1)" by (simp add: L_def)
        also have "\<dots> = 1" using L0 by linarith
        finally show ?thesis .
      qed
      show ?thesis
      proof (cases "i = 0")
        case True
        then show ?thesis using r ld L0 by (simp add: nth_append L_def)
      next
        case False
        then show ?thesis using r ld i by (simp add: nth_append L_def)
      qed
    qed
    have "(i + L - 1) mod L = (if i = 0 then L - 1 else i - 1)"
    proof (cases "i = 0")
      case True
      then show ?thesis using L0 by simp
    next
      case False
      then have "i + L - 1 = (i - 1) + L" by simp
      then have "(i + L - 1) mod L = (i - 1) mod L" by simp
      then show ?thesis using False i by simp
    qed
    then show "map (prev_in l) l ! i = rotr1 l ! i" using lhs rhs by simp
  qed
qed

locale revsnip_proper = revsnip +
  assumes proper: "proper_ring G r"
begin

lemma rr_notN: "x \<in> set rr \<Longrightarrow> x \<notin> diskN"
  using diskN_edge_ring[OF proper, of "e x"] mem_rev_ring by simp

lemma grr_darts: "darts R.snipr = diskN \<union> set rr"
proof -
  have "x \<in> D - R.diskE \<longleftrightarrow> x \<in> diskN \<union> set rr" for x
  proof
    assume x: "x \<in> D - R.diskE"
    then have xD: "x \<in> D" by simp
    show "x \<in> diskN \<union> set rr"
      using x diskN_rev_ring[OF proper xD] by (auto simp: R.diskE_def)
  next
    assume x: "x \<in> diskN \<union> set rr"
    then have xD: "x \<in> D" using diskN_D rr_D by blast
    show "x \<in> D - R.diskE"
      using x xD diskN_rev_ring[OF proper xD] by (auto simp: R.diskE_def)
  qed
  then show ?thesis by auto
qed

sublocale Sd: hypermap snipd by (rule hypermap_snipd)
sublocale Rr: hypermap R.snipr by (rule R.hypermap_snipr)
sublocale P: patch G snipd snipr id id r "rev r" by (rule snip_patch)
sublocale RP: patch G R.snipd R.snipr id id rr "rev rr" by (rule R.snip_patch)

lemma cface_snipd:
  assumes u: "u \<in> diskN" and v: "v \<in> diskN" and uv: "cface u v"
  shows "fconnect snipd_face u v"
proof (cases "u \<in> P.outer")
  case False
  then show ?thesis using P.patch_face_d[of u v] u v uv by simp
next
  case True
  have vo: "v \<in> P.outer" using P.outer_cface[OF uv] True by simp
  obtain u1 where u1: "u1 \<in> set r" "fconnect snipd_face u u1"
    using P.outer_hd[of u] True u by (auto simp: fband_def)
  obtain v1 where v1: "v1 \<in> set r" "fconnect snipd_face v v1"
    using P.outer_hd[of v] vo v by (auto simp: fband_def)
  have cu: "cface u u1" using P.patch_face_d'[of u u1] u u1 by simp
  have cv: "cface v v1" using P.patch_face_d'[of v v1] v v1 by simp
  have "cface u1 v1" using fconnect_trans[OF fconnect_trans[OF F.fconnect_sym[OF cu] uv] cv] .
  then have "u1 = v1" using r_cface u1(1) v1(1) by blast
  have "fconnect snipd_face v1 v" using Sd.F.fconnect_sym[of v v1] v1(2) by simp
  then show ?thesis using fconnect_trans[OF u1(2)] \<open>u1 = v1\<close> by simp
qed

lemma rotr1_rr: "rotr1 (map e r) = map (e \<circ> prev_in r) r"
proof -
  have "map (prev_in r) r = rotr1 r" by (rule rotr1_prev[OF distinct_r])
  then have "map e (map (prev_in r) r) = map e (rotr1 r)" by simp
  also have "map e (rotr1 r) = rotr1 (map e r)" by (simp add: rotr1_def map_rot)
  finally show ?thesis by simp
qed

lemma prev_rr: "x \<in> set r \<Longrightarrow> e (prev_in r x) \<in> set rr \<and> cface (e (prev_in r x)) x"
  using mem_rev_ring prev_in_mem[of x r] cface_e_next[of "prev_in r x"] next_prev_in[OF distinct_r]
  by simp

lemma rev_ring_cotrace:
  "ring_trace snipd r et \<longleftrightarrow> ring_trace R.snipr (rotr1 (map e r)) et"
proof
  assume "ring_trace snipd r et"
  then obtain kd where kd: "coloring snipd kd" and et: "et = trace (map kd r)"
    by (auto simp: ring_trace_def)
  have kdE: "\<And>u. u \<in> diskN \<Longrightarrow> kd (snipd_edge u) \<noteq> kd u" using kd by (simp add: coloring_def)
  define proj where "proj u = (if u \<in> diskN then u else next_in r (e u))" for u
  define kr where "kr u = kd (proj u)" for u
  have proj: "proj u \<in> diskN \<and> cface u (proj u)" if u: "u \<in> darts R.snipr" for u
  proof (cases "u \<in> diskN")
    case True
    then show ?thesis by (simp add: proj_def)
  next
    case False
    then have ur: "u \<in> set rr" using u grr_darts by auto
    then have eur: "e u \<in> set r" using mem_rev_ring by simp
    have "cface u (next_in r (e u))" using cface_e_next[OF eur] by simp
    then show ?thesis using False r_diskN next_in_mem[OF eur] by (simp add: proj_def)
  qed
  have krF: "kr (face R.snipr u) = kr u" if u: "u \<in> darts R.snipr" for u
  proof -
    have fu: "face R.snipr u \<in> darts R.snipr" using Rr.F.closed[of u] u by blast
    have "Rr.cface u (face R.snipr u)" by (rule fconnect_step)
    then have c: "cface u (face R.snipr u)" using RP.patch_face_r[OF u fu] by simp
    have p1: "cface u (proj u)" and p2: "cface (face R.snipr u) (proj (face R.snipr u))"
      using proj[OF u] proj[OF fu] by auto
    have "cface (proj u) (proj (face R.snipr u))"
      using fconnect_trans[OF fconnect_trans[OF F.fconnect_sym[OF p1] c] p2] .
    then have "fconnect snipd_face (proj u) (proj (face R.snipr u))"
      using cface_snipd proj[OF u] proj[OF fu] by blast
    then have "kd (proj (face R.snipr u)) = kd (proj u)"
      using Sd.coloring_cface[OF kd] proj[OF u] by simp
    then show ?thesis by (simp add: kr_def)
  qed
  have krE: "kr (e u) \<noteq> kr u" if u: "u \<in> darts R.snipr" for u
  proof (cases "u \<in> diskN")
    case uN: True
    show ?thesis
    proof (cases "u \<in> set r")
      case True
      have eu: "e u \<notin> diskN" by (rule diskN_edge_ring[OF proper True])
      have "kr (e u) = kd (next_in r u)" using eu by (simp add: kr_def proj_def)
      moreover have "snipd_edge u = next_in r u" using uN True by (simp add: snipd_edge_def)
      ultimately show ?thesis using kdE[OF uN] uN by (simp add: kr_def proj_def)
    next
      case False
      have uD: "u \<in> D" using uN diskN_D by blast
      have "u \<in> diskE" using uN False by (simp add: diskE_def)
      then have "e u \<in> diskE" using diskE_edge[OF uD] by simp
      then have euN: "e u \<in> diskN" by (simp add: diskE_def)
      have "snipd_edge u = e u" using uN False by (simp add: snipd_edge_def)
      then show ?thesis using kdE[OF uN] uN euN by (simp add: kr_def proj_def)
    qed
  next
    case False
    then have ur: "u \<in> set rr" using u grr_darts by auto
    then have eur: "e u \<in> set r" using mem_rev_ring by simp
    have euN: "e u \<in> diskN" using r_diskN[OF eur] .
    have "snipd_edge (e u) = next_in r (e u)" using euN eur by (simp add: snipd_edge_def)
    then have "kd (next_in r (e u)) \<noteq> kd (e u)" using kdE[OF euN] by simp
    then show ?thesis using False euN by (simp add: kr_def proj_def)
  qed
  have "coloring R.snipr kr"
    using krE krF by (simp add: coloring_def R.snipr_edge_def)
  moreover have "map kr (rotr1 (map e r)) = map kd r"
  proof -
    have "kr (e (prev_in r x)) = kd x" if x: "x \<in> set r" for x
    proof -
      have "e (prev_in r x) \<notin> diskN" using prev_rr[OF x] rr_notN by blast
      then show ?thesis using next_prev_in[OF distinct_r x] by (simp add: kr_def proj_def)
    qed
    then show ?thesis unfolding rotr1_rr by simp
  qed
  ultimately show "ring_trace R.snipr (rotr1 (map e r)) et" using et by (auto simp: ring_trace_def)
next
  assume "ring_trace R.snipr (rotr1 (map e r)) et"
  then obtain kr where kr: "coloring R.snipr kr" and et: "et = trace (map kr (rotr1 (map e r)))"
    by (auto simp: ring_trace_def)
  have NR: "diskN \<subseteq> darts R.snipr" using grr_darts by simp
  have krE: "\<And>u. u \<in> darts R.snipr \<Longrightarrow> kr (e u) \<noteq> kr u"
    using kr by (simp add: coloring_def R.snipr_edge_def)
  have krC: "kr v = kr u" if "u \<in> darts R.snipr" "v \<in> darts R.snipr" "cface u v" for u v
  proof -
    have "Rr.cface u v" by (rule iffD2[OF RP.patch_face_r[OF that(1,2)]]) (simp only: id_apply that(3))
    then show ?thesis by (rule Rr.coloring_cface[OF kr _ that(1)])
  qed
  have kdF: "kr (snipd_face u) = kr u" if u: "u \<in> diskN" for u
  proof -
    have "cface u (snipd_face u)" by (rule snipd_face_cface[OF u])
    moreover have "snipd_face u \<in> diskN" by (rule snipd_face_cl[OF u])
    ultimately show ?thesis using krC[of u "snipd_face u"] NR u by blast
  qed
  have kdE: "kr (snipd_edge u) \<noteq> kr u" if u: "u \<in> diskN" for u
  proof -
    define y where "y = snipd_face (snipd_edge u)"
    have yN: "y \<in> diskN" using snipd_face_cl snipd_edge_cl u by (simp add: y_def)
    have ky: "kr y = kr (snipd_edge u)" using kdF[OF snipd_edge_cl[OF u]] by (simp add: y_def)
    have "snipd_node y = u" using snipd_cancel3 by (simp add: y_def)
    then have "n y = u" using yN by (simp add: snipd_node_def)
    then have yfe: "y = f (e u)" using node_eq_iff by blast
    have uR: "u \<in> darts R.snipr" using u NR by blast
    have euR: "e u \<in> darts R.snipr" using Rr.E.closed[of u] uR by (simp add: R.snipr_edge_def)
    have "cface (e u) y" using yfe by simp
    then have "kr y = kr (e u)" using krC[OF euR] yN NR by blast
    then show ?thesis using krE[OF uR] ky by simp
  qed
  have "coloring snipd kr" using kdE kdF by (simp add: coloring_def)
  moreover have "map kr (rotr1 (map e r)) = map kr r"
  proof -
    have "kr (e (prev_in r x)) = kr x" if x: "x \<in> set r" for x
    proof -
      have a: "e (prev_in r x) \<in> darts R.snipr" using prev_rr[OF x] grr_darts by auto
      have b: "x \<in> darts R.snipr" using r_diskN[OF x] NR by blast
      have c: "cface (e (prev_in r x)) x" using prev_rr[OF x] by blast
      show ?thesis using krC[OF a b c] by simp
    qed
    then show ?thesis unfolding rotr1_rr by simp
  qed
  ultimately show "ring_trace snipd r et" using et by (auto simp: ring_trace_def)
qed

lemma rev_rr: "rev rr = map e r" by (simp add: rev_ring_def)

lemma ring_disk_closed:
  assumes cubicG: "cubic G"
  shows "Kempe_closed (ring_trace snipd r)"
proof -
  let ?q = "rotr1 (map e r)"
  have eqP: "ring_trace snipd r = ring_trace R.snipr ?q"
    using rev_ring_cotrace by (simp add: fun_eq_iff)
  have plainR: "plain R.snipr" using RP.plain_patch plainG by blast
  have cubR: "cubicb R.snipr (darts R.snipr - set (rev rr))" using RP.cubic_patch cubicG by blast
  have setq: "set ?q = set (rev rr)" using rev_rr by simp
  have "kempe_hyps R.snipr ?q"
    unfolding kempe_hyps_def
  proof (intro conjI)
    show "hypermap R.snipr" by (rule R.hypermap_snipr)
    show "planar R.snipr" by (rule R.planar_snipr)
    show "plain R.snipr" by (rule plainR)
    show "quasicubic R.snipr ?q" using cubR setq by (simp add: quasicubic_def)
    show "cycle (frel (node R.snipr)) ?q" using RP.cycle_r rev_rr by simp
    show "distinct ?q" using RP.distinct_r rev_rr by simp
    show "set ?q \<subseteq> darts R.snipr" using RP.bGr_D setq by simp
  qed
  then have "Kempe_closed (ring_trace R.snipr ?q)" using Kempe_map kempe_hyps_iff by blast
  then show ?thesis using eqP by simp
qed

lemma colorable_from_ring:
  assumes d: "ring_trace snipd r et" and rd: "ring_trace R.snipd rr (rev et)"
  shows "four_colorable G"
proof -
  obtain kr where kr: "coloring R.snipr kr" and et: "et = trace (map kr (rotr1 (map e r)))"
    using d rev_ring_cotrace by (auto simp: ring_trace_def)
  have "trace (map kr (map e r)) = trace (map kr (rot 1 (rotr1 (map e r))))" by (simp only: rot_rotr1)
  also have "\<dots> = rot 1 et" unfolding et by (simp only: map_rot trace_rot1)
  finally have "ring_trace R.snipr (rev rr) (rot 1 (rev (rev et)))"
    using kr rev_rr by (auto simp: ring_trace_def)
  then show ?thesis using RP.colorable_patch rd by blast
qed

end

lemma (in snip_ring) diskN_via_edge:
  "y \<in> D \<Longrightarrow> y \<in> diskN \<longleftrightarrow> y \<in> set r \<or> (e y \<in> diskN \<and> e y \<notin> set r)"
  using diskN_E diskE_edge by (auto simp: diskE_def)

section \<open>Chord rings\<close>

locale chord = revsnip_proper +
  fixes x :: 'a
  assumes dEx: "x \<in> diskE" and rFx: "fband G r x" and rFex: "fband G r (e x)"
begin

abbreviation x1 :: 'a where "x1 \<equiv> fproj G r x"
abbreviation x2 :: 'a where "x2 \<equiv> fproj G r (e x)"
abbreviation cr1 :: "'a list" where "cr1 \<equiv> chord_ring G r x"
abbreviation cr2 :: "'a list" where "cr2 \<equiv> chord_ring G r (e x)"

lemma xD: "x \<in> D" using dEx diskE_D by blast
lemma xr: "x \<notin> set r" using dEx by (simp add: diskE_def)
lemma dEex: "e x \<in> diskE" using dEx diskE_edge xD by simp
lemma exr: "e x \<notin> set r" using dEex by (simp add: diskE_def)
lemma x_ex: "x \<noteq> e x" using e'id xD by metis

lemma rFeex: "fband G r (e (e x))" using rFx by simp

lemma decomp:
  "\<exists>i p1 p2. i < length r \<and> rot i r = x1 # p1 @ x2 # p2 \<and> cr1 = x # x2 # p2 \<and> cr2 = e x # x1 # p1"
proof -
  have y1: "x1 \<in> set r" using fprojP[OF rFx] by auto
  have y2: "x2 \<in> set r" using fprojP[OF rFex] by auto
  have ne: "x1 \<noteq> x2" using chord_neq[OF rFx rFex] by simp
  obtain i p1 p2 where i: "i < length r" and a1: "arc r x1 x2 = x1 # p1" and a2: "arc r x2 x1 = x2 # p2"
    and rt: "rot i r = x1 # p1 @ x2 # p2"
    using rot_to_arc[OF distinct_r y1 y2 ne] by blast
  have "cr1 = x # x2 # p2" using a2 by (simp add: chord_ring_def)
  moreover have "cr2 = e x # x1 # p1" using a1 by (simp add: chord_ring_def)
  ultimately show ?thesis using i rt by blast
qed

lemma sc1: "scycle G (rlink G) cr1 \<and> set cr1 \<subseteq> D" by (rule scycle_chord_ring[OF rFx rFex])
lemma sc2: "scycle G (rlink G) cr2 \<and> set cr2 \<subseteq> D" using scycle_chord_ring[OF rFex rFeex] .

sublocale C1: snip_ring G cr1 using planarG sc1 by unfold_locales auto
sublocale C2: snip_ring G cr2 using planarG sc2 by unfold_locales auto

lemma proper_chord_ring: "proper_ring G cr1"
proof -
  obtain i p1 p2 where rt: "rot i r = x1 # p1 @ x2 # p2" and c1: "cr1 = x # x2 # p2"
    using decomp by blast
  have x2r: "x2 \<in> set r" using fprojP[OF rFex] by auto
  show ?thesis
  proof (cases p2)
    case Nil
    have "e x \<noteq> x2" using x2r exr by auto
    then show ?thesis using c1 Nil by simp
  next
    case (Cons z p2')
    then show ?thesis using c1 by simp
  qed
qed

lemma diskN_chord_inv:
  assumes yD: "y \<in> D"
  shows "\<not> (y \<in> C1.diskN \<and> y \<in> C2.diskN) \<and> (y \<in> diskN \<longleftrightarrow> y \<in> C1.diskN \<or> y \<in> C2.diskN)"
proof -
  obtain i p1 p2 where rt: "rot i r = x1 # p1 @ x2 # p2" and c1: "cr1 = x # x2 # p2"
    and c2: "cr2 = e x # x1 # p1"
    using decomp by blast
  define r1 where "r1 = x1 # p1"
  define r2 where "r2 = x2 # p2"
  have "set r = set (rot i r)" by simp
  also have "\<dots> = set r1 \<union> set r2" using rt by (auto simp: r1_def r2_def)
  finally have setr: "set r = set r1 \<union> set r2" .
  have disj: "set r1 \<inter> set r2 = {}" using distinct_r rt distinct_rot[of i r] by (simp add: r1_def r2_def)
  have sc1': "set cr1 = insert x (set r2)" using c1 by (simp add: r2_def)
  have sc2': "set cr2 = insert (e x) (set r1)" using c2 by (simp add: r1_def)
  define Inv where "Inv w \<longleftrightarrow> \<not> (w \<in> C1.diskN \<and> w \<in> C2.diskN) \<and>
                               (w \<in> diskN \<longleftrightarrow> w \<in> C1.diskN \<or> w \<in> C2.diskN)" for w
  have base: "Inv x"
  proof -
    have "x \<in> diskN" using dEx by (simp add: diskE_def)
    moreover have "x \<in> C1.diskN" using C1.r_diskN sc1' by simp
    moreover have "x \<notin> C2.diskN"
    proof -
      have "x \<notin> set cr2" using sc2' x_ex xr setr by auto
      moreover have "e x \<in> set cr2" using sc2' by simp
      ultimately show ?thesis using C2.diskN_via_edge[OF xD] by simp
    qed
    ultimately show ?thesis by (simp add: Inv_def)
  qed
  have step: "Inv w" if wD: "w \<in> D" and fw: "f w = w'" and IH: "Inv w'" for w w'
  proof -
    have w'D: "w' \<in> D" using wD fw by auto
    define u where "u = e w"
    have uD: "u \<in> D" using wD by (simp add: u_def)
    have un: "u = n w'" using fw edgeK[of "e w"] by (simp add: u_def)
    have Iu: "Inv u"
      using IH un diskN_node[OF w'D] C1.diskN_node[OF w'D] C2.diskN_node[OF w'D] by (simp add: Inv_def)
    have eu: "e u = w" by (simp add: u_def)
    have EN: "w \<in> diskN \<longleftrightarrow> w \<in> set r \<or> (u \<in> diskN \<and> u \<notin> set r)"
      using diskN_via_edge[OF wD] by (simp add: u_def)
    have E1: "w \<in> C1.diskN \<longleftrightarrow> w \<in> set cr1 \<or> (u \<in> C1.diskN \<and> u \<notin> set cr1)"
      using C1.diskN_via_edge[OF wD] by (simp add: u_def)
    have E2: "w \<in> C2.diskN \<longleftrightarrow> w \<in> set cr2 \<or> (u \<in> C2.diskN \<and> u \<notin> set cr2)"
      using C2.diskN_via_edge[OF wD] by (simp add: u_def)
    consider (ex) "w = e x" | (x) "w = x" | (r) "w \<in> set r" | (o) "w \<notin> set r" "w \<noteq> x" "w \<noteq> e x"
      by blast
    then show ?thesis
    proof cases
      case ex
      then have ux: "u = x" by (simp add: u_def)
      have "w \<in> set cr2" using ex sc2' by simp
      moreover have "w \<notin> set cr1" using ex sc1' x_ex exr setr by auto
      moreover have "x \<in> set cr1" using sc1' by simp
      moreover have "x \<in> diskN" "x \<notin> set r" using dEx xr by (auto simp: diskE_def)
      ultimately show ?thesis using EN E1 E2 ux C2.r_diskN by (auto simp: Inv_def)
    next
      case x
      then show ?thesis using base by simp
    next
      case r
      have wN: "w \<in> diskN" using r_diskN[OF r] .
      have uN: "u \<notin> diskN" using diskN_edge_ring[OF proper r] by (simp add: u_def)
      have u12: "u \<notin> C1.diskN" "u \<notin> C2.diskN" using Iu uN by (auto simp: Inv_def)
      have wx: "w \<noteq> x" "w \<noteq> e x" using r xr exr by auto
      show ?thesis
      proof (cases "w \<in> set r2")
        case True
        then have "w \<in> set cr1" "w \<notin> set cr2" using sc1' sc2' disj wx by auto
        then show ?thesis using wN E1 E2 u12 C1.r_diskN by (auto simp: Inv_def)
      next
        case False
        then have "w \<in> set r1" using r setr by auto
        then have "w \<in> set cr2" "w \<notin> set cr1" using sc1' sc2' disj wx by auto
        then show ?thesis using wN E1 E2 u12 C2.r_diskN by (auto simp: Inv_def)
      qed
    next
      case o
      have nw1: "w \<notin> set cr1" and nw2: "w \<notin> set cr2" using o sc1' sc2' setr by auto
      consider (u1) "u \<in> set r1" | (u2) "u \<in> set r2" | (un) "u \<notin> set r" using setr by blast
      then show ?thesis
      proof cases
        case u1
        have "u \<in> set r" "u \<in> set cr2" using u1 setr sc2' by auto
        moreover have "u \<notin> set cr1" using u1 disj sc1' xr setr by auto
        moreover have "u \<in> C2.diskN" using C2.r_diskN \<open>u \<in> set cr2\<close> by blast
        ultimately show ?thesis using EN E1 E2 o nw1 nw2 Iu by (auto simp: Inv_def)
      next
        case u2
        have "u \<in> set r" "u \<in> set cr1" using u2 setr sc1' by auto
        moreover have "u \<notin> set cr2" using u2 disj sc2' exr setr by auto
        moreover have "u \<in> C1.diskN" using C1.r_diskN \<open>u \<in> set cr1\<close> by blast
        ultimately show ?thesis using EN E1 E2 o nw1 nw2 Iu by (auto simp: Inv_def)
      next
        case un
        have "u \<noteq> x" using o(3) by (auto simp: u_def)
        moreover have "u \<noteq> e x" using o(2) by (auto simp: u_def)
        ultimately have "u \<notin> set cr1" "u \<notin> set cr2" using un sc1' sc2' setr by auto
        then show ?thesis using EN E1 E2 o nw1 nw2 Iu un by (auto simp: Inv_def)
      qed
    qed
  qed
  obtain p where p: "path (clink G) y p" "lastd y p = x"
    using connected_clink[OF connectedG yD xD] by blast
  have "Inv y" using p yD
  proof (induction p arbitrary: y)
    case Nil
    then show ?case using base by simp
  next
    case (Cons y' p)
    have cl: "clink G y y'" and py: "path (clink G) y' p" and ly: "lastd y' p = x"
      using Cons.prems by simp_all
    have y'D: "y' \<in> D" using clink_closed[OF cl] Cons.prems(3) by simp
    have IH: "Inv y'" using Cons.IH[OF py ly y'D] .
    consider (N) "y = n y'" | (F) "f y = y'" using cl by (auto simp: clink_def)
    then show ?case
    proof cases
      case N
      then show ?thesis using IH diskN_node[OF y'D] C1.diskN_node[OF y'D] C2.diskN_node[OF y'D]
        by (simp add: Inv_def)
    next
      case F
      show ?thesis by (rule step[OF Cons.prems(3) F IH])
    qed
  qed
  then show ?thesis by (simp add: Inv_def)
qed

lemma diskN_chord_ring: "y \<in> C1.diskN \<longleftrightarrow> y \<in> diskN \<and> y \<notin> C2.diskN"
proof (cases "y \<in> D")
  case True
  then show ?thesis using diskN_chord_inv[OF True] by blast
next
  case False
  then show ?thesis using C1.diskN_D diskN_D by blast
qed

lemma fband_chord_ring: "fband G cr1 y \<or> fband G cr2 y \<longleftrightarrow> fband G r y"
proof -
  obtain i p1 p2 where rt: "rot i r = x1 # p1 @ x2 # p2" and c1: "cr1 = x # x2 # p2"
    and c2: "cr2 = e x # x1 # p1"
    using decomp by blast
  have "set r = set (rot i r)" by simp
  also have "\<dots> = set (x1 # p1) \<union> set (x2 # p2)" using rt by auto
  finally have setr: "set r = set (x1 # p1) \<union> set (x2 # p2)" .
  have fx: "cface x x1" and fex: "cface (e x) x2" using fprojP rFx rFex by auto
  show ?thesis
  proof
    assume "fband G cr1 y \<or> fband G cr2 y"
    then obtain w where w: "w \<in> set cr1 \<union> set cr2" "cface y w" by (auto simp: fband_def)
    then consider "w = x" | "w = e x" | "w \<in> set r" using c1 c2 setr by auto
    then show "fband G r y"
    proof cases
      case 1
      then show ?thesis using fconnect_trans[OF w(2)] fx fprojP[OF rFx] by (auto simp: fband_def)
    next
      case 2
      then show ?thesis using fconnect_trans[OF w(2)] fex fprojP[OF rFex] by (auto simp: fband_def)
    next
      case 3
      then show ?thesis using w(2) by (auto simp: fband_def)
    qed
  next
    assume "fband G r y"
    then obtain w where w: "w \<in> set r" "cface y w" by (auto simp: fband_def)
    then have "w \<in> set cr1 \<or> w \<in> set cr2" using c1 c2 setr by auto
    then show "fband G cr1 y \<or> fband G cr2 y" using w(2) by (auto simp: fband_def)
  qed
qed

lemma C1_diskF_cface: "cface y z \<Longrightarrow> y \<in> C1.diskF \<longleftrightarrow> z \<in> C1.diskF"
  using C1.closed_cface[OF C1.diskF_face] by blast

lemma diskF_chord_ring: "y \<in> C1.diskF \<longleftrightarrow> y \<in> diskF \<and> y \<notin> C2.diskF"
proof (cases "fband G cr2 y")
  case True
  then obtain z where z: "z \<in> set cr2" "cface y z" by (auto simp: fband_def)
  have "z \<in> C2.diskN" using C2.r_diskN[OF z(1)] .
  then have "z \<notin> C1.diskN" using diskN_chord_ring by blast
  then have "z \<notin> C1.diskF" by (simp add: C1.diskF_def)
  then have "y \<notin> C1.diskF" using C1_diskF_cface[OF z(2)] by simp
  moreover have "fband G r y" using fband_chord_ring True by blast
  ultimately show ?thesis by (simp add: diskF_def)
next
  case False
  then show ?thesis using diskN_chord_ring fband_chord_ring[of y]
    by (auto simp: diskF_def C1.diskF_def C2.diskF_def)
qed

lemma nontrivial_chord_ring:
  assumes nx: "x2 \<noteq> next_in r x1" and ne: "C1.diskF \<noteq> {}"
  shows "nontrivial_ring G 0 cr1 \<and> length cr1 < length r"
proof -
  obtain i p1 p2 where i: "i < length r" and rt: "rot i r = x1 # p1 @ x2 # p2"
    and c1: "cr1 = x # x2 # p2" and c2: "cr2 = e x # x1 # p1"
    using decomp by blast
  have x1r: "x1 \<in> set r" using fprojP[OF rFx] by auto
  have dr: "distinct (x1 # p1 @ x2 # p2)" using distinct_r rt distinct_rot[of i r] by simp
  obtain x3 p1' where p1: "p1 = x3 # p1'"
  proof (cases p1)
    case Nil
    have "next_in (rot i r) x1 = x2" using rt Nil dr by (simp add: next_in_def)
    then have "next_in r x1 = x2" using next_in_rot[OF distinct_r x1r] by simp
    then show ?thesis using nx by simp
  next
    case (Cons a l)
    then show ?thesis using that by blast
  qed
  have len: "length cr1 < length r"
  proof -
    have "length r = length (rot i r)" by simp
    then show ?thesis using rt c1 p1 by simp
  qed
  have x3r: "x3 \<in> set r" using rt p1 set_rot[of i r] by (metis list.set_intros(1,2) set_append UnI1)
  have x3D: "x3 \<in> D" using x3r r_D by blast
  have x3N2: "x3 \<in> C2.diskN" using C2.r_diskN c2 p1 by simp
  then have x3N1: "x3 \<notin> C1.diskN" using diskN_chord_ring by blast
  have nb: "\<not> fband G cr1 x3"
  proof
    assume "fband G cr1 x3"
    then obtain w where w: "w \<in> set cr1" "cface x3 w" by (auto simp: fband_def)
    have fx: "cface x x1" using fprojP[OF rFx] by auto
    have "w = x \<or> w \<in> set (x2 # p2)" using w(1) c1 by simp
    then show False
    proof
      assume "w = x"
      then have "cface x3 x1" using fconnect_trans[OF w(2)] fx by simp
      then have "x3 = x1" using r_cface x3r x1r by blast
      then show False using dr p1 by simp
    next
      assume wr2: "w \<in> set (x2 # p2)"
      then have "w \<in> set r" using rt set_rot[of i r] by (metis UnI2 set_append list.set_intros(2))
      then have "x3 = w" using r_cface x3r w(2) by blast
      then show False using dr p1 wr2 by auto
    qed
  qed
  have "x3 \<in> C1.diskFC" using x3D x3N1 nb by (simp add: C1.diskFC_def)
  then have "nontrivial_ring G 0 cr1" using C1.nontrivial0P ne by blast
  then show ?thesis using len by simp
qed

end

section \<open>Chords of a ring disk\<close>

context revsnip_proper
begin

lemma ring_disk_chord:
  assumes nt: "nontrivial_ring G 0 r" and nc: "\<not> chordless snipd r"
  shows "\<exists>r'. scycle G (rlink G) r' \<and> set r' \<subseteq> D \<and> nontrivial_ring G 0 r' \<and> length r' < length r"
proof -
  obtain x0 y where x0: "x0 \<in> set r" and y: "y \<in> set r" and yp: "y \<noteq> prev_in r x0"
    and yn: "y \<noteq> next_in r x0" and ad: "adj snipd x0 y"
    using nc by (auto simp: chordless_def)
  obtain z where xz: "fconnect snipd_face x0 z" and zy: "fconnect snipd_face (snipd_edge z) y"
    using ad by (auto simp: adj_def rlink_def)
  have x0N: "x0 \<in> diskN" using r_diskN[OF x0] .
  have zN: "z \<in> diskN" using Sd.F.fconnect_in_D[of x0 z] xz x0N by simp
  have cxz: "cface x0 z" using P.patch_face_d'[of x0 z] x0N xz by simp
  have ezN: "snipd_edge z \<in> diskN" using snipd_edge_cl[OF zN] .
  have cezy: "cface (snipd_edge z) y" using P.patch_face_d'[of "snipd_edge z" y] ezN zy by simp
  have zr: "z \<notin> set r"
  proof
    assume zr: "z \<in> set r"
    have "x0 = z" by (rule r_cface[OF x0 zr cxz])
    then have "snipd_edge z = next_in r x0" using zN zr by (simp add: snipd_edge_def)
    then have "cface (next_in r x0) y" using cezy by simp
    then have "next_in r x0 = y" by (rule r_cface[OF next_in_mem[OF x0] y])
    then show False using yn by simp
  qed
  have ez: "snipd_edge z = e z" using zN zr by (simp add: snipd_edge_def)
  have dEz: "z \<in> diskE" using zN zr by (simp add: diskE_def)
  have rFz: "fband G r z" using x0 cxz F.fconnect_sym by (auto simp: fband_def)
  have rFez: "fband G r (e z)" using y cezy ez by (auto simp: fband_def)
  have pz: "fproj G r z = x0"
    using fproj_cface[OF F.fconnect_sym[OF cxz] rFz] simple_fproj[OF simple_r x0] by simp
  have pez: "fproj G r (e z) = y"
    using fproj_cface[OF _ rFez, of y] cezy ez simple_fproj[OF simple_r y] by simp
  interpret K1: chord G r z using dEz rFz rFez by unfold_locales
  have dEez: "e z \<in> diskE" using K1.dEex .
  interpret K2: chord G r "e z" using dEez rFez rFz by unfold_locales simp_all
  obtain t where t: "t \<in> diskF" using nt nontrivial0P by blast
  show ?thesis
  proof (cases "t \<in> K1.C1.diskF")
    case True
    have "K1.x2 \<noteq> next_in r K1.x1" using pz pez yn by simp
    then have "nontrivial_ring G 0 K1.cr1 \<and> length K1.cr1 < length r"
      using K1.nontrivial_chord_ring True by blast
    then show ?thesis using K1.sc1 by blast
  next
    case False
    then have tK2: "t \<in> K1.C2.diskF" using K1.diskF_chord_ring t by blast
    have "K2.cr1 = K1.cr2" by simp
    have x2': "K2.x2 = x0" using pz by simp
    have x1': "K2.x1 = y" using pez by simp
    have "x0 \<noteq> next_in r y"
    proof
      assume "x0 = next_in r y"
      then have "prev_in r x0 = y" using prev_next_in[OF distinct_r y] by simp
      then show False using yp by simp
    qed
    then have "K2.x2 \<noteq> next_in r K2.x1" using x1' x2' by simp
    moreover have "K1.C2.diskF \<noteq> {}" using tK2 by auto
    ultimately have "nontrivial_ring G 0 K2.cr1 \<and> length K2.cr1 < length r"
      using K2.nontrivial_chord_ring by blast
    then show ?thesis using K2.sc1 by blast
  qed
qed

end


section \<open>Rotation and set invariance of disks\<close>

lemma (in snip_ring) snip_ring_rot: "snip_ring G (rot k r)"
proof unfold_locales
  show "planar G" by (rule planarG)
  have "simple G (rot k r)"
    using simple_r by (simp add: simple_def map_rot)
  then show "scycle G (rlink G) (rot k r)" using cycle_r by (simp add: scycle_def cycle_rot)
  show "set (rot k r) \<subseteq> D" using r_D by simp
qed

context snip_ring
begin

lemma rot_disks:
  "snip_ring.diskN G (rot k r) = diskN" "snip_ring.diskE G (rot k r) = diskE"
  "snip_ring.diskF G (rot k r) = diskF" "snip_ring.diskFC G (rot k r) = diskFC"
proof -
  interpret K: snip_ring G "rot k r" by (rule snip_ring_rot)
  have dl: "K.dlink = dlink" by (simp add: K.dlink_def dlink_def fun_eq_iff)
  show N: "K.diskN = diskN" using dl by (simp add: K.diskN_def diskN_def K.dconnect_def dconnect_def)
  show "K.diskE = diskE" using N by (simp add: K.diskE_def diskE_def)
  have fb: "fband G (rot k r) = fband G r" by (simp add: fband_def fun_eq_iff)
  show "K.diskF = diskF" using N fb by (simp add: K.diskF_def diskF_def)
  show "K.diskFC = diskFC" using N fb by (simp add: K.diskFC_def diskFC_def)
qed

lemma nontrivial_ring_rot: "nontrivial_ring G m (rot k r) = nontrivial_ring G m r"
  by (simp add: nontrivial_ring_def rot_disks)

end

lemma (in hypermap) proper_ring_rot:
  assumes plainG: "plain G"
  shows "proper_ring G (rot k r) = proper_ring G r"
proof (cases "2 < length r")
  case True
  then show ?thesis using size_proper_ring[of r G] size_proper_ring[of "rot k r" G] by simp
next
  case False
  then consider "r = []" | a where "r = [a]" | a b where "r = [a, b]"
  proof (cases r rule: remdups_adj.cases)
    case (3 a b rest)
    then have "rest = []" using False by (cases rest) auto
    then show thesis using 3 that(3) by blast
  qed auto
  then show ?thesis
  proof cases
    case 1
    then show ?thesis by (simp add: rot_def)
  next
    case (2 a)
    then show ?thesis by (cases k) (simp_all add: rot_def)
  next
    case (3 a b)
    have "rot k [a, b] = [a, b] \<or> rot k [a, b] = [b, a]"
      by (cases k; cases "k - 1") (auto simp: rot_def)
    moreover have "e a \<noteq> b \<longleftrightarrow> e b \<noteq> a" using plain_eq[OF plainG] by metis
    ultimately show ?thesis using 3 by auto
  qed
qed

lemma (in hypermap) proper_rev_ring:
  assumes plainG: "plain G"
  shows "proper_ring G (rev_ring G r) = proper_ring G r"
proof (cases "2 < length r")
  case True
  then show ?thesis using size_proper_ring[of r G] size_proper_ring[of "rev_ring G r" G]
    by (simp add: rev_ring_def)
next
  case False
  then consider "r = []" | a where "r = [a]" | a b where "r = [a, b]"
  proof (cases r rule: remdups_adj.cases)
    case (3 a b rest)
    then have "rest = []" using False by (cases rest) auto
    then show thesis using 3 that(3) by blast
  qed auto
  then show ?thesis
  proof cases
    case 1
    then show ?thesis by (simp add: rev_ring_def)
  next
    case (2 a)
    then show ?thesis by (simp add: rev_ring_def)
  next
    case (3 a b)
    have "e (e b) \<noteq> e a \<longleftrightarrow> e a \<noteq> b" using plain_eq[OF plainG] by metis
    then show ?thesis using 3 by (simp add: rev_ring_def)
  qed
qed

end
