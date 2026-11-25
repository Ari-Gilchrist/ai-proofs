(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Embed1.thy
    Second half of embed.v up to embed_inj: perimeter adjacency, hom rings of length <= 5,
    embed_full, pre_embed_inj, the extension h1 to the whole kernel complement bc.
    Ported from G. Gonthier's Coq development (embed.v).
*)
theory Embed1
  imports Four_Colour_Maps.Embed
begin

context embed_ctx
begin
lemma adj_perimeter_set:
  assumes xD: "x \<in> C.D" and nac: "x \<notin> ac"
  shows "\<exists>y. y \<in> set rc \<and> C.cface x y \<and> y \<noteq> C.e (C.n y) \<and>
           {z. C.cface x z \<and> fband Gc rc (C.e z)} = {y, C.e (C.n y)}"
proof -
  have "fband Gc rc x" using xD nac by (simp add: ac_def kernel_def)
  then obtain y where yr: "y \<in> set rc" and xy: "C.cface x y" by (auto simp: fband_def)
  have rc0: "rc \<noteq> []" using yr by auto
  interpret E: revsnip_proper Gc erc by (rule erc_props(1)[OF rc0])
  have yD: "y \<in> C.D" using geoGc(8) yr by auto
  have plC: "C.e (C.e w) = w" for w using C.plain_eq[OF geoGc(4)] .
  define eny where "eny = C.e (C.n y)"
  have feny: "C.f eny = y" by (simp add: eny_def C.nodeK)
  have enyy: "C.cface eny y" using fconnect_step[of "C.f" eny] feny by simp
  have nyr: "C.n y \<in> set rc" using rcN yr by simp
  have eeny: "C.e eny = C.n y" using plC by (simp add: eny_def)
  have ne: "y \<noteq> eny"
  proof
    assume yeny: "y = eny"
    have nyD: "C.n y \<in> C.D" using yD by simp
    have "C.n y \<in> bc \<or> C.e (C.n y) \<in> bc" by (rule edge_perimeter[OF nyD])
    moreover have "C.e (C.n y) = y" using yeny[unfolded eny_def, symmetric] .
    ultimately show False using nyr yr by (simp add: bc_def)
  qed
  have fey: "fband Gc rc (C.e y)"
  proof -
    have "C.n (C.f (C.e y)) = y" using C.plain_eq'[OF geoGc(4), of "C.e y"] plC by simp
    then have "C.f (C.e y) \<in> set rc" using rcN[of "C.f (C.e y)"] yr by simp
    then show ?thesis using fconnect_step[of "C.f" "C.e y"] by (auto simp: fband_def)
  qed
  have enyerc: "eny \<in> set erc" using nyr by (auto simp: erc_def eny_def)
  have "{z. C.cface x z \<and> fband Gc rc (C.e z)} = {y, eny}"
  proof (intro set_eqI iffI)
    fix z assume "z \<in> {y, eny}"
    then show "z \<in> {z. C.cface x z \<and> fband Gc rc (C.e z)}"
    proof
      assume "z = y"
      then show ?thesis using xy fey by simp
    next
      assume "z \<in> {eny}"
      then have z: "z = eny" by simp
      have "C.cface x eny" by (rule fconnect_trans[OF xy C.F.fconnect_sym[OF enyy]])
      moreover have "fband Gc rc (C.e eny)" using nyr eeny by (auto simp: fband_def)
      ultimately show ?thesis using z by simp
    qed
  next
    fix z assume "z \<in> {z. C.cface x z \<and> fband Gc rc (C.e z)}"
    then have xz: "C.cface x z" and fez: "fband Gc rc (C.e z)" by auto
    show "z \<in> {y, eny}"
    proof (rule ccontr)
      assume nz: "z \<notin> {y, eny}"
      have yz: "C.cface y z" by (rule fconnect_trans[OF C.F.fconnect_sym[OF xy] xz])
      have zD: "z \<in> C.D" using C.F.fconnect_in_D[OF yz] yD by simp
      have zr: "z \<notin> set rc"
      proof
        assume "z \<in> set rc"
        then have "y = z" by (rule C.simple_cface[OF geoGc(9) yr _ yz])
        then show False using nz by simp
      qed
      have ezr: "C.e z \<notin> set rc"
      proof
        assume "C.e z \<in> set rc"
        then have "z \<in> set erc" using plC[of z] by (auto simp: erc_def image_iff) (metis plC)
        moreover have "C.cface z eny"
          by (rule fconnect_trans[OF C.F.fconnect_sym[OF yz] C.F.fconnect_sym[OF enyy]])
        ultimately have "z = eny" using E.r_cface enyerc by blast
        then show False using nz by simp
      qed
      have zbc: "z \<in> bc" using zD zr by (simp add: bc_def)
      have ezbc: "C.e z \<in> bc" using zD ezr by (simp add: bc_def)
      have "z \<in> ac \<or> C.e z \<in> ac" by (rule chordless_perimeter[OF zbc ezbc])
      moreover have "fband Gc rc z" using yr C.F.fconnect_sym[OF yz] by (auto simp: fband_def)
      ultimately show False using fez by (auto simp: ac_def kernel_def)
    qed
  qed
  then show ?thesis using yr xy ne by (auto simp: eny_def)
qed

lemma card_adj_perimeter:
  assumes "x \<in> C.D" and "x \<notin> ac"
  shows "card {z. C.cface x z \<and> fband Gc rc (C.e z)} = 2"
  using adj_perimeter_set[OF assms] by auto

lemma arity_perimeter:
  assumes xD: "x \<in> C.D" and nac: "x \<notin> ac"
  shows "3 \<le> arity Gc x \<and> arity Gc x \<le> 6"
proof -
  obtain y where yr: "y \<in> set rc" and xy: "C.cface x y" using adj_perimeter_set[OF assms] by blast
  have "good_ring_arity Gc y" using embedGc yr by (simp add: embeddable_def)
  moreover have "arity Gc x = arity Gc y" by (rule C.arity_cface[OF xy])
  ultimately show ?thesis by (auto simp: good_ring_arity_def)
qed

lemma adj_kernel_split:
  assumes xD: "x \<in> C.D" and nac: "x \<notin> ac"
  shows "card {z. C.cface x z \<and> \<not> fband Gc rc (C.e z)} = arity Gc x - 2"
proof -
  define A where "A = {z. C.cface x z}"
  define B where "B = {z. C.cface x z \<and> fband Gc rc (C.e z)}"
  have fA: "finite A" using C.F.finite_cyc[of x] by (simp add: A_def cyc_def)
  have BA: "B \<subseteq> A" by (auto simp: A_def B_def)
  have cA: "card A = arity Gc x" by (simp add: A_def order_def cyc_def)
  have cB: "card B = 2" using card_adj_perimeter[OF assms] by (simp add: B_def)
  have "A - B = {z. C.cface x z \<and> \<not> fband Gc rc (C.e z)}" by (auto simp: A_def B_def)
  moreover have "card (A - B) = card A - card B" by (rule card_Diff_subset[OF finite_subset[OF BA fA] BA])
  ultimately show ?thesis using cA cB by simp
qed

lemma adj_kernel_min:
  assumes xD: "x \<in> C.D" and nac: "x \<notin> ac"
  shows "\<exists>y \<in> ac. C.cface x (C.e y)"
proof -
  have "card {z. C.cface x z \<and> \<not> fband Gc rc (C.e z)} \<noteq> 0"
    using adj_kernel_split[OF assms] arity_perimeter[OF assms] by simp
  then obtain z where xz: "C.cface x z" and nb: "\<not> fband Gc rc (C.e z)"
    by (metis (mono_tags, lifting) card.empty empty_Collect_eq)
  have "z \<in> C.D" using C.F.fconnect_in_D[OF xz] xD by simp
  then have "C.e z \<in> ac" using nb by (simp add: ac_def kernel_def)
  moreover have "C.e (C.e z) = z" by (rule C.plain_eq[OF geoGc(4)])
  ultimately show ?thesis using xz by metis
qed

lemma adj_kernel_max:
  assumes xD: "x \<in> C.D" and nac: "x \<notin> ac"
  shows "card {z. C.cface x z \<and> C.e z \<in> ac} \<le> 4"
proof -
  have fin: "finite {z. C.cface x z \<and> \<not> fband Gc rc (C.e z)}"
    using C.F.finite_cyc[of x] by (rule finite_subset[rotated]) (auto simp: cyc_def)
  have "{z. C.cface x z \<and> C.e z \<in> ac} \<subseteq> {z. C.cface x z \<and> \<not> fband Gc rc (C.e z)}"
    by (auto simp: ac_def kernel_def)
  then have "card {z. C.cface x z \<and> C.e z \<in> ac} \<le> arity Gc x - 2"
    using card_mono[OF fin] adj_kernel_split[OF assms] by metis
  then show ?thesis using arity_perimeter[OF assms] by arith
qed

lemma h_node:
  assumes w: "w \<in> ac" and nw: "C.n w \<in> ac"
  shows "h (C.n w) = M.n (h w)"
proof -
  have few: "C.f (C.e (C.n w)) = w" by (rule C.nodeK)
  have ew: "C.e (C.n w) \<in> ac" using acF[of "C.e (C.n w)"] few w by simp
  have he: "h (C.e (C.n w)) = M.e (h (C.n w))" by (rule embed_functor[OF nw ew])
  have "h w = M.f (h (C.e (C.n w)))" using hF[OF ew] few by simp
  then have "h w = M.f (M.e (h (C.n w)))" using he by simp
  then have "M.n (h w) = M.n (M.f (M.e (h (C.n w))))" by simp
  also have "\<dots> = M.e (M.e (h (C.n w)))" by (rule M.plain_eq'[OF M.plainG])
  also have "\<dots> = h (C.n w)" by (rule M.plain_eq[OF M.plainG])
  finally show ?thesis by simp
qed

lemma ac_ffe:
  assumes a: "a \<in> ac" and b: "b \<in> ac" and ab: "rlink Gc a b" and hb: "h b = M.f (M.f (M.e (h a)))"
  shows "b = C.f (C.f (C.e a))"
proof -
  have eab: "C.cface (C.e a) b" using ab by (simp add: rlink_def)
  have ea: "C.e a \<in> ac" by (rule ac_cface[OF b C.F.fconnect_sym[OF eab]])
  have fea: "C.f (C.e a) \<in> ac" using acF ea by blast
  have ffea: "C.f (C.f (C.e a)) \<in> ac" using acF fea by blast
  have "h (C.f (C.f (C.e a))) = M.f (M.f (h (C.e a)))" using hF[OF ea] hF[OF fea] by simp
  also have "h (C.e a) = M.e (h a)" by (rule embed_functor[OF a ea])
  finally have heq: "h b = h (C.f (C.f (C.e a)))" using hb by simp
  have "C.cface (C.e a) (C.f (C.f (C.e a)))"
    by (rule fconnect_trans[OF fconnect_step fconnect_step])
  then have "C.cface b (C.f (C.f (C.e a)))" by (rule fconnect_trans[OF C.F.fconnect_sym[OF eab]])
  then show ?thesis using cface_inj_embed[OF b] heq by blast
qed

lemma node_ffe:
  assumes a: "a \<in> bc" and b: "b = C.f (C.f (C.e a))"
  shows "C.cface (C.n a) (C.n b)"
proof -
  have cub: "C.n (C.n (C.n a)) = a" using bc_cubic[OF a] by simp
  have fe: "C.f (C.e a) = C.n (C.n a)" using C.nodeK[of "C.n (C.n a)"] cub by simp
  have "C.n b = C.e (C.f (C.e a))" using b C.plain_eq'[OF geoGc(4)] by simp
  then have "C.f (C.n b) = C.n a" using fe C.nodeK[of "C.n a"] by simp
  then have "C.cface (C.n b) (C.n a)" using fconnect_step[of "C.f" "C.n b"] by simp
  then show ?thesis by (rule C.F.fconnect_sym)
qed

lemma hom_ring5:
  assumes hr: "pre_hom_ring x p" and l4: "length p = 4"
    and dF1: "fcard (face Gm) (snip_ring.diskF Gm (map h (x # p))) \<le> 1"
  shows "rlink Gc (lastd x p) x"
proof (rule ccontr)
  assume nR: "\<not> rlink Gc (lastd x p) x"
  define xp where "xp = x # p"
  define hxp where "hxp = map h xp"
  have xRp: "path (rlink Gc) x p" and pac: "set xp \<subseteq> ac" and Uh: "scycle Gm (rlink Gm) hxp"
    using hr unfolding pre_hom_ring_def xp_def hxp_def by blast+
  have hxpD: "set hxp \<subseteq> M.D" using pac hD by (auto simp: hxp_def ac_def)
  have len: "length hxp = 5" using l4 by (simp add: hxp_def xp_def)
  have prh: "proper_ring Gm hxp" by (rule size_proper_ring) (simp add: len)
  interpret H: revsnip_proper Gm hxp by (rule M.revsnip_properI[OF Uh hxpD prh])
  have simp_h: "simple Gm hxp" using Uh by (simp add: scycle_def)
  have dh: "distinct hxp" by (rule M.simple_distinct[OF simp_h])
  have dxp: "distinct xp" using dh by (simp add: hxp_def distinct_map)
  have inj: "inj_on h (set xp)" using dh by (simp add: hxp_def distinct_map)
  have plM: "M.e (M.e w) = w" for w using M.plain_eq[OF M.plainG] .
  \<comment> \<open>the face disk is a single face\<close>
  have neF: "H.diskF \<noteq> {}"
  proof
    assume e: "H.diskF = {}"
    have "rlink Gc (lastd x p) x" by (rule trivial_hom_ring_aux[OF hr]) (use e in \<open>simp add: hxp_def xp_def\<close>)
    then show False using nR by simp
  qed
  then obtain u where uF: "u \<in> H.diskF" by blast
  have finF: "finite (cyc M.f ` H.diskF)" using H.diskF_D M.finite_darts finite_subset by blast
  have cF: "card (cyc M.f ` H.diskF) \<le> 1" using dF1 by (simp add: fcard_def hxp_def xp_def)
  have DdF: "v \<in> H.diskF \<longleftrightarrow> M.cface u v" for v
  proof
    assume vF: "v \<in> H.diskF"
    have all1: "\<forall>a \<in> cyc M.f ` H.diskF. \<forall>b \<in> cyc M.f ` H.diskF. a = b"
      by (rule iffD1[OF card_le_Suc0_iff_eq[OF finF] cF[unfolded One_nat_def]])
    have "cyc M.f u \<in> cyc M.f ` H.diskF" "cyc M.f v \<in> cyc M.f ` H.diskF"
      using uF vF by blast+
    then have "cyc M.f u = cyc M.f v" using all1 by blast
    then show "M.cface u v" by (simp add: M.F.cyc_eq_iff)
  next
    assume "M.cface u v"
    then show "v \<in> H.diskF" by (rule H.diskF_cface[OF uF])
  qed
  have uD: "u \<in> M.D" using uF H.diskF_D by blast
  interpret U: spoke_ctx Gm u using M.birk_axioms uD by (simp add: spoke_ctx_def spoke_ctx_axioms_def)
  \<comment> \<open>the band of the ring is the band of the spoke ring of u\<close>
  have sub1: "fband Gm hxp v" if fsr: "fband Gm U.sr v" for v
  proof -
    obtain w where wsr: "w \<in> set U.sr" and vw: "M.cface v w" using fsr by (auto simp: fband_def)
    have unw: "M.cface u (M.n w)" using wsr by (simp add: U.mem_sr)
    have wD: "w \<in> M.D" by (rule U.sr_D[OF wsr])
    have "M.n w \<in> H.diskF" using DdF[of "M.n w"] unw by simp
    then have "M.n w \<in> H.diskN" by (simp add: H.diskF_def)
    then have wN: "w \<in> H.diskN" using H.diskN_node[OF wD] by simp
    have "w \<notin> H.diskF"
    proof
      assume "w \<in> H.diskF"
      then have "M.cface u w" using DdF by blast
      then have "M.cface (M.n w) w" by (rule fconnect_trans[OF M.F.fconnect_sym[OF unw]])
      then show False using M.no_cface_node[OF wD] by simp
    qed
    then have "fband Gm hxp w" using wN by (simp add: H.diskF_def)
    then show ?thesis using M.fband_cface[OF vw] by simp
  qed
  have eqb: "fband Gm U.sr v" if vb: "fband Gm hxp v" for v
  proof -
    define A where "A = {w \<in> M.D. fband Gm U.sr w}"
    define B where "B = {w \<in> M.D. fband Gm hxp w}"
    have AB: "cyc M.f ` A \<subseteq> cyc M.f ` B" using sub1 by (auto simp: A_def B_def)
    have finB: "finite (cyc M.f ` B)" using M.finite_darts by (auto simp: B_def)
    have cA: "card (cyc M.f ` A) = length U.sr"
      using M.simple_fcard_fband[OF _ U.sr_subset] U.scycle_sr by (simp add: A_def fcard_def scycle_def)
    have cB: "card (cyc M.f ` B) = 5"
      using M.simple_fcard_fband[OF simp_h hxpD] len by (simp add: B_def fcard_def)
    have "card (cyc M.f ` B) \<le> card (cyc M.f ` A)" using cA cB U.length_sr_gt by simp
    then have AB': "cyc M.f ` A = cyc M.f ` B" by (rule card_seteq[OF finB AB])
    obtain w where wr: "w \<in> set hxp" and vw: "M.cface v w" using vb by (auto simp: fband_def)
    have "w \<in> M.D" using hxpD wr by blast
    then have vD: "v \<in> M.D" using M.F.fconnect_in_D[OF vw] by simp
    then have "cyc M.f v \<in> cyc M.f ` A" using AB' vb by (auto simp: B_def)
    then obtain a where aA: "a \<in> A" and "cyc M.f a = cyc M.f v" by blast
    then have "M.cface a v" by (simp add: M.F.cyc_eq_iff)
    then show ?thesis using aA M.fband_cface[of a v] by (simp add: A_def)
  qed
  have hxp_ru: "v \<in> set U.sr" if vr: "v \<in> set hxp" for v
  proof -
    have "adj Gm u v" using eqb[OF M.fband_ring[OF vr]] U.fband_sr by simp
    moreover have "adj Gm u (M.e v)"
    proof -
      have "M.cface (M.e v) (next_in hxp v)" by (rule H.cface_e_next[OF vr])
      then have "fband Gm hxp (M.e v)" using next_in_mem[OF vr] by (auto simp: fband_def)
      then show ?thesis using eqb U.fband_sr by simp
    qed
    ultimately have "v \<in> set U.sr \<or> M.e v \<in> set U.sr" by (rule U.adj11_edge)
    then show ?thesis
    proof
      assume ev: "M.e v \<in> set U.sr"
      have vD: "v \<in> M.D" using vr hxpD by blast
      have "M.cface u (M.n (M.e v))" using ev by (simp add: U.mem_sr)
      then have "M.n (M.e v) \<in> H.diskF" using DdF[of "M.n (M.e v)"] by simp
      then have "M.n (M.e v) \<in> H.diskN" by (simp add: H.diskF_def)
      then have "M.e v \<in> H.diskN" using H.diskN_node[of "M.e v"] vD by simp
      then show ?thesis using H.diskN_edge_ring[OF prh vr] by simp
    qed
  qed
  have nxt: "next_in hxp v = M.f (M.f (M.e v))" if vr: "v \<in> set hxp" for v
  proof -
    have vs: "v \<in> set U.sr" by (rule hxp_ru[OF vr])
    have ns: "next_in U.sr v = M.f (M.f (M.e v))" using U.next_sr[OF vs] by (simp add: U.spoke_def)
    have n1: "next_in hxp v \<in> set U.sr" by (rule hxp_ru[OF next_in_mem[OF vr]])
    have n2: "M.f (M.f (M.e v)) \<in> set U.sr" using next_in_mem[OF vs] ns by simp
    have "M.cface (M.e v) (M.f (M.f (M.e v)))" by (rule fconnect_trans[OF fconnect_step fconnect_step])
    then have "M.cface (next_in hxp v) (M.f (M.f (M.e v)))"
      by (rule fconnect_trans[OF M.F.fconnect_sym[OF H.cface_e_next[OF vr]]])
    then show ?thesis by (rule U.S.r_cface[OF n1 n2])
  qed
  \<comment> \<open>consecutive darts of the ring have face-connected nodes\<close>
  have pair: "C.cface (C.n a) (C.n b)" if dec: "xp = l1 @ a # b # l2" for l1 a b l2
  proof -
    have a: "a \<in> ac" and b: "b \<in> ac" using pac dec by auto
    have ab: "rlink Gc a b" using path_mid[OF xRp, of l1 a b l2] dec by (simp add: xp_def)
    have "hxp = map h l1 @ h a # h b # map h l2" using dec by (simp add: hxp_def)
    then have "next_in hxp (h a) = h b" using next_in_mid[of "map h l1" "h a" "h b" "map h l2"] dh by simp
    moreover have "h a \<in> set hxp" using dec by (simp add: hxp_def)
    ultimately have "h b = M.f (M.f (M.e (h a)))" using nxt by simp
    then have "b = C.f (C.f (C.e a))" by (rule ac_ffe[OF a b ab])
    then show ?thesis by (rule node_ffe[OF ac_bc[THEN subsetD, OF a]])
  qed
  have allN: "\<forall>i < length xp. C.cface (C.n x) (C.n (xp ! i))"
  proof (intro allI impI)
    fix i assume "i < length xp"
    then show "C.cface (C.n x) (C.n (xp ! i))"
    proof (induction i)
      case 0
      then show ?case by (simp add: xp_def)
    next
      case (Suc i)
      have il: "i < length xp" using Suc.prems by simp
      have d1: "xp = take i xp @ xp ! i # drop (Suc i) xp" by (rule id_take_nth_drop[OF il])
      have d2: "drop (Suc i) xp = xp ! Suc i # drop (Suc (Suc i)) xp"
        by (rule Cons_nth_drop_Suc[symmetric, OF Suc.prems])
      have "xp = take i xp @ xp ! i # xp ! Suc i # drop (Suc (Suc i)) xp"
        using d1 d2 by simp
      then have "C.cface (C.n (xp ! i)) (C.n (xp ! Suc i))" by (rule pair)
      then show ?case by (rule fconnect_trans[OF Suc.IH[OF il]])
    qed
  qed
  have nxpF: "C.cface (C.n x) (C.n z)" if zx: "z \<in> set xp" for z
  proof -
    obtain i where "i < length xp" "xp ! i = z" using zx by (auto simp: in_set_conv_nth)
    then show ?thesis using allN by blast
  qed
  \<comment> \<open>the node of x is not in the kernel\<close>
  define y where "y = lastd x p"
  have yxp: "y \<in> set xp" by (simp add: y_def xp_def)
  have xac: "x \<in> ac" and yac: "y \<in> ac" using pac yxp by (auto simp: xp_def)
  have Lhp: "h x = M.f (M.f (M.e (h y)))"
  proof -
    obtain p' where p': "p = p' @ [y]" using l4 by (cases p rule: rev_cases) (auto simp: y_def)
    have "hxp = h x # map h p' @ [h y]" using p' by (simp add: hxp_def xp_def)
    then have "next_in hxp (h y) = h x" using next_in_last[of "h x" "map h p'" "h y"] dh by simp
    then show ?thesis using nxt[of "h y"] yxp by (simp add: hxp_def)
  qed
  have nxac: "C.n x \<notin> ac"
  proof
    assume nxac: "C.n x \<in> ac"
    have nxny: "C.cface (C.n x) (C.n y)" by (rule nxpF[OF yxp])
    have nyac: "C.n y \<in> ac" by (rule ac_cface[OF nxac nxny])
    have hnx: "h (C.n x) = M.n (h x)" by (rule h_node[OF xac nxac])
    have hny: "h (C.n y) = M.n (h y)" by (rule h_node[OF yac nyac])
    have hyD: "h y \<in> M.D" using hD yac by (auto simp: ac_def)
    have "M.n (h x) = M.e (M.f (M.e (h y)))" using Lhp M.plain_eq'[OF M.plainG] by simp
    moreover have "M.f (M.e (h y)) = M.n (M.n (h y))"
      using M.nodeK[of "M.n (M.n (h y))"] M.nnn[OF hyD] by simp
    ultimately have "M.f (M.n (h x)) = M.n (h y)" using M.nodeK[of "M.n (h y)"] by simp
    then have heq: "h (C.n y) = h (C.f (C.n x))" using hF[OF nxac] hnx hny by simp
    have "C.cface (C.n y) (C.f (C.n x))"
      by (rule fconnect_trans[OF C.F.fconnect_sym[OF nxny] fconnect_step])
    then have nyf: "C.n y = C.f (C.n x)" using cface_inj_embed[OF nyac] heq by blast
    have cub: "C.n (C.n (C.n y)) = y" using bc_cubic(1)[OF ac_bc[THEN subsetD, OF yac]] .
    have "C.f (C.e y) = C.n (C.n y)" using C.nodeK[of "C.n (C.n y)"] cub by simp
    also have "\<dots> = C.e (C.n x)" using nyf C.plain_eq'[OF geoGc(4)] by simp
    finally have "C.cface (C.e y) (C.e (C.n x))" using fconnect_step[of "C.f" "C.e y"] by simp
    moreover have "C.cface (C.e (C.n x)) x" using fconnect_step[of "C.f" "C.e (C.n x)"] C.nodeK by simp
    ultimately have "rlink Gc y x" unfolding rlink_def by (rule fconnect_trans)
    then show False using nR by (simp add: y_def)
  qed
  \<comment> \<open>five distinct nodes in one face, all edge-adjacent to the kernel: too many\<close>
  have xD: "x \<in> C.D" using xac by (simp add: ac_def)
  have nxD: "C.n x \<in> C.D" using xD by simp
  have sub: "C.n ` set xp \<subseteq> {z. C.cface (C.n x) z \<and> C.e z \<in> ac}"
  proof
    fix z assume "z \<in> C.n ` set xp"
    then obtain w where w: "w \<in> set xp" and z: "z = C.n w" by blast
    have "C.e (C.n w) \<in> ac" using acF[of "C.e (C.n w)"] C.nodeK[of w] pac w by auto
    then show "z \<in> {z. C.cface (C.n x) z \<and> C.e z \<in> ac}" using nxpF[OF w] z by simp
  qed
  have fin: "finite {z. C.cface (C.n x) z \<and> C.e z \<in> ac}"
    using C.F.finite_cyc[of "C.n x"] by (rule finite_subset[rotated]) (auto simp: cyc_def)
  have "card (C.n ` set xp) = 5"
  proof -
    have "inj_on C.n (set xp)" using C.N.inj by (rule inj_on_subset) simp
    then have "card (C.n ` set xp) = card (set xp)" by (rule card_image)
    also have "\<dots> = 5" using dxp l4 distinct_card by (fastforce simp: xp_def)
    finally show ?thesis .
  qed
  then have "5 \<le> card {z. C.cface (C.n x) z \<and> C.e z \<in> ac}" using card_mono[OF fin sub] by simp
  then show False using adj_kernel_max[OF nxD nxac] by simp
qed

lemma rev_rlink_path:
  assumes xp: "path (rlink Gc) x p1"
  shows "path (rlink Gc) (C.e (lastd x p1)) (rev (map C.e (butlast (x # p1))))"
proof -
  have plC: "C.e (C.e w) = w" for w using C.plain_eq[OF geoGc(4)] .
  have st: "rlink Gc (C.e b) (C.e a)" if "rlink Gc a b" for a b
    using C.F.fconnect_sym[OF that[unfolded rlink_def]] plC by (simp add: rlink_def)
  have "path (\<lambda>a b. rlink Gc (C.e b) (C.e a)) x p1" by (rule path_mono[OF st xp])
  then have "path (\<lambda>a b. rlink Gc b a) (C.e x) (map C.e p1)" by (simp add: path_map)
  then have "path (rlink Gc) (lastd (C.e x) (map C.e p1)) (rev (belast (C.e x) (map C.e p1)))"
    by (simp only: path_rev)
  moreover have "lastd (C.e x) (map C.e p1) = C.e (lastd x p1)" by (cases p1 rule: rev_cases) simp_all
  moreover have "belast (C.e x) (map C.e p1) = map C.e (butlast (x # p1))" by (simp add: map_butlast)
  ultimately show ?thesis by simp
qed

lemma short_hom_ring_F:
  assumes hr: "pre_hom_ring x p" and l4: "length p \<le> 4"
    and dF: "fcard (face Gm) (snip_ring.diskF Gm (map h (x # p))) \<le> (if length p = 4 then 1 else 0)"
  shows "rlink Gc (lastd x p) x"
proof (cases "length p = 4")
  case True
  then show ?thesis using hom_ring5[OF hr True] dF by simp
next
  case False
  then have "fcard (face Gm) (snip_ring.diskF Gm (map h (x # p))) = 0" using dF by simp
  then show ?thesis by (rule trivial_hom_ring[OF hr])
qed

theorem short_hom_ring:
  assumes hr: "pre_hom_ring x p" and l4: "length p \<le> 4"
  shows "rlink Gc (lastd x p) x"
proof (rule ccontr)
  assume nR: "\<not> rlink Gc (lastd x p) x"
  define xp where "xp = x # p"
  define hxp where "hxp = map h xp"
  have xRp: "path (rlink Gc) x p" and pac: "set xp \<subseteq> ac" and Uh: "scycle Gm (rlink Gm) hxp"
    using hr unfolding pre_hom_ring_def xp_def hxp_def by blast+
  have hxpD: "set hxp \<subseteq> M.D" using pac hD by (auto simp: hxp_def ac_def)
  have plC: "C.e (C.e w) = w" for w using C.plain_eq[OF geoGc(4)] .
  have plM: "M.e (M.e w) = w" for w using M.plain_eq[OF M.plainG] .
  have xac: "x \<in> ac" using pac by (simp add: xp_def)
  have pne: "p \<noteq> []"
  proof
    assume "p = []"
    then show False using M.ring1_impossible[of "h x"] Uh hxpD by (simp add: hxp_def xp_def)
  qed
  then obtain p1 y where p: "p = p1 @ [y]" by (cases p rule: rev_cases) auto
  define w where "w = x # p1"
  have xpw: "xp = w @ [y]" by (simp add: xp_def w_def p)
  have yac: "y \<in> ac" using pac xpw by simp
  have wac: "set w \<subseteq> ac" using pac xpw by simp
  have hyRx: "rlink Gm (h y) (h x)"
  proof -
    have "cycle (rlink Gm) hxp" using Uh by (simp add: scycle_def)
    then show ?thesis by (simp add: hxp_def xp_def p cycle_Cons)
  qed
  have lwy: "rlink Gc (last w) y" using xRp by (simp add: p w_def)
  have nRe: "\<not> (y = C.e x)"
  proof
    assume "y = C.e x"
    then have "rlink Gc y x" using plC by (simp add: rlink_def)
    then show False using nR by (simp add: p)
  qed
  have prh: "proper_ring Gm hxp"
  proof (cases p1)
    case (Cons a l)
    then show ?thesis by (intro size_proper_ring) (simp add: hxp_def xp_def p)
  next
    case Nil
    have xy: "rlink Gc x y" using xRp by (simp add: p Nil)
    have eac: "C.e x \<in> ac" by (rule ac_cface[OF yac C.F.fconnect_sym[OF xy[unfolded rlink_def]]])
    have "M.e (h x) \<noteq> h y"
    proof
      assume e: "M.e (h x) = h y"
      have "h (C.e x) = M.e (h x)" by (rule embed_functor[OF xac eac])
      then have "h (C.e x) = h y" using e by simp
      then have "C.e x = y" using cface_inj_embed[OF eac xy[unfolded rlink_def]] by simp
      then show False using nRe by simp
    qed
    then show ?thesis by (simp add: hxp_def xp_def p Nil)
  qed
  interpret H: revsnip_proper Gm hxp by (rule M.revsnip_properI[OF Uh hxpD prh])
  define m where "m = (if length p = 4 then 1 else 0 :: nat)"
  have lh: "length hxp \<le> 5" using l4 by (simp add: hxp_def xp_def)
  have "\<not> nontrivial_ring Gm (if length hxp = 5 then 1 else 0) hxp" by (rule M.Birkhoff[OF lh Uh hxpD])
  moreover have "(if length hxp = 5 then 1 else 0) = m" by (simp add: m_def hxp_def xp_def)
  ultimately have "fcard M.f H.diskF \<le> m \<or> fcard M.f H.diskFC \<le> m"
    by (simp add: nontrivial_ring_def not_less)
  then show False
  proof
    assume "fcard M.f H.diskF \<le> m"
    then have "rlink Gc (lastd x p) x" using short_hom_ring_F[OF hr l4] by (simp add: m_def hxp_def xp_def)
    then show False using nR by simp
  next
    assume dFC: "fcard M.f H.diskFC \<le> m"
    \<comment> \<open>the reversed ring, pulled back to the configuration\<close>
    have ew: "C.e z \<in> ac" and hew: "h (C.e z) = M.e (h z)" if zw: "z \<in> set w" for z
    proof -
      obtain l1 l2 where wz: "w = l1 @ z # l2" using split_list[OF zw] by blast
      obtain z' rest where zr: "l2 @ [y] = z' # rest" by (cases l2) auto
      have dec: "x # p = l1 @ z # z' # rest" using xpw wz zr by (simp add: xp_def)
      then have zz: "rlink Gc z z'" by (rule path_mid[OF xRp])
      have "z' \<in> set (x # p)" unfolding dec by simp
      then have "z' \<in> set xp" by (simp add: xp_def)
      then have "z' \<in> ac" using pac by blast
      then show eac: "C.e z \<in> ac" by (rule ac_cface[OF _ C.F.fconnect_sym[OF zz[unfolded rlink_def]]])
      show "h (C.e z) = M.e (h z)" by (rule embed_functor[OF _ eac]) (use wac zw in blast)
    qed
    have "M.cface (h x) (M.e (h y))" using M.F.fconnect_sym[OF hyRx[unfolded rlink_def]] by simp
    then obtain ry where xry: "C.cface x ry" and hry: "h ry = M.e (h y)" using cface_h_ac[OF xac] by blast
    have ryac: "ry \<in> ac" by (rule ac_cface[OF xac xry])
    define rx where "rx = C.e (lastd x p1)"
    define rp where "rp = rev (map C.e (butlast w)) @ [ry]"
    have lw: "last w = lastd x p1" by (simp add: w_def)
    have rxp: "rx # rp = rev (map C.e w) @ [ry]"
      by (cases p1 rule: rev_cases) (simp_all add: rx_def rp_def w_def)
    have rpath: "path (rlink Gc) rx rp"
    proof -
      have a: "path (rlink Gc) rx (rev (map C.e (butlast w)))"
        using rev_rlink_path[OF conjunct1[OF xRp[unfolded p, simplified]]] by (simp add: rx_def w_def)
      have "lastd rx (rev (map C.e (butlast w))) = C.e x"
        by (cases p1 rule: rev_cases) (simp_all add: rx_def w_def)
      moreover have "rlink Gc (C.e x) ry" using xry plC by (simp add: rlink_def)
      ultimately show ?thesis using a by (simp add: rp_def)
    qed
    have mh: "map h (rx # rp) = rot 1 (rev_ring Gm hxp)"
    proof -
      have "map h (rev (map C.e w)) = rev (map M.e (map h w))"
        using hew by (simp add: rev_map[symmetric])
      then have "map h (rx # rp) = rev (map M.e (map h w)) @ [M.e (h y)]"
        using rxp hry by simp
      moreover have "rev_ring Gm hxp = M.e (h y) # rev (map M.e (map h w))"
        by (simp add: rev_ring_def hxp_def xpw)
      ultimately show ?thesis by (simp add: rot1_Cons)
    qed
    have rhr: "pre_hom_ring rx rp"
    proof (rule intro_pre_hom_ring[OF rpath])
      have "lastd rx rp = ry" by (simp add: rp_def)
      moreover have "M.cface (M.e (h ry)) (h rx)"
      proof -
        have lwac: "last w \<in> ac" using wac last_in_set[of w] by (auto simp: w_def)
        have "rlink Gm (h (last w)) (h y)" by (rule rlink_h[OF lwac yac lwy])
        then have "M.cface (h y) (M.e (h (last w)))"
          using M.F.fconnect_sym by (simp add: rlink_def)
        moreover have "h rx = M.e (h (last w))" using hew[of "last w"] by (simp add: rx_def w_def)
        ultimately show ?thesis using hry plM by simp
      qed
      ultimately show "rlink Gm (h (lastd rx rp)) (h rx)" by (simp add: rlink_def)
      show "set (rx # rp) \<subseteq> ac" using rxp ew ryac by auto
      have "simple Gm (rev_ring Gm hxp)" by (rule H.simple_rev_ring)
      then show "simple Gm (map h (rx # rp))" using mh by (simp add: H.simple_rot)
    qed
    have lrp: "length rp = length p" by (simp add: rp_def w_def p)
    have "snip_ring.diskF Gm (map h (rx # rp)) = H.R.diskF" using mh H.R.rot_disks(3) by simp
    also have "\<dots> = H.diskFC" using H.diskF_rev_ring[OF prh] by (auto simp: H.diskFC_def)
    finally have "fcard (face Gm) (snip_ring.diskF Gm (map h (rx # rp))) \<le> (if length rp = 4 then 1 else 0)"
      using dFC lrp by (simp add: m_def)
    then have rR: "rlink Gc (lastd rx rp) rx"
      using short_hom_ring_F[OF rhr] lrp l4 by simp
    \<comment> \<open>which pulls back to the closing link of the original ring\<close>
    have "C.cface (C.e ry) rx" using rR by (simp add: rp_def rlink_def)
    moreover have "C.cface rx y" using lwy by (simp add: rlink_def rx_def lw)
    ultimately have ery: "C.cface (C.e ry) y" by (rule fconnect_trans)
    have eryac: "C.e ry \<in> ac" by (rule ac_cface[OF yac C.F.fconnect_sym[OF ery]])
    have "h (C.e ry) = M.e (h ry)" by (rule embed_functor[OF ryac eryac])
    then have "h (C.e ry) = h y" using hry plM by simp
    then have "C.e ry = y" using cface_inj_embed[OF eryac ery] by simp
    then have "C.e y = ry" using plC by metis
    then have "rlink Gc y x" using C.F.fconnect_sym[OF xry] by (simp add: rlink_def)
    then show False using nR by (simp add: p)
  qed
qed

lemma simple_hom_path:
  "path (rlink Gc) x0 p \<Longrightarrow> set p \<subseteq> ac \<Longrightarrow> length p \<le> 5 \<Longrightarrow>
   \<exists>q. path (rlink Gc) x0 q \<and> lastd x0 q = lastd x0 p \<and> set q \<subseteq> ac \<and> simple Gm (map h q) \<and>
       length q \<le> length p"
proof (induction p arbitrary: x0)
  case Nil
  then show ?case by (intro exI[of _ "[]"]) (simp add: simple_def)
next
  case (Cons x1 p)
  have x0x1: "rlink Gc x0 x1" and x1p: "path (rlink Gc) x1 p" using Cons.prems(1) by simp_all
  have x1ac: "x1 \<in> ac" and pac: "set p \<subseteq> ac" using Cons.prems(2) by simp_all
  have lp: "length p \<le> 4" using Cons.prems(3) by simp
  obtain q where x1q: "path (rlink Gc) x1 q" and lq: "lastd x1 q = lastd x1 p" and qac: "set q \<subseteq> ac"
    and sq: "simple Gm (map h q)" and lenq: "length q \<le> length p"
    using Cons.IH[OF x1p pac] lp by auto
  have plC: "C.e (C.e w) = w" for w using C.plain_eq[OF geoGc(4)] .
  have plM: "M.e (M.e w) = w" for w using M.plain_eq[OF M.plainG] .
  show ?case
  proof (cases "fband Gm (map h q) (h x1)")
    case False
    show ?thesis
    proof (intro exI[of _ "x1 # q"] conjI)
      show "path (rlink Gc) x0 (x1 # q)" using x0x1 x1q by simp
      show "lastd x0 (x1 # q) = lastd x0 (x1 # p)" using lq by simp
      show "set (x1 # q) \<subseteq> ac" using x1ac qac by simp
      show "simple Gm (map h (x1 # q))" using False sq by (simp add: M.simple_Cons)
      show "length (x1 # q) \<le> length (x1 # p)" using lenq by simp
    qed
  next
    case True
    then obtain x2 where x2q: "x2 \<in> set q" and x12: "M.cface (h x1) (h x2)" by (auto simp: fband_def)
    have x2ac: "x2 \<in> ac" using x2q qac by blast
    obtain x3 where x23: "C.cface x2 x3" and hx3: "h x3 = h x1"
      using cface_h_ac[OF x2ac M.F.fconnect_sym[OF x12]] by blast
    have x3ac: "x3 \<in> ac" by (rule ac_cface[OF x2ac x23])
    obtain q1 q2 where q: "q = q1 @ x2 # q2" using split_list[OF x2q] by blast
    show ?thesis
    proof (cases "x1 = x3")
      case True
      show ?thesis
      proof (intro exI[of _ "x2 # q2"] conjI)
        have "C.cface (C.e x0) x2"
          using fconnect_trans[OF x0x1[unfolded rlink_def] C.F.fconnect_sym[OF x23[folded True]]] .
        moreover have "path (rlink Gc) x2 q2" using x1q q by simp
        ultimately show "path (rlink Gc) x0 (x2 # q2)" by (simp add: rlink_def)
        show "lastd x0 (x2 # q2) = lastd x0 (x1 # p)" using lq q by simp
        show "set (x2 # q2) \<subseteq> ac" using qac q by auto
        show "simple Gm (map h (x2 # q2))"
          using sq M.simple_append[of "map h q1" "map h (x2 # q2)"] q by simp
        show "length (x2 # q2) \<le> length (x1 # p)" using lenq q by simp
      qed
    next
      case False
      show ?thesis
      proof (cases q1)
        case Nil
        have x12': "rlink Gc x1 x2" using x1q q Nil by simp
        have ex1: "C.e x1 \<in> ac" by (rule ac_cface[OF x2ac C.F.fconnect_sym[OF x12'[unfolded rlink_def]]])
        have "h (C.e x1) = M.e (h x1)" by (rule embed_functor[OF x1ac ex1])
        moreover have "M.cface (h (C.e x1)) (h x2)" by (rule cface_ac_h[OF ex1 x12'[unfolded rlink_def]])
        ultimately have "M.cface (M.e (h x1)) (h x1)" using fconnect_trans[OF _ M.F.fconnect_sym[OF x12]] by simp
        moreover have "h x1 \<in> M.D" using hD x1ac by (auto simp: ac_def)
        ultimately show ?thesis using M.bridgelessG M.F.fconnect_sym by (auto simp: bridgeless_def)
      next
        case (Cons x q')
        have qx: "q = x # q' @ x2 # q2" using q Cons by simp
        have x1x: "rlink Gc x1 x" and xq': "path (rlink Gc) x (q' @ [x2])" using x1q qx by simp_all
        have xac: "x \<in> ac" using qac qx by simp
        have ex1: "C.e x1 \<in> ac" by (rule ac_cface[OF xac C.F.fconnect_sym[OF x1x[unfolded rlink_def]]])
        have hex1: "h (C.e x1) = M.e (h x1)" by (rule embed_functor[OF x1ac ex1])
        define r where "r = q' @ [x3]"
        have hr: "pre_hom_ring x r"
        proof (rule intro_pre_hom_ring)
          have "rlink Gc (lastd x q') x2" using xq' by simp
          then have "rlink Gc (lastd x q') x3" unfolding rlink_def by (rule fconnect_trans[OF _ x23])
          then show "path (rlink Gc) x r" using xq' by (simp add: r_def)
          have "M.cface (h (C.e x1)) (h x)" by (rule cface_ac_h[OF ex1 x1x[unfolded rlink_def]])
          then show "rlink Gm (h (lastd x r)) (h x)" using hex1 hx3 by (simp add: r_def rlink_def)
          show "set (x # r) \<subseteq> ac" using qac qx x3ac by (auto simp: r_def)
          have "simple Gm (map h (x # q' @ [x2]))"
            using sq M.simple_append[of "map h (x # q' @ [x2])" "map h q2"] qx by simp
          moreover have "M.cface (h x2) (h x3)" using M.F.fconnect_sym[OF x12] hx3 by simp
          ultimately show "simple Gm (map h (x # r))"
            using M.simple_snoc_cface[of "map h (x # q')" "h x2" "h x3"] by (simp add: r_def)
        qed
        have lr: "length r \<le> 4" using lenq lp qx by (simp add: r_def)
        have "rlink Gc (lastd x r) x" by (rule short_hom_ring[OF hr lr])
        then have e3x: "C.cface (C.e x3) x" by (simp add: r_def rlink_def)
        have ex3: "C.e x3 \<in> ac" by (rule ac_cface[OF xac C.F.fconnect_sym[OF e3x]])
        have "h (C.e x3) = M.e (h x3)" by (rule embed_functor[OF x3ac ex3])
        then have heq: "h (C.e x3) = h (C.e x1)" using hex1 hx3 by simp
        have "C.cface (C.e x3) (C.e x1)"
          by (rule fconnect_trans[OF e3x C.F.fconnect_sym[OF x1x[unfolded rlink_def]]])
        then have "C.e x3 = C.e x1" using cface_inj_embed[OF ex3] heq by blast
        then have "x3 = x1" using plC by metis
        then show ?thesis using False by simp
      qed
    qed
  qed
qed

theorem embed_full:
  assumes x1ac: "x1 \<in> ac" and x2ac: "x2 \<in> ac" and eh: "M.e (h x1) = h x2"
  shows "C.e x1 = x2"
proof (rule ccontr)
  assume ne: "C.e x1 \<noteq> x2"
  have plC: "C.e (C.e w) = w" for w using C.plain_eq[OF geoGc(4)] .
  have plM: "M.e (M.e w) = w" for w using M.plain_eq[OF M.plainG] .
  obtain x0 where x0ac: "x0 \<in> ac"
    and rad: "\<And>y. y \<in> ac \<Longrightarrow> at_radius2 Gc (kernel Gc rc) x0 y"
    using embedGc by (auto simp: embeddable_def radius2_def ac_def)
  have spoke2: "\<exists>a b z. C.cface y a \<and> C.cface x0 b \<and> C.cface (C.e a) z \<and> C.cface (C.e b) z \<and> z \<in> ac"
    if yac: "y \<in> ac" for y
  proof -
    obtain z where yz: "adj Gc y z" and x0z: "adj Gc x0 z" and kz: "kernel Gc rc z"
      using rad[OF yac] by (auto simp: at_radius2_def)
    obtain a where ya: "C.cface y a" and az: "C.cface (C.e a) z" using yz by (auto simp: C.adj_iff)
    obtain b where x0b: "C.cface x0 b" and bz: "C.cface (C.e b) z" using x0z by (auto simp: C.adj_iff)
    have "y \<in> C.D" using yac by (simp add: ac_def)
    then have "a \<in> C.D" using C.F.fconnect_in_D[OF ya] by simp
    then have "z \<in> C.D" using C.F.fconnect_in_D[OF az] by simp
    then have "z \<in> ac" using kz by (simp add: ac_def)
    then show ?thesis using ya x0b az bz by blast
  qed
  obtain a b z1 where x1a: "C.cface x1 a" and x0b: "C.cface x0 b" and az1: "C.cface (C.e a) z1"
    and bz1: "C.cface (C.e b) z1" and z1ac: "z1 \<in> ac" using spoke2[OF x1ac] by blast
  obtain c d z2 where x2c: "C.cface x2 c" and x0d: "C.cface x0 d" and cz2: "C.cface (C.e c) z2"
    and dz2: "C.cface (C.e d) z2" and z2ac: "z2 \<in> ac" using spoke2[OF x2ac] by blast
  define p where "p = [a, C.e b, d, C.e c, x2]"
  have pp: "path (rlink Gc) (C.e x1) p"
  proof -
    have r1: "rlink Gc (C.e x1) a" using x1a plC by (simp add: rlink_def)
    have r2: "rlink Gc a (C.e b)" unfolding rlink_def by (rule fconnect_trans[OF az1 C.F.fconnect_sym[OF bz1]])
    have r3: "rlink Gc (C.e b) d" unfolding rlink_def plC by (rule fconnect_trans[OF C.F.fconnect_sym[OF x0b] x0d])
    have r4: "rlink Gc d (C.e c)" unfolding rlink_def by (rule fconnect_trans[OF dz2 C.F.fconnect_sym[OF cz2]])
    have r5: "rlink Gc (C.e c) x2" unfolding rlink_def plC by (rule C.F.fconnect_sym[OF x2c])
    show ?thesis using r1 r2 r3 r4 r5 by (simp add: p_def)
  qed
  have pac: "set p \<subseteq> ac"
  proof -
    have "a \<in> ac" by (rule ac_cface[OF x1ac x1a])
    moreover have "C.e b \<in> ac" by (rule ac_cface[OF z1ac C.F.fconnect_sym[OF bz1]])
    moreover have "d \<in> ac" by (rule ac_cface[OF x0ac x0d])
    moreover have "C.e c \<in> ac" by (rule ac_cface[OF z2ac C.F.fconnect_sym[OF cz2]])
    ultimately show ?thesis using x2ac by (simp add: p_def)
  qed
  obtain q where eq: "path (rlink Gc) (C.e x1) q" and lq: "lastd (C.e x1) q = x2" and qac: "set q \<subseteq> ac"
    and sq: "simple Gm (map h q)" and lenq: "length q \<le> 5"
    using simple_hom_path[OF pp pac] by (auto simp: p_def)
  obtain x q' where q: "q = x # q'"
  proof (cases q)
    case Nil
    then show ?thesis using lq ne by simp
  qed
  have ex1x: "C.cface x1 x" using eq q plC by (simp add: rlink_def)
  have xac: "x \<in> ac" using qac q by simp
  have lx: "lastd x q' = x2" using lq q by simp
  have hr: "pre_hom_ring x q'"
  proof (rule intro_pre_hom_ring)
    show "path (rlink Gc) x q'" using eq q by simp
    have "M.cface (h x1) (h x)" by (rule cface_ac_h[OF x1ac ex1x])
    then show "rlink Gm (h (lastd x q')) (h x)" using lx eh[symmetric] plM by (simp add: rlink_def)
    show "set (x # q') \<subseteq> ac" using qac q by simp
    show "simple Gm (map h (x # q'))" using sq q by simp
  qed
  have "rlink Gc (lastd x q') x" by (rule short_hom_ring[OF hr]) (use lenq q in simp)
  then have e2x: "C.cface (C.e x2) x" using lx by (simp add: rlink_def)
  have ex2: "C.e x2 \<in> ac" by (rule ac_cface[OF xac C.F.fconnect_sym[OF e2x]])
  have "h (C.e x2) = M.e (h x2)" by (rule embed_functor[OF x2ac ex2])
  then have heq: "h (C.e x2) = h x1" using eh plM by metis
  have "C.cface (C.e x2) x1" by (rule fconnect_trans[OF e2x C.F.fconnect_sym[OF ex1x]])
  then have "C.e x2 = x1" using cface_inj_embed[OF ex2] heq by blast
  then show False using ne plC by metis
qed

lemma M_fef:
  assumes vD: "v \<in> M.D"
  shows "M.f (M.e (M.f v)) = M.n (M.e v)"
proof -
  have "M.n (M.f v) = M.e v" by (rule M.plain_eq'[OF M.plainG])
  then have "M.n (M.n (M.n (M.f v))) = M.n (M.n (M.e v))" by simp
  then have "M.f v = M.n (M.n (M.e v))" using M.nnn[of "M.f v"] vD by simp
  then show ?thesis using M.nodeK[of "M.n (M.e v)"] by simp
qed

theorem pre_embed_inj:
  assumes xac: "x \<in> ac" and yac: "y \<in> ac" and hxy: "h x = h y"
  shows "x = y"
proof -
  have plC: "C.e (C.e w) = w" for w using C.plain_eq[OF geoGc(4)] .
  have "C.e (C.e x) \<in> ac" using xac plC by simp
  then obtain q where qp: "path (rlink Gc) (C.e x) q" and ly: "C.cface (lastd (C.e x) q) y"
    and qne: "q \<noteq> []" and qac: "\<forall>u \<in> set q. u \<in> ac \<and> hc u"
    using h_spoke[of "C.e x" y] yac by blast
  obtain z1 q' where q: "q = z1 # q'" using qne by (cases q) auto
  have xz1: "C.cface x z1" using qp q plC by (simp add: rlink_def)
  have z1ac: "z1 \<in> ac" using qac q by simp
  have "C.cface y z1"
  proof (cases q')
    case Nil
    then show ?thesis using ly q by (simp add: C.F.fconnect_sym)
  next
    case (Cons z2 q'')
    have z12: "rlink Gc z1 z2" using qp q Cons by simp
    have z2ac: "z2 \<in> ac" using qac q Cons by simp
    have ez1: "C.e z1 \<in> ac" by (rule ac_cface[OF z2ac C.F.fconnect_sym[OF z12[unfolded rlink_def]]])
    have hez1: "h (C.e z1) = M.e (h z1)" by (rule embed_functor[OF z1ac ez1])
    have "M.cface (h x) (h z1)" by (rule cface_ac_h[OF xac xz1])
    then have "M.cface (h y) (h z1)" using hxy by simp
    then obtain t where yt: "C.cface y t" and ht: "h t = h z1" using cface_h_ac[OF yac] by blast
    have tac: "t \<in> ac" by (rule ac_cface[OF yac yt])
    have "M.e (h t) = h (C.e z1)" using ht hez1 by simp
    then have "C.e t = C.e z1" by (rule embed_full[OF tac ez1])
    then have "t = z1" using plC by metis
    then show ?thesis using yt by simp
  qed
  then have "C.cface x y" by (rule fconnect_trans[OF xz1 C.F.fconnect_sym])
  then show ?thesis using cface_inj_embed[OF xac] hxy by blast
qed

definition h1 :: "'a \<Rightarrow> 'b" where
  "h1 x = (if x \<in> ac then h x else if C.e x \<in> ac then M.e (h (C.e x))
           else if C.n x \<in> ac then M.f (M.e (h (C.n x)))
           else M.e (M.n (M.n (h (C.n (C.e x))))))"

lemma bc_rcN: "x \<in> C.D \<Longrightarrow> C.n x \<in> bc \<longleftrightarrow> x \<in> bc"
  using rcN by (simp add: bc_def)

lemma embed_cases_bc:
  assumes xbc: "x \<in> bc"
  shows "x \<in> ac \<or> C.e x \<in> ac \<or> C.n x \<in> ac"
proof -
  have xD: "x \<in> C.D" and xr: "x \<notin> set rc" using xbc by (auto simp: bc_def)
  have plC: "C.e (C.e w) = w" for w using C.plain_eq[OF geoGc(4)] .
  show ?thesis
  proof (cases "C.e x \<in> set rc")
    case False
    then have "C.e x \<in> bc" using xD by (simp add: bc_def)
    then show ?thesis using chordless_perimeter[OF xbc] by blast
  next
    case exr: True
    show ?thesis
    proof (cases "C.e (C.n x) \<in> set rc")
      case False
      have nxbc: "C.n x \<in> bc" using bc_rcN[OF xD] xbc by simp
      have "C.e (C.n x) \<in> bc" using False xD by (simp add: bc_def)
      then have "C.n x \<in> ac \<or> C.e (C.n x) \<in> ac" using chordless_perimeter[OF nxbc] by blast
      moreover have "C.e (C.n x) \<in> ac \<Longrightarrow> x \<in> ac" using acF[of "C.e (C.n x)"] C.nodeK[of x] by simp
      ultimately show ?thesis by blast
    next
      case enxr: True
      have "C.n (C.f x) = C.e x" by (rule C.plain_eq'[OF geoGc(4)])
      then have fxr: "C.f x \<in> set rc" using rcN[of "C.f x"] exr by simp
      have s1: "C.cface (C.e (C.n x)) x"
        using fconnect_step[of "C.f" "C.e (C.n x)"] by (simp only: C.nodeK)
      have "C.cface (C.e (C.n x)) (C.f x)"
        by (rule fconnect_trans[OF s1 fconnect_step[of "C.f" x]])
      then have fx: "C.e (C.n x) = C.f x" by (rule C.simple_cface[OF geoGc(9) enxr fxr])
      have "(C.f ^^ 2) (C.f x) = C.f x" using fx C.nodeK[of x] by (simp add: numeral_2_eq_2)
      then have "order C.f (C.f x) dvd 2" using C.F.order_dvd by blast
      then have "arity Gc (C.f x) \<le> 2" by (simp add: dvd_imp_le)
      moreover have "good_ring_arity Gc (C.f x)" using embedGc fxr by (simp add: embeddable_def)
      ultimately show ?thesis by (simp add: good_ring_arity_def)
    qed
  qed
qed

lemma bc_acN: "x \<in> bc \<Longrightarrow> x \<notin> ac \<Longrightarrow> C.e x \<notin> ac \<Longrightarrow> C.n x \<in> ac"
  using embed_cases_bc by blast

lemma nac_ebc: "x \<in> bc \<Longrightarrow> x \<notin> ac \<Longrightarrow> C.e x \<notin> ac \<Longrightarrow> C.e x \<notin> bc"
  using chordless_perimeter by blast

lemma embedE_bc:
  assumes xbc: "x \<in> bc"
  shows "h1 (C.e x) = M.e (h1 x)"
proof -
  have plC: "C.e (C.e w) = w" for w using C.plain_eq[OF geoGc(4)] .
  have plM: "M.e (M.e w) = w" for w using M.plain_eq[OF M.plainG] .
  have xD: "x \<in> C.D" using xbc by (simp add: bc_def)
  show ?thesis
  proof (cases "x \<in> ac")
    case xac: True
    show ?thesis
    proof (cases "C.e x \<in> ac")
      case True
      then show ?thesis using embed_functor[OF xac True] xac by (simp add: h1_def)
    next
      case False
      then show ?thesis using xac plC by (simp add: h1_def)
    qed
  next
    case xac: False
    show ?thesis
    proof (cases "C.e x \<in> ac")
      case True
      then show ?thesis using xac plC plM by (simp add: h1_def)
    next
      case exac: False
      have nxac: "C.n x \<in> ac" by (rule bc_acN[OF xbc xac exac])
      have "C.e x \<notin> bc" by (rule nac_ebc[OF xbc xac exac])
      then have "C.e x \<in> set rc" using xD by (simp add: bc_def)
      then have "C.n (C.e x) \<in> set rc" using rcN by simp
      then have nexac: "C.n (C.e x) \<notin> ac" using ac_bc by (auto simp: bc_def)
      have hD': "h (C.n x) \<in> M.D" using hD nxac by (auto simp: ac_def)
      have "M.f (M.e (h (C.n x))) = M.n (M.n (h (C.n x)))"
        using M.nodeK[of "M.n (M.n (h (C.n x)))"] M.nnn[OF hD'] by simp
      then show ?thesis using xac exac nxac nexac plC by (simp add: h1_def)
    qed
  qed
qed

lemma embedE:
  assumes xD: "x \<in> C.D"
  shows "h1 (C.e x) = M.e (h1 x)"
proof -
  have plC: "C.e (C.e w) = w" for w using C.plain_eq[OF geoGc(4)] .
  have plM: "M.e (M.e w) = w" for w using M.plain_eq[OF M.plainG] .
  have "x \<in> bc \<or> C.e x \<in> bc" by (rule edge_perimeter[OF xD])
  then show ?thesis
  proof
    assume "x \<in> bc"
    then show ?thesis by (rule embedE_bc)
  next
    assume "C.e x \<in> bc"
    then have "h1 (C.e (C.e x)) = M.e (h1 (C.e x))" by (rule embedE_bc)
    then have "h1 x = M.e (h1 (C.e x))" using plC by simp
    then show ?thesis using plM by simp
  qed
qed

lemma embedN:
  assumes xbc: "x \<in> bc"
  shows "h1 (C.n x) = M.n (h1 x)"
proof -
  have plC: "C.e (C.e w) = w" for w using C.plain_eq[OF geoGc(4)] .
  have plM: "M.e (M.e w) = w" for w using M.plain_eq[OF M.plainG] .
  have xD: "x \<in> C.D" using xbc by (simp add: bc_def)
  have cub: "C.n (C.n (C.n x)) = x" using bc_cubic[OF xbc] by simp
  have enxac: "C.e (C.n x) \<in> ac \<longleftrightarrow> x \<in> ac" using acF[of "C.e (C.n x)"] C.nodeK[of x] by simp
  have fex: "C.f (C.e x) = C.n (C.n x)" using C.nodeK[of "C.n (C.n x)"] cub by simp
  show ?thesis
  proof (cases "x \<in> ac")
    case xac: True
    show ?thesis
    proof (cases "C.n x \<in> ac")
      case True
      then show ?thesis using h_node[OF xac True] xac by (simp add: h1_def)
    next
      case False
      have enx: "C.e (C.n x) \<in> ac" using enxac xac by simp
      have "h x = M.f (h (C.e (C.n x)))" using hF[OF enx] C.nodeK[of x] by simp
      then have "h (C.e (C.n x)) = M.e (M.n (h x))" using M.faceK[of "h (C.e (C.n x))"] by simp
      then show ?thesis using xac False enx plM by (simp add: h1_def)
    qed
  next
    case xac: False
    show ?thesis
    proof (cases "C.e x \<in> ac")
      case exac: True
      have nnx: "C.n (C.n x) \<in> ac" using acF[of "C.e x"] exac fex by simp
      have hv: "h (C.e x) \<in> M.D" using hD exac by (auto simp: ac_def)
      have hnn: "h (C.n (C.n x)) = M.f (h (C.e x))" using hF[OF exac] fex by simp
      have key: "M.f (M.e (M.f (h (C.e x)))) = M.n (M.e (h (C.e x)))" by (rule M_fef[OF hv])
      show ?thesis
      proof (cases "C.n x \<in> ac")
        case nxac: True
        have ennx: "C.e (C.n (C.n x)) \<in> ac" using acF[of "C.e (C.n (C.n x))"] C.nodeK[of "C.n x"] nxac by simp
        have "h (C.e (C.n (C.n x))) = M.e (h (C.n (C.n x)))" by (rule embed_functor[OF nnx ennx])
        moreover have "h (C.n x) = M.f (h (C.e (C.n (C.n x))))" using hF[OF ennx] C.nodeK[of "C.n x"] by simp
        ultimately have "h (C.n x) = M.n (M.e (h (C.e x)))" using hnn key by simp
        then show ?thesis using xac exac nxac by (simp add: h1_def)
      next
        case nxac: False
        have "h1 (C.n x) = M.f (M.e (h (C.n (C.n x))))" using nxac enxac xac nnx by (simp add: h1_def)
        then show ?thesis using xac exac hnn key by (simp add: h1_def)
      qed
    next
      case exac: False
      have nxac: "C.n x \<in> ac" by (rule bc_acN[OF xbc xac exac])
      have "h1 x = M.f (M.e (h (C.n x)))" using xac exac nxac by (simp add: h1_def)
      moreover have "M.n (M.f (M.e (h (C.n x)))) = h (C.n x)"
        using M.plain_eq'[OF M.plainG, of "M.e (h (C.n x))"] plM by simp
      ultimately show ?thesis using nxac by (simp add: h1_def)
    qed
  qed
qed

lemma h1_ac: "x \<in> ac \<Longrightarrow> h1 x = h x" by (simp add: h1_def)
lemma h1_eac: "x \<notin> ac \<Longrightarrow> C.e x \<in> ac \<Longrightarrow> h1 x = M.e (h (C.e x))" by (simp add: h1_def)
lemma h1_nac: "x \<notin> ac \<Longrightarrow> C.e x \<notin> ac \<Longrightarrow> C.n x \<in> ac \<Longrightarrow> h1 x = M.f (M.e (h (C.n x)))"
  by (simp add: h1_def)

theorem embed_inj:
  assumes xbc: "x \<in> bc" and ybc: "y \<in> bc" and eq: "h1 x = h1 y"
  shows "x = y"
proof -
  have plC: "C.e (C.e w) = w" for w using C.plain_eq[OF geoGc(4)] .
  have plM: "M.e (M.e w) = w" for w using M.plain_eq[OF M.plainG] .
  have main: "x = y" if xac: "x \<in> ac" and ybc: "y \<in> bc" and eq: "h1 x = h1 y" for x y
  proof -
    have hx: "h1 x = h x" by (rule h1_ac[OF xac])
    show ?thesis
    proof (cases "y \<in> ac")
      case True
      have "h x = h y" using eq hx h1_ac[OF True] by simp
      then show ?thesis using pre_embed_inj[OF xac True] by simp
    next
      case yac: False
      show ?thesis
      proof (cases "C.e y \<in> ac")
        case True
        have "h x = M.e (h (C.e y))" using eq hx h1_eac[OF yac True] by simp
        then have "M.e (h x) = h (C.e y)" using plM by simp
        then have "C.e x = C.e y" by (rule embed_full[OF xac True])
        then show ?thesis using C.E.inj by (simp add: inj_eq)
      next
        case eyac: False
        have nyac: "C.n y \<in> ac" by (rule bc_acN[OF ybc yac eyac])
        have enx: "C.e (C.n x) \<in> ac" using acF[of "C.e (C.n x)"] C.nodeK[of x] xac by simp
        have a: "h x = M.f (h (C.e (C.n x)))" using hF[OF enx] C.nodeK[of x] by simp
        have b: "h x = M.f (M.e (h (C.n y)))" using eq hx h1_nac[OF yac eyac nyac] by simp
        have "h (C.e (C.n x)) = M.e (h (C.n y))" using a b M.F.inj by (simp add: inj_eq)
        then have "M.e (h (C.n y)) = h (C.e (C.n x))" by simp
        then have "C.e (C.n y) = C.e (C.n x)" by (rule embed_full[OF nyac enx])
        then have "C.n y = C.n x" using C.E.inj by (simp add: inj_eq)
        then show ?thesis using C.N.inj by (simp add: inj_eq)
      qed
    qed
  qed
  show ?thesis
  proof (cases "x \<in> ac")
    case True
    show ?thesis by (rule main[OF True ybc eq])
  next
    case xac: False
    show ?thesis
    proof (cases "y \<in> ac")
      case True
      have "y = x" by (rule main[OF True xbc eq[symmetric]])
      then show ?thesis by (rule sym)
    next
      case yac: False
      have xD: "x \<in> C.D" and yD: "y \<in> C.D" using xbc ybc by (auto simp: bc_def)
      have nxbc: "C.n x \<in> bc" and nybc: "C.n y \<in> bc" using bc_rcN xD yD xbc ybc by auto
      have neq: "h1 (C.n x) = h1 (C.n y)" using embedN[OF xbc] embedN[OF ybc] eq by simp
      show ?thesis
      proof (cases "C.n x \<in> ac")
        case True
        then have "C.n x = C.n y" using main[OF True nybc neq] by simp
        then show ?thesis using C.N.inj by (simp add: inj_eq)
      next
        case nxac: False
        show ?thesis
        proof (cases "C.n y \<in> ac")
          case True
          then have "C.n y = C.n x" using main[OF True nxbc neq[symmetric]] by simp
          then show ?thesis using C.N.inj by (simp add: inj_eq)
        next
          case nyac: False
          have exac: "C.e x \<in> ac" using embed_cases_bc[OF xbc] xac nxac by blast
          have eyac: "C.e y \<in> ac" using embed_cases_bc[OF ybc] yac nyac by blast
          have eybc: "C.e y \<in> bc" using eyac ac_bc by blast
          have "h1 (C.e x) = h1 (C.e y)" using embedE[OF xD] embedE[OF yD] eq by simp
          then have "C.e x = C.e y" by (rule main[OF exac eybc])
          then show ?thesis using C.E.inj by (simp add: inj_eq)
        qed
      qed
    qed
  qed
qed

end

end
