(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Contract.thy
    Valid contracts in a minimal counterexample admit no contract rings, hence contract
    colourings exist.
    Ported from G. Gonthier's Coq development (contract.v).
*)
theory Contract
  imports Four_Colour_Maps.Cfcontract2 Four_Colour_Maps.Spoke
begin

definition contract_ring :: "'a hypermap \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "contract_ring G cc r \<longleftrightarrow> scycle G (rlink G) r \<and> proper_ring G r \<and> set (tl r) \<subseteq> set (insertE G cc)"

lemma lindex_app: "a \<notin> set l1 \<Longrightarrow> lindex (l1 @ a # t) a = length l1"
  by (induction l1) auto

lemma next_in_mid: "distinct (l1 @ a # b # l2) \<Longrightarrow> next_in (l1 @ a # b # l2) a = b"
  by (simp add: next_in_def lindex_app nth_append)

lemma lindex_snoc: "x \<notin> set l \<Longrightarrow> lindex (l @ [x]) x = length l"
  by (induction l) auto

context birk
begin

lemma revsnip_properI: "scycle G (rlink G) p \<Longrightarrow> set p \<subseteq> D \<Longrightarrow> proper_ring G p \<Longrightarrow> revsnip_proper G p"
  using revsnipI by (simp add: revsnip_proper_def revsnip_proper_axioms_def)

lemma n_neq: "y \<in> D \<Longrightarrow> n y \<noteq> y"
  using no_cface_node by fastforce

lemma contract_ring_diskF:
  assumes sp: "sparse G (insertE G cc)"
  shows "contract_ring G cc p \<Longrightarrow> set p \<subseteq> D \<Longrightarrow> snip_ring.diskF G p \<noteq> {}"
proof (induction "length p" arbitrary: p rule: less_induct)
  case less
  have Up: "scycle G (rlink G) p" and pr: "proper_ring G p" and ccp: "set (tl p) \<subseteq> set (insertE G cc)"
    using less.prems(1) by (simp_all add: contract_ring_def)
  have pD: "set p \<subseteq> D" by (rule less.prems(2))
  interpret S: revsnip_proper G p by (rule revsnip_properI[OF Up pD pr])
  show ?case
  proof
    assume dF0: "S.diskF = {}"
    obtain x x1 p0 where p: "p = x # x1 # p0" using pr by (cases p rule: remdups_adj.cases) auto
    have xp: "x \<in> set p" and xD: "x \<in> D" using p pD by auto
    have notF: "fband G p y" if "y \<in> S.diskN" for y using that dF0 by (auto simp: S.diskF_def)
    have nxN: "n x \<in> S.diskN" using S.diskN_node[OF xD] S.r_diskN[OF xp] by simp
    have nxD: "n x \<in> D" using xD by simp
    have nnxN: "n (n x) \<in> S.diskN" using S.diskN_node[OF nxD] nxN by simp
    have tlp: "set (tl p) = set p - {x}" using S.distinct_r p by auto
    \<comment> \<open>a chord through y cutting off a shorter contract ring is impossible\<close>
    have chordarg: False if yE: "y \<in> S.diskE" and fy: "fband G p y" and fey: "fband G p (edge G y)"
      and sub: "set (tl (chord_ring G p y)) \<subseteq> set (tl p)" and len: "length (chord_ring G p y) < length p" for y
    proof -
      interpret C: chord G p y by unfold_locales (use yE fy fey in auto)
      have "contract_ring G cc (chord_ring G p y)"
        using C.sc1 C.proper_chord_ring sub ccp by (auto simp: contract_ring_def)
      then have "C.C1.diskF \<noteq> {}" using less.hyps[OF len] C.sc1 by blast
      then obtain z where "z \<in> C.C1.diskF" by blast
      then show False using C.diskF_chord_ring dF0 by blast
    qed
    have nx1: "next_in p x = x1" using p S.distinct_r by (simp add: next_in_def)
    \<comment> \<open>the node of x is on the ring\<close>
    have p_nx: "n x \<in> set p"
    proof (rule ccontr)
      assume nnp: "n x \<notin> set p"
      have dEnx: "n x \<in> S.diskE" using nxN nnp by (simp add: S.diskE_def)
      define y where "y = e (n x)"
      have yE: "y \<in> S.diskE" using S.diskE_edge[OF nxD] dEnx by (simp add: y_def)
      have yx: "cface y x" using cface_enK[of x] by (simp add: y_def)
      have fy: "fband G p y" using yx xp by (auto simp: fband_def)
      have fey: "fband G p (e y)" using notF[OF nxN] by (simp add: y_def)
      have py: "fproj G p y = x"
      proof -
        have "fproj G p y \<in> set p" "cface y (fproj G p y)" using fprojP[OF fy] by auto
        then show ?thesis using S.r_cface[OF xp] yx F.fconnect_sym fconnect_trans by metis
      qed
      define j where "j = fproj G p (e y)"
      have jp: "j \<in> set p" and nxj: "cface (n x) j" using fprojP[OF fey] by (simp_all add: j_def y_def)
      have jx: "j \<noteq> x" using nxj no_cface_node[OF xD] by auto
      have jx1: "j \<noteq> x1"
      proof
        assume "j = x1"
        have "rlink G x x1" using cycle_next_in_rel[OF S.cycle_r xp] nx1 by simp
        then have "cface (e x) x1" by (simp add: rlink_def)
        then have a: "cface (e x) (n x)" using nxj \<open>j = x1\<close> F.fconnect_sym fconnect_trans by metis
        have b: "cface (e x) (n (n x))" by (rule cface_edge_nn[OF xD])
        have "cface (n (n x)) (n x)" by (rule fconnect_trans[OF F.fconnect_sym[OF b] a])
        moreover have "cface (e (n (n x))) (n x)" by (rule cface_enK)
        ultimately have "cface (n (n x)) (e (n (n x)))" using F.fconnect_sym fconnect_trans by metis
        then show False using bridgelessG nxD unfolding bridgeless_def by simp
      qed
      obtain i p1 p2 where a1: "arc p j x = j # p1" and rt: "rot i p = j # p1 @ x # p2"
        using rot_to_arc[OF S.distinct_r jp xp jx] by blast
      have cr: "chord_ring G p y = y # j # p1" using a1 py by (simp add: chord_ring_def j_def)
      have dr: "distinct (j # p1 @ x # p2)" using rt S.distinct_r by (metis distinct_rot)
      have sr: "set (j # p1 @ x # p2) = set p" using rt by (metis set_rot)
      have p2ne: "p2 \<noteq> []"
      proof
        assume "p2 = []"
        then have "next_in (rot i p) x = j" using rt dr by (simp add: next_in_def lindex_snoc)
        then show False using next_in_rot[OF S.distinct_r xp, of i] nx1 jx1 by simp
      qed
      have "set (tl (chord_ring G p y)) \<subseteq> set (tl p)" using cr dr sr tlp by auto
      moreover have "length (chord_ring G p y) < length p"
      proof -
        have "length p = length (j # p1 @ x # p2)" using rt by (metis length_rot)
        then show ?thesis using cr p2ne by simp
      qed
      ultimately show False using chordarg[OF yE fy] fey by blast
    qed
    \<comment> \<open>the second node of x is on the ring\<close>
    have nnxD: "n (n x) \<in> D" using xD by simp
    have nxx: "next_in p (n x) = x"
    proof -
      have "rlink G (n x) (next_in p (n x))" by (rule cycle_next_in_rel[OF S.cycle_r p_nx])
      then have "cface (e (n x)) (next_in p (n x))" by (simp add: rlink_def)
      then have "cface x (next_in p (n x))" by (rule fconnect_trans[OF F.fconnect_sym[OF cface_enK]])
      then show ?thesis using S.r_cface[OF xp next_in_mem[OF p_nx]] by simp
    qed
    have p_nnx: "n (n x) \<in> set p"
    proof (rule ccontr)
      assume nnp: "n (n x) \<notin> set p"
      have dEnnx: "n (n x) \<in> S.diskE" using nnxN nnp by (simp add: S.diskE_def)
      define y where "y = e (n (n x))"
      have yE: "y \<in> S.diskE" using S.diskE_edge[OF nnxD] dEnnx by (simp add: y_def)
      have ynx: "cface y (n x)" using cface_enK[of "n x"] by (simp add: y_def)
      have fy: "fband G p y" using ynx p_nx by (auto simp: fband_def)
      have fey: "fband G p (e y)" using notF[OF nnxN] by (simp add: y_def)
      have py: "fproj G p y = n x"
      proof -
        have "fproj G p y \<in> set p" "cface y (fproj G p y)" using fprojP[OF fy] by auto
        then show ?thesis using S.r_cface[OF p_nx] ynx F.fconnect_sym fconnect_trans by metis
      qed
      define j where "j = fproj G p (e y)"
      have jp: "j \<in> set p" and nnxj: "cface (n (n x)) j" using fprojP[OF fey] by (simp_all add: j_def y_def)
      have jnx: "j \<noteq> n x"
      proof
        assume "j = n x"
        then have "cface (n (n x)) (n x)" using nnxj by simp
        moreover have "cface (e (n (n x))) (n x)" by (rule cface_enK)
        ultimately have "cface (n (n x)) (e (n (n x)))" using F.fconnect_sym fconnect_trans by metis
        then show False using bridgelessG nnxD unfolding bridgeless_def by blast
      qed
      have jx: "j \<noteq> x"
      proof
        assume "j = x"
        then have "cface (n (n x)) x" using nnxj by simp
        then have "cface (e x) x" by (rule fconnect_trans[OF cface_edge_nn[OF xD]])
        then show False using bridgelessG xD F.fconnect_sym unfolding bridgeless_def by blast
      qed
      obtain i p1 p2 where a1: "arc p j (n x) = j # p1" and rt: "rot i p = j # p1 @ n x # p2"
        using rot_to_arc[OF S.distinct_r jp p_nx jnx] by blast
      have cr: "chord_ring G p y = y # j # p1" using a1 py by (simp add: chord_ring_def j_def)
      have dr: "distinct (j # p1 @ n x # p2)" using rt S.distinct_r by (metis distinct_rot)
      have sr: "set (j # p1 @ n x # p2) = set p" using rt by (metis set_rot)
      have nrot: "next_in (rot i p) (n x) = x" using next_in_rot[OF S.distinct_r p_nx, of i] nxx by simp
      obtain z p2' where p2: "p2 = z # p2'"
      proof (cases p2)
        case Nil
        then have "next_in (rot i p) (n x) = j" using rt dr by (simp add: next_in_def lindex_snoc)
        then show ?thesis using nrot jx by simp
      qed
      have "z = x"
        using nrot rt dr p2 next_in_mid[of "j # p1" "n x" z p2'] by simp
      then have xp1: "x \<notin> set (j # p1)" using dr p2 by auto
      have "set (tl (chord_ring G p y)) \<subseteq> set (tl p)" using cr sr xp1 tlp by auto
      moreover have "length (chord_ring G p y) < length p"
      proof -
        have "length p = length (j # p1 @ n x # p2)" using rt by (metis length_rot)
        then show ?thesis using cr p2 by simp
      qed
      ultimately show False using chordarg[OF yE fy] fey by blast
    qed
    \<comment> \<open>two node-adjacent contract darts contradict sparseness\<close>
    have nxx': "n x \<noteq> x" by (rule n_neq[OF xD])
    have nnxx: "n (n x) \<noteq> x"
    proof
      assume "n (n x) = x"
      then have "n x = n (n (n x))" by simp
      then show False using nnn[OF xD] nxx' by simp
    qed
    have c1: "n x \<in> set (insertE G cc)" using ccp tlp p_nx nxx' by auto
    have c2: "n (n x) \<in> set (insertE G cc)" using ccp tlp p_nnx nnxx by auto
    have "fconnect n (n x) (n (n x))" by (rule fconnect_step)
    then have "n x = n (n x)" using sp c1 c2 sparse_iff[OF hypermap_axioms] by blast
    then show False using n_neq[OF nxD] by simp
  qed
qed

theorem sparse_contract_ring:
  assumes sp: "sparse G (insertE G cc)" and cr: "contract_ring G cc p" and pD: "set p \<subseteq> D"
  shows "nontrivial_ring G 0 p"
proof -
  have Up: "scycle G (rlink G) p" and pr: "proper_ring G p" and ccp: "set (tl p) \<subseteq> set (insertE G cc)"
    using cr by (simp_all add: contract_ring_def)
  interpret S: revsnip_proper G p by (rule revsnip_properI[OF Up pD pr])
  obtain x p' where p: "p = x # p'" using pr by (cases p) auto
  define q where "q = rot 1 p"
  have q: "q = p' @ [x]" by (simp add: q_def p rot1_Cons)
  have Uq: "scycle G (rlink G) q" and qD: "set q \<subseteq> D" and prq: "proper_ring G q"
    using S.snip_ring_rot[of 1] pr proper_ring_rot[OF plainG] pD
    by (auto simp: q_def snip_ring_def snip_ring_axioms_def)
  interpret Q: revsnip_proper G q by (rule revsnip_properI[OF Uq qD prq])
  have "contract_ring G cc (rev_ring G q)"
    unfolding contract_ring_def
  proof (intro conjI)
    show "scycle G (rlink G) (rev_ring G q)" by (rule Q.scycle_rev_ring)
    show "proper_ring G (rev_ring G q)" using prq proper_rev_ring[OF plainG] by simp
    have "set (tl (rev_ring G q)) = e ` set p'" by (simp add: rev_ring_def q)
    moreover have "e y \<in> set (insertE G cc)" if "y \<in> set p'" for y
    proof -
      have "y \<in> set (insertE G cc)" using that ccp p by auto
      then show ?thesis by (auto simp: set_insertE)
    qed
    ultimately show "set (tl (rev_ring G q)) \<subseteq> set (insertE G cc)" by auto
  qed
  then have "Q.R.diskF \<noteq> {}" using contract_ring_diskF[OF sp] Q.rr_D by blast
  then obtain z where "z \<in> Q.R.diskF" by blast
  then have zFC: "z \<in> D" "z \<notin> Q.diskN" "\<not> fband G q z" using Q.diskF_rev_ring[OF prq] by auto
  have "Q.diskN = S.diskN" using S.rot_disks(1)[of 1] by (simp add: q_def)
  moreover have "fband G q z \<longleftrightarrow> fband G p z" by (simp add: fband_def q_def)
  ultimately have "z \<in> S.diskFC" using zFC by (simp add: S.diskFC_def)
  moreover have "S.diskF \<noteq> {}" using contract_ring_diskF[OF sp cr pD] .
  ultimately show ?thesis using S.nontrivial0P by blast
qed

lemma contract_ring_max:
  assumes cr: "contract_ring G cc p" and pD: "set p \<subseteq> D"
  shows "length p \<le> Suc (length cc)"
proof -
  have Up: "scycle G (rlink G) p" and pr: "proper_ring G p" and ccp: "set (tl p) \<subseteq> set (insertE G cc)"
    using cr by (simp_all add: contract_ring_def)
  interpret S: revsnip_proper G p by (rule revsnip_properI[OF Up pD pr])
  define phi where "phi x = (if x \<in> set cc then x else e x)" for x
  have phic: "phi x \<in> set cc" if "x \<in> set (tl p)" for x
    using ccp that by (auto simp: phi_def set_insertE)
  have tlp: "set (tl p) \<subseteq> set p" by (cases p) auto
  have inj: "inj_on phi (set (tl p))"
  proof (rule inj_onI)
    fix x y assume x: "x \<in> set (tl p)" and y: "y \<in> set (tl p)" and eq: "phi x = phi y"
    have xp: "x \<in> set p" and yp: "y \<in> set p" using x y tlp by auto
    have nb: "e a \<noteq> b" if "a \<in> set p" "b \<in> set p" for a b
    proof
      assume "e a = b"
      then have "e a \<in> S.diskN" using S.r_diskN that(2) by simp
      then show False using S.diskN_edge_ring[OF pr that(1)] by simp
    qed
    show "x = y" using eq nb[OF xp yp] nb[OF yp xp] by (auto simp: phi_def split: if_splits)
  qed
  have dtl: "distinct (tl p)" using S.distinct_r by (cases p) auto
  have "length (tl p) = card (phi ` set (tl p))" using card_image[OF inj] distinct_card[OF dtl] by simp
  also have "\<dots> \<le> card (set cc)" using phic by (intro card_mono) auto
  also have "\<dots> \<le> length cc" by (rule card_length)
  finally show ?thesis by simp
qed

theorem contract3_valid:
  assumes sp: "sparse G (insertE G cc)" and l3: "length cc \<le> 3"
  shows "\<not> (contract_ring G cc p \<and> set p \<subseteq> D)"
proof
  assume "contract_ring G cc p \<and> set p \<subseteq> D"
  then have cr: "contract_ring G cc p" and pD: "set p \<subseteq> D" by auto
  have l4: "length p \<le> 4" using contract_ring_max[OF cr pD] l3 by simp
  have Up: "scycle G (rlink G) p" using cr by (simp add: contract_ring_def)
  have "\<not> nontrivial_ring G (if length p = 5 then 1 else 0) p" by (rule Birkhoff[OF _ Up pD]) (use l4 in simp)
  then show False using sparse_contract_ring[OF sp cr pD] l4 by simp
qed

lemma fcard_two:
  assumes "a \<in> A" "b \<in> A" "\<not> cface a b" "A \<subseteq> D"
  shows "1 < fcard f A"
proof -
  have "cyc f a \<noteq> cyc f b" using assms(3) by (simp add: F.cyc_eq_iff)
  moreover have "finite (cyc f ` A)" using assms(4) finite_subset[OF _ finite_darts] by blast
  ultimately show ?thesis unfolding fcard_def using assms(1,2)
    by (metis One_nat_def card_le_Suc0_iff_eq imageI not_less)
qed

lemma face_closed_cface:
  assumes "\<And>u. u \<in> X \<Longrightarrow> f u \<in> X" "a \<in> X" "cface a b"
  shows "b \<in> X"
  using assms(3) by (induction rule: fconnect_induct) (use assms(1,2) in auto)

theorem triad_valid:
  assumes sp: "sparse G (insertE G cc)" and c4: "length cc = 4" and x0D: "x0 \<in> D"
    and tri: "triad G (insertE G cc) x0"
  shows "\<not> (contract_ring G cc p \<and> set p \<subseteq> D)"
proof
  assume "contract_ring G cc p \<and> set p \<subseteq> D"
  then have cr: "contract_ring G cc p" and pD: "set p \<subseteq> D" by auto
  have Up: "scycle G (rlink G) p" and pr: "proper_ring G p" and ccp: "set (tl p) \<subseteq> set (insertE G cc)"
    using cr by (simp_all add: contract_ring_def)
  interpret S: revsnip_proper G p by (rule revsnip_properI[OF Up pD pr])
  have l5: "length p \<le> 5" using contract_ring_max[OF cr pD] c4 by simp
  have nt0: "nontrivial_ring G 0 p" by (rule sparse_contract_ring[OF sp cr pD])
  have bk: "\<not> nontrivial_ring G (if length p = 5 then 1 else 0) p" by (rule Birkhoff[OF l5 Up pD])
  have p5: "length p = 5" using bk nt0 by (cases "length p = 5") auto
  have triv1: "\<not> nontrivial_ring G 1 p" using bk p5 by simp
  \<comment> \<open>a face all of whose neighbours touch the ring\<close>
  have second: "\<exists>v \<in> X. \<not> cface y v"
    if X: "X = S.diskF \<or> X = S.diskFC" and yX: "y \<in> X" and nz: "adj G y z" "\<not> fband G p z" for X y z
  proof -
    have fX: "\<And>u. u \<in> X \<Longrightarrow> f u \<in> X" using X S.diskF_face S.diskFC_face by blast
    have XD: "X \<subseteq> D" using X S.diskF_D S.diskFC_D by blast
    obtain w where yw: "cface y w" and wz: "cface (e w) z" using nz(1) by (auto simp: adj_iff)
    have wX: "w \<in> X" by (rule face_closed_cface[OF fX yX yw])
    have wD: "w \<in> D" using wX XD by blast
    define v where "v = f (e w)"
    have vz: "cface v z" using wz by (simp add: v_def)
    have nbv: "\<not> fband G p v" using nz(2) fband_cface[OF vz] by simp
    have nv: "n v = w" by (simp add: v_def edgeK)
    have vD: "v \<in> D" using wD by (simp add: v_def)
    have "v \<in> S.diskN \<longleftrightarrow> w \<in> S.diskN" using S.diskN_node[OF vD] nv by simp
    then have "v \<in> X" using X wX nbv vD by (auto simp: S.diskF_def S.diskFC_def)
    moreover have "\<not> cface y v"
    proof
      assume "cface y v"
      then have "cface w (e w)"
        using fconnect_trans[OF F.fconnect_sym[OF yw]] fconnect_step[of f "e w"] F.fconnect_sym
        by (metis v_def fconnect_trans)
      then show False using bridgelessG wD unfolding bridgeless_def by blast
    qed
    ultimately show ?thesis by blast
  qed
  obtain y0 where y0D: "y0 \<in> D" and A: "\<And>z. adj G y0 z \<Longrightarrow> fband G p z"
  proof (rule ccontr)
    assume no: "\<not> thesis"
    then have none: "\<forall>y \<in> D. \<exists>z. adj G y z \<and> \<not> fband G p z" using that by blast
    obtain a where aF: "a \<in> S.diskF" and bFC: "\<exists>b. b \<in> S.diskFC" using nt0 S.nontrivial0P by blast
    obtain b where bFC: "b \<in> S.diskFC" using bFC by blast
    have aD: "a \<in> D" and bD: "b \<in> D" using aF bFC S.diskF_D S.diskFC_D by blast+
    obtain za where "adj G a za" "\<not> fband G p za" using none aD by blast
    then obtain a' where "a' \<in> S.diskF" "\<not> cface a a'" using second[of S.diskF a za] aF by blast
    then have f1: "1 < fcard f S.diskF" using fcard_two aF S.diskF_D by blast
    obtain zb where "adj G b zb" "\<not> fband G p zb" using none bD by blast
    then obtain b' where "b' \<in> S.diskFC" "\<not> cface b b'" using second[of S.diskFC b zb] bFC by blast
    then have f2: "1 < fcard f S.diskFC" using fcard_two bFC S.diskFC_D by blast
    show False using triv1 f1 f2 by (simp add: nontrivial_ring_def)
  qed
  interpret Sy: spoke_ctx G y0 by (rule spoke_ctxI[OF y0D])
  \<comment> \<open>y0 is adjacent to every face of the ring\<close>
  have B: "adj G y0 x" if px: "fband G p x" for x
  proof (rule ccontr)
    assume nx: "\<not> adj G y0 x"
    have xD: "x \<in> D" using px S.fband_D by blast
    have fin: "finite (cyc f ` {u \<in> D. fband G p u})" using finite_darts by simp
    have sub: "cyc f ` {u \<in> D. fband G Sy.sr u} \<subseteq> cyc f ` {u \<in> D. fband G p u}"
      using A Sy.fband_sr by auto
    have xin: "cyc f x \<in> cyc f ` {u \<in> D. fband G p u}" using xD px by blast
    have xout: "cyc f x \<notin> cyc f ` {u \<in> D. fband G Sy.sr u}"
    proof
      assume "cyc f x \<in> cyc f ` {u \<in> D. fband G Sy.sr u}"
      then obtain u where "fband G Sy.sr u" "cyc f x = cyc f u" by blast
      then have "adj G y0 u" "cface x u" using Sy.fband_sr by (auto simp: F.cyc_eq_iff)
      then show False using nx adj_cface_r by blast
    qed
    have "card (cyc f ` {u \<in> D. fband G Sy.sr u}) < card (cyc f ` {u \<in> D. fband G p u})"
      using sub xin xout fin by (intro psubset_card_mono) auto
    then have "fcard f {u \<in> D. fband G Sy.sr u} < fcard f {u \<in> D. fband G p u}" by (simp add: fcard_def)
    moreover have "fcard f {u \<in> D. fband G Sy.sr u} = length Sy.sr"
      using simple_fcard_fband Sy.scycle_sr Sy.sr_subset by (simp add: scycle_def)
    moreover have "fcard f {u \<in> D. fband G p u} = length p"
      using simple_fcard_fband S.simple_r pD by simp
    ultimately show False using Sy.length_sr_gt p5 by simp
  qed
  \<comment> \<open>every contract dart touches the ring\<close>
  have C: "fband G p z" if zc: "z \<in> set (insertE G cc)" for z
  proof (rule ccontr)
    assume nz: "\<not> fband G p z"
    obtain z1 where z1: "z1 \<in> set cc" and zz1: "z = z1 \<or> z = e z1" using zc by (auto simp: set_insertE)
    define cc1 where "cc1 = remove1 z1 cc"
    have l3: "length cc1 = 3" using c4 z1 by (simp add: cc1_def length_remove1)
    have sc: "set cc \<subseteq> insert z1 (set cc1)" using set_remove1_subset[of z1 cc]
      by (auto simp: cc1_def) (metis in_set_remove1)
    have "set (tl p) \<subseteq> set (insertE G cc1)"
    proof
      fix t assume tt: "t \<in> set (tl p)"
      have tp: "t \<in> set p" using tt by (cases p) auto
      have tc: "t \<in> set (insertE G cc)" using ccp tt by blast
      have nt: "t \<noteq> z1 \<and> t \<noteq> e z1"
      proof -
        have tn: "t \<noteq> z" using nz tp fband_ring by blast
        have etn: "e t \<noteq> z"
        proof
          assume "e t = z"
          have "rlink G t (next_in p t)" by (rule cycle_next_in_rel[OF S.cycle_r tp])
          then have "cface z (next_in p t)" using \<open>e t = z\<close> by (simp add: rlink_def)
          then show False using nz next_in_mem[OF tp] by (auto simp: fband_def)
        qed
        show ?thesis using tn etn zz1 by auto
      qed
      then show "t \<in> set (insertE G cc1)" using tc sc by (auto simp: set_insertE)
    qed
    then have "contract_ring G cc1 p" using Up pr by (simp add: contract_ring_def)
    then show False using contract_ring_max[of cc1 p] pD l3 p5 by simp
  qed
  show False
  proof (cases "cface x0 y0")
    case True
    have "\<forall>y \<in> set (insertE G cc). adj G x0 y"
      using C B adj_cface[OF True] by blast
    then show False using tri by (simp add: triad_def)
  next
    case False
    interpret Sx: spoke_ctx G x0 by (rule spoke_ctxI[OF x0D])
    have mx: "fcard f {t. adj G y0 t \<and> adj G x0 t} \<le> 2" by (rule Sx.fcard_adj_max[OF False])
    define L where "L = filter (\<lambda>y. fband G (insertE G cc) (e y)) (orb f x0)"
    have lL: "2 < length L" using tri by (simp add: triad_def L_def)
    have dL: "distinct L" by (simp add: L_def F.distinct_orb)
    have inA: "e y \<in> {t. adj G y0 t \<and> adj G x0 t}" if yL: "y \<in> set L" for y
    proof -
      have xy: "cface x0 y" using yL by (simp add: L_def F.set_orb F.in_cyc_iff)
      have "fband G (insertE G cc) (e y)" using yL by (simp add: L_def)
      then obtain w where "w \<in> set (insertE G cc)" "cface (e y) w" by (auto simp: fband_def)
      then have "fband G p (e y)" using C fband_cface by blast
      then have "adj G y0 (e y)" by (rule B)
      moreover have "adj G x0 (e y)" using xy by (auto simp: adj_iff)
      ultimately show ?thesis by simp
    qed
    have inj: "inj_on (\<lambda>y. cyc f (e y)) (set L)"
    proof (rule inj_onI)
      fix y1 y2 assume y1: "y1 \<in> set L" and y2: "y2 \<in> set L" and eq: "cyc f (e y1) = cyc f (e y2)"
      have c1: "cface x0 y1" and c2: "cface x0 y2" using y1 y2 by (simp_all add: L_def F.set_orb F.in_cyc_iff)
      have yD: "y1 \<in> D" "y2 \<in> D" using c1 c2 x0D F.fconnect_in_D by blast+
      have "cface y1 y2" by (rule fconnect_trans[OF F.fconnect_sym[OF c1] c2])
      moreover have "cface (e y1) (e y2)" using eq by (simp add: F.cyc_eq_iff)
      ultimately show "y1 = y2" by (rule double_dart[OF yD])
    qed
    have fin: "finite (cyc f ` {t. adj G y0 t \<and> adj G x0 t})"
    proof -
      have "{t. adj G y0 t \<and> adj G x0 t} \<subseteq> D"
      proof
        fix t assume "t \<in> {t. adj G y0 t \<and> adj G x0 t}"
        then obtain w where "cface x0 w" "cface (e w) t" by (auto simp: adj_iff)
        then show "t \<in> D" using x0D F.fconnect_in_D by (metis E.closed)
      qed
      then show ?thesis using finite_subset[OF _ finite_darts] by blast
    qed
    have "length L = card ((\<lambda>y. cyc f (e y)) ` set L)" using card_image[OF inj] distinct_card[OF dL] by simp
    also have "\<dots> \<le> card (cyc f ` {t. adj G y0 t \<and> adj G x0 t})" using inA fin by (intro card_mono) auto
    finally show False using mx lL by (simp add: fcard_def)
  qed
qed

end

end
