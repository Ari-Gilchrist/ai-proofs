(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Cfmap_prog.thy
    Configuration maps, part 4: running construction programs (cpmap), ring size,
    and the geometric invariants of cubic programs.
    Ported from G. Gonthier's Coq development (cfmap.v).
*)
theory Cfmap_prog
  imports Four_Colour_Maps.Cfmap_ext Four_Colour_Maps.Cfmap_ka
begin

section \<open>The base map\<close>

definition sw01 :: "nat \<Rightarrow> nat" where
  "sw01 x = (if x = 0 then 1 else if x = 1 then 0 else x)"

definition cpmap0 :: "nat hypermap" where
  "cpmap0 = \<lparr>darts = {0, 1}, edge = sw01, node = sw01, face = id\<rparr>"

lemma sw01_sw01 [simp]: "sw01 (sw01 x) = x" by (simp add: sw01_def)

lemma hypermap_cpmap0: "hypermap cpmap0"
  unfolding cpmap0_def
  by (rule hypermap_cancel3) (auto simp: sw01_def)

lemma cpmap0_simps [simp]:
  "darts cpmap0 = {0, 1}" "edge cpmap0 = sw01" "node cpmap0 = sw01" "face cpmap0 = id"
  by (simp_all add: cpmap0_def)

lemma cpring0: "cpring cpmap0 1 = [0, 1]"
proof (rule hypermap.cpring_def_char[OF hypermap_cpmap0])
  show "[0, 1] = node cpmap0 1 # [1]" by (simp add: sw01_def)
qed (simp_all add: cycle_Cons sw01_def)

section \<open>Running a program\<close>

fun cpmap :: "cprog \<Rightarrow> nat hypermap \<times> nat" where
  "cpmap [] = (cpmap0, 1)"
| "cpmap (CpR k # cp) = (case cpmap cp of (G, x) \<Rightarrow> (G, (node G ^^ (order (node G) x - k)) x))"
| "cpmap (CpR' # cp) = (case cpmap cp of (G, x) \<Rightarrow> (G, node G x))"
| "cpmap (CpU # cp) = (case cpmap cp of (G, x) \<Rightarrow> (ecpU G x, ecpX G))"
| "cpmap (CpY # cp) = (case cpmap cp of (G, x) \<Rightarrow> (ecpN (ecpU G x) (ecpX G), ecpX (ecpU G x)))"
| "cpmap (CpH # cp) = (case cpmap cp of (G, x) \<Rightarrow>
     (ecpN (ecpN (ecpU G x) (ecpX G)) (ecpX (ecpU G x)), ecpX (ecpN (ecpU G x) (ecpX G))))"
| "cpmap (CpK # cp) = (case cpmap cp of (G, x) \<Rightarrow>
     (ecpN G (node G x), face (ecpN G (node G x)) (edge (ecpN G (node G x)) (ecpX G))))"
| "cpmap (CpA # cp) = (case cpmap cp of (G, x) \<Rightarrow> (ecpA G x, ecpA_ptr G x))"

abbreviation cpG where "cpG cp \<equiv> fst (cpmap cp)"
abbreviation cpx where "cpx cp \<equiv> snd (cpmap cp)"

definition cfmap :: "config \<Rightarrow> nat hypermap \<times> nat" where
  "cfmap cf = cpmap (cfprog cf)"

definition cpring_of :: "cprog \<Rightarrow> nat list" where
  "cpring_of cp = cpring (cpG cp) (cpx cp)"

definition cfring :: "config \<Rightarrow> nat list" where
  "cfring cf = rev (cpring_of (cfprog cf))"

lemma ecp_intro: "hypermap G \<Longrightarrow> x \<in> darts G \<Longrightarrow> ecp G x"
  by (simp add: ecp_def ecp_axioms_def)

lemma ecp2_intro: "hypermap G \<Longrightarrow> x \<in> darts G \<Longrightarrow> ecp2 G x"
  by (simp add: ecp2_def ecp_intro)

lemma ecp2h_intro: "hypermap G \<Longrightarrow> x \<in> darts G \<Longrightarrow> ecp2h G x"
  by (simp add: ecp2h_def ecp2_intro)

lemma ecp3_intro: "hypermap G \<Longrightarrow> x \<in> darts G \<Longrightarrow> proper_cpring G x \<Longrightarrow> ecp3 G x"
  by (simp add: ecp3_def ecp3_axioms_def ecp2h_intro)

lemma ecpk_intro: "hypermap G \<Longrightarrow> x \<in> darts G \<Longrightarrow> ecpk G x"
  by (simp add: ecpk_def ecp_intro)

lemma ecpa_intro: "hypermap G \<Longrightarrow> x \<in> darts G \<Longrightarrow> ecpa G x"
  by (simp add: ecpa_def ecpa_axioms_def)

lemma cpmap_inv: "hypermap (cpG cp) \<and> cpx cp \<in> darts (cpG cp)"
proof (induction cp rule: cpmap.induct)
  case 1
  then show ?case by (simp add: hypermap_cpmap0)
next
  case (2 k cp)
  obtain G x where c: "cpmap cp = (G, x)" by (cases "cpmap cp")
  interpret E: ecp G x using 2 c by (intro ecp_intro) simp_all
  show ?case using c E.hypermap_axioms E.x0D by simp
next
  case (3 cp)
  obtain G x where c: "cpmap cp = (G, x)" by (cases "cpmap cp")
  interpret E: ecp G x using 3 c by (intro ecp_intro) simp_all
  show ?case using c E.hypermap_axioms E.x0D by simp
next
  case (4 cp)
  obtain G x where c: "cpmap cp = (G, x)" by (cases "cpmap cp")
  interpret E: ecp G x using 4 c by (intro ecp_intro) simp_all
  show ?case using c E.hypermap_GU E.GU_simps(1) unfolding E.GU_def by simp
next
  case (5 cp)
  obtain G x where c: "cpmap cp = (G, x)" by (cases "cpmap cp")
  interpret E: ecp2 G x using 5 c by (intro ecp2_intro) simp_all
  show ?case using c E.T.hypermap_GN[unfolded E.T.GN_def, unfolded E.GU_def]
      E.T.GN_simps(1)[unfolded E.T.GN_def, unfolded E.GU_def] by simp
next
  case (6 cp)
  obtain G x where c: "cpmap cp = (G, x)" by (cases "cpmap cp")
  interpret E: ecp2 G x using 6 c by (intro ecp2_intro) simp_all
  interpret H: ecp E.GY E.XY using E.T.hypermap_GN by (intro ecp_intro) simp_all
  show ?case using c H.hypermap_GN[unfolded H.GN_def, unfolded E.T.GN_def, unfolded E.GU_def]
      H.GN_simps(1)[unfolded H.GN_def, unfolded E.T.GN_def, unfolded E.GU_def] by simp
next
  case (7 cp)
  obtain G x where c: "cpmap cp = (G, x)" by (cases "cpmap cp")
  interpret E: ecpk G x using 7 c by (intro ecpk_intro) simp_all
  have "cpx (CpK # cp) = E.pK"
    using c E.K.NN.ecpR1_eq by (simp add: E.pK_def E.K.GN_def)
  then show ?case using c E.K.hypermap_GN E.pK_in by (simp add: E.K.GN_def)
next
  case (8 cp)
  obtain G x where c: "cpmap cp = (G, x)" by (cases "cpmap cp")
  interpret E: ecpa G x using 8 c by (intro ecpa_intro) simp_all
  show ?case using c E.hypermap_GA E.pA_in E.pA_eq by (simp add: E.GA_def ecpA_def)
qed

lemma hypermap_cpmap: "hypermap (cpG cp)" using cpmap_inv by blast
lemma cpx_in: "cpx cp \<in> darts (cpG cp)" using cpmap_inv by blast

section \<open>Explicit forms of the step maps\<close>

context ecp
begin
lemma GU_eq: "GU = ecpU G x0" by (rule GU_def)
end

context ecp2
begin
lemma GY_eq: "GY = ecpN (ecpU G x0) (ecpX G)"
  unfolding T.GN_def unfolding GU_def ..
lemma XY_eq: "XY = ecpX (ecpU G x0)"
  unfolding GU_def ..
end

context ecp2h
begin
lemma GH_eq: "GH = ecpN (ecpN (ecpU G x0) (ecpX G)) (ecpX (ecpU G x0))"
  unfolding T2.GN_def unfolding GY_eq XY_eq ..
lemma XH_eq: "XH = ecpX (ecpN (ecpU G x0) (ecpX G))"
  unfolding GY_eq ..
end

context ecpk
begin
lemma GK_eq: "GK = ecpN G (n x0)" by (rule K.GN_def)
lemma pK_eq': "pK = face (ecpN G (n x0)) (edge (ecpN G (n x0)) X)"
  using K.NN.ecpR1_eq[of X] unfolding pK_def K.GN_def .
end

context ecpa
begin
lemma GA_eq: "GA = ecpA G x0" by (rule GA_def)
end

lemma cpmap_Cons_cases:
  assumes c: "cpmap cp = (G, x)"
  shows "cpmap (CpR k # cp) = (G, hypermap.ecpR_ptr G k x)"
    and "cpmap (CpR' # cp) = (G, node G x)"
    and "ecp G x \<Longrightarrow> cpmap (CpU # cp) = (ecp.GU G x, ecpX G)"
    and "ecp2 G x \<Longrightarrow> cpmap (CpY # cp) = (ecp.GN (ecp.GU G x) (ecpX G), ecpX (ecp.GU G x))"
    and "ecpk G x \<Longrightarrow> cpmap (CpK # cp) = (ecp.GN G (node G x), ecpk.pK G x)"
    and "ecpa G x \<Longrightarrow> cpmap (CpA # cp) = (ecpa.GA G x, ecpa.pA G x)"
proof -
  have hG: "hypermap G" using hypermap_cpmap[of cp] c by simp
  show "cpmap (CpR k # cp) = (G, hypermap.ecpR_ptr G k x)"
    using c by (simp add: hypermap.ecpR_ptr_def[OF hG])
  show "cpmap (CpR' # cp) = (G, node G x)" using c by simp
  show "ecp G x \<Longrightarrow> cpmap (CpU # cp) = (ecp.GU G x, ecpX G)"
    using c by (simp add: ecp.GU_eq)
  show "ecp2 G x \<Longrightarrow> cpmap (CpY # cp) = (ecp.GN (ecp.GU G x) (ecpX G), ecpX (ecp.GU G x))"
    using c by (simp add: ecp2.GY_eq ecp2.XY_eq)
  show "ecpk G x \<Longrightarrow> cpmap (CpK # cp) = (ecp.GN G (node G x), ecpk.pK G x)"
    using c by (simp add: ecpk.GK_eq ecpk.pK_eq')
  show "ecpa G x \<Longrightarrow> cpmap (CpA # cp) = (ecpa.GA G x, ecpa.pA G x)"
    using c by (simp add: ecpa.GA_eq ecpa.pA_eq)
qed

lemma cpmap_H:
  assumes c: "cpmap cp = (G, x)" and E: "ecp2h G x"
  shows "cpmap (CpH # cp) = (ecp.GN (ecp.GN (ecp.GU G x) (ecpX G)) (ecpX (ecp.GU G x)),
                             ecpX (ecp.GN (ecp.GU G x) (ecpX G)))"
  using c E by (simp add: ecp2h.GH_eq ecp2h.XH_eq)

section \<open>Ring size\<close>

definition sub2ifgt2 :: "nat \<Rightarrow> nat" where
  "sub2ifgt2 m = (if 2 < m then m - 2 else m)"

fun cprsize :: "cprog \<Rightarrow> nat" where
  "cprsize [] = 2"
| "cprsize (CpY # cp) = Suc (cprsize cp)"
| "cprsize (CpU # cp) = Suc (Suc (cprsize cp))"
| "cprsize (CpK # cp) = Suc (cprsize cp - 2)"
| "cprsize (CpA # cp) = sub2ifgt2 (cprsize cp)"
| "cprsize (_ # cp) = cprsize cp"

lemma size_ring_cpmap: "length (cpring_of cp) = cprsize cp"
proof (induction cp)
  case Nil
  then show ?case using cpring0 by (simp add: cpring_of_def)
next
  case (Cons s cp)
  obtain G x where c: "cpmap cp = (G, x)" by (cases "cpmap cp")
  interpret E: ecp G x using hypermap_cpmap[of cp] cpx_in[of cp] c by (intro ecp_intro) simp_all
  have IH: "length (cpring G x) = cprsize cp" using Cons c by (simp add: cpring_of_def)
  show ?case
  proof (cases s)
    case (CpR k)
    then show ?thesis using IH cpmap_Cons_cases(1)[OF c] E.length_cpring_ecpR by (simp add: cpring_of_def)
  next
    case CpR'
    have "node G x = E.ecpR_ptr (order (node G) x - 1) x" using E.ecpR'_eq[of x] by simp
    then show ?thesis using IH CpR' cpmap_Cons_cases(2)[OF c] E.length_cpring_ecpR[of "order (node G) x - 1" x]
      by (simp add: cpring_of_def)
  next
    case CpU
    then show ?thesis using IH cpmap_Cons_cases(3)[OF c E.ecp_axioms] E.length_cpring_GU
      by (simp add: cpring_of_def)
  next
    case CpY
    interpret E2: ecp2 G x by (simp add: ecp2_def E.ecp_axioms)
    show ?thesis using IH CpY cpmap_Cons_cases(4)[OF c E2.ecp2_axioms] E2.length_cpring_GY
      by (simp add: cpring_of_def)
  next
    case CpH
    interpret E2: ecp2 G x by (simp add: ecp2_def E.ecp_axioms)
    interpret H: ecp E2.GY E2.XY using E2.T.hypermap_GN by (intro ecp_intro) simp_all
    have pr: "proper_cpring E2.GY E2.XY"
      using E2.length_cpring_GY E.cpring_ne[of x] E2.T.NN.size_proper_cpring[of E2.XY]
      by (cases "cpring G x") simp_all
    have hg: "H.GN = ecpN (ecpN (ecpU G x) (ecpX G)) (ecpX (ecpU G x))"
      unfolding H.GN_def unfolding E2.GY_eq E2.XY_eq ..
    have hx: "H.X = ecpX (ecpN (ecpU G x) (ecpX G))" unfolding E2.GY_eq ..
    have m: "cpmap (CpH # cp) = (H.GN, H.X)"
      using c by (simp only: hg hx cpmap.simps prod.case)
    show ?thesis using IH CpH m H.length_cpring_GN[OF pr] E2.length_cpring_GY
      by (simp add: cpring_of_def)
  next
    case CpK
    interpret K: ecpk G x by (simp add: ecpk_def E.ecp_axioms)
    show ?thesis using IH CpK cpmap_Cons_cases(5)[OF c K.ecpk_axioms] K.cpring_GK
      by (simp add: cpring_of_def)
  next
    case CpA
    interpret A: ecpa G x using E.hypermap_axioms E.x0D by (intro ecpa_intro)
    show ?thesis using IH CpA cpmap_Cons_cases(6)[OF c A.ecpa_axioms] A.cpring_GA E.size_long_cpring[of x]
      by (simp add: cpring_of_def sub2ifgt2_def)
  qed
qed

section \<open>Geometry of cubic programs\<close>

definition geo :: "nat hypermap \<Rightarrow> nat \<Rightarrow> bool" where
  "geo G x \<longleftrightarrow> proper_cpring G x \<and> plain G \<and> quasicubic G (rev (cpring G x)) \<and>
               connected G \<and> bridgeless G \<and> planar G"

lemma geo_cpmap0: "geo cpmap0 1"
proof -
  interpret M: hypermap cpmap0 by (rule hypermap_cpmap0)
  have pr: "proper_cpring cpmap0 1" by (simp add: proper_cpring_def sw01_def)
  have pl: "plain cpmap0" unfolding plain_def M.plainP by (auto simp: sw01_def)
  have q: "quasicubic cpmap0 (rev (cpring cpmap0 1))"
    using cpring0 by (simp add: quasicubic_def cubicb_def)
  have cf: "fconnect id x y \<longleftrightarrow> y = x" for x y
    by (auto simp: fconnect_def)
  have cc: "connected cpmap0"
  proof (rule M.connectedI[of 1])
    show "1 \<in> darts cpmap0" by simp
    fix y assume "y \<in> darts cpmap0"
    then have "y = 0 \<or> y = 1" by auto
    moreover have "glink cpmap0 1 0" by (simp add: glink_def sw01_def)
    ultimately show "gcomp cpmap0 1 y" by blast
  qed
  have br: "bridgeless cpmap0" by (auto simp: bridgeless_def cf sw01_def)
  have geo0: "ucycle_plain_quasicubic_connected cpmap0 (rev (cpring cpmap0 1))"
    using hypermap_cpmap0 pl q cc M.ucycle_rev_cpring[of 1] M.ringD_gen[of 1]
    by (simp add: ucycle_plain_quasicubic_connected_def ucycle_plain_quasicubic_def plain_quasicubic_def)
  have fc: "fcard id {0::nat, 1} = 2"
  proof -
    have "cyc id x = {x}" for x :: nat by (auto simp: cyc_def fconnect_def)
    then show ?thesis by (simp add: fcard_def)
  qed
  have pl2: "planar cpmap0" using M.quasicubic_Euler[OF geo0] cpring0 fc by simp
  show ?thesis using pr pl q cc br pl2 by (simp add: geo_def)
qed

lemma geo_cpmap: "cubic_prog cp \<Longrightarrow> geo (cpG cp) (cpx cp)"
proof (induction cp)
  case Nil
  then show ?case using geo_cpmap0 by simp
next
  case (Cons s cp)
  obtain G x where c: "cpmap cp = (G, x)" by (cases "cpmap cp")
  interpret E: ecp G x using hypermap_cpmap[of cp] cpx_in[of cp] c by (intro ecp_intro) simp_all
  have cpq: "cubic_prog cp" using Cons.prems by (cases s) simp_all
  have g: "geo G x" using Cons.IH[OF cpq] c by simp
  then have pr: "proper_cpring G x" and pl: "plain G" and q: "quasicubic G (rev (cpring G x))"
    and cc: "connected G" and br: "bridgeless G" and pn: "planar G" by (simp_all add: geo_def)
  show ?case
  proof (cases s)
    case (CpR k)
    have "proper_cpring G (E.ecpR_ptr k x)" using pr E.size_proper_cpring E.length_cpring_ecpR by simp
    moreover have "quasicubic G (rev (cpring G (E.ecpR_ptr k x)))"
      using q by (simp add: E.cpring_ecpR quasicubic_def)
    ultimately show ?thesis using CpR cpmap_Cons_cases(1)[OF c] g by (simp add: geo_def)
  next
    case CpR'
    then show ?thesis using Cons.prems by simp
  next
    case CpU
    have "proper_cpring E.GU E.X"
      using E.U.size_proper_cpring E.length_cpring_GU by simp
    then have "geo E.GU E.X"
      using E.plain_GU[OF pl] E.quasicubic_GU[OF q] E.connected_GU[OF cc] E.bridgeless_GU[OF br]
        E.planar_GU[OF pn pl q cc] by (simp add: geo_def)
    then show ?thesis using CpU cpmap_Cons_cases(3)[OF c E.ecp_axioms] by simp
  next
    case CpY
    interpret E2: ecp2 G x by (simp add: ecp2_def E.ecp_axioms)
    have "proper_cpring E2.GY E2.XY"
      using E2.T.NN.size_proper_cpring E2.length_cpring_GY E.cpring_ne[of x]
      by (cases "cpring G x") simp_all
    then have "geo E2.GY E2.XY"
      using E2.plain_GY[OF pl] E2.quasicubic_GY[OF q] E2.connected_GY[OF cc] E2.bridgeless_GY[OF br]
        E2.planar_GY[OF pn pl q cc] by (simp add: geo_def)
    then show ?thesis using CpY cpmap_Cons_cases(4)[OF c E2.ecp2_axioms] by simp
  next
    case CpH
    interpret E3: ecp3 G x using E.hypermap_axioms E.x0D pr by (intro ecp3_intro)
    have "proper_cpring E3.GH E3.XH"
      using E3.T2.NN.size_proper_cpring E3.length_cpring_GH pr E.size_proper_cpring by simp
    then have "geo E3.GH E3.XH"
      using E3.plain_GH[OF pl] E3.quasicubic_GH[OF q] E3.connected_GH[OF cc] E3.bridgeless_GH[OF br]
        E3.planar_GH[OF pn pl q cc] by (simp add: geo_def)
    then show ?thesis using CpH cpmap_H[OF c E3.ecp2h_axioms] by simp
  next
    case CpK
    then show ?thesis using Cons.prems by simp
  next
    case CpA
    then show ?thesis using Cons.prems by simp
  qed
qed

lemma cpmap_proper: "cubic_prog cp \<Longrightarrow> proper_cpring (cpG cp) (cpx cp)"
  using geo_cpmap by (simp add: geo_def)
lemma cpmap_plain: "cubic_prog cp \<Longrightarrow> plain (cpG cp)"
  using geo_cpmap by (simp add: geo_def)
lemma cpmap_cubic: "cubic_prog cp \<Longrightarrow> quasicubic (cpG cp) (rev (cpring_of cp))"
  using geo_cpmap by (simp add: geo_def cpring_of_def)
lemma cpmap_connected: "cubic_prog cp \<Longrightarrow> connected (cpG cp)"
  using geo_cpmap by (simp add: geo_def)
lemma cpmap_bridgeless: "cubic_prog cp \<Longrightarrow> bridgeless (cpG cp)"
  using geo_cpmap by (simp add: geo_def)
lemma cpmap_planar: "cubic_prog cp \<Longrightarrow> planar (cpG cp)"
  using geo_cpmap by (simp add: geo_def)

lemma config_prog_size: "config_prog cp \<Longrightarrow> 2 < cprsize cp"
proof (induction cp rule: config_prog.induct)
  case (3 v va)
  then show ?case by simp
qed simp_all

lemma cfmap_long: "config_prog cp \<Longrightarrow> long_cpring (cpG cp) (cpx cp)"
  using hypermap.size_long_cpring[OF hypermap_cpmap] size_ring_cpmap config_prog_size
  by (simp add: cpring_of_def)

section \<open>One-step monotonicity (the injections are identities)\<close>

context ecpa
begin

lemma sub_cface_GA: "x \<in> D \<Longrightarrow> y \<in> D \<Longrightarrow> cface x y \<Longrightarrow> fconnect (face GA) x y"
  using cface_GA by blast

lemma sub_adj_GA:
  assumes x: "x \<in> D" and y: "y \<in> D" and a: "adj G x y"
  shows "adj GA x y"
proof -
  obtain z where z: "cface x z" "cface (e z) y" using a unfolding adj_def rlink_def by blast
  have zD: "z \<in> D" using F.fconnect_in_D[OF z(1)] x by simp
  have xz: "fconnect (face GA) x z" using sub_cface_GA[OF x zD z(1)] .
  have "fconnect (face GA) (edge GA z) y"
  proof (cases cc)
    case False
    then show ?thesis using sub_cface_GA[of "e z" y] z(2) zD y by simp
  next
    case True
    have fa: "face GA = f" using True by (simp add: fun_eq_iff)
    have c1: "cface (e (n (n x0))) (n x0)"
      using fconnect_step[of f "e (n (n x0))"] by (simp add: nodeK)
    have c2: "cface (n x0) (e x0)" using True F.fconnect_sym by blast
    show ?thesis
    proof (cases "z = x0")
      case True
      have "cface (e (n (n x0))) y"
        by (rule fconnect_trans[OF c1 fconnect_trans[OF c2]]) (use z(2) True in simp)
      then show ?thesis using True \<open>cc\<close> fa by simp
    next
      case nx: False
      show ?thesis
      proof (cases "z = n (n x0)")
        case True
        have "cface (e x0) y"
          by (rule fconnect_trans[OF F.fconnect_sym[OF fconnect_trans[OF c1 c2]]]) (use z(2) True in simp)
        then show ?thesis using True nx \<open>cc\<close> fa by simp
      next
        case False
        then show ?thesis using nx \<open>cc\<close> fa z(2) by simp
      qed
    qed
  qed
  then show ?thesis using xz unfolding adj_def rlink_def by blast
qed

end

lemma in_set_tl_D: "x \<in> set (tl l) \<Longrightarrow> x \<in> set l"
  by (cases l) simp_all

lemma ring_props:
  assumes "hypermap G" "x \<in> darts G"
  shows "node G x \<in> set (cpring G x)" "x \<in> set (cpring G x)" "face G (edge G x) \<in> set (cpring G x)"
proof -
  interpret hypermap G by fact
  show "node G x \<in> set (cpring G x)" "x \<in> set (cpring G x)"
    by (simp_all add: mem_cpring)
  have "face G (edge G x) = inv (node G) x" by (simp add: inv_node_apply)
  then show "face G (edge G x) \<in> set (cpring G x)" by (simp add: mem_cpring)
qed

lemma step_mono:
  assumes x: "x \<in> darts (cpG cp)" and y: "y \<in> darts (cpG cp)"
  shows "darts (cpG cp) \<subseteq> darts (cpG (s # cp))"
    and "fconnect (face (cpG cp)) x y \<Longrightarrow> fconnect (face (cpG (s # cp))) x y"
    and "adj (cpG cp) x y \<Longrightarrow> adj (cpG (s # cp)) x y"
proof -
  obtain G x0 where c: "cpmap cp = (G, x0)" by (cases "cpmap cp")
  interpret E: ecp G x0 using hypermap_cpmap[of cp] cpx_in[of cp] c by (intro ecp_intro) simp_all
  have xD: "x \<in> darts G" and yD: "y \<in> darts G" using x y c by simp_all
  have "darts G \<subseteq> darts (cpG (s # cp)) \<and>
        (fconnect (face G) x y \<longrightarrow> fconnect (face (cpG (s # cp))) x y) \<and>
        (adj G x y \<longrightarrow> adj (cpG (s # cp)) x y)"
  proof (cases s)
    case (CpR k) then show ?thesis using cpmap_Cons_cases(1)[OF c] by simp
  next
    case CpR' then show ?thesis using cpmap_Cons_cases(2)[OF c] by simp
  next
    case CpU
    then show ?thesis using cpmap_Cons_cases(3)[OF c E.ecp_axioms] E.cface_GU_old[OF xD yD]
        E.adj_GU_old[OF xD yD] by auto
  next
    case CpY
    interpret E2: ecp2 G x0 by (simp add: ecp2_def E.ecp_axioms)
    show ?thesis using CpY cpmap_Cons_cases(4)[OF c E2.ecp2_axioms] E2.cface_GY_old[OF xD yD]
        E2.adj_GY_old[OF xD yD] E2.darts_GY by auto
  next
    case CpH
    interpret E2: ecp2h G x0 by (simp add: ecp2h_def ecp2_def E.ecp_axioms)
    show ?thesis using CpH cpmap_H[OF c E2.ecp2h_axioms] E2.cface_GH_old[OF xD yD]
        E2.adj_GH_old[OF xD yD] E2.darts_GH by auto
  next
    case CpK
    interpret K: ecpk G x0 by (simp add: ecpk_def E.ecp_axioms)
    show ?thesis using CpK cpmap_Cons_cases(5)[OF c K.ecpk_axioms] K.cface_GK_old[OF xD yD]
        K.adj_GK_old[OF xD yD] by auto
  next
    case CpA
    interpret A: ecpa G x0 using E.hypermap_axioms E.x0D by (intro ecpa_intro)
    show ?thesis using CpA cpmap_Cons_cases(6)[OF c A.ecpa_axioms] A.sub_cface_GA[OF xD yD]
        A.sub_adj_GA[OF xD yD] by (simp add: A.GA_def ecpA_def)
  qed
  then show "darts (cpG cp) \<subseteq> darts (cpG (s # cp))"
    and "fconnect (face (cpG cp)) x y \<Longrightarrow> fconnect (face (cpG (s # cp))) x y"
    and "adj (cpG cp) x y \<Longrightarrow> adj (cpG (s # cp)) x y" using c by auto
qed

lemma cubic_step:
  assumes cs: "cubic_prog [s]" and x: "x \<in> darts (cpG cp)" and y: "y \<in> darts (cpG cp)"
  shows "fconnect (face (cpG (s # cp))) x y \<longleftrightarrow> fconnect (face (cpG cp)) x y"
    and "adj (cpG (s # cp)) x y \<longleftrightarrow> adj (cpG cp) x y"
    and "edge (cpG (s # cp)) x = edge (cpG cp) x"
    and "x \<notin> set (cpring_of cp) \<Longrightarrow> node (cpG (s # cp)) x = node (cpG cp) x \<and> x \<notin> set (cpring_of (s # cp))"
proof -
  obtain G x0 where c: "cpmap cp = (G, x0)" by (cases "cpmap cp")
  interpret E: ecp G x0 using hypermap_cpmap[of cp] cpx_in[of cp] c by (intro ecp_intro) simp_all
  have xD: "x \<in> darts G" and yD: "y \<in> darts G" using x y c by simp_all
  have rp: "E.n x0 \<in> set (cpring G x0)" "x0 \<in> set (cpring G x0)" "E.f (E.e x0) \<in> set (cpring G x0)"
    using ring_props[OF E.hypermap_axioms E.x0D] by simp_all
  have "(fconnect (face (cpG (s # cp))) x y \<longleftrightarrow> fconnect (face G) x y) \<and>
        (adj (cpG (s # cp)) x y \<longleftrightarrow> adj G x y) \<and> edge (cpG (s # cp)) x = edge G x \<and>
        (x \<notin> set (cpring G x0) \<longrightarrow> node (cpG (s # cp)) x = node G x \<and>
            x \<notin> set (cpring (cpG (s # cp)) (cpx (s # cp))))"
  proof (cases s)
    case (CpR k)
    then show ?thesis using cpmap_Cons_cases(1)[OF c] by (simp add: E.cpring_ecpR)
  next
    case CpR' then show ?thesis using cs by simp
  next
    case CpU
    show ?thesis using CpU cpmap_Cons_cases(3)[OF c E.ecp_axioms] E.cface_GU_old[OF xD yD]
        E.adj_GU_old[OF xD yD] xD rp E.cpring_GU by auto
  next
    case CpY
    interpret E2: ecp2 G x0 by (simp add: ecp2_def E.ecp_axioms)
    have "x \<notin> set (cpring G x0) \<Longrightarrow> node E2.GY x = E.n x"
      using rp xD by (intro E2.node_GY_old) auto
    moreover have "x \<notin> set (cpring G x0) \<Longrightarrow> x \<notin> set (cpring E2.GY E2.XY)"
      using E2.cpring_GY xD by (auto dest: in_set_tl_D)
    ultimately show ?thesis using CpY cpmap_Cons_cases(4)[OF c E2.ecp2_axioms] E2.cface_GY_old[OF xD yD]
        E2.adj_GY_old[OF xD yD] xD by auto
  next
    case CpH
    interpret E2: ecp2h G x0 by (simp add: ecp2h_def ecp2_def E.ecp_axioms)
    have "x \<notin> set (cpring G x0) \<Longrightarrow> node E2.GH x = E.n x"
      using rp xD by (intro E2.node_GH_old) auto
    moreover have "x \<notin> set (cpring G x0) \<Longrightarrow> x \<notin> set (cpring E2.GH E2.XH)"
    proof -
      assume nx: "x \<notin> set (cpring G x0)"
      have r: "cpring E2.GY E2.XY = E.Xe # E2.XY # tl (cpring G x0)" by (rule E2.cpring_GY)
      have "x \<notin> set (cpring E2.GY E2.XY)" using r nx xD by (auto dest: in_set_tl_D)
      moreover have "set (cpring E2.GH E2.XH) \<subseteq> set (cpring E2.GY E2.XY) \<union> {E2.XH}"
      proof (cases "long_cpring E2.GY E2.XY")
        case True
        have "cpring E2.GH E2.XH = node E2.GY E2.XY # E2.XH # drop 3 (cpring E2.GY E2.XY)"
          by (rule E2.T2.cpring_GN_long[OF True])
        moreover have "node E2.GY E2.XY \<in> set (cpring E2.GY E2.XY)"
          by (rule ring_props(1)[OF E2.T.hypermap_GN E2.XY_in])
        ultimately show ?thesis by (auto dest: in_set_dropD)
      next
        case False
        then show ?thesis using E2.T2.cpring_GN_short by simp
      qed
      ultimately show ?thesis using xD E2.D_neq_XH(1)[OF xD] by blast
    qed
    moreover have "edge E2.GH x = E.e x" using xD by simp
    moreover have "cpmap (s # cp) = (E2.GH, E2.XH)" using CpH cpmap_H[OF c E2.ecp2h_axioms] by simp
    ultimately show ?thesis using E2.cface_GH_old[OF xD yD] E2.adj_GH_old[OF xD yD]
      by (simp only: prod.sel) blast
  next
    case CpK then show ?thesis using cs by simp
  next
    case CpA then show ?thesis using cs by simp
  qed
  then show "fconnect (face (cpG (s # cp))) x y \<longleftrightarrow> fconnect (face (cpG cp)) x y"
    and "adj (cpG (s # cp)) x y \<longleftrightarrow> adj (cpG cp) x y"
    and "edge (cpG (s # cp)) x = edge (cpG cp) x"
    and "x \<notin> set (cpring_of cp) \<Longrightarrow> node (cpG (s # cp)) x = node (cpG cp) x \<and> x \<notin> set (cpring_of (s # cp))"
    using c by (auto simp: cpring_of_def)
qed

section \<open>Injections into extended programs\<close>

lemma cubic_prog_Cons: "cubic_prog (s # cp) \<longleftrightarrow> cubic_prog [s] \<and> cubic_prog cp"
  by (cases s) simp_all

lemma injcp_mono:
  "darts (cpG cp2) \<subseteq> darts (cpG (rev cp1 @ cp2)) \<and>
   (\<forall>x \<in> darts (cpG cp2). \<forall>y \<in> darts (cpG cp2).
      (fconnect (face (cpG cp2)) x y \<longrightarrow> fconnect (face (cpG (rev cp1 @ cp2))) x y) \<and>
      (adj (cpG cp2) x y \<longrightarrow> adj (cpG (rev cp1 @ cp2)) x y))"
proof (induction cp1 arbitrary: cp2)
  case Nil
  then show ?case by simp
next
  case (Cons s cp1)
  have IH: "darts (cpG (s # cp2)) \<subseteq> darts (cpG (rev cp1 @ s # cp2)) \<and>
      (\<forall>x \<in> darts (cpG (s # cp2)). \<forall>y \<in> darts (cpG (s # cp2)).
        (fconnect (face (cpG (s # cp2))) x y \<longrightarrow> fconnect (face (cpG (rev cp1 @ s # cp2))) x y) \<and>
        (adj (cpG (s # cp2)) x y \<longrightarrow> adj (cpG (rev cp1 @ s # cp2)) x y))"
    by (rule Cons.IH)
  have sub: "darts (cpG cp2) \<subseteq> darts (cpG (s # cp2))"
    using step_mono(1)[of "cpx cp2" cp2 "cpx cp2" s] cpx_in by blast
  have st: "x \<in> darts (cpG cp2) \<Longrightarrow> y \<in> darts (cpG cp2) \<Longrightarrow>
      (fconnect (face (cpG cp2)) x y \<longrightarrow> fconnect (face (cpG (s # cp2))) x y) \<and>
      (adj (cpG cp2) x y \<longrightarrow> adj (cpG (s # cp2)) x y)" for x y
    using step_mono(2,3)[of x cp2 y s] by blast
  show ?case using IH sub st by (auto simp del: cpmap.simps) (meson subsetD)+
qed

lemma sub_cface_injcp:
  "x \<in> darts (cpG cp2) \<Longrightarrow> y \<in> darts (cpG cp2) \<Longrightarrow> fconnect (face (cpG cp2)) x y \<Longrightarrow>
   fconnect (face (cpG (rev cp1 @ cp2))) x y"
  using injcp_mono by blast

lemma sub_adj_injcp:
  "x \<in> darts (cpG cp2) \<Longrightarrow> y \<in> darts (cpG cp2) \<Longrightarrow> adj (cpG cp2) x y \<Longrightarrow>
   adj (cpG (rev cp1 @ cp2)) x y"
  using injcp_mono by blast

lemma darts_injcp: "darts (cpG cp2) \<subseteq> darts (cpG (rev cp1 @ cp2))"
  using injcp_mono by blast

lemma injcp_cubic:
  assumes "cubic_prog cp1"
  shows "\<forall>x \<in> darts (cpG cp2). \<forall>y \<in> darts (cpG cp2).
     (fconnect (face (cpG (rev cp1 @ cp2))) x y \<longleftrightarrow> fconnect (face (cpG cp2)) x y) \<and>
     (adj (cpG (rev cp1 @ cp2)) x y \<longleftrightarrow> adj (cpG cp2) x y) \<and>
     edge (cpG (rev cp1 @ cp2)) x = edge (cpG cp2) x \<and>
     (x \<notin> set (cpring_of cp2) \<longrightarrow> node (cpG (rev cp1 @ cp2)) x = node (cpG cp2) x \<and>
                                    x \<notin> set (cpring_of (rev cp1 @ cp2)))"
  using assms
proof (induction cp1 arbitrary: cp2)
  case Nil
  then show ?case by simp
next
  case (Cons s cp1)
  have cs: "cubic_prog [s]" and c1: "cubic_prog cp1" using Cons.prems cubic_prog_Cons by blast+
  note IH = Cons.IH[OF c1, of "s # cp2"]
  have sub: "darts (cpG cp2) \<subseteq> darts (cpG (s # cp2))"
    using step_mono(1)[of "cpx cp2" cp2 "cpx cp2" s] cpx_in by blast
  show ?case
  proof (intro ballI)
    fix x y assume x: "x \<in> darts (cpG cp2)" and y: "y \<in> darts (cpG cp2)"
    have x': "x \<in> darts (cpG (s # cp2))" and y': "y \<in> darts (cpG (s # cp2))" using x y sub by auto
    note S = cubic_step[OF cs x y]
    note I = IH[rule_format, OF x' y']
    show "(fconnect (face (cpG (rev (s # cp1) @ cp2))) x y \<longleftrightarrow> fconnect (face (cpG cp2)) x y) \<and>
     (adj (cpG (rev (s # cp1) @ cp2)) x y \<longleftrightarrow> adj (cpG cp2) x y) \<and>
     edge (cpG (rev (s # cp1) @ cp2)) x = edge (cpG cp2) x \<and>
     (x \<notin> set (cpring_of cp2) \<longrightarrow> node (cpG (rev (s # cp1) @ cp2)) x = node (cpG cp2) x \<and>
                                    x \<notin> set (cpring_of (rev (s # cp1) @ cp2)))"
      using S I by (simp del: cpmap.simps)
  qed
qed

lemma cface_injcp:
  "cubic_prog cp1 \<Longrightarrow> x \<in> darts (cpG cp2) \<Longrightarrow> y \<in> darts (cpG cp2) \<Longrightarrow>
   fconnect (face (cpG (rev cp1 @ cp2))) x y \<longleftrightarrow> fconnect (face (cpG cp2)) x y"
  using injcp_cubic by blast

lemma adj_injcp:
  "cubic_prog cp1 \<Longrightarrow> x \<in> darts (cpG cp2) \<Longrightarrow> y \<in> darts (cpG cp2) \<Longrightarrow>
   adj (cpG (rev cp1 @ cp2)) x y \<longleftrightarrow> adj (cpG cp2) x y"
  using injcp_cubic by blast

lemma edge_injcp:
  "cubic_prog cp1 \<Longrightarrow> x \<in> darts (cpG cp2) \<Longrightarrow> edge (cpG (rev cp1 @ cp2)) x = edge (cpG cp2) x"
  using injcp_cubic by blast

lemma node_injcp:
  "cubic_prog cp1 \<Longrightarrow> x \<in> darts (cpG cp2) \<Longrightarrow> x \<notin> set (cpring_of cp2) \<Longrightarrow>
   node (cpG (rev cp1 @ cp2)) x = node (cpG cp2) x"
  using injcp_cubic by blast

lemma cnode_injcp:
  assumes c1: "cubic_prog cp1" and x: "x \<in> darts (cpG cp2)" and nx: "x \<notin> set (cpring_of cp2)"
  shows "fconnect (node (cpG (rev cp1 @ cp2))) x y \<longleftrightarrow> fconnect (node (cpG cp2)) x y"
proof -
  interpret H2: hypermap "cpG cp2" by (rule hypermap_cpmap)
  have pw: "(node (cpG (rev cp1 @ cp2)) ^^ k) x = (node (cpG cp2) ^^ k) x \<and>
            (node (cpG cp2) ^^ k) x \<in> darts (cpG cp2) \<and> (node (cpG cp2) ^^ k) x \<notin> set (cpring_of cp2)" for k
  proof (induction k)
    case 0
    then show ?case using x nx by simp
  next
    case (Suc k)
    define z where "z = (node (cpG cp2) ^^ k) x"
    have z: "z \<in> darts (cpG cp2)" "z \<notin> set (cpring_of cp2)" using Suc by (simp_all add: z_def)
    have "node (cpG (rev cp1 @ cp2)) z = node (cpG cp2) z" using node_injcp[OF c1 z] .
    moreover have "node (cpG cp2) z \<notin> set (cpring_of cp2)"
      using z(2) H2.ring_closed_node by (simp add: cpring_of_def)
    ultimately show ?case using Suc z by (simp add: z_def[symmetric])
  qed
  show ?thesis unfolding fconnect_def using pw by metis
qed

end
