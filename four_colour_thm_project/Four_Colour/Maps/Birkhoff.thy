(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Birkhoff.thy
    The Birkhoff theorem: a minimal counterexample is internally 5-connected,
    and its consequences for spoke rings.
    Ported from G. Gonthier's Coq development (birkhoff.v).
*)
theory Birkhoff
  imports Birkhoff_check Hypermap_iso Four_Colour_Maps.Revsnip Four_Colour_Maps.Sew
begin

section \<open>Bridgeless patches (patch.v)\<close>

lemma (in patch) bridgeless_patch:
  assumes bd: "bridgeless Gd" and br: "bridgeless Gr" and cl: "chordless Gd bGd"
  shows "bridgeless G"
  unfolding bridgeless_def
proof (intro ballI notI)
  fix x assume xD: "x \<in> darts G" and xF: "G.cface x (edge G x)"
  show False
  proof (cases "x \<in> hr ` darts Gr")
    case True
    then obtain xr where xr: "xr \<in> darts Gr" "x = hr xr" by blast
    have exr: "edge Gr xr \<in> darts Gr" using xr by simp
    have "G.cface (hr xr) (hr (edge Gr xr))" using xF xr edge_r[OF xr(1)] by simp
    then have "Gr.cface xr (edge Gr xr)" using patch_face_r[OF xr(1) exr] by simp
    then show False using br xr(1) by (simp add: bridgeless_def)
  next
    case False
    then obtain xd where xd: "xd \<in> darts Gd" "x = hd xd" using xD codom_union by blast
    have nb: "xd \<notin> set bGd" using hd_in_r[OF xd(1)] False xd(2) by simp
    have exd: "edge Gd xd \<in> darts Gd" using xd by simp
    have ex: "edge G x = hd (edge Gd xd)" using edge_d[OF xd(1) nb] xd(2) by simp
    have xF': "G.cface (hd xd) (hd (edge Gd xd))" using xF xd(2) ex by simp
    show False
    proof (cases "hd xd \<in> outer")
      case False
      then have "Gd.cface xd (edge Gd xd)" using patch_face_d[OF xd(1) exd False] xF' by simp
      then show False using bd xd(1) by (simp add: bridgeless_def)
    next
      case True
      have out2: "hd (edge Gd xd) \<in> outer" using True outer_cface[OF xF'] by simp
      have "fband Gd bGd xd" using outer_hd[OF xd(1)] True by simp
      then obtain yd where yd: "yd \<in> set bGd" "Gd.cface xd yd" by (auto simp: fband_def)
      have "fband Gd bGd (edge Gd xd)" using outer_hd[OF exd] out2 by simp
      then obtain zd where zd: "zd \<in> set bGd" "Gd.cface (edge Gd xd) zd" by (auto simp: fband_def)
      have ydD: "yd \<in> darts Gd" "zd \<in> darts Gd" using yd(1) zd(1) bGd_D by auto
      have adj: "adj Gd yd zd"
        unfolding adj_def rlink_def using Gd.F.fconnect_sym[OF yd(2)] zd(2) by blast
      have pn: "zd = prev_in bGd yd \<or> zd = next_in bGd yd"
        using cl yd(1) zd(1) adj by (auto simp: chordless_def)
      obtain yr where yr: "yr \<in> darts Gr" "hd (edge Gd yd) = hr yr" "hd yd = hr (node Gr yr)"
        using bGdP[OF yd(1)] by blast
      have hy: "G.cface (hd yd) (hd xd)" using G.F.fconnect_sym[OF patch_face_d'[OF xd(1) yd(2)]] .
      have hz: "G.cface (hd (edge Gd xd)) (hd zd)" by (rule patch_face_d'[OF exd zd(2)])
      have yz: "G.cface (hd yd) (hd zd)" by (rule fconnect_trans[OF hy fconnect_trans[OF xF' hz]])
      have nyD: "node Gr yr \<in> darts Gr" "node Gr (node Gr yr) \<in> darts Gr" using yr(1) by simp_all
      from pn show False
      proof
        assume zn: "zd = next_in bGd yd"
        have "edge Gd yd = next_in bGd yd" by (rule cycle_next_in[OF cycle_d yd(1)])
        then have "hd zd = hr yr" using zn yr(2) by simp
        then have "G.cface (hr (node Gr yr)) (hr yr)" using yz yr(3) by simp
        then have c: "Gr.cface (node Gr yr) yr" using patch_face_r[OF nyD(1) yr(1)] by simp
        have "face Gr (edge Gr (node Gr yr)) = yr" by (rule Gr.nodeK)
        then have "Gr.cface (node Gr yr) (edge Gr (node Gr yr))" using c Gr.F.fconnect_f_right by metis
        then show False using br nyD(1) by (simp add: bridgeless_def)
      next
        assume zp: "zd = prev_in bGd yd"
        have "edge Gd zd = yd"
        proof -
          have zin: "zd \<in> set bGd" using zd(1) .
          have "edge Gd zd = next_in bGd zd" by (rule cycle_next_in[OF cycle_d zin])
          also have "\<dots> = yd" using zp yd(1) distinct_d by (simp add: next_prev_in)
          finally show ?thesis .
        qed
        then have "hd (edge Gd zd) = hr (node Gr yr)" using yr(3) by simp
        then have hz2: "hd zd = hr (node Gr (node Gr yr))" using hdErN[OF ydD(2) nyD(1)] by simp
        then have "G.cface (hr (node Gr (node Gr yr))) (hr (node Gr yr))"
          using G.F.fconnect_sym[OF yz] yr(3) by simp
        then have c: "Gr.cface (node Gr (node Gr yr)) (node Gr yr)" using patch_face_r[OF nyD(2) nyD(1)] by simp
        have "face Gr (edge Gr (node Gr (node Gr yr))) = node Gr yr" by (rule Gr.nodeK)
        then have "Gr.cface (node Gr (node Gr yr)) (edge Gr (node Gr (node Gr yr)))"
          using c Gr.F.fconnect_f_right by metis
        then show False using br nyD(2) by (simp add: bridgeless_def)
      qed
    qed
  qed
qed

section \<open>Reversed traces (color.v)\<close>

lemma nth_trace:
  assumes i: "i < length lc"
  shows "trace lc ! i = lc ! i +c lc ! (Suc i mod length lc)"
proof (cases lc)
  case Nil then show ?thesis using i by simp
next
  case (Cons c l)
  have L: "length (l @ [c]) = length lc" using Cons by simp
  have t: "trace lc = pairmap addc c (l @ [c])" using Cons by (simp add: trace_Cons)
  have "pairmap addc c (l @ [c]) ! i = (c # l @ [c]) ! i +c (l @ [c]) ! i"
    using i L by (intro nth_pairmap) simp
  moreover have "(c # l @ [c]) ! i = lc ! i" using i Cons by (cases i) (simp_all add: nth_append)
  moreover have "(l @ [c]) ! i = lc ! (Suc i mod length lc)"
  proof (cases "Suc i = length lc")
    case True then show ?thesis using Cons by (simp add: nth_append)
  next
    case False
    then have "Suc i < length lc" using i by simp
    then show ?thesis using Cons by (simp add: nth_append)
  qed
  ultimately show ?thesis using t by simp
qed

lemma trace_rev: "trace (rev lc) = rot 1 (rev (trace lc))"
proof (rule nth_equalityI)
  show "length (trace (rev lc)) = length (rot 1 (rev (trace lc)))" by simp
next
  fix i assume "i < length (trace (rev lc))"
  then have i: "i < length lc" by simp
  define m where "m = length lc"
  have m0: "0 < m" using i unfolding m_def by linarith
  have r1: "rot 1 (rev (trace lc)) ! i = rev (trace lc) ! (Suc i mod m)"
  proof -
    have "trace lc \<noteq> []" using m0 unfolding m_def by (metis length_0_conv length_trace less_irrefl)
    then obtain a t where at: "rev (trace lc) = a # t" by (cases "rev (trace lc)") auto
    have lt: "length t = m - 1" using arg_cong[OF at, of length] by (simp add: m_def)
    show ?thesis
    proof (cases "Suc i = m")
      case True
      then have im: "i = m - Suc 0" by simp
      show ?thesis using at lt True by (simp add: rot_def nth_append im)
    next
      case False then have si: "Suc i < m" using i by (simp add: m_def)
      then have im: "i < m - Suc 0" by linarith
      show ?thesis using at lt si im by (simp add: rot_def nth_append)
    qed
  qed
  show "trace (rev lc) ! i = rot 1 (rev (trace lc)) ! i"
  proof (cases "Suc i = m")
    case True
    have "trace (rev lc) ! i = rev lc ! i +c rev lc ! 0" using nth_trace[of i "rev lc"] i True by (simp add: m_def)
    also have "\<dots> = lc ! 0 +c lc ! (m - 1)" using True m0 by (simp add: rev_nth m_def)
    also have "\<dots> = trace lc ! (m - 1)"
      using nth_trace[of "m - 1" lc] m0 by (simp add: m_def addcC)
    also have "\<dots> = rot 1 (rev (trace lc)) ! i" using r1 True m0 by (simp add: rev_nth m_def)
    finally show ?thesis .
  next
    case False
    then have si: "Suc i < m" using i by (simp add: m_def)
    have "trace (rev lc) ! i = rev lc ! i +c rev lc ! (Suc i)" using nth_trace[of i "rev lc"] i si by (simp add: m_def)
    also have "\<dots> = lc ! (m - Suc i) +c lc ! (m - Suc (Suc i))" using si by (simp add: rev_nth m_def)
    also have "\<dots> = trace lc ! (m - Suc (Suc i))"
      using nth_trace[of "m - Suc (Suc i)" lc] si by (simp add: m_def addcC Suc_diff_Suc)
    also have "\<dots> = rot 1 (rev (trace lc)) ! i" using r1 si by (simp add: rev_nth m_def)
    finally show ?thesis .
  qed
qed

section \<open>The minimal counterexample context\<close>

locale birk = hypermap G for G :: "'a hypermap" +
  assumes mce: "minimal_counter_example G"
begin

lemma planarG: "planar G" and bridgelessG: "bridgeless G" and plainG: "plain G"
  and noncolG: "\<not> four_colorable G"
  using mce by (auto simp: minimal_counter_example_def planar_bridgeless_plain_precubic_def
      planar_bridgeless_plain_def planar_bridgeless_def)

lemma cubicG: "cubic G" by (rule minimal_counter_example_is_cubic[OF mce])

lemma connectedG: "connected G" by (rule minimal_counter_example_is_connected[OF mce])

lemma minG:
  "planar_bridgeless_plain_precubic H \<Longrightarrow> card (darts H) < card D \<Longrightarrow> four_colorable H"
  by (rule minimal_counter_example_any_type[OF mce])

lemma ee [simp]: "e (e x) = x" using plainG by (rule plain_eq)

lemma nnn: "x \<in> D \<Longrightarrow> n (n (n x)) = x" using cubicG by (rule cubic_eq)

end

section \<open>Card of configuration maps\<close>

lemma card_cpmap: "card (darts (cpG cp)) = cpcard cp"
proof (induction cp)
  case Nil then show ?case by simp
next
  case (Cons s cp)
  obtain G x where c: "cpmap cp = (G, x)" by (cases "cpmap cp")
  interpret E: ecp2h G x using hypermap_cpmap[of cp] cpx_in[of cp] c by (intro ecp2h_intro) simp_all
  have IH: "card E.D = cpcard cp" using Cons c by simp
  show ?case
  proof (cases s)
    case (CpR k) then show ?thesis using cpmap_Cons_cases(1)[OF c] IH by simp
  next
    case CpR' then show ?thesis using cpmap_Cons_cases(2)[OF c] IH by simp
  next
    case CpU then show ?thesis using cpmap_Cons_cases(3)[OF c E.ecp_axioms] IH E.card_GU by simp
  next
    case CpY
    have "card (darts E.GY) = Suc (Suc (card (darts E.GU)))" by (rule E.T.card_GN)
    then show ?thesis using CpY cpmap_Cons_cases(4)[OF c E.ecp2_axioms] IH E.card_GU by simp
  next
    case CpH
    have "card (darts E.GH) = Suc (Suc (card (darts E.GY)))" by (rule E.T2.card_GN)
    moreover have "card (darts E.GY) = Suc (Suc (card (darts E.GU)))" by (rule E.T.card_GN)
    ultimately show ?thesis using CpH cpmap_H[OF c E.ecp2h_axioms] IH E.card_GU by simp
  next
    case CpK
    interpret K: ecpk G x by (simp add: ecpk_def E.ecp_axioms)
    show ?thesis using CpK cpmap_Cons_cases(5)[OF c K.ecpk_axioms] IH K.K.card_GN by simp
  next
    case CpA
    interpret A: ecpa G x using E.hypermap_axioms E.x0D by (intro ecpa_intro)
    show ?thesis using CpA cpmap_Cons_cases(6)[OF c A.ecpa_axioms] IH by (simp add: A.GA_def ecpA_def)
  qed
qed

section \<open>The basis check\<close>

context birk
begin

lemma chkbP:
  assumes leq: "\<And>r'. scycle G (rlink G) r' \<Longrightarrow> set r' \<subseteq> D \<Longrightarrow> length r' \<le> nn \<Longrightarrow> \<not> nontrivial_ring G 0 r'"
    and Ur: "scycle G (rlink G) r" "set r \<subseteq> D" and sz: "length r = Suc nn"
    and nt: "nontrivial_ring G m r"
    and cpok: "Birkhoff_check1 nn m cp" and dj: "ctree_disjoint ctu (cpcolor cp)"
  shows "\<exists>et. ring_trace (snip_ring.snipd G r) r (ctrace et) \<and> \<not> ctree_mem ctu (etrace et)"
proof -
  have rs: "revsnip G r"
    using planarG Ur bridgelessG plainG connectedG hypermap_axioms
    by (simp add: revsnip_def revsnip_axioms_def snip_ring_def snip_ring_axioms_def)
  have pr: "proper_ring G r" by (rule revsnip.nontrivial_ring_proper[OF rs nt])
  interpret S: revsnip_proper G r using rs pr by (simp add: revsnip_proper_def revsnip_proper_axioms_def)
  have cpQ: "cubic_prog cp" and cpsz: "Suc (cpcard cp) < 6 * m + 4 * nn" and cprs: "cprsize cp = Suc nn"
    using cpok by (simp_all add: Birkhoff_check1_def)
  define Gr where "Gr = cpG cp"
  define bGr where "bGr = rotr1 (rev (cpring_of cp))"
  interpret HR: hypermap Gr unfolding Gr_def by (rule hypermap_cpmap)
  have ringr: "cpring_of cp = cpring Gr (cpx cp)" by (simp add: cpring_of_def Gr_def)
  have cycr: "cycle (frel (node Gr)) bGr"
    using HR.cycle_rev_cpring[of "cpx cp"] by (simp add: bGr_def ringr rotr1_def cycle_rotate rot_rotate)
  have distr: "distinct bGr" using HR.cpring_distinct by (simp add: bGr_def ringr)
  have bGrD: "set bGr \<subseteq> darts Gr" using HR.ringD_gen[OF cpx_in[of cp, folded Gr_def]] by (simp add: bGr_def ringr)
  have lenr: "length r = length bGr" using sz size_ring_cpmap[of cp] cprs by (simp add: bGr_def rotr1_def)
  interpret SW: sew_data S.snipd Gr r bGr
    using S.Sd.hypermap_axioms HR.hypermap_axioms S.P.cycle_d S.P.simple_d S.P.bGd_D cycr distr bGrD lenr
    by unfold_locales simp_all
  interpret PP: patch SW.sew_map S.snipd Gr Inl SW.sewr r bGr by (rule SW.sew_map_patch)
  define G2 where "G2 = SW.sew_map"
  have pl2: "planar G2" unfolding G2_def
    using PP.planar_patch S.planar_snipd cpmap_planar[OF cpQ] by (simp add: Gr_def)
  have plain2: "plain G2" unfolding G2_def
    using PP.plain_patch S.P.plain_patch plainG cpmap_plain[OF cpQ] by (simp add: Gr_def)
  have cubic2: "cubic G2"
  proof -
    have "cubic S.snipd" using S.P.cubic_patch cubicG by simp
    moreover have "cubicb Gr (darts Gr - set bGr)"
      using cpmap_cubic[OF cpQ] by (simp add: quasicubic_def Gr_def bGr_def ringr)
    ultimately show ?thesis unfolding G2_def using PP.cubic_patch by simp
  qed
  have chordless: "chordless S.snipd r"
  proof (rule ccontr)
    assume nc: "\<not> chordless S.snipd r"
    have nt0: "nontrivial_ring G 0 r" using nt by (simp add: nontrivial_ring_def)
    obtain r' where r': "scycle G (rlink G) r'" "set r' \<subseteq> D" "nontrivial_ring G 0 r'" "length r' < length r"
      using S.ring_disk_chord[OF nt0 nc] by blast
    then show False using leq[OF r'(1,2)] sz by simp
  qed
  have br2: "bridgeless G2" unfolding G2_def
  proof (rule PP.bridgeless_patch)
    show "bridgeless S.snipd" using S.P.patch_bridgeless bridgelessG by blast
    show "bridgeless Gr" using cpmap_bridgeless[OF cpQ] by (simp add: Gr_def)
    show "chordless S.snipd r" by (rule chordless)
  qed
  have card2: "card (darts G2) < card D"
  proof -
    have c1: "card (darts S.snipd) + card (darts Gr) = length r + card (darts G2)"
      using PP.card_patch unfolding G2_def by simp
    have c2: "card (darts S.snipd) + card (darts S.snipr) = length r + card D"
      using S.P.card_patch by simp
    have cGr: "card (darts Gr) = cpcard cp" by (simp add: Gr_def card_cpmap)
    have ucq: "ucycle_plain_quasicubic_connected S.snipr (rev r)"
    proof -
      have "plain S.snipr" using S.P.plain_patch plainG by simp
      moreover have "quasicubic S.snipr (rev r)" using S.P.cubic_patch cubicG by (simp add: quasicubic_def)
      moreover have "connected S.snipr"
        using S.P.patch_connected_r[OF connectedG] S.P.bGr_D Ur(2) sz by (cases r) auto
      moreover have "ucycle (frel (node S.snipr)) (rev r)" using S.P.cycle_r S.P.distinct_r by (simp add: ucycle_def)
      ultimately show ?thesis using S.hypermap_snipr S.P.bGr_D
        by (simp add: ucycle_plain_quasicubic_connected_def ucycle_plain_quasicubic_def plain_quasicubic_def)
    qed
    have eul: "6 * (1 + fcard (face S.snipr) (darts S.snipr)) = card (darts S.snipr) + (2 * length r + 12)"
      using hypermap.quasicubic_Euler[OF S.hypermap_snipr ucq] S.planar_snipr sz by (cases r) simp_all
    have fo: "fcard (face S.snipr) (darts S.snipr) = Suc nn + fcard f S.diskFC"
    proof -
      have o: "S.P.outer = {x \<in> D. fband G r x} \<union> S.diskFC"
      proof (rule set_eqI)
        fix x
        show "x \<in> S.P.outer \<longleftrightarrow> x \<in> {x \<in> D. fband G r x} \<union> S.diskFC"
        proof
          assume xo: "x \<in> S.P.outer"
          then have xD: "x \<in> D" and "\<exists>y \<in> darts S.snipr. cface x y" by (auto simp: S.P.outer_def)
          then obtain y where y: "y \<in> D - S.diskE" "cface x y" by auto
          show "x \<in> {x \<in> D. fband G r x} \<union> S.diskFC"
          proof (cases "fband G r x")
            case True then show ?thesis using xD by simp
          next
            case nf: False
            have "x \<notin> S.diskN"
            proof
              assume xN: "x \<in> S.diskN"
              have xF: "x \<in> S.diskF" using xN nf by (simp add: S.diskF_def)
              have "y \<in> S.diskF"
                using y(2) xF by (induction rule: fconnect_induct) (auto intro: S.diskF_face)
              then have "y \<in> S.diskN" "\<not> fband G r y" by (simp_all add: S.diskF_def)
              then have "y \<in> set r" using y(1) by (simp add: S.diskE_def)
              then show False using \<open>\<not> fband G r y\<close> fband_ring by blast
            qed
            then show ?thesis using xD nf by (simp add: S.diskFC_def)
          qed
        next
          assume "x \<in> {x \<in> D. fband G r x} \<union> S.diskFC"
          then consider "x \<in> D" "fband G r x" | "x \<in> S.diskFC" by blast
          then show "x \<in> S.P.outer"
          proof cases
            case 1
            then obtain y where y: "y \<in> set r" "cface x y" by (auto simp: fband_def)
            have "y \<in> darts S.snipr" using y(1) S.r_diskR by simp
            then show ?thesis using 1 y by (auto simp: S.P.outer_def)
          next
            case 2
            then have "x \<in> D" "x \<notin> S.diskN" by (simp_all add: S.diskFC_def)
            then have "x \<in> darts S.snipr" by (simp add: S.diskE_def)
            then show ?thesis using \<open>x \<in> D\<close> by (auto simp: S.P.outer_def)
          qed
        qed
      qed
      have dj2: "{x \<in> D. fband G r x} \<inter> S.diskFC = {}" by (auto simp: S.diskFC_def)
      have cl: "\<And>x. x \<in> {x \<in> D. fband G r x} \<Longrightarrow> f x \<in> {x \<in> D. fband G r x}" by simp
      have "fcard f S.P.outer = fcard f {x \<in> D. fband G r x} + fcard f (S.P.outer - {x \<in> D. fband G r x})"
        by (rule F.fcard_split_closed[OF _ _ cl]) (auto simp: o S.diskFC_def)
      moreover have "S.P.outer - {x \<in> D. fband G r x} = S.diskFC" using o dj2 by blast
      moreover have "fcard f {x \<in> D. fband G r x} = length r"
        using simple_fcard_fband[OF S.simple_r Ur(2)] .
      ultimately show ?thesis using S.P.fcard_face_r sz by simp
    qed
    have "m < fcard f S.diskFC" using nt by (simp add: nontrivial_ring_def)
    then have "4 * nn + 6 * m + 4 \<le> card (darts S.snipr)" using eul fo sz by presburger
    then have "card (darts Gr) < card (darts S.snipr)" using cGr cpsz by linarith
    then show ?thesis using c1 c2 by linarith
  qed
  have col2: "four_colorable G2"
  proof (rule minG)
    show "planar_bridgeless_plain_precubic G2"
      using PP.G.hypermap_axioms pl2 br2 plain2 hypermap.cubic_precubic[OF PP.G.hypermap_axioms cubic2[unfolded G2_def]]
      unfolding G2_def
      by (simp add: planar_bridgeless_plain_precubic_def planar_bridgeless_plain_def planar_bridgeless_def)
    show "card (darts G2) < card D" by (rule card2)
  qed
  obtain et where etd: "ring_trace S.snipd r et" and etr: "ring_trace Gr bGr (rot 1 (rev et))"
    using PP.colorable_patch col2 unfolding G2_def by blast
  obtain kd where kd: "coloring S.snipd kd" "et = trace (map kd r)" using etd by (auto simp: ring_trace_def)
  have ne: "et \<noteq> []" using kd(2) sz by (metis Zero_not_Suc length_0_conv length_map length_trace)
  define et' where "et' = butlast et"
  have Det: "et = ctrace et'" unfolding et'_def using kd(2) ne by (intro ctrace_butlast) simp_all
  have last: "et = et' @ [sumt et']" using Det by (simp add: ctrace_def)
  obtain k where k: "coloring Gr k" and kt: "rot 1 (rev et) = trace (map k bGr)" using etr by (auto simp: ring_trace_def)
  define T where "T = trace (map k (cpring_of cp))"
  have "trace (map k bGr) = rotr1 (trace (map k (rev (cpring_of cp))))"
    by (simp add: bGr_def rotr1_def map_rot trace_rot)
  also have "trace (map k (rev (cpring_of cp))) = rot 1 (rev T)" by (simp add: T_def rev_map[symmetric] trace_rev)
  also have "rotr1 (rot 1 (rev T)) = rev T"
  proof (cases "rev T")
    case Nil then show ?thesis by (simp add: rotr1_def rot_def)
  next
    case (Cons a l) then show ?thesis by (simp add: rotr1_def rot_def)
  qed
  finally have "rev T = rot 1 (rev et)" using kt by simp
  then have "rev T = rev (sumt et' # et')" using last by (simp add: rot_def)
  then have TT: "T = sumt et' # et'" by (metis rev_rev_ident)
  define g where "g = etrace_perm et'"
  define k' where "k' x = permc g (k x)" for x
  have colk': "coloring (cpG cp) k'" using k by (simp add: coloring_def k'_def permc_inj Gr_def)
  have "trace (map k' (cpring_of cp)) = permt g T"
  proof -
    have "map k' (cpring_of cp) = permt g (map k (cpring_of cp))" by (simp add: k'_def permt_def)
    then show ?thesis by (simp add: T_def trace_permt)
  qed
  also have "\<dots> = sumt (etrace et') # etrace et'" using TT by (simp add: g_def etrace_def sumt_permt)
  finally have "ring_trace (cpG cp) (cpring_of cp) (sumt (etrace et') # etrace et')"
    using colk' by (auto simp: ring_trace_def)
  then have "ctree_mem (cpcolor cp) (etrace et')" using ctree_mem_cpcolor even_etrace by blast
  then have "\<not> ctree_mem ctu (etrace et')" using ctree_mem_disjoint[OF dj] by blast
  moreover have "ring_trace S.snipd r (ctrace et')" using etd Det by simp
  ultimately show ?thesis by blast
qed

end

section \<open>Picking traces\<close>

lemma sumt_pick_rec:
  "e +c sumt et = Color0 \<Longrightarrow> sumt (ctree_pick_rev_rec et e t' t) = Color0"
proof (induction et e t' t rule: ctree_pick_rev_rec.induct)
  case (1 et e t' uu)
  then show ?case by simp
next
  case (2 et e t' t1 t2 t3)
  have s: "(e +c c) +c sumt (c # et) = Color0" for c
  proof -
    have "(e +c c) +c sumt (c # et) = e +c (c +c (c +c sumt et))" by (simp only: sumt_Cons addcA)
    also have "\<dots> = e +c sumt et" by (simp only: addKc)
    finally show ?thesis using 2(4) by simp
  qed
  show ?case using 2(1)[OF s] 2(2)[OF _ s] 2(3)[OF _ _ s]
    by (auto split: list.splits)
next
  case (3 et e t')
  then show ?case by simp
qed

lemma sumt_ctree_pick_rev: "sumt (ctree_pick_rev t' t) = Color0"
  unfolding ctree_pick_rev_def by (rule sumt_pick_rec) simp

lemma size_pick_rec:
  "ctree_proper k t \<Longrightarrow> ctree_pick_rev_rec et e t' t = [] \<or>
     length (ctree_pick_rev_rec et e t' t) = Suc (k + length et)"
proof (induction k t arbitrary: et e rule: ctree_proper.induct)
  case (2 h t1 t2 t3)
  have p: "ctree_proper h t1" "ctree_proper h t2" "ctree_proper h t3" using 2(4) by simp_all
  note I1 = 2(1)[OF p(1), of "Color1 # et" "e +c Color1"]
  note I2 = 2(2)[OF p(2), of "Color2 # et" "e +c Color2"]
  note I3 = 2(3)[OF p(3), of "Color3 # et" "e +c Color3"]
  show ?case using I1 I2 I3 by (auto split: list.splits)
next
  case (3 lf)
  then show ?case by simp
qed simp_all

lemma size_ctree_pick_rev:
  "ctree_proper k t \<Longrightarrow> ctree_pick_rev t' t = [] \<or> length (ctree_pick_rev t' t) = Suc k"
  unfolding ctree_pick_rev_def using size_pick_rec[of k t "[]"] by simp

lemma sumt_rev: "sumt (rev l) = sumt l"
  by (induction l) (simp_all add: sumt_append addcC)

lemma kclosed_perm:
  assumes "Kempe_closed P" "P (permt g et)"
  shows "P et"
proof -
  have "P (permt (inv_eperm g) (permt g et))" using assms by (auto simp: Kempe_closed_def)
  moreover have "permt (inv_eperm g) (permt g et) = et" by (induction et) simp_all
  ultimately show ?thesis by simp
qed

context birk
begin

definition Pn :: "'a list \<Rightarrow> colseq \<Rightarrow> bool" where
  "Pn r et \<longleftrightarrow> \<not> ring_trace (snip_ring.snipd G r) r et"

lemma rev_rev_ring: "rev_ring G (rev_ring G r) = r"
  by (simp add: rev_ring_def rev_map[symmetric] map_map comp_def)

lemma ring_facts:
  assumes Ur: "scycle G (rlink G) r" "set r \<subseteq> D" and nt: "nontrivial_ring G m r"
  shows "revsnip_proper G r"
proof -
  have rs: "revsnip G r"
    using planarG Ur bridgelessG plainG connectedG hypermap_axioms
    by (simp add: revsnip_def revsnip_axioms_def snip_ring_def snip_ring_axioms_def)
  have pr: "proper_ring G r" by (rule revsnip.nontrivial_ring_proper[OF rs nt])
  show ?thesis using rs pr by (simp add: revsnip_proper_def revsnip_proper_axioms_def)
qed

lemma rev_ring_facts:
  assumes Ur: "scycle G (rlink G) r" "set r \<subseteq> D" and nt: "nontrivial_ring G m r"
  shows "scycle G (rlink G) (rev_ring G r)" "set (rev_ring G r) \<subseteq> D"
    "nontrivial_ring G m (rev_ring G r)" "length (rev_ring G r) = length r"
proof -
  interpret S: revsnip_proper G r by (rule ring_facts[OF Ur nt])
  show "scycle G (rlink G) (rev_ring G r)" by (rule S.scycle_rev_ring)
  show "set (rev_ring G r) \<subseteq> D" by (rule S.rr_D)
  show "nontrivial_ring G m (rev_ring G r)" by (rule S.nontrivial_rev_ring[OF nt])
  show "length (rev_ring G r) = length r" by (simp add: rev_ring_def)
qed

lemma length_ring_trace: "ring_trace H p et \<Longrightarrow> length et = length p"
  by (auto simp: ring_trace_def)

lemma side_check:
  assumes leq: "\<And>r'. scycle G (rlink G) r' \<Longrightarrow> set r' \<subseteq> D \<Longrightarrow> length r' \<le> Suc n' \<Longrightarrow> \<not> nontrivial_ring G 0 r'"
    and cps: "list_all (Birkhoff_check1 (Suc n') m) cps"
    and Ur: "scycle G (rlink G) r" "set r \<subseteq> D" and sz: "length r = Suc (Suc n')"
    and nt: "nontrivial_ring G m r"
    and v: "Kempe_valid n' (Pn r) ctu1 CtreeEmpty GtreeEmpty gtu1"
    and full: "ctrace X = ett" "length X = Suc n'" "Color0 \<notin> set X"
    and nrt: "\<not> ring_trace (snip_ring.snipd G r) r ett"
    and chk: "do_Birkhoff_check2 (Suc n') (Birkhoff_basis_check cps) X ctu1 gtu1 chk"
  shows "\<exists>ctu3 gtu3. Kempe_valid n' (Pn r) ctu3 CtreeEmpty GtreeEmpty gtu3 \<and> chk ctu3 gtu3"
proof -
  interpret S: revsnip_proper G r by (rule ring_facts[OF Ur nt])
  have kc: "Kempe_closed (ring_trace S.snipd r)" by (rule S.ring_disk_closed[OF cubicG])
  define ctr where "ctr = ctree_of_ttail (etrace X)"
  have nz: "Color0 \<notin> set (etrace X)" using full(3) by (simp add: etrace_def)
  have Dctr: "ctree_mem ctr et1 \<Longrightarrow> Pn r (ctrace et1) \<and> length et1 = Suc n'" for et1
  proof -
    assume "ctree_mem ctr et1"
    then have e1: "et1 = etrace X" using ctree_of_ttail_mem[OF nz] by (simp add: ctr_def)
    have "\<not> ring_trace S.snipd r (ctrace et1)"
    proof
      assume rt: "ring_trace S.snipd r (ctrace et1)"
      have "ctrace et1 = permt (etrace_perm X) ett" using e1 full(1) by (simp add: etrace_def ctrace_permt)
      then have "ring_trace S.snipd r ett" using kclosed_perm[OF kc] rt by metis
      then show False using nrt by simp
    qed
    then show ?thesis using e1 full(2) by (simp add: Pn_def etrace_def)
  qed
  have v0: "Kempe_valid n' (Pn r) ctu1 ctr GtreeEmpty gtu1" by (rule Kempe_valid_restrict[OF Dctr v])
  obtain ctu3 gtr3 gtu3 where R: "Kempe_tree_closure n' (Suc n') ctu1 ctr gtu1 = (ctu3, GtreePair gtr3 gtu3)"
    by (metis gtree_pair.exhaust prod.exhaust)
  have v3: "Kempe_valid n' (Pn r) ctu3 CtreeEmpty gtr3 gtu3"
    using Kempe_tree_closure_correct[OF v0, of "Suc n'"] R by (simp add: ktr_prop_def)
  have c3: "gtr3 = GtreeEmpty" "Birkhoff_basis_check cps ctu3 \<or> chk ctu3 gtu3"
    using chk full(3) R by (simp_all add: do_Birkhoff_check2_def ctr_def)
  have "\<not> Birkhoff_basis_check cps ctu3"
  proof
    assume "Birkhoff_basis_check cps ctu3"
    then obtain cp where cp: "cp \<in> set cps" "ctree_disjoint ctu3 (cpcolor cp)"
      by (auto simp: Birkhoff_basis_check_def list_ex_iff)
    have ck: "Birkhoff_check1 (Suc n') m cp" using cps cp(1) by (simp add: list_all_iff)
    obtain et1 where et1: "ring_trace S.snipd r (ctrace et1)" "\<not> ctree_mem ctu3 (etrace et1)"
      using chkbP[OF leq Ur sz nt ck cp(2)] by blast
    have "length et1 = Suc n'" using length_ring_trace[OF et1(1)] sz by (simp add: ctrace_def)
    then have "Kempe_coclosure (Pn r) (ctrace et1)" using Kempe_validP[OF v3 _ et1(2)] by blast
    then obtain x where "Pn r x" "ring_trace S.snipd r x" using kc et1(1) by (auto simp: Kempe_coclosure_def)
    then show False by (simp add: Pn_def)
  qed
  then show ?thesis using v3 c3 by blast
qed

lemma Birkhoff_iter:
  assumes leq: "\<And>r'. scycle G (rlink G) r' \<Longrightarrow> set r' \<subseteq> D \<Longrightarrow> length r' \<le> Suc n' \<Longrightarrow> \<not> nontrivial_ring G 0 r'"
    and cps: "list_all (Birkhoff_check1 (Suc n') m) cps"
  shows "scycle G (rlink G) r1 \<Longrightarrow> set r1 \<subseteq> D \<Longrightarrow> length r1 = Suc (Suc n') \<Longrightarrow> nontrivial_ring G m r1 \<Longrightarrow>
    Kempe_valid n' (Pn r1) ctu1 CtreeEmpty GtreeEmpty gtu1 \<Longrightarrow>
    Kempe_valid n' (Pn (rev_ring G r1)) ctu2 CtreeEmpty GtreeEmpty gtu2 \<Longrightarrow>
    \<not> Birkhoff_check2 (Suc n') (Birkhoff_basis_check cps) ctu1 gtu1 nm ctu2 gtu2"
proof (induction nm arbitrary: r1 ctu1 gtu1 ctu2 gtu2)
  case 0
  then show ?case by simp
next
  case (Suc nm)
  define cb where "cb = Birkhoff_basis_check cps"
  define rr where "rr = rev_ring G r1"
  have rrf: "scycle G (rlink G) rr" "set rr \<subseteq> D" "nontrivial_ring G m rr" "length rr = Suc (Suc n')"
    using rev_ring_facts[OF Suc.prems(1,2,4)] Suc.prems(3) by (simp_all add: rr_def)
  interpret S: revsnip_proper G r1 by (rule ring_facts[OF Suc.prems(1,2,4)])
  show ?case
  proof
    assume B: "Birkhoff_check2 (Suc n') (Birkhoff_basis_check cps) ctu1 gtu1 (Suc nm) ctu2 gtu2"
    then obtain e et where pk: "ctree_pick_rev ctu1 ctu2 = e # et"
      by (cases "ctree_pick_rev ctu1 ctu2") simp_all
    have chk1: "do_Birkhoff_check2 (Suc n') cb (butlast (e # et)) ctu1 gtu1
                  (Birkhoff_check2 (Suc n') cb ctu2 gtu2 nm)"
      and chk2: "do_Birkhoff_check2 (Suc n') cb (rev et) ctu2 gtu2
                  (Birkhoff_check2 (Suc n') cb ctu1 gtu1 nm)"
      using B pk by (simp_all add: cb_def)
    have s0: "sumt (e # et) = Color0" using sumt_ctree_pick_rev[of ctu1 ctu2] pk by simp
    then have esum: "e = sumt et" by (simp add: addc_eq0)
    have p2: "ctree_proper (Suc n') ctu2" using Suc.prems(6) by (simp add: Kempe_valid_def)
    have len: "length et = Suc n'" using size_ctree_pick_rev[OF p2, of ctu1] pk by simp
    have nz1: "Color0 \<notin> set (butlast (e # et))" and nz2: "Color0 \<notin> set (rev et)"
      using chk1 chk2 by (auto simp: do_Birkhoff_check2_def)
    have A: "ring_trace S.snipd r1 (e # et)"
    proof (rule ccontr)
      assume nrt: "\<not> ring_trace S.snipd r1 (e # et)"
      have ct: "ctrace (butlast (e # et)) = e # et"
      proof -
        have "e # et \<noteq> []" by simp
        then show ?thesis using ctrace_butlast[OF s0] by metis
      qed
      have lb: "length (butlast (e # et)) = Suc n'" using len by (simp only: length_butlast) simp
      obtain ctu3 gtu3 where v3: "Kempe_valid n' (Pn r1) ctu3 CtreeEmpty GtreeEmpty gtu3"
        and c3: "Birkhoff_check2 (Suc n') cb ctu2 gtu2 nm ctu3 gtu3"
        using side_check[OF leq cps Suc.prems(1,2,3,4,5) ct lb nz1 nrt chk1[unfolded cb_def]]
        unfolding cb_def by blast
      have "\<not> Birkhoff_check2 (Suc n') cb ctu2 gtu2 nm ctu3 gtu3"
        using Suc.IH[OF rrf(1,2,4,3) Suc.prems(6)[folded rr_def]] v3 rev_rev_ring[of r1] by (simp add: rr_def cb_def)
      then show False using c3 by simp
    qed
    have Bt: "ring_trace S.R.snipd rr (rev (e # et))"
    proof (rule ccontr)
      assume nrt: "\<not> ring_trace S.R.snipd rr (rev (e # et))"
      have ct: "ctrace (rev et) = rev (e # et)" using esum by (simp add: ctrace_def sumt_rev)
      have Prr: "Kempe_valid n' (Pn rr) ctu2 CtreeEmpty GtreeEmpty gtu2" using Suc.prems(6) by (simp add: rr_def)
      have lr: "length (rev et) = Suc n'" using len by simp
      have nrt': "\<not> ring_trace (snip_ring.snipd G rr) rr (rev (e # et))" using nrt by (simp add: rr_def)
      obtain ctu3 gtu3 where v3: "Kempe_valid n' (Pn rr) ctu3 CtreeEmpty GtreeEmpty gtu3"
        and c3: "Birkhoff_check2 (Suc n') cb ctu1 gtu1 nm ctu3 gtu3"
        using side_check[OF leq cps rrf(1,2,4,3) Prr ct lr nz2 nrt' chk2[unfolded cb_def]]
        unfolding cb_def by blast
      have "\<not> Birkhoff_check2 (Suc n') cb ctu1 gtu1 nm ctu3 gtu3"
        using Suc.IH[OF Suc.prems(1,2,3,4,5)] v3 by (simp add: rr_def cb_def)
      then show False using c3 by simp
    qed
    have "four_colorable G" using S.colorable_from_ring[OF A Bt[unfolded rr_def]] .
    then show False using noncolG by simp
  qed
qed

theorem Birkhoff_valid:
  assumes leq: "\<And>r'. scycle G (rlink G) r' \<Longrightarrow> set r' \<subseteq> D \<Longrightarrow> length r' \<le> nn \<Longrightarrow> \<not> nontrivial_ring G 0 r'"
    and bk: "Birkhoff_check nn m"
    and Ur: "scycle G (rlink G) r" "set r \<subseteq> D" and sz: "length r = Suc nn"
  shows "\<not> nontrivial_ring G m r"
proof (cases nn)
  case 0
  then obtain x where r: "r = [x]" using sz by (cases r) auto
  have "rlink G x x" using Ur(1) r by (simp add: scycle_def cycle_Cons)
  then have "cface (e x) x" by (simp add: rlink_def)
  moreover have "x \<in> D" using Ur(2) r by simp
  ultimately show ?thesis using bridgelessG F.fconnect_sym by (auto simp: bridgeless_def)
next
  case (Suc n')
  obtain niter cps where cps: "list_all (Birkhoff_check1 nn m) cps"
    and B: "Birkhoff_check2 nn (Birkhoff_basis_check cps) (ctree_init_tree nn) (gtree_init_tree nn) niter
              (ctree_init_tree nn) (gtree_init_tree nn)"
    using bk by (auto simp: Birkhoff_check_def Birkhoff_check_with_def)
  show ?thesis
  proof
    assume nt: "nontrivial_ring G m r"
    have v: "Kempe_valid n' P (ctree_init_tree (Suc n')) CtreeEmpty GtreeEmpty (gtree_init_tree (Suc n'))" for P
      by (rule Kempe_valid_init)
    have "\<not> Birkhoff_check2 (Suc n') (Birkhoff_basis_check cps) (ctree_init_tree (Suc n'))
            (gtree_init_tree (Suc n')) niter (ctree_init_tree (Suc n')) (gtree_init_tree (Suc n'))"
      using Birkhoff_iter[OF leq[unfolded Suc] cps[unfolded Suc] Ur sz[unfolded Suc] nt v v] .
    then show False using B Suc by simp
  qed
qed

end

context birk
begin

lemma ring1_impossible:
  assumes "scycle G (rlink G) [x]" "set [x] \<subseteq> D"
  shows False
proof -
  have "rlink G x x" using assms(1) by (simp add: scycle_def cycle_Cons)
  then have "cface (e x) x" by (simp add: rlink_def)
  then have "cface x (e x)" by (rule F.fconnect_sym)
  then show False using bridgelessG assms(2) by (simp add: bridgeless_def)
qed

theorem Birkhoff:
  assumes "length r \<le> 5" "scycle G (rlink G) r" "set r \<subseteq> D"
  shows "\<not> nontrivial_ring G (if length r = 5 then 1 else 0) r"
proof -
  have "\<forall>r. length r \<le> k \<longrightarrow> scycle G (rlink G) r \<longrightarrow> set r \<subseteq> D \<longrightarrow>
            \<not> nontrivial_ring G (if length r = 5 then 1 else 0) r" if k5: "k \<le> 5" for k
    using k5
  proof (induction k)
    case 0
    show ?case
    proof (intro allI impI)
      fix r :: "'a list" assume "length r \<le> 0"
      then have r: "r = []" by simp
      have sr: "snip_ring G []"
        using hypermap_axioms planarG by (simp add: snip_ring_def snip_ring_axioms_def scycle_def simple_def)
      have "snip_ring.diskF G r = {}"
        unfolding r snip_ring.diskF_def[OF sr] snip_ring.diskN_def[OF sr] by simp
      then show "\<not> nontrivial_ring G (if length r = 5 then 1 else 0) r"
        by (simp add: nontrivial_ring_def fcard_def)
    qed
  next
    case (Suc k)
    have IH: "\<And>r. length r \<le> k \<Longrightarrow> scycle G (rlink G) r \<Longrightarrow> set r \<subseteq> D \<Longrightarrow>
               \<not> nontrivial_ring G (if length r = 5 then 1 else 0) r" using Suc by simp
    show ?case
    proof (intro allI impI)
      fix r :: "'a list" assume lr: "length r \<le> Suc k" and Ur: "scycle G (rlink G) r" and rD: "set r \<subseteq> D"
      show "\<not> nontrivial_ring G (if length r = 5 then 1 else 0) r"
      proof (cases "length r \<le> k")
        case True then show ?thesis using IH Ur rD by blast
      next
        case False
        then have sz: "length r = Suc k" using lr by simp
        have leq: "\<And>r'. scycle G (rlink G) r' \<Longrightarrow> set r' \<subseteq> D \<Longrightarrow> length r' \<le> k \<Longrightarrow> \<not> nontrivial_ring G 0 r'"
          using IH Suc.prems by fastforce
        show ?thesis
        proof (cases k)
          case 0
          then obtain x where "r = [x]" using sz by (cases r) auto
          then show ?thesis using ring1_impossible Ur rD by blast
        next
          case (Suc k')
          have bk: "Birkhoff_check k (if length r = 5 then 1 else 0)"
            using Birkhoff2 Birkhoff3 Birkhoff4 Birkhoff5 Suc.prems sz Suc
            by (cases k'; cases "k' - 1"; cases "k' - 2"; cases "k' - 3") (auto simp: numeral_eq_Suc)
          show ?thesis by (rule Birkhoff_valid[OF leq bk Ur rD sz])
        qed
      qed
    qed
  qed
  then show ?thesis using assms by blast
qed

end

context birk
begin

lemma no_cface_node: "x \<in> D \<Longrightarrow> \<not> cface (n x) x"
proof
  assume xD: "x \<in> D" and c: "cface (n x) x"
  have "cface (e (n x)) x" using fconnect_step[of f "e (n x)"] by (simp add: nodeK)
  then have "cface (n x) (e (n x))" by (rule fconnect_trans[OF c F.fconnect_sym])
  then show False using bridgelessG xD by (simp add: bridgeless_def)
qed

lemma cface_edge_nn: "cface (e x) (n (n x))" if "x \<in> D" for x
proof -
  have "f (e (n (n (n x)))) = n (n x)" by (rule nodeK)
  then have "f (e x) = n (n x)" using nnn[OF that] by simp
  then show ?thesis using fconnect_step[of f "e x"] by simp
qed

lemma scycle2:
  assumes "x \<in> D" "y \<in> D"
  shows "scycle G (rlink G) [x, y] \<longleftrightarrow> rlink G x y \<and> rlink G y x \<and> \<not> cface x y"
  using assms by (auto simp: scycle_def cycle_Cons simple_def F.cyc_eq_iff)

lemma nontrivial_cycle2:
  assumes xD: "x \<in> D" and yD: "y \<in> D" and Ur: "scycle G (rlink G) [x, y]" and ne: "e x \<noteq> y"
  shows "nontrivial_ring G 0 [x, y]"
proof -
  interpret S: snip_ring G "[x, y]" using planarG Ur xD yD by unfold_locales auto
  have r: "rlink G x y" "rlink G y x" "\<not> cface x y" using Ur scycle2[OF xD yD] by auto
  have nxD: "n x \<in> D" using xD by simp
  have nxN: "n x \<in> S.diskN" using S.diskN_node[OF xD] S.r_diskN[of x] by simp
  have nx1: "\<not> cface (n x) x" by (rule no_cface_node[OF xD])
  have nx2: "\<not> cface (n x) y"
  proof
    assume c: "cface (n x) y"
    have "cface (e x) y" using r(1) by (simp add: rlink_def)
    then have "cface (e x) (n x)" by (rule fconnect_trans[OF _ F.fconnect_sym[OF c]])
    then have "cface (n x) (n (n x))" by (rule fconnect_trans[OF F.fconnect_sym cface_edge_nn[OF xD]])
    then show False using no_cface_node[of "n x"] nxD F.fconnect_sym by blast
  qed
  have dF: "n x \<in> S.diskF" using nxN nx1 nx2 by (simp add: S.diskF_def fband_def)
  define nex where "nex = n (e x)"
  have exD: "e x \<in> D" "nex \<in> D" using xD by (simp_all add: nex_def)
  have ex_r: "e x \<notin> set [x, y]" using ne plain_neq[OF plainG xD] by auto
  have "e x \<notin> S.diskE" using S.diskE_edge[OF xD] S.r_diskE[of x] by simp
  then have "e x \<notin> S.diskN" using ex_r by (simp add: S.diskE_def)
  then have nN: "nex \<notin> S.diskN" using S.diskN_node[OF exD(1)] by (simp add: nex_def)
  have f1: "\<not> cface nex x"
  proof
    assume c: "cface nex x"
    have nn: "n (n nex) = e x" using nnn[OF exD(1)] by (simp add: nex_def)
    have "n nex = f (e (n (n nex)))" by (simp only: nodeK)
    then have nnex: "n nex = f x" by (simp only: nn ee)
    have fxD: "f x \<in> D" using xD by simp
    have "cface (e (n nex)) nex" using fconnect_step[of f "e (n nex)"] by (simp only: nodeK)
    then have "cface (e (f x)) nex" by (simp only: nnex)
    then have a: "cface (e (f x)) x" by (rule fconnect_trans[OF _ c])
    have "cface x (f x)" by (rule fconnect_step)
    then have "cface (e (f x)) (f x)" by (rule fconnect_trans[OF a])
    then have "cface (f x) (e (f x))" by (rule F.fconnect_sym)
    moreover have "\<not> cface (f x) (e (f x))"
      using bridgelessG fxD unfolding bridgeless_def by blast
    ultimately show False by contradiction
  qed
  have f2: "\<not> cface nex y"
  proof
    assume c: "cface nex y"
    have "cface (e (n (e x))) (e x)" using fconnect_step[of f "e (n (e x))"] by (simp add: nodeK)
    moreover have "cface (e x) y" using r(1) by (simp add: rlink_def)
    ultimately have "cface (e nex) y" by (simp add: nex_def) (rule fconnect_trans)
    then have "cface nex (e nex)" by (rule fconnect_trans[OF c F.fconnect_sym])
    then show False using bridgelessG exD(2) by (simp add: bridgeless_def)
  qed
  have dFC: "nex \<in> S.diskFC" using exD(2) nN f1 f2 by (simp add: S.diskFC_def fband_def)
  show ?thesis using S.nontrivial0P dF dFC by blast
qed

lemma double_dart:
  assumes xD: "x \<in> D" and yD: "y \<in> D" and xy: "cface x y" and exy: "cface (e x) (e y)"
  shows "x = y"
proof (rule ccontr)
  assume ne: "x \<noteq> y"
  have eyD: "e y \<in> D" using yD by simp
  have "\<not> cface x (e y)"
  proof
    assume "cface x (e y)"
    then have "cface y (e y)" by (rule fconnect_trans[OF F.fconnect_sym[OF xy]])
    then show False using bridgelessG yD by (simp add: bridgeless_def)
  qed
  moreover have "rlink G x (e y)" using exy by (simp add: rlink_def)
  moreover have "rlink G (e y) x" using xy F.fconnect_sym by (simp add: rlink_def)
  ultimately have Ur: "scycle G (rlink G) [x, e y]" using scycle2[OF xD eyD] by simp
  have "e x \<noteq> e y" using ne by simp
  then have "nontrivial_ring G 0 [x, e y]" by (rule nontrivial_cycle2[OF xD eyD Ur])
  moreover have "\<not> nontrivial_ring G 0 [x, e y]" using Birkhoff[of "[x, e y]"] Ur xD eyD by simp
  ultimately show False by simp
qed

end

end
