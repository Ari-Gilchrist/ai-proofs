(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Sew.thy
    Sewing two hypermaps along a common cycle; the result satisfies the patch
    predicate.  Ported from G. Gonthier's Coq development (sew.v).
*)
theory Sew
  imports Four_Colour_Base.Patch
begin

section \<open>Position-preserving maps between lists\<close>

definition posmap :: "'a list \<Rightarrow> 'b list \<Rightarrow> 'a \<Rightarrow> 'b" where
  "posmap p q x = q ! lindex p x"

lemma posmap_mem:
  assumes len: "length p = length q" and x: "x \<in> set p"
  shows "posmap p q x \<in> set q"
proof -
  have "lindex p x < length q" using lindex_less[OF x] len by simp
  then show ?thesis by (simp add: posmap_def)
qed

lemma posmap_inv:
  assumes len: "length p = length q" and dq: "distinct q" and x: "x \<in> set p"
  shows "posmap q p (posmap p q x) = x"
proof -
  define i where "i = lindex p x"
  have i: "i < length q" using lindex_less[OF x] len by (simp add: i_def)
  have "lindex q (q ! i) = i" by (rule lindex_nth_distinct[OF dq i])
  then have "posmap q p (posmap p q x) = p ! i" by (simp add: posmap_def i_def)
  also have "\<dots> = x" unfolding i_def by (rule nth_lindex[OF x])
  finally show ?thesis .
qed

lemma posmap_prev:
  assumes len: "length p = length q" and dp: "distinct p" and dq: "distinct q" and x: "x \<in> set p"
  shows "posmap p q (prev_in p x) = prev_in q (posmap p q x)"
proof -
  define i where "i = lindex p x"
  define n where "n = length p"
  have iL: "i < n" unfolding i_def n_def by (rule lindex_less[OF x])
  have n0: "0 < n" using iL by simp
  have j: "(i + n - 1) mod n < n" using n0 by simp
  have pp: "prev_in p x = p ! ((i + n - 1) mod n)" using x by (simp add: prev_in_def i_def n_def)
  have "lindex p (prev_in p x) = (i + n - 1) mod n"
    using pp j dp by (simp add: lindex_nth_distinct n_def)
  then have l: "posmap p q (prev_in p x) = q ! ((i + n - 1) mod n)" by (simp add: posmap_def)
  have qi: "posmap p q x = q ! i" by (simp add: posmap_def i_def)
  have qin: "q ! i \<in> set q" using iL len by (simp add: n_def)
  have "lindex q (q ! i) = i" using iL len dq by (simp add: lindex_nth_distinct n_def)
  then have "prev_in q (q ! i) = q ! ((i + n - 1) mod n)" using qin len by (simp add: prev_in_def n_def)
  then show ?thesis using l qi by simp
qed

lemma posmap_next:
  assumes len: "length p = length q" and dp: "distinct p" and dq: "distinct q" and x: "x \<in> set p"
  shows "posmap p q (next_in p x) = next_in q (posmap p q x)"
proof -
  define i where "i = lindex p x"
  define n where "n = length p"
  have iL: "i < n" unfolding i_def n_def by (rule lindex_less[OF x])
  have n0: "0 < n" using iL by simp
  have j: "Suc i mod n < n" using n0 by simp
  have pp: "next_in p x = p ! (Suc i mod n)" using x by (simp add: next_in_def i_def n_def)
  have "lindex p (next_in p x) = Suc i mod n"
    using pp j dp by (simp add: lindex_nth_distinct n_def)
  then have l: "posmap p q (next_in p x) = q ! (Suc i mod n)" by (simp add: posmap_def)
  have qi: "posmap p q x = q ! i" by (simp add: posmap_def i_def)
  have qin: "q ! i \<in> set q" using iL len by (simp add: n_def)
  have "lindex q (q ! i) = i" using iL len dq by (simp add: lindex_nth_distinct n_def)
  then have "next_in q (q ! i) = q ! (Suc i mod n)" using qin len by (simp add: next_in_def n_def)
  then show ?thesis using l qi by simp
qed

section \<open>The sewing construction\<close>

locale sew_data =
  Gd: hypermap Gd + Gr: hypermap Gr
  for Gd :: "'b hypermap" and Gr :: "'c hypermap" and bGd :: "'b list" and bGr :: "'c list" +
  assumes cycle_d: "cycle (frel (edge Gd)) bGd" and simple_d: "simple Gd bGd"
    and bGd_D: "set bGd \<subseteq> darts Gd"
    and cycle_r: "cycle (frel (node Gr)) bGr" and distinct_r: "distinct bGr"
    and bGr_D: "set bGr \<subseteq> darts Gr"
    and sz: "length bGd = length bGr"
begin

lemma distinct_d: "distinct bGd" using simple_d Gd.simple_distinct by blast

definition hdr :: "'b \<Rightarrow> 'c" where "hdr = posmap bGd (rev bGr)"
definition hrd :: "'c \<Rightarrow> 'b" where "hrd = posmap (rev bGr) bGd"

lemma len_rev: "length bGd = length (rev bGr)" using sz by simp
lemma dist_rev: "distinct (rev bGr)" using distinct_r by simp

lemma hdr_mem: "xd \<in> set bGd \<Longrightarrow> hdr xd \<in> set bGr"
  using posmap_mem[OF len_rev] by (simp add: hdr_def)

lemma hrd_mem: "xr \<in> set bGr \<Longrightarrow> hrd xr \<in> set bGd"
  using posmap_mem[OF len_rev[symmetric]] by (simp add: hrd_def)

lemma hrd_hdr: "xd \<in> set bGd \<Longrightarrow> hrd (hdr xd) = xd"
  using posmap_inv[OF len_rev dist_rev] by (simp add: hdr_def hrd_def)

lemma hdr_hrd: "xr \<in> set bGr \<Longrightarrow> hdr (hrd xr) = xr"
  using posmap_inv[OF len_rev[symmetric] distinct_d] by (simp add: hdr_def hrd_def)

lemma bGd_edge: "x \<in> set bGd \<Longrightarrow> edge Gd x \<in> set bGd"
  using Gd.E.fcycle_fconnect[OF cycle_d distinct_d] fconnect_step by blast

lemma bGd_edge_iff: "edge Gd x \<in> set bGd \<longleftrightarrow> x \<in> set bGd"
proof
  assume h: "edge Gd x \<in> set bGd"
  have "fconnect (edge Gd) (edge Gd x) x" using Gd.E.fconnect_sym fconnect_step by blast
  then show "x \<in> set bGd" using Gd.E.fcycle_fconnect[OF cycle_d distinct_d h] by blast
qed (rule bGd_edge)

lemma bGr_node: "x \<in> set bGr \<Longrightarrow> node Gr x \<in> set bGr"
  using Gr.N.fcycle_fconnect[OF cycle_r distinct_r] fconnect_step by blast

lemma bGr_node_iff: "node Gr x \<in> set bGr \<longleftrightarrow> x \<in> set bGr"
proof
  assume h: "node Gr x \<in> set bGr"
  have "fconnect (node Gr) (node Gr x) x" using Gr.N.fconnect_sym fconnect_step by blast
  then show "x \<in> set bGr" using Gr.N.fcycle_fconnect[OF cycle_r distinct_r h] by blast
qed (rule bGr_node)

lemma node_face_prev: "xd \<in> set bGd \<Longrightarrow> node Gd (face Gd xd) = prev_in bGd xd"
proof -
  assume xd: "xd \<in> set bGd"
  define y where "y = node Gd (face Gd xd)"
  have ey: "edge Gd y = xd" unfolding y_def by (rule Gd.faceK)
  have yb: "y \<in> set bGd" using bGd_edge_iff[of y] ey xd by simp
  have "next_in bGd y = xd" using cycle_next_in[OF cycle_d yb] ey by simp
  then show ?thesis using prev_next_in[OF distinct_d yb] by (simp add: y_def)
qed

lemma node_hdr: "xd \<in> set bGd \<Longrightarrow> node Gr (hdr xd) = hdr (node Gd (face Gd xd))"
proof -
  assume xd: "xd \<in> set bGd"
  have hb: "hdr xd \<in> set bGr" by (rule hdr_mem[OF xd])
  have "node Gr (hdr xd) = next_in bGr (hdr xd)" by (rule cycle_next_in[OF cycle_r hb])
  also have "\<dots> = prev_in (rev bGr) (hdr xd)"
    using next_in_rev[OF dist_rev, of "hdr xd"] hb by simp
  also have "\<dots> = hdr (prev_in bGd xd)"
    using posmap_prev[OF len_rev distinct_d dist_rev xd] by (simp add: hdr_def)
  also have "\<dots> = hdr (node Gd (face Gd xd))" using node_face_prev[OF xd] by simp
  finally show ?thesis .
qed

lemma edge_hrd: "xr \<in> set bGr \<Longrightarrow> edge Gd (hrd xr) = hrd (face Gr (edge Gr xr))"
proof -
  assume xr: "xr \<in> set bGr"
  define yr where "yr = face Gr (edge Gr xr)"
  have nyr: "node Gr yr = xr" unfolding yr_def by (rule Gr.edgeK)
  have yb: "yr \<in> set bGr" using bGr_node_iff[of yr] nyr xr by simp
  define yd where "yd = hrd yr"
  have ydb: "yd \<in> set bGd" using hrd_mem[OF yb] by (simp add: yd_def)
  have "hdr (node Gd (face Gd yd)) = node Gr (hdr yd)" using node_hdr[OF ydb] by simp
  also have "hdr yd = yr" using hdr_hrd[OF yb] by (simp add: yd_def)
  finally have "hdr (node Gd (face Gd yd)) = xr" using nyr by simp
  then have "hrd xr = node Gd (face Gd yd)"
    using hrd_hdr[of "node Gd (face Gd yd)"] node_face_prev[OF ydb] prev_in_mem[OF ydb] by simp
  then have "edge Gd (hrd xr) = yd" by (simp add: Gd.faceK)
  then show ?thesis by (simp add: yd_def yr_def)
qed

definition sew_darts :: "('b + 'c) set" where
  "sew_darts = Inl ` darts Gd \<union> Inr ` (darts Gr - set bGr)"

definition sewr :: "'c \<Rightarrow> 'b + 'c" where
  "sewr xr = (if xr \<in> set bGr then Inl (hrd xr) else Inr xr)"

definition sew_edge :: "'b + 'c \<Rightarrow> 'b + 'c" where
  "sew_edge w = (if w \<notin> sew_darts then w else (case w of
      Inl xd \<Rightarrow> if xd \<in> set bGd then sewr (edge Gr (hdr xd)) else Inl (edge Gd xd)
    | Inr xr \<Rightarrow> sewr (edge Gr xr)))"

definition sew_face_r :: "'c \<Rightarrow> 'b + 'c" where
  "sew_face_r xr = (case sewr (face Gr xr) of Inl xd \<Rightarrow> Inl (face Gd xd) | w \<Rightarrow> w)"

definition sew_face :: "'b + 'c \<Rightarrow> 'b + 'c" where
  "sew_face w = (if w \<notin> sew_darts then w else (case w of
      Inl xd \<Rightarrow> if xd \<in> set bGd then sew_face_r (hdr xd) else Inl (face Gd xd)
    | Inr xr \<Rightarrow> sew_face_r xr))"

definition sew_node :: "'b + 'c \<Rightarrow> 'b + 'c" where
  "sew_node w = (if w \<notin> sew_darts then w else (case w of
      Inl xd \<Rightarrow> Inl (node Gd xd) | Inr xr \<Rightarrow> sewr (node Gr xr)))"

definition sew_map :: "('b + 'c) hypermap" where
  "sew_map = \<lparr>darts = sew_darts, edge = sew_edge, node = sew_node, face = sew_face\<rparr>"

lemma sewr_D: "xr \<in> darts Gr \<Longrightarrow> sewr xr \<in> sew_darts"
  using hrd_mem bGd_D by (auto simp: sewr_def sew_darts_def)

lemma Inl_D [simp]: "Inl xd \<in> sew_darts \<longleftrightarrow> xd \<in> darts Gd"
  by (auto simp: sew_darts_def)

lemma Inr_D [simp]: "Inr xr \<in> sew_darts \<longleftrightarrow> xr \<in> darts Gr \<and> xr \<notin> set bGr"
  by (auto simp: sew_darts_def)

lemma sew_edge_D:
  assumes w: "w \<in> sew_darts"
  shows "sew_edge w \<in> sew_darts"
proof (cases w)
  case (Inl xd)
  then have xd: "xd \<in> darts Gd" using w by simp
  show ?thesis
  proof (cases "xd \<in> set bGd")
    case True
    have "edge Gr (hdr xd) \<in> darts Gr" using hdr_mem[OF True] bGr_D by auto
    then show ?thesis using Inl w True sewr_D by (simp add: sew_edge_def)
  next
    case False
    then show ?thesis using Inl w xd by (simp add: sew_edge_def)
  qed
next
  case (Inr xr)
  then have "edge Gr xr \<in> darts Gr" using w by simp
  then show ?thesis using Inr w sewr_D by (simp add: sew_edge_def)
qed

lemma sew_node_D: "w \<in> sew_darts \<Longrightarrow> sew_node w \<in> sew_darts"
  using sewr_D by (auto simp: sew_node_def split: sum.splits)

lemma sew_face_r_D: "xr \<in> darts Gr \<Longrightarrow> sew_face_r xr \<in> sew_darts"
proof -
  assume xr: "xr \<in> darts Gr"
  have "sewr (face Gr xr) \<in> sew_darts" using sewr_D xr by simp
  then show ?thesis by (auto simp: sew_face_r_def split: sum.splits)
qed

lemma sew_face_D:
  assumes w: "w \<in> sew_darts"
  shows "sew_face w \<in> sew_darts"
proof (cases w)
  case (Inl xd)
  then have xd: "xd \<in> darts Gd" using w by simp
  show ?thesis
  proof (cases "xd \<in> set bGd")
    case True
    have "hdr xd \<in> darts Gr" using hdr_mem[OF True] bGr_D by blast
    then show ?thesis using Inl w True sew_face_r_D by (simp add: sew_face_def)
  next
    case False
    then show ?thesis using Inl w xd by (simp add: sew_face_def)
  qed
next
  case (Inr xr)
  then have "xr \<in> darts Gr" using w by simp
  then show ?thesis using Inr w sew_face_r_D by (simp add: sew_face_def)
qed

lemma sew_cancel3: "sew_node (sew_face (sew_edge w)) = w"
proof (cases "w \<in> sew_darts")
  case False
  then show ?thesis by (simp add: sew_edge_def sew_face_def sew_node_def)
next
  case True
  show ?thesis
  proof (cases w)
    case (Inl xd)
    then have xd: "xd \<in> darts Gd" using True by simp
    show ?thesis
    proof (cases "xd \<in> set bGd")
      case False
      have exd: "edge Gd xd \<in> darts Gd" "edge Gd xd \<notin> set bGd" using xd False bGd_edge_iff by simp_all
      have "sew_edge w = Inl (edge Gd xd)" using Inl True False by (simp add: sew_edge_def)
      then show ?thesis using exd xd Inl by (simp add: sew_face_def sew_node_def Gd.edgeK)
    next
      case xb: True
      define exr where "exr = edge Gr (hdr xd)"
      have hb: "hdr xd \<in> set bGr" by (rule hdr_mem[OF xb])
      have exrD: "exr \<in> darts Gr" using hb bGr_D by (auto simp: exr_def)
      have fexr: "face Gr exr \<in> set bGr"
        using bGr_node_iff[of "face Gr exr"] Gr.edgeK[of "hdr xd"] hb by (simp add: exr_def)
      have e: "sew_edge w = sewr exr" using Inl True xb by (simp add: sew_edge_def exr_def)
      have f: "sew_face (sewr exr) = sew_face_r exr"
      proof (cases "exr \<in> set bGr")
        case True
        then have "sewr exr = Inl (hrd exr)" by (simp add: sewr_def)
        moreover have "hrd exr \<in> set bGd" using hrd_mem[OF True] .
        moreover have "hrd exr \<in> darts Gd" using hrd_mem[OF True] bGd_D by blast
        ultimately show ?thesis using hdr_hrd[OF True] by (simp add: sew_face_def)
      next
        case False
        then show ?thesis using exrD by (simp add: sewr_def sew_face_def)
      qed
      have "sew_face_r exr = Inl (face Gd (hrd (face Gr exr)))"
        using fexr by (simp add: sew_face_r_def sewr_def)
      also have "hrd (face Gr exr) = edge Gd (hrd (hdr xd))"
        using edge_hrd[OF hb] by (simp add: exr_def)
      also have "hrd (hdr xd) = xd" by (rule hrd_hdr[OF xb])
      finally have fr: "sew_face_r exr = Inl (face Gd (edge Gd xd))" .
      have "Inl (face Gd (edge Gd xd)) \<in> sew_darts" using xd by simp
      then show ?thesis using e f fr Inl by (simp add: sew_node_def Gd.edgeK)
    qed
  next
    case (Inr xr)
    then have xr: "xr \<in> darts Gr" "xr \<notin> set bGr" using True by simp_all
    define exr where "exr = edge Gr xr"
    have exrD: "exr \<in> darts Gr" using xr by (simp add: exr_def)
    have fexr: "face Gr exr \<notin> set bGr"
      using bGr_node_iff[of "face Gr exr"] Gr.edgeK[of xr] xr(2) by (simp add: exr_def)
    have e: "sew_edge w = sewr exr" using Inr True by (simp add: sew_edge_def exr_def)
    have f: "sew_face (sewr exr) = sew_face_r exr"
    proof (cases "exr \<in> set bGr")
      case True
      then have "sewr exr = Inl (hrd exr)" by (simp add: sewr_def)
      moreover have "hrd exr \<in> set bGd" using hrd_mem[OF True] .
      moreover have "hrd exr \<in> darts Gd" using hrd_mem[OF True] bGd_D by blast
      ultimately show ?thesis using hdr_hrd[OF True] by (simp add: sew_face_def)
    next
      case False
      then show ?thesis using exrD by (simp add: sewr_def sew_face_def)
    qed
    have fr: "sew_face_r exr = Inr (face Gr exr)" using fexr by (simp add: sew_face_r_def sewr_def)
    have "Inr (face Gr exr) \<in> sew_darts" using fexr exrD by simp
    then show ?thesis using e f fr Inr xr by (simp add: sew_node_def sewr_def exr_def Gr.edgeK)
  qed
qed

lemma hypermap_sew: "hypermap sew_map"
proof -
  have fin: "finite sew_darts" using Gd.finite_darts Gr.finite_darts by (simp add: sew_darts_def)
  have outE: "w \<notin> sew_darts \<Longrightarrow> sew_edge w = w" for w by (simp add: sew_edge_def)
  have outN: "w \<notin> sew_darts \<Longrightarrow> sew_node w = w" for w by (simp add: sew_node_def)
  have outF: "w \<notin> sew_darts \<Longrightarrow> sew_face w = w" for w by (simp add: sew_face_def)
  have injE: "inj_on sew_edge sew_darts"
  proof (rule inj_onI)
    fix x y assume "x \<in> sew_darts" "y \<in> sew_darts" "sew_edge x = sew_edge y"
    then show "x = y" using sew_cancel3 by metis
  qed
  have pE: "sew_edge permutes sew_darts" by (rule perm_of_inj[OF fin sew_edge_D injE outE])
  have surjN: "sew_node ` sew_darts = sew_darts"
  proof
    show "sew_node ` sew_darts \<subseteq> sew_darts" using sew_node_D by blast
    show "sew_darts \<subseteq> sew_node ` sew_darts"
    proof
      fix w assume w: "w \<in> sew_darts"
      have "sew_face (sew_edge w) \<in> sew_darts" using w sew_edge_D sew_face_D by blast
      then show "w \<in> sew_node ` sew_darts" using sew_cancel3[of w] by (metis image_eqI)
    qed
  qed
  have injN: "inj_on sew_node sew_darts"
    using surjN fin by (simp add: eq_card_imp_inj_on)
  have pN: "sew_node permutes sew_darts" by (rule perm_of_inj[OF fin sew_node_D injN outN])
  have injF: "inj_on sew_face sew_darts"
  proof (rule inj_onI)
    fix x y assume x: "x \<in> sew_darts" and y: "y \<in> sew_darts" and eq: "sew_face x = sew_face y"
    have "sew_edge ` sew_darts = sew_darts" using permutes_image[OF pE] .
    then obtain x0 y0 where x0: "x0 \<in> sew_darts" "x = sew_edge x0" and y0: "y0 \<in> sew_darts" "y = sew_edge y0"
      using x y by (metis imageE)
    have "x0 = y0" using eq x0 y0 sew_cancel3 by metis
    then show "x = y" using x0 y0 by simp
  qed
  have pF: "sew_face permutes sew_darts" by (rule perm_of_inj[OF fin sew_face_D injF outF])
  show ?thesis
    by unfold_locales (simp_all add: sew_map_def fin pE pN pF sew_cancel3)
qed

lemma sewr_border: "xr \<in> set bGr \<Longrightarrow> sewr xr = Inl (hrd xr)"
  by (simp add: sewr_def)

lemma inj_sewr: "inj_on sewr (darts Gr)"
proof (rule inj_onI)
  fix x y assume x: "x \<in> darts Gr" and y: "y \<in> darts Gr" and eq: "sewr x = sewr y"
  show "x = y"
  proof (cases "x \<in> set bGr")
    case True
    then have yb: "y \<in> set bGr" using eq by (auto simp: sewr_def split: if_splits)
    have "hrd x = hrd y" using eq True yb by (simp add: sewr_def)
    then show ?thesis using hdr_hrd True yb by metis
  next
    case False
    then have "y \<notin> set bGr" using eq by (auto simp: sewr_def split: if_splits)
    then show ?thesis using eq False by (simp add: sewr_def)
  qed
qed

lemma map_sewr: "map sewr bGr = rev (map Inl bGd)"
proof (rule nth_equalityI)
  show "length (map sewr bGr) = length (rev (map Inl bGd))" using sz by simp
next
  fix i assume i: "i < length (map sewr bGr)"
  then have ir: "i < length bGr" by simp
  have bi: "bGr ! i \<in> set bGr" using ir by simp
  have "lindex (rev bGr) (bGr ! i) = length bGr - 1 - i"
    using lindex_rev[OF distinct_r bi] lindex_nth_distinct[OF distinct_r ir] by simp
  then have "hrd (bGr ! i) = bGd ! (length bGd - 1 - i)" using sz by (simp add: hrd_def posmap_def)
  then show "map sewr bGr ! i = rev (map Inl bGd) ! i"
    using ir bi sz by (simp add: sewr_def rev_nth)
qed

theorem sew_map_patch: "patch sew_map Gd Gr Inl sewr bGd bGr"
proof -
  interpret S: hypermap sew_map by (rule hypermap_sew)
  show ?thesis
  proof unfold_locales
    show "inj_on Inl (darts Gd)" by simp
    show "inj_on sewr (darts Gr)" by (rule inj_sewr)
    show "map sewr bGr = rev (map Inl bGd)" by (rule map_sewr)
    show "Inl ` darts Gd \<subseteq> darts sew_map" by (auto simp: sew_map_def)
    show "sewr ` darts Gr = (darts sew_map - Inl ` darts Gd) \<union> set (map Inl bGd)"
    proof
      show "sewr ` darts Gr \<subseteq> (darts sew_map - Inl ` darts Gd) \<union> set (map Inl bGd)"
        using hrd_mem by (auto simp: sewr_def sew_map_def sew_darts_def)
      show "(darts sew_map - Inl ` darts Gd) \<union> set (map Inl bGd) \<subseteq> sewr ` darts Gr"
      proof
        fix w assume w: "w \<in> (darts sew_map - Inl ` darts Gd) \<union> set (map Inl bGd)"
        show "w \<in> sewr ` darts Gr"
        proof (cases "w \<in> set (map Inl bGd)")
          case True
          then obtain xd where xd: "xd \<in> set bGd" "w = Inl xd" by auto
          have "sewr (hdr xd) = Inl xd" using hdr_mem[OF xd(1)] hrd_hdr[OF xd(1)] by (simp add: sewr_def)
          moreover have "hdr xd \<in> darts Gr" using hdr_mem[OF xd(1)] bGr_D by blast
          ultimately show ?thesis using xd(2) by (metis image_eqI)
        next
          case False
          then obtain xr where xr: "w = Inr xr" "xr \<in> darts Gr" "xr \<notin> set bGr"
            using w by (auto simp: sew_map_def sew_darts_def)
          then have "sewr xr = w" by (simp add: sewr_def)
          then show ?thesis using xr(2) by (metis image_eqI)
        qed
      qed
    qed
    show "\<And>x. x \<in> darts Gd \<Longrightarrow> x \<notin> set bGd \<Longrightarrow> Inl (edge Gd x) = edge sew_map (Inl x)"
      by (simp add: sew_map_def sew_edge_def)
    show "\<And>x. x \<in> darts Gd \<Longrightarrow> Inl (node Gd x) = node sew_map (Inl x)"
      by (simp add: sew_map_def sew_node_def)
    show "\<And>x. x \<in> darts Gr \<Longrightarrow> sewr (edge Gr x) = edge sew_map (sewr x)"
    proof -
      fix x assume x: "x \<in> darts Gr"
      show "sewr (edge Gr x) = edge sew_map (sewr x)"
      proof (cases "x \<in> set bGr")
        case True
        have "hrd x \<in> set bGd" "hrd x \<in> darts Gd" using hrd_mem[OF True] bGd_D by blast+
        then show ?thesis using True hdr_hrd[OF True] by (simp add: sew_map_def sew_edge_def sewr_def)
      next
        case False
        then show ?thesis using x by (simp add: sew_map_def sew_edge_def sewr_def)
      qed
    qed
    show "\<And>x. x \<in> darts Gr \<Longrightarrow> x \<notin> set bGr \<Longrightarrow> sewr (node Gr x) = node sew_map (sewr x)"
      by (simp add: sew_map_def sew_node_def sewr_def)
  qed (simp_all add: cycle_d simple_d bGd_D cycle_r distinct_r bGr_D)
qed

end

end
