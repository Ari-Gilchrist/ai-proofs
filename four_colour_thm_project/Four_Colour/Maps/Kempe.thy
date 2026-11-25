(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Kempe.thy
    Kempe closure of the ring traces of planar plain quasicubic hypermaps.
    Ported from G. Gonthier's Coq development (kempe.v).
*)
theory Kempe
  imports Chromogram Four_Colour_Base.Coloring Four_Colour_Base.Euler_Tree
begin

section \<open>Chromogram transformations\<close>

text \<open>Negate the parity bit of the first unmatched pop.\<close>

fun gram_neg_rec :: "nat \<Rightarrow> chromogram \<Rightarrow> chromogram" where
  "gram_neg_rec n (Gpush # w) = Gpush # gram_neg_rec (Suc n) w"
| "gram_neg_rec n (Gskip # w) = Gskip # gram_neg_rec n w"
| "gram_neg_rec (Suc n) (Gpop0 # w) = Gpop0 # gram_neg_rec n w"
| "gram_neg_rec (Suc n) (Gpop1 # w) = Gpop1 # gram_neg_rec n w"
| "gram_neg_rec 0 (Gpop0 # w) = Gpop1 # w"
| "gram_neg_rec 0 (Gpop1 # w) = Gpop0 # w"
| "gram_neg_rec n [] = []"

definition gram_neg :: "chromogram \<Rightarrow> chromogram" where
  "gram_neg = gram_neg_rec 0"

lemma mstep_append:
  "lb \<noteq> [] \<or> s = Gpush \<or> s = Gskip \<Longrightarrow> mstep e s (lb @ l) = map_option (\<lambda>x. x @ l) (mstep e s lb)"
  by (induction e s lb rule: mstep.induct) auto

lemma matchg_Nil_len: "length w \<noteq> length et \<Longrightarrow> \<not> matchg lb et w"
  using matchg_size by blast

lemma match_gram_neg_gen:
  "matchg (lb @ [b0]) et (gram_neg_rec (length lb) w) = matchg (lb @ [\<not> b0]) et w"
proof (induction w arbitrary: et lb)
  case Nil
  then show ?case by (cases et) simp_all
next
  case (Cons s w)
  show ?case
  proof (cases et)
    case Nil
    then show ?thesis by (cases s; cases lb) simp_all
  next
    case (Cons e et')
    show ?thesis
    proof (cases s)
      case Gpush
      have "gram_neg_rec (length lb) (s # w) = Gpush # gram_neg_rec (length (x # lb)) w" for x
        using Gpush by simp
      then show ?thesis using Gpush Cons Cons.IH[of "False # lb" et'] Cons.IH[of "True # lb" et']
        by (cases e) (simp_all add: mstep_append)
    next
      case Gskip
      then show ?thesis using Cons Cons.IH[of lb et'] by (cases e) (simp_all add: mstep_append)
    next
      case Gpop0
      show ?thesis
      proof (cases lb)
        case Nil
        then show ?thesis using Gpop0 Cons by (cases e; cases b0) simp_all
      next
        case (Cons y lb')
        then show ?thesis using Gpop0 \<open>et = e # et'\<close> Cons.IH[of lb' et']
          by (cases e; cases y) simp_all
      qed
    next
      case Gpop1
      show ?thesis
      proof (cases lb)
        case Nil
        then show ?thesis using Gpop1 Cons by (cases e; cases b0) simp_all
      next
        case (Cons y lb')
        then show ?thesis using Gpop1 \<open>et = e # et'\<close> Cons.IH[of lb' et']
          by (cases e; cases y) simp_all
      qed
    qed
  qed
qed

lemma match_gram_neg: "matchg [b0] et (gram_neg w) = matchg [\<not> b0] et w"
  using match_gram_neg_gen[of "[]" b0 et w] by (simp add: gram_neg_def)

text \<open>Change the next unmatched pop into a push, adjusting the following pop.\<close>

fun gram_flip_rec :: "nat \<Rightarrow> chromogram \<Rightarrow> chromogram" where
  "gram_flip_rec n (Gpush # w) = Gpush # gram_flip_rec (Suc n) w"
| "gram_flip_rec n (Gskip # w) = Gskip # gram_flip_rec n w"
| "gram_flip_rec (Suc n) (Gpop0 # w) = Gpop0 # gram_flip_rec n w"
| "gram_flip_rec (Suc n) (Gpop1 # w) = Gpop1 # gram_flip_rec n w"
| "gram_flip_rec 0 (Gpop0 # w) = Gpush # gram_neg w"
| "gram_flip_rec 0 (Gpop1 # w) = Gpush # w"
| "gram_flip_rec n [] = [Gpush]"

definition gram_flip :: "chromogram \<Rightarrow> chromogram" where
  "gram_flip = gram_flip_rec 0"

lemma match_gram_flip_gen:
  "matchg lb et (gram_flip_rec (length lb) w) =
     (matchg (lb @ [True, False]) et w \<or> matchg (lb @ [False, True]) et w)"
proof (induction w arbitrary: et lb)
  case Nil
  show ?case
  proof (cases et)
    case Nil
    then show ?thesis by simp
  next
    case (Cons e et')
    then show ?thesis by (cases e; cases et') (simp_all split: option.splits)
  qed
next
  case (Cons s w)
  show ?case
  proof (cases et)
    case Nil
    then show ?thesis by (cases s; cases lb) simp_all
  next
    case (Cons e et')
    show ?thesis
    proof (cases s)
      case Gpush
      have "gram_flip_rec (length lb) (s # w) = Gpush # gram_flip_rec (length (x # lb)) w" for x
        using Gpush by simp
      then show ?thesis using Gpush Cons Cons.IH[of "False # lb" et'] Cons.IH[of "True # lb" et']
        by (cases e) (simp_all add: mstep_append)
    next
      case Gskip
      then show ?thesis using Cons Cons.IH[of lb et'] by (cases e) (simp_all add: mstep_append)
    next
      case Gpop0
      show ?thesis
      proof (cases lb)
        case Nil
        then show ?thesis using Gpop0 Cons by (cases e) (simp_all add: match_gram_neg)
      next
        case (Cons y lb')
        then show ?thesis using Gpop0 \<open>et = e # et'\<close> Cons.IH[of lb' et']
          by (cases e; cases y) simp_all
      qed
    next
      case Gpop1
      show ?thesis
      proof (cases lb)
        case Nil
        then show ?thesis using Gpop1 Cons by (cases e) simp_all
      next
        case (Cons y lb')
        then show ?thesis using Gpop1 \<open>et = e # et'\<close> Cons.IH[of lb' et']
          by (cases e; cases y) simp_all
      qed
    qed
  qed
qed

lemma match_gram_flip:
  "matchg [] et (gram_flip w) = (matchg [True, False] et w \<or> matchg [False, True] et w)"
  using match_gram_flip_gen[of "[]" et w] by (simp add: gram_flip_def)

text \<open>Rotation of a balanced chromogram.\<close>

definition gram_rot :: "chromogram \<Rightarrow> chromogram" where
  "gram_rot w = (if \<exists>b. gram_balanced 0 b w then
      (case w of Gpush # w' \<Rightarrow> gram_flip (w' @ [Gpop1]) | Gskip # w' \<Rightarrow> w' @ [Gskip] | _ \<Rightarrow> w)
    else w)"

lemma matchg_w_Nil [simp]: "matchg lb et [] \<longleftrightarrow> et = [] \<and> lb = []"
  by (cases et) auto

lemma matchg_et_Nil [simp]: "matchg lb [] w \<longleftrightarrow> w = [] \<and> lb = []"
  by (cases w) auto

lemma matchg_snoc_skip:
  "matchg lb (et @ [e]) (w @ [Gskip]) = (e = Color1 \<and> matchg lb et w)"
proof (induction w arbitrary: lb et)
  case Nil
  show ?case
  proof (cases et)
    case Nil
    then show ?thesis by (cases e) simp_all
  next
    case (Cons x xs)
    then show ?thesis by (simp split: option.splits)
  qed
next
  case (Cons s w)
  show ?case
  proof (cases et)
    case Nil
    then show ?thesis by (simp split: option.splits)
  next
    case (Cons x xs)
    then show ?thesis using Cons.IH by (simp split: option.splits)
  qed
qed

lemma matchg_snoc_pop1:
  "gram_balanced (length lb) b0 w \<Longrightarrow>
   matchg (b # lb) (et @ [e]) (w @ [Gpop1]) =
     (e = ccons True (\<not> last (b # lb)) \<and> matchg (butlast (b # lb)) et w)"
proof (induction w arbitrary: lb b b0 et)
  case Nil
  then have lb: "lb = []" by (cases lb) simp_all
  show ?case
  proof (cases et)
    case Nil
    then show ?thesis using lb by (cases e; cases b) simp_all
  next
    case (Cons e' et')
    then show ?thesis using lb matchg_Nil_len[of "[Gpop1]" "e' # et' @ [e]" "[b]"] by simp
  qed
next
  case (Cons s w)
  show ?case
  proof (cases et)
    case Nil
    have "\<not> matchg (b # lb) [e] (s # w @ [Gpop1])" by (rule matchg_Nil_len) simp
    then show ?thesis using Nil by simp
  next
    case (Cons e' et')
    show ?thesis
    proof (cases s)
      case Gpush
      have bal: "gram_balanced (length (b # lb)) b0 w"
        using Cons.prems Gpush by simp
      have bl: "butlast (x # b # lb) = x # butlast (b # lb)" for x by simp
      show ?thesis using Gpush Cons Cons.IH[OF bal] bl
        by (cases e') (simp_all del: butlast.simps)
    next
      case Gskip
      have bal: "gram_balanced (length lb) (\<not> b0) w" using Cons.prems Gskip by simp
      show ?thesis using Gskip Cons Cons.IH[OF bal] by (cases e') simp_all
    next
      case Gpop0
      then obtain y lb' where lb: "lb = y # lb'" using Cons.prems by (cases lb) auto
      have bal: "gram_balanced (length lb') b0 w" using Cons.prems Gpop0 lb by simp
      show ?thesis using Gpop0 Cons lb Cons.IH[OF bal] by (cases e'; cases b) simp_all
    next
      case Gpop1
      then obtain y lb' where lb: "lb = y # lb'" using Cons.prems by (cases lb) auto
      have bal: "gram_balanced (length lb') (\<not> b0) w" using Cons.prems Gpop1 lb by simp
      show ?thesis using Gpop1 Cons lb Cons.IH[OF bal] by (cases e'; cases b) simp_all
    qed
  qed
qed

lemma gram_flip_rec_ne: "gram_flip_rec n w \<noteq> []"
  by (induction n w rule: gram_flip_rec.induct) simp_all

lemma match_gram_rot: "matchg [] (rot 1 et) (gram_rot w) = matchg [] et w"
proof (cases "\<exists>b. gram_balanced 0 b w")
  case False
  then have gw: "gram_rot w = w" by (simp add: gram_rot_def)
  have "\<not> matchg [] et' w" for et' using matchg_balanced[of et' w] False by blast
  then show ?thesis using gw by simp
next
  case True
  then obtain b0 where bal: "gram_balanced 0 b0 w" by blast
  show ?thesis
  proof (cases et)
    case Nil
    have "gram_rot w = [] \<longleftrightarrow> w = []"
      by (cases w) (auto simp: gram_rot_def gram_flip_def gram_flip_rec_ne split: gram_symbol.splits)
    then show ?thesis using Nil by (cases "gram_rot w"; cases w) (simp_all add: rot_def)
  next
    case (Cons e et')
    have r: "rot 1 et = et' @ [e]" unfolding Cons by (rule rot1_Cons)
    show ?thesis
    proof (cases w)
      case Nil
      then show ?thesis using r Cons by (simp add: gram_rot_def matchg_Nil_len)
    next
      case (Cons s w')
      show ?thesis
      proof (cases s)
        case Gpush
        have gw: "gram_rot w = gram_flip (w' @ [Gpop1])" using True Cons Gpush by (simp add: gram_rot_def)
        have bal1: "gram_balanced (length [x]) b0 w'" for x using bal Cons Gpush by simp
        show ?thesis
          using gw r \<open>et = e # et'\<close> Cons Gpush matchg_snoc_pop1[OF bal1[of False], where b=True and et=et' and e=e]
            matchg_snoc_pop1[OF bal1[of True], where b=False and et=et' and e=e]
          by (cases e) (simp_all add: match_gram_flip)
      next
        case Gskip
        have gw: "gram_rot w = w' @ [Gskip]" using True Cons Gskip by (simp add: gram_rot_def)
        show ?thesis using gw r \<open>et = e # et'\<close> Cons Gskip matchg_snoc_skip
          by (cases e) simp_all
      next
        case Gpop0
        have gw: "gram_rot w = w" using Cons Gpop0 by (simp add: gram_rot_def)
        show ?thesis using gw r \<open>et = e # et'\<close> Cons Gpop0 by (cases et'; cases e) simp_all
      next
        case Gpop1
        have gw: "gram_rot w = w" using Cons Gpop1 by (simp add: gram_rot_def)
        show ?thesis using gw r \<open>et = e # et'\<close> Cons Gpop1 by (cases et'; cases e) simp_all
      qed
    qed
  qed
qed

subsection \<open>Chromogram bookkeeping for the contraction step\<close>

lemma match2_skip_skip:
  "matchg [] (a # b # t) (Gskip # Gskip # w) \<longleftrightarrow> a = Color1 \<and> b = Color1 \<and> matchg [] t w"
  by (cases a; cases b) simp_all

lemma match2_push_pop0:
  "matchg [] (a # b # t) (Gpush # Gpop0 # w) \<longleftrightarrow> a = b \<and> (a = Color2 \<or> a = Color3) \<and> matchg [] t w"
  by (cases a; cases b) simp_all

definition gram_P12 :: "gram_symbol \<Rightarrow> gram_symbol \<Rightarrow> bool" where
  "gram_P12 s1 s2 \<longleftrightarrow> (if s1 = Gpush then s2 \<noteq> Gpop0 else s1 = Gskip \<and> s2 = Gpush)"

definition gram_W :: "gram_symbol \<Rightarrow> gram_symbol \<Rightarrow> chromogram \<Rightarrow> chromogram" where
  "gram_W s1 s2 w1 = (if s1 = Gskip \<or> s2 = Gskip then Gpush # gram_neg w1
                      else Gskip # (if s2 = Gpush then gram_flip w1 else w1))"

lemma gram_P12I:
  "e1 \<noteq> Color0 \<Longrightarrow> matchg [] (e2 # (e2 +c e1) # rest) (s1 # s2 # w1) \<Longrightarrow> gram_P12 s1 s2"
  by (cases e2; cases e1; cases s1; cases s2) (simp_all add: gram_P12_def)

lemma gram_W_fwd:
  "e1 \<noteq> Color0 \<Longrightarrow> matchg [] (e2 # (e2 +c e1) # rest) (s1 # s2 # w1) \<Longrightarrow>
   matchg [] (e1 # rest) (gram_W s1 s2 w1)"
  by (cases e2; cases e1; cases s1; cases s2)
     (simp_all add: gram_W_def match_gram_neg match_gram_flip)

definition gram_e0 :: "gram_symbol \<Rightarrow> gram_symbol \<Rightarrow> chromogram \<Rightarrow> color \<Rightarrow> colseq \<Rightarrow> color" where
  "gram_e0 s1 s2 w1 e et = (if s1 = Gskip then Color1 else if s2 = Gskip then Color1 +c e
     else ccons True (s2 = Gpush \<and> matchg [False, True] et w1))"

lemma gram_W_bwd:
  "gram_P12 s1 s2 \<Longrightarrow> matchg [] (e # et) (gram_W s1 s2 w1) \<Longrightarrow>
   matchg [] (gram_e0 s1 s2 w1 e et # (gram_e0 s1 s2 w1 e et +c e) # et) (s1 # s2 # w1)"
  by (cases e; cases s1; cases s2; cases "matchg [False, True] et w1")
     (auto simp: gram_P12_def gram_W_def gram_e0_def match_gram_neg match_gram_flip)


section \<open>The Kempe closure theorem: the contraction step\<close>

locale kempe_step = hypermap +
  fixes z :: 'a and p1 :: "'a list"
  assumes planarG: "planar G" and plainG: "plain G" and zD: "z \<in> D"
    and n'id: "\<And>x. x \<in> D \<Longrightarrow> n x \<noteq> x"
    and cycq: "cycle (frel n) (z # n z # p1)" and distq: "distinct (z # n z # p1)"
    and qcub: "quasicubic G (z # n z # p1)"
    and Dfz: "f z = z \<or> f z \<notin> set (z # n z # p1)"
begin

abbreviation q :: "'a list" where "q \<equiv> z # n z # p1"

lemma ee [simp]: "e (e x) = x" using plainG by (rule plain_eq)

lemma e'id: "x \<in> D \<Longrightarrow> e x \<noteq> x" using plainG by (rule plain_neq)

lemma nf_e [simp]: "n (f x) = e x" using plainG by (rule plain_eq')

lemma ezD: "e z \<in> D" using zD by simp

lemma ez_z: "e z \<noteq> z" using e'id[OF zD] .

lemma fz_ez: "f z \<noteq> e z"
proof
  assume "f z = e z"
  then have "n (e z) = e z" using nf_e[of z] by simp
  then show False using n'id ezD by blast
qed

lemma fez_z: "f (e z) \<noteq> z"
proof
  assume "f (e z) = z"
  then have "n z = z" using edgeK[of z] by simp
  then show False using n'id zD by blast
qed

lemma q_cnode: "x \<in> set q \<longleftrightarrow> cnode z x"
  using N.fcycle_fconnect[OF cycq distq, of z x] by simp

lemma qD: "set q \<subseteq> D"
proof
  fix x assume "x \<in> set q"
  then have "cnode z x" using q_cnode by simp
  then show "x \<in> D" using N.fconnect_in_D zD by blast
qed

lemma q_closed: "x \<in> set q \<Longrightarrow> n x \<in> set q"
  using q_cnode fconnect_stepI_r by metis

lemma q_closed_inv: "n x \<in> set q \<Longrightarrow> x \<in> set q"
  using q_cnode N.fconnect_sym fconnect_trans fconnect_step
  by (metis N.fconnect_f_right)

definition H :: "'a hypermap" where
  "H = WalkupE (WalkupN G z) (e z)"

abbreviation DH :: "'a set" where "DH \<equiv> D - {z} - {e z}"

lemma W_hyp: "hypermap (WalkupN G z)" by (rule hypermap_WalkupN)

lemma hypermap_H: "hypermap H"
proof -
  interpret W: hypermap "WalkupN G z" by (rule W_hyp)
  show ?thesis unfolding H_def by (rule W.hypermap_WalkupE)
qed

lemma darts_H [simp]: "darts H = DH"
  by (simp add: H_def)

lemma edge_H_fun: "edge H = skip (e z) (skip z e)"
proof -
  interpret W: hypermap "WalkupN G z" by (rule W_hyp)
  have "glink (WalkupN G z) (e z) (e z)"
    using ez_z by (simp add: glink_def skip_def)
  then show ?thesis unfolding H_def using W.glink_fp_skip_edge by (simp add: fun_eq_iff)
qed

lemma edge_H: "u \<in> DH \<Longrightarrow> edge H u = e u"
proof -
  assume u: "u \<in> DH"
  have "e u \<noteq> z"
  proof
    assume "e u = z"
    then have "u = e z" using ee[of u] by simp
    then show False using u by simp
  qed
  moreover have "e u \<noteq> e z" using u by simp
  ultimately show ?thesis using u by (simp add: edge_H_fun skip_def)
qed

lemma node_H: "u \<in> DH \<Longrightarrow> node H u = (if n u = z then n (e z) else if n u = e z then n z else n u)"
proof -
  assume u: "u \<in> DH"
  have nz: "n z \<noteq> z" using n'id zD by blast
  have nez: "n (e z) \<noteq> e z" using n'id ezD by blast
  have e1: "e (n w) = z \<longleftrightarrow> n w = e z" for w by (metis ee)
  have node1: "skip_edge (permN G) z w =
     (if w = z then z else if n w = e z then n z else if n w = z then e z else n w)" for w
    using nz by (simp add: skip_edge_permN e1)
  have nuz: "n (e z) \<noteq> z" if h: "n u = z"
  proof
    assume "n (e z) = z"
    then have "n (e z) = n u" using h by simp
    then have "e z = u" by simp
    then show False using u by simp
  qed
  have nuez: "n z \<noteq> e z" if h: "n u = e z"
  proof
    assume "n z = e z"
    then have "n z = n u" using h by simp
    then have "z = u" by simp
    then show False using u by simp
  qed
  show ?thesis
    unfolding H_def WalkupE_simps WalkupN_simps
    using u nz nez nuz nuez ez_z by (auto simp: skip_def node1)
qed

lemma face_H: "u \<in> DH \<Longrightarrow> face H u = (if f u = z then f z else if f u = e z then f (e z) else f u)"
  using fz_ez fez_z ez_z by (auto simp: H_def skip_def)

lemma card_H: "card DH < card D"
proof -
  have "DH \<subset> D" using zD by blast
  with finite_darts show ?thesis by (rule psubset_card_mono)
qed

lemma planar_H: "planar H"
proof -
  interpret W: hypermap "WalkupN G z" by (rule W_hyp)
  have "planar (WalkupN G z)" by (rule planar_WalkupN[OF planarG zD])
  moreover have "e z \<in> darts (WalkupN G z)" using ezD ez_z by simp
  ultimately show ?thesis unfolding H_def by (rule W.planar_WalkupE)
qed

lemma e_DH: "u \<in> DH \<Longrightarrow> e u \<in> DH"
proof -
  assume u: "u \<in> DH"
  have "e u \<noteq> z"
  proof
    assume "e u = z"
    then have "u = e z" using ee[of u] by simp
    then show False using u by simp
  qed
  moreover have "e u \<noteq> e z" using u by simp
  moreover have "e u \<in> D" using u by simp
  ultimately show ?thesis by simp
qed

lemma plain_H: "plain H"
proof -
  interpret H: hypermap H by (rule hypermap_H)
  show ?thesis
    unfolding plain_def H.plainP
    using e_DH edge_H e'id by simp
qed

lemma coloring_H: "coloring G k \<Longrightarrow> coloring H k"
proof -
  assume col: "coloring G k"
  have kE: "\<And>x. x \<in> D \<Longrightarrow> k (e x) \<noteq> k x" and kF: "\<And>x. x \<in> D \<Longrightarrow> k (f x) = k x"
    using col by (auto simp: coloring_def)
  show ?thesis unfolding coloring_def
  proof (intro conjI ballI)
    fix u assume u: "u \<in> darts H"
    then show "k (edge H u) \<noteq> k u" using edge_H kE by auto
    have uD: "u \<in> D" using u by simp
    show "k (face H u) = k u"
    proof (cases "f u = z")
      case True
      then show ?thesis using u face_H kF[OF uD] kF[OF zD] by simp
    next
      case fz: False
      show ?thesis
      proof (cases "f u = e z")
        case True
        then show ?thesis using u fz face_H kF[OF uD] kF[OF ezD] by simp
      next
        case False
        then show ?thesis using u fz face_H kF[OF uD] by simp
      qed
    qed
  qed
qed

subsection \<open>The new perimeter\<close>

abbreviation L :: 'a where "L \<equiv> lastd (n z) p1"

lemma path_p1: "path (frel n) (n z) p1" and nL: "n L = z"
  using cycq by (simp_all add: cycle_Cons)

lemma L_q: "L \<in> set q" using lastd_in[of "n z" p1] by auto

lemma L_eq: "L = f (e z)" using nL node_eq_iff by blast

lemma z_notin: "z \<notin> set (n z # p1)" using distq by simp

lemma qcubG: "x \<in> D \<Longrightarrow> x \<notin> set q \<Longrightarrow> n (n (n x)) = x \<and> n x \<noteq> x"
  using qcub by (simp add: quasicubic_def cubicP)

lemma node_H_eq: "a \<in> DH \<Longrightarrow> n a \<noteq> z \<Longrightarrow> n a \<noteq> e z \<Longrightarrow> node H a = n a"
  using node_H by simp

lemma path_node_H: "set (a # l) \<subseteq> DH \<Longrightarrow> path (frel n) a l \<Longrightarrow> path (frel (node H)) a l"
proof (induction l arbitrary: a)
  case Nil
  then show ?case by simp
next
  case (Cons b l)
  have "n a = b" and "path (frel n) b l" using Cons.prems(2) by simp_all
  moreover have "node H a = n a" using Cons.prems(1) \<open>n a = b\<close> by (intro node_H_eq) auto
  ultimately show ?case using Cons.IH Cons.prems(1) by simp
qed

definition s :: "'a list" where
  "s = (if f z = z then p1 else n (e z) # f z # n z # p1)"

lemma caseA_ez: "f z = z \<Longrightarrow> e z = n z" using nf_e[of z] by simp

lemma caseB_facts:
  assumes fz: "f z \<notin> set q"
  shows "n (n (n (f z))) = f z" "n (f z) \<noteq> f z" "n (f z) = e z" "n (n (e z)) = f z"
    "e z \<notin> set q" "n (e z) \<notin> set q" "n (e z) \<noteq> f z" "f z \<noteq> z"
proof -
  have fzD: "f z \<in> D" using zD by simp
  show c: "n (n (n (f z))) = f z" and c2: "n (f z) \<noteq> f z" using qcubG[OF fzD fz] by auto
  show nfz: "n (f z) = e z" by simp
  show "n (n (e z)) = f z" using c nfz by simp
  show ezq: "e z \<notin> set q" using fz q_closed_inv nfz by metis
  show "n (e z) \<notin> set q" using ezq q_closed_inv by metis
  show "n (e z) \<noteq> f z"
  proof
    assume h: "n (e z) = f z"
    then have "n (n (f z)) = f z" using nfz by simp
    then have "n (n (n (f z))) = n (f z)" by simp
    then show False using c c2 by simp
  qed
  show "f z \<noteq> z" using fz by auto
qed

lemma s_DH: "set s \<subseteq> DH"
proof (cases "f z = z")
  case True
  have "set p1 \<subseteq> D" using qD by auto
  moreover have "z \<notin> set p1" "e z \<notin> set p1" using distq caseA_ez[OF True] by auto
  ultimately show ?thesis using True by (auto simp: s_def)
next
  case False
  then have fz: "f z \<notin> set q" using Dfz by blast
  note B = caseB_facts[OF fz]
  have "set (n z # p1) \<subseteq> D" using qD by auto
  moreover have "z \<notin> set (n z # p1)" by (rule z_notin)
  moreover have "e z \<notin> set (n z # p1)" using B(5) by auto
  moreover have "n (e z) \<in> D" "f z \<in> D" using ezD zD by simp_all
  moreover have "n (e z) \<noteq> z" "n (e z) \<noteq> e z" using B(6) n'id ezD by auto
  moreover have "f z \<noteq> z" "f z \<noteq> e z" using B(8) fz_ez by auto
  ultimately show ?thesis using False by (auto simp: s_def)
qed

lemma distinct_s: "distinct s"
proof (cases "f z = z")
  case True
  then show ?thesis using distq by (simp add: s_def)
next
  case False
  then have fz: "f z \<notin> set q" using Dfz by blast
  note B = caseB_facts[OF fz]
  show ?thesis using False distq B(6,7) fz by (auto simp: s_def)
qed

lemma cycle_s: "cycle (frel (node H)) s"
proof (cases "f z = z")
  case True
  note ez = caseA_ez[OF True]
  have sA: "s = p1" using True by (simp add: s_def)
  have p1D: "set p1 \<subseteq> DH" using s_DH sA by simp
  have "cycle (frel (node H)) p1"
  proof (cases p1)
    case Nil
    then show ?thesis by simp
  next
    case (Cons u s1)
    have pu: "path (frel n) u s1" and nnz: "n (n z) = u" using path_p1 Cons by simp_all
    have sD: "set (u # s1) \<subseteq> DH" using p1D Cons by simp
    have p: "path (frel (node H)) u s1" by (rule path_node_H[OF sD pu])
    have Ld: "lastd u s1 \<in> DH" using sD lastd_in[of u s1] by auto
    have "lastd u s1 = L" using Cons by simp
    then have "node H (lastd u s1) = u" using node_H[OF Ld] nL ez nnz by simp
    then show ?thesis using Cons p by (simp add: cycle_Cons)
  qed
  then show ?thesis using sA by simp
next
  case False
  then have fz: "f z \<notin> set q" using Dfz by blast
  note B = caseB_facts[OF fz]
  have sD: "set (n (e z) # f z # n z # p1) \<subseteq> DH" using s_DH False by (simp add: s_def)
  have h1: "node H (n (e z)) = f z" using node_H[of "n (e z)"] sD B(4,8) fz_ez by simp
  have h2: "node H (f z) = n z" using node_H[of "f z"] sD ez_z by simp
  have sD': "set (n z # p1) \<subseteq> DH" using sD by simp
  have p: "path (frel (node H)) (n z) p1" by (rule path_node_H[OF sD' path_p1])
  have Ld: "L \<in> DH" using sD' lastd_in[of "n z" p1] by auto
  have h3: "node H L = n (e z)" using node_H[OF Ld] nL by simp
  show ?thesis using False h1 h2 p h3 by (simp add: s_def cycle_Cons)
qed

lemma quasicubic_s: "quasicubic H s"
proof -
  interpret H: hypermap H by (rule hypermap_H)
  show ?thesis unfolding quasicubic_def H.cubicP
  proof
    fix u assume u: "u \<in> darts H - set s"
    then have uDH: "u \<in> DH" and us: "u \<notin> set s" by auto
    have uD: "u \<in> D" using uDH by simp
    have uq: "u \<notin> set q"
    proof
      assume "u \<in> set q"
      then have "u \<in> set (n z # p1)" using uDH by auto
      then show False
      proof (cases "f z = z")
        case True
        then have "u \<in> set p1" using \<open>u \<in> set (n z # p1)\<close> uDH caseA_ez[OF True] by auto
        then show False using us True by (simp add: s_def)
      next
        case False
        then show False using us \<open>u \<in> set (n z # p1)\<close> by (simp add: s_def)
      qed
    qed
    have c3: "n (n (n u)) = u" and c1: "n u \<noteq> u" using qcubG[OF uD uq] by auto
    have nuq: "n u \<notin> set q" using uq q_closed_inv by blast
    have nnuq: "n (n u) \<notin> set q" using nuq q_closed_inv by blast
    have nu_z: "n u \<noteq> z" using nuq by auto
    have nnu_z: "n (n u) \<noteq> z" using nnuq by auto
    have nu_ez: "n u \<noteq> e z"
    proof
      assume h: "n u = e z"
      then have "u = f z" using nf_e[of z] by (metis N.eq_iff)
      then show False
      proof (cases "f z = z")
        case True
        then show False using \<open>u = f z\<close> uDH by simp
      next
        case False
        then show False using \<open>u = f z\<close> us by (simp add: s_def)
      qed
    qed
    have nnu_ez: "n (n u) \<noteq> e z"
    proof
      assume h: "n (n u) = e z"
      then have nuf: "n u = f z" using nf_e[of z] by (metis N.eq_iff)
      show False
      proof (cases "f z = z")
        case True
        then show False using nuf nu_z by simp
      next
        case False
        then have fz: "f z \<notin> set q" using Dfz by blast
        have "n (n (n (f z))) = f z" using caseB_facts(1)[OF fz] .
        then have "n (n (f z)) = u" using nuf by (metis N.eq_iff)
        then have "u = n (e z)" by simp
        then show False using us False by (simp add: s_def)
      qed
    qed
    have v: "n u \<in> DH" using uD nu_z nu_ez by simp
    have w: "n (n u) \<in> DH" using uD nnu_z nnu_ez by simp
    have h1: "node H u = n u" using node_H_eq[OF uDH nu_z nu_ez] .
    have h2: "node H (n u) = n (n u)" using node_H_eq[OF v nnu_z nnu_ez] .
    have h3: "node H (n (n u)) = u" using node_H_eq[OF w] c3 uDH by simp
    show "node H (node H (node H u)) = u \<and> node H u \<noteq> u" using h1 h2 h3 c1 by simp
  qed
qed

subsection \<open>Lifting colorings of the contraction\<close>

lemma addc_left_id: "a +c b = b \<Longrightarrow> a = Color0"
  by (cases a; cases b) simp_all

lemma L_DH_B: "f z \<notin> set q \<Longrightarrow> L \<in> DH"
proof -
  assume fz: "f z \<notin> set q"
  have "set s \<subseteq> DH" by (rule s_DH)
  moreover have "L \<in> set s" using lastd_in[of "n z" p1] fz Dfz by (auto simp: s_def)
  ultimately show ?thesis by blast
qed

lemma lift_coloring:
  assumes k1: "coloring H k1"
    and cond: "if f z = z then e1 \<noteq> Color0 else k1 L \<noteq> k1 (f z)"
  shows "\<exists>k0. coloring G k0 \<and> (\<forall>u\<in>DH. k0 u = k1 u) \<and> (f z = z \<longrightarrow> k0 z +c k0 (n z) = e1)"
proof -
  have k1E: "\<And>u. u \<in> DH \<Longrightarrow> k1 (e u) \<noteq> k1 u" using k1 edge_H by (auto simp: coloring_def)
  have k1F: "\<And>u. u \<in> DH \<Longrightarrow> k1 (face H u) = k1 u" using k1 by (auto simp: coloring_def)
  define k0 where "k0 x = (if x \<in> DH then k1 x else e1)" for x
  define e2 where "e2 = k0 (f (e z))"
  define e3 where "e3 = (if f z = z then e1 +c e2 else k0 (f z))"
  define k' where "k' = (k0(z := e3))(e z := e2)"
  have k'z: "k' z = e3" using ez_z by (simp add: k'_def)
  have k'ez: "k' (e z) = e2" by (simp add: k'_def)
  have k'DH: "k' u = k1 u" if "u \<in> DH" for u using that by (simp add: k'_def k0_def)
  have fezD: "f (e z) \<in> D" using ezD by simp
  have e23: "e3 \<noteq> e2"
  proof (cases "f z = z")
    case True
    then have "e1 \<noteq> Color0" using cond by simp
    then show ?thesis using True addc_left_id by (auto simp: e3_def)
  next
    case False
    then have fz: "f z \<notin> set q" using Dfz by blast
    have fzDH: "f z \<in> DH" using caseB_facts(8)[OF fz] fz_ez zD by simp
    have LDH: "f (e z) \<in> DH" using L_DH_B[OF fz] L_eq by simp
    have "k1 (f (e z)) \<noteq> k1 (f z)" using cond False L_eq by simp
    then show ?thesis using False fzDH LDH by (simp add: e3_def e2_def k0_def)
  qed
  have colE: "k' (e x) \<noteq> k' x" if xD: "x \<in> D" for x
  proof -
    consider (z) "x = z" | (ez) "x = e z" | (o) "x \<in> DH" using xD by blast
    then show ?thesis
    proof cases
      case z
      then show ?thesis using k'z k'ez e23 by simp
    next
      case ez
      then show ?thesis using k'z k'ez e23 by simp
    next
      case o
      then show ?thesis using k1E[OF o] k'DH[OF o] k'DH[OF e_DH[OF o]] by simp
    qed
  qed
  have colF: "k' (f x) = k' x" if xD: "x \<in> D" for x
  proof -
    consider (z) "x = z" | (ez) "x = e z" | (o) "x \<in> DH" using xD by blast
    then show ?thesis
    proof cases
      case z
      show ?thesis
      proof (cases "f z = z")
        case True
        then show ?thesis using z by simp
      next
        case False
        then have fz: "f z \<notin> set q" using Dfz by blast
        have fzDH: "f z \<in> DH" using caseB_facts(8)[OF fz] fz_ez zD by simp
        show ?thesis using z False k'DH[OF fzDH] k'z fzDH by (simp add: e3_def k0_def)
      qed
    next
      case ez
      show ?thesis
      proof (cases "f (e z) = e z")
        case True
        then show ?thesis using ez by simp
      next
        case False
        then have fezDH: "f (e z) \<in> DH" using fez_z fezD by simp
        show ?thesis using ez k'DH[OF fezDH] k'ez fezDH by (simp add: e2_def k0_def)
      qed
    next
      case o
      have kf: "k1 (face H x) = k1 x" by (rule k1F[OF o])
      show ?thesis
      proof (cases "f x = z")
        case True
        have fzz: "f z \<noteq> z"
        proof
          assume "f z = z"
          then have "f x = f z" using True by simp
          then show False using o by simp
        qed
        then have fz: "f z \<notin> set q" using Dfz by blast
        have fzDH: "f z \<in> DH" using caseB_facts(8)[OF fz] fz_ez zD by simp
        have "k1 (f z) = k1 x" using kf face_H[OF o] True by simp
        then show ?thesis using True k'z fzz fzDH k'DH[OF o] by (simp add: e3_def k0_def)
      next
        case fxz: False
        show ?thesis
        proof (cases "f x = e z")
          case True
          have "f (e z) \<noteq> e z"
          proof
            assume "f (e z) = e z"
            then have "f x = f (e z)" using True by simp
            then show False using o by simp
          qed
          then have fezDH: "f (e z) \<in> DH" using fez_z fezD by simp
          have "k1 (f (e z)) = k1 x" using kf face_H[OF o] fxz True by simp
          then show ?thesis using True k'ez fezDH k'DH[OF o] by (simp add: e2_def k0_def)
        next
          case False
          have fxDH: "f x \<in> DH" using o fxz False by simp
          have "k1 (f x) = k1 x" using kf face_H[OF o] fxz False by simp
          then show ?thesis using k'DH[OF o] k'DH[OF fxDH] by simp
        qed
      qed
    qed
  qed
  have "coloring G k'" using colE colF by (simp add: coloring_def)
  moreover have "\<forall>u\<in>DH. k' u = k1 u" using k'DH by blast
  moreover have "f z = z \<longrightarrow> k' z +c k' (n z) = e1"
  proof
    assume fz: "f z = z"
    then have "n z = e z" using caseA_ez by simp
    then show "k' z +c k' (n z) = e1" using k'z k'ez fz by (simp add: e3_def addcA)
  qed
  ultimately show ?thesis by blast
qed

subsection \<open>The induction step\<close>

lemma addc_chain: "(a +c b) +c (b +c c) = a +c c"
  by (cases a; cases b; cases c) simp_all

lemma addc_cancel_l: "(a +c b) +c (a +c c) = b +c c"
  by (cases a; cases b; cases c) simp_all

lemma addc_self_eq: "a = a +c b \<Longrightarrow> b = Color0"
  by (cases a; cases b) simp_all

lemma addc_neq0: "a \<noteq> b \<Longrightarrow> a +c b \<noteq> Color0"
  using addc_eq0 by blast

lemma last_map_q: "last (map k q) = k L"
proof -
  have "last (map k (n z # p1)) = k (last (n z # p1))" by (rule last_map) simp
  then show ?thesis by simp
qed

lemma ur_q: "urtrace (map k q) = (k L +c k z) # (k z +c k (n z)) # pairmap addc (k (n z)) (map k p1)"
  using last_map_q[of k] by (simp add: urtrace_def)

lemma ur_p1: "k L = k (n z) \<Longrightarrow> urtrace (map k p1) = pairmap addc (k (n z)) (map k p1)"
proof (cases p1)
  case Nil
  then show ?thesis by (simp add: urtrace_def)
next
  case (Cons u s1)
  assume h: "k L = k (n z)"
  have "last (map k p1) = k (last p1)" using Cons by (simp add: last_map)
  moreover have "last p1 = L" using Cons by simp
  ultimately show ?thesis using h Cons by (simp add: urtrace_def)
qed

lemma ur_sB:
  assumes "f z \<noteq> z"
  shows "urtrace (map k s) = (k L +c k (n (e z))) # (k (n (e z)) +c k (f z)) # (k (f z) +c k (n z)) #
           pairmap addc (k (n z)) (map k p1)"
proof -
  have sB: "s = n (e z) # f z # n z # p1" using assms by (simp add: s_def)
  have "last (map k (n z # p1)) = k (last (n z # p1))" by (rule last_map) simp
  then have "last (map k s) = k L" using sB by simp
  then show ?thesis using sB by (simp add: urtrace_def)
qed

lemma kGL: "coloring G k \<Longrightarrow> k L = k (e z)"
  using L_eq ezD by (simp add: coloring_def)

lemma kGfz: "coloring G k \<Longrightarrow> k (f z) = k z"
  using zD by (simp add: coloring_def)

lemma kGE: "coloring G k \<Longrightarrow> k (e z) \<noteq> k z"
  using zD by (simp add: coloring_def)

lemma step:
  assumes IH: "\<And>k1. coloring H k1 \<Longrightarrow> \<exists>w. matchg [] (urtrace (map k1 s)) w \<and>
                  (\<forall>et. matchg [] et w \<longrightarrow> (\<exists>k1'. coloring H k1' \<and> et = urtrace (map k1' s)))"
    and k: "coloring G k"
  shows "\<exists>w. matchg [] (urtrace (map k q)) w \<and>
           (\<forall>et. matchg [] et w \<longrightarrow> (\<exists>k'. coloring G k' \<and> et = urtrace (map k' q)))"
proof (cases "f z = z")
  case True
  have sA: "s = p1" using True by (simp add: s_def)
  have p1DH: "set p1 \<subseteq> DH" using s_DH sA by simp
  have ez: "e z = n z" by (rule caseA_ez[OF True])
  have urG: "urtrace (map k' q) = (k' z +c k' (n z)) # (k' z +c k' (n z)) # urtrace (map k' p1)"
    if k': "coloring G k'" for k'
  proof -
    have "k' L = k' (n z)" using kGL[OF k'] ez by simp
    then show ?thesis using ur_q[of k'] ur_p1[of k'] by (simp add: addcC)
  qed
  define e1 where "e1 = k z +c k (n z)"
  have e10: "e1 \<noteq> Color0" using kGE[OF k] ez addc_neq0 by (auto simp: e1_def)
  obtain w where w: "matchg [] (urtrace (map k p1)) w"
    and wall: "\<forall>et. matchg [] et w \<longrightarrow> (\<exists>k1'. coloring H k1' \<and> et = urtrace (map k1' p1))"
    using IH[OF coloring_H[OF k]] sA by auto
  define w2 where "w2 = (if e1 = Color1 then Gskip # Gskip # w else Gpush # Gpop0 # w)"
  show ?thesis
  proof (rule exI[of _ w2], intro conjI allI impI)
    show "matchg [] (urtrace (map k q)) w2"
      using urG[OF k] w e10 by (cases e1) (simp_all add: w2_def e1_def[symmetric])
    fix et assume m: "matchg [] et w2"
    have len: "length et = length w2" using matchg_size[OF m] by simp
    obtain a b et2 where et: "et = a # b # et2"
      using len by (cases et rule: remdups_adj.cases) (auto simp: w2_def split: if_splits)
    have m': "matchg [] (a # b # et2) w2" using m et by simp
    have abw: "a = b \<and> a \<noteq> Color0 \<and> matchg [] et2 w"
    proof (cases "e1 = Color1")
      case True
      then have "a = Color1 \<and> b = Color1 \<and> matchg [] et2 w"
      proof -
        have "matchg [] (a # b # et2) (Gskip # Gskip # w)" using m' True by (simp add: w2_def del: matchg.simps)
        then show ?thesis using match2_skip_skip[of a b et2 w] by blast
      qed
      then show ?thesis by simp
    next
      case False
      then have "a = b \<and> (a = Color2 \<or> a = Color3) \<and> matchg [] et2 w"
      proof -
        have "matchg [] (a # b # et2) (Gpush # Gpop0 # w)" using m' False by (simp add: w2_def del: matchg.simps)
        then show ?thesis using match2_push_pop0[of a b et2 w] by blast
      qed
      then show ?thesis by auto
    qed
    then have ab: "a = b" "a \<noteq> Color0" and m2: "matchg [] et2 w" by auto
    obtain k1 where k1: "coloring H k1" and et2: "et2 = urtrace (map k1 p1)" using wall m2 by blast
    obtain k0 where k0: "coloring G k0" and agree: "\<forall>u\<in>DH. k0 u = k1 u"
      and k0z: "k0 z +c k0 (n z) = a"
      using lift_coloring[OF k1, of a] True ab by auto
    have mp: "map k0 p1 = map k1 p1" using agree p1DH by (auto intro: map_cong)
    have "urtrace (map k0 p1) = urtrace (map k1 p1)" using mp by (rule arg_cong)
    then have "urtrace (map k0 q) = et" using urG[OF k0] k0z ab et et2 by simp
    then show "\<exists>k'. coloring G k' \<and> et = urtrace (map k' q)" using k0 by metis
  qed
next
  case False
  then have fz: "f z \<notin> set q" using Dfz by blast
  note B = caseB_facts[OF fz]
  have p1DH: "set (n z # p1) \<subseteq> DH" using s_DH False by (simp add: s_def)
  have fzDH: "f z \<in> DH" using s_DH False by (simp add: s_def)
  have LDH: "L \<in> DH" by (rule L_DH_B[OF fz])
  define rest where "rest k' = (k' z +c k' (n z)) # pairmap addc (k' (n z)) (map k' p1)" for k'
  define e1 where "e1 = k (e z) +c k z"
  define e2 where "e2 = k (e z) +c k (n (e z))"
  have urq: "urtrace (map k q) = e1 # rest k"
    using ur_q[of k] kGL[OF k] by (simp add: e1_def rest_def)
  have urs: "urtrace (map k s) = e2 # (e2 +c e1) # rest k"
    using ur_sB[OF False, of k] kGL[OF k] kGfz[OF k] addc_cancel_l[of "k (e z)" "k (n (e z))" "k z"]
    by (simp add: e1_def e2_def rest_def)
  have e10: "e1 \<noteq> Color0" using kGE[OF k] addc_neq0 by (simp add: e1_def)
  obtain w where w: "matchg [] (urtrace (map k s)) w"
    and wall: "\<forall>et. matchg [] et w \<longrightarrow> (\<exists>k1'. coloring H k1' \<and> et = urtrace (map k1' s))"
    using IH[OF coloring_H[OF k]] by auto
  have "length w = length (urtrace (map k s))" using matchg_size[OF w] .
  then obtain s1 s2 w1 where ws: "w = s1 # s2 # w1"
    using urs by (cases w rule: remdups_adj.cases) auto
  have m12: "matchg [] (e2 # (e2 +c e1) # rest k) (s1 # s2 # w1)" using w urs ws by simp
  have P: "gram_P12 s1 s2" by (rule gram_P12I[OF e10 m12])
  show ?thesis
  proof (rule exI[of _ "gram_W s1 s2 w1"], intro conjI allI impI)
    show "matchg [] (urtrace (map k q)) (gram_W s1 s2 w1)"
      using gram_W_fwd[OF e10 m12] urq by simp
    fix et assume m: "matchg [] et (gram_W s1 s2 w1)"
    have "gram_W s1 s2 w1 \<noteq> []" by (simp add: gram_W_def)
    then have "et \<noteq> []" using m by auto
    then obtain c et'' where et: "et = c # et''" by (cases et) auto
    have c0: "c \<noteq> Color0" using matchg_memc0[OF m] et by auto
    define e0 where "e0 = gram_e0 s1 s2 w1 c et''"
    have mb: "matchg [] (e0 # (e0 +c c) # et'') w"
      using gram_W_bwd[OF P, of c et''] m et ws by (simp add: e0_def)
    obtain k1 where k1: "coloring H k1" and k1s: "e0 # (e0 +c c) # et'' = urtrace (map k1 s)"
      using wall mb by blast
    have h1: "e0 = k1 L +c k1 (n (e z))" and h2: "e0 +c c = k1 (n (e z)) +c k1 (f z)"
      and h3: "et'' = (k1 (f z) +c k1 (n z)) # pairmap addc (k1 (n z)) (map k1 p1)"
    proof -
      have eq: "e0 # (e0 +c c) # et'' = (k1 L +c k1 (n (e z))) # (k1 (n (e z)) +c k1 (f z)) #
                 (k1 (f z) +c k1 (n z)) # pairmap addc (k1 (n z)) (map k1 p1)"
        using k1s ur_sB[OF False, of k1] by (rule trans)
      then show "e0 = k1 L +c k1 (n (e z))" "e0 +c c = k1 (n (e z)) +c k1 (f z)"
        "et'' = (k1 (f z) +c k1 (n z)) # pairmap addc (k1 (n z)) (map k1 p1)"
        unfolding list.inject by blast+
    qed
    have sum: "k1 L +c k1 (f z) = c"
      using h1 h2 addc_chain[of "k1 L" "k1 (n (e z))" "k1 (f z)"] by (metis addKc)
    have cond: "k1 L \<noteq> k1 (f z)"
    proof
      assume "k1 L = k1 (f z)"
      then have "c = Color0" using sum by simp
      then show False using c0 by simp
    qed
    obtain k0 where k0: "coloring G k0" and agree: "\<forall>u\<in>DH. k0 u = k1 u"
      using lift_coloring[OF k1, of Color0] cond False by auto
    have k0z: "k0 z = k1 (f z)" using kGfz[OF k0] agree fzDH by simp
    have k0L: "k0 L = k1 L" using agree LDH by simp
    have k0nz: "k0 (n z) = k1 (n z)" using agree p1DH by simp
    have mp: "map k0 p1 = map k1 p1" using agree p1DH by (auto intro: map_cong)
    have "pairmap addc (k0 (n z)) (map k0 p1) = pairmap addc (k1 (n z)) (map k1 p1)"
      unfolding mp k0nz by (rule refl)
    then have "urtrace (map k0 q) = et"
      using ur_q[of k0] k0z k0L k0nz sum h3 et by simp
    then show "\<exists>k'. coloring G k' \<and> et = urtrace (map k' q)" using k0 by metis
  qed
qed

end

section \<open>Rotation lemmas for traces\<close>

lemma rot_Suc0_Cons [simp]: "rot (Suc 0) (x # l) = l @ [x]"
  using rot1_Cons[of x l] by simp

lemma map_rot: "map k (rot n l) = rot n (map k l)"
  by (simp add: rot_def drop_map take_map)

lemma cycle_rot: "cycle R (rot n l) = cycle R l"
proof (cases "n \<le> length l")
  case True
  then show ?thesis using rot_rotate cycle_rotate by metis
next
  case False
  then show ?thesis by (simp add: rot_oversize)
qed

lemma urtrace_trace: "urtrace (rot 1 l) = trace l"
proof (cases l)
  case Nil
  then show ?thesis by (simp add: urtrace_def trace_def rot_def)
next
  case (Cons c l')
  then show ?thesis by (simp add: rot1_Cons urtrace_def trace_Cons)
qed

lemma urtrace_rot: "urtrace (rot 1 l) = rot 1 (urtrace l)"
proof (cases l)
  case Nil
  then show ?thesis by (simp add: urtrace_def rot_def)
next
  case (Cons c l')
  have "urtrace (rot 1 l) = pairmap addc c (l' @ [c])" using Cons by (simp add: rot1_Cons urtrace_def)
  also have "\<dots> = pairmap addc c l' @ [last (c # l') +c c]" by (simp add: pairmap_snoc)
  also have "\<dots> = rot 1 (urtrace l)" using Cons by (simp add: urtrace_def rot1_Cons)
  finally show ?thesis .
qed

lemma trace_rot1: "trace (rot 1 l) = rot 1 (trace l)"
  by (metis urtrace_trace urtrace_rot)

definition rotr1 :: "'b list \<Rightarrow> 'b list" where
  "rotr1 l = rot (length l - 1) l"

lemma rot_rotr1: "rot 1 (rotr1 l) = l"
proof (cases l)
  case Nil
  then show ?thesis by (simp add: rotr1_def rot_def)
next
  case (Cons c l')
  have "rot 1 (rot (length l - 1) l) = rot (length l - 1 + 1) l"
    using Cons by (subst rot_add) simp_all
  also have "\<dots> = l" using Cons by (simp add: rot_oversize)
  finally show ?thesis by (simp add: rotr1_def)
qed

lemma set_rotr1 [simp]: "set (rotr1 l) = set l" by (simp add: rotr1_def)
lemma distinct_rotr1 [simp]: "distinct (rotr1 l) = distinct l" by (simp add: rotr1_def)
lemma cycle_rotr1 [simp]: "cycle R (rotr1 l) = cycle R l" by (simp add: rotr1_def cycle_rot)

section \<open>The Kempe closure theorem\<close>

definition kempe_claim :: "'a hypermap \<Rightarrow> 'a list \<Rightarrow> bool" where
  "kempe_claim G r \<longleftrightarrow> (\<forall>k. coloring G k \<longrightarrow>
     (\<exists>w. matchg [] (trace (map k r)) w \<and> (\<forall>et. matchg [] et w \<longrightarrow> ring_trace G r et)))"

lemma kempe_claim_rot1: "kempe_claim G r \<Longrightarrow> kempe_claim G (rot 1 r)"
  unfolding kempe_claim_def
proof (intro allI impI)
  fix k assume cl: "\<forall>k. coloring G k \<longrightarrow> (\<exists>w. matchg [] (trace (map k r)) w \<and>
                        (\<forall>et. matchg [] et w \<longrightarrow> ring_trace G r et))"
    and k: "coloring G k"
  obtain w where w: "matchg [] (trace (map k r)) w" and wall: "\<forall>et. matchg [] et w \<longrightarrow> ring_trace G r et"
    using cl k by blast
  show "\<exists>w. matchg [] (trace (map k (rot 1 r))) w \<and> (\<forall>et. matchg [] et w \<longrightarrow> ring_trace G (rot 1 r) et)"
  proof (rule exI[of _ "gram_rot w"], intro conjI allI impI)
    have "trace (map k (rot 1 r)) = rot 1 (trace (map k r))" by (simp only: map_rot trace_rot1)
    then show "matchg [] (trace (map k (rot 1 r))) (gram_rot w)"
      using w match_gram_rot[of "trace (map k r)" w] by simp
    fix et assume m: "matchg [] et (gram_rot w)"
    have "matchg [] (rot 1 (rotr1 et)) (gram_rot w)" by (simp only: rot_rotr1 m)
    then have "matchg [] (rotr1 et) w" using match_gram_rot by simp
    then obtain k' where k': "coloring G k'" and et0: "rotr1 et = trace (map k' r)"
      using wall by (auto simp: ring_trace_def)
    have "et = rot 1 (rotr1 et)" by (rule rot_rotr1[symmetric])
    also have "\<dots> = trace (map k' (rot 1 r))" unfolding et0 by (simp only: map_rot trace_rot1)
    finally show "ring_trace G (rot 1 r) et" using k' by (auto simp: ring_trace_def)
  qed
qed

lemma kempe_claim_rot: "kempe_claim G r \<Longrightarrow> j \<le> length r \<Longrightarrow> kempe_claim G (rot j r)"
proof (induction j)
  case 0
  then show ?case by simp
next
  case (Suc j)
  have "rot (j + 1) r = rot 1 (rot j r)" using Suc.prems(2) by (intro rot_add) simp
  then show ?case using Suc kempe_claim_rot1 by simp
qed

lemma kempe_claim_unrot:
  assumes "kempe_claim G (rot i r)" "i \<le> length r"
  shows "kempe_claim G r"
proof -
  have "kempe_claim G (rot (length r - i) (rot i r))"
    using kempe_claim_rot[OF assms(1)] by simp
  moreover have "rot (length r - i) (rot i r) = r"
  proof -
    have "rot (i + (length r - i)) r = rot (length r - i) (rot i r)" using assms(2) by (intro rot_add) simp
    moreover have "rot (i + (length r - i)) r = r" using assms(2) by (simp add: rot_oversize)
    ultimately show ?thesis by simp
  qed
  ultimately show ?thesis by simp
qed

definition kempe_hyps :: "'a hypermap \<Rightarrow> 'a list \<Rightarrow> bool" where
  "kempe_hyps G r \<longleftrightarrow> hypermap G \<and> planar G \<and> plain G \<and> quasicubic G r \<and>
     cycle (frel (node G)) r \<and> distinct r \<and> set r \<subseteq> darts G"

lemma kempe_hyps_rot: "kempe_hyps G r \<Longrightarrow> kempe_hyps G (rot i r)"
  by (simp add: kempe_hyps_def quasicubic_def cycle_rot)

lemma kempe_hyps_iff: "ucycle_planar_plain_quasicubic G r \<longleftrightarrow> kempe_hyps G r"
  by (auto simp: kempe_hyps_def ucycle_planar_plain_quasicubic_def ucycle_plain_quasicubic_def
      plain_quasicubic_def ucycle_def)

lemma (in kempe_step) H_hyps: "kempe_hyps H (rotr1 s)"
  using hypermap_H planar_H plain_H quasicubic_s cycle_s distinct_s s_DH
  by (simp add: kempe_hyps_def quasicubic_def)

lemma kempe_claim_main: "kempe_hyps G r \<Longrightarrow> kempe_claim G r"
proof (induction "card (darts G)" arbitrary: G r rule: less_induct)
  case less
  have hyps: "kempe_hyps G r" by (rule less.prems)
  then interpret hypermap G by (simp add: kempe_hyps_def)
  have planG: "planar G" and plainG: "plain G" and qc: "quasicubic G r"
    and cycr: "cycle (frel n) r" and dr: "distinct r" and rD: "set r \<subseteq> D"
    using hyps by (auto simp: kempe_hyps_def)
  show ?case unfolding kempe_claim_def
  proof (intro allI impI)
    fix k assume k: "coloring G k"
    have n'id: "n x \<noteq> x" if xD: "x \<in> D" for x
    proof
      assume nx: "n x = x"
      have "f (e x) = x" using nx node_eq_iff[of x x] by simp
      then have "k (e x) = k x" using k xD by (metis coloring_def E.closed)
      then show False using k xD by (simp add: coloring_def)
    qed
    show "\<exists>w. matchg [] (trace (map k r)) w \<and> (\<forall>et. matchg [] et w \<longrightarrow> ring_trace G r et)"
    proof (cases r)
      case Nil
      show ?thesis
      proof (rule exI[of _ "[]"], intro conjI allI impI)
        show "matchg [] (trace (map k r)) []" using Nil by (simp add: trace_def)
        fix et assume "matchg [] et []"
        then have "et = []" by simp
        then show "ring_trace G r et" using Nil k by (auto simp: ring_trace_def trace_def)
      qed
    next
      case (Cons x0 r0)
      have x0D: "x0 \<in> D" using rD Cons by simp
      interpret P: hypermap "permN G" by (rule hypermap_permN)
      have "Jordan (permN G)" using planar_Jordan[OF hypermap_permN] planG planar_permN by blast
      then obtain z where xz: "cnode x0 z" and zc: "clink (permN G) z z \<or> \<not> cross_edge (permN G) z"
        using P.Euler_tree[of x0] x0D by auto
      have x0r: "x0 \<in> set r" using Cons by simp
      have zr: "z \<in> set r" using N.fcycle_fconnect[OF cycr dr x0r] xz by simp
      have zD: "z \<in> D" using zr rD by blast
      have Dfz: "f z = z \<or> f z \<notin> set r"
      proof (cases "clink (permN G) z z")
        case True
        then have "z = f z \<or> e z = z" by (simp add: clink_def)
        then show ?thesis using plain_neq[OF plainG zD] by auto
      next
        case False
        then have "\<not> cnode z (f z)" using zc by (simp add: cross_edge_def)
        then show ?thesis using N.fcycle_fconnect[OF cycr dr zr] by auto
      qed
      obtain j where j: "j < length r" "r ! j = z" using zr by (meson in_set_conv_nth)
      define i where "i = (if j = 0 then length r - 1 else j - 1)"
      have ir: "i \<le> length r"
      proof -
        have "j - 1 \<le> length r" "length r - 1 \<le> length r" using j(1) by linarith+
        then show ?thesis unfolding i_def by simp
      qed
      have si: "i + 1 \<le> length r"
      proof (cases "j = 0")
        case True
        have "0 < length r" using j(1) by linarith
        then show ?thesis using True by (simp add: i_def)
      next
        case False
        then show ?thesis using j(1) by (simp add: i_def)
      qed
      have rot1: "rot 1 (rot i r) = rot (Suc i) r" using rot_add[OF si] by simp
      have hd_rot: "\<exists>p. rot 1 (rot i r) = z # p"
      proof (cases "j = 0")
        case True
        have "rot (Suc i) r = r" using True Cons by (simp add: i_def rot_oversize)
        then show ?thesis using rot1 Cons j True by simp
      next
        case False
        have "rot (Suc i) r = drop j r @ take j r" using False by (simp add: i_def rot_def)
        moreover have "drop j r = z # drop (Suc j) r" using j by (metis Cons_nth_drop_Suc)
        ultimately show ?thesis using rot1 by simp
      qed
      then obtain p where p: "rot 1 (rot i r) = z # p" by blast
      define r' where "r' = rot i r"
      have hq: "kempe_hyps G (z # p)"
        using kempe_hyps_rot[OF kempe_hyps_rot[OF hyps, of i], of 1] p by (simp only:)
      have setq: "set (z # p) = set r"
      proof -
        have "set (rot 1 (rot i r)) = set r" by simp
        then show ?thesis using p by (simp only:)
      qed
      have cq: "cycle (frel n) (z # p)" and dq: "distinct (z # p)" and qcq: "quasicubic G (z # p)"
        using hq by (auto simp: kempe_hyps_def)
      have "p \<noteq> []" using cq n'id[OF zD] by (auto simp: cycle_Cons)
      then obtain p1 where pp: "p = n z # p1" using cq by (cases p) (auto simp: cycle_Cons)
      interpret S: kempe_step G z p1
      proof unfold_locales
        show "cycle (frel n) (z # n z # p1)" using cq pp by simp
        show "distinct (z # n z # p1)" using dq pp by simp
        show "quasicubic G (z # n z # p1)" using qcq pp by simp
        show "f z = z \<or> f z \<notin> set (z # n z # p1)" using Dfz setq pp by simp
      qed (use planG plainG zD n'id in auto)
      have IHH: "kempe_claim S.H (rotr1 S.s)"
        using less.hyps[OF _ S.H_hyps] S.card_H by simp
      have IH: "\<exists>w. matchg [] (urtrace (map k1 S.s)) w \<and>
                  (\<forall>et. matchg [] et w \<longrightarrow> (\<exists>k1'. coloring S.H k1' \<and> et = urtrace (map k1' S.s)))"
        if k1: "coloring S.H k1" for k1
      proof -
        have tr: "trace (map k' (rotr1 S.s)) = urtrace (map k' S.s)" for k'
        proof -
          have "trace (map k' (rotr1 S.s)) = urtrace (rot 1 (map k' (rotr1 S.s)))"
            by (rule urtrace_trace[symmetric])
          also have "rot 1 (map k' (rotr1 S.s)) = map k' S.s" by (simp only: map_rot[symmetric] rot_rotr1)
          finally show ?thesis .
        qed
        show ?thesis using IHH k1 by (auto simp: kempe_claim_def ring_trace_def tr)
      qed
      have st: "\<forall>k. coloring G k \<longrightarrow> (\<exists>w. matchg [] (urtrace (map k S.q)) w \<and>
              (\<forall>et. matchg [] et w \<longrightarrow> (\<exists>k'. coloring G k' \<and> et = urtrace (map k' S.q))))"
        using S.step IH by blast
      have trq: "trace (map k' r') = urtrace (map k' S.q)" for k'
      proof -
        have "trace (map k' r') = urtrace (rot 1 (map k' r'))" by (rule urtrace_trace[symmetric])
        also have "rot 1 (map k' r') = map k' (z # p)" unfolding r'_def by (simp only: map_rot[symmetric] p)
        finally show ?thesis using pp by simp
      qed
      have "kempe_claim G r'"
        unfolding kempe_claim_def ring_trace_def trq using st by simp
      then have "kempe_claim G r" using kempe_claim_unrot ir by (simp add: r'_def)
      then show ?thesis using k by (simp add: kempe_claim_def)
    qed
  qed
qed

theorem Kempe_map:
  assumes geo: "ucycle_planar_plain_quasicubic G r"
  shows "Kempe_closed (ring_trace G r)"
  unfolding Kempe_closed_def
proof (rule allI, rule impI, rule conjI)
  fix et assume "ring_trace G r et"
  then obtain k where k: "coloring G k" and et: "et = trace (map k r)" by (auto simp: ring_trace_def)
  show "\<forall>g. ring_trace G r (permt g et)"
  proof
    fix g
    have "coloring G (permc g \<circ> k)" using k by (simp add: coloring_def permc_inj)
    moreover have "permt g et = trace (map (permc g \<circ> k) r)"
    proof -
      have "trace (map (permc g \<circ> k) r) = trace (permt g (map k r))" by (simp add: permt_def)
      also have "\<dots> = permt g (trace (map k r))" by (rule trace_permt)
      finally show "permt g et = trace (map (permc g \<circ> k) r)" using et by simp
    qed
    ultimately show "ring_trace G r (permt g et)" by (auto simp: ring_trace_def)
  qed
  have "kempe_claim G r" using kempe_claim_main geo kempe_hyps_iff by blast
  then show "\<exists>w. matchg [] et w \<and> (\<forall>et'. matchg [] et' w \<longrightarrow> ring_trace G r et')"
    using k et by (auto simp: kempe_claim_def)
qed

end
