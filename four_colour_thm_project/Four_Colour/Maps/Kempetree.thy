(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Kempetree.thy
    The Kempe co-closure tree of a configuration (D-reducibility test).
    Ported from G. Gonthier's Coq development (kempetree.v).
*)
theory Kempetree
  imports Four_Colour_Maps.Cfcolor Four_Colour_Maps.Initctree Four_Colour_Maps.Initgtree Four_Colour_Maps.Gtreerestrict Four_Colour_Maps.Ctreerestrict
begin

section \<open>Sizes of colouring trees\<close>

fun ctree_size :: "ctree \<Rightarrow> nat" where
  "ctree_size (CtreeNode t1 t2 t3) = ctree_size t1 + (ctree_size t2 + ctree_size t3)"
| "ctree_size (CtreeLeaf _) = 1"
| "ctree_size CtreeEmpty = 0"

definition cmems :: "ctree \<Rightarrow> colseq set" where
  "cmems t = {et. ctree_mem t et}"

lemma cmems_node:
  "cmems (CtreeNode t1 t2 t3) =
     (Cons Color1) ` cmems t1 \<union> (Cons Color2) ` cmems t2 \<union> (Cons Color3) ` cmems t3"
proof (rule set_eqI)
  fix et show "et \<in> cmems (CtreeNode t1 t2 t3) \<longleftrightarrow>
    et \<in> (Cons Color1) ` cmems t1 \<union> (Cons Color2) ` cmems t2 \<union> (Cons Color3) ` cmems t3"
  proof (cases et)
    case (Cons c et')
    then show ?thesis by (cases c) (auto simp: cmems_def ctree_mem_def)
  qed (auto simp: cmems_def ctree_mem_def)
qed

lemma card_cmems: "finite (cmems t) \<and> card (cmems t) = ctree_size t"
proof (induction t)
  case (CtreeNode t1 t2 t3)
  have inj: "inj (Cons c)" for c :: color by (rule injI) simp
  have d: "(Cons Color1) ` A \<inter> (Cons Color2) ` B = {}" "(Cons Color1) ` A \<inter> (Cons Color3) ` C = {}"
    "(Cons Color2) ` B \<inter> (Cons Color3) ` C = {}" for A B C :: "colseq set" by auto
  show ?case using CtreeNode
    by (simp add: cmems_node card_Un_disjoint card_image[OF inj_on_subset[OF inj]] d Int_Un_distrib2)
next
  case (CtreeLeaf lf)
  have "cmems (CtreeLeaf lf) = {[]}" by (auto simp: cmems_def ctree_mem_leaf)
  then show ?case by simp
next
  case CtreeEmpty
  then show ?case by (simp add: cmems_def)
qed

lemma ctree_size_partition:
  assumes "ctree_partition t (CtreePair t' t'')"
  shows "ctree_size t = ctree_size t' + ctree_size t''"
proof -
  have p: "\<forall>et. if ctree_mem t et then ctree_mem t' et \<noteq> ctree_mem t'' et
               else \<not> ctree_mem t' et \<and> \<not> ctree_mem t'' et"
    using assms by (simp add: sctree_partition_def)
  have u: "cmems t = cmems t' \<union> cmems t''" using p by (auto simp: cmems_def) (metis)+
  have i: "cmems t' \<inter> cmems t'' = {}" using p by (auto simp: cmems_def) (metis)+
  show ?thesis using card_cmems[of t] card_cmems[of t'] card_cmems[of t''] u i
    by (simp add: card_Un_disjoint)
qed

lemma ctree_proper_mem: "ctree_proper h t \<Longrightarrow> t \<noteq> CtreeEmpty \<Longrightarrow> \<exists>et. ctree_mem t et"
proof (induction h t rule: ctree_proper.induct)
  case (2 h t1 t2 t3)
  have "t1 \<noteq> CtreeEmpty \<or> t2 \<noteq> CtreeEmpty \<or> t3 \<noteq> CtreeEmpty" using 2 by (auto simp: ctree_empty_node_def)
  then show ?case
  proof (elim disjE)
    assume "t1 \<noteq> CtreeEmpty"
    then obtain et where "ctree_mem t1 et" using 2 by auto
    then have "ctree_mem (CtreeNode t1 t2 t3) (Color1 # et)" by (simp add: ctree_mem_def)
    then show ?case by blast
  next
    assume "t2 \<noteq> CtreeEmpty"
    then obtain et where "ctree_mem t2 et" using 2 by auto
    then have "ctree_mem (CtreeNode t1 t2 t3) (Color2 # et)" by (simp add: ctree_mem_def)
    then show ?case by blast
  next
    assume "t3 \<noteq> CtreeEmpty"
    then obtain et where "ctree_mem t3 et" using 2 by auto
    then have "ctree_mem (CtreeNode t1 t2 t3) (Color3 # et)" by (simp add: ctree_mem_def)
    then show ?case by blast
  qed
next
  case (3 lf)
  then show ?case by (auto simp: ctree_mem_leaf)
qed simp_all

lemma ctree_size_proper: "ctree_proper h t \<Longrightarrow> ctree_size t = 0 \<Longrightarrow> t = CtreeEmpty"
proof (rule ccontr)
  assume p: "ctree_proper h t" and s: "ctree_size t = 0" and ne: "t \<noteq> CtreeEmpty"
  obtain et where "ctree_mem t et" using ctree_proper_mem[OF p ne] by blast
  then have "cmems t \<noteq> {}" by (auto simp: cmems_def)
  then show False using card_cmems[of t] s card_0_eq by metis
qed

lemma ctree_max_size_proper: "ctree_proper h t \<Longrightarrow> ctree_size t \<le> 3 ^ h"
proof (induction h t rule: ctree_proper.induct)
  case (2 h t1 t2 t3)
  then show ?case by simp
next
  case (3 lf) then show ?case by simp
qed simp_all

section \<open>Properness of the initial colouring tree\<close>

definition table_ok :: "nat \<Rightarrow> ctree_table \<Rightarrow> bool" where
  "table_ok n T \<longleftrightarrow> (\<forall>i b. i < length T \<longrightarrow> ctree_proper n (ctree_table_sub T i b))"

lemma ctree_leaf_of_proper': "ctree_proper 0 (ctree_leaf_of m)" by (rule ctree_leaf_of_proper)

lemma table_ok_leaf: "table_ok 0 (ctree_leaf_table h)"
  unfolding table_ok_def
proof (intro allI impI)
  fix i b assume "i < length (ctree_leaf_table h)"
  then have "i \<le> h" by (simp add: ctree_leaf_table_size)
  then show "ctree_proper 0 (ctree_table_sub (ctree_leaf_table h) i b)"
    by (simp add: ctree_leaf_table_sub leaf_val_def Let_def ctree_leaf_of_proper)
qed

lemma table_ok_merge:
  assumes "table_ok n T"
  shows "table_ok (Suc n) (ctree_merge_table T) \<and> length (ctree_merge_table T) = length T - 1"
proof (cases T)
  case Nil
  then show ?thesis by (simp add: table_ok_def)
next
  case (Cons line tab)
  have len: "length (ctree_merge_table T) = length T - 1" using Cons by simp
  have "ctree_proper (Suc n) (ctree_table_sub (ctree_merge_table T) i b)"
    if i: "i < length (ctree_merge_table T)" for i b
  proof -
    have i1: "i < length T" "Suc i < length T" using i len by simp_all
    obtain t0 t1 where p0: "T ! i = CtreePair t0 t1" by (cases "T ! i")
    obtain t2 t3 where p1: "T ! Suc i = CtreePair t2 t3" by (cases "T ! Suc i")
    have a: "\<And>b. ctree_proper n (ctree_table_sub T i b)" "\<And>b. ctree_proper n (ctree_table_sub T (Suc i) b)"
      using assms i1 by (auto simp: table_ok_def)
    have pr: "ctree_proper n t0" "ctree_proper n t1" "ctree_proper n t2" "ctree_proper n t3"
      using a(1)[of False] a(1)[of True] a(2)[of False] a(2)[of True] p0 p1 i1
      by (simp_all add: ctree_table_sub_def)
    have "ctree_merge_table T ! i = ctree_merge_pair (T ! i) (T ! Suc i)"
      using Cons i by (simp add: nth_pairmap)
    then show ?thesis using i p0 p1 pr
      by (cases b) (simp_all add: ctree_table_sub_def ctree_cons_proper)
  qed
  then show ?thesis using len by (simp add: table_ok_def)
qed

lemma table_ok_iter:
  "n \<le> h \<Longrightarrow> table_ok n ((ctree_merge_table ^^ n) (ctree_leaf_table h)) \<and>
             length ((ctree_merge_table ^^ n) (ctree_leaf_table h)) = Suc h - n"
proof (induction n)
  case 0
  then show ?case using table_ok_leaf by (simp add: ctree_leaf_table_size)
next
  case (Suc n)
  then show ?case using table_ok_merge[of n "(ctree_merge_table ^^ n) (ctree_leaf_table h)"] by auto
qed

lemma prune_proper:
  "ctree_proper m t \<Longrightarrow> ctree_proper m (ctree_prune_1 t) \<and> ctree_proper m (ctree_prune_2 t) \<and>
                        ctree_proper m (ctree_prune_3 t)"
proof (induction m t rule: ctree_proper.induct)
  case (2 h t1 t2 t3)
  then show ?case by (simp add: ctree_cons_proper)
qed simp_all

lemma ctree_init_tree_proper: "ctree_proper h (ctree_init_tree h)"
proof (cases h)
  case 0
  then show ?thesis by (simp add: ctree_init_tree_def ctree_leaf_table_def)
next
  case (Suc h')
  define T where "T = (ctree_merge_table ^^ h') (ctree_leaf_table h)"
  have ok: "table_ok h' T" and len: "length T = 2" using table_ok_iter[of h' h] Suc by (simp_all add: T_def)
  obtain p q where pq: "T = [p, q]" using len by (cases T; cases "tl T") auto
  obtain t0 t1 where p: "p = CtreePair t0 t1" by (cases p)
  obtain t2 t3 where q: "q = CtreePair t2 t3" by (cases q)
  have T: "T = [CtreePair t0 t1, CtreePair t2 t3]" using pq p q by simp
  have a: "\<And>i b. i < 2 \<Longrightarrow> ctree_proper h' (ctree_table_sub T i b)" using ok len by (simp add: table_ok_def)
  have pr: "ctree_proper h' t1" "ctree_proper h' t2" "ctree_proper h' t3"
    using a[of 0 True] a[of 1 False] a[of 1 True] unfolding T by (simp_all add: ctree_table_sub_def)
  have "ctree_init_tree h = ctree_cons (ctree_prune_1 t1) (ctree_prune_2 t2) (ctree_prune_3 t3)"
    using Suc T by (simp add: ctree_init_tree_def T_def)
  then show ?thesis using Suc pr prune_proper by (simp add: ctree_cons_proper)
qed

section \<open>The Kempe closure iteration\<close>

type_synonym ktc_fun = "ctree \<Rightarrow> ctree \<Rightarrow> gtree \<Rightarrow> ctree \<times> gtree_pair"

fun ktc_step :: "nat \<Rightarrow> ktc_fun \<Rightarrow> ctree \<times> gtree_pair \<Rightarrow> ctree \<times> gtree_pair" where
  "ktc_step h cl (ctu, GtreePair gtr gtu) =
     (if ctu = CtreeEmpty then (ctu, GtreePair gtr gtu)
      else if gtr = GtreeEmpty then (ctu, GtreePair gtr gtu)
      else if gtu = GtreeEmpty then (CtreeEmpty, empty_gtree_pair)
      else (case ctree_restrict h ctu (CtrCons [] gtr CtrNil) of
              CtreePair ctu' ctr \<Rightarrow> cl ctu' (ctree_rotlr ctr) gtu))"

fun Kempe_tree_closure :: "nat \<Rightarrow> nat \<Rightarrow> ktc_fun" where
  "Kempe_tree_closure h 0 ctu ctr gtu = (ctu, gtree_restrict gtu (GtrCons [] ctr GtrNil))"
| "Kempe_tree_closure h (Suc d) ctu ctr gtu =
     ktc_step h (Kempe_tree_closure h d) (ktc_step h (Kempe_tree_closure h d) (Kempe_tree_closure h d ctu ctr gtu))"

definition Kempe_valid :: "nat \<Rightarrow> (colseq \<Rightarrow> bool) \<Rightarrow> ctree \<Rightarrow> ctree \<Rightarrow> gtree \<Rightarrow> gtree \<Rightarrow> bool" where
  "Kempe_valid h P ctu ctr gtr gtu \<longleftrightarrow>
     ctree_proper (Suc h) ctu \<and>
     (\<forall>et. ctree_sub ctu et = (if even_trace et then gtree_sub gtr [] et + gtree_sub gtu [] et else 0)) \<and>
     (\<forall>et. ctree_mem ctr et \<longrightarrow> Kempe_coclosure P (ctrace et) \<and> length et = Suc h) \<and>
     (\<forall>w. gtree_mem gtr w \<longrightarrow> \<not> gtree_mem gtu w \<and> init_gtree_spec (Suc h) w) \<and>
     (\<forall>w. gtree_mem gtu w \<longrightarrow> init_gtree_spec (Suc h) w) \<and>
     (\<forall>w. \<not> gtree_mem gtu w \<longrightarrow> init_gtree_spec (Suc h) w \<longrightarrow>
          (\<exists>et. Kempe_coclosure P (ctrace et) \<and> matchpg [] et w))"

definition Kempe_complete :: "(colseq \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> ctree \<Rightarrow> ctree \<Rightarrow> gtree \<Rightarrow> gtree \<Rightarrow> bool" where
  "Kempe_complete P sz ctu ctr gtr gtu \<longleftrightarrow>
     (ctree_size ctu < sz \<or> (ctr = CtreeEmpty \<and> (\<forall>w. \<not> gtree_mem gtr w))) \<and>
     (\<forall>et. (P (ctrace et) \<or> (\<exists>e. \<not> ctree_mem ctu (permt (edge_rot e) (etrace et)))) \<longrightarrow>
          ctree_mem ctr (etrace et) \<or> gtree_sub gtu [] et = 0)"

definition ktr_prop :: "(ctree \<Rightarrow> ctree \<Rightarrow> gtree \<Rightarrow> gtree \<Rightarrow> bool) \<Rightarrow> ctree \<times> gtree_pair \<Rightarrow> bool" where
  "ktr_prop Q kr = (case kr of (ctu, GtreePair gtr gtu) \<Rightarrow> Q ctu CtreeEmpty gtr gtu)"

lemma gtree_sub_0_iff: "gtree_sub t bs et = 0 \<longleftrightarrow> \<not> (\<exists>w. gtree_mem t w \<and> matchpg bs et w)"
  using match_countP[of "gtree_mem t" bs et] by (auto simp: gtree_sub_def)

lemma gtree_sub_etrace: "gtree_sub t [] (etrace et) = 0 \<longleftrightarrow> gtree_sub t [] et = 0"
  by (simp add: gtree_sub_0_iff matchpg_etrace)

lemma rotlr_empty [simp]: "ctree_rotlr CtreeEmpty = CtreeEmpty"
  by (simp add: ctree_rotlr_def)

lemma closure_base:
  assumes v: "Kempe_valid h P ctu ctr GtreeEmpty gtu"
  shows "ktr_prop (Kempe_valid h P) (Kempe_tree_closure h 0 ctu ctr gtu) \<and>
         (\<forall>sz. Kempe_complete P (3 ^ 0 + sz) ctu ctr GtreeEmpty gtu \<longrightarrow>
               ktr_prop (Kempe_complete P (Suc sz)) (Kempe_tree_closure h 0 ctu ctr gtu))"
proof -
  define ctrr where "ctrr = GtrCons [] ctr GtrNil"
  obtain gtr gtu' where R: "gtree_restrict gtu ctrr = GtreePair gtr gtu'" by (cases "gtree_restrict gtu ctrr")
  have Pg: "sgtree_partition (gtree_mem gtu) (gtree_mem gtr) (gtree_mem gtu')"
    using gtree_restrict_partition[of gtu ctrr] R by simp
  have Pgtr: "gtree_mem gtr w \<longleftrightarrow> gtree_mem gtu w \<and> has_match [] (ctree_mem ctr) w" for w
    using gtree_mem0_restrict[of gtu ctrr w] R by (simp add: ctrr_def)
  have pw: "(gtree_mem gtu w \<longrightarrow> gtree_mem gtr w \<noteq> gtree_mem gtu' w) \<and>
            (\<not> gtree_mem gtu w \<longrightarrow> \<not> gtree_mem gtr w \<and> \<not> gtree_mem gtu' w)" for w
    using Pg by (simp add: sgtree_partition_def)
  have subP: "gtree_sub gtu [] et = gtree_sub gtr [] et + gtree_sub gtu' [] et" for et
    using match_count_partition[OF Pg] by (simp add: gtree_sub_def)
  from v have ctu_ok: "ctree_proper (Suc h) ctu"
    and Dctu: "\<And>et. ctree_sub ctu et = (if even_trace et then gtree_sub gtu [] et else 0)"
    and Dctr: "\<And>et. ctree_mem ctr et \<Longrightarrow> Kempe_coclosure P (ctrace et) \<and> length et = Suc h"
    and Dgtu: "\<And>w. gtree_mem gtu w \<Longrightarrow> init_gtree_spec (Suc h) w"
    and closedP: "\<And>w. \<not> gtree_mem gtu w \<Longrightarrow> init_gtree_spec (Suc h) w \<Longrightarrow>
                    \<exists>et. Kempe_coclosure P (ctrace et) \<and> matchpg [] et w"
    by (auto simp: Kempe_valid_def)
  have v2: "\<forall>et. ctree_sub ctu et = (if even_trace et then gtree_sub gtr [] et + gtree_sub gtu' [] et else 0)"
    using Dctu subP by simp
  have v4: "\<forall>w. gtree_mem gtr w \<longrightarrow> \<not> gtree_mem gtu' w \<and> init_gtree_spec (Suc h) w"
  proof (intro allI impI)
    fix w assume g: "gtree_mem gtr w"
    then have "gtree_mem gtu w" using Pgtr by blast
    then show "\<not> gtree_mem gtu' w \<and> init_gtree_spec (Suc h) w" using pw[of w] g Dgtu by auto
  qed
  have v5: "\<forall>w. gtree_mem gtu' w \<longrightarrow> init_gtree_spec (Suc h) w"
  proof (intro allI impI)
    fix w assume "gtree_mem gtu' w"
    then have "gtree_mem gtu w" using pw[of w] by blast
    then show "init_gtree_spec (Suc h) w" by (rule Dgtu)
  qed
  have v6: "\<forall>w. \<not> gtree_mem gtu' w \<longrightarrow> init_gtree_spec (Suc h) w \<longrightarrow>
             (\<exists>et. Kempe_coclosure P (ctrace et) \<and> matchpg [] et w)"
  proof (intro allI impI)
    fix w assume nw: "\<not> gtree_mem gtu' w" and sw: "init_gtree_spec (Suc h) w"
    show "\<exists>et. Kempe_coclosure P (ctrace et) \<and> matchpg [] et w"
    proof (cases "gtree_mem gtu w")
      case True
      then have "gtree_mem gtr w" using pw[of w] nw by blast
      then obtain et where "ctree_mem ctr et" "matchpg [] et w" using Pgtr has_matchP by blast
      then show ?thesis using Dctr by blast
    next
      case False then show ?thesis using closedP sw by blast
    qed
  qed
  have valid: "Kempe_valid h P ctu CtreeEmpty gtr gtu'"
    unfolding Kempe_valid_def using ctu_ok v2 v4 v5 v6 by simp
  have full: "Kempe_complete P (Suc sz) ctu CtreeEmpty gtr gtu'"
    if c: "Kempe_complete P (3 ^ 0 + sz) ctu ctr GtreeEmpty gtu" for sz
  proof -
    from c have sz1: "ctree_size ctu < Suc sz \<or> (ctr = CtreeEmpty \<and> (\<forall>w. \<not> gtree_mem GtreeEmpty w))"
      and cl: "\<And>et. P (ctrace et) \<or> (\<exists>e. \<not> ctree_mem ctu (permt (edge_rot e) (etrace et))) \<Longrightarrow>
                ctree_mem ctr (etrace et) \<or> gtree_sub gtu [] et = 0"
      by (auto simp: Kempe_complete_def)
    have s: "ctree_size ctu < Suc sz \<or> (CtreeEmpty = CtreeEmpty \<and> (\<forall>w. \<not> gtree_mem gtr w))"
    proof (cases "ctree_size ctu < Suc sz")
      case False
      then have "ctr = CtreeEmpty" using sz1 by blast
      then have "\<not> gtree_mem gtr w" for w using Pgtr has_matchP by (auto simp: ctree_mem_def)
      then show ?thesis by blast
    qed simp
    have "ctree_mem CtreeEmpty (etrace et) \<or> gtree_sub gtu' [] et = 0"
      if pe: "P (ctrace et) \<or> (\<exists>e. \<not> ctree_mem ctu (permt (edge_rot e) (etrace et)))" for et
    proof -
      have "gtree_sub gtu' [] et = 0"
      proof (cases "gtree_sub gtu [] et = 0")
        case True then show ?thesis using subP[of et] by simp
      next
        case False
        then have ce: "ctree_mem ctr (etrace et)" using cl[OF pe] by auto
        show ?thesis unfolding gtree_sub_0_iff
        proof
          assume "\<exists>w. gtree_mem gtu' w \<and> matchpg [] et w"
          then obtain w where w: "gtree_mem gtu' w" "matchpg [] et w" by blast
          have gw: "gtree_mem gtu w" using pw[of w] w(1) by blast
          have "has_match [] (ctree_mem ctr) w" using ce w(2) has_matchP matchpg_etrace by blast
          then have "gtree_mem gtr w" using Pgtr gw by blast
          then show False using pw[of w] gw w(1) by blast
        qed
      qed
      then show ?thesis by simp
    qed
    then show ?thesis using s by (simp add: Kempe_complete_def)
  qed
  show ?thesis using valid full R by (simp add: ktr_prop_def ctrr_def)
qed

lemma edge_rot_132:
  "c \<noteq> Color0 \<Longrightarrow> permc (edge_rot (permc Eperm132 c)) (permc Eperm132 x) = permc Eperm132 (permc (edge_rot c) x)"
  by (cases c; cases x) simp_all

lemma even_etrace: "even_trace (etrace et)"
proof -
  have "ttail (etrace et) = etail et"
  proof (cases "proper_trace et")
    case False
    then show ?thesis by (simp add: etrace_def etail_def ttail_def)
  next
    case True
    then obtain c et' where et: "et = c # et'" and c: "c \<noteq> Color0"
      by (cases et) (auto simp: proper_trace_def head_color_def)
    show ?thesis
    proof (cases "even_trace et")
      case True then show ?thesis by (simp add: etrace_def etail_def etrace_perm_def)
    next
      case False
      have "permt (edge_rot (permc Eperm132 c)) (permt Eperm132 et') = permt Eperm132 (permt (edge_rot c) et')"
        using c by (simp add: permt_def edge_rot_132)
      then show ?thesis using False et c
        by (simp add: etrace_def etail_def etrace_perm_def ttail_def proper_trace_def head_color_def)
    qed
  qed
  then show ?thesis by (simp add: even_trace_def even_etail)
qed

lemma ktc_step_correct:
  assumes cl: "\<And>ctu ctr gtu. Kempe_valid h P ctu ctr GtreeEmpty gtu \<Longrightarrow>
      ktr_prop (Kempe_valid h P) (cl ctu ctr gtu) \<and>
      (\<forall>sz. Kempe_complete P (3 ^ d + sz) ctu ctr GtreeEmpty gtu \<longrightarrow>
            ktr_prop (Kempe_complete P (Suc sz)) (cl ctu ctr gtu))"
    and v: "ktr_prop (Kempe_valid h P) kr"
  shows "ktr_prop (Kempe_valid h P) (ktc_step h cl kr) \<and>
         (\<forall>sz. ktr_prop (Kempe_complete P (3 ^ d + Suc sz)) kr \<longrightarrow>
               ktr_prop (Kempe_complete P (Suc sz)) (ktc_step h cl kr))"
proof -
  obtain ctu gp where kr0: "kr = (ctu, gp)" by (cases kr)
  obtain gtr gtu where gp: "gp = GtreePair gtr gtu" by (cases gp)
  have kr: "kr = (ctu, GtreePair gtr gtu)" using kr0 gp by simp
  have V: "Kempe_valid h P ctu CtreeEmpty gtr gtu" using v kr by (simp add: ktr_prop_def)
  from V have ctu_ok: "ctree_proper (Suc h) ctu"
    and Dctu: "\<And>et. ctree_sub ctu et = (if even_trace et then gtree_sub gtr [] et + gtree_sub gtu [] et else 0)"
    and Dgtr: "\<And>w. gtree_mem gtr w \<Longrightarrow> \<not> gtree_mem gtu w \<and> init_gtree_spec (Suc h) w"
    and Dgtu: "\<And>w. gtree_mem gtu w \<Longrightarrow> init_gtree_spec (Suc h) w"
    and closedP: "\<And>w. \<not> gtree_mem gtu w \<Longrightarrow> init_gtree_spec (Suc h) w \<Longrightarrow>
                    \<exists>et. Kempe_coclosure P (ctrace et) \<and> matchpg [] et w"
    by (auto simp: Kempe_valid_def)
  have cl2: "\<And>et. Kempe_complete P m ctu CtreeEmpty gtr gtu \<Longrightarrow>
       P (ctrace et) \<or> (\<exists>e. \<not> ctree_mem ctu (permt (edge_rot e) (etrace et))) \<Longrightarrow> gtree_sub gtu [] et = 0"
    for m by (auto simp: Kempe_complete_def)
  show ?thesis
  proof (cases "ctu = CtreeEmpty")
    case True
    then show ?thesis using v kr by (simp add: ktr_prop_def Kempe_complete_def)
  next
    case ne1: False
    show ?thesis
    proof (cases "gtr = GtreeEmpty")
      case True
      then show ?thesis using v kr ne1 by (simp add: ktr_prop_def Kempe_complete_def)
    next
      case ne2: False
      show ?thesis
      proof (cases "gtu = GtreeEmpty")
        case True
        have "Kempe_valid h P CtreeEmpty CtreeEmpty GtreeEmpty GtreeEmpty"
          using closedP True by (simp add: Kempe_valid_def)
        then show ?thesis using kr ne1 ne2 True
          by (simp add: ktr_prop_def Kempe_complete_def empty_gtree_pair_def)
      next
        case ne3: False
        define r where "r = CtrCons [] gtr CtrNil"
        obtain ctu' ctr where R: "ctree_restrict h ctu r = CtreePair ctu' ctr"
          by (cases "ctree_restrict h ctu r")
        have step: "ktc_step h cl kr = cl ctu' (ctree_rotlr ctr) gtu"
          using kr ne1 ne2 ne3 R by (simp add: r_def)
        note RC = ctree_restrict_correct[OF ctu_ok, of r, unfolded R]
        have ctr_ok: "ctree_proper (Suc h) ctr" and ctu'_ok: "ctree_proper (Suc h) ctu'"
          using RC by (metis ctree_pair_sub.simps)+
        have Pctu: "\<And>et. if ctree_mem ctu et then ctree_mem ctu' et \<noteq> ctree_mem ctr et
                         else \<not> ctree_mem ctu' et \<and> \<not> ctree_mem ctr et"
          using RC by (simp add: sctree_partition_def)
        have Dctu'0: "\<And>et. ctree_sub ctu' et = ctree_sub ctu et - gtree_sub gtr [] et"
          using RC by (simp add: r_def)
        have Dctu': "\<And>et. ctree_sub ctu' et = (if even_trace et then gtree_sub gtu [] et else 0)"
          using Dctu'0 Dctu by simp
        have vctr: "Kempe_coclosure P (ctrace et0) \<and> length et0 = Suc h"
          if m0: "ctree_mem (ctree_rotlr ctr) et0" for et0
        proof -
          obtain g where ce: "ctree_mem ctr (permt g et0)"
            using m0 ctree_mem_rotlr[OF ctr_ok] by blast
          define et where "et = permt g et0"
          have ct: "ctree_mem ctu et" "\<not> ctree_mem ctu' et"
            using Pctu[of et] ce by (auto simp: et_def split: if_splits)
          have gtr_et: "gtree_sub gtr [] et \<noteq> 0" and gtu_et: "gtree_sub gtu [] et = 0"
            using ct Dctu[of et] Dctu'[of et] by (auto simp: ctree_mem_def split: if_splits)
          have "\<exists>w. gtree_mem gtr w \<and> matchpg [] et w" using gtr_et gtree_sub_0_iff[of gtr "[]" et] by simp
          then obtain w where w: "gtree_mem gtr w" "matchpg [] et w" by blast
          have len: "length et = Suc h"
            using Dgtr[OF w(1)] matchpg_size[OF w(2)] by (simp add: init_gtree_spec_def)
          have clo: "Kempe_coclosure P (ctrace et0)"
            unfolding Kempe_coclosure_def
          proof (intro allI impI)
            fix P1 assume cP1: "Kempe_closed P1" and P1e: "P1 (ctrace et0)"
            have "P1 (ctrace et)"
              using cP1 P1e by (simp add: Kempe_closed_def et_def ctrace_permt)
            then obtain w0 where w0: "matchg [] (ctrace et) w0" "\<forall>et'. matchg [] et' w0 \<longrightarrow> P1 et'"
              using cP1 by (auto simp: Kempe_closed_def)
            have bal: "gram_balanced 0 False w0"
              using matchg_balanced[OF w0(1)] by simp
            define w1 where "w1 = take (length w0 - 1) w0"
            have Dw: "w0 = cgram 0 False w1" unfolding w1_def by (rule matchg_cgram[OF w0(1)])
            have etM: "matchpg [] et w1" using w0(1) bal matchg_pg[of w1 et] Dw by simp
            have nu: "\<not> gtree_mem gtu w1" using gtu_et etM gtree_sub_0_iff[of gtu "[]" et] by blast
            have sp: "init_gtree_spec (Suc h) w1"
              using matchpg_size[OF etM] len bal Dw by (simp add: init_gtree_spec_def)
            obtain et1 where et1: "Kempe_coclosure P (ctrace et1)" "matchpg [] et1 w1"
              using closedP[OF nu sp] by blast
            have "matchg [] (ctrace et1) w0" using et1(2) bal matchg_pg[of w1 et1] Dw by simp
            then have "P1 (ctrace et1)" using w0(2) by blast
            then show "\<exists>et'. P et' \<and> P1 et'" using et1(1) cP1 by (auto simp: Kempe_coclosure_def)
          qed
          show ?thesis using clo len by (simp add: et_def)
        qed
        have gt_valid: "Kempe_valid h P ctu' (ctree_rotlr ctr) GtreeEmpty gtu"
          unfolding Kempe_valid_def using ctu'_ok Dctu' vctr Dgtu closedP by simp
        have gt_full: "Kempe_complete P sz ctu' (ctree_rotlr ctr) GtreeEmpty gtu"
          if c: "Kempe_complete P (Suc sz) ctu CtreeEmpty gtr gtu" for sz
        proof -
          have s1: "ctree_size ctu < Suc sz \<or> (\<forall>w. \<not> gtree_mem gtr w)"
            using c by (simp add: Kempe_complete_def)
          have szp: "ctree_size ctu = ctree_size ctu' + ctree_size ctr"
            using RC by (intro ctree_size_partition) simp
          have size_part: "ctree_size ctu' < sz \<or> (ctree_rotlr ctr = CtreeEmpty \<and> (\<forall>w. \<not> gtree_mem GtreeEmpty w))"
          proof (cases "\<forall>w. \<not> gtree_mem gtr w")
            case True
            then have "gtree_sub gtr [] et = 0" for et using gtree_sub_0_iff[of gtr "[]" et] by blast
            then have "ctree_mem ctu' et = ctree_mem ctu et" for et
              using Dctu'0 by (simp add: ctree_mem_def)
            then have "\<not> ctree_mem ctr et" for et using Pctu[of et] by (auto split: if_splits)
            then have "ctr = CtreeEmpty" using ctree_proper_mem[OF ctr_ok] by blast
            then show ?thesis by simp
          next
            case False
            then have lt: "ctree_size ctu < Suc sz" using s1 by blast
            show ?thesis
            proof (cases "ctree_size ctr = 0")
              case True
              then have "ctr = CtreeEmpty" by (rule ctree_size_proper[OF ctr_ok])
              then show ?thesis by simp
            next
              case False
              then show ?thesis using lt szp by simp
            qed
          qed
          have cl_part: "ctree_mem (ctree_rotlr ctr) (etrace et) \<or> gtree_sub gtu [] et = 0"
            if pe: "P (ctrace et) \<or> (\<exists>e. \<not> ctree_mem ctu' (permt (edge_rot e) (etrace et)))" for et
          proof (cases "P (ctrace et)")
            case True then show ?thesis using cl2[OF c, of et] by auto
          next
            case False
            then obtain e where ne: "\<not> ctree_mem ctu' (permt (edge_rot e) (etrace et))" using pe by blast
            define et1 where "et1 = permt (edge_rot e) (etrace et)"
            show ?thesis
            proof (cases "ctree_mem ctu' (etrace et)")
              case False
              have "gtree_sub gtu [] et = 0"
              proof (rule ccontr)
                assume "gtree_sub gtu [] et \<noteq> 0"
                then have "gtree_sub gtu [] (etrace et) \<noteq> 0" using gtree_sub_etrace[of gtu et] by simp
                then have "ctree_mem ctu' (etrace et)" using Dctu'[of "etrace et"] even_etrace
                  by (simp add: ctree_mem_def)
                then show False using False by simp
              qed
              then show ?thesis by simp
            next
              case ctu'et: True
              show ?thesis
              proof (cases "ctree_mem ctu et1")
                case False
                then have "\<exists>e. \<not> ctree_mem ctu (permt (edge_rot e) (etrace et))" using et1_def by blast
                then have "gtree_sub gtu [] et = 0" using cl2[OF c, of et] by blast
                then show ?thesis by simp
              next
                case True
                have ctr1: "ctree_mem ctr et1" using Pctu[of et1] True ne by (simp add: et1_def)
                have nctr: "\<not> ctree_mem ctr (etrace et)" using Pctu[of "etrace et"] ctu'et
                  by (auto split: if_splits)
                have "ctree_mem ctr (permt Eperm312 (etrace et)) \<or> ctree_mem ctr (permt Eperm231 (etrace et))"
                  using ctr1 nctr by (cases e) (simp_all add: et1_def)
                then show ?thesis using ctree_mem_rotlr[OF ctr_ok] by blast
              qed
            qed
          qed
          show ?thesis using size_part cl_part by (simp add: Kempe_complete_def)
        qed
        have "ktr_prop (Kempe_valid h P) (cl ctu' (ctree_rotlr ctr) gtu)" using cl[OF gt_valid] by blast
        moreover have "ktr_prop (Kempe_complete P (Suc sz)) (cl ctu' (ctree_rotlr ctr) gtu)"
          if "ktr_prop (Kempe_complete P (3 ^ d + Suc sz)) kr" for sz
        proof -
          have "Kempe_complete P (Suc (3 ^ d + sz)) ctu CtreeEmpty gtr gtu" using that kr by (simp add: ktr_prop_def)
          then have "Kempe_complete P (3 ^ d + sz) ctu' (ctree_rotlr ctr) GtreeEmpty gtu" by (rule gt_full)
          then show ?thesis using cl[OF gt_valid] by blast
        qed
        ultimately show ?thesis using step by simp
      qed
    qed
  qed
qed

theorem Kempe_tree_closure_correct:
  "Kempe_valid h P ctu ctr GtreeEmpty gtu \<Longrightarrow>
   ktr_prop (Kempe_valid h P) (Kempe_tree_closure h d ctu ctr gtu) \<and>
   (\<forall>sz. Kempe_complete P (3 ^ d + sz) ctu ctr GtreeEmpty gtu \<longrightarrow>
         ktr_prop (Kempe_complete P (Suc sz)) (Kempe_tree_closure h d ctu ctr gtu))"
proof (induction d arbitrary: ctu ctr gtu)
  case 0
  then show ?case using closure_base by blast
next
  case (Suc d)
  define K0 where "K0 = Kempe_tree_closure h d ctu ctr gtu"
  define S1 where "S1 = ktc_step h (Kempe_tree_closure h d) K0"
  define S2 where "S2 = ktc_step h (Kempe_tree_closure h d) S1"
  have I0: "ktr_prop (Kempe_valid h P) K0"
    and F1: "\<And>sz. Kempe_complete P (3 ^ d + sz) ctu ctr GtreeEmpty gtu \<Longrightarrow> ktr_prop (Kempe_complete P (Suc sz)) K0"
    using Suc.IH[OF Suc.prems] unfolding K0_def by blast+
  have I1: "ktr_prop (Kempe_valid h P) S1"
    and F2: "\<And>sz. ktr_prop (Kempe_complete P (3 ^ d + Suc sz)) K0 \<Longrightarrow> ktr_prop (Kempe_complete P (Suc sz)) S1"
    using ktc_step_correct[OF Suc.IH I0] unfolding S1_def by blast+
  have I2: "ktr_prop (Kempe_valid h P) S2"
    and F3: "\<And>sz. ktr_prop (Kempe_complete P (3 ^ d + Suc sz)) S1 \<Longrightarrow> ktr_prop (Kempe_complete P (Suc sz)) S2"
    using ktc_step_correct[OF Suc.IH I1] unfolding S2_def by blast+
  have eq: "Kempe_tree_closure h (Suc d) ctu ctr gtu = S2" by (simp add: S2_def S1_def K0_def)
  have "ktr_prop (Kempe_complete P (Suc sz)) S2"
    if c: "Kempe_complete P (3 ^ Suc d + sz) ctu ctr GtreeEmpty gtu" for sz
  proof -
    have e: "3 ^ Suc d + sz = 3 ^ d + (3 ^ d + (3 ^ d + sz))" by simp
    have c': "Kempe_complete P (3 ^ d + (3 ^ d + (3 ^ d + sz))) ctu ctr GtreeEmpty gtu" using c unfolding e .
    have "ktr_prop (Kempe_complete P (Suc (3 ^ d + (3 ^ d + sz)))) K0" by (rule F1[OF c'])
    then have "ktr_prop (Kempe_complete P (3 ^ d + Suc (3 ^ d + sz))) K0" by simp
    then have "ktr_prop (Kempe_complete P (Suc (3 ^ d + sz))) S1" by (rule F2)
    then have "ktr_prop (Kempe_complete P (3 ^ d + Suc sz)) S1" by simp
    then show ?thesis by (rule F3)
  qed
  then show ?case using I2 eq by simp
qed

lemma ctrace_butlast: "sumt cet = Color0 \<Longrightarrow> cet \<noteq> [] \<Longrightarrow> cet = ctrace (butlast cet)"
proof -
  assume s: "sumt cet = Color0" and ne: "cet \<noteq> []"
  obtain l c where l: "cet = l @ [c]" using ne by (metis append_butlast_last_id)
  have "sumt l +c c = Color0" using s l by (simp add: sumt_append)
  then have "c = sumt l" by (simp add: addc_eq0)
  then show ?thesis using l by (simp add: ctrace_def)
qed

lemma Kempe_validP:
  assumes v: "Kempe_valid h P ctu ctr gtr gtu" and len: "length et0 = Suc h"
    and nm: "\<not> ctree_mem ctu (etrace et0)"
  shows "Kempe_coclosure P (ctrace et0)"
  unfolding Kempe_coclosure_def
proof (intro allI impI)
  from v have Dctu: "\<And>et. ctree_sub ctu et = (if even_trace et then gtree_sub gtr [] et + gtree_sub gtu [] et else 0)"
    and closedP: "\<And>w. \<not> gtree_mem gtu w \<Longrightarrow> init_gtree_spec (Suc h) w \<Longrightarrow>
                    \<exists>et. Kempe_coclosure P (ctrace et) \<and> matchpg [] et w"
    by (auto simp: Kempe_valid_def)
  fix P1 assume cP1: "Kempe_closed P1" and P1e: "P1 (ctrace et0)"
  have "P1 (ctrace (etrace et0))" using cP1 P1e by (simp add: Kempe_closed_def etrace_def ctrace_permt)
  then obtain w0 where w0: "matchg [] (ctrace (etrace et0)) w0" "\<forall>et'. matchg [] et' w0 \<longrightarrow> P1 et'"
    using cP1 by (auto simp: Kempe_closed_def)
  have bal: "gram_balanced 0 False w0" using matchg_balanced[OF w0(1)] by simp
  define w where "w = take (length w0 - 1) w0"
  have Dw: "w0 = cgram 0 False w" unfolding w_def by (rule matchg_cgram[OF w0(1)])
  have etM: "matchpg [] (etrace et0) w" using w0(1) bal matchg_pg[of w "etrace et0"] Dw by simp
  have nu: "\<not> gtree_mem gtu w"
  proof
    assume "gtree_mem gtu w"
    then have "gtree_sub gtu [] (etrace et0) \<noteq> 0" using etM gtree_sub_0_iff[of gtu "[]" "etrace et0"] by blast
    then have "ctree_mem ctu (etrace et0)" using Dctu[of "etrace et0"] even_etrace by (simp add: ctree_mem_def)
    then show False using nm by simp
  qed
  have sp: "init_gtree_spec (Suc h) w"
    using matchpg_size[OF etM] len bal Dw by (simp add: init_gtree_spec_def etrace_def)
  obtain et1 where et1: "Kempe_coclosure P (ctrace et1)" "matchpg [] et1 w" using closedP[OF nu sp] by blast
  have "matchg [] (ctrace et1) w0" using et1(2) bal matchg_pg[of w et1] Dw by simp
  then have "P1 (ctrace et1)" using w0(2) by blast
  then show "\<exists>et'. P et' \<and> P1 et'" using et1(1) cP1 by (auto simp: Kempe_coclosure_def)
qed

lemma edge_rot_rot: "c \<noteq> Color0 \<Longrightarrow> permc (edge_rot (permc (edge_rot e) c)) (permc (edge_rot e) x) = permc (edge_rot c) x"
  by (cases e; cases c; cases x) simp_all

lemma ttail_rot: "ttail (permt (edge_rot e) et) = ttail et"
proof (cases "proper_trace et")
  case False
  then show ?thesis by (simp add: ttail_def)
next
  case True
  then obtain c et' where et: "et = c # et'" and c: "c \<noteq> Color0"
    by (cases et) (auto simp: proper_trace_def head_color_def)
  have pr: "proper_trace (permt (edge_rot e) et)" using True by simp
  have "ttail (permt (edge_rot e) et) = permt (edge_rot (permc (edge_rot e) c)) (permt (edge_rot e) et')"
    using pr et by (simp add: ttail_def)
  also have "\<dots> = permt (edge_rot c) et'" using c by (simp add: permt_def edge_rot_rot)
  also have "\<dots> = ttail et" using True et by (simp add: ttail_def)
  finally show ?thesis .
qed

lemma odd_count_cbit1: "odd (count_cbit1 l) = cbit1 (sumt l)"
proof (induction l)
  case (Cons c l)
  then show ?case by (cases c) (simp_all add: cbit1_addc)
qed simp

lemma Kempe_valid_restrict:
  assumes Dctr: "\<And>et. ctree_mem ctr et \<Longrightarrow> P (ctrace et) \<and> length et = Suc h"
    and v: "Kempe_valid h P ctu CtreeEmpty gtr gtu"
  shows "Kempe_valid h P ctu ctr gtr gtu"
proof -
  have "Kempe_coclosure P (ctrace et)" if "P (ctrace et)" for et
    using that by (auto simp: Kempe_coclosure_def)
  then show ?thesis using v Dctr by (simp add: Kempe_valid_def)
qed

lemma Kempe_valid_init:
  "Kempe_valid h P (ctree_init_tree (Suc h)) CtreeEmpty GtreeEmpty (gtree_init_tree (Suc h))"
proof -
  have gm: "gtree_mem (gtree_init_tree (Suc h)) = init_gtree_spec (Suc h)"
    by (rule ext) (rule gtree_mem_init_tree)
  have sub: "gtree_sub (gtree_init_tree (Suc h)) [] et =
             (if length et = Suc h \<and> Color0 \<notin> set (ctrace et) then dyck (count_cbit1 (ctrace et)) else 0)" for et
    unfolding gtree_sub_def gm by (rule match_count_balanced)
  show ?thesis unfolding Kempe_valid_def
    using ctree_init_tree_proper[of "Suc h"] by (auto simp: ctree_sub_init_tree sub gm)
qed

lemma Kempe_complete_init:
  assumes Pctr: "\<And>et. P (ctrace et) \<Longrightarrow> ctree_mem ctr (etrace et)"
  shows "Kempe_complete P (3 ^ Suc (Suc h)) (ctree_init_tree (Suc h)) ctr gtr (gtree_init_tree (Suc h))"
proof -
  have sz: "ctree_size (ctree_init_tree (Suc h)) < 3 ^ Suc (Suc h)"
  proof -
    have "ctree_size (ctree_init_tree (Suc h)) \<le> 3 ^ Suc h"
      by (rule ctree_max_size_proper[OF ctree_init_tree_proper])
    moreover have "(3::nat) ^ Suc h < 3 ^ Suc (Suc h)" by simp
    ultimately show ?thesis by linarith
  qed
  have cl: "ctree_mem ctr (etrace et) \<or> gtree_sub (gtree_init_tree (Suc h)) [] et = 0"
    if pe: "P (ctrace et) \<or> (\<exists>e. \<not> ctree_mem (ctree_init_tree (Suc h)) (permt (edge_rot e) (etrace et)))" for et
  proof (cases "P (ctrace et)")
    case True then show ?thesis using Pctr by blast
  next
    case False
    then obtain e where ne: "\<not> ctree_mem (ctree_init_tree (Suc h)) (permt (edge_rot e) (etrace et))"
      using pe by blast
    have "gtree_sub (gtree_init_tree (Suc h)) [] et = 0"
    proof (rule ccontr)
      assume "gtree_sub (gtree_init_tree (Suc h)) [] et \<noteq> 0"
      then obtain w where w: "gtree_mem (gtree_init_tree (Suc h)) w" "matchpg [] et w"
        using gtree_sub_0_iff[of "gtree_init_tree (Suc h)" "[]" et] by auto
      have sp: "length w = Suc h" "gram_balanced 0 False (cgram 0 False w)"
        using w(1) gtree_mem_init_tree by (simp_all add: init_gtree_spec_def)
      have mg: "matchg [] (ctrace et) (cgram 0 False w)" using matchg_pg[OF sp(2)] w(2) by simp
      have c0: "Color0 \<notin> set (ctrace et)" using matchg_memc0[OF mg] .
      define pe where "pe = permt (edge_rot e) (etrace et)"
      have len: "length pe = Suc h" using sp(1) matchpg_size[OF w(2)] by (simp add: pe_def etrace_def)
      have c0': "Color0 \<notin> set (ctrace pe)"
        using c0 by (simp add: pe_def etrace_def ctrace_permt)
      have ev: "even_trace pe" using even_etrace[of et] by (simp add: pe_def even_trace_def ttail_rot)
      have "even (count_cbit1 (ctrace pe))" using odd_count_cbit1[of "ctrace pe"] by simp
      then obtain m where "count_cbit1 (ctrace pe) = 2 * m" by (metis evenE)
      then have "0 < dyck (count_cbit1 (ctrace pe))" using even_dyck_pos by simp
      then have "ctree_mem (ctree_init_tree (Suc h)) pe"
        using len c0' ev by (simp add: ctree_mem_def ctree_sub_init_tree)
      then show False using ne pe_def by simp
    qed
    then show ?thesis by simp
  qed
  show ?thesis using sz cl by (simp add: Kempe_complete_def)
qed

lemma rot_cover:
  assumes "tau = Eperm123 \<or> tau = Eperm132"
  shows "\<exists>e. (\<forall>x. permc (edge_rot e) (permc tau x) = permc g x) \<or>
             (\<forall>x. permc (edge_rot e) (permc tau x) = permc Eperm132 (permc g x))"
  using assms by (cases g; cases tau) (auto simp: color_ex color_all)

lemma gtree_sub_132: "gtree_sub t [] (permt Eperm132 et) = 0 \<longleftrightarrow> gtree_sub t [] et = 0"
  by (simp add: gtree_sub_0_iff matchpg_flip)

lemma Kempe_completeP:
  assumes v: "Kempe_valid h P ctu ctr gtr gtu" and c: "Kempe_complete P 1 ctu ctr gtr gtu"
    and len: "length et0 = Suc h"
  shows "\<not> ctree_mem ctu (etrace et0) \<longleftrightarrow> Kempe_coclosure P (ctrace et0)"
proof
  assume "\<not> ctree_mem ctu (etrace et0)"
  then show "Kempe_coclosure P (ctrace et0)" by (rule Kempe_validP[OF v len])
next
  assume clP: "Kempe_coclosure P (ctrace et0)"
  from v have ctu_ok: "ctree_proper (Suc h) ctu"
    and Dctu: "\<And>et. ctree_sub ctu et = (if even_trace et then gtree_sub gtr [] et + gtree_sub gtu [] et else 0)"
    and Dgtu: "\<And>w. gtree_mem gtu w \<Longrightarrow> init_gtree_spec (Suc h) w"
    by (auto simp: Kempe_valid_def)
  from c have s1: "ctree_size ctu < 1 \<or> (ctr = CtreeEmpty \<and> (\<forall>w. \<not> gtree_mem gtr w))"
    and ce0: "\<And>et. P (ctrace et) \<or> (\<exists>e. \<not> ctree_mem ctu (permt (edge_rot e) (etrace et))) \<Longrightarrow>
                 ctree_mem ctr (etrace et) \<or> gtree_sub gtu [] et = 0"
    by (auto simp: Kempe_complete_def)
  show "\<not> ctree_mem ctu (etrace et0)"
  proof (cases "ctree_size ctu < 1")
    case True
    then have "ctu = CtreeEmpty" using ctree_size_proper[OF ctu_ok] by simp
    then show ?thesis by simp
  next
    case False
    then have ctr0: "ctr = CtreeEmpty" and gtr0: "\<And>w. \<not> gtree_mem gtr w" using s1 by auto
    have sgtr: "gtree_sub gtr [] et = 0" for et using gtr0 gtree_sub_0_iff[of gtr "[]" et] by blast
    have memctu: "ctree_mem ctu et \<longleftrightarrow> even_trace et \<and> gtree_sub gtu [] et \<noteq> 0" for et
      using Dctu[of et] sgtr[of et] by (simp add: ctree_mem_def)
    have ce: "\<And>et. P (ctrace et) \<or> (\<exists>e. \<not> ctree_mem ctu (permt (edge_rot e) (etrace et))) \<Longrightarrow>
                 gtree_sub gtu [] et = 0" using ce0 ctr0 by auto
    have tau: "etrace_perm et = Eperm123 \<or> etrace_perm et = Eperm132" for et
      by (simp add: etrace_perm_def)
    have sub_tau: "gtree_sub gtu [] (permt (etrace_perm et) y) = 0 \<longleftrightarrow> gtree_sub gtu [] y = 0" for et y
      using tau[of et] gtree_sub_132 by auto
    define P1 where "P1 cet \<longleftrightarrow> (\<exists>et. cet = ctrace et \<and> ctree_mem ctu (etrace et))" for cet
    show ?thesis
    proof
      assume m0: "ctree_mem ctu (etrace et0)"
      have closed: "Kempe_closed P1"
        unfolding Kempe_closed_def
      proof (intro allI impI conjI)
        fix cet assume "P1 cet"
        then obtain et where cet: "cet = ctrace et" and m: "ctree_mem ctu (etrace et)"
          by (auto simp: P1_def)
        fix g
        show "P1 (permt g cet)"
        proof (rule ccontr)
          assume nP: "\<not> P1 (permt g cet)"
          have nm: "\<not> ctree_mem ctu (etrace (permt g et))"
            using nP cet by (auto simp: P1_def ctrace_permt)
          have z1: "gtree_sub gtu [] (permt g et) = 0"
            using nm memctu[of "etrace (permt g et)"] even_etrace[of "permt g et"] sub_tau[of "permt g et" "permt g et"]
            by (simp add: etrace_def)
          have z2: "gtree_sub gtu [] (permt Eperm132 (permt g et)) = 0" using z1 gtree_sub_132 by simp
          obtain e where e: "(\<forall>x. permc (edge_rot e) (permc (etrace_perm et) x) = permc g x) \<or>
              (\<forall>x. permc (edge_rot e) (permc (etrace_perm et) x) = permc Eperm132 (permc g x))"
            using rot_cover[OF tau[of et]] by blast
          have "permt (edge_rot e) (etrace et) = permt g et \<or>
                permt (edge_rot e) (etrace et) = permt Eperm132 (permt g et)"
            using e by (auto simp: etrace_def permt_def)
          then have "\<not> ctree_mem ctu (permt (edge_rot e) (etrace et))"
            using z1 z2 memctu by auto
          then have "gtree_sub gtu [] et = 0" using ce by blast
          then have "gtree_sub gtu [] (etrace et) = 0" using gtree_sub_etrace by simp
          then show False using m memctu by simp
        qed
      next
        fix cet assume "P1 cet"
        then obtain et where cet: "cet = ctrace et" and m: "ctree_mem ctu (etrace et)"
          by (auto simp: P1_def)
        have "gtree_sub gtu [] (etrace et) \<noteq> 0" using m memctu by simp
        then obtain w where w: "gtree_mem gtu w" "matchpg [] (etrace et) w"
          using gtree_sub_0_iff[of gtu "[]" "etrace et"] by auto
        have bal: "gram_balanced 0 False (cgram 0 False w)" using Dgtu[OF w(1)] by (simp add: init_gtree_spec_def)
        have mg: "matchg [] cet (cgram 0 False w)"
          using matchg_pg[OF bal] w(2) cet by (simp add: matchpg_etrace)
        have "P1 cet'" if mc: "matchg [] cet' (cgram 0 False w)" for cet'
        proof -
          have s0: "sumt cet' = Color0" by (rule balanced_sumt0[OF bal mc])
          have "length cet' = length (cgram 0 False w)" using matchg_size[OF mc] by simp
          then have ne: "cet' \<noteq> []" by auto
          define et1 where "et1 = butlast cet'"
          have ce1: "cet' = ctrace et1" unfolding et1_def by (rule ctrace_butlast[OF s0 ne])
          have "matchpg [] et1 w" using mc ce1 matchg_pg[OF bal] by simp
          then have "matchpg [] (etrace et1) w" by (simp add: matchpg_etrace)
          then have "gtree_sub gtu [] (etrace et1) \<noteq> 0" using w(1) gtree_sub_0_iff[of gtu "[]" "etrace et1"] by auto
          then have "ctree_mem ctu (etrace et1)" using memctu even_etrace by simp
          then show ?thesis using ce1 by (auto simp: P1_def)
        qed
        then show "\<exists>w'. matchg [] cet w' \<and> (\<forall>et'. matchg [] et' w' \<longrightarrow> P1 et')" using mg by blast
      qed
      have "P1 (ctrace et0)" using m0 by (auto simp: P1_def)
      then obtain cet where cet: "P cet" "P1 cet" using clP closed by (auto simp: Kempe_coclosure_def)
      then obtain et2 where e2: "cet = ctrace et2" "ctree_mem ctu (etrace et2)" by (auto simp: P1_def)
      have "gtree_sub gtu [] et2 = 0" using ce[of et2] cet(1) e2(1) by blast
      then have "gtree_sub gtu [] (etrace et2) = 0" using gtree_sub_etrace by simp
      then show False using e2(2) memctu by simp
    qed
  qed
qed

section \<open>The Kempe tree of a configuration\<close>

definition Kempe_tree :: "cprog \<Rightarrow> ctree" where
  "Kempe_tree cp = (case cprsize cp of
       Suc (Suc h) \<Rightarrow> fst (Kempe_tree_closure h (Suc (Suc h)) (ctree_init_tree (Suc h)) (cpcolor cp)
                            (gtree_init_tree (Suc h)))
     | _ \<Rightarrow> CtreeEmpty)"

lemma rot1_eq_snoc:
  assumes "rot 1 l = et @ [s]"
  shows "l = s # et"
proof (cases l)
  case Nil
  then show ?thesis using assms by (simp add: rot_def)
next
  case (Cons a l')
  then show ?thesis using assms by (simp add: rot_def)
qed

theorem Kempe_treeP:
  assumes len: "length et = cprsize cp - 1"
  shows "\<not> ctree_mem (Kempe_tree cp) (etrace et) \<longleftrightarrow>
         Kempe_coclosure (ring_trace (cpG cp) (rot 1 (cpring_of cp))) (ctrace et)"
proof -
  define Pcol where "Pcol = ring_trace (cpG cp) (rot 1 (cpring_of cp))"
  have szr: "length (cpring_of cp) = cprsize cp" by (rule size_ring_cpmap)
  have rne: "cpring_of cp \<noteq> []"
    using hypermap.cpring_ne[OF hypermap_cpmap] by (simp add: cpring_of_def)
  consider "cprsize cp = Suc 0" | h where "cprsize cp = Suc (Suc h)"
    using szr rne by (cases "cprsize cp"; cases "cprsize cp - 1") auto
  then show ?thesis
  proof cases
    case 1
    then have e: "et = []" using len by simp
    have "Kempe_coclosure Pcol (ctrace et)"
      unfolding Kempe_coclosure_def
    proof (intro allI impI)
      fix P1 assume "Kempe_closed P1" "P1 (ctrace et)"
      then obtain w where "matchg [] (ctrace et) w" by (auto simp: Kempe_closed_def)
      then have "Color0 \<notin> set (ctrace et)" by (rule matchg_memc0)
      then show "\<exists>et'. Pcol et' \<and> P1 et'" using e by (simp add: ctrace_def)
    qed
    then show ?thesis using 1 by (simp add: Kempe_tree_def Pcol_def)
  next
    case (2 h)
    define ctu where "ctu = ctree_init_tree (Suc h)"
    define gtu where "gtu = gtree_init_tree (Suc h)"
    define ctr where "ctr = cpcolor cp"
    have Dctr: "ctree_mem ctr et1 \<longleftrightarrow> even_trace et1 \<and> ring_trace (cpG cp) (cpring_of cp) (sumt et1 # et1)" for et1
      unfolding ctr_def by (rule ctree_mem_cpcolor)
    have rt: "Pcol (ctrace et1) \<and> length et1 = Suc h" if m: "ctree_mem ctr et1" for et1
    proof -
      obtain k where col: "coloring (cpG cp) k" and tr: "sumt et1 # et1 = trace (map k (cpring_of cp))"
        using m Dctr by (auto simp: ring_trace_def)
      have "trace (map k (rot 1 (cpring_of cp))) = rot 1 (trace (map k (cpring_of cp)))"
        by (simp add: rot_map[symmetric] trace_rot)
      also have "\<dots> = ctrace et1" using tr[symmetric] by (simp add: rot_def ctrace_def)
      finally have "Pcol (ctrace et1)" using col by (auto simp: Pcol_def ring_trace_def)
      moreover have "length et1 = Suc h"
        using arg_cong[OF tr, of length] szr 2 by simp
      ultimately show ?thesis by blast
    qed
    have v0: "Kempe_valid h Pcol ctu ctr GtreeEmpty gtu"
      unfolding ctu_def gtu_def by (rule Kempe_valid_restrict[OF rt Kempe_valid_init])
    have pc: "ctree_mem ctr (etrace et1)" if hp: "Pcol (ctrace et1)" for et1
    proof -
      obtain k where col: "coloring (cpG cp) k" and tr: "ctrace et1 = trace (map k (rot 1 (cpring_of cp)))"
        using hp by (auto simp: Pcol_def ring_trace_def)
      have "rot 1 (trace (map k (cpring_of cp))) = et1 @ [sumt et1]"
        using tr by (simp add: rot_map[symmetric] trace_rot ctrace_def)
      then have t0: "trace (map k (cpring_of cp)) = sumt et1 # et1" by (rule rot1_eq_snoc)
      define g where "g = etrace_perm et1"
      define k' where "k' x = permc g (k x)" for x
      have colk': "coloring (cpG cp) k'" using col by (simp add: coloring_def k'_def permc_inj)
      have mk: "map k' (cpring_of cp) = permt g (map k (cpring_of cp))" by (simp add: k'_def permt_def)
      have "trace (map k' (cpring_of cp)) = permt g (sumt et1 # et1)" unfolding mk trace_permt t0 ..
      also have "\<dots> = sumt (etrace et1) # etrace et1" by (simp add: etrace_def g_def sumt_permt)
      finally show ?thesis using Dctr colk' even_etrace by (auto simp: ring_trace_def)
    qed
    have cinit: "Kempe_complete Pcol (3 ^ Suc (Suc h)) ctu ctr GtreeEmpty gtu"
      unfolding ctu_def gtu_def by (rule Kempe_complete_init[OF pc])
    note KC = Kempe_tree_closure_correct[OF v0, of "Suc (Suc h)"]
    obtain ctu' gtr' gtu' where R: "Kempe_tree_closure h (Suc (Suc h)) ctu ctr gtu = (ctu', GtreePair gtr' gtu')"
      by (metis gtree_pair.exhaust prod.exhaust)
    have v': "Kempe_valid h Pcol ctu' CtreeEmpty gtr' gtu'" using KC R by (simp add: ktr_prop_def)
    have c': "Kempe_complete Pcol 1 ctu' CtreeEmpty gtr' gtu'"
      using KC R cinit by (simp add: ktr_prop_def)
    have kt: "Kempe_tree cp = ctu'" using R 2 by (simp add: Kempe_tree_def ctu_def gtu_def ctr_def)
    have "length et = Suc h" using len 2 by simp
    then show ?thesis using Kempe_completeP[OF v' c'] kt by (simp add: Pcol_def)
  qed
qed

end
