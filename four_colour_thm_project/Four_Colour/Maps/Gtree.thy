(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Gtree.thy
    Trees representing sets of (partial) chromograms, and matching counts.
    Ported from G. Gonthier's Coq development (gtree.v).
*)
theory Gtree
  imports Chromogram
begin

datatype gtree = GtreeNode gtree gtree gtree gtree
  | GtreeLeaf0 | GtreeLeaf1 | GtreeLeaf2 | GtreeLeaf3
  | GtreeLeaf01 | GtreeLeaf12 | GtreeLeaf13 | GtreeLeaf23
  | GtreeEmpty

definition gram_symbol_rec :: "'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> gram_symbol \<Rightarrow> 'b" where
  "gram_symbol_rec a0 a1 a2 a3 s = (case s of Gpush \<Rightarrow> a0 | Gskip \<Rightarrow> a1 | Gpop0 \<Rightarrow> a2 | Gpop1 \<Rightarrow> a3)"

lemma gram_symbol_rec_simps [simp]:
  "gram_symbol_rec a0 a1 a2 a3 Gpush = a0" "gram_symbol_rec a0 a1 a2 a3 Gskip = a1"
  "gram_symbol_rec a0 a1 a2 a3 Gpop0 = a2" "gram_symbol_rec a0 a1 a2 a3 Gpop1 = a3"
  by (simp_all add: gram_symbol_rec_def)

lemma gram_symbol_rec_same [simp]: "gram_symbol_rec a a a a s = a"
  by (cases s) simp_all

fun gtree_mem :: "gtree \<Rightarrow> chromogram \<Rightarrow> bool" where
  "gtree_mem (GtreeNode t0 t1 t2 t3) (s # w) = gtree_mem (gram_symbol_rec t0 t1 t2 t3 s) w"
| "gtree_mem GtreeLeaf0 [Gpush] = True"
| "gtree_mem GtreeLeaf1 [Gskip] = True"
| "gtree_mem GtreeLeaf2 [Gpop0] = True"
| "gtree_mem GtreeLeaf3 [Gpop1] = True"
| "gtree_mem GtreeLeaf01 [Gpush] = True"
| "gtree_mem GtreeLeaf01 [Gskip] = True"
| "gtree_mem GtreeLeaf12 [Gskip] = True"
| "gtree_mem GtreeLeaf12 [Gpop0] = True"
| "gtree_mem GtreeLeaf13 [Gskip] = True"
| "gtree_mem GtreeLeaf13 [Gpop1] = True"
| "gtree_mem GtreeLeaf23 [Gpop0] = True"
| "gtree_mem GtreeLeaf23 [Gpop1] = True"
| "gtree_mem _ _ = False"

type_synonym spec_ctree = "colseq \<Rightarrow> bool"
type_synonym spec_gtree = "chromogram \<Rightarrow> bool"

fun has_match :: "bool list \<Rightarrow> spec_ctree \<Rightarrow> chromogram \<Rightarrow> bool" where
  "has_match bs ct [] = ct []"
| "has_match bs ct (Gpush # w) =
     (has_match (False # bs) (\<lambda>et. ct (Color2 # et)) w \<or> has_match (True # bs) (\<lambda>et. ct (Color3 # et)) w)"
| "has_match bs ct (Gskip # w) = has_match bs (\<lambda>et. ct (Color1 # et)) w"
| "has_match (False # bs) ct (Gpop0 # w) = has_match bs (\<lambda>et. ct (Color2 # et)) w"
| "has_match (True # bs) ct (Gpop0 # w) = has_match bs (\<lambda>et. ct (Color3 # et)) w"
| "has_match [] ct (Gpop0 # w) = False"
| "has_match (False # bs) ct (Gpop1 # w) = has_match bs (\<lambda>et. ct (Color3 # et)) w"
| "has_match (True # bs) ct (Gpop1 # w) = has_match bs (\<lambda>et. ct (Color2 # et)) w"
| "has_match [] ct (Gpop1 # w) = False"

lemma matchpg_Nil_w [simp]: "matchpg bs et [] \<longleftrightarrow> et = []"
  by (cases et) simp_all

lemma matchpg_et_Nil [simp]: "matchpg bs [] w \<longleftrightarrow> w = []"
  by (cases w) simp_all

lemma ex_step:
  "(\<exists>et. ct et \<and> matchpg bs et (s # w)) \<longleftrightarrow>
   (\<exists>e l. mstep e s bs = Some l \<and> (\<exists>et. ct (e # et) \<and> matchpg l et w))"
proof
  assume "\<exists>et. ct et \<and> matchpg bs et (s # w)"
  then obtain et where h: "ct et" "matchpg bs et (s # w)" by blast
  then obtain e et' where et: "et = e # et'" by (cases et) auto
  then show "\<exists>e l. mstep e s bs = Some l \<and> (\<exists>et. ct (e # et) \<and> matchpg l et w)"
    using h by (auto split: option.splits)
next
  assume "\<exists>e l. mstep e s bs = Some l \<and> (\<exists>et. ct (e # et) \<and> matchpg l et w)"
  then show "\<exists>et. ct et \<and> matchpg bs et (s # w)" by force
qed

lemma has_matchP: "has_match bs ct w \<longleftrightarrow> (\<exists>et. ct et \<and> matchpg bs et w)"
proof (induction bs ct w rule: has_match.induct)
  case (1 bs ct)
  then show ?case by simp
qed (simp only: ex_step has_match.simps; auto simp: mstep_Some_iff)+

fun match_count :: "spec_gtree \<Rightarrow> bool list \<Rightarrow> colseq \<Rightarrow> nat" where
  "match_count st bs [] = (if st [] then 1 else 0)"
| "match_count st bs (Color0 # et) = 0"
| "match_count st bs (Color1 # et) = match_count (\<lambda>w. st (Gskip # w)) bs et"
| "match_count st bs (Color2 # et) =
     match_count (\<lambda>w. st (Gpush # w)) (False # bs) et +
     (case bs of [] \<Rightarrow> 0
      | b # bs' \<Rightarrow> if b then match_count (\<lambda>w. st (Gpop1 # w)) bs' et
                  else match_count (\<lambda>w. st (Gpop0 # w)) bs' et)"
| "match_count st bs (Color3 # et) =
     match_count (\<lambda>w. st (Gpush # w)) (True # bs) et +
     (case bs of [] \<Rightarrow> 0
      | b # bs' \<Rightarrow> if b then match_count (\<lambda>w. st (Gpop0 # w)) bs' et
                  else match_count (\<lambda>w. st (Gpop1 # w)) bs' et)"

definition gtree_sub :: "gtree \<Rightarrow> bool list \<Rightarrow> colseq \<Rightarrow> nat" where
  "gtree_sub t = match_count (gtree_mem t)"

lemma ex_chromogram_Cons:
  "(\<exists>w. P w \<and> matchpg bs (e # et) w) \<longleftrightarrow> (\<exists>s w. P (s # w) \<and> matchpg bs (e # et) (s # w))"
proof
  assume "\<exists>w. P w \<and> matchpg bs (e # et) w"
  then obtain w where h: "P w" "matchpg bs (e # et) w" by blast
  then obtain s w' where "w = s # w'" by (cases w) auto
  then show "\<exists>s w. P (s # w) \<and> matchpg bs (e # et) (s # w)" using h by blast
qed blast

lemma ex_stepw:
  "(\<exists>w. st w \<and> matchpg bs (e # et) w) \<longleftrightarrow>
   (\<exists>s l. mstep e s bs = Some l \<and> (\<exists>w. st (s # w) \<and> matchpg l et w))"
proof
  assume "\<exists>w. st w \<and> matchpg bs (e # et) w"
  then obtain w where h: "st w" "matchpg bs (e # et) w" by blast
  then obtain s w' where w: "w = s # w'" by (cases w) auto
  then show "\<exists>s l. mstep e s bs = Some l \<and> (\<exists>w. st (s # w) \<and> matchpg l et w)"
    using h by (auto split: option.splits)
next
  assume "\<exists>s l. mstep e s bs = Some l \<and> (\<exists>w. st (s # w) \<and> matchpg l et w)"
  then show "\<exists>w. st w \<and> matchpg bs (e # et) w" by force
qed

lemma match_countP: "match_count st bs et \<noteq> 0 \<longleftrightarrow> (\<exists>w. st w \<and> matchpg bs et w)"
proof (induction st bs et rule: match_count.induct)
  case (1 st bs)
  then show ?case by auto
qed (simp only: ex_stepw match_count.simps;
     auto simp: mstep_Some_iff split: list.splits if_splits)+

definition gtree_empty4 :: "gtree \<Rightarrow> bool" where
  "gtree_empty4 t \<longleftrightarrow> t = GtreeNode GtreeEmpty GtreeEmpty GtreeEmpty GtreeEmpty"

datatype gtree_pair = GtreePair gtree gtree

definition empty_gtree_pair :: gtree_pair where
  "empty_gtree_pair = GtreePair GtreeEmpty GtreeEmpty"

fun gtree_pair_sub :: "gtree_pair \<Rightarrow> bool \<Rightarrow> gtree" where
  "gtree_pair_sub (GtreePair t0 t1) b = (if b then t1 else t0)"

definition sgtree_partition :: "spec_gtree \<Rightarrow> spec_gtree \<Rightarrow> spec_gtree \<Rightarrow> bool" where
  "sgtree_partition st st' st'' \<longleftrightarrow>
     (\<forall>w. (st w \<longrightarrow> st' w \<noteq> st'' w) \<and> (\<not> st w \<longrightarrow> \<not> st' w \<and> \<not> st'' w))"

fun gtree_pair_partition :: "gtree \<Rightarrow> gtree_pair \<Rightarrow> bool" where
  "gtree_pair_partition t (GtreePair t0 t1) = sgtree_partition (gtree_mem t) (gtree_mem t0) (gtree_mem t1)"

lemma match_count_0: "(\<And>w. \<not> st w) \<Longrightarrow> match_count st bs et = 0"
  using match_countP by blast

lemma gtree_mem_empty [simp]: "\<not> gtree_mem GtreeEmpty w"
  by (cases w) simp_all

lemma gtree_sub_empty [simp]: "gtree_sub GtreeEmpty bs et = 0"
  by (simp add: gtree_sub_def match_count_0)

lemma gtree_sub_node_0:
  "length et \<le> 1 \<Longrightarrow> gtree_sub (GtreeNode t0 t1 t2 t3) bs et = 0"
proof -
  assume l: "length et \<le> 1"
  have "\<not> gtree_mem (GtreeNode t0 t1 t2 t3) w" if "matchpg bs et w" for w
  proof -
    have "length w = length et" using that matchpg_size by blast
    then have lw: "length w \<le> 1" using l by simp
    then have "w = [] \<or> (\<exists>s. w = [s])" by (cases w; cases "tl w") auto
    then show ?thesis
    proof
      assume "\<exists>s. w = [s]"
      then obtain s where w: "w = [s]" by blast
      have "\<not> gtree_mem t [] " for t by (cases t) simp_all
      then show ?thesis using w by (cases s) simp_all
    qed simp
  qed
  then show ?thesis using match_countP[of "gtree_mem (GtreeNode t0 t1 t2 t3)" bs et]
    by (auto simp: gtree_sub_def)
qed

lemma match_count_partition:
  "sgtree_partition st st' st'' \<Longrightarrow> match_count st bs et = match_count st' bs et + match_count st'' bs et"
proof (induction et arbitrary: st st' st'' bs)
  case Nil
  then show ?case by (auto simp: sgtree_partition_def)
next
  case (Cons e et)
  have p: "sgtree_partition (\<lambda>w. st (s # w)) (\<lambda>w. st' (s # w)) (\<lambda>w. st'' (s # w))" for s
    using Cons.prems by (simp add: sgtree_partition_def)
  note IH = Cons.IH[OF p]
  show ?case
  proof (cases e)
    case Color0
    then show ?thesis by simp
  next
    case Color1
    then show ?thesis using IH by simp
  next
    case Color2
    then show ?thesis using IH by (cases bs; cases "hd bs") simp_all
  next
    case Color3
    then show ?thesis using IH by (cases bs; cases "hd bs") simp_all
  qed
qed

definition gtree_cons_pairs :: "gtree \<Rightarrow> gtree_pair \<Rightarrow> gtree_pair \<Rightarrow> gtree_pair \<Rightarrow> gtree_pair \<Rightarrow> gtree_pair" where
  "gtree_cons_pairs t pt0 pt1 pt2 pt3 =
     (case (pt0, pt1, pt2, pt3) of
       (GtreePair t'0 t''0, GtreePair t'1 t''1, GtreePair t'2 t''2, GtreePair t'3 t''3) \<Rightarrow>
         (let t' = GtreeNode t'0 t'1 t'2 t'3; t'' = GtreeNode t''0 t''1 t''2 t''3 in
          if gtree_empty4 t' then GtreePair t'0 t
          else if gtree_empty4 t'' then GtreePair t t''0
          else GtreePair t' t''))"

lemma gtree_mem_node_Nil [simp]: "\<not> gtree_mem (GtreeNode a b c d) []"
  by simp

lemma gtree_cons_pairs_partition:
  assumes "gtree_pair_partition t0 pt0" "gtree_pair_partition t1 pt1"
    "gtree_pair_partition t2 pt2" "gtree_pair_partition t3 pt3"
  shows "gtree_pair_partition (GtreeNode t0 t1 t2 t3)
           (gtree_cons_pairs (GtreeNode t0 t1 t2 t3) pt0 pt1 pt2 pt3)"
proof -
  obtain t'0 t''0 t'1 t''1 t'2 t''2 t'3 t''3 where
    p: "pt0 = GtreePair t'0 t''0" "pt1 = GtreePair t'1 t''1" "pt2 = GtreePair t'2 t''2" "pt3 = GtreePair t'3 t''3"
    by (cases pt0; cases pt1; cases pt2; cases pt3) auto
  have P: "sgtree_partition (gtree_mem t0) (gtree_mem t'0) (gtree_mem t''0)"
    "sgtree_partition (gtree_mem t1) (gtree_mem t'1) (gtree_mem t''1)"
    "sgtree_partition (gtree_mem t2) (gtree_mem t'2) (gtree_mem t''2)"
    "sgtree_partition (gtree_mem t3) (gtree_mem t'3) (gtree_mem t''3)"
    using assms p by simp_all
  have node: "sgtree_partition (gtree_mem (GtreeNode t0 t1 t2 t3))
                (gtree_mem (GtreeNode t'0 t'1 t'2 t'3)) (gtree_mem (GtreeNode t''0 t''1 t''2 t''3))"
    unfolding sgtree_partition_def
  proof
    fix w show "(gtree_mem (GtreeNode t0 t1 t2 t3) w \<longrightarrow>
       gtree_mem (GtreeNode t'0 t'1 t'2 t'3) w \<noteq> gtree_mem (GtreeNode t''0 t''1 t''2 t''3) w) \<and>
      (\<not> gtree_mem (GtreeNode t0 t1 t2 t3) w \<longrightarrow>
       \<not> gtree_mem (GtreeNode t'0 t'1 t'2 t'3) w \<and> \<not> gtree_mem (GtreeNode t''0 t''1 t''2 t''3) w)"
      using P by (cases w; cases "hd w") (auto simp: sgtree_partition_def)
  qed
  have e1: "sgtree_partition (gtree_mem t) (gtree_mem GtreeEmpty) (gtree_mem t)" for t
    by (simp add: sgtree_partition_def)
  have e2: "sgtree_partition (gtree_mem t) (gtree_mem t) (gtree_mem GtreeEmpty)" for t
    by (simp add: sgtree_partition_def)
  show ?thesis
    using node e1 e2 p by (auto simp: gtree_cons_pairs_def gtree_empty4_def Let_def)
qed

lemma gtree_mem0_cons_pairs:
  assumes "gtree_pair_partition t0 pt0" "gtree_pair_partition t1 pt1"
    "gtree_pair_partition t2 pt2" "gtree_pair_partition t3 pt3"
  shows "gtree_mem (gtree_pair_sub (gtree_cons_pairs (GtreeNode t0 t1 t2 t3) pt0 pt1 pt2 pt3) False) w =
         gtree_mem (GtreeNode (gtree_pair_sub pt0 False) (gtree_pair_sub pt1 False)
                              (gtree_pair_sub pt2 False) (gtree_pair_sub pt3 False)) w"
proof -
  obtain t'0 t''0 t'1 t''1 t'2 t''2 t'3 t''3 where
    p: "pt0 = GtreePair t'0 t''0" "pt1 = GtreePair t'1 t''1" "pt2 = GtreePair t'2 t''2" "pt3 = GtreePair t'3 t''3"
    by (cases pt0; cases pt1; cases pt2; cases pt3) auto
  have P: "sgtree_partition (gtree_mem t0) (gtree_mem t'0) (gtree_mem t''0)"
    "sgtree_partition (gtree_mem t1) (gtree_mem t'1) (gtree_mem t''1)"
    "sgtree_partition (gtree_mem t2) (gtree_mem t'2) (gtree_mem t''2)"
    "sgtree_partition (gtree_mem t3) (gtree_mem t'3) (gtree_mem t''3)"
    using assms p by simp_all
  show ?thesis
  proof (cases "gtree_empty4 (GtreeNode t'0 t'1 t'2 t'3)")
    case True
    then show ?thesis using p by (cases w) (auto simp: gtree_cons_pairs_def gtree_empty4_def)
  next
    case F1: False
    show ?thesis
    proof (cases "gtree_empty4 (GtreeNode t''0 t''1 t''2 t''3)")
      case True
      then have e: "t''0 = GtreeEmpty" "t''1 = GtreeEmpty" "t''2 = GtreeEmpty" "t''3 = GtreeEmpty"
        by (simp_all add: gtree_empty4_def)
      have "gtree_mem ti v = gtree_mem t'i v"
        if "sgtree_partition (gtree_mem ti) (gtree_mem t'i) (gtree_mem GtreeEmpty)" for ti t'i v
        using that by (auto simp: sgtree_partition_def)
      then show ?thesis using F1 True P e p
        by (cases w; cases "hd w") (auto simp: gtree_cons_pairs_def Let_def)
    next
      case False
      then show ?thesis using F1 p by (simp add: gtree_cons_pairs_def Let_def)
    qed
  qed
qed

end
