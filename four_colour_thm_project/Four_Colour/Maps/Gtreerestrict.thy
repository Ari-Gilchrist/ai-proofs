(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Gtreerestrict.thy
    First phase of a D-reducibility step: removing the chromograms matching
    a set of admissible colorings from a chromogram tree.
    Ported from G. Gonthier's Coq development (gtreerestrict.v).

    Design note: the continuation-passing gtr_split returns a 4-tuple here, and
    the gtr_match0..3 optimisations are replaced by gtr_mem r [s] (equal by
    gtr_matchiE in the original).
*)
theory Gtreerestrict
  imports Four_Colour_Maps.Gtree Four_Colour_Maps.Ctree
begin

datatype gtree_restriction = GtrNil | GtrCons "bool list" ctree gtree_restriction

fun gtr_mem :: "gtree_restriction \<Rightarrow> chromogram \<Rightarrow> bool" where
  "gtr_mem GtrNil w = False"
| "gtr_mem (GtrCons bs t r) w = (has_match bs (ctree_mem t) w \<or> gtr_mem r w)"

definition gtr_cons :: "bool list \<Rightarrow> ctree \<Rightarrow> gtree_restriction \<Rightarrow> gtree_restriction" where
  "gtr_cons bs t r = (if t = CtreeEmpty then r else GtrCons bs t r)"

lemma has_match_empty [simp]: "\<not> has_match bs (ctree_mem CtreeEmpty) w"
  by (simp add: has_matchP)

lemma gtr_mem_cons [simp]: "gtr_mem (gtr_cons bs t r) w = (has_match bs (ctree_mem t) w \<or> gtr_mem r w)"
  by (simp add: gtr_cons_def)

section \<open>Splitting\<close>

definition gcons_pop :: "bool list \<Rightarrow> ctree \<Rightarrow> ctree \<Rightarrow> gtree_restriction \<Rightarrow> gtree_restriction" where
  "gcons_pop bs t t' r = (case bs of [] \<Rightarrow> r | b # bs' \<Rightarrow> gtr_cons bs' (if b then t' else t) r)"

type_synonym gtr4 = "gtree_restriction \<times> gtree_restriction \<times> gtree_restriction \<times> gtree_restriction"

fun gtr_split :: "gtree_restriction \<Rightarrow> gtree_restriction \<Rightarrow> gtree_restriction \<Rightarrow> gtree_restriction \<Rightarrow>
                  gtree_restriction \<Rightarrow> gtr4" where
  "gtr_split r0 r1 r2 r3 GtrNil = (r0, r1, r2, r3)"
| "gtr_split r0 r1 r2 r3 (GtrCons bs (CtreeNode t1 t2 t3) r) =
     gtr_split (gtr_cons (False # bs) t2 (gtr_cons (True # bs) t3 r0)) (gtr_cons bs t1 r1)
               (gcons_pop bs t2 t3 r2) (gcons_pop bs t3 t2 r3) r"
| "gtr_split r0 r1 r2 r3 (GtrCons bs _ r) = gtr_split r0 r1 r2 r3 r"

definition gsel :: "gtr4 \<Rightarrow> gram_symbol \<Rightarrow> gtree_restriction" where
  "gsel p s = (case p of (a, b, c, d) \<Rightarrow> gram_symbol_rec a b c d s)"

definition gsplit :: "gtree_restriction \<Rightarrow> gram_symbol \<Rightarrow> gtree_restriction" where
  "gsplit r s = gsel (gtr_split GtrNil GtrNil GtrNil GtrNil r) s"

lemma has_match_nonnode:
  assumes "\<And>t1 t2 t3. ct \<noteq> CtreeNode t1 t2 t3"
  shows "\<not> has_match bs (ctree_mem ct) (s # w)"
proof
  assume "has_match bs (ctree_mem ct) (s # w)"
  then obtain et where h: "ctree_mem ct et" "matchpg bs et (s # w)" by (auto simp: has_matchP)
  then obtain e et' where "et = e # et'" by (cases et) auto
  then show False using h(1) assms by (cases ct) (auto simp: ctree_mem_def)
qed

lemma ctree_mem_node_sel [simp]:
  "ctree_mem (CtreeNode t1 t2 t3) (Color1 # et) = ctree_mem t1 et"
  "ctree_mem (CtreeNode t1 t2 t3) (Color2 # et) = ctree_mem t2 et"
  "ctree_mem (CtreeNode t1 t2 t3) (Color3 # et) = ctree_mem t3 et"
  by (simp_all add: ctree_mem_def)

lemma gtr_mem_split_gen:
  "gtr_mem (gsel (gtr_split r0 r1 r2 r3 r) s) w = (gtr_mem (gsel (r0, r1, r2, r3) s) w \<or> gtr_mem r (s # w))"
proof (induction r0 r1 r2 r3 r rule: gtr_split.induct)
  case (2 r0 r1 r2 r3 bs t1 t2 t3 r)
  have key: "gtr_mem (gsel (gtr_cons (False # bs) t2 (gtr_cons (True # bs) t3 r0), gtr_cons bs t1 r1,
               gcons_pop bs t2 t3 r2, gcons_pop bs t3 t2 r3) s) w =
             (gtr_mem (gsel (r0, r1, r2, r3) s) w \<or> has_match bs (ctree_mem (CtreeNode t1 t2 t3)) (s # w))"
  proof (cases s)
    case Gpop0
    then show ?thesis by (cases bs; cases "hd bs") (auto simp: gsel_def gcons_pop_def)
  next
    case Gpop1
    then show ?thesis by (cases bs; cases "hd bs") (auto simp: gsel_def gcons_pop_def)
  qed (auto simp: gsel_def)
  show ?case using 2 key by auto
qed (auto simp: has_match_nonnode)

lemma gtr_mem_gsplit: "gtr_mem r (s # w) = gtr_mem (gsplit r s) w"
  using gtr_mem_split_gen[of GtrNil GtrNil GtrNil GtrNil r s w]
  by (cases s) (simp_all add: gsplit_def gsel_def)

section \<open>Restriction\<close>

definition gtp :: "bool \<Rightarrow> gtree \<Rightarrow> gtree_pair" where
  "gtp m t = (if m then GtreePair t GtreeEmpty else GtreePair GtreeEmpty t)"

definition gtp2 :: "bool \<Rightarrow> bool \<Rightarrow> gtree \<Rightarrow> gtree \<Rightarrow> gtree \<Rightarrow> gtree_pair" where
  "gtp2 m m' tab ta tb =
     (if m then (if m' then GtreePair tab GtreeEmpty else GtreePair ta tb)
      else (if m' then GtreePair tb ta else GtreePair GtreeEmpty tab))"

fun gtree_restrict :: "gtree \<Rightarrow> gtree_restriction \<Rightarrow> gtree_pair" where
  "gtree_restrict t GtrNil = GtreePair GtreeEmpty t"
| "gtree_restrict (GtreeNode t0 t1 t2 t3) (GtrCons bs ct r) =
     (case gtr_split GtrNil GtrNil GtrNil GtrNil (GtrCons bs ct r) of (r0, r1, r2, r3) \<Rightarrow>
        gtree_cons_pairs (GtreeNode t0 t1 t2 t3) (gtree_restrict t0 r0) (gtree_restrict t1 r1)
                         (gtree_restrict t2 r2) (gtree_restrict t3 r3))"
| "gtree_restrict GtreeLeaf0 r = gtp (gtr_mem r [Gpush]) GtreeLeaf0"
| "gtree_restrict GtreeLeaf1 r = gtp (gtr_mem r [Gskip]) GtreeLeaf1"
| "gtree_restrict GtreeLeaf2 r = gtp (gtr_mem r [Gpop0]) GtreeLeaf2"
| "gtree_restrict GtreeLeaf3 r = gtp (gtr_mem r [Gpop1]) GtreeLeaf3"
| "gtree_restrict GtreeLeaf01 r = gtp2 (gtr_mem r [Gpush]) (gtr_mem r [Gskip]) GtreeLeaf01 GtreeLeaf0 GtreeLeaf1"
| "gtree_restrict GtreeLeaf12 r = gtp2 (gtr_mem r [Gskip]) (gtr_mem r [Gpop0]) GtreeLeaf12 GtreeLeaf1 GtreeLeaf2"
| "gtree_restrict GtreeLeaf13 r = gtp2 (gtr_mem r [Gskip]) (gtr_mem r [Gpop1]) GtreeLeaf13 GtreeLeaf1 GtreeLeaf3"
| "gtree_restrict GtreeLeaf23 r = gtp2 (gtr_mem r [Gpop0]) (gtr_mem r [Gpop1]) GtreeLeaf23 GtreeLeaf2 GtreeLeaf3"
| "gtree_restrict GtreeEmpty r = empty_gtree_pair"

lemma gtree_restrict_leaves [simp]:
  "gtree_restrict GtreeLeaf0 r = gtp (gtr_mem r [Gpush]) GtreeLeaf0"
  "gtree_restrict GtreeLeaf1 r = gtp (gtr_mem r [Gskip]) GtreeLeaf1"
  "gtree_restrict GtreeLeaf2 r = gtp (gtr_mem r [Gpop0]) GtreeLeaf2"
  "gtree_restrict GtreeLeaf3 r = gtp (gtr_mem r [Gpop1]) GtreeLeaf3"
  "gtree_restrict GtreeLeaf01 r = gtp2 (gtr_mem r [Gpush]) (gtr_mem r [Gskip]) GtreeLeaf01 GtreeLeaf0 GtreeLeaf1"
  "gtree_restrict GtreeLeaf12 r = gtp2 (gtr_mem r [Gskip]) (gtr_mem r [Gpop0]) GtreeLeaf12 GtreeLeaf1 GtreeLeaf2"
  "gtree_restrict GtreeLeaf13 r = gtp2 (gtr_mem r [Gskip]) (gtr_mem r [Gpop1]) GtreeLeaf13 GtreeLeaf1 GtreeLeaf3"
  "gtree_restrict GtreeLeaf23 r = gtp2 (gtr_mem r [Gpop0]) (gtr_mem r [Gpop1]) GtreeLeaf23 GtreeLeaf2 GtreeLeaf3"
  "gtree_restrict GtreeEmpty r = empty_gtree_pair"
  by (cases r; simp add: gtp_def gtp2_def empty_gtree_pair_def)+

lemma gtree_mem_leaf_iff [simp]:
  "gtree_mem GtreeLeaf0 w \<longleftrightarrow> w = [Gpush]"
  "gtree_mem GtreeLeaf1 w \<longleftrightarrow> w = [Gskip]"
  "gtree_mem GtreeLeaf2 w \<longleftrightarrow> w = [Gpop0]"
  "gtree_mem GtreeLeaf3 w \<longleftrightarrow> w = [Gpop1]"
  "gtree_mem GtreeLeaf01 w \<longleftrightarrow> w = [Gpush] \<or> w = [Gskip]"
  "gtree_mem GtreeLeaf12 w \<longleftrightarrow> w = [Gskip] \<or> w = [Gpop0]"
  "gtree_mem GtreeLeaf13 w \<longleftrightarrow> w = [Gskip] \<or> w = [Gpop1]"
  "gtree_mem GtreeLeaf23 w \<longleftrightarrow> w = [Gpop0] \<or> w = [Gpop1]"
  by (auto elim: gtree_mem.elims)

lemma gtp_partition: "gtree_pair_partition t (gtp m t)"
  by (simp add: gtp_def sgtree_partition_def)

lemma gtp2_partition:
  assumes "\<And>w. gtree_mem tab w \<longleftrightarrow> gtree_mem ta w \<or> gtree_mem tb w" "\<And>w. \<not> (gtree_mem ta w \<and> gtree_mem tb w)"
  shows "gtree_pair_partition tab (gtp2 m m' tab ta tb)"
  using assms by (auto simp: gtp2_def sgtree_partition_def)

theorem gtree_restrict_partition: "gtree_pair_partition t (gtree_restrict t r)"
proof (induction t arbitrary: r)
  case (GtreeNode t0 t1 t2 t3)
  show ?case
  proof (cases r)
    case GtrNil
    then show ?thesis by (simp add: sgtree_partition_def)
  next
    case (GtrCons bs ct r')
    obtain r0 r1 r2 r3 where sp: "gtr_split GtrNil GtrNil GtrNil GtrNil r = (r0, r1, r2, r3)"
      by (cases "gtr_split GtrNil GtrNil GtrNil GtrNil r") auto
    show ?thesis using sp GtrCons GtreeNode.IH
      by (simp add: gtree_cons_pairs_partition)
  qed
next
  case GtreeEmpty
  then show ?case by (simp add: empty_gtree_pair_def sgtree_partition_def)
qed (simp_all add: gtp_partition gtp2_partition)

theorem gtree_mem0_restrict:
  "gtree_mem (gtree_pair_sub (gtree_restrict t r) False) w = (gtree_mem t w \<and> gtr_mem r w)"
proof (induction t arbitrary: r w)
  case (GtreeNode t0 t1 t2 t3)
  show ?case
  proof (cases r)
    case GtrNil
    then show ?thesis by simp
  next
    case (GtrCons bs ct r')
    obtain r0 r1 r2 r3 where sp: "gtr_split GtrNil GtrNil GtrNil GtrNil r = (r0, r1, r2, r3)"
      by (cases "gtr_split GtrNil GtrNil GtrNil GtrNil r") auto
    have gs: "gsplit r Gpush = r0" "gsplit r Gskip = r1" "gsplit r Gpop0 = r2" "gsplit r Gpop1 = r3"
      using sp by (simp_all add: gsplit_def gsel_def)
    have R: "gtree_restrict (GtreeNode t0 t1 t2 t3) r =
             gtree_cons_pairs (GtreeNode t0 t1 t2 t3) (gtree_restrict t0 r0) (gtree_restrict t1 r1)
                              (gtree_restrict t2 r2) (gtree_restrict t3 r3)"
      using sp GtrCons by simp
    show ?thesis
    proof (cases w)
      case Nil
      then show ?thesis unfolding R
        by (simp add: gtree_mem0_cons_pairs gtree_restrict_partition)
    next
      case (Cons s w')
      show ?thesis unfolding R Cons
        using GtreeNode.IH gtr_mem_gsplit[of r s w']
        by (cases s) (simp_all add: gtree_mem0_cons_pairs gtree_restrict_partition gs)
    qed
  qed
next
  case GtreeEmpty
  then show ?case by (simp add: empty_gtree_pair_def)
qed (auto simp: gtp_def gtp2_def)

end
