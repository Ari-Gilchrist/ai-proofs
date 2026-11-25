(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Ctree.thy
    Ternary trees representing sets (multisets) of edge colouring traces.
    Ported from G. Gonthier's Coq development (ctree.v).
*)
theory Ctree
  imports Four_Colour_Base.Color
begin

datatype ctree = CtreeNode ctree ctree ctree | CtreeLeaf ctree | CtreeEmpty

datatype ctree_pair = CtreePair ctree ctree

definition palette :: "'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> color \<Rightarrow> 'b" where
  "palette a0 a1 a2 a3 c = (case c of Color0 \<Rightarrow> a0 | Color1 \<Rightarrow> a1 | Color2 \<Rightarrow> a2 | Color3 \<Rightarrow> a3)"

lemma palette_simps [simp]:
  "palette a0 a1 a2 a3 Color0 = a0" "palette a0 a1 a2 a3 Color1 = a1"
  "palette a0 a1 a2 a3 Color2 = a2" "palette a0 a1 a2 a3 Color3 = a3"
  by (simp_all add: palette_def)

fun ctree_leaf :: "ctree \<Rightarrow> bool" where
  "ctree_leaf (CtreeLeaf _) = True"
| "ctree_leaf _ = False"

definition ctree_empty_node :: "ctree \<Rightarrow> bool" where
  "ctree_empty_node t \<longleftrightarrow> t = CtreeNode CtreeEmpty CtreeEmpty CtreeEmpty"

fun ctree_sel :: "ctree \<Rightarrow> color \<Rightarrow> ctree" where
  "ctree_sel (CtreeNode t1 t2 t3) c = palette CtreeEmpty t1 t2 t3 c"
| "ctree_sel _ c = CtreeEmpty"

fun ctree_proper :: "nat \<Rightarrow> ctree \<Rightarrow> bool" where
  "ctree_proper h CtreeEmpty = True"
| "ctree_proper (Suc h) (CtreeNode t1 t2 t3) =
     (\<not> ctree_empty_node (CtreeNode t1 t2 t3) \<and> ctree_proper h t1 \<and> ctree_proper h t2 \<and> ctree_proper h t3)"
| "ctree_proper 0 (CtreeLeaf lf) = ctree_proper 0 lf"
| "ctree_proper _ _ = False"

fun ctree_sub :: "ctree \<Rightarrow> colseq \<Rightarrow> nat" where
  "ctree_sub (CtreeNode t1 t2 t3) (e # et) =
     palette 0 (ctree_sub t1 et) (ctree_sub t2 et) (ctree_sub t3 et) e"
| "ctree_sub (CtreeLeaf lf) [] = Suc (ctree_sub lf [])"
| "ctree_sub _ _ = 0"

definition ctree_mem :: "ctree \<Rightarrow> colseq \<Rightarrow> bool" where
  "ctree_mem t et \<longleftrightarrow> ctree_sub t et \<noteq> 0"

definition ctree_empty_pair :: ctree_pair where
  "ctree_empty_pair = CtreePair CtreeEmpty CtreeEmpty"

fun ctree_pair_sub :: "ctree_pair \<Rightarrow> bool \<Rightarrow> ctree" where
  "ctree_pair_sub (CtreePair t0 t1) b = (if b then t1 else t0)"

definition ctree_leaf_of :: "nat \<Rightarrow> ctree" where
  "ctree_leaf_of n = (CtreeLeaf ^^ n) CtreeEmpty"

definition ctree_cons :: "ctree \<Rightarrow> ctree \<Rightarrow> ctree \<Rightarrow> ctree" where
  "ctree_cons t1 t2 t3 =
     (if t1 = CtreeEmpty \<and> t2 = CtreeEmpty \<and> t3 = CtreeEmpty then CtreeEmpty else CtreeNode t1 t2 t3)"

definition ctree_simple_leaf :: ctree where
  "ctree_simple_leaf = CtreeLeaf CtreeEmpty"

definition ctree_cons_e :: "color \<Rightarrow> ctree \<Rightarrow> ctree" where
  "ctree_cons_e c t = palette CtreeEmpty (ctree_cons t CtreeEmpty CtreeEmpty)
     (ctree_cons CtreeEmpty t CtreeEmpty) (ctree_cons CtreeEmpty CtreeEmpty t) c"

definition ctree_of_ttail :: "colseq \<Rightarrow> ctree" where
  "ctree_of_ttail et = foldr ctree_cons_e et ctree_simple_leaf"

fun ctree_union :: "ctree \<Rightarrow> ctree \<Rightarrow> ctree" where
  "ctree_union (CtreeNode tl1 tl2 tl3) (CtreeNode tr1 tr2 tr3) =
     ctree_cons (ctree_union tl1 tr1) (ctree_union tl2 tr2) (ctree_union tl3 tr3)"
| "ctree_union CtreeEmpty tb = tb"
| "ctree_union ta CtreeEmpty = ta"
| "ctree_union _ _ = ctree_simple_leaf"

fun ctree_rotl :: "ctree \<Rightarrow> ctree" where
  "ctree_rotl (CtreeNode t1 t2 t3) = ctree_cons (ctree_rotl t3) (ctree_rotl t1) (ctree_rotl t2)"
| "ctree_rotl t = t"

fun ctree_rotr :: "ctree \<Rightarrow> ctree" where
  "ctree_rotr (CtreeNode t1 t2 t3) = ctree_cons (ctree_rotr t2) (ctree_rotr t3) (ctree_rotr t1)"
| "ctree_rotr t = t"

definition ctree_cons_rot :: "ctree \<Rightarrow> ctree" where
  "ctree_cons_rot t = ctree_cons t (ctree_rotl t) (ctree_rotr t)"

fun ctree_union_rotlr :: "ctree \<Rightarrow> ctree \<Rightarrow> ctree" where
  "ctree_union_rotlr (CtreeNode tl1 tl2 tl3) (CtreeNode tr1 tr2 tr3) =
     ctree_cons (ctree_union_rotlr tl3 tr2) (ctree_union_rotlr tl1 tr3) (ctree_union_rotlr tl2 tr1)"
| "ctree_union_rotlr (CtreeLeaf _) (CtreeLeaf _) = ctree_simple_leaf"
| "ctree_union_rotlr ta tb = ctree_union (ctree_rotl ta) (ctree_rotr tb)"

definition ctree_rotlr :: "ctree \<Rightarrow> ctree" where
  "ctree_rotlr t = ctree_union_rotlr t t"

fun ctree_disjoint :: "ctree \<Rightarrow> ctree \<Rightarrow> bool" where
  "ctree_disjoint (CtreeLeaf _) (CtreeLeaf _) = False"
| "ctree_disjoint (CtreeNode tl1 tl2 tl3) (CtreeNode tr1 tr2 tr3) =
     (ctree_disjoint tl1 tr1 \<and> ctree_disjoint tl2 tr2 \<and> ctree_disjoint tl3 tr3)"
| "ctree_disjoint _ _ = True"

section \<open>Basic properties\<close>

lemma ctree_sel_0 [simp]: "ctree_sel t Color0 = CtreeEmpty"
  by (cases t) simp_all

lemma ctree_proper_sel: "ctree_proper h t \<Longrightarrow> ctree_proper (h - 1) (ctree_sel t e)"
  by (cases "(h, t)" rule: ctree_proper.cases) (auto simp: palette_def split: color.splits)

lemma ctree_sub_0: "Color0 \<in> set et \<Longrightarrow> ctree_sub t et = 0"
proof (induction et arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons e et)
  show ?case
  proof (cases t)
    case (CtreeNode t1 t2 t3)
    then show ?thesis using Cons by (cases e) auto
  qed simp_all
qed

lemma ctree_mem_Empty [simp]: "\<not> ctree_mem CtreeEmpty et"
  by (simp add: ctree_mem_def)

lemma ctree_mem_Node_Nil [simp]: "\<not> ctree_mem (CtreeNode a b c) []"
  by (simp add: ctree_mem_def)

lemma ctree_mem_0: "Color0 \<in> set et \<Longrightarrow> \<not> ctree_mem t et"
  by (simp add: ctree_mem_def ctree_sub_0)

lemma ctree_mem_seq0: "ctree_mem t [] = ctree_leaf t"
  by (cases t) (simp_all add: ctree_mem_def)

lemma ctree_sub_sel: "ctree_sub t (e # et) = ctree_sub (ctree_sel t e) et"
  by (cases t; cases e) simp_all

lemma ctree_mem_sel: "ctree_mem t (e # et) = ctree_mem (ctree_sel t e) et"
  by (simp add: ctree_mem_def ctree_sub_sel)

lemma ctree_mem_leaf: "ctree_mem (CtreeLeaf lf) et = (et = [])"
  by (cases et) (simp_all add: ctree_mem_def)

lemma ctree_leaf_of_proper: "ctree_proper 0 (ctree_leaf_of n)"
  by (induction n) (simp_all add: ctree_leaf_of_def)

lemma ctree_sub_leaf_of: "ctree_sub (ctree_leaf_of n) et = (if et = [] then n else 0)"
proof (cases et)
  case Nil
  then show ?thesis by (induction n) (simp_all add: ctree_leaf_of_def)
next
  case (Cons e et')
  then show ?thesis by (cases n) (simp_all add: ctree_leaf_of_def)
qed

section \<open>The interlocking constructor\<close>

lemma ctree_cons_spec:
  "ctree_cons t1 t2 t3 = (if ctree_empty_node (CtreeNode t1 t2 t3) then CtreeEmpty else CtreeNode t1 t2 t3)"
  by (simp add: ctree_cons_def ctree_empty_node_def)

lemma ctree_leaf_cons [simp]: "\<not> ctree_leaf (ctree_cons t1 t2 t3)"
  by (simp add: ctree_cons_def)

lemma ctree_sel_cons [simp]: "ctree_sel (ctree_cons t1 t2 t3) e = ctree_sel (CtreeNode t1 t2 t3) e"
  by (cases e) (auto simp: ctree_cons_def)

lemma ctree_cons_proper:
  "ctree_proper h t1 \<Longrightarrow> ctree_proper h t2 \<Longrightarrow> ctree_proper h t3 \<Longrightarrow> ctree_proper (Suc h) (ctree_cons t1 t2 t3)"
  by (simp add: ctree_cons_def ctree_empty_node_def)

lemma ctree_sub_cons [simp]: "ctree_sub (ctree_cons t1 t2 t3) et = ctree_sub (CtreeNode t1 t2 t3) et"
  by (cases et) (auto simp: ctree_cons_def palette_def split: color.splits)

lemma ctree_mem_cons [simp]: "ctree_mem (ctree_cons t1 t2 t3) et = ctree_mem (CtreeNode t1 t2 t3) et"
  by (simp add: ctree_mem_def)

lemma ctree_cons_e_proper: "ctree_proper h t \<Longrightarrow> ctree_proper (Suc h) (ctree_cons_e e t)"
  by (cases e) (simp_all add: ctree_cons_e_def ctree_cons_proper)

lemma ctree_of_ttail_proper: "length et = h \<Longrightarrow> ctree_proper h (ctree_of_ttail et)"
proof (induction et arbitrary: h)
  case Nil
  then show ?case by (simp add: ctree_of_ttail_def ctree_simple_leaf_def)
next
  case (Cons e et)
  then show ?case using ctree_cons_e_proper by (auto simp: ctree_of_ttail_def)
qed

lemma ctree_of_ttail_mem:
  "Color0 \<notin> set et \<Longrightarrow> ctree_mem (ctree_of_ttail et) et' \<longleftrightarrow> et' = et"
proof (induction et arbitrary: et')
  case Nil
  then show ?case by (cases et') (simp_all add: ctree_of_ttail_def ctree_simple_leaf_def ctree_mem_def)
next
  case (Cons e et)
  have IH: "\<And>et'. ctree_mem (ctree_of_ttail et) et' \<longleftrightarrow> et' = et" using Cons by simp
  have e0: "e \<noteq> Color0" using Cons.prems by auto
  have of: "ctree_of_ttail (e # et) = ctree_cons_e e (ctree_of_ttail et)" by (simp add: ctree_of_ttail_def)
  show ?case
  proof (cases et')
    case Nil
    then show ?thesis using of e0 by (cases e) (simp_all add: ctree_cons_e_def ctree_mem_def)
  next
    case (Cons e' et'')
    then show ?thesis using of e0 IH by (cases e; cases e') (simp_all add: ctree_cons_e_def ctree_mem_def)
  qed
qed

section \<open>Union\<close>

lemma ctree_union_Nl [simp]: "ctree_union CtreeEmpty t = t"
  by simp

lemma ctree_union_Nr [simp]: "ctree_union t CtreeEmpty = t"
  by (cases t) simp_all

lemma ctree_union_sym: "ctree_union t1 t2 = ctree_union t2 t1"
  by (induction t1 t2 rule: ctree_union.induct) simp_all

lemma ctree_union_proper:
  "ctree_proper h ta \<Longrightarrow> ctree_proper h tb \<Longrightarrow> ctree_proper h (ctree_union ta tb)"
proof (induction ta tb arbitrary: h rule: ctree_union.induct)
  case (1 tl1 tl2 tl3 tr1 tr2 tr3)
  then show ?case by (cases h) (auto intro: ctree_cons_proper)
qed (auto simp: ctree_simple_leaf_def elim: ctree_proper.elims)

lemma ctree_mem_union:
  "ctree_proper h ta \<Longrightarrow> ctree_proper h tb \<Longrightarrow>
   ctree_mem (ctree_union ta tb) et = (ctree_mem ta et \<or> ctree_mem tb et)"
proof (induction ta tb arbitrary: h et rule: ctree_union.induct)
  case (1 tl1 tl2 tl3 tr1 tr2 tr3)
  then obtain h' where h: "h = Suc h'" by (cases h) auto
  show ?case
  proof (cases et)
    case Nil
    then show ?thesis by (simp add: ctree_mem_def)
  next
    case (Cons e et')
    then show ?thesis using 1 h by (cases e) (auto simp: ctree_mem_def)
  qed
qed (auto simp: ctree_simple_leaf_def ctree_mem_leaf elim: ctree_proper.elims)

section \<open>Rotations\<close>

lemma ctree_rotl_proper: "ctree_proper h t \<Longrightarrow> ctree_proper h (ctree_rotl t)"
proof (induction t arbitrary: h)
  case (CtreeNode t1 t2 t3)
  then show ?case by (cases h) (auto intro: ctree_cons_proper)
qed simp_all

lemma ctree_rotr_proper: "ctree_proper h t \<Longrightarrow> ctree_proper h (ctree_rotr t)"
proof (induction t arbitrary: h)
  case (CtreeNode t1 t2 t3)
  then show ?case by (cases h) (auto intro: ctree_cons_proper)
qed simp_all

lemma ctree_mem_rotl: "ctree_mem (ctree_rotl t) et = ctree_mem t (permt Eperm312 et)"
proof (induction et arbitrary: t)
  case Nil
  then show ?case by (cases t) (simp_all add: ctree_mem_def permt_def)
next
  case (Cons e et)
  then show ?case by (cases t; cases e) (simp_all add: ctree_mem_def permt_def)
qed

lemma ctree_mem_rotr: "ctree_mem (ctree_rotr t) et = ctree_mem t (permt Eperm231 et)"
proof (induction et arbitrary: t)
  case Nil
  then show ?case by (cases t) (simp_all add: ctree_mem_def permt_def)
next
  case (Cons e et)
  then show ?case by (cases t; cases e) (simp_all add: ctree_mem_def permt_def)
qed

lemma ctree_cons_rot_proper: "ctree_proper h t \<Longrightarrow> ctree_proper (Suc h) (ctree_cons_rot t)"
  by (simp add: ctree_cons_rot_def ctree_cons_proper ctree_rotl_proper ctree_rotr_proper)

lemma ctree_mem_cons_rot: "ctree_mem (ctree_cons_rot t) et = ctree_mem t (ttail et)"
proof (cases et)
  case Nil
  then show ?thesis
    by (simp add: ctree_cons_rot_def ttail_def proper_trace_def head_color_def ctree_mem_seq0 ctree_mem_0)
next
  case (Cons e et')
  have "ctree_mem (ctree_cons_rot t) et =
        ctree_mem (ctree_sel (CtreeNode t (ctree_rotl t) (ctree_rotr t)) e) et'"
    by (simp only: Cons ctree_cons_rot_def ctree_mem_sel ctree_sel_cons)
  then show ?thesis using Cons
    by (cases e) (simp_all add: ttail_def proper_trace_def head_color_def ctree_mem_0 ctree_mem_rotl ctree_mem_rotr)
qed

lemma ctree_rotlr_spec: "ctree_rotlr t = ctree_union (ctree_rotl t) (ctree_rotr t)"
proof -
  have "ctree_union_rotlr t u = ctree_union (ctree_rotl t) (ctree_rotr u)" for u
  proof (induction t u rule: ctree_union_rotlr.induct)
    case (1 tl1 tl2 tl3 tr1 tr2 tr3)
    then show ?case by (simp add: ctree_cons_def)
  qed (simp_all add: ctree_simple_leaf_def)
  then show ?thesis by (simp add: ctree_rotlr_def)
qed

lemma ctree_rotlr_proper: "ctree_proper h t \<Longrightarrow> ctree_proper h (ctree_rotlr t)"
  by (simp add: ctree_rotlr_spec ctree_union_proper ctree_rotl_proper ctree_rotr_proper)

lemma ctree_mem_rotlr:
  "ctree_proper h t \<Longrightarrow>
   ctree_mem (ctree_rotlr t) et = (ctree_mem t (permt Eperm312 et) \<or> ctree_mem t (permt Eperm231 et))"
  by (simp add: ctree_rotlr_spec ctree_mem_union[OF ctree_rotl_proper ctree_rotr_proper]
      ctree_mem_rotl ctree_mem_rotr)

section \<open>Disjointness\<close>

lemma ctree_mem_disjoint_spec:
  "\<not> ctree_disjoint ta tb \<longleftrightarrow> (\<exists>et. ctree_mem ta et \<and> ctree_mem tb et)"
proof (induction ta tb rule: ctree_disjoint.induct)
  case (1 a b)
  then show ?case by (auto simp: ctree_mem_leaf intro: exI[of _ "[]"])
next
  case (2 tl1 tl2 tl3 tr1 tr2 tr3)
  have "(\<exists>et. ctree_mem (CtreeNode tl1 tl2 tl3) et \<and> ctree_mem (CtreeNode tr1 tr2 tr3) et) \<longleftrightarrow>
        (\<exists>et. ctree_mem tl1 et \<and> ctree_mem tr1 et) \<or> (\<exists>et. ctree_mem tl2 et \<and> ctree_mem tr2 et) \<or>
        (\<exists>et. ctree_mem tl3 et \<and> ctree_mem tr3 et)"
  proof
    assume "\<exists>et. ctree_mem (CtreeNode tl1 tl2 tl3) et \<and> ctree_mem (CtreeNode tr1 tr2 tr3) et"
    then obtain et where h: "ctree_mem (CtreeNode tl1 tl2 tl3) et" "ctree_mem (CtreeNode tr1 tr2 tr3) et"
      by blast
    then obtain e et' where et: "et = e # et'" by (cases et) (auto simp: ctree_mem_def)
    show "(\<exists>et. ctree_mem tl1 et \<and> ctree_mem tr1 et) \<or> (\<exists>et. ctree_mem tl2 et \<and> ctree_mem tr2 et) \<or>
          (\<exists>et. ctree_mem tl3 et \<and> ctree_mem tr3 et)"
      using h et by (cases e) (auto simp: ctree_mem_def)
  next
    assume "(\<exists>et. ctree_mem tl1 et \<and> ctree_mem tr1 et) \<or> (\<exists>et. ctree_mem tl2 et \<and> ctree_mem tr2 et) \<or>
            (\<exists>et. ctree_mem tl3 et \<and> ctree_mem tr3 et)"
    then show "\<exists>et. ctree_mem (CtreeNode tl1 tl2 tl3) et \<and> ctree_mem (CtreeNode tr1 tr2 tr3) et"
    proof (elim disjE exE)
      fix et assume "ctree_mem tl1 et \<and> ctree_mem tr1 et"
      then show ?thesis by (intro exI[of _ "Color1 # et"]) (simp add: ctree_mem_def)
    next
      fix et assume "ctree_mem tl2 et \<and> ctree_mem tr2 et"
      then show ?thesis by (intro exI[of _ "Color2 # et"]) (simp add: ctree_mem_def)
    next
      fix et assume "ctree_mem tl3 et \<and> ctree_mem tr3 et"
      then show ?thesis by (intro exI[of _ "Color3 # et"]) (simp add: ctree_mem_def)
    qed
  qed
  then show ?case using 2 by simp
qed (auto simp: ctree_mem_leaf)

lemma ctree_mem_disjoint:
  "ctree_disjoint ta tb \<Longrightarrow> ctree_mem tb et \<Longrightarrow> \<not> ctree_mem ta et"
  using ctree_mem_disjoint_spec by blast

end
