(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Initctree.thy
    Dyck word counts and the initial tree of unreachable traces.
    Ported from G. Gonthier's Coq development (dyck.v, initctree.v).
*)
theory Initctree
  imports Ctree
begin

section \<open>Dyck numbers\<close>

fun gen_dyck :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "gen_dyck m 0 = (if m = 1 then 1 else 0)"
| "gen_dyck 0 (Suc n) = 0"
| "gen_dyck (Suc m) (Suc n) = gen_dyck (Suc (Suc m)) n + gen_dyck m n"

definition dyck :: "nat \<Rightarrow> nat" where
  "dyck = gen_dyck 1"

lemma gen_dyck_max: "Suc n < m \<Longrightarrow> gen_dyck m n = 0"
proof (induction n arbitrary: m)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then obtain m' where "m = Suc m'" by (cases m) auto
  then show ?case using Suc by simp
qed

lemma gen_dyck_all_close: "gen_dyck (Suc m) m = 1"
  by (induction m) (simp_all add: gen_dyck_max)

lemma even_dyck_pos: "0 < dyck (2 * n)"
proof -
  have "0 < gen_dyck (Suc m) (m + 2 * n)" for m
  proof (induction n arbitrary: m)
    case 0
    then show ?case by (simp add: gen_dyck_all_close)
  next
    case (Suc n)
    have "m + 2 * Suc n = Suc (Suc m + 2 * n)" by simp
    then show ?case using Suc[of "Suc m"] by simp
  qed
  from this[of 0] show ?thesis by (simp add: dyck_def)
qed

section \<open>Tables of subtrees\<close>

type_synonym ctree_table = "ctree_pair list"

definition ctree_table_sub :: "ctree_table \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> ctree" where
  "ctree_table_sub tab i b = ctree_pair_sub (if i < length tab then tab ! i else ctree_empty_pair) b"

fun iteri :: "nat \<Rightarrow> (nat \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'b" where
  "iteri 0 g x = x"
| "iteri (Suc n) g x = g n (iteri n g x)"

fun ctree_add_dyck :: "nat \<Rightarrow> nat \<Rightarrow> ctree \<Rightarrow> ctree" where
  "ctree_add_dyck m 0 = CtreeLeaf"
| "ctree_add_dyck m (Suc n) = iteri (Suc m) (\<lambda>m'. ctree_add_dyck (Suc m') n)"

fun ctree_leaf_table_from :: "ctree \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ctree_table" where
  "ctree_leaf_table_from lf n 0 = []"
| "ctree_leaf_table_from lf n (Suc 0) = [CtreePair lf lf]"
| "ctree_leaf_table_from lf n (Suc (Suc h)) =
     CtreePair lf lf # CtreePair CtreeEmpty lf # ctree_leaf_table_from (ctree_add_dyck 2 n lf) (Suc n) h"

definition ctree_leaf_table :: "nat \<Rightarrow> ctree_table" where
  "ctree_leaf_table h = CtreePair CtreeEmpty (CtreeLeaf CtreeEmpty) # ctree_leaf_table_from (CtreeLeaf CtreeEmpty) 0 h"

fun ctree_merge_pair :: "ctree_pair \<Rightarrow> ctree_pair \<Rightarrow> ctree_pair" where
  "ctree_merge_pair (CtreePair t0 t1) (CtreePair t2 t3) = CtreePair (ctree_cons t1 t2 t3) (ctree_cons t0 t3 t2)"

fun ctree_merge_table :: "ctree_table \<Rightarrow> ctree_table" where
  "ctree_merge_table (line # tab) = pairmap ctree_merge_pair line tab"
| "ctree_merge_table [] = []"

fun ctree_prune_1 :: "ctree \<Rightarrow> ctree" where
  "ctree_prune_1 (CtreeNode t1 t2 t3) = ctree_cons (ctree_prune_1 t1) t2 CtreeEmpty"
| "ctree_prune_1 t = t"

fun ctree_prune_2 :: "ctree \<Rightarrow> ctree" where
  "ctree_prune_2 (CtreeNode t1 t2 t3) = ctree_cons CtreeEmpty (ctree_prune_2 t2) t3"
| "ctree_prune_2 t = t"

fun ctree_prune_3 :: "ctree \<Rightarrow> ctree" where
  "ctree_prune_3 (CtreeNode t1 t2 t3) = ctree_cons t1 CtreeEmpty (ctree_prune_3 t3)"
| "ctree_prune_3 t = t"

definition ctree_init_tree :: "nat \<Rightarrow> ctree" where
  "ctree_init_tree h = (case (ctree_merge_table ^^ (h - 1)) (ctree_leaf_table h) of
       CtreePair t0 t1 # CtreePair t2 t3 # _ \<Rightarrow>
         ctree_cons (ctree_prune_1 t1) (ctree_prune_2 t2) (ctree_prune_3 t3)
     | _ \<Rightarrow> CtreeEmpty)"

section \<open>Leaf correctness\<close>

lemma ctree_leaf_of_Suc: "ctree_leaf_of (Suc d) = CtreeLeaf (ctree_leaf_of d)"
  by (simp add: ctree_leaf_of_def)

lemma ctree_add_dyck_leaf_of:
  "ctree_add_dyck m n (ctree_leaf_of d) = ctree_leaf_of (gen_dyck (Suc m) (m + 2 * n) + d)"
proof (induction n arbitrary: m d)
  case 0
  then show ?case by (simp add: gen_dyck_all_close ctree_leaf_of_Suc)
next
  case (Suc n)
  have "iteri (Suc m) (\<lambda>m'. ctree_add_dyck (Suc m') n) (ctree_leaf_of d) =
        ctree_leaf_of (gen_dyck (Suc m) (m + 2 * Suc n) + d)" for m
  proof (induction m)
    case 0
    have "gen_dyck (Suc 0) (2 * Suc n) = gen_dyck 2 (Suc (2 * n))" by (simp add: numeral_2_eq_2)
    then show ?case using Suc.IH[of 1 d] by (simp add: numeral_2_eq_2)
  next
    case (Suc m)
    have e: "Suc m + 2 * Suc n = Suc (m + 2 * Suc n)" by simp
    have "gen_dyck (Suc (Suc m)) (Suc (m + 2 * Suc n)) =
          gen_dyck (Suc (Suc (Suc m))) (m + 2 * Suc n) + gen_dyck (Suc m) (m + 2 * Suc n)" by simp
    moreover have "Suc (Suc m) + 2 * n = m + 2 * Suc n" by simp
    ultimately show ?case using Suc.IH \<open>\<And>m d. ctree_add_dyck m n (ctree_leaf_of d) = _\<close>[of "Suc (Suc m)"] e
      by (simp add: add.assoc)
  qed
  then show ?case by simp
qed

lemma length_leaf_table_from: "length (ctree_leaf_table_from lf n h) = h"
  by (induction lf n h rule: ctree_leaf_table_from.induct) simp_all

lemma ctree_leaf_table_size: "length (ctree_leaf_table h) = Suc h"
  by (simp add: ctree_leaf_table_def length_leaf_table_from)

definition leaf_val :: "nat \<Rightarrow> bool \<Rightarrow> ctree" where
  "leaf_val i b = (let c = ccons (odd i) b in
     if Color0 \<in> set [c] then CtreeEmpty else ctree_leaf_of (dyck (i + count_cbit1 [c])))"

lemma dyck_2: "dyck 2 = 1"
  by (simp add: dyck_def numeral_2_eq_2)

lemma dyck_step: "dyck (2 * n + 4) = gen_dyck 3 (2 * n + 2) + dyck (2 * n + 2)"
proof -
  have e4: "2 * n + 4 = Suc (Suc (Suc (Suc (2 * n))))" by simp
  have e2: "2 * n + 2 = Suc (Suc (2 * n))" by simp
  show ?thesis unfolding e4 e2 dyck_def by (simp add: numeral_2_eq_2 numeral_3_eq_3)
qed

lemma leaf_table_from_sub:
  "i < h \<Longrightarrow> ctree_table_sub (ctree_leaf_table_from (ctree_leaf_of (dyck (2 * n + 2))) n h) i b =
            leaf_val (2 * n + 1 + i) b"
proof (induction h arbitrary: n i rule: less_induct)
  case (less h)
  define lf where "lf = ctree_leaf_of (dyck (2 * n + 2))"
  have odd_val: "leaf_val (2 * n + 1) b = lf" by (cases b) (simp_all add: leaf_val_def lf_def Let_def)
  have even_val: "leaf_val (2 * n + 2) b = (if b then lf else CtreeEmpty)"
    by (cases b) (simp_all add: leaf_val_def lf_def Let_def)
  consider (one) "h = Suc 0" | (two) h' where "h = Suc (Suc h')"
  proof (cases h)
    case 0
    then show thesis using less.prems by simp
  next
    case (Suc k)
    then show thesis using that by (cases k) auto
  qed
  then show ?case
  proof cases
    case one
    then have "i = 0" using less.prems by simp
    then show ?thesis using one odd_val by (simp add: ctree_table_sub_def lf_def)
  next
    case two
    show ?thesis
    proof (cases i)
      case 0
      then show ?thesis using two odd_val by (simp add: ctree_table_sub_def lf_def)
    next
      case (Suc i')
      show ?thesis
      proof (cases i')
        case 0
        then show ?thesis using two Suc even_val by (cases b) (simp_all add: ctree_table_sub_def lf_def)
      next
        case (Suc i'')
        have a: "ctree_add_dyck 2 n lf = ctree_leaf_of (gen_dyck (Suc 2) (2 + 2 * n) + dyck (2 * n + 2))"
          unfolding lf_def by (rule ctree_add_dyck_leaf_of)
        have b: "gen_dyck (Suc 2) (2 + 2 * n) + dyck (2 * n + 2) = dyck (2 * Suc n + 2)"
        proof -
          have e1: "2 * Suc n + 2 = 2 * n + 4" by simp
          have e2: "Suc 2 = (3::nat)" by simp
          have e3: "2 + 2 * n = 2 * n + 2" by simp
          show ?thesis unfolding e1 e2 e3 by (rule dyck_step[symmetric])
        qed
        have lf': "ctree_add_dyck 2 n lf = ctree_leaf_of (dyck (2 * Suc n + 2))" using a b by simp
        have ih: "i'' < h'" using less.prems \<open>i = Suc i'\<close> Suc two by simp
        have "ctree_table_sub (ctree_leaf_table_from (ctree_leaf_of (dyck (2 * Suc n + 2))) (Suc n) h') i'' b =
              leaf_val (2 * Suc n + 1 + i'') b"
        proof -
          have hh: "h' < h" using two by simp
          show ?thesis by (rule less.IH[OF hh ih])
        qed
        moreover have "2 * Suc n + 1 + i'' = 2 * n + 1 + i" using \<open>i = Suc i'\<close> Suc by simp
        moreover have "ctree_table_sub (ctree_leaf_table_from lf n h) i b =
                       ctree_table_sub (ctree_leaf_table_from (ctree_add_dyck 2 n lf) (Suc n) h') i'' b"
          using two \<open>i = Suc i'\<close> Suc ih by (simp add: ctree_table_sub_def length_leaf_table_from)
        ultimately show ?thesis using lf' \<open>i = Suc i'\<close> Suc by (simp add: lf_def)
      qed
    qed
  qed
qed

lemma ctree_leaf_table_sub:
  "i \<le> h \<Longrightarrow> ctree_table_sub (ctree_leaf_table h) i b = leaf_val i b"
proof (cases i)
  case 0
  then show ?thesis
    by (cases b) (simp_all add: ctree_table_sub_def ctree_leaf_table_def leaf_val_def dyck_def ctree_leaf_of_def)
next
  case (Suc i')
  assume ih: "i \<le> h"
  have d: "dyck (2 * 0 + 2) = 1" by (simp add: dyck_def numeral_2_eq_2)
  have l1: "CtreeLeaf CtreeEmpty = ctree_leaf_of (dyck (2 * 0 + 2))"
    unfolding d by (simp add: ctree_leaf_of_def)
  have "i' < h" using ih Suc by simp
  then have "ctree_table_sub (ctree_leaf_table_from (CtreeLeaf CtreeEmpty) 0 h) i' b = leaf_val (Suc i') b"
    using leaf_table_from_sub[of i' h 0 b] l1 by simp
  then show ?thesis using Suc \<open>i' < h\<close> by (simp add: ctree_table_sub_def ctree_leaf_table_def length_leaf_table_from)
qed

section \<open>Global correctness\<close>

lemma pairmap_nth': "i < length l \<Longrightarrow> pairmap f x l ! i = f ((x # l) ! i) (l ! i)"
proof (induction l arbitrary: x i)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then show ?case by (cases i) simp_all
qed

definition tab_spec :: "nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> colseq \<Rightarrow> nat" where
  "tab_spec n i b et = (let cet = et @ [ccons (odd i) b +c sumt et] in
      if length et = n \<and> Color0 \<notin> set cet then dyck (i + count_cbit1 cet) else 0)"

lemma count_cbit1_append: "count_cbit1 (a @ b) = count_cbit1 a + count_cbit1 b"
  by (induction a) simp_all

lemma ccons_addc: "ccons x y +c c = ccons (x \<noteq> cbit1 c) (y \<noteq> cbit0 c)"
  by (cases x; cases y; cases c) simp_all

lemma tab_invariant:
  assumes "n \<le> h"
  shows "length ((ctree_merge_table ^^ n) (ctree_leaf_table h)) = Suc h - n \<and>
         (\<forall>i < length ((ctree_merge_table ^^ n) (ctree_leaf_table h)). \<forall>b et.
            ctree_sub (ctree_table_sub ((ctree_merge_table ^^ n) (ctree_leaf_table h)) i b) et = tab_spec n i b et)"
  using assms
proof (induction n)
  case 0
  have "ctree_sub (leaf_val i b) et = tab_spec 0 i b et" for i b et
    by (cases et) (auto simp: leaf_val_def tab_spec_def Let_def ctree_sub_leaf_of)
  then show ?case using ctree_leaf_table_sub ctree_leaf_table_size by simp
next
  case (Suc n)
  define tab where "tab = (ctree_merge_table ^^ n) (ctree_leaf_table h)"
  have IH: "length tab = Suc h - n"
    "\<And>i b et. i < length tab \<Longrightarrow> ctree_sub (ctree_table_sub tab i b) et = tab_spec n i b et"
    using Suc by (auto simp: tab_def)
  obtain line tab' where tb: "tab = line # tab'" using IH(1) Suc.prems by (cases tab) auto
  have new: "(ctree_merge_table ^^ Suc n) (ctree_leaf_table h) = pairmap ctree_merge_pair line tab'"
    using tb by (simp add: tab_def)
  have len: "length (pairmap ctree_merge_pair line tab') = Suc h - Suc n" using IH(1) tb by simp
  have ent: "ctree_sub (ctree_table_sub (pairmap ctree_merge_pair line tab') i b) et = tab_spec (Suc n) i b et"
    if i: "i < length tab'" for i b et
  proof -
    have pi: "pairmap ctree_merge_pair line tab' ! i = ctree_merge_pair (tab ! i) (tab ! Suc i)"
      using pairmap_nth'[OF i] tb by simp
    obtain t0 t1 where p0: "tab ! i = CtreePair t0 t1" by (cases "tab ! i") auto
    obtain t2 t3 where p1: "tab ! Suc i = CtreePair t2 t3" by (cases "tab ! Suc i") auto
    have i0: "i < length tab" "Suc i < length tab" using i tb by simp_all
    have T: "\<And>b et. ctree_sub (ctree_pair_sub (CtreePair t0 t1) b) et = tab_spec n i b et"
      using IH(2)[OF i0(1)] p0 i0 by (simp add: ctree_table_sub_def)
    have T': "\<And>b et. ctree_sub (ctree_pair_sub (CtreePair t2 t3) b) et = tab_spec n (Suc i) b et"
      using IH(2)[OF i0(2)] p1 i0 by (simp add: ctree_table_sub_def)
    have t0: "ctree_sub t0 et = tab_spec n i False et" and t1: "ctree_sub t1 et = tab_spec n i True et"
      and t2: "ctree_sub t2 et = tab_spec n (Suc i) False et" and t3: "ctree_sub t3 et = tab_spec n (Suc i) True et"
      for et using T[of False et] T[of True et] T'[of False et] T'[of True et] by simp_all
    have val: "ctree_table_sub (pairmap ctree_merge_pair line tab') i b =
               (if b then ctree_cons t0 t3 t2 else ctree_cons t1 t2 t3)"
      using pi p0 p1 i by (simp add: ctree_table_sub_def)
    show ?thesis
    proof (cases et)
      case Nil
      then show ?thesis using val by (simp add: tab_spec_def Let_def)
    next
      case (Cons e et')
      have sumt_e: "sumt (e # et') = e +c sumt et'" by simp
      show ?thesis
        using val Cons t0 t1 t2 t3
        by (cases b; cases e)
           (simp_all add: tab_spec_def Let_def addcA[symmetric] ccons_addc count_cbit1_append)
    qed
  qed
  show ?case using len ent new by (simp add: ctree_table_sub_def)
qed

lemma ctree_prune_1_sub: "ctree_sub (ctree_prune_1 t) et = (if even_tail et then ctree_sub t et else 0)"
proof (induction t arbitrary: et)
  case (CtreeNode t1 t2 t3)
  then show ?case by (cases et; cases "hd et") auto
next
  case (CtreeLeaf t)
  then show ?case by (cases et) simp_all
qed simp

lemma ctree_prune_2_sub:
  "ctree_sub (ctree_prune_2 t) et = (if even_tail (permt Eperm312 et) then ctree_sub t et else 0)"
proof (induction t arbitrary: et)
  case (CtreeNode t1 t2 t3)
  then show ?case by (cases et; cases "hd et") (auto simp: permt_def)
next
  case (CtreeLeaf t)
  then show ?case by (cases et) (simp_all add: permt_def)
qed simp

lemma ctree_prune_3_sub:
  "ctree_sub (ctree_prune_3 t) et = (if even_tail (permt Eperm231 et) then ctree_sub t et else 0)"
proof (induction t arbitrary: et)
  case (CtreeNode t1 t2 t3)
  then show ?case by (cases et; cases "hd et") (auto simp: permt_def)
next
  case (CtreeLeaf t)
  then show ?case by (cases et) (simp_all add: permt_def)
qed simp

lemma ctree_sub_init_tree:
  "ctree_sub (ctree_init_tree h) et =
     (if length et = h \<and> Color0 \<notin> set (ctrace et) \<and> even_trace et then dyck (count_cbit1 (ctrace et)) else 0)"
proof (cases h)
  case 0
  have "ctree_init_tree 0 = CtreeEmpty"
    by (simp add: ctree_init_tree_def ctree_leaf_table_def)
  then show ?thesis using 0 by (cases et) (simp_all add: ctrace_def)
next
  case (Suc h')
  define tab where "tab = (ctree_merge_table ^^ h') (ctree_leaf_table h)"
  have inv: "length tab = 2"
    "\<And>i b et. i < length tab \<Longrightarrow> ctree_sub (ctree_table_sub tab i b) et = tab_spec h' i b et"
    using tab_invariant[of h' h] Suc by (auto simp: tab_def)
  obtain t0 t1 t2 t3 where tb: "tab = [CtreePair t0 t1, CtreePair t2 t3]"
    using inv(1) by (cases tab rule: remdups_adj.cases; cases "hd tab"; cases "hd (tl tab)") auto
  have init: "ctree_init_tree h = ctree_cons (ctree_prune_1 t1) (ctree_prune_2 t2) (ctree_prune_3 t3)"
    using tb Suc by (simp add: ctree_init_tree_def tab_def)
  have t1: "ctree_sub t1 et = tab_spec h' 0 True et" and t2: "ctree_sub t2 et = tab_spec h' 1 False et"
    and t3: "ctree_sub t3 et = tab_spec h' 1 True et" for et
    using inv(2)[of 0 True et] inv(2)[of 1 False et] inv(2)[of 1 True et] tb
    by (simp_all add: ctree_table_sub_def)
  show ?thesis
  proof (cases et)
    case Nil
    then show ?thesis using init Suc by simp
  next
    case (Cons e et')
    have ttl: "ttail (e # et') = permt (edge_rot e) et'" if "e \<noteq> Color0"
      using that by (simp add: ttail_def proper_trace_def head_color_def)
    show ?thesis
    proof (cases e)
      case Color0
      then show ?thesis using init Cons by (simp add: ctrace_def)
    next
      case Color1
      then show ?thesis using init Cons t1 ttl Suc
        by (simp add: ctree_prune_1_sub tab_spec_def Let_def ctrace_def even_trace_def count_cbit1_append)
    next
      case Color2
      then show ?thesis using init Cons t2 ttl Suc
        by (simp add: ctree_prune_2_sub tab_spec_def Let_def ctrace_def even_trace_def count_cbit1_append)
    next
      case Color3
      then show ?thesis using init Cons t3 ttl Suc
        by (simp add: ctree_prune_3_sub tab_spec_def Let_def ctrace_def even_trace_def count_cbit1_append)
    qed
  qed
qed

end
