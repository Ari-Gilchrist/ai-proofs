(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Ctreerestrict.thy
    Second phase of a D-reducibility step: subtracting chromogram match counts
    from a coloring tree.
    Ported from G. Gonthier's Coq development (ctreerestrict.v).

    Design note: Gonthier's continuation-passing ctr_split / ctr_decr are
    replaced by functions returning triples; ctr_split_eq / ctr_decr_eq then
    hold by definition.
*)
theory Ctreerestrict
  imports Four_Colour_Maps.Gtree Four_Colour_Maps.Ctree
begin

datatype ctree_restriction = CtrNil | CtrCons "bool list" gtree ctree_restriction

definition ctr_cons :: "bool list \<Rightarrow> gtree \<Rightarrow> ctree_restriction \<Rightarrow> ctree_restriction" where
  "ctr_cons bs t r = (if t = GtreeEmpty then r else CtrCons bs t r)"

fun ctr_sub :: "ctree_restriction \<Rightarrow> colseq \<Rightarrow> nat" where
  "ctr_sub CtrNil et = 0"
| "ctr_sub (CtrCons bs t r) et = gtree_sub t bs et + ctr_sub r et"

lemma ctr_sub_cons [simp]: "ctr_sub (ctr_cons bs t r) et = gtree_sub t bs et + ctr_sub r et"
  by (simp add: ctr_cons_def)

section \<open>Splitting a restriction\<close>

definition cons_pop :: "bool list \<Rightarrow> gtree \<Rightarrow> gtree \<Rightarrow> ctree_restriction \<Rightarrow> ctree_restriction" where
  "cons_pop bs t t' r = (case bs of [] \<Rightarrow> r | b # bs' \<Rightarrow> ctr_cons bs' (if b then t' else t) r)"

fun ctr_split :: "ctree_restriction \<Rightarrow> ctree_restriction \<Rightarrow> ctree_restriction \<Rightarrow> ctree_restriction \<Rightarrow>
                  ctree_restriction \<times> ctree_restriction \<times> ctree_restriction" where
  "ctr_split r1 r2 r3 CtrNil = (r1, r2, r3)"
| "ctr_split r1 r2 r3 (CtrCons bs (GtreeNode t0 t1 t2 t3) r) =
     ctr_split (ctr_cons bs t1 r1) (ctr_cons (False # bs) t0 (cons_pop bs t2 t3 r2))
               (ctr_cons (True # bs) t0 (cons_pop bs t3 t2 r3)) r"
| "ctr_split r1 r2 r3 (CtrCons bs _ r) = ctr_split r1 r2 r3 r"

definition csel :: "'b \<Rightarrow> 'b \<times> 'b \<times> 'b \<Rightarrow> color \<Rightarrow> 'b" where
  "csel z p e = (case p of (a, b, c) \<Rightarrow> palette z a b c e)"

definition csplit :: "ctree_restriction \<Rightarrow> color \<Rightarrow> ctree_restriction" where
  "csplit r e = csel CtrNil (ctr_split CtrNil CtrNil CtrNil r) e"

lemma gtree_mem_Nil [simp]: "\<not> gtree_mem t []"
  by (cases t) simp_all

lemma ctr_sub_Nil [simp]: "ctr_sub r [] = 0"
  by (induction r) (simp_all add: gtree_sub_def)

lemma match_count_len_ne:
  "(\<And>w. st w \<Longrightarrow> length w \<noteq> length et) \<Longrightarrow> match_count st lb et = 0"
  using match_countP matchpg_size by metis

lemma match_count_eta: "match_count (\<lambda>w. st w) lb et = match_count st lb et"
  by simp

lemma gtree_sub_nonnode:
  assumes "\<And>t0 t1 t2 t3. t \<noteq> GtreeNode t0 t1 t2 t3"
  shows "gtree_sub t bs (e # e' # et) = 0"
proof -
  have "length w \<le> 1" if "gtree_mem t w" for w
    using that assms by (cases "(t, w)" rule: gtree_mem.cases) auto
  then show ?thesis unfolding gtree_sub_def
    by (intro match_count_len_ne) fastforce
qed

lemma ctr_sub_split_gen:
  "ctr_sub (csel CtrNil (ctr_split r1 r2 r3 r) e) (e' # et) =
   ctr_sub (csel CtrNil (r1, r2, r3) e) (e' # et) + ctr_sub r (e # e' # et)"
proof (induction r1 r2 r3 r rule: ctr_split.induct)
  case (1 r1 r2 r3)
  then show ?case by simp
next
  case (2 r1 r2 r3 bs t0 t1 t2 t3 r)
  have key: "ctr_sub (csel CtrNil (ctr_cons bs t1 r1, ctr_cons (False # bs) t0 (cons_pop bs t2 t3 r2),
                ctr_cons (True # bs) t0 (cons_pop bs t3 t2 r3)) e) (e' # et) =
             ctr_sub (csel CtrNil (r1, r2, r3) e) (e' # et) + gtree_sub (GtreeNode t0 t1 t2 t3) bs (e # e' # et)"
  proof (cases e)
    case Color2
    then show ?thesis
      by (cases bs; cases "hd bs") (simp_all add: csel_def cons_pop_def gtree_sub_def)
  next
    case Color3
    then show ?thesis
      by (cases bs; cases "hd bs") (simp_all add: csel_def cons_pop_def gtree_sub_def)
  qed (simp_all add: csel_def gtree_sub_def)
  show ?case using 2 key by simp
next
  case ("3_1" r1 r2 r3 bs r)
  then show ?case by (simp add: gtree_sub_nonnode)
qed (simp_all add: gtree_sub_nonnode)

lemma ctr_sub_csplit:
  "ctr_sub (csplit r e) et = (if et = [] then 0 else ctr_sub r (e # et))"
proof (cases et)
  case (Cons e' et')
  then show ?thesis
    using ctr_sub_split_gen[of CtrNil CtrNil CtrNil r e e' et'] by (cases e) (simp_all add: csplit_def csel_def)
qed simp

section \<open>Decrementing leaves\<close>

fun ctree_decr :: "ctree \<Rightarrow> nat \<Rightarrow> ctree" where
  "ctree_decr lf 0 = lf"
| "ctree_decr (CtreeLeaf lf') (Suc n) = ctree_decr lf' n"
| "ctree_decr lf (Suc n) = lf"

lemma ctree_val_decr: "ctree_decr (ctree_leaf_of m) n = ctree_leaf_of (m - n)"
proof (induction n arbitrary: m)
  case (Suc n)
  then show ?case by (cases m) (simp_all add: ctree_leaf_of_def)
qed simp

lemma ctree_no_decr: "\<not> ctree_leaf t \<Longrightarrow> ctree_decr t n = t"
  by (cases t; cases n) simp_all

definition ctr_e_decr :: "bool list \<Rightarrow> gtree \<Rightarrow> color \<Rightarrow> ctree \<Rightarrow> ctree" where
  "ctr_e_decr bs t e lf = ctree_decr lf (gtree_sub t bs [e])"

fun ctr_decr :: "ctree \<Rightarrow> ctree \<Rightarrow> ctree \<Rightarrow> ctree_restriction \<Rightarrow> ctree \<times> ctree \<times> ctree" where
  "ctr_decr lf1 lf2 lf3 CtrNil = (lf1, lf2, lf3)"
| "ctr_decr lf1 lf2 lf3 (CtrCons bs t r) =
     ctr_decr (ctr_e_decr bs t Color1 lf1) (ctr_e_decr bs t Color2 lf2) (ctr_e_decr bs t Color3 lf3) r"

definition cdecr :: "color \<Rightarrow> ctree \<Rightarrow> ctree \<Rightarrow> ctree \<Rightarrow> ctree_restriction \<Rightarrow> ctree" where
  "cdecr e lf1 lf2 lf3 r = csel CtreeEmpty (ctr_decr lf1 lf2 lf3 r) e"

lemma ctree_leaf_of_0 [simp]: "ctree_leaf_of 0 = CtreeEmpty"
  by (simp add: ctree_leaf_of_def)

lemma ctree_proper_leaf_of_val: "ctree_proper 0 lf \<Longrightarrow> lf = ctree_leaf_of (ctree_sub lf [])"
proof (induction lf)
  case (CtreeLeaf lf)
  then show ?case by (simp add: ctree_leaf_of_def)
qed (simp_all add: ctree_leaf_of_def)

lemma cdecr_leaf_gen:
  "ctr_decr (ctree_leaf_of n1) (ctree_leaf_of n2) (ctree_leaf_of n3) r =
   (ctree_leaf_of (n1 - ctr_sub r [Color1]), ctree_leaf_of (n2 - ctr_sub r [Color2]),
    ctree_leaf_of (n3 - ctr_sub r [Color3]))"
proof (induction r arbitrary: n1 n2 n3)
  case CtrNil
  then show ?case by simp
next
  case (CtrCons bs t r)
  then show ?case by (simp add: ctr_e_decr_def ctree_val_decr diff_diff_add)
qed

lemma cdecr_leaf:
  assumes "ctree_proper 0 lf1" "ctree_proper 0 lf2" "ctree_proper 0 lf3"
  shows "cdecr e lf1 lf2 lf3 r =
         ctree_leaf_of (ctree_sub (CtreeNode lf1 lf2 lf3) [e] - ctr_sub r [e])"
proof -
  have "cdecr e lf1 lf2 lf3 r =
        cdecr e (ctree_leaf_of (ctree_sub lf1 [])) (ctree_leaf_of (ctree_sub lf2 []))
                (ctree_leaf_of (ctree_sub lf3 [])) r"
    using ctree_proper_leaf_of_val[OF assms(1)] ctree_proper_leaf_of_val[OF assms(2)]
      ctree_proper_leaf_of_val[OF assms(3)] by simp
  also have "\<dots> = ctree_leaf_of (ctree_sub (CtreeNode lf1 lf2 lf3) [e] - ctr_sub r [e])"
    by (cases e) (simp_all add: cdecr_def csel_def cdecr_leaf_gen)
  finally show ?thesis .
qed

section \<open>Pairs and partitions\<close>

fun ctree_cons_pairs :: "ctree_pair \<Rightarrow> ctree_pair \<Rightarrow> ctree_pair \<Rightarrow> ctree_pair" where
  "ctree_cons_pairs (CtreePair t1 t1') (CtreePair t2 t2') (CtreePair t3 t3') =
     CtreePair (ctree_cons t1 t2 t3) (ctree_cons t1' t2' t3')"

definition sctree_partition :: "spec_ctree \<Rightarrow> spec_ctree \<Rightarrow> spec_ctree \<Rightarrow> bool" where
  "sctree_partition st st' st'' \<longleftrightarrow>
     (\<forall>et. if st et then st' et \<noteq> st'' et else \<not> st' et \<and> \<not> st'' et)"

fun ctree_partition :: "ctree \<Rightarrow> ctree_pair \<Rightarrow> bool" where
  "ctree_partition t (CtreePair t' t'') = sctree_partition (ctree_mem t) (ctree_mem t') (ctree_mem t'')"

lemma ctree_cons_pairs_partition:
  assumes "ctree_partition t1 pt1" "ctree_partition t2 pt2" "ctree_partition t3 pt3"
  shows "ctree_partition (CtreeNode t1 t2 t3) (ctree_cons_pairs pt1 pt2 pt3)"
proof -
  obtain t1' t1'' t2' t2'' t3' t3'' where
    p: "pt1 = CtreePair t1' t1''" "pt2 = CtreePair t2' t2''" "pt3 = CtreePair t3' t3''"
    by (cases pt1; cases pt2; cases pt3) auto
  have P: "sctree_partition (ctree_mem t1) (ctree_mem t1') (ctree_mem t1'')"
    "sctree_partition (ctree_mem t2) (ctree_mem t2') (ctree_mem t2'')"
    "sctree_partition (ctree_mem t3) (ctree_mem t3') (ctree_mem t3'')"
    using assms p by simp_all
  show ?thesis unfolding p ctree_cons_pairs.simps ctree_partition.simps sctree_partition_def
  proof
    fix et
    show "if ctree_mem (CtreeNode t1 t2 t3) et
          then ctree_mem (ctree_cons t1' t2' t3') et \<noteq> ctree_mem (ctree_cons t1'' t2'' t3'') et
          else \<not> ctree_mem (ctree_cons t1' t2' t3') et \<and> \<not> ctree_mem (ctree_cons t1'' t2'' t3'') et"
    proof (cases et)
      case (Cons e et')
      then show ?thesis using P[unfolded sctree_partition_def]
        by (cases e) (simp_all add: ctree_mem_sel del: ctree_mem_cons)
    qed simp
  qed
qed

definition if_e :: "ctree \<Rightarrow> ctree \<Rightarrow> ctree" where
  "if_e lf lf' = (if lf' = CtreeEmpty then lf else CtreeEmpty)"

definition ctree_leaf_pair :: "ctree \<Rightarrow> ctree \<Rightarrow> ctree \<Rightarrow> ctree \<Rightarrow> ctree \<Rightarrow> ctree \<Rightarrow> ctree_pair" where
  "ctree_leaf_pair lf1 lf2 lf3 lf1' lf2' lf3' =
     CtreePair (ctree_cons lf1' lf2' lf3') (ctree_cons (if_e lf1 lf1') (if_e lf2 lf2') (if_e lf3 lf3'))"

section \<open>Restriction\<close>

fun ctree_restrict :: "nat \<Rightarrow> ctree \<Rightarrow> ctree_restriction \<Rightarrow> ctree_pair" where
  "ctree_restrict h t CtrNil = CtreePair t CtreeEmpty"
| "ctree_restrict (Suc h) (CtreeNode t1 t2 t3) (CtrCons bs g r) =
     (case ctr_split CtrNil CtrNil CtrNil (CtrCons bs g r) of (r1, r2, r3) \<Rightarrow>
        ctree_cons_pairs (ctree_restrict h t1 r1) (ctree_restrict h t2 r2) (ctree_restrict h t3 r3))"
| "ctree_restrict 0 (CtreeNode lf1 lf2 lf3) (CtrCons bs g r) =
     (case ctr_decr lf1 lf2 lf3 (CtrCons bs g r) of (a, b, c) \<Rightarrow> ctree_leaf_pair lf1 lf2 lf3 a b c)"
| "ctree_restrict _ _ _ = ctree_empty_pair"

lemma ctree_proper_Suc_sub_Nil: "ctree_proper (Suc h) t \<Longrightarrow> ctree_sub t [] = 0"
  by (cases t) simp_all

lemma ctree_mem_leaf_of: "ctree_mem (ctree_leaf_of n) et \<longleftrightarrow> et = [] \<and> n \<noteq> 0"
  by (simp add: ctree_mem_def ctree_sub_leaf_of)

lemma ctree_restrict_base:
  assumes ok: "ctree_proper (Suc 0) t"
  shows "(\<forall>b. ctree_proper (Suc 0) (ctree_pair_sub (ctree_restrict 0 t r) b)) \<and>
         ctree_partition t (ctree_restrict 0 t r) \<and>
         (\<forall>et. ctree_sub (ctree_pair_sub (ctree_restrict 0 t r) False) et = ctree_sub t et - ctr_sub r et)"
proof (cases r)
  case CtrNil
  then show ?thesis using ok by (simp add: sctree_partition_def)
next
  case (CtrCons bs g r')
  show ?thesis
  proof (cases t)
    case CtreeEmpty
    then show ?thesis using CtrCons by (simp add: ctree_empty_pair_def sctree_partition_def)
  next
    case (CtreeLeaf x)
    then show ?thesis using ok by simp
  next
    case (CtreeNode lf1 lf2 lf3)
    have p: "ctree_proper 0 lf1" "ctree_proper 0 lf2" "ctree_proper 0 lf3" using ok CtreeNode by simp_all
    define n1 n2 n3 where "n1 = ctree_sub lf1 []" "n2 = ctree_sub lf2 []" "n3 = ctree_sub lf3 []"
    define s1 s2 s3 where "s1 = ctr_sub r [Color1]" "s2 = ctr_sub r [Color2]" "s3 = ctr_sub r [Color3]"
    have lf: "lf1 = ctree_leaf_of n1" "lf2 = ctree_leaf_of n2" "lf3 = ctree_leaf_of n3"
      using ctree_proper_leaf_of_val p unfolding n1_n2_n3_def by blast+
    have dec: "ctr_decr lf1 lf2 lf3 r = (ctree_leaf_of (n1 - s1), ctree_leaf_of (n2 - s2), ctree_leaf_of (n3 - s3))"
      unfolding lf s1_s2_s3_def by (rule cdecr_leaf_gen)
    have R: "ctree_restrict 0 t r =
             ctree_leaf_pair lf1 lf2 lf3 (ctree_leaf_of (n1 - s1)) (ctree_leaf_of (n2 - s2)) (ctree_leaf_of (n3 - s3))"
      using dec CtrCons CtreeNode by simp
    have leE: "ctree_leaf_of m = CtreeEmpty \<longleftrightarrow> m = 0" for m
      by (cases m) (simp_all add: ctree_leaf_of_def)
    have ife: "if_e (ctree_leaf_of n) (ctree_leaf_of (n - s)) = ctree_leaf_of (if n - s = 0 then n else 0)" for n s
      by (auto simp: if_e_def leE)
    have props: "\<forall>b. ctree_proper (Suc 0) (ctree_pair_sub (ctree_restrict 0 t r) b)"
      unfolding R ctree_leaf_pair_def lf ife
      by (auto intro!: ctree_cons_proper ctree_leaf_of_proper)
    have part: "ctree_partition t (ctree_restrict 0 t r)"
      unfolding R ctree_leaf_pair_def ctree_partition.simps sctree_partition_def
    proof
      fix et
      show "if ctree_mem t et then ctree_mem (ctree_cons (ctree_leaf_of (n1 - s1)) (ctree_leaf_of (n2 - s2)) (ctree_leaf_of (n3 - s3))) et \<noteq>
              ctree_mem (ctree_cons (if_e lf1 (ctree_leaf_of (n1 - s1))) (if_e lf2 (ctree_leaf_of (n2 - s2))) (if_e lf3 (ctree_leaf_of (n3 - s3)))) et
            else \<not> ctree_mem (ctree_cons (ctree_leaf_of (n1 - s1)) (ctree_leaf_of (n2 - s2)) (ctree_leaf_of (n3 - s3))) et \<and>
              \<not> ctree_mem (ctree_cons (if_e lf1 (ctree_leaf_of (n1 - s1))) (if_e lf2 (ctree_leaf_of (n2 - s2))) (if_e lf3 (ctree_leaf_of (n3 - s3)))) et"
      proof (cases et)
        case (Cons e et')
        then show ?thesis unfolding CtreeNode lf ife
          by (cases e) (simp_all add: ctree_mem_sel ctree_mem_leaf_of del: ctree_mem_cons)
      qed (simp add: CtreeNode)
    qed
    have sub: "\<forall>et. ctree_sub (ctree_pair_sub (ctree_restrict 0 t r) False) et = ctree_sub t et - ctr_sub r et"
    proof
      fix et
      show "ctree_sub (ctree_pair_sub (ctree_restrict 0 t r) False) et = ctree_sub t et - ctr_sub r et"
      proof (cases et)
        case (Cons e et')
        then show ?thesis unfolding R unfolding ctree_leaf_pair_def CtreeNode lf
          by (cases e; cases et') (simp_all add: ctree_sub_leaf_of s1_s2_s3_def)
      qed (unfold R, simp add: ctree_leaf_pair_def CtreeNode)
    qed
    show ?thesis using props part sub by blast
  qed
qed

theorem ctree_restrict_correct:
  "ctree_proper (Suc h) t \<Longrightarrow>
   (\<forall>b. ctree_proper (Suc h) (ctree_pair_sub (ctree_restrict h t r) b)) \<and>
   ctree_partition t (ctree_restrict h t r) \<and>
   (\<forall>et. ctree_sub (ctree_pair_sub (ctree_restrict h t r) False) et = ctree_sub t et - ctr_sub r et)"
proof (induction h arbitrary: t r)
  case 0
  then show ?case using ctree_restrict_base by blast
next
  case (Suc h)
  show ?case
  proof (cases r)
    case CtrNil
    then show ?thesis using Suc.prems by (simp add: sctree_partition_def)
  next
    case (CtrCons bs g r')
    show ?thesis
    proof (cases t)
      case CtreeEmpty
      then show ?thesis using CtrCons by (simp add: ctree_empty_pair_def sctree_partition_def)
    next
      case (CtreeLeaf x)
      then show ?thesis using Suc.prems by simp
    next
      case (CtreeNode t1 t2 t3)
      have p: "ctree_proper (Suc h) t1" "ctree_proper (Suc h) t2" "ctree_proper (Suc h) t3"
        using Suc.prems CtreeNode by simp_all
      obtain r1 r2 r3 where sp: "ctr_split CtrNil CtrNil CtrNil r = (r1, r2, r3)"
        by (cases "ctr_split CtrNil CtrNil CtrNil r") auto
      have cs: "csplit r Color1 = r1" "csplit r Color2 = r2" "csplit r Color3 = r3"
        using sp by (simp_all add: csplit_def csel_def)
      have R: "ctree_restrict (Suc h) t r =
               ctree_cons_pairs (ctree_restrict h t1 r1) (ctree_restrict h t2 r2) (ctree_restrict h t3 r3)"
        using sp CtrCons CtreeNode by simp
      obtain a1 b1 where P1: "ctree_restrict h t1 r1 = CtreePair a1 b1" by (cases "ctree_restrict h t1 r1") auto
      obtain a2 b2 where P2: "ctree_restrict h t2 r2 = CtreePair a2 b2" by (cases "ctree_restrict h t2 r2") auto
      obtain a3 b3 where P3: "ctree_restrict h t3 r3 = CtreePair a3 b3" by (cases "ctree_restrict h t3 r3") auto
      note I1 = Suc.IH[OF p(1), of r1] and I2 = Suc.IH[OF p(2), of r2] and I3 = Suc.IH[OF p(3), of r3]
      have props: "\<forall>b. ctree_proper (Suc (Suc h)) (ctree_pair_sub (ctree_restrict (Suc h) t r) b)"
      proof
        fix b
        have "ctree_proper (Suc h) (ctree_pair_sub (CtreePair a1 b1) b)"
          "ctree_proper (Suc h) (ctree_pair_sub (CtreePair a2 b2) b)"
          "ctree_proper (Suc h) (ctree_pair_sub (CtreePair a3 b3) b)"
          using I1 I2 I3 P1 P2 P3 by metis+
        then show "ctree_proper (Suc (Suc h)) (ctree_pair_sub (ctree_restrict (Suc h) t r) b)"
          unfolding R P1 P2 P3 by (cases b) (simp_all add: ctree_cons_proper)
      qed
      have part: "ctree_partition t (ctree_restrict (Suc h) t r)"
        unfolding R unfolding CtreeNode using I1 I2 I3 by (blast intro: ctree_cons_pairs_partition)
      have sub: "\<forall>et. ctree_sub (ctree_pair_sub (ctree_restrict (Suc h) t r) False) et = ctree_sub t et - ctr_sub r et"
      proof
        fix et
        have S1: "ctree_sub a1 et' = ctree_sub t1 et' - ctr_sub r1 et'"
          and S2: "ctree_sub a2 et' = ctree_sub t2 et' - ctr_sub r2 et'"
          and S3: "ctree_sub a3 et' = ctree_sub t3 et' - ctr_sub r3 et'" for et'
          using I1 I2 I3 P1 P2 P3 by (metis ctree_pair_sub.simps)+
        show "ctree_sub (ctree_pair_sub (ctree_restrict (Suc h) t r) False) et = ctree_sub t et - ctr_sub r et"
        proof (cases et)
          case Nil
          then show ?thesis unfolding R P1 P2 P3 unfolding CtreeNode by simp
        next
          case (Cons e et')
          have z: "ctree_sub t1 [] = 0" "ctree_sub t2 [] = 0" "ctree_sub t3 [] = 0"
            using p ctree_proper_Suc_sub_Nil by blast+
          show ?thesis unfolding R P1 P2 P3 unfolding CtreeNode Cons
            using S1[of et'] S2[of et'] S3[of et'] z
              ctr_sub_csplit[of r Color1 et'] ctr_sub_csplit[of r Color2 et'] ctr_sub_csplit[of r Color3 et']
            by (cases e) (simp_all add: cs gtree_sub_def split: if_splits)
        qed
      qed
      show ?thesis using props part sub by blast
    qed
  qed
qed

end
