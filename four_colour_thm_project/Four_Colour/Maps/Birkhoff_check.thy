(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Birkhoff_check.thy
    The computational part of the Birkhoff theorem (birkhoff.v, BirkhoffCheck).
*)
theory Birkhoff_check
  imports Four_Colour_Maps.Kempetree
begin

fun cpcard :: "cprog \<Rightarrow> nat" where
  "cpcard [] = 2"
| "cpcard (CpU # cp) = Suc (Suc (cpcard cp))"
| "cpcard (CpK # cp) = Suc (Suc (cpcard cp))"
| "cpcard (CpY # cp) = cpcard cp + 4"
| "cpcard (CpH # cp) = cpcard cp + 6"
| "cpcard (_ # cp) = cpcard cp"

definition Birkhoff_check1 :: "nat \<Rightarrow> nat \<Rightarrow> cprog \<Rightarrow> bool" where
  "Birkhoff_check1 h m cp \<longleftrightarrow> cubic_prog cp \<and> Suc (cpcard cp) < 6 * m + 4 * h \<and> cprsize cp = Suc h"

fun ctree_pick_rev_rec :: "colseq \<Rightarrow> color \<Rightarrow> ctree \<Rightarrow> ctree \<Rightarrow> colseq" where
  "ctree_pick_rev_rec et e t' (CtreeLeaf _) =
     (if ctree_mem t' (etrace (butlast (e # et))) then e # et else [])"
| "ctree_pick_rev_rec et e t' (CtreeNode t1 t2 t3) =
     (case ctree_pick_rev_rec (Color1 # et) (e +c Color1) t' t1 of
        e' # et' \<Rightarrow> e' # et'
      | [] \<Rightarrow> (case ctree_pick_rev_rec (Color2 # et) (e +c Color2) t' t2 of
                 e' # et' \<Rightarrow> e' # et'
               | [] \<Rightarrow> ctree_pick_rev_rec (Color3 # et) (e +c Color3) t' t3))"
| "ctree_pick_rev_rec et e t' CtreeEmpty = []"

definition ctree_pick_rev :: "ctree \<Rightarrow> ctree \<Rightarrow> colseq" where
  "ctree_pick_rev t' t = ctree_pick_rev_rec [] Color0 t' t"

definition do_Birkhoff_check2 ::
  "nat \<Rightarrow> (ctree \<Rightarrow> bool) \<Rightarrow> colseq \<Rightarrow> ctree \<Rightarrow> gtree \<Rightarrow> (ctree \<Rightarrow> gtree \<Rightarrow> bool) \<Rightarrow> bool" where
  "do_Birkhoff_check2 h cb et ctu gtu chk =
     (if Color0 \<in> set et then False
      else (case Kempe_tree_closure (h - 1) h ctu (ctree_of_ttail (etrace et)) gtu of
              (ctu', GtreePair gtr gtu') \<Rightarrow> gtr = GtreeEmpty \<and> (cb ctu' \<or> chk ctu' gtu')))"

fun Birkhoff_check2 :: "nat \<Rightarrow> (ctree \<Rightarrow> bool) \<Rightarrow> ctree \<Rightarrow> gtree \<Rightarrow> nat \<Rightarrow> ctree \<Rightarrow> gtree \<Rightarrow> bool" where
  "Birkhoff_check2 h cb ctu1 gtu1 0 ctu2 gtu2 = False"
| "Birkhoff_check2 h cb ctu1 gtu1 (Suc n) ctu2 gtu2 =
     (case ctree_pick_rev ctu1 ctu2 of
        [] \<Rightarrow> False
      | e # et \<Rightarrow> do_Birkhoff_check2 h cb (butlast (e # et)) ctu1 gtu1 (Birkhoff_check2 h cb ctu2 gtu2 n) \<and>
                  do_Birkhoff_check2 h cb (rev et) ctu2 gtu2 (Birkhoff_check2 h cb ctu1 gtu1 n))"

definition Birkhoff_basis_check :: "cprog list \<Rightarrow> ctree \<Rightarrow> bool" where
  "Birkhoff_basis_check cps t = list_ex (ctree_disjoint t) (map cpcolor cps)"

definition Birkhoff_check_with :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> cprog list \<Rightarrow> bool" where
  "Birkhoff_check_with h m niter cps \<longleftrightarrow>
     list_all (Birkhoff_check1 h m) cps \<and>
     Birkhoff_check2 h (Birkhoff_basis_check cps) (ctree_init_tree h) (gtree_init_tree h) niter
       (ctree_init_tree h) (gtree_init_tree h)"

definition Birkhoff_check :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "Birkhoff_check h m \<longleftrightarrow> (\<exists>niter cps. Birkhoff_check_with h m niter cps)"

lemma Birkhoff2: "Birkhoff_check 1 0"
  unfolding Birkhoff_check_def by (rule exI[of _ 1], rule exI[of _ "[[]]"]) eval

lemma Birkhoff3: "Birkhoff_check 2 0"
  unfolding Birkhoff_check_def by (rule exI[of _ 1], rule exI[of _ "[[CpY]]"]) eval

lemma Birkhoff4: "Birkhoff_check 3 0"
  unfolding Birkhoff_check_def by (rule exI[of _ 4], rule exI[of _ "[[CpU], [CpR 1, CpU]]"]) eval

lemma Birkhoff5: "Birkhoff_check 4 1"
  unfolding Birkhoff_check_def
  by (rule exI[of _ 10], rule exI[of _ "[[CpU, CpY], [CpR 1, CpU, CpY], [CpR 2, CpU, CpY],
      [CpR 3, CpU, CpY], [CpR 4, CpU, CpY], [CpH, CpR 4, CpY, CpY, CpY]]"]) eval

end
