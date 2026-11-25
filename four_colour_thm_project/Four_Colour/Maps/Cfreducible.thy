(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Cfreducible.thy
    The reducibility check for a configuration: the Kempe tree of the ring and the
    contract tree are disjoint.
    Ported from G. Gonthier's Coq development (cfreducible.v).
*)
theory Cfreducible
  imports Four_Colour_Maps.Cfcontract2
begin

definition C_reducible :: "'a hypermap \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "C_reducible G r cc \<longleftrightarrow> valid_contract G r cc \<and>
     (\<forall>et. cc_ring_trace G cc (rev r) et \<longrightarrow> Kempe_coclosure (ring_trace G (rev r)) et)"

definition check_reducible :: "config \<Rightarrow> bool" where
  "check_reducible cf = (case contract_ctree cf of
      Some t \<Rightarrow> ctree_disjoint (Kempe_tree (cfprog cf)) t | None \<Rightarrow> False)"

definition cfreducible :: "config \<Rightarrow> bool" where
  "cfreducible cf \<longleftrightarrow> C_reducible (cpG (cfprog cf)) (cfring cf) (cfcontract cf)"

lemma rot1_inj: "rot 1 a = rot 1 b \<Longrightarrow> a = b"
  by (cases a; cases b) (auto simp: rot_def)

lemma rot1_Cons: "rot 1 (c # e) = e @ [c]"
  by (simp add: rot_def)

lemma Kempe_closed_rot1:
  assumes "Kempe_closed P"
  shows "Kempe_closed (\<lambda>x. \<exists>y. x = rot 1 y \<and> P y)"
  unfolding Kempe_closed_def
proof (intro allI impI)
  fix x assume "\<exists>y. x = rot 1 y \<and> P y"
  then obtain y where xy: "x = rot 1 y" and Py: "P y" by blast
  from assms Py have pg: "\<forall>g. P (permt g y)"
    and gw: "\<exists>w. matchg [] y w \<and> (\<forall>et'. matchg [] et' w \<longrightarrow> P et')"
    unfolding Kempe_closed_def by blast+
  have A: "\<forall>g. \<exists>y'. permt g x = rot 1 y' \<and> P y'"
    using pg xy by (metis map_rot permt_def)
  from gw obtain w where m: "matchg [] y w" and wP: "\<forall>et'. matchg [] et' w \<longrightarrow> P et'" by blast
  have B: "\<exists>w. matchg [] x w \<and> (\<forall>et'. matchg [] et' w \<longrightarrow> (\<exists>y. et' = rot 1 y \<and> P y))"
  proof (intro exI[of _ "gram_rot w"] conjI allI impI)
    show "matchg [] x (gram_rot w)" unfolding xy match_gram_rot by (rule m)
    fix et2 assume "matchg [] et2 (gram_rot w)"
    then have "matchg [] (rot 1 (rotr1 et2)) (gram_rot w)" by (simp only: rot_rotr1)
    then have "matchg [] (rotr1 et2) w" by (simp only: match_gram_rot)
    then show "\<exists>y. et2 = rot 1 y \<and> P y" using wP rot_rotr1[of et2] by metis
  qed
  from A B show "(\<forall>g. \<exists>y. permt g x = rot 1 y \<and> P y) \<and>
      (\<exists>w. matchg [] x w \<and> (\<forall>et'. matchg [] et' w \<longrightarrow> (\<exists>y. et' = rot 1 y \<and> P y)))" by blast
qed

theorem check_reducible_valid:
  assumes chk: "check_reducible cf"
  shows "cfreducible cf"
proof -
  define cp where "cp = cfprog cf"
  define r where "r = cpring_of cp"
  obtain t where ct: "contract_ctree cf = Some t" and dj: "ctree_disjoint (Kempe_tree cp) t"
    using chk by (auto simp: check_reducible_def cp_def split: option.splits)
  have rr: "rev (cfring cf) = r" by (simp add: cfring_def r_def cp_def)
  have co: "Kempe_coclosure (ring_trace (cpG cp) r) et"
    if tr: "cc_ring_trace (cpG cp) (cfcontract cf) r et" for et
  proof -
    obtain k where et: "et = trace (map k r)" using tr by (auto simp: cc_ring_trace_def)
    have mem: "ctree_mem t (etrace (tl et))" using contract_ctreeP(2)[OF ct] tr rr by (simp add: cp_def)
    have nm: "\<not> ctree_mem (Kempe_tree cp) (etrace (tl et))" by (rule ctree_mem_disjoint[OF dj mem])
    have rne: "r \<noteq> []" using hypermap.cpring_ne[OF hypermap_cpmap[of cp]] by (simp add: r_def cpring_of_def)
    have len: "length (tl et) = cprsize cp - 1" using et by (simp add: r_def size_ring_cpmap)
    have KC: "Kempe_coclosure (ring_trace (cpG cp) (rot 1 r)) (ctrace (tl et))"
      using Kempe_treeP[OF len] nm by (simp add: r_def)
    have "et \<noteq> []" using et rne length_trace[of "map k r"] by (metis length_0_conv length_map)
    then obtain c e where etc: "et = c # e" by (cases et) auto
    have "sumt (c # e) = Color0" unfolding etc[symmetric] et by (rule sumt_trace)
    then have cs: "c = sumt e" by (cases c; cases "sumt e") simp_all
    have rot_et: "ctrace (tl et) = rot 1 et" using etc cs by (simp add: ctrace_def rot1_Cons)
    show ?thesis unfolding Kempe_coclosure_def
    proof (intro allI impI)
      fix P assume kP: "Kempe_closed P" and Pet: "P et"
      have "\<exists>et1. ring_trace (cpG cp) (rot 1 r) et1 \<and> (\<exists>y. et1 = rot 1 y \<and> P y)"
        using KC Kempe_closed_rot1[OF kP] Pet rot_et unfolding Kempe_coclosure_def by blast
      then obtain y k' where col: "coloring (cpG cp) k'" and ey: "rot 1 y = trace (map k' (rot 1 r))"
        and Py: "P y" unfolding ring_trace_def by metis
      have "rot 1 y = rot 1 (trace (map k' r))" using ey by (simp add: map_rot trace_rot)
      then have "y = trace (map k' r)" by (rule rot1_inj)
      then show "\<exists>et'. ring_trace (cpG cp) r et' \<and> P et'" using col Py unfolding ring_trace_def by blast
    qed
  qed
  show ?thesis
    unfolding cfreducible_def C_reducible_def using contract_ctreeP(1)[OF ct] co rr by (simp add: cp_def)
qed

end
