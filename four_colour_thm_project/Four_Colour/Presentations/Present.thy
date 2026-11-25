(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Present.thy
    Presentations: verified checker for the unavoidability case analyses (present.v).
    Gonthier's tactic scripts (Pcase / Similar / Reducible / Hubcap) are represented as data of
    type pscript and checked by the executable function check_ps, proved sound below.
    Ported from G. Gonthier's Coq development (present.v).
*)
theory Present
  imports Four_Colour_Parts.Hubcap
begin

datatype pscript =
    PSplit subpart_loc nat nat bool nat pscript pscript
  | PSim nat bool nat
  | PRed
  | PHub hubcap

fun check_ps :: "quiz_tree \<Rightarrow> (nat \<times> part) list \<Rightarrow> part \<Rightarrow> part \<Rightarrow> pscript \<Rightarrow> bool" where
  "check_ps qt env p0 p PRed = redpart qt p"
| "check_ps qt env p0 p (PHub hc) =
     (hubcap_cover (psize p) hc \<and> hubcap_fit (psize p) (redpart qt) p hc)"
| "check_ps qt env p0 p (PSim j mir lab) =
     (case map_of env lab of None \<Rightarrow> False
      | Some ps \<Rightarrow> (let p2 = rot_part j (if mir then mirror_part p else p) in
                    psize ps = psize p2 \<and> cmp_part p2 ps = Psubset))"
| "check_ps qt env p0 p (PSplit i j k lo lab sl sr) =
     (good_split i j k p \<and>
      (let pl = split_part i j k lo p; pr = split_part i j k (\<not> lo) p;
           p0l = (if good_split i j k p0 then split_part i j k lo p0 else pl) in
       check_ps qt env p0l pl sl \<and> check_ps qt ((lab, p0l) # env) p0 pr sr))"

lemma psize0': "psize q = 0 \<Longrightarrow> q = Pnil" by (cases q) simp_all

lemma drop_part_big: "psize q \<le> j \<Longrightarrow> drop_part j q = Pnil"
  by (induction j q rule: drop_part.induct) (auto dest!: psize0')

lemma psize0: "psize q = 0 \<Longrightarrow> q = Pnil" by (cases q) simp_all

lemma take_part_big: "psize q \<le> j \<Longrightarrow> take_part j q = q"
  by (induction j q rule: take_part.induct) (auto dest!: psize0)

section \<open>Semantics\<close>

definition valid_hub :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> bool" where
  "valid_hub G x \<longleftrightarrow> minimal_counter_example G \<and> x \<in> darts G \<and> 0 < dscore G x"

definition successful :: "'a itself \<Rightarrow> part \<Rightarrow> bool" where
  "successful T p \<longleftrightarrow> (\<forall>G :: 'a hypermap. \<forall>x. valid_hub G x \<longrightarrow> \<not> exact_fitp G x p)"

definition forced_part :: "'a itself \<Rightarrow> part \<Rightarrow> part \<Rightarrow> bool" where
  "forced_part T p0 p \<longleftrightarrow> (\<forall>G :: 'a hypermap. \<forall>x. valid_hub G x \<longrightarrow> exact_fitp G x p0 \<longrightarrow> exact_fitp G x p)"

lemma mce_pcp: "minimal_counter_example G \<Longrightarrow> pcp G"
proof -
  assume m: "minimal_counter_example G"
  interpret B: birk G using m by (simp add: birk_def birk_axioms_def mce_hypermap)
  have p: "pentagonal G" by (rule B.minimal_counter_example_is_pentagonal)
  show "pcp G"
    by unfold_locales (use B.plainG B.cubicG p in \<open>auto simp: pentagonal_def\<close>)
qed

lemma valid_hub_mirror:
  assumes "valid_hub G x" shows "valid_hub (mirror G) x"
proof -
  have m: "minimal_counter_example G" and xD: "x \<in> darts G" and pos: "0 < dscore G x"
    using assms by (simp_all add: valid_hub_def)
  interpret P: pcp G by (rule mce_pcp[OF m])
  show ?thesis using P.minimal_counter_example_mirror[OF m] xD pos P.dscore_mirror[OF xD]
    by (simp add: valid_hub_def)
qed

lemma valid_hub_face:
  assumes "valid_hub G x" shows "valid_hub G ((face G ^^ k) x)"
proof -
  have m: "minimal_counter_example G" and xD: "x \<in> darts G" and pos: "0 < dscore G x"
    using assms by (simp_all add: valid_hub_def)
  interpret P: pcp G by (rule mce_pcp[OF m])
  have "dscore G ((face G ^^ k) x) = dscore G x"
    using P.dscore_cface[of x "(face G ^^ k) x"] by (simp add: fconnect_funpow)
  then show ?thesis using m xD pos by (simp add: valid_hub_def)
qed

section \<open>Soundness of the checker\<close>

locale present_ctx =
  fixes T :: "'a itself" and qt :: quiz_tree
  assumes nofit: "\<And>G :: 'a hypermap. minimal_counter_example G \<Longrightarrow> \<forall>y. \<not> qzt_ctx.qzt_fit G y qt"
begin

lemma redpart_ok:
  assumes m: "minimal_counter_example (G :: 'a hypermap)" and r: "redpart qt p" and xD: "x \<in> darts G"
  shows "\<not> exact_fitp G x p"
proof -
  interpret P: pcp G by (rule mce_pcp[OF m])
  show ?thesis
    by (rule no_fit_redpart[OF P.hypermap_axioms P.plainG P.cubicG P.pentaG _ r xD])
       (use nofit[OF m] in auto)
qed

lemma soundness:
  "check_ps qt env p0 p s \<Longrightarrow> (\<forall>(l, q) \<in> set env. successful T q) \<Longrightarrow> forced_part T p0 p \<Longrightarrow>
   successful T p"
proof (induction s arbitrary: env p0 p)
  case PRed
  then show ?case using redpart_ok by (auto simp: successful_def valid_hub_def)
next
  case (PHub hc)
  show ?case unfolding successful_def
  proof (intro allI impI)
    fix G :: "'a hypermap" and x assume vh: "valid_hub G x"
    have m: "minimal_counter_example G" and xD: "x \<in> darts G" and pos: "0 < dscore G x"
      using vh by (simp_all add: valid_hub_def)
    interpret P: pcp G by (rule mce_pcp[OF m])
    have rp: "\<And>x p. x \<in> darts G \<Longrightarrow> redpart qt p \<Longrightarrow> \<not> exact_fitp G x p"
      using redpart_ok[OF m] "PHub.prems" by simp
    have cv: "hubcap_cover (psize p) hc" and ft: "hubcap_fit (psize p) (redpart qt) p hc"
      using "PHub.prems"(1) by simp_all
    show "\<not> exact_fitp G x p" by (rule P.hubcap_fit_bound[OF rp xD refl pos cv ft])
  qed
next
  case (PSim j mir lab)
  obtain ps where ps: "map_of env lab = Some ps" using "PSim.prems"(1) by (cases "map_of env lab") auto
  let ?p1 = "if mir then mirror_part p else p"
  let ?p2 = "rot_part j ?p1"
  have sz: "psize ps = psize ?p2" and cmp: "cmp_part ?p2 ps = Psubset"
    using "PSim.prems"(1) ps by (simp_all add: Let_def)
  have sps: "successful T ps" using "PSim.prems"(2) map_of_SomeD[OF ps] by auto
  show ?case unfolding successful_def
  proof (intro allI impI notI)
    fix G :: "'a hypermap" and x assume vh: "valid_hub G x" and ex: "exact_fitp G x p"
    define G1 where "G1 = (if mir then mirror G else G)"
    have m: "minimal_counter_example G" and xD: "x \<in> darts G" using vh by (simp_all add: valid_hub_def)
    interpret P: pcp G by (rule mce_pcp[OF m])
    have vh1: "valid_hub G1 x" using vh valid_hub_mirror[OF vh] by (cases mir) (simp_all add: G1_def)
    have ex1: "exact_fitp G1 x ?p1" using ex P.exact_fitp_mirror[OF xD] by (simp add: G1_def)
    have m1: "minimal_counter_example G1" and x1D: "x \<in> darts G1" using vh1 by (simp_all add: valid_hub_def)
    interpret P1: pcp G1 by (rule mce_pcp[OF m1])
    obtain x2 where vh2: "valid_hub G1 x2" and ex2: "exact_fitp G1 x2 ?p2"
    proof (cases "j \<le> psize ?p1")
      case True
      have "exact_fitp G1 ((face G1 ^^ j) x) ?p2" using P1.fitp_rot[OF True, of x] ex1 by simp
      then show ?thesis using that valid_hub_face[OF vh1] by blast
    next
      case False
      then have "drop_part j ?p1 = Pnil" "take_part j ?p1 = ?p1"
        using drop_part_big[of ?p1 j] take_part_big[of ?p1 j] by simp_all
      then have "?p2 = ?p1" by (simp add: rot_part_def)
      then show ?thesis using that vh1 ex1 by simp
    qed
    have "exact_fitp G1 x2 ps" using P1.subset_fit[OF cmp] sz ex2 by simp
    then show False using sps vh2 by (simp add: successful_def)
  qed
next
  case (PSplit i j k lo lab sl sr)
  let ?pl = "split_part i j k lo p" and ?pr = "split_part i j k (\<not> lo) p"
  let ?p0l = "if good_split i j k p0 then split_part i j k lo p0 else ?pl"
  have g: "good_split i j k p" and cl: "check_ps qt env ?p0l ?pl sl"
    and cr: "check_ps qt ((lab, ?p0l) # env) p0 ?pr sr" using "PSplit.prems"(1) by (simp_all add: Let_def)
  have fsplit: "\<And>(G :: 'a hypermap) x q b. valid_hub G x \<Longrightarrow> good_split i j k q \<Longrightarrow>
      exact_fitp G x (split_part i j k b q) \<longleftrightarrow> (b \<noteq> fitc i j k G x) \<and> exact_fitp G x q"
  proof -
    fix G :: "'a hypermap" and x q b assume vh: "valid_hub G x" and gq: "good_split i j k q"
    have m: "minimal_counter_example G" and xD: "x \<in> darts G" using vh by (simp_all add: valid_hub_def)
    interpret P: pcp G by (rule mce_pcp[OF m])
    show "exact_fitp G x (split_part i j k b q) \<longleftrightarrow> (b \<noteq> fitc i j k G x) \<and> exact_fitp G x q"
      by (rule P.fitp_split[OF P.pentaG xD gq])
  qed
  have fl: "forced_part T ?p0l ?pl"
    unfolding forced_part_def
  proof (intro allI impI)
    fix G :: "'a hypermap" and x assume vh: "valid_hub G x" and e0: "exact_fitp G x ?p0l"
    show "exact_fitp G x ?pl"
    proof (cases "good_split i j k p0")
      case True
      then have "(lo \<noteq> fitc i j k G x) \<and> exact_fitp G x p0" using e0 fsplit[OF vh True] by simp
      then show ?thesis using "PSplit.prems"(3) vh fsplit[OF vh g] by (auto simp: forced_part_def)
    next
      case False then show ?thesis using e0 by simp
    qed
  qed
  have sl: "successful T ?pl" by (rule PSplit.IH(1)[OF cl "PSplit.prems"(2) fl])
  have s0l: "successful T ?p0l"
    unfolding successful_def
  proof (intro allI impI notI)
    fix G :: "'a hypermap" and x assume vh: "valid_hub G x" and e0: "exact_fitp G x ?p0l"
    have "exact_fitp G x ?pl" using fl vh e0 by (simp add: forced_part_def)
    then show False using sl vh by (simp add: successful_def)
  qed
  have fr: "forced_part T p0 ?pr"
    unfolding forced_part_def
  proof (intro allI impI)
    fix G :: "'a hypermap" and x assume vh: "valid_hub G x" and e0: "exact_fitp G x p0"
    have ep: "exact_fitp G x p" using "PSplit.prems"(3) vh e0 by (simp add: forced_part_def)
    have "\<not> exact_fitp G x ?pl" using sl vh by (simp add: successful_def)
    then have "lo = fitc i j k G x" using fsplit[OF vh g, of lo] ep by simp
    then show "exact_fitp G x ?pr" using fsplit[OF vh g, of "\<not> lo"] ep by simp
  qed
  have env': "\<forall>(l, q) \<in> set ((lab, ?p0l) # env). successful T q" using "PSplit.prems"(2) s0l by simp
  have sr: "successful T ?pr" by (rule PSplit.IH(2)[OF cr env' fr])
  show ?case unfolding successful_def
  proof (intro allI impI notI)
    fix G :: "'a hypermap" and x assume vh: "valid_hub G x" and ep: "exact_fitp G x p"
    show False
    proof (cases "lo = fitc i j k G x")
      case True
      then have "exact_fitp G x ?pr" using fsplit[OF vh g, of "\<not> lo"] ep by simp
      then show False using sr vh by (simp add: successful_def)
    next
      case False
      then have "exact_fitp G x ?pl" using fsplit[OF vh g, of lo] ep by simp
      then show False using sl vh by (simp add: successful_def)
    qed
  qed
qed

theorem exclude_arity:
  assumes ck: "check_ps qt [] (pcons_any n) (pcons_any n) s" and vh: "valid_hub (G :: 'a hypermap) x"
  shows "arity G x \<noteq> n"
proof
  assume a: "arity G x = n"
  have m: "minimal_counter_example G" and xD: "x \<in> darts G" using vh by (simp_all add: valid_hub_def)
  interpret P: pcp G by (rule mce_pcp[OF m])
  have "successful T (pcons_any n)"
    by (rule soundness[OF ck]) (simp_all add: forced_part_def)
  moreover have "exact_fitp G x (pcons_any n)" using P.exact_fitp_pcons_any[OF P.pentaG xD] a by simp
  ultimately show False using vh by (simp add: successful_def)
qed

end

end
