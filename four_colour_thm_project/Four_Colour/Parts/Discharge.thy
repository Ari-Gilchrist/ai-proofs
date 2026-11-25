(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Discharge.thy
    The discharge rules and the discharge score (discharge.v).
    Ported from G. Gonthier's Coq development (discharge.v). The rule data was translated
    mechanically from discharge.v by tools/partsyn.py.
*)
theory Discharge
  imports Four_Colour_Parts.Mirror
begin

section \<open>The discharge rules\<close>
definition "drule1 = (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 (Pcons Pr69 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil)))))"
definition "drule2 = (Pcons Pr59 Pr59 (Pcons Pr55 Pr59 (Pcons Pr79 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil)))))"
definition "drule2p = (Pcons Pr59 Pr59 (Pcons Pr55 Pr59 (Pcons Pr79 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil))))))"
definition "drule3 = (Pcons Pr55 Pr59 (Pcons Pr56 Pr59 (Pcons Pr69 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil)))))"
definition "drule3p = (Pcons Pr55 Pr59 (Pcons Pr56 Pr59 (Pcons Pr69 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil))))))"
definition "drule4 = (Pcons Pr56 Pr59 (Pcons Pr55 Pr55 (Pcons Pr69 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil))))))"
definition "drule4p = (Pcons Pr56 Pr59 (Pcons Pr66 Pr55 (Pcons Pr69 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil))))))"
definition "drule5 = (Pcons Pr66 Pr59 (Pcons6 Pr56 Pr55 (Pcons Pr69 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil))))))"
definition "drule6 = (Pcons Pr66 Pr59 (Pcons Pr55 Pr56 (Pcons Pr79 Pr55 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil))))))"
definition "drule7 = (Pcons Pr66 Pr59 (Pcons6 Pr66 Pr56 (Pcons Pr79 Pr55 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil))))))"
definition "drule8 = (Pcons Pr55 Pr59 (Pcons Pr56 Pr59 (Pcons Pr79 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil)))))))"
definition "drule9 = (Pcons Pr56 Pr59 (Pcons Pr56 Pr59 (Pcons Pr79 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 (Pcons Pr55 Pr59 Pnil)))))))"
definition "drule10 = (Pcons Pr55 Pr59 (Pcons Pr55 Pr59 (Pcons Pr79 Pr59 (Pcons Pr55 Pr59 (Pcons Pr69 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil)))))))"
definition "drule10p = (Pcons Pr55 Pr59 (Pcons Pr55 Pr59 (Pcons Pr79 Pr59 (Pcons Pr55 Pr59 (Pcons Pr55 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil)))))))"
definition "drule11 = (Pcons Pr66 Pr59 (Pcons Pr55 Pr55 (Pcons Pr79 Pr59 (Pcons Pr55 Pr59 (Pcons Pr69 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil)))))))"
definition "drule12 = (Pcons Pr55 Pr59 (Pcons Pr55 Pr55 (Pcons Pr79 Pr59 (Pcons Pr55 Pr59 (Pcons Pr55 Pr55 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil)))))))"
definition "drule13 = (Pcons Pr66 Pr59 (Pcons Pr55 Pr55 (Pcons Pr89 Pr55 (Pcons Pr55 Pr59 (Pcons Pr55 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil)))))))"
definition "drule14 = (Pcons Pr55 Pr59 (Pcons Pr66 Pr55 (Pcons Pr79 Pr59 (Pcons Pr55 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil)))))))"
definition "drule15 = (Pcons Pr55 Pr59 (Pcons Pr66 Pr59 (Pcons Pr79 Pr59 (Pcons Pr55 Pr59 (Pcons Pr79 Pr59 (Pcons Pr55 Pr59 (Pcons Pr66 Pr59 Pnil)))))))"
definition "drule16 = (Pcons Pr66 Pr59 (Pcons Pr66 Pr59 (Pcons Pr79 Pr59 (Pcons Pr55 Pr59 (Pcons Pr55 Pr59 (Pcons Pr55 Pr59 (Pcons Pr66 Pr59 Pnil)))))))"
definition "drule17 = (Pcons Pr55 Pr59 (Pcons Pr66 Pr66 (Pcons Pr79 Pr59 (Pcons Pr55 Pr59 (Pcons Pr55 Pr59 (Pcons Pr79 Pr59 (Pcons Pr55 Pr59 Pnil)))))))"
definition "drule18 = (Pcons Pr66 Pr59 (Pcons Pr55 Pr55 (Pcons Pr77 Pr55 (Pcons Pr69 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 (Pcons Pr55 Pr59 Pnil)))))))"
definition "drule19 = (Pcons Pr66 Pr59 (Pcons Pr69 Pr59 (Pcons Pr89 Pr59 (Pcons Pr55 Pr55 (Pcons Pr66 Pr55 (Pcons Pr55 Pr59 (Pcons Pr66 Pr59 Pnil)))))))"
definition "drule20 = (Pcons Pr55 Pr59 (Pcons Pr66 Pr59 (Pcons Pr79 Pr59 (Pcons Pr66 Pr59 (Pcons Pr66 Pr59 (Pcons Pr55 Pr59 (Pcons Pr55 Pr59 Pnil)))))))"
definition "drule21 = (Pcons Pr56 Pr59 (Pcons Pr66 Pr59 (Pcons Pr77 Pr55 (Pcons Pr69 Pr59 (Pcons Pr59 Pr59 (Pcons Pr55 Pr59 (Pcons Pr55 Pr59 Pnil)))))))"
definition "drule22 = (Pcons Pr55 Pr59 (Pcons Pr66 Pr59 (Pcons Pr77 Pr55 (Pcons Pr69 Pr59 (Pcons Pr59 Pr59 (Pcons Pr55 Pr59 (Pcons Pr66 Pr59 Pnil)))))))"
definition "drule23 = (Pcons Pr55 Pr59 (Pcons Pr77 Pr55 (Pcons Pr79 Pr59 (Pcons Pr55 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil)))))))"
definition "drule24 = (Pcons Pr55 Pr59 (Pcons Pr55 Pr59 (Pcons Pr77 Pr55 (Pcons Pr79 Pr59 (Pcons Pr66 Pr59 (Pcons Pr66 Pr59 (Pcons Pr55 Pr59 Pnil)))))))"
definition "drule25 = (Pcons Pr55 Pr59 (Pcons Pr55 Pr59 (Pcons Pr79 Pr59 (Pcons7 Pr59 Pr59 Pr55 (Pcons Pr55 Pr66 (Pcons Pr55 Pr59 (Pcons Pr59 Pr59 Pnil)))))))"
definition "drule26 = (Pcons Pr66 Pr59 (Pcons Pr66 Pr59 (Pcons Pr77 Pr55 (Pcons Pr79 Pr59 (Pcons Pr55 Pr59 (Pcons Pr55 Pr59 (Pcons Pr66 Pr59 Pnil)))))))"
definition "drule27 = (Pcons Pr79 Pr59 (Pcons Pr66 Pr59 (Pcons7 Pr66 Pr55 Pr69 (Pcons Pr77 Pr59 (Pcons Pr56 Pr55 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil)))))))"
definition "drule28 = (Pcons Pr55 Pr59 (Pcons Pr55 Pr59 (Pcons Pr79 Pr59 (Pcons Pr55 Pr59 (Pcons Pr55 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 (Pcons Pr55 Pr59 Pnil))))))))"
definition "drule29 = (Pcons Pr55 Pr59 (Pcons Pr55 Pr55 (Pcons Pr79 Pr59 (Pcons Pr55 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 (Pcons Pr55 Pr59 (Pcons Pr55 Pr59 Pnil))))))))"
definition "drule30 = (Pcons Pr55 Pr59 (Pcons Pr55 Pr59 (Pcons Pr79 Pr59 (Pcons Pr55 Pr59 (Pcons Pr66 Pr55 (Pcons Pr55 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil))))))))"
definition "drule31 = (Pcons Pr55 Pr59 (Pcons Pr55 Pr55 (Pcons Pr79 Pr59 (Pcons Pr55 Pr59 (Pcons Pr55 Pr69 (Pcons Pr69 Pr59 (Pcons Pr59 Pr59 (Pcons Pr69 Pr59 Pnil))))))))"
definition "drule31p = (Pcons Pr55 Pr59 (Pcons Pr55 Pr55 (Pcons Pr79 Pr59 (Pcons Pr55 Pr59 (Pcons Pr55 Pr55 (Pcons Pr69 Pr59 (Pcons Pr59 Pr59 (Pcons Pr69 Pr59 Pnil))))))))"
definition "drule32 = (Pcons Pr55 Pr59 (Pcons Pr66 Pr59 (Pcons Pr77 Pr55 (Pcons Pr79 Pr59 (Pcons Pr66 Pr59 (Pcons Pr55 Pr59 (Pcons Pr55 Pr59 (Pcons Pr55 Pr59 Pnil))))))))"
definition base_drules :: "part list" where
  "base_drules = [drule1, drule1, drule2, drule2p, drule3, drule3p, drule4, drule4p, drule5, drule6, drule7, drule8, drule9, drule10, drule10p, drule11, drule12, drule13, drule14, drule15, drule16, drule17, drule18, drule19, drule20, drule21, drule22, drule23, drule24, drule25, drule26, drule27, drule28, drule29, drule30, drule31, drule31p, drule32]"

fun symmetrize_drules :: "part list \<Rightarrow> part list" where
  "symmetrize_drules [] = []"
| "symmetrize_drules (p # r) =
    (let p' = (rot_part (psize p - 1) ^^ 5) (mirror_part p); psr = p # symmetrize_drules r in
     if cmp_part p p' = Psubset then psr else p' # psr)"

definition the_drules :: "part list" where "the_drules = symmetrize_drules base_drules"

section \<open>Scores\<close>

definition dscore1 :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> int" where
  "dscore1 G x = int (length (filter (exact_fitp G (inv_face2 G x)) the_drules))"

definition dscore2 :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> int" where
  "dscore2 G x = dscore1 G (edge G x) - dscore1 G x"

definition dscore :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> int" where
  "dscore G x = 60 - 10 * int (arity G x) + (\<Sum>y \<in> cyc (face G) x. dscore2 G y)"

lemma (in hypermap) dscore_cface: "cface x y \<Longrightarrow> dscore G x = dscore G y"
  using arity_cface[of x y] F.cyc_eq_iff[of x y] by (simp add: dscore_def)

context hypermap
begin

lemma sum_dscore2: "(\<Sum>y \<in> D. dscore2 G y) = 0"
proof -
  have "(\<Sum>y \<in> D. dscore1 G (e y)) = (\<Sum>y \<in> D. dscore1 G y)"
    using sum.permute[OF edge_perm, of "dscore1 G"] by (simp add: comp_def)
  then show ?thesis by (simp add: dscore2_def sum_subtractf)
qed

lemma faces_partition:
  "(\<Sum>y \<in> D. h y) = (\<Sum>C \<in> cyc f ` D. \<Sum>y \<in> C. h y)"
proof -
  have U: "\<Union> (cyc f ` D) = D" using F.cyc_subset by auto
  have disj: "\<forall>A \<in> cyc f ` D. \<forall>B \<in> cyc f ` D. A \<noteq> B \<longrightarrow> A \<inter> B = {}"
  proof (intro ballI impI)
    fix A B assume "A \<in> cyc f ` D" "B \<in> cyc f ` D" "A \<noteq> B"
    then obtain a b where ab: "A = cyc f a" "B = cyc f b" by blast
    show "A \<inter> B = {}"
    proof (rule ccontr)
      assume "A \<inter> B \<noteq> {}"
      then obtain z where "z \<in> cyc f a" "z \<in> cyc f b" using ab by blast
      then have "fconnect f a z" "fconnect f b z" by (simp_all add: F.in_cyc_iff)
      then have "cyc f a = cyc f z" "cyc f b = cyc f z" by (simp_all add: F.cyc_eq)
      then show False using ab \<open>A \<noteq> B\<close> by simp
    qed
  qed
  have "sum h (\<Union> (cyc f ` D)) = sum (sum h) (cyc f ` D)"
    using sum.Union_disjoint[of "cyc f ` D" h] disj finite_darts
    by (auto simp: pairwise_def disjnt_def)
  then show ?thesis using U by simp
qed

lemma dscore_face_sum:
  assumes eul: "6 * fcard f D = card D + 12"
  shows "(\<Sum>C \<in> cyc f ` D. 60 - 10 * int (card C) + (\<Sum>y \<in> C. dscore2 G y)) = 120"
proof -
  have c: "(\<Sum>C \<in> cyc f ` D. int (card C)) = int (card D)"
    using faces_partition[of "\<lambda>_. (1::int)"] by simp
  have d: "(\<Sum>C \<in> cyc f ` D. \<Sum>y \<in> C. dscore2 G y) = 0"
    using faces_partition[of "dscore2 G"] sum_dscore2 by simp
  have "(\<Sum>C \<in> cyc f ` D. 60 - 10 * int (card C) + (\<Sum>y \<in> C. dscore2 G y)) =
      60 * int (card (cyc f ` D)) - 10 * int (card D)"
    using c d by (simp add: sum.distrib sum_subtractf sum_distrib_left[symmetric])
  also have "\<dots> = 120" using eul by (simp add: fcard_def)
  finally show ?thesis .
qed

theorem posz_dscore:
  assumes eul: "6 * fcard f D = card D + 12"
  shows "\<exists>x \<in> D. 0 < dscore G x"
proof (rule ccontr)
  assume "\<not> (\<exists>x \<in> D. 0 < dscore G x)"
  then have le: "\<And>x. x \<in> D \<Longrightarrow> dscore G x \<le> 0" by auto
  have "(\<Sum>C \<in> cyc f ` D. 60 - 10 * int (card C) + (\<Sum>y \<in> C. dscore2 G y)) \<le> 0"
  proof (rule sum_nonpos)
    fix C assume "C \<in> cyc f ` D"
    then obtain x where x: "x \<in> D" "C = cyc f x" by blast
    have "dscore G x = 60 - 10 * int (card C) + (\<Sum>y \<in> C. dscore2 G y)"
      using x by (simp add: dscore_def order_def)
    then show "60 - 10 * int (card C) + (\<Sum>y \<in> C. dscore2 G y) \<le> 0" using le[OF x(1)] by simp
  qed
  then show False using dscore_face_sum[OF eul] by simp
qed

end


section \<open>Score bounds\<close>

definition pick_source_drules :: "nat \<Rightarrow> part list" where
  "pick_source_drules nhub = filter (\<lambda>p. psize p = nhub) the_drules"

fun pick_target :: "nat \<Rightarrow> part list \<Rightarrow> part list" where
  "pick_target nhub [] = []"
| "pick_target nhub (p # r) =
    (case converse_part p of (u, p') \<Rightarrow> if mem_range u nhub then p' # pick_target nhub r else pick_target nhub r)"

definition pick_target_drules :: "nat \<Rightarrow> part list" where
  "pick_target_drules nhub = pick_target nhub the_drules"

fun sort_drules_rec :: "part \<Rightarrow> nat \<Rightarrow> part list \<Rightarrow> part list \<Rightarrow> nat \<times> part list" where
  "sort_drules_rec p n rs [] = (n, rs)"
| "sort_drules_rec p n rs (p' # r') = (case cmp_part p p' of
      Psubset \<Rightarrow> sort_drules_rec p (Suc n) rs r'
    | Pstraddle \<Rightarrow> sort_drules_rec p n (p' # rs) r'
    | Pdisjoint \<Rightarrow> sort_drules_rec p n rs r')"

definition sort_drules :: "part \<Rightarrow> part list \<Rightarrow> nat \<times> part list" where
  "sort_drules p r = sort_drules_rec p 0 [] r"

definition dbound1 :: "'a hypermap \<Rightarrow> part list \<Rightarrow> 'a \<Rightarrow> nat" where
  "dbound1 G r x = length (filter (fitp G x) r)"

definition dbound2 :: "'a hypermap \<Rightarrow> part list \<Rightarrow> part list \<Rightarrow> 'a \<Rightarrow> int" where
  "dbound2 G r r' x = int (dbound1 G r x) - int (dbound1 G r' x)"

definition dboundK :: "nat \<Rightarrow> int" where
  "dboundK nhub = (if nhub \<le> 5 then 10 else - int ((nhub - 6) * 10))"

lemma sort_drules_rec_eq:
  "fitp G x p \<Longrightarrow> sort_drules_rec p n rs ru = (n', rs') \<Longrightarrow>
   n + dbound1 G rs x + dbound1 G ru x = n' + dbound1 G rs' x"
proof (induction p n rs ru rule: sort_drules_rec.induct)
  case (1 p n rs) then show ?case by (simp add: dbound1_def)
next
  case (2 p n rs p' r')
  have rel: "rel_ok (cmp_part p p') (fitp G x p')" by (rule fitp_cmp[OF "2.prems"(1)])
  show ?case
  proof (cases "cmp_part p p'")
    case Pdisjoint
    then have "\<not> fitp G x p'" using rel by (simp add: rel_ok_def)
    have sr: "sort_drules_rec p n rs r' = (n', rs')" using "2.prems"(2) Pdisjoint by simp
    then show ?thesis using "2.IH"(1)[OF Pdisjoint "2.prems"(1) sr] \<open>\<not> fitp G x p'\<close> by (simp add: dbound1_def)
  next
    case Pstraddle
    have sr: "sort_drules_rec p n (p' # rs) r' = (n', rs')" using "2.prems"(2) Pstraddle by simp
    then show ?thesis using "2.IH"(2)[OF Pstraddle "2.prems"(1) sr] Pstraddle "2.prems"(2) by (cases "fitp G x p'") (simp_all add: dbound1_def)
  next
    case Psubset
    then have "fitp G x p'" using rel by (simp add: rel_ok_def)
    have sr: "sort_drules_rec p (Suc n) rs r' = (n', rs')" using "2.prems"(2) Psubset by simp
    then show ?thesis using "2.IH"(3)[OF Psubset "2.prems"(1) sr] \<open>fitp G x p'\<close> by (simp add: dbound1_def)
  qed
qed

lemma sort_dbound1_eq:
  "fitp G x p \<Longrightarrow> sort_drules p ru = (n, rs) \<Longrightarrow> dbound1 G ru x = n + dbound1 G rs x"
  using sort_drules_rec_eq[of G x p 0 "[]" ru n rs] by (simp add: sort_drules_def dbound1_def)

context pcp
begin

lemma inv_face2_ff [simp]: "inv_face2 G (f (f x)) = x" by (simp add: inv_face2_def)

lemma ff_inv_face2 [simp]: "f (f (inv_face2 G z)) = z" by (simp add: inv_face2_def)

lemma dbound1_eq:
  assumes nFx: "arity G x = nhub"
  shows "dscore1 G (f (f x)) = int (dbound1 G (pick_source_drules nhub) x)"
proof -
  have "filter (exact_fitp G x) the_drules = filter (fitp G x) (filter (\<lambda>p. psize p = nhub) the_drules)"
    using nFx by (auto simp: exact_fitp_def filter_filter intro!: filter_cong)
  then show ?thesis by (simp add: dscore1_def dbound1_def pick_source_drules_def)
qed

lemma count_target:
  assumes yD: "y \<in> D" and xy: "inv_face2 G (e (f (f y))) = x"
  shows "length (filter (exact_fitp G y) r) \<le> length (filter (fitp G x) (pick_target (arity G x) r))"
proof (induction r)
  case Nil then show ?case by simp
next
  case (Cons p r)
  obtain u p' where c: "converse_part p = (u, p')" by fastforce
  show ?case
  proof (cases "exact_fitp G y p")
    case True
    have "tight_fitp G x (u, p')" using fitp_converse[OF yD True] c xy by simp
    then have "mem_range u (arity G x)" "fitp G x p'" by (simp_all add: tight_fitp_def)
    then show ?thesis using Cons c True by simp
  next
    case False
    then show ?thesis using Cons c by (auto simp: Let_def)
  qed
qed

lemma dbound2_leq:
  assumes xD: "x \<in> D" and nFx: "arity G x = nhub"
  shows "dscore2 G (f (f x)) \<le> dbound2 G (pick_target_drules nhub) (pick_source_drules nhub) x"
proof -
  let ?y = "inv_face2 G (e (f (f x)))"
  have yD: "?y \<in> D" using xD by (simp add: inv_face2_def)
  have "inv_face2 G (e (f (f ?y))) = x" by simp
  then have "length (filter (exact_fitp G ?y) the_drules) \<le> length (filter (fitp G x) (pick_target nhub the_drules))"
    using count_target[OF yD, of x the_drules] nFx by simp
  then have "dscore1 G (e (f (f x))) \<le> int (dbound1 G (pick_target_drules nhub) x)"
    by (simp add: dscore1_def dbound1_def pick_target_drules_def)
  then show ?thesis using dbound1_eq[OF nFx] by (simp add: dscore2_def dbound2_def)
qed

lemma dboundK_eq: "arity G x = nhub \<Longrightarrow> x \<in> D \<Longrightarrow> dboundK nhub = 60 - 10 * int (arity G x)"
  using pentaG[of x] by (auto simp: dboundK_def)

lemma dscore1_ge0: "0 \<le> dscore1 G y" by (simp add: dscore1_def)

lemma dscore_cap1:
  assumes ub: "\<And>y. y \<in> D \<Longrightarrow> dscore1 G y \<le> int m" and xD: "x \<in> D" and pos: "0 < dscore G x"
    and big: "59 < (10 - m) * d"
  shows "arity G x < d"
proof (rule ccontr)
  assume "\<not> arity G x < d"
  then have ad: "d \<le> arity G x" by simp
  have m10: "m < 10" using big by (cases "10 - m") auto
  let ?C = "cyc f x"
  have cD: "?C \<subseteq> D" using F.cyc_subset[OF xD] .
  have "(\<Sum>y \<in> ?C. dscore2 G y) \<le> (\<Sum>y \<in> ?C. int m)"
  proof (rule sum_mono)
    fix y assume "y \<in> ?C"
    then have "e y \<in> D" using cD by auto
    then show "dscore2 G y \<le> int m" using ub[of "e y"] dscore1_ge0[of y] by (simp add: dscore2_def)
  qed
  also have "\<dots> = int m * int (arity G x)" by (simp add: order_def)
  finally have "dscore G x \<le> 60 - 10 * int (arity G x) + int m * int (arity G x)"
    by (simp add: dscore_def)
  also have "\<dots> = 60 - int (10 - m) * int (arity G x)" using m10 by (simp add: algebra_simps of_nat_diff)
  also have "\<dots> \<le> 60 - int (10 - m) * int d" using ad by (simp add: mult_left_mono)
  also have "\<dots> \<le> 0"
  proof -
    have "60 \<le> (10 - m) * d" using big by simp
    then have "60 \<le> int ((10 - m) * d)" by linarith
    then show ?thesis by (simp only: of_nat_mult)
  qed
  finally show False using pos by simp
qed

lemma ff_bij: "bij_betw (\<lambda>y. f (f y)) (cyc f x) (cyc f x)"
proof -
  have "inj (\<lambda>y. f (f y))" using F.inj by (auto simp: inj_def)
  moreover have "(\<lambda>y. f (f y)) ` cyc f x = cyc f x"
  proof
    show "(\<lambda>y. f (f y)) ` cyc f x \<subseteq> cyc f x" by (auto simp: F.in_cyc_iff intro: fconnect_stepI_r)
    show "cyc f x \<subseteq> (\<lambda>y. f (f y)) ` cyc f x"
    proof
      fix z assume z: "z \<in> cyc f x"
      have "z = f (f (inv_face2 G z))" by simp
      moreover have "inv_face2 G z \<in> cyc f x"
      proof -
        have "fconnect f (inv_face2 G z) z" using fconnect_funpow[of f "inv_face2 G z" 2]
          by (simp add: eval_nat_numeral)
        then show ?thesis using z by (auto simp: F.in_cyc_iff intro: fconnect_trans F.fconnect_sym)
      qed
      ultimately show "z \<in> (\<lambda>y. f (f y)) ` cyc f x" by blast
    qed
  qed
  ultimately show ?thesis by (simp add: bij_betw_def inj_on_subset[of _ UNIV])
qed

lemma dscore_cap2:
  assumes xD: "x \<in> D" and nFx: "arity G x = nhub" and pos: "0 < dscore G x"
  shows "0 < dboundK nhub + (\<Sum>y \<in> cyc f x. dbound2 G (pick_target_drules nhub) (pick_source_drules nhub) y)"
proof -
  have "(\<Sum>y \<in> cyc f x. dscore2 G y) = (\<Sum>y \<in> cyc f x. dscore2 G (f (f y)))"
    using sum.reindex_bij_betw[OF ff_bij[of x], of "dscore2 G"] by simp
  also have "\<dots> \<le> (\<Sum>y \<in> cyc f x. dbound2 G (pick_target_drules nhub) (pick_source_drules nhub) y)"
  proof (rule sum_mono)
    fix y assume y: "y \<in> cyc f x"
    then have yD: "y \<in> D" using F.cyc_subset[OF xD] by blast
    have "arity G y = nhub" using y nFx arity_cface[of x y] by (simp add: F.in_cyc_iff)
    then show "dscore2 G (f (f y)) \<le> dbound2 G (pick_target_drules nhub) (pick_source_drules nhub) y"
      by (rule dbound2_leq[OF yD])
  qed
  finally show ?thesis using pos dboundK_eq[OF nFx xD] by (simp add: dscore_def)
qed

end


section \<open>Mirror invariance of the score\<close>

lemma plist_inj: "plist p = plist q \<Longrightarrow> p = q"
proof (induction p arbitrary: q)
  case Pnil then show ?case by (cases q) simp_all
next
  case (Pcons s h p) then show ?case by (cases q) simp_all
next
  case (Pcons6 h a p) then show ?case by (cases q) simp_all
next
  case (Pcons7 h a b p) then show ?case by (cases q) simp_all
next
  case (Pcons8 h a b c p) then show ?case by (cases q) simp_all
qed

lemma nmir_nsethat [simp]: "nmir (nsethat h c) = nsethat h (nmir c)" by (cases c) simp_all
lemma nsethat_nsethat [simp]: "nsethat h (nsethat h' c) = nsethat h c" by (cases c) simp_all
lemma nsethat_nhat [simp]: "nsethat (nhat c) c = c" by (cases c) simp_all

lemma mirror_nth:
  assumes pne: "p \<noteq> Pnil" and i: "i < psize p"
  shows "plist (mirror_part p) ! i =
    nsethat (nhat (plist p ! ((psize p - i) mod psize p))) (nmir (plist p ! (psize p - 1 - i)))"
proof -
  let ?l = "plist p" and ?m = "psize p"
  have lm: "length ?l = ?m" by (simp add: length_plist)
  have h0: "get_hat p = nhat (?l ! 0)" by (rule get_hat_plist[OF pne])
  have "plist (mirror_part p) ! i = mhats (get_hat p) ?l ! (?m - 1 - i)"
    using i lm by (simp add: plist_mirror rev_nth)
  also have "\<dots> = nsethat (if Suc (?m - 1 - i) < ?m then nhat (?l ! Suc (?m - 1 - i)) else get_hat p)
      (nmir (?l ! (?m - 1 - i)))" using mhats_nth[of "?m - 1 - i" ?l] i lm by simp
  also have "(if Suc (?m - 1 - i) < ?m then nhat (?l ! Suc (?m - 1 - i)) else get_hat p) =
      nhat (?l ! ((?m - i) mod ?m))"
  proof (cases i)
    case 0 then show ?thesis using i h0 by simp
  next
    case (Suc j)
    then have "Suc (?m - 1 - i) = ?m - i" "Suc (?m - 1 - i) < ?m" "(?m - i) mod ?m = ?m - i" using i by auto
    then show ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma mirror_mirror_part: "mirror_part (mirror_part p) = p"
proof (cases "p = Pnil")
  case True then show ?thesis by (simp add: mirror_part_def)
next
  case pne: False
  let ?m = "psize p" and ?l = "plist p"
  have m0: "0 < ?m" using pne by (cases p) simp_all
  have szm: "psize (mirror_part p) = ?m" by (rule psize_mirror)
  have mne: "mirror_part p \<noteq> Pnil" using szm m0 by auto
  show ?thesis
  proof (rule plist_inj, rule nth_equalityI)
    show "length (plist (mirror_part (mirror_part p))) = length (plist p)"
      by (simp add: length_plist psize_mirror)
    fix i assume "i < length (plist (mirror_part (mirror_part p)))"
    then have i: "i < ?m" by (simp add: length_plist psize_mirror)
    have a: "plist (mirror_part (mirror_part p)) ! i =
      nsethat (nhat (plist (mirror_part p) ! ((?m - i) mod ?m))) (nmir (plist (mirror_part p) ! (?m - 1 - i)))"
      using mirror_nth[OF mne, of i] szm i by simp
    have j: "(?m - i) mod ?m < ?m" "?m - 1 - i < ?m" using m0 i by auto
    have b: "plist (mirror_part p) ! (?m - 1 - i) =
      nsethat (nhat (?l ! ((?m - (?m - 1 - i)) mod ?m))) (nmir (?l ! i))"
      using mirror_nth[OF pne j(2)] i by simp
    have c: "nhat (plist (mirror_part p) ! ((?m - i) mod ?m)) = nhat (?l ! i)"
    proof -
      have "plist (mirror_part p) ! ((?m - i) mod ?m) =
          nsethat (nhat (?l ! ((?m - (?m - i) mod ?m) mod ?m))) (nmir (?l ! (?m - 1 - (?m - i) mod ?m)))"
        by (rule mirror_nth[OF pne j(1)])
      moreover have "(?m - (?m - i) mod ?m) mod ?m = i" using i by (cases i) auto
      ultimately show ?thesis by simp
    qed
    show "plist (mirror_part (mirror_part p)) ! i = plist p ! i" using a b c by simp
  qed
qed

context hypermap
begin

lemma mirror_mirror: "mirror (mirror G) = G"
proof -
  have "inv (inv n) = n" using N.bij by (simp add: inv_inv_eq)
  moreover have "inv (inv f) = f" using F.bij by (simp add: inv_inv_eq)
  moreover have "inv f \<circ> inv n = e"
  proof -
    have "(n \<circ> f) \<circ> e = id" by (simp add: fun_eq_iff edgeK)
    then have "inv (n \<circ> f) = e" using N.bij F.bij
      by (metis bij_comp inv_unique_comp edgeK comp_apply fun_eq_iff id_apply faceK)
    moreover have "inv (n \<circ> f) = inv f \<circ> inv n" using N.bij F.bij by (simp add: o_inv_distrib)
    ultimately show ?thesis by simp
  qed
  ultimately show ?thesis by (simp add: mirror_def)
qed

end

context pcp
begin

lemma cubic_mirror: "cubic (mirror G)"
  using cubicG by (simp add: cubic_def cubicb_def N.order_inv)

lemma pcp_mirror: "pcp (mirror G)"
proof -
  interpret M: hypermap "mirror G" by (rule hypermap_mirror)
  show ?thesis
    by unfold_locales (use plainG plain_mirror cubic_mirror pentaG in \<open>simp_all add: F.order_inv\<close>)
qed

lemma inv_face2_mirror: "inv_face2 (mirror G) z = f (f z)"
proof -
  have "inv n w = n (n w)" for w using N.inv_f[of "n (n w)"] nnn[of w] by simp
  then show ?thesis by (simp add: inv_face2_def f_ne)
qed

lemma rot_back:
  assumes zD: "z \<in> D" and sz: "psize q = arity G z" and q0: "0 < psize q"
  shows "exact_fitp G z (rot_part (psize q - 1) q) \<longleftrightarrow> exact_fitp G (f z) q"
proof -
  have "exact_fitp G (f z) q \<longleftrightarrow> exact_fitp G ((f ^^ (psize q - 1)) (f z)) (rot_part (psize q - 1) q)"
    by (rule fitp_rot) simp
  also have "(f ^^ (psize q - 1)) (f z) = z"
  proof -
    have "(f ^^ (psize q - 1)) (f z) = (f ^^ Suc (psize q - 1)) z" by (simp add: funpow_Suc_right del: funpow.simps)
    also have "Suc (psize q - 1) = arity G z" using sz q0 by simp
    finally show ?thesis using iter_arity by simp
  qed
  finally show ?thesis ..
qed

lemma rot_iter:
  assumes q0: "0 < psize q"
  shows "z \<in> D \<Longrightarrow> exact_fitp G z (((rot_part (psize q - 1)) ^^ k) q) \<longleftrightarrow> exact_fitp G ((f ^^ k) z) q"
proof (induction k arbitrary: z)
  case 0 then show ?case by simp
next
  case (Suc k)
  have szk: "psize (((rot_part (psize q - 1)) ^^ k) q) = psize q" by (induction k) (simp_all add: psize_rot)
  show ?case
  proof (cases "psize q = arity G z")
    case True
    let ?Q = "((rot_part (psize q - 1)) ^^ k) q"
    have r: "exact_fitp G z (rot_part (psize ?Q - 1) ?Q) \<longleftrightarrow> exact_fitp G (f z) ?Q"
      by (rule rot_back) (use Suc.prems szk True q0 in simp_all)
    have "exact_fitp G z (rot_part (psize q - 1) (((rot_part (psize q - 1)) ^^ k) q)) \<longleftrightarrow>
        exact_fitp G (f z) (((rot_part (psize q - 1)) ^^ k) q)"
      using r unfolding szk .
    also have "\<dots> \<longleftrightarrow> exact_fitp G ((f ^^ k) (f z)) q" by (rule Suc.IH) (use Suc.prems in simp)
    finally show ?thesis by (simp add: funpow_swap1)
  next
    case False
    have "psize (rot_part (psize q - 1) (((rot_part (psize q - 1)) ^^ k) q)) = psize q" using szk by (simp add: psize_rot)
    then show ?thesis using False by (simp add: exact_fitp_def)
  qed
qed

end


context pcp
begin

interpretation M: pcp "mirror G" by (rule pcp_mirror)

lemma inv_f_pow: "((inv f) ^^ k) ((f ^^ k) z) = z"
proof (induction k)
  case 0 then show ?case by simp
next
  case (Suc k)
  have a1: "(f ^^ Suc k) z = f ((f ^^ k) z)" by simp
  have a2: "((inv f) ^^ Suc k) w = ((inv f) ^^ k) (inv f w)" for w
    by (simp only: funpow_Suc_right comp_apply)
  have "((inv f) ^^ Suc k) ((f ^^ Suc k) z) = ((inv f) ^^ k) (inv f (f ((f ^^ k) z)))"
    unfolding a1 a2 ..
  also have "\<dots> = ((inv f) ^^ k) ((f ^^ k) z)" by simp
  finally show ?case using Suc.IH by simp
qed

lemma mirror_pair:
  assumes xD: "x \<in> D" and p0: "0 < psize p"
  defines "p1 \<equiv> (rot_part (psize p - 1) ^^ 5) (mirror_part p)"
  shows "exact_fitp (mirror G) (f (f (f x))) p1 \<longleftrightarrow> exact_fitp G (inv_face2 G x) p"
    and "exact_fitp G (inv_face2 G x) p1 \<longleftrightarrow> exact_fitp (mirror G) (f (f (f x))) p"
proof -
  let ?w = "inv_face2 G x" and ?z = "f (f (f x))"
  have wD: "?w \<in> D" and zD: "?z \<in> D" using xD by (simp_all add: inv_face2_def)
  have zM: "?z \<in> darts (mirror G)" using zD by simp
  have m0: "0 < psize (mirror_part p)" using p0 by (simp add: psize_mirror)
  have pm: "psize (mirror_part p) - 1 = psize p - 1" by (simp add: psize_mirror)
  have fw: "(f ^^ 5) ?w = ?z"
  proof -
    have "(f ^^ 5) ?w = f (f (f (f (f ?w))))" by (simp add: eval_nat_numeral)
    then show ?thesis by simp
  qed
  have iw: "((inv f) ^^ 5) ?z = ?w"
  proof -
    have "?z = (f ^^ 5) ?w" using fw by simp
    then show ?thesis using inv_f_pow[of 5 ?w] by simp
  qed
  show "exact_fitp (mirror G) ?z p1 \<longleftrightarrow> exact_fitp G ?w p"
  proof -
    have "exact_fitp (mirror G) ?z p1 \<longleftrightarrow> exact_fitp (mirror G) (((inv f) ^^ 5) ?z) (mirror_part p)"
      using M.rot_iter[OF m0 zM, of 5] by (simp add: p1_def psize_mirror)
    also have "\<dots> \<longleftrightarrow> exact_fitp G ?w p" using iw exact_fitp_mirror[OF wD] by simp
    finally show ?thesis .
  qed
  show "exact_fitp G ?w p1 \<longleftrightarrow> exact_fitp (mirror G) ?z p"
  proof -
    have "exact_fitp G ?w p1 \<longleftrightarrow> exact_fitp G ((f ^^ 5) ?w) (mirror_part p)"
      using rot_iter[OF m0 wD, of 5] by (simp add: p1_def psize_mirror)
    also have "\<dots> \<longleftrightarrow> exact_fitp (mirror (mirror G)) ?z (mirror_part p)" using fw by (simp add: mirror_mirror)
    also have "\<dots> \<longleftrightarrow> exact_fitp (mirror G) ?z p" using M.exact_fitp_mirror zD by simp
    finally show ?thesis .
  qed
qed

lemma subset_fit: "cmp_part p q = Psubset \<Longrightarrow> psize p = psize q \<Longrightarrow> exact_fitp H z p \<Longrightarrow> exact_fitp H z q"
  using fitp_cmp[of H z p q] by (auto simp: exact_fitp_def rel_ok_def)

lemma count_mirror:
  assumes xD: "x \<in> D" and r0: "\<forall>p \<in> set r. 0 < psize p"
  shows "length (filter (exact_fitp (mirror G) (f (f (f x)))) (symmetrize_drules r)) =
         length (filter (exact_fitp G (inv_face2 G x)) (symmetrize_drules r))"
  using r0
proof (induction r)
  case Nil then show ?case by simp
next
  case (Cons p r)
  let ?p1 = "(rot_part (psize p - 1) ^^ 5) (mirror_part p)"
  let ?F' = "exact_fitp (mirror G) (f (f (f x)))" and ?F = "exact_fitp G (inv_face2 G x)"
  have p0: "0 < psize p" using Cons.prems by simp
  have IH: "length (filter ?F' (symmetrize_drules r)) = length (filter ?F (symmetrize_drules r))"
    using Cons by simp
  note mp = mirror_pair[OF xD p0]
  have sz1: "psize ?p1 = psize p"
  proof -
    have "psize ((rot_part (psize p - 1) ^^ k) (mirror_part p)) = psize p" for k
      by (induction k) (simp_all add: psize_rot psize_mirror)
    then show ?thesis .
  qed
  show ?case
  proof (cases "cmp_part p ?p1 = Psubset")
    case True
    have "?F' p \<longleftrightarrow> ?F p"
    proof
      assume "?F' p"
      then have "?F' ?p1" by (rule subset_fit[OF True sz1[symmetric]])
      then show "?F p" using mp(1) by simp
    next
      assume "?F p"
      then have "?F ?p1" by (rule subset_fit[OF True sz1[symmetric]])
      then show "?F' p" using mp(2) by simp
    qed
    then show ?thesis using True IH by (simp add: Let_def)
  next
    case False
    then show ?thesis using IH mp by (simp add: Let_def)
  qed
qed

lemma base_drules_pos: "\<forall>p \<in> set base_drules. 0 < psize p"
  by eval

lemma score1F: "x \<in> D \<Longrightarrow> dscore1 (mirror G) (f x) = dscore1 G x"
  using count_mirror[OF _ base_drules_pos, of x]
  by (simp add: dscore1_def the_drules_def inv_face2_mirror)

lemma f_bij_cyc: "bij_betw f (cyc f x) (cyc f x)"
proof -
  have "f ` cyc f x = cyc f x"
  proof
    show "f ` cyc f x \<subseteq> cyc f x" by (auto simp: F.in_cyc_iff intro: fconnect_stepI_r)
    show "cyc f x \<subseteq> f ` cyc f x"
    proof
      fix z assume z: "z \<in> cyc f x"
      have "z = f (inv f z)" by simp
      moreover have "inv f z \<in> cyc f x"
        using z F.cyc_inv[of z] by (metis F.cyc_eq_iff F.in_cyc_iff F.x_in_cyc fconnect_stepI_r F.f_inv F.fconnect_sym)
      ultimately show "z \<in> f ` cyc f x" by blast
    qed
  qed
  then show ?thesis using F.inj by (simp add: bij_betw_def inj_on_subset[of _ UNIV])
qed

theorem dscore_mirror:
  assumes xD: "x \<in> D"
  shows "dscore (mirror G) x = dscore G x"
proof -
  let ?C = "cyc f x"
  have cD: "?C \<subseteq> D" using F.cyc_subset[OF xD] .
  have "(\<Sum>y \<in> ?C. dscore2 (mirror G) y) = (\<Sum>y \<in> ?C. dscore2 (mirror G) (f y))"
    using sum.reindex_bij_betw[OF f_bij_cyc[of x], of "dscore2 (mirror G)"] by simp
  also have "\<dots> = (\<Sum>y \<in> ?C. dscore2 G y)"
  proof (rule sum.cong[OF refl])
    fix y assume "y \<in> ?C"
    then have yD: "y \<in> D" using cD by blast
    have "dscore2 (mirror G) (f y) = dscore1 (mirror G) (f (e y)) - dscore1 (mirror G) (f y)"
      by (simp add: dscore2_def)
    then show "dscore2 (mirror G) (f y) = dscore2 G y"
      using score1F[OF yD] score1F[of "e y"] yD by (simp add: dscore2_def)
  qed
  finally show ?thesis by (simp add: dscore_def F.order_inv F.cyc_inv)
qed

end

end
