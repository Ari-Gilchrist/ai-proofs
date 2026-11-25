(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Hubcap.thy
    Hubcaps: certificates bounding the discharged score of a hub (hubcap.v).
    Ported from G. Gonthier's Coq development (hubcap.v).
*)
theory Hubcap
  imports Discharge
begin

datatype hubcap = Hubcap0 | Hubcap1 nat int hubcap | Hubcap2 nat nat int hubcap

section \<open>Checking score bounds\<close>

fun check_dbound1_rec :: "(part \<Rightarrow> bool) \<Rightarrow> part \<Rightarrow> part list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "check_dbound1_rec redp p rs ns 0 = False"
| "check_dbound1_rec redp p [] ns (Suc m) = True"
| "check_dbound1_rec redp p (r # rs') ns (Suc m) =
    (if length rs' < ns then True else
     (let p' = meet_part p r in
      (case sort_drules p' rs' of (dns, rs'') \<Rightarrow>
        if ns - dns = 0 then redp p' else check_dbound1_rec redp p' rs'' (ns - dns - 1) m))
     \<and> check_dbound1_rec redp p rs' ns m)"

definition check_dbound1 :: "nat \<Rightarrow> (part \<Rightarrow> bool) \<Rightarrow> part \<Rightarrow> nat \<Rightarrow> bool" where
  "check_dbound1 nhub redp p ns =
     (let rs = pick_source_drules nhub in check_dbound1_rec redp p rs ns (length rs + 1))"

fun check_unfit :: "part \<Rightarrow> part list \<Rightarrow> bool" where
  "check_unfit p [] = False"
| "check_unfit p (r # ru') = (cmp_part p r = Psubset \<or> check_unfit p ru')"

fun check_dbound2_rec :: "(part \<Rightarrow> bool) \<Rightarrow> part \<Rightarrow> part list \<Rightarrow> part list \<Rightarrow> part list \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> bool" where
  "check_dbound2_rec redp p rt rs ru nt 0 = False"
| "check_dbound2_rec redp p [] rs ru nt (Suc m) = True"
| "check_dbound2_rec redp p (r # rt') rs ru nt (Suc m) =
    (if length rt' < nt then True else
     (let p' = meet_part p r in
      (check_unfit p' ru \<or>
        (case sort_drules p' rt' of (dnt, rt'') \<Rightarrow>
         case sort_drules p' rs of (dns, rs') \<Rightarrow>
         if dns + nt - dnt = 0 then redp p' else check_dbound2_rec redp p' rt'' rs' ru (dns + nt - dnt - 1) m))
     \<and> check_dbound2_rec redp p rt' rs (r # ru) nt m))"

definition check_dbound2 :: "nat \<Rightarrow> (part \<Rightarrow> bool) \<Rightarrow> part \<Rightarrow> int \<Rightarrow> bool" where
  "check_dbound2 nhub redp p b =
    (case sort_drules p (pick_target_drules nhub) of (dnt, rt') \<Rightarrow>
     case sort_drules p (pick_source_drules nhub) of (dns, rs') \<Rightarrow>
     let bb = int dns - int dnt + b in
     0 \<le> bb \<and> check_dbound2_rec redp p rt' rs' [] (nat bb) (length rt' + 2))"

fun check_2dbound2_rec :: "nat \<Rightarrow> (part \<Rightarrow> bool) \<Rightarrow> part \<Rightarrow> part \<Rightarrow> part list \<Rightarrow> part list \<Rightarrow> part list \<Rightarrow>
    part list \<Rightarrow> part list \<Rightarrow> part list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "check_2dbound2_rec nhub redp p1 p2 rt1 rs1 ru1 rt2 rs2 ru2 i nt 0 = False"
| "check_2dbound2_rec nhub redp p1 p2 [] rs1 ru1 rt2 rs2 ru2 i nt (Suc m) =
    (rt2 = [] \<or> check_2dbound2_rec nhub redp p2 p1 rt2 rs2 ru2 [] rs1 ru1 (nhub - i) nt m)"
| "check_2dbound2_rec nhub redp p1 p2 (r # rt1') rs1 ru1 rt2 rs2 ru2 i nt (Suc m) =
    (if length rt1' + length rt2 < nt then True else
     (let p1' = meet_part p1 r; p2' = rot_part i p1' in
      (check_unfit p1' ru1 \<or> check_unfit p2' ru2 \<or>
        (case sort_drules p1' rt1' of (dnt1, rt1'') \<Rightarrow>
         case sort_drules p1' rs1 of (dns1, rs1') \<Rightarrow>
         case sort_drules p2' rt2 of (dnt2, rt2') \<Rightarrow>
         case sort_drules p2' rs2 of (dns2, rs2') \<Rightarrow>
         if dns1 + (dns2 + nt) - (dnt1 + dnt2) = 0 then redp p1'
         else check_2dbound2_rec nhub redp p1' p2' rt1'' rs1' ru1 rt2' rs2' ru2 i
                (dns1 + (dns2 + nt) - (dnt1 + dnt2) - 1) m))
     \<and> check_2dbound2_rec nhub redp p1 p2 rt1' rs1 (r # ru1) rt2 rs2 ru2 i nt m))"

definition check_2dbound2 :: "nat \<Rightarrow> (part \<Rightarrow> bool) \<Rightarrow> part \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> bool" where
  "check_2dbound2 nhub redp p1 i b =
    (let p2 = rot_part i p1; rs = pick_source_drules nhub; rt = pick_target_drules nhub in
     case sort_drules p1 rt of (dnt1, rt1) \<Rightarrow>
     case sort_drules p1 rs of (dns1, rs1) \<Rightarrow>
     case sort_drules p2 rt of (dnt2, rt2) \<Rightarrow>
     case sort_drules p2 rs of (dns2, rs2) \<Rightarrow>
     let bb = int (dns1 + dns2) - int (dnt1 + dnt2) + b in
     0 \<le> bb \<and> check_2dbound2_rec nhub redp p1 p2 rt1 rs1 [] rt2 rs2 [] i (nat bb)
                (length rt1 + (length rt2 + 3)))"

section \<open>Soundness of the bound checks\<close>

lemma check_unfitP: "fitp G x p \<Longrightarrow> dbound1 G ru x = 0 \<Longrightarrow> \<not> check_unfit p ru"
proof (induction ru)
  case Nil then show ?case by simp
next
  case (Cons r ru)
  have nr: "\<not> fitp G x r" and z: "dbound1 G ru x = 0" using Cons.prems(2) by (auto simp: dbound1_def split: if_splits)
  have "cmp_part p r \<noteq> Psubset" using fitp_cmp[OF Cons.prems(1), of r] nr by (auto simp: rel_ok_def)
  then show ?case using Cons.IH[OF Cons.prems(1) z] by simp
qed


section \<open>Hubcap certificates\<close>

definition nth0 :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "nth0 v i = (if i < length v then v ! i else 0)"

definition incr_nth :: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "incr_nth v i = (if i < length v then v[i := Suc (v ! i)] else v @ replicate (i - length v) 0 @ [1])"

lemma nth0_incr: "nth0 (incr_nth v j) i = nth0 v i + (if i = j then 1 else 0)"
  by (auto simp: nth0_def incr_nth_def nth_append nth_list_update)

lemma length_incr: "length (incr_nth v j) = max (length v) (Suc j)"
  by (simp add: incr_nth_def)

fun tally_hubcap :: "hubcap \<Rightarrow> nat list" where
  "tally_hubcap (Hubcap1 i _ hc') = incr_nth (tally_hubcap hc') i"
| "tally_hubcap (Hubcap2 i j _ hc') = incr_nth (incr_nth (tally_hubcap hc') i) j"
| "tally_hubcap Hubcap0 = []"

fun hubcap_cover_rec :: "nat list \<Rightarrow> int \<Rightarrow> hubcap \<Rightarrow> bool" where
  "hubcap_cover_rec v b (Hubcap1 i b' hc') = (nth0 v i = 1 \<and> hubcap_cover_rec v (2 * b' + b) hc')"
| "hubcap_cover_rec v b (Hubcap2 i j b' hc') =
     (nth0 v i = nth0 v j \<and> nth0 v i \<le> 2 \<and>
      hubcap_cover_rec v (b' * (if nth0 v i = 1 then 2 else 1) + b) hc')"
| "hubcap_cover_rec v b Hubcap0 = (\<not> 0 < b)"

definition hubcap_cover :: "nat \<Rightarrow> hubcap \<Rightarrow> bool" where
  "hubcap_cover nhub hc = (let b = 2 * dboundK nhub - 1; v = tally_hubcap hc in
     length v = nhub \<and> 0 \<notin> set v \<and> hubcap_cover_rec v b hc)"

definition hubcap_rot :: "nat \<Rightarrow> nat \<Rightarrow> part \<Rightarrow> part" where
  "hubcap_rot nhub j = rot_part (if 2 \<le> j then j - 2 else nhub + j - 2)"

definition hub_subn :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "hub_subn nhub i j = (if j \<le> i then i else i + nhub) - j"

fun hubcap_fit :: "nat \<Rightarrow> (part \<Rightarrow> bool) \<Rightarrow> part \<Rightarrow> hubcap \<Rightarrow> bool" where
  "hubcap_fit nhub redp p (Hubcap1 j b hc') = (check_dbound2 nhub redp (hubcap_rot nhub j p) b \<and> hubcap_fit nhub redp p hc')"
| "hubcap_fit nhub redp p (Hubcap2 j1 j2 b hc') =
     (check_2dbound2 nhub redp (hubcap_rot nhub j1 p) (hub_subn nhub j2 j1) b \<and> hubcap_fit nhub redp p hc')"
| "hubcap_fit nhub redp p Hubcap0 = True"

text \<open>Weighted sums over a hubcap.\<close>

fun hB :: "nat list \<Rightarrow> hubcap \<Rightarrow> int" where
  "hB v (Hubcap1 i b' hc') = 2 * b' + hB v hc'"
| "hB v (Hubcap2 i j b' hc') = b' * (if nth0 v i = 1 then 2 else 1) + hB v hc'"
| "hB v Hubcap0 = 0"

fun hL :: "(nat \<Rightarrow> int) \<Rightarrow> nat list \<Rightarrow> hubcap \<Rightarrow> int" where
  "hL d v (Hubcap1 i b' hc') = 2 * d i + hL d v hc'"
| "hL d v (Hubcap2 i j b' hc') = (d i + d j) * (if nth0 v i = 1 then 2 else 1) + hL d v hc'"
| "hL d v Hubcap0 = 0"

fun hW :: "nat list \<Rightarrow> hubcap \<Rightarrow> nat \<Rightarrow> int" where
  "hW v (Hubcap1 i b' hc') k = (if k = i then 2 else 0) + hW v hc' k"
| "hW v (Hubcap2 i j b' hc') k =
     ((if k = i then 1 else 0) + (if k = j then 1 else 0)) * (if nth0 v i = 1 then 2 else 1) + hW v hc' k"
| "hW v Hubcap0 k = 0"

fun hconds :: "nat list \<Rightarrow> hubcap \<Rightarrow> bool" where
  "hconds v (Hubcap1 i b' hc') = (nth0 v i = 1 \<and> hconds v hc')"
| "hconds v (Hubcap2 i j b' hc') = (nth0 v i = nth0 v j \<and> nth0 v i \<le> 2 \<and> hconds v hc')"
| "hconds v Hubcap0 = True"

lemma cover_rec_sound: "hubcap_cover_rec v b hc \<Longrightarrow> hconds v hc \<and> b + hB v hc \<le> 0"
proof (induction v b hc rule: hubcap_cover_rec.induct)
  case (1 v b i b' hc')
  then have "hconds v hc' \<and> 2 * b' + b + hB v hc' \<le> 0" by simp
  then show ?case using "1.prems" by (simp add: algebra_simps)
next
  case (2 v b i j b' hc')
  let ?w = "(if nth0 v i = 1 then 2 else 1) :: int"
  have r: "hubcap_cover_rec v (b' * ?w + b) hc'" using "2.prems" unfolding hubcap_cover_rec.simps by blast
  then have "hconds v hc' \<and> b' * ?w + b + hB v hc' \<le> 0" using "2.IH" by blast
  then show ?case using "2.prems" by (simp add: algebra_simps)
next
  case (3 v b) then show ?case by simp
qed

lemma hL_eq: "(\<forall>k. nth0 (tally_hubcap hc) k > 0 \<longrightarrow> k < n) \<Longrightarrow>
    hL d v hc = (\<Sum>k < n. hW v hc k * d k)"
proof (induction hc)
  case Hubcap0 then show ?case by simp
next
  case (Hubcap1 i b' hc)
  have i: "i < n" using Hubcap1.prems[rule_format, of i] by (simp add: nth0_incr)
  have r: "\<forall>k. nth0 (tally_hubcap hc) k > 0 \<longrightarrow> k < n"
    using Hubcap1.prems by (auto simp: nth0_incr)
  have "(\<Sum>k < n. (if k = i then 2 else 0) * d k) = (\<Sum>k < n. if k = i then 2 * d i else 0)"
    by (rule sum.cong) auto
  also have "\<dots> = 2 * d i" using i by (simp add: sum.delta)
  finally have s1: "(\<Sum>k < n. (if k = i then 2 else 0) * d k) = 2 * d i" .
  have "(\<Sum>k < n. ((if k = i then 2 else 0) + hW v hc k) * d k) =
      (\<Sum>k < n. (if k = i then 2 else 0) * d k) + (\<Sum>k < n. hW v hc k * d k)"
    by (simp add: algebra_simps sum.distrib)
  then show ?case using Hubcap1.IH[OF r] s1 by simp
next
  case (Hubcap2 i j b' hc)
  have ij: "i < n" "j < n" using Hubcap2.prems[rule_format, of i] Hubcap2.prems[rule_format, of j]
    by (simp_all add: nth0_incr)
  have r: "\<forall>k. nth0 (tally_hubcap hc) k > 0 \<longrightarrow> k < n"
    using Hubcap2.prems by (auto simp: nth0_incr)
  let ?w = "(if nth0 v i = 1 then 2 else 1) :: int"
  have "(\<Sum>k < n. ((if k = i then 1 else 0) + (if k = j then 1 else 0)) * ?w * d k) =
      (\<Sum>k < n. if k = i then ?w * d i else 0) + (\<Sum>k < n. if k = j then ?w * d j else 0)"
    unfolding sum.distrib[symmetric] by (rule sum.cong) (auto simp: algebra_simps)
  also have "\<dots> = (d i + d j) * ?w" using ij by (simp add: sum.delta algebra_simps)
  finally have s2: "(\<Sum>k < n. ((if k = i then 1 else 0) + (if k = j then 1 else 0)) * ?w * d k) = (d i + d j) * ?w" .
  have "(\<Sum>k < n. (((if k = i then 1 else 0) + (if k = j then 1 else 0)) * ?w + hW v hc k) * d k) =
      (\<Sum>k < n. ((if k = i then 1 else 0) + (if k = j then 1 else 0)) * ?w * d k) + (\<Sum>k < n. hW v hc k * d k)"
    by (simp add: algebra_simps sum.distrib)
  then show ?case using Hubcap2.IH[OF r] s2 by simp
qed

lemma hW_eq: "hconds v hc \<Longrightarrow> hW v hc k = (if nth0 v k = 1 then 2 else 1) * int (nth0 (tally_hubcap hc) k)"
proof (induction hc)
  case Hubcap0 then show ?case by (simp add: nth0_def)
next
  case (Hubcap1 i b' hc)
  have vi: "nth0 v i = 1" and hc: "hconds v hc" using Hubcap1.prems by simp_all
  have IH: "hW v hc k = (if nth0 v k = 1 then 2 else 1) * int (nth0 (tally_hubcap hc) k)"
    by (rule Hubcap1.IH[OF hc])
  have t: "nth0 (tally_hubcap (Hubcap1 i b' hc)) k = nth0 (tally_hubcap hc) k + (if k = i then 1 else 0)"
    by (simp add: nth0_incr)
  show ?case
  proof (cases "k = i")
    case True then show ?thesis using IH t vi by (simp add: algebra_simps)
  next
    case False then show ?thesis using IH t by simp
  qed
next
  case (Hubcap2 i j b' hc)
  have vij: "nth0 v i = nth0 v j" and hc: "hconds v hc" using Hubcap2.prems by simp_all
  have IH: "hW v hc k = (if nth0 v k = 1 then 2 else 1) * int (nth0 (tally_hubcap hc) k)"
    by (rule Hubcap2.IH[OF hc])
  have t: "nth0 (tally_hubcap (Hubcap2 i j b' hc)) k =
      nth0 (tally_hubcap hc) k + (if k = i then 1 else 0) + (if k = j then 1 else 0)"
    by (simp add: nth0_incr)
  let ?wk = "(if nth0 v k = 1 then 2 else 1) :: int"
  have w: "k = i \<or> k = j \<Longrightarrow> (if nth0 v i = 1 then 2 else 1) = ?wk" using vij by auto
  show ?case
  proof (cases "k = i \<or> k = j")
    case True
    have "hW v (Hubcap2 i j b' hc) k =
        ((if k = i then 1 else 0) + (if k = j then 1 else 0)) * ?wk + ?wk * int (nth0 (tally_hubcap hc) k)"
      using w[OF True] IH by simp
    then show ?thesis using t by (simp add: algebra_simps)
  next
    case False then show ?thesis using IH t by simp
  qed
qed


lemma hconds_le2: "hconds v hc \<Longrightarrow> 0 < nth0 (tally_hubcap hc) k \<Longrightarrow> nth0 v k \<le> 2"
proof (induction hc)
  case Hubcap0 then show ?case by (simp add: nth0_def)
next
  case (Hubcap1 i b' hc)
  have vi: "nth0 v i = 1" and hc: "hconds v hc" using Hubcap1.prems(1) by simp_all
  show ?case
  proof (cases "k = i")
    case True then show ?thesis using vi by simp
  next
    case False
    then have "0 < nth0 (tally_hubcap hc) k" using Hubcap1.prems(2) by (simp add: nth0_incr)
    then show ?thesis by (rule Hubcap1.IH[OF hc])
  qed
next
  case (Hubcap2 i j b' hc)
  have vij: "nth0 v i = nth0 v j" "nth0 v i \<le> 2" and hc: "hconds v hc" using Hubcap2.prems(1) by simp_all
  show ?case
  proof (cases "k = i \<or> k = j")
    case True then show ?thesis using vij by auto
  next
    case False
    then have "0 < nth0 (tally_hubcap hc) k" using Hubcap2.prems(2) by (simp add: nth0_incr)
    then show ?thesis by (rule Hubcap2.IH[OF hc])
  qed
qed

fun hidx_ok :: "nat \<Rightarrow> hubcap \<Rightarrow> bool" where
  "hidx_ok n (Hubcap1 i _ hc) = (i < n \<and> hidx_ok n hc)"
| "hidx_ok n (Hubcap2 i j _ hc) = (i < n \<and> j < n \<and> hidx_ok n hc)"
| "hidx_ok n Hubcap0 = True"

lemma hidx_tally: "(\<forall>k. 0 < nth0 (tally_hubcap hc) k \<longrightarrow> k < n) \<Longrightarrow> hidx_ok n hc"
proof (induction hc)
  case Hubcap0 then show ?case by simp
next
  case (Hubcap1 i b' hc)
  have "\<forall>k. 0 < nth0 (tally_hubcap hc) k \<longrightarrow> k < n" using Hubcap1.prems by (auto simp: nth0_incr)
  moreover have "i < n" using Hubcap1.prems[rule_format, of i] by (simp add: nth0_incr)
  ultimately show ?case using Hubcap1.IH by simp
next
  case (Hubcap2 i j b' hc)
  have "\<forall>k. 0 < nth0 (tally_hubcap hc) k \<longrightarrow> k < n" using Hubcap2.prems by (auto simp: nth0_incr)
  moreover have "i < n" "j < n" using Hubcap2.prems[rule_format, of i] Hubcap2.prems[rule_format, of j]
    by (simp_all add: nth0_incr)
  ultimately show ?case using Hubcap2.IH by simp
qed

context pcp
begin

lemma check_dbound1_rec_ok:
  "(\<And>x p. x \<in> D \<Longrightarrow> redp p \<Longrightarrow> \<not> exact_fitp G x p) \<Longrightarrow>
   x \<in> D \<Longrightarrow> exact_fitp G x p \<Longrightarrow> check_dbound1_rec redp p rs ns m \<Longrightarrow> dbound1 G rs x \<le> ns"
proof (induction redp p rs ns m rule: check_dbound1_rec.induct)
  case (1 redp p rs ns) then show ?case by simp
next
  case (2 redp p ns m) then show ?case by (simp add: dbound1_def)
next
  case (3 redp' p r rs' ns m)
  show ?case
  proof (cases "length rs' < ns")
    case True
    have "dbound1 G (r # rs') x \<le> Suc (length rs')"
      unfolding dbound1_def using length_filter_le[of "fitp G x" "r # rs'"] by simp
    then show ?thesis using True by simp
  next
    case nlt: False
    let ?p' = "meet_part p r"
    obtain dns rs'' where sd: "sort_drules ?p' rs' = (dns, rs'')" by fastforce
    have c: "(if ns - dns = 0 then redp' ?p' else check_dbound1_rec redp' ?p' rs'' (ns - dns - 1) m) \<and>
        check_dbound1_rec redp' p rs' ns m"
      using "3.prems"(4) unfolding check_dbound1_rec.simps if_not_P[OF nlt] Let_def sd prod.case by assumption
    have c1: "if ns - dns = 0 then redp' ?p' else check_dbound1_rec redp' ?p' rs'' (ns - dns - 1) m"
      and c2: "check_dbound1_rec redp' p rs' ns m" using c by blast+
    show ?thesis
    proof (cases "fitp G x r")
      case False
      then show ?thesis using "3.IH"(2)[OF nlt "3.prems"(1,2,3) c2] by (simp add: dbound1_def)
    next
      case fr: True
      have ef: "exact_fitp G x ?p'" by (rule exact_fitp_meet[OF "3.prems"(3) fr])
      have fp': "fitp G x ?p'" using ef by (simp add: exact_fitp_def)
      have sdeq: "dbound1 G rs' x = dns + dbound1 G rs'' x" by (rule sort_dbound1_eq[OF fp' sd])
      have nz: "ns - dns \<noteq> 0"
      proof
        assume "ns - dns = 0"
        then have "redp' ?p'" using c1 by simp
        then show False using "3.prems"(1) "3.prems"(2) ef by blast
      qed
      then have rec: "check_dbound1_rec redp' ?p' rs'' (ns - dns - 1) m" using c1 by simp
      have "dbound1 G rs'' x \<le> ns - dns - 1"
        by (rule "3.IH"(1)[OF nlt refl sd[symmetric] _ "3.prems"(1,2) ef rec]) (use nz in simp)
      then show ?thesis using sdeq nz fr by (simp add: dbound1_def)
    qed
  qed
qed

lemma dbound1_cons: "dbound1 G (r # l) x = (if fitp G x r then Suc (dbound1 G l x) else dbound1 G l x)"
  by (simp add: dbound1_def)

lemma dbound1_le_len: "dbound1 G l x \<le> length l" by (simp add: dbound1_def)

lemma check_dbound2_rec_ok:
  "(\<And>x p. x \<in> D \<Longrightarrow> redp p \<Longrightarrow> \<not> exact_fitp G x p) \<Longrightarrow>
   x \<in> D \<Longrightarrow> exact_fitp G x p \<Longrightarrow> dbound1 G ru x = 0 \<Longrightarrow> check_dbound2_rec redp p rt rs ru nt m \<Longrightarrow>
   dbound1 G rt x \<le> nt + dbound1 G rs x"
proof (induction redp p rt rs ru nt m rule: check_dbound2_rec.induct)
  case (1 redp p rt rs ru nt) then show ?case by simp
next
  case (2 redp p rs ru nt m) then show ?case by (simp add: dbound1_def)
next
  case (3 redp' p r rt' rs ru nt m)
  show ?case
  proof (cases "length rt' < nt")
    case True
    have "dbound1 G (r # rt') x \<le> Suc (length rt')"
      using dbound1_le_len[of rt' x] by (simp add: dbound1_cons)
    then show ?thesis using True by simp
  next
    case nlt: False
    let ?p' = "meet_part p r"
    obtain dnt rt'' where st: "sort_drules ?p' rt' = (dnt, rt'')" by fastforce
    obtain dns rs' where ss: "sort_drules ?p' rs = (dns, rs')" by fastforce
    have c: "(check_unfit ?p' ru \<or>
        (if dns + nt - dnt = 0 then redp' ?p' else check_dbound2_rec redp' ?p' rt'' rs' ru (dns + nt - dnt - 1) m))
        \<and> check_dbound2_rec redp' p rt' rs (r # ru) nt m"
      using "3.prems"(5) unfolding check_dbound2_rec.simps if_not_P[OF nlt] Let_def st ss prod.case
      by assumption
    show ?thesis
    proof (cases "fitp G x r")
      case False
      have z: "dbound1 G (r # ru) x = 0" using "3.prems"(4) False by (simp add: dbound1_cons)
      have "dbound1 G rt' x \<le> nt + dbound1 G rs x"
        by (rule "3.IH"(2)[OF nlt refl "3.prems"(1,2,3) z conjunct2[OF c]])
      then show ?thesis using False by (simp add: dbound1_cons)
    next
      case fr: True
      have ef: "exact_fitp G x ?p'" by (rule exact_fitp_meet[OF "3.prems"(3) fr])
      have fp': "fitp G x ?p'" using ef by (simp add: exact_fitp_def)
      have nu: "\<not> check_unfit ?p' ru" by (rule check_unfitP[OF fp' "3.prems"(4)])
      have et: "dbound1 G rt' x = dnt + dbound1 G rt'' x" by (rule sort_dbound1_eq[OF fp' st])
      have es: "dbound1 G rs x = dns + dbound1 G rs' x" by (rule sort_dbound1_eq[OF fp' ss])
      have nz: "dns + nt - dnt \<noteq> 0"
      proof
        assume "dns + nt - dnt = 0"
        then have "redp' ?p'" using c nu by simp
        then show False using "3.prems"(1,2) ef by blast
      qed
      then have rec: "check_dbound2_rec redp' ?p' rt'' rs' ru (dns + nt - dnt - 1) m" using c nu by simp
      have "dbound1 G rt'' x \<le> (dns + nt - dnt - 1) + dbound1 G rs' x"
        by (rule "3.IH"(1)[OF nlt refl st[symmetric] ss[symmetric] nz "3.prems"(1,2) ef "3.prems"(4) rec])
      then show ?thesis using et es nz fr by (simp add: dbound1_cons)
    qed
  qed
qed

lemma check_dbound2P:
  assumes rp: "\<And>x p. x \<in> D \<Longrightarrow> redp p \<Longrightarrow> \<not> exact_fitp G x p"
    and xD: "x \<in> D" and ex: "exact_fitp G x p" and ck: "check_dbound2 nhub redp p b"
  shows "dbound2 G (pick_target_drules nhub) (pick_source_drules nhub) x \<le> b"
proof -
  obtain dnt rt' where st: "sort_drules p (pick_target_drules nhub) = (dnt, rt')" by fastforce
  obtain dns rs' where ss: "sort_drules p (pick_source_drules nhub) = (dns, rs')" by fastforce
  have fp: "fitp G x p" using ex by (simp add: exact_fitp_def)
  let ?bb = "int dns - int dnt + b"
  have bb: "0 \<le> ?bb" and rc: "check_dbound2_rec redp p rt' rs' [] (nat ?bb) (length rt' + 2)"
    using ck st ss by (simp_all add: check_dbound2_def Let_def)
  have "dbound1 G rt' x \<le> nat ?bb + dbound1 G rs' x"
  proof -
    have z0: "dbound1 G [] x = 0" unfolding dbound1_def by simp
    show ?thesis by (rule check_dbound2_rec_ok[OF rp xD ex z0 rc])
  qed
  moreover have "dbound1 G (pick_target_drules nhub) x = dnt + dbound1 G rt' x" by (rule sort_dbound1_eq[OF fp st])
  moreover have "dbound1 G (pick_source_drules nhub) x = dns + dbound1 G rs' x" by (rule sort_dbound1_eq[OF fp ss])
  ultimately show ?thesis using bb by (simp add: dbound2_def)
qed


lemma iter_nhub: "arity G x1 = nhub \<Longrightarrow> i \<le> nhub \<Longrightarrow> (f ^^ (nhub - i)) ((f ^^ i) x1) = x1"
proof -
  assume a: "arity G x1 = nhub" and i: "i \<le> nhub"
  have "(f ^^ (nhub - i)) ((f ^^ i) x1) = (f ^^ (nhub - i + i)) x1" by (simp add: funpow_add)
  also have "nhub - i + i = arity G x1" using a i by simp
  finally show ?thesis using iter_arity by simp
qed

lemma check_2dbound2_rec_ok:
  "(\<And>x p. x \<in> D \<Longrightarrow> redp p \<Longrightarrow> \<not> exact_fitp G x p) \<Longrightarrow>
   x1 \<in> D \<Longrightarrow> arity G x1 = nhub \<Longrightarrow> i \<le> nhub \<Longrightarrow>
   exact_fitp G x1 p1 \<Longrightarrow> exact_fitp G ((f ^^ i) x1) p2 \<Longrightarrow>
   dbound1 G ru1 x1 = 0 \<Longrightarrow> dbound1 G ru2 ((f ^^ i) x1) = 0 \<Longrightarrow>
   check_2dbound2_rec nhub redp p1 p2 rt1 rs1 ru1 rt2 rs2 ru2 i nt m \<Longrightarrow>
   dbound1 G rt1 x1 + dbound1 G rt2 ((f ^^ i) x1) \<le> nt + dbound1 G rs1 x1 + dbound1 G rs2 ((f ^^ i) x1)"
proof (induction nhub redp p1 p2 rt1 rs1 ru1 rt2 rs2 ru2 i nt m arbitrary: x1
    rule: check_2dbound2_rec.induct)
  case (1 nhub redp p1 p2 rt1 rs1 ru1 rt2 rs2 ru2 i nt) then show ?case by simp
next
  case (2 nhub redp' p1 p2 rs1 ru1 rt2 rs2 ru2 i nt m)
  show ?case
  proof (cases "rt2 = []")
    case True then show ?thesis by (simp add: dbound1_def)
  next
    case False
    let ?x2 = "(f ^^ i) x1"
    have rec: "check_2dbound2_rec nhub redp' p2 p1 rt2 rs2 ru2 [] rs1 ru1 (nhub - i) nt m"
      using "2.prems"(9) False by simp
    have bk: "(f ^^ (nhub - i)) ?x2 = x1" by (rule iter_nhub[OF "2.prems"(3,4)])
    have x2D: "?x2 \<in> D" using "2.prems"(2) by simp
    have a2: "arity G ?x2 = nhub" using "2.prems"(3) by simp
    have "dbound1 G rt2 ?x2 + dbound1 G [] ((f ^^ (nhub - i)) ?x2) \<le>
        nt + dbound1 G rs2 ?x2 + dbound1 G rs1 ((f ^^ (nhub - i)) ?x2)"
      by (rule "2.IH"[OF "2.prems"(1) x2D a2 _ "2.prems"(6)])
         (use "2.prems" bk rec in simp_all)
    then show ?thesis using bk by (simp add: dbound1_def)
  qed
next
  case (3 nhub redp' p1 p2 r rt1' rs1 ru1 rt2 rs2 ru2 i nt m)
  let ?x2 = "(f ^^ i) x1"
  show ?case
  proof (cases "length rt1' + length rt2 < nt")
    case True
    have "dbound1 G (r # rt1') x1 + dbound1 G rt2 ?x2 \<le> Suc (length rt1') + length rt2"
      using dbound1_le_len[of rt1' x1] dbound1_le_len[of rt2 ?x2] by (simp add: dbound1_cons)
    then show ?thesis using True by simp
  next
    case nlt: False
    let ?p1' = "meet_part p1 r"
    let ?p2' = "rot_part i ?p1'"
    obtain dnt1 rt1'' where s1: "sort_drules ?p1' rt1' = (dnt1, rt1'')" by fastforce
    obtain dns1 rs1' where s2: "sort_drules ?p1' rs1 = (dns1, rs1')" by fastforce
    obtain dnt2 rt2' where s3: "sort_drules ?p2' rt2 = (dnt2, rt2')" by fastforce
    obtain dns2 rs2' where s4: "sort_drules ?p2' rs2 = (dns2, rs2')" by fastforce
    let ?K = "dns1 + (dns2 + nt) - (dnt1 + dnt2)"
    have c: "(check_unfit ?p1' ru1 \<or> check_unfit ?p2' ru2 \<or>
        (if ?K = 0 then redp' ?p1' else check_2dbound2_rec nhub redp' ?p1' ?p2' rt1'' rs1' ru1 rt2' rs2' ru2 i (?K - 1) m))
        \<and> check_2dbound2_rec nhub redp' p1 p2 rt1' rs1 (r # ru1) rt2 rs2 ru2 i nt m"
      using "3.prems"(9) unfolding check_2dbound2_rec.simps if_not_P[OF nlt] Let_def s1 s2 s3 s4 prod.case
      by assumption
    show ?thesis
    proof (cases "fitp G x1 r")
      case False
      have z: "dbound1 G (r # ru1) x1 = 0" using "3.prems"(7) False by (simp add: dbound1_cons)
      have "dbound1 G rt1' x1 + dbound1 G rt2 ?x2 \<le> nt + dbound1 G rs1 x1 + dbound1 G rs2 ?x2"
        by (rule "3.IH"(2)[OF nlt refl refl "3.prems"(1-6) z "3.prems"(8) conjunct2[OF c]])
      then show ?thesis using False by (simp add: dbound1_cons)
    next
      case fr: True
      have e1: "exact_fitp G x1 ?p1'" by (rule exact_fitp_meet[OF "3.prems"(5) fr])
      have sz: "psize ?p1' = nhub" using e1 "3.prems"(3) by (simp add: exact_fitp_def)
      have e2: "exact_fitp G ?x2 ?p2'" using fitp_rot[of i ?p1' x1] e1 sz "3.prems"(4) by simp
      have f1: "fitp G x1 ?p1'" and f2: "fitp G ?x2 ?p2'" using e1 e2 by (simp_all add: exact_fitp_def)
      have nu1: "\<not> check_unfit ?p1' ru1" by (rule check_unfitP[OF f1 "3.prems"(7)])
      have nu2: "\<not> check_unfit ?p2' ru2" by (rule check_unfitP[OF f2 "3.prems"(8)])
      have q1: "dbound1 G rt1' x1 = dnt1 + dbound1 G rt1'' x1" by (rule sort_dbound1_eq[OF f1 s1])
      have q2: "dbound1 G rs1 x1 = dns1 + dbound1 G rs1' x1" by (rule sort_dbound1_eq[OF f1 s2])
      have q3: "dbound1 G rt2 ?x2 = dnt2 + dbound1 G rt2' ?x2" by (rule sort_dbound1_eq[OF f2 s3])
      have q4: "dbound1 G rs2 ?x2 = dns2 + dbound1 G rs2' ?x2" by (rule sort_dbound1_eq[OF f2 s4])
      have nz: "?K \<noteq> 0"
      proof
        assume "?K = 0"
        then have "redp' ?p1'" using c nu1 nu2 by simp
        then show False using "3.prems"(1,2) e1 by blast
      qed
      then have rec: "check_2dbound2_rec nhub redp' ?p1' ?p2' rt1'' rs1' ru1 rt2' rs2' ru2 i (?K - 1) m"
        using c nu1 nu2 by simp
      have "dbound1 G rt1'' x1 + dbound1 G rt2' ?x2 \<le> (?K - 1) + dbound1 G rs1' x1 + dbound1 G rs2' ?x2"
        by (rule "3.IH"(1)[OF nlt refl refl s1[symmetric] s2[symmetric] s3[symmetric] s4[symmetric] nz
              "3.prems"(1-4) e1 e2 "3.prems"(7,8) rec])
      then show ?thesis using q1 q2 q3 q4 nz fr by (simp add: dbound1_cons)
    qed
  qed
qed

lemma check_2dbound2P:
  assumes rp: "\<And>x p. x \<in> D \<Longrightarrow> redp p \<Longrightarrow> \<not> exact_fitp G x p"
    and xD: "x \<in> D" and nFx: "arity G x = nhub" and ex: "exact_fitp G x p" and i: "i \<le> nhub"
    and ck: "check_2dbound2 nhub redp p i b"
  shows "dbound2 G (pick_target_drules nhub) (pick_source_drules nhub) x +
         dbound2 G (pick_target_drules nhub) (pick_source_drules nhub) ((f ^^ i) x) \<le> b"
proof -
  let ?rs = "pick_source_drules nhub" and ?rt = "pick_target_drules nhub"
  let ?p2 = "rot_part i p" and ?x2 = "(f ^^ i) x"
  have sz: "psize p = nhub" using ex nFx by (simp add: exact_fitp_def)
  have e2: "exact_fitp G ?x2 ?p2" using fitp_rot[of i p x] ex sz i by simp
  have f1: "fitp G x p" and f2: "fitp G ?x2 ?p2" using ex e2 by (simp_all add: exact_fitp_def)
  obtain dnt1 rt1 where s1: "sort_drules p ?rt = (dnt1, rt1)" by fastforce
  obtain dns1 rs1 where s2: "sort_drules p ?rs = (dns1, rs1)" by fastforce
  obtain dnt2 rt2 where s3: "sort_drules ?p2 ?rt = (dnt2, rt2)" by fastforce
  obtain dns2 rs2 where s4: "sort_drules ?p2 ?rs = (dns2, rs2)" by fastforce
  let ?bb = "int (dns1 + dns2) - int (dnt1 + dnt2) + b"
  have bb: "0 \<le> ?bb" and rc: "check_2dbound2_rec nhub redp p ?p2 rt1 rs1 [] rt2 rs2 [] i (nat ?bb)
      (length rt1 + (length rt2 + 3))"
    using ck s1 s2 s3 s4 by (simp_all add: check_2dbound2_def Let_def)
  have z0: "dbound1 G [] y = 0" for y unfolding dbound1_def by simp
  have "dbound1 G rt1 x + dbound1 G rt2 ?x2 \<le> nat ?bb + dbound1 G rs1 x + dbound1 G rs2 ?x2"
    by (rule check_2dbound2_rec_ok[OF rp xD nFx i ex e2 z0 z0 rc])
  moreover have "dbound1 G ?rt x = dnt1 + dbound1 G rt1 x" by (rule sort_dbound1_eq[OF f1 s1])
  moreover have "dbound1 G ?rs x = dns1 + dbound1 G rs1 x" by (rule sort_dbound1_eq[OF f1 s2])
  moreover have "dbound1 G ?rt ?x2 = dnt2 + dbound1 G rt2 ?x2" by (rule sort_dbound1_eq[OF f2 s3])
  moreover have "dbound1 G ?rs ?x2 = dns2 + dbound1 G rs2 ?x2" by (rule sort_dbound1_eq[OF f2 s4])
  ultimately show ?thesis using bb by (simp add: dbound2_def)
qed


lemma fit_hubcap_rot:
  assumes xD: "x \<in> D" and nFx: "arity G x = nhub" and ex: "exact_fitp G x p" and j: "j < nhub"
  shows "exact_fitp G ((f ^^ j) ((f ^^ (nhub - 2)) x)) (hubcap_rot nhub j p)"
proof -
  have n5: "5 \<le> nhub" using pentaG[OF xD] nFx by simp
  have sz: "psize p = nhub" using ex nFx by (simp add: exact_fitp_def)
  let ?m = "if 2 \<le> j then j - 2 else nhub + j - 2"
  have mle: "?m \<le> psize p" using j sz n5 by auto
  have "(f ^^ j) ((f ^^ (nhub - 2)) x) = (f ^^ ?m) x"
  proof (cases "2 \<le> j")
    case True
    have ar: "j + (nhub - 2) = (j - 2) + nhub" using True n5 by simp
    have "(f ^^ j) ((f ^^ (nhub - 2)) x) = (f ^^ (j + (nhub - 2))) x" by (simp add: funpow_add)
    also have "\<dots> = (f ^^ (j - 2)) ((f ^^ nhub) x)" unfolding ar by (simp add: funpow_add)
    finally have "(f ^^ j) ((f ^^ (nhub - 2)) x) = (f ^^ (j - 2)) ((f ^^ nhub) x)" .
    then show ?thesis using True iter_arity[of x] nFx by simp
  next
    case False
    have ar: "j + (nhub - 2) = nhub + j - 2" using False n5 by simp
    have "(f ^^ j) ((f ^^ (nhub - 2)) x) = (f ^^ (j + (nhub - 2))) x" by (simp add: funpow_add)
    then show ?thesis using False ar by simp
  qed
  then show ?thesis using fitp_rot[OF mle, of x] ex by (simp add: hubcap_rot_def)
qed

lemma iter_hub_subn:
  assumes a1: "arity G x1 = nhub" and i: "i < nhub" and j: "j < nhub"
  shows "(f ^^ hub_subn nhub i j) ((f ^^ j) x1) = (f ^^ i) x1"
proof (cases "j \<le> i")
  case True
  have "(f ^^ (i - j)) ((f ^^ j) x1) = (f ^^ (i - j + j)) x1" by (simp add: funpow_add)
  then show ?thesis using True by (simp add: hub_subn_def)
next
  case False
  have "(f ^^ (i + nhub - j)) ((f ^^ j) x1) = (f ^^ (i + nhub - j + j)) x1" by (simp add: funpow_add)
  then have "(f ^^ hub_subn nhub i j) ((f ^^ j) x1) = (f ^^ (i + nhub)) x1"
    using False j by (simp add: hub_subn_def)
  also have "\<dots> = (f ^^ i) x1" using iter_arity[of x1] a1 by (simp add: funpow_add)
  finally show ?thesis .
qed

lemma hub_subn_le: "i < nhub \<Longrightarrow> hub_subn nhub i j \<le> nhub"
  by (auto simp: hub_subn_def)

lemma hL_bound:
  assumes rp: "\<And>x p. x \<in> D \<Longrightarrow> redp p \<Longrightarrow> \<not> exact_fitp G x p"
    and xD: "x \<in> D" and nFx: "arity G x = nhub" and ex: "exact_fitp G x p"
  defines "x1 \<equiv> (f ^^ (nhub - 2)) x"
  defines "d \<equiv> \<lambda>k. dbound2 G (pick_target_drules nhub) (pick_source_drules nhub) ((f ^^ k) x1)"
  shows "hidx_ok nhub hc \<Longrightarrow> hubcap_fit nhub redp p hc \<Longrightarrow> hL d v hc \<le> hB v hc"
proof (induction hc)
  case Hubcap0 then show ?case by simp
next
  case (Hubcap1 j b hc)
  have j: "j < nhub" using Hubcap1.prems by simp
  have ef: "exact_fitp G ((f ^^ j) x1) (hubcap_rot nhub j p)"
    unfolding x1_def by (rule fit_hubcap_rot[OF xD nFx ex j])
  have "d j \<le> b" unfolding d_def
    by (rule check_dbound2P[OF rp _ ef]) (use xD Hubcap1.prems in \<open>auto simp: x1_def\<close>)
  then show ?case using Hubcap1 by simp
next
  case (Hubcap2 j1 j2 b hc)
  have j: "j1 < nhub" "j2 < nhub" using Hubcap2.prems by simp_all
  have a1: "arity G x1 = nhub" using nFx by (simp add: x1_def)
  have ef: "exact_fitp G ((f ^^ j1) x1) (hubcap_rot nhub j1 p)"
    unfolding x1_def by (rule fit_hubcap_rot[OF xD nFx ex j(1)])
  have y1D: "(f ^^ j1) x1 \<in> D" using xD by (simp add: x1_def)
  have ay: "arity G ((f ^^ j1) x1) = nhub" using a1 by simp
  have "dbound2 G (pick_target_drules nhub) (pick_source_drules nhub) ((f ^^ j1) x1) +
        dbound2 G (pick_target_drules nhub) (pick_source_drules nhub) ((f ^^ hub_subn nhub j2 j1) ((f ^^ j1) x1)) \<le> b"
    by (rule check_2dbound2P[OF rp y1D ay ef hub_subn_le[OF j(2)]]) (use Hubcap2.prems in auto)
  then have "d j1 + d j2 \<le> b" using iter_hub_subn[OF a1 j(2) j(1)] by (simp add: d_def)
  then have "(d j1 + d j2) * (if nth0 v j1 = 1 then 2 else 1) \<le> b * (if nth0 v j1 = 1 then 2 else 1)"
    by (simp add: mult_right_mono)
  then show ?case using Hubcap2 by simp
qed

lemma sum_cyc_orb: "x1 \<in> D \<Longrightarrow> (\<Sum>y \<in> cyc f x1. (hh::'a \<Rightarrow> int) y) = (\<Sum>k < arity G x1. hh ((f ^^ k) x1))"
proof -
  assume "x1 \<in> D"
  have "(\<Sum>y \<in> cyc f x1. hh y) = sum_list (map hh (orb f x1))"
    using sum.distinct_set_conv_list[OF F.distinct_orb, of hh x1] F.set_orb by simp
  also have "\<dots> = (\<Sum>k < arity G x1. hh ((f ^^ k) x1))"
    by (simp add: orb_def traject_def sum_list_sum_nth atLeast0LessThan)
  finally show ?thesis .
qed

theorem hubcap_fit_bound:
  assumes rp: "\<And>x p. x \<in> D \<Longrightarrow> redp p \<Longrightarrow> \<not> exact_fitp G x p"
    and xD: "x \<in> D" and psz: "psize p = nhub" and pos: "0 < dscore G x"
    and cov: "hubcap_cover nhub hc" and fit: "hubcap_fit nhub redp p hc"
  shows "\<not> exact_fitp G x p"
proof
  assume ex: "exact_fitp G x p"
  have nFx: "arity G x = nhub" using ex psz by (simp add: exact_fitp_def)
  have n5: "5 \<le> nhub" using pentaG[OF xD] nFx by simp
  define x1 where "x1 = (f ^^ (nhub - 2)) x"
  define d where "d = (\<lambda>k. dbound2 G (pick_target_drules nhub) (pick_source_drules nhub) ((f ^^ k) x1))"
  define v where "v = tally_hubcap hc"
  have lv: "length v = nhub" and v0: "0 \<notin> set v" and cr: "hubcap_cover_rec v (2 * dboundK nhub - 1) hc"
    using cov by (simp_all add: hubcap_cover_def v_def Let_def)
  have hc: "hconds v hc" and hb: "2 * dboundK nhub - 1 + hB v hc \<le> 0" using cover_rec_sound[OF cr] by simp_all
  have idx: "\<forall>k. 0 < nth0 v k \<longrightarrow> k < nhub" using lv by (simp add: nth0_def)
  have hok: "hidx_ok nhub hc" by (rule hidx_tally) (use idx in \<open>simp add: v_def\<close>)
  have W2: "hW v hc k = 2" if k: "k < nhub" for k
  proof -
    have pos: "0 < nth0 v k" using v0 k lv by (auto simp: nth0_def in_set_conv_nth)
    have le2: "nth0 v k \<le> 2" by (rule hconds_le2[OF hc]) (use pos in \<open>simp add: v_def\<close>)
    have "hW v hc k = (if nth0 v k = 1 then 2 else 1) * int (nth0 v k)"
      using hW_eq[OF hc, of k] by (simp add: v_def)
    moreover have "nth0 v k = 1 \<or> nth0 v k = 2" using pos le2 by auto
    ultimately show ?thesis by auto
  qed
  have "hL d v hc = (\<Sum>k < nhub. hW v hc k * d k)" by (rule hL_eq) (use idx in \<open>simp add: v_def\<close>)
  also have "\<dots> = (\<Sum>k < nhub. 2 * d k)" by (rule sum.cong) (simp_all add: W2)
  finally have hl: "hL d v hc = 2 * (\<Sum>k < nhub. d k)" by (simp add: sum_distrib_left)
  have "hL d v hc \<le> hB v hc"
    using hL_bound[OF rp xD nFx ex hok fit] by (simp add: d_def x1_def)
  then have le: "2 * (dboundK nhub + (\<Sum>k < nhub. d k)) \<le> 1" using hl hb by simp
  have x1D: "x1 \<in> D" using xD by (simp add: x1_def)
  have a1: "arity G x1 = nhub" using nFx by (simp add: x1_def)
  have cyc: "cyc f x = cyc f x1"
  proof -
    have "fconnect f x x1" by (simp add: x1_def fconnect_funpow)
    then show ?thesis by (rule F.cyc_eq)
  qed
  have "(\<Sum>y \<in> cyc f x. dbound2 G (pick_target_drules nhub) (pick_source_drules nhub) y) = (\<Sum>k < nhub. d k)"
    using sum_cyc_orb[OF x1D] cyc a1 by (simp add: d_def)
  then have "0 < dboundK nhub + (\<Sum>k < nhub. d k)" using dscore_cap2[OF xD nFx pos] by simp
  then show False using le by simp
qed

end

end
