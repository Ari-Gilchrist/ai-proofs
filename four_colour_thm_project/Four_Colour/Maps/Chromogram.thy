(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Chromogram.thy
    Chromograms: words representing Kempe-inversion classes of ring colorings.
    Ported from G. Gonthier's Coq development (chromogram.v).
*)
theory Chromogram
  imports Four_Colour_Base.Color
begin

datatype gram_symbol = Gpush | Gskip | Gpop0 | Gpop1

type_synonym chromogram = "gram_symbol list"

fun gram_balanced :: "nat \<Rightarrow> bool \<Rightarrow> chromogram \<Rightarrow> bool" where
  "gram_balanced 0 b [] = (\<not> b)"
| "gram_balanced (Suc d) b [] = False"
| "gram_balanced d b (Gpush # w) = gram_balanced (Suc d) b w"
| "gram_balanced d b (Gskip # w) = gram_balanced d (\<not> b) w"
| "gram_balanced (Suc d) b (Gpop0 # w) = gram_balanced d b w"
| "gram_balanced (Suc d) b (Gpop1 # w) = gram_balanced d (\<not> b) w"
| "gram_balanced 0 b (Gpop0 # w) = False"
| "gram_balanced 0 b (Gpop1 # w) = False"

text \<open>One matching step: the new stack of open-chord parities, if the symbol matches the color.
  (Gonthier's @{text bit_stack} is replaced by plain boolean lists.)\<close>

fun mstep :: "color \<Rightarrow> gram_symbol \<Rightarrow> bool list \<Rightarrow> bool list option" where
  "mstep Color1 Gskip lb = Some lb"
| "mstep Color2 Gpush lb = Some (False # lb)"
| "mstep Color2 Gpop0 (False # lb) = Some lb"
| "mstep Color2 Gpop1 (True # lb) = Some lb"
| "mstep Color3 Gpush lb = Some (True # lb)"
| "mstep Color3 Gpop0 (True # lb) = Some lb"
| "mstep Color3 Gpop1 (False # lb) = Some lb"
| "mstep _ _ _ = None"

fun matchg :: "bool list \<Rightarrow> colseq \<Rightarrow> chromogram \<Rightarrow> bool" where
  "matchg lb [] [] = (lb = [])"
| "matchg lb (e # et) (s # w) = (case mstep e s lb of Some lb' \<Rightarrow> matchg lb' et w | None \<Rightarrow> False)"
| "matchg lb (e # et) [] = False"
| "matchg lb [] (s # w) = False"

fun matchpg :: "bool list \<Rightarrow> colseq \<Rightarrow> chromogram \<Rightarrow> bool" where
  "matchpg lb [] [] = True"
| "matchpg lb (e # et) (s # w) = (case mstep e s lb of Some lb' \<Rightarrow> matchpg lb' et w | None \<Rightarrow> False)"
| "matchpg lb (e # et) [] = False"
| "matchpg lb [] (s # w) = False"

definition Kempe_closed :: "(colseq \<Rightarrow> bool) \<Rightarrow> bool" where
  "Kempe_closed P \<longleftrightarrow> (\<forall>et. P et \<longrightarrow>
     (\<forall>g. P (permt g et)) \<and> (\<exists>w. matchg [] et w \<and> (\<forall>et'. matchg [] et' w \<longrightarrow> P et')))"

definition Kempe_coclosure :: "(colseq \<Rightarrow> bool) \<Rightarrow> colseq \<Rightarrow> bool" where
  "Kempe_coclosure P et \<longleftrightarrow> (\<forall>P'. Kempe_closed P' \<longrightarrow> P' et \<longrightarrow> (\<exists>et'. P et' \<and> P' et'))"

fun cgram :: "nat \<Rightarrow> bool \<Rightarrow> chromogram \<Rightarrow> chromogram" where
  "cgram d b [] = [if d = 0 then Gskip else if b then Gpop1 else Gpop0]"
| "cgram d b (s # w) = s # (case s of
       Gpush \<Rightarrow> cgram (Suc d) b w
     | Gskip \<Rightarrow> cgram d (\<not> b) w
     | Gpop0 \<Rightarrow> cgram (d - 1) b w
     | Gpop1 \<Rightarrow> cgram (d - 1) (\<not> b) w)"

definition sumb :: "bool list \<Rightarrow> bool" where
  "sumb lb = foldr (\<lambda>a b. a \<noteq> b) lb False"

lemma sumb_Nil [simp]: "sumb [] = False" and sumb_Cons [simp]: "sumb (a # lb) = (a \<noteq> sumb lb)"
  by (simp_all add: sumb_def)

lemma mstep_Some_iff:
  "mstep e s lb = Some lb' \<longleftrightarrow>
     (e = Color1 \<and> s = Gskip \<and> lb' = lb) \<or> (e = Color2 \<and> s = Gpush \<and> lb' = False # lb) \<or>
     (e = Color3 \<and> s = Gpush \<and> lb' = True # lb) \<or> (e = Color2 \<and> s = Gpop0 \<and> lb = False # lb') \<or>
     (e = Color2 \<and> s = Gpop1 \<and> lb = True # lb') \<or> (e = Color3 \<and> s = Gpop0 \<and> lb = True # lb') \<or>
     (e = Color3 \<and> s = Gpop1 \<and> lb = False # lb')"
  by (induction e s lb rule: mstep.induct) auto

lemma mstep_flip: "mstep (permc Eperm132 e) s (map Not lb) = map_option (map Not) (mstep e s lb)"
  by (induction e s lb rule: mstep.induct) simp_all

lemma mstep_SomeE:
  assumes "mstep e s lb = Some lb'"
  obtains (skip) "e = Color1" "s = Gskip" "lb' = lb"
  | (push2) "e = Color2" "s = Gpush" "lb' = False # lb"
  | (push3) "e = Color3" "s = Gpush" "lb' = True # lb"
  | (pop20) "e = Color2" "s = Gpop0" "lb = False # lb'"
  | (pop21) "e = Color2" "s = Gpop1" "lb = True # lb'"
  | (pop30) "e = Color3" "s = Gpop0" "lb = True # lb'"
  | (pop31) "e = Color3" "s = Gpop1" "lb = False # lb'"
  using assms unfolding mstep_Some_iff by (elim disjE conjE) (simp_all add: that)

lemma mstep_c0 [simp]: "mstep Color0 s lb = None"
  by simp

lemma matchg_size: "matchg lb et w \<Longrightarrow> length w = length et"
  by (induction lb et w rule: matchg.induct) (auto split: option.splits)

lemma matchpg_size: "matchpg lb et w \<Longrightarrow> length w = length et"
  by (induction lb et w rule: matchpg.induct) (auto split: option.splits)

lemma matchg_memc0: "matchg lb et w \<Longrightarrow> Color0 \<notin> set et"
proof (induction lb et w rule: matchg.induct)
  case (2 lb e et s w)
  then show ?case by (cases e) (auto split: option.splits)
qed auto

lemma matchg_balanced_gen:
  "matchg lb et w \<Longrightarrow>
   (cbit1 (sumt et) \<longleftrightarrow> odd (length lb)) \<and> gram_balanced (length lb) (cbit0 (sumt et) \<noteq> sumb lb) w"
proof (induction lb et w rule: matchg.induct)
  case (1 lb)
  then show ?case by simp
next
  case (2 lb e et s w)
  then obtain lb' where st: "mstep e s lb = Some lb'" and m: "matchg lb' et w"
    by (auto split: option.splits)
  have IH: "(cbit1 (sumt et) \<longleftrightarrow> odd (length lb')) \<and>
            gram_balanced (length lb') (cbit0 (sumt et) \<noteq> sumb lb') w"
    using 2 st m by simp
  from st show ?case
  proof (cases rule: mstep_SomeE)
    case skip
    then show ?thesis using IH by (simp add: cbit0_addc cbit1_addc)
  next
    case push2
    then show ?thesis using IH by (simp add: cbit0_addc cbit1_addc)
  next
    case push3
    then show ?thesis using IH by (simp add: cbit0_addc cbit1_addc)
  next
    case pop20
    then show ?thesis using IH by (simp add: cbit0_addc cbit1_addc)
  next
    case pop21
    then show ?thesis using IH by (simp add: cbit0_addc cbit1_addc)
  next
    case pop30
    then show ?thesis using IH by (simp add: cbit0_addc cbit1_addc)
  next
    case pop31
    then show ?thesis using IH by (simp add: cbit0_addc cbit1_addc)
  qed
qed auto

lemma matchg_balanced:
  "matchg [] et w \<Longrightarrow> \<not> cbit1 (sumt et) \<and> gram_balanced 0 (cbit0 (sumt et)) w"
  using matchg_balanced_gen[of "[]" et w] by simp

lemma balanced_inj:
  "gram_balanced n1 b1 w \<Longrightarrow> gram_balanced n2 b2 w \<Longrightarrow> n1 = n2 \<and> b1 = b2"
proof (induction w arbitrary: n1 n2 b1 b2)
  case Nil
  then show ?case by (cases n1; cases n2) auto
next
  case (Cons s w)
  show ?case
  proof (cases s)
    case Gpush
    then show ?thesis using Cons by fastforce
  next
    case Gskip
    then show ?thesis using Cons by fastforce
  next
    case Gpop0
    then show ?thesis using Cons by (cases n1; cases n2) fastforce+
  next
    case Gpop1
    then show ?thesis using Cons by (cases n1; cases n2) fastforce+
  qed
qed

lemma balanced_sumt0:
  assumes bal: "gram_balanced 0 False w" and m: "matchg [] et w"
  shows "sumt et = Color0"
proof -
  have b1: "\<not> cbit1 (sumt et)" and b0: "gram_balanced 0 (cbit0 (sumt et)) w"
    using matchg_balanced[OF m] by auto
  have "\<not> cbit0 (sumt et)" using balanced_inj[OF b0 bal] by simp
  then show ?thesis using b1 ccons_cbits[of "sumt et"] by simp
qed

lemma permc132 [simp]:
  "permc Eperm132 Color0 = Color0" "permc Eperm132 Color1 = Color1"
  "permc Eperm132 Color2 = Color3" "permc Eperm132 Color3 = Color2"
  by simp_all

lemma matchg_flip_gen: "matchg (map Not lb) (permt Eperm132 et) w = matchg lb et w"
proof (induction et arbitrary: lb w)
  case Nil
  then show ?case by (cases w) simp_all
next
  case (Cons e et)
  then show ?case
    by (cases w) (simp_all add: mstep_flip split: option.splits)
qed

lemma matchg_flip: "matchg [] (permt Eperm132 et) w = matchg [] et w"
  using matchg_flip_gen[of "[]"] by simp

lemma match_etrace: "matchg [] (etrace et) w = matchg [] et w"
  by (simp add: etrace_def etrace_perm_def matchg_flip)

lemma matchpg_flip_gen: "matchpg (map Not lb) (permt Eperm132 et) w = matchpg lb et w"
proof (induction et arbitrary: lb w)
  case Nil
  then show ?case by (cases w) simp_all
next
  case (Cons e et)
  then show ?case
    by (cases w) (simp_all add: mstep_flip split: option.splits)
qed

lemma matchpg_flip: "matchpg [] (permt Eperm132 et) w = matchpg [] et w"
  using matchpg_flip_gen[of "[]"] by simp

lemma matchpg_etrace: "matchpg [] (etrace et) w = matchpg [] et w"
  by (simp add: etrace_def etrace_perm_def matchpg_flip)

lemma balanced_cgram:
  "gram_balanced d b cw \<Longrightarrow> cw \<noteq> [] \<Longrightarrow> cw = cgram d b (butlast cw)"
proof (induction cw arbitrary: d b)
  case Nil
  then show ?case by simp
next
  case (Cons s w)
  show ?case
  proof (cases w)
    case Nil
    then show ?thesis using Cons.prems(1)
      by (cases s; cases d) (auto elim: gram_balanced.elims)
  next
    case (Cons s' w')
    then have wne: "w \<noteq> []" by simp
    have bl: "butlast (s # w) = s # butlast w" using wne by simp
    show ?thesis
    proof (cases s)
      case Gpush
      then show ?thesis using Cons.IH[OF _ wne] Cons.prems(1) bl by simp
    next
      case Gskip
      then show ?thesis using Cons.IH[OF _ wne] Cons.prems(1) bl by simp
    next
      case Gpop0
      then show ?thesis using Cons.IH[OF _ wne] Cons.prems(1) bl by (cases d) simp_all
    next
      case Gpop1
      then show ?thesis using Cons.IH[OF _ wne] Cons.prems(1) bl by (cases d) simp_all
    qed
  qed
qed

lemma matchg_cgram:
  assumes m: "matchg [] (ctrace et) cw"
  shows "cw = cgram 0 False (take (length cw - 1) cw)"
proof -
  have "gram_balanced 0 False cw" using matchg_balanced[OF m] by simp
  moreover have "cw \<noteq> []" using matchg_size[OF m] by (auto simp: ctrace_def)
  ultimately show ?thesis using balanced_cgram by (simp add: butlast_conv_take)
qed

lemma ccons_addc: "ccons x y +c c = ccons (x \<noteq> cbit1 c) (y \<noteq> cbit0 c)"
  by (cases x; cases y; cases c) simp_all

lemma length_cgram: "length (cgram d b w) = Suc (length w)"
  by (induction d b w rule: cgram.induct) (auto split: gram_symbol.splits)

lemma cgram_ne [simp]: "cgram d b w \<noteq> []"
  by (cases w) simp_all

lemma matchg_pg_gen:
  "gram_balanced (length lb) b (cgram (length lb) b w) \<Longrightarrow>
   matchg lb (et @ [ccons (odd (length lb)) (b \<noteq> sumb lb) +c sumt et]) (cgram (length lb) b w)
     = matchpg lb et w"
proof (induction et arbitrary: lb b w)
  case Nil
  show ?case
  proof (cases w)
    case Nil
    show ?thesis
    proof (cases lb)
      case Nil
      then show ?thesis using Nil Cons \<open>w = []\<close> \<open>gram_balanced (length lb) b (cgram (length lb) b w)\<close>
        by (cases b) simp_all
    next
      case (Cons x lb')
      then show ?thesis using \<open>w = []\<close> \<open>gram_balanced (length lb) b (cgram (length lb) b w)\<close>
        by (cases b; cases x; cases lb') simp_all
    qed
  next
    case (Cons s w')
    have "length (cgram (length lb) b w) \<noteq> length [ccons (odd (length lb)) (b \<noteq> sumb lb) +c sumt []]"
      using Cons by (simp add: length_cgram split: gram_symbol.split)
    then show ?thesis using Cons matchg_size by fastforce
  qed
next
  case (Cons e et)
  note bal = Cons.prems
  show ?case
  proof (cases w)
    case Nil
    have "length (cgram (length lb) b w) \<noteq> length (e # et @ [ccons (odd (length lb)) (b \<noteq> sumb lb) +c sumt (e # et)])"
      using Nil by simp
    then show ?thesis using Nil matchg_size by fastforce
  next
    case (Cons s w')
    show ?thesis
    proof (cases "mstep e s lb")
      case None
      then show ?thesis using Cons by simp
    next
      case (Some lb')
      then show ?thesis
      proof (cases rule: mstep_SomeE)
        case skip
        then show ?thesis using Cons Some bal Cons.IH[of lb "\<not> b" w']
          by (simp add: ccons_addc addcA[symmetric])
      next
        case push2
        then show ?thesis using Cons Some bal Cons.IH[of lb' b w']
          by (simp add: ccons_addc addcA[symmetric])
      next
        case push3
        then show ?thesis using Cons Some bal Cons.IH[of lb' b w']
          by (simp add: ccons_addc addcA[symmetric])
      next
        case pop20
        then show ?thesis using Cons Some bal Cons.IH[of lb' b w']
          by (simp add: ccons_addc addcA[symmetric])
      next
        case pop21
        then show ?thesis using Cons Some bal Cons.IH[of lb' "\<not> b" w']
          by (simp add: ccons_addc addcA[symmetric])
      next
        case pop30
        then show ?thesis using Cons Some bal Cons.IH[of lb' b w']
          by (simp add: ccons_addc addcA[symmetric])
      next
        case pop31
        then show ?thesis using Cons Some bal Cons.IH[of lb' "\<not> b" w']
          by (simp add: ccons_addc addcA[symmetric])
      qed
    qed
  qed
qed

lemma matchg_pg:
  "gram_balanced 0 False (cgram 0 False w) \<Longrightarrow>
   matchg [] (ctrace et) (cgram 0 False w) = matchpg [] et w"
  using matchg_pg_gen[of "[]" False w et] by (simp add: ctrace_def)

end
