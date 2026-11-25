(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Mirror.thy
    Mirror images of parts (fitp_mirror, fitp_sym of part.v), via a node-list view of parts.
    Ported from G. Gonthier's Coq development (part.v, section FitMirrorPart).
*)
theory Mirror
  imports Converse
begin

section \<open>Parts as node lists\<close>

datatype pnode = NC prange prange | N6 prange prange | N7 prange prange prange
  | N8 prange prange prange prange

fun plist :: "part \<Rightarrow> pnode list" where
  "plist Pnil = []"
| "plist (Pcons s h p) = NC s h # plist p"
| "plist (Pcons6 h f1 p) = N6 h f1 # plist p"
| "plist (Pcons7 h f1 f2 p) = N7 h f1 f2 # plist p"
| "plist (Pcons8 h f1 f2 f3 p) = N8 h f1 f2 f3 # plist p"

lemma length_plist: "length (plist p) = psize p" by (induction p) simp_all

fun nhat :: "pnode \<Rightarrow> prange" where
  "nhat (NC s h) = h" | "nhat (N6 h _) = h" | "nhat (N7 h _ _) = h" | "nhat (N8 h _ _ _) = h"

fun nsethat :: "prange \<Rightarrow> pnode \<Rightarrow> pnode" where
  "nsethat h' (NC s h) = NC s h'" | "nsethat h' (N6 h a) = N6 h' a"
| "nsethat h' (N7 h a b) = N7 h' a b" | "nsethat h' (N8 h a b c) = N8 h' a b c"

fun nmir :: "pnode \<Rightarrow> pnode" where
  "nmir (NC s h) = NC s h" | "nmir (N6 h a) = N6 h a"
| "nmir (N7 h a b) = N7 h b a" | "nmir (N8 h a b c) = N8 h c b a"

text \<open>Spoke and fan constraints of a node, and the hat constraint.\<close>

fun sfit :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> pnode \<Rightarrow> bool" where
  "sfit G y (NC s h) \<longleftrightarrow> mem_range s (ar_at Pspoke G y)"
| "sfit G y (N6 h a) \<longleftrightarrow> ar_at Pspoke G y = 6 \<and> mem_range a (ar_at Pfan1 G y)"
| "sfit G y (N7 h a b) \<longleftrightarrow> ar_at Pspoke G y = 7 \<and> mem_range a (ar_at Pfan1 G y) \<and>
     mem_range b (ar_at Pfan2 G y)"
| "sfit G y (N8 h a b c) \<longleftrightarrow> ar_at Pspoke G y = 8 \<and> mem_range a (ar_at Pfan1 G y) \<and>
     mem_range b (ar_at Pfan2 G y) \<and> mem_range c (ar_at Pfan3 G y)"

definition nfit :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> pnode \<Rightarrow> bool" where
  "nfit G y c \<longleftrightarrow> sfit G y c \<and> mem_range (nhat c) (ar_at Phat G y)"

lemma fitp_plist: "fitp G x p \<longleftrightarrow> (\<forall>i < psize p. nfit G ((face G ^^ i) x) (plist p ! i))"
proof (induction p arbitrary: x)
  case Pnil then show ?case by simp
next
  case (Pcons s h p)
  show ?case
  proof
    assume a: "fitp G x (Pcons s h p)"
    show "\<forall>i < psize (Pcons s h p). nfit G ((face G ^^ i) x) (plist (Pcons s h p) ! i)"
    proof (intro allI impI)
      fix i assume "i < psize (Pcons s h p)"
      then show "nfit G ((face G ^^ i) x) (plist (Pcons s h p) ! i)"
        using a Pcons.IH[of "face G x"] by (cases i) (auto simp: nfit_def funpow_Suc_right simp del: funpow.simps)
    qed
  next
    assume a: "\<forall>i < psize (Pcons s h p). nfit G ((face G ^^ i) x) (plist (Pcons s h p) ! i)"
    have "nfit G x (NC s h)" using a[rule_format, of 0] by simp
    moreover have "fitp G (face G x) p"
      using a Pcons.IH[of "face G x"] by (auto simp: funpow_Suc_right simp del: funpow.simps)
    ultimately show "fitp G x (Pcons s h p)" by (simp add: nfit_def)
  qed
next
  case (Pcons6 h a p)
  show ?case
  proof
    assume a: "fitp G x (Pcons6 h a p)"
    show "\<forall>i < psize (Pcons6 h a p). nfit G ((face G ^^ i) x) (plist (Pcons6 h a p) ! i)"
    proof (intro allI impI)
      fix i assume "i < psize (Pcons6 h a p)"
      then show "nfit G ((face G ^^ i) x) (plist (Pcons6 h a p) ! i)"
        using a Pcons6.IH[of "face G x"] by (cases i) (auto simp: nfit_def funpow_Suc_right simp del: funpow.simps)
    qed
  next
    assume a: "\<forall>i < psize (Pcons6 h a p). nfit G ((face G ^^ i) x) (plist (Pcons6 h a p) ! i)"
    have "nfit G x (N6 h a)" using a[rule_format, of 0] by simp
    moreover have "fitp G (face G x) p"
      using a Pcons6.IH[of "face G x"] by (auto simp: funpow_Suc_right simp del: funpow.simps)
    ultimately show "fitp G x (Pcons6 h a p)" by (auto simp: nfit_def)
  qed
next
  case (Pcons7 h a b p)
  show ?case
  proof
    assume a: "fitp G x (Pcons7 h a b p)"
    show "\<forall>i < psize (Pcons7 h a b p). nfit G ((face G ^^ i) x) (plist (Pcons7 h a b p) ! i)"
    proof (intro allI impI)
      fix i assume "i < psize (Pcons7 h a b p)"
      then show "nfit G ((face G ^^ i) x) (plist (Pcons7 h a b p) ! i)"
        using a Pcons7.IH[of "face G x"] by (cases i) (auto simp: nfit_def funpow_Suc_right simp del: funpow.simps)
    qed
  next
    assume a: "\<forall>i < psize (Pcons7 h a b p). nfit G ((face G ^^ i) x) (plist (Pcons7 h a b p) ! i)"
    have "nfit G x (N7 h a b)" using a[rule_format, of 0] by simp
    moreover have "fitp G (face G x) p"
      using a Pcons7.IH[of "face G x"] by (auto simp: funpow_Suc_right simp del: funpow.simps)
    ultimately show "fitp G x (Pcons7 h a b p)" by (auto simp: nfit_def)
  qed
next
  case (Pcons8 h a b c p)
  show ?case
  proof
    assume a: "fitp G x (Pcons8 h a b c p)"
    show "\<forall>i < psize (Pcons8 h a b c p). nfit G ((face G ^^ i) x) (plist (Pcons8 h a b c p) ! i)"
    proof (intro allI impI)
      fix i assume "i < psize (Pcons8 h a b c p)"
      then show "nfit G ((face G ^^ i) x) (plist (Pcons8 h a b c p) ! i)"
        using a Pcons8.IH[of "face G x"] by (cases i) (auto simp: nfit_def funpow_Suc_right simp del: funpow.simps)
    qed
  next
    assume a: "\<forall>i < psize (Pcons8 h a b c p). nfit G ((face G ^^ i) x) (plist (Pcons8 h a b c p) ! i)"
    have "nfit G x (N8 h a b c)" using a[rule_format, of 0] by simp
    moreover have "fitp G (face G x) p"
      using a Pcons8.IH[of "face G x"] by (auto simp: funpow_Suc_right simp del: funpow.simps)
    ultimately show "fitp G x (Pcons8 h a b c p)" by (auto simp: nfit_def)
  qed
qed


section \<open>Node lists of mirror parts\<close>

fun mhats :: "prange \<Rightarrow> pnode list \<Rightarrow> pnode list" where
  "mhats h0 [] = []"
| "mhats h0 (c # cs) = nsethat (case cs of [] \<Rightarrow> h0 | c' # _ \<Rightarrow> nhat c') (nmir c) # mhats h0 cs"

lemma next_hat_plist: "next_hat h0 p = (case plist p of [] \<Rightarrow> h0 | c' # _ \<Rightarrow> nhat c')"
  by (cases p) simp_all

lemma plist_mirror_rec: "plist (mirror_part_rec h0 rp p) = rev (mhats h0 (plist p)) @ plist rp"
  by (induction h0 rp p rule: mirror_part_rec.induct) (simp_all add: next_hat_plist)

lemma plist_mirror: "plist (mirror_part p) = rev (mhats (get_hat p) (plist p))"
  using plist_mirror_rec[of "get_hat p" Pnil p] by (simp add: mirror_part_def)

lemma length_mhats [simp]: "length (mhats h0 l) = length l" by (induction l) simp_all

lemma mhats_nth: "k < length l \<Longrightarrow>
   mhats h0 l ! k = nsethat (if Suc k < length l then nhat (l ! Suc k) else h0) (nmir (l ! k))"
proof (induction l arbitrary: k)
  case Nil then show ?case by simp
next
  case (Cons c cs)
  then show ?case by (cases k; cases cs) auto
qed

lemma get_hat_plist: "p \<noteq> Pnil \<Longrightarrow> get_hat p = nhat (plist p ! 0)"
  by (cases p) (simp_all add: get_hat_def)

lemma nhat_nsethat [simp]: "nhat (nsethat h c) = h" by (cases c) simp_all

lemma nfit_split: "nfit G y (nsethat h c) \<longleftrightarrow> sfit G y (nmir (nmir c)) \<and> mem_range h (ar_at Phat G y)"
  by (cases c) (simp_all add: nfit_def)

lemma nmir_nmir [simp]: "nmir (nmir c) = c" by (cases c) simp_all

lemma sfit_sethat [simp]: "sfit G y (nsethat h c) = sfit G y c" by (cases c) simp_all

context pcp
begin

lemma inv_f: "inv f = e \<circ> n" by (rule inv_face)

lemma mirror_move: "i \<noteq> Pspoke \<Longrightarrow> subpart_loc_move i (mirror G) z =
    f (n (((e \<circ> n) ^^ (case i of Pspoke \<Rightarrow> 0 | Phat \<Rightarrow> 2 | Pfan1 \<Rightarrow> 3 | Pfan2 \<Rightarrow> 4 | Pfan3 \<Rightarrow> 5))
           (f (n z))))"
  by (cases i) (simp_all add: subpart_loc_move.simps inv_f)

lemma mirror_arity: "arity (mirror G) z = arity G z" by (simp add: F.order_inv)

lemma mir_spoke: "ar_at Pspoke (mirror G) (f y) = arity G (e y)"
  by (simp add: subpart_loc_move.simps F.order_inv)

lemma mir_k: "arity G (f (n (((e \<circ> n) ^^ (Suc (Suc k))) (f (n (f y)))))) =
    arity G (e (((e \<circ> n) ^^ (Suc (Suc k))) (e y)))"
proof -
  have a: "((e \<circ> n) ^^ (Suc (Suc k))) (f (e y)) = ((e \<circ> n) ^^ (Suc k)) (e y)"
    by (simp only: funpow_Suc_right comp_apply) simp
  have b: "e (((e \<circ> n) ^^ (Suc (Suc k))) (e y)) = n (((e \<circ> n) ^^ (Suc k)) (e y))"
    by (simp only: funpow.simps(2) comp_apply) simp
  have "arity G (f (n (((e \<circ> n) ^^ (Suc (Suc k))) (f (n (f y)))))) =
        arity G (n (((e \<circ> n) ^^ (Suc k)) (e y)))"
    by (simp only: nf a F.order_f)
  then show ?thesis by (simp only: b)
qed

lemma mir_ar: "ar_at i (mirror G) z = arity G (subpart_loc_move i (mirror G) z)"
  by (simp add: F.order_inv)

lemma mir_mv: "subpart_loc_move Phat (mirror G) z = f (n (((e \<circ> n) ^^ Suc (Suc 0)) (f (n z))))"
  "subpart_loc_move Pfan1 (mirror G) z = f (n (((e \<circ> n) ^^ Suc (Suc 1)) (f (n z))))"
  "subpart_loc_move Pfan2 (mirror G) z = f (n (((e \<circ> n) ^^ Suc (Suc 2)) (f (n z))))"
  "subpart_loc_move Pfan3 (mirror G) z = f (n (((e \<circ> n) ^^ Suc (Suc 3)) (f (n z))))"
  using mirror_move[of Phat z] mirror_move[of Pfan1 z] mirror_move[of Pfan2 z] mirror_move[of Pfan3 z]
  by (simp_all add: numeral_2_eq_2 numeral_3_eq_3 eval_nat_numeral del: funpow.simps)

lemma mir_hat: "ar_at Phat (mirror G) (f y) = ar_at Phat G (f y)"
proof -
  have "ar_at Phat (mirror G) (f y) = arity G (e (((e \<circ> n) ^^ Suc (Suc 0)) (e y)))"
    unfolding mir_ar unfolding mir_mv by (rule mir_k)
  also have "\<dots> = ar_at Phat G (f y)"
    by (simp add: subpart_loc_move.simps eval_nat_numeral fe_nn ar_ef)
  finally show ?thesis .
qed

lemma mir_fan: "ar_at Pfan1 (mirror G) (f y) = arity G (e (((e \<circ> n) ^^ 3) (e y)))"
  "ar_at Pfan2 (mirror G) (f y) = arity G (e (((e \<circ> n) ^^ 4) (e y)))"
  "ar_at Pfan3 (mirror G) (f y) = arity G (e (((e \<circ> n) ^^ 5) (e y)))"
proof -
  show "ar_at Pfan1 (mirror G) (f y) = arity G (e (((e \<circ> n) ^^ 3) (e y)))"
    unfolding mir_ar unfolding mir_mv mir_k by (simp add: numeral_3_eq_3)
  show "ar_at Pfan2 (mirror G) (f y) = arity G (e (((e \<circ> n) ^^ 4) (e y)))"
    unfolding mir_ar unfolding mir_mv mir_k by (simp add: eval_nat_numeral)
  show "ar_at Pfan3 (mirror G) (f y) = arity G (e (((e \<circ> n) ^^ 5) (e y)))"
    unfolding mir_ar unfolding mir_mv mir_k by (simp add: eval_nat_numeral)
qed

lemma rot_fan: "arity G (e y) = m \<Longrightarrow> k \<le> m \<Longrightarrow>
    arity G (e (((e \<circ> n) ^^ k) (e y))) = arity G (e ((f ^^ (m - k)) (e y)))"
  using enk[of "e y" m k] by simp

lemma sfit_mirror: "sfit (mirror G) (f y) (nmir c) \<longleftrightarrow> sfit G y c"
proof (cases c)
  case (NC s h) then show ?thesis by (simp add: mir_spoke subpart_loc_move.simps F.order_inv)
next
  case (N6 h a)
  have "arity G (e y) = 6 \<Longrightarrow> ar_at Pfan1 (mirror G) (f y) = ar_at Pfan1 G y"
    using mir_fan(1) rot_fan[of y 6 3] by (simp add: subpart_loc_move.simps)
  then show ?thesis using N6 by (auto simp: mir_spoke subpart_loc_move.simps F.order_inv)
next
  case (N7 h a b)
  have "arity G (e y) = 7 \<Longrightarrow> ar_at Pfan1 (mirror G) (f y) = ar_at Pfan2 G y \<and>
      ar_at Pfan2 (mirror G) (f y) = ar_at Pfan1 G y"
    using mir_fan(1,2) rot_fan[of y 7 3] rot_fan[of y 7 4] by (simp add: subpart_loc_move.simps)
  then show ?thesis using N7 by (auto simp: mir_spoke subpart_loc_move.simps F.order_inv)
next
  case (N8 h a b cc)
  have "arity G (e y) = 8 \<Longrightarrow> ar_at Pfan1 (mirror G) (f y) = ar_at Pfan3 G y \<and>
      ar_at Pfan2 (mirror G) (f y) = ar_at Pfan2 G y \<and> ar_at Pfan3 (mirror G) (f y) = ar_at Pfan1 G y"
    using mir_fan rot_fan[of y 8 3] rot_fan[of y 8 4] rot_fan[of y 8 5] by (simp add: subpart_loc_move.simps)
  then show ?thesis using N8 by (auto simp: mir_spoke subpart_loc_move.simps F.order_inv)
qed

lemma nfit_mirror:
  "nfit (mirror G) (f y) (nsethat h (nmir c)) \<longleftrightarrow> sfit G y c \<and> mem_range h (ar_at Phat G (f y))"
  using sfit_mirror[of y c] mir_hat[of y] by (simp add: nfit_def)

lemma reidx1: "(\<forall>i < (a::nat). P (a - 1 - i)) \<longleftrightarrow> (\<forall>k < a. P k)"
proof
  assume h: "\<forall>i < a. P (a - 1 - i)"
  show "\<forall>k < a. P k"
  proof (intro allI impI)
    fix k assume k: "k < a"
    have "a - 1 - k < a" using k by linarith
    then have "P (a - 1 - (a - 1 - k))" using h by blast
    moreover have "a - 1 - (a - 1 - k) = k" using k by simp
    ultimately show "P k" by simp
  qed
qed simp

lemma reidx2: "0 < (a::nat) \<Longrightarrow> (\<forall>i < a. Q ((a - i) mod a)) \<longleftrightarrow> (\<forall>k < a. Q k)"
proof
  assume a: "0 < a" and h: "\<forall>i < a. Q ((a - i) mod a)"
  show "\<forall>k < a. Q k"
  proof (intro allI impI)
    fix k assume k: "k < a"
    show "Q k"
    proof (cases k)
      case 0 then show ?thesis using h a by (metis diff_zero mod_self)
    next
      case (Suc j)
      have i: "a - k < a" using k Suc by linarith
      then have "Q ((a - (a - k)) mod a)" using h by blast
      moreover have "(a - (a - k)) mod a = k" using k by simp
      ultimately show ?thesis by simp
    qed
  qed
qed simp

theorem fitp_mirror:
  assumes xD: "x \<in> D" and a: "arity G x = psize p"
  shows "fitp (mirror G) x (mirror_part p) \<longleftrightarrow> fitp G x p"
proof -
  define l where "l = plist p"
  define m where "m = psize p"
  have lm: "length l = m" by (simp add: l_def m_def length_plist)
  have m0: "0 < m" using pentaG[OF xD] a by (simp add: m_def)
  then have pne: "p \<noteq> Pnil" by (auto simp: m_def)
  have h0: "get_hat p = nhat (l ! 0)" using get_hat_plist[OF pne] by (simp add: l_def)
  have am: "arity G x = m" using a by (simp add: m_def)
  have inv_pow: "((inv f) ^^ i) x = (f ^^ (m - i)) x" if "i \<le> m" for i
    using enk[OF am that] by (simp add: inv_f)
  have node: "rev (mhats (get_hat p) l) ! i =
      nsethat (nhat (l ! ((m - i) mod m))) (nmir (l ! (m - 1 - i)))" if i: "i < m" for i
  proof -
    have "rev (mhats (get_hat p) l) ! i = mhats (get_hat p) l ! (m - 1 - i)"
      using i lm by (simp add: rev_nth)
    also have "\<dots> = nsethat (if Suc (m - 1 - i) < m then nhat (l ! Suc (m - 1 - i)) else get_hat p)
        (nmir (l ! (m - 1 - i)))" using mhats_nth[of "m - 1 - i" l] i lm by simp
    also have "(if Suc (m - 1 - i) < m then nhat (l ! Suc (m - 1 - i)) else get_hat p) = nhat (l ! ((m - i) mod m))"
    proof (cases i)
      case 0 then show ?thesis using i h0 by simp
    next
      case (Suc j)
      then have "Suc (m - 1 - i) = m - i" "Suc (m - 1 - i) < m" "(m - i) mod m = m - i" using i by auto
      then show ?thesis by simp
    qed
    finally show ?thesis .
  qed
  have fy: "f ((f ^^ (m - 1 - i)) x) = (f ^^ ((m - i) mod m)) x" if i: "i < m" for i
  proof -
    have mi: "m - i = Suc (m - 1 - i)" using i by simp
    have "f ((f ^^ (m - 1 - i)) x) = (f ^^ (m - i)) x" by (simp only: mi funpow.simps(2) comp_apply)
    also have "\<dots> = (f ^^ ((m - i) mod m)) x" using F.funpow_mod_order[of "m - i" x] am by simp
    finally show ?thesis .
  qed
  have Hk: "ar_at Phat G ((f ^^ ((m - i) mod m)) x) = ar_at Phat G ((f ^^ ((m - i) mod m)) x)" for i ..
  have "fitp (mirror G) x (mirror_part p) \<longleftrightarrow>
      (\<forall>i < m. nfit (mirror G) (((inv f) ^^ i) x) (rev (mhats (get_hat p) l) ! i))"
    using fitp_plist[of "mirror G" x "mirror_part p"] by (simp add: psize_mirror plist_mirror l_def m_def)
  also have "\<dots> \<longleftrightarrow> (\<forall>i < m. sfit G ((f ^^ (m - 1 - i)) x) (l ! (m - 1 - i)) \<and>
        mem_range (nhat (l ! ((m - i) mod m))) (ar_at Phat G ((f ^^ ((m - i) mod m)) x)))"
  proof -
    have "nfit (mirror G) (((inv f) ^^ i) x) (rev (mhats (get_hat p) l) ! i) \<longleftrightarrow>
        sfit G ((f ^^ (m - 1 - i)) x) (l ! (m - 1 - i)) \<and>
        mem_range (nhat (l ! ((m - i) mod m))) (ar_at Phat G ((f ^^ ((m - i) mod m)) x))" if i: "i < m" for i
    proof -
      have mi: "m - i = Suc (m - 1 - i)" using i by simp
      have "((inv f) ^^ i) x = (f ^^ (m - i)) x" using inv_pow[of i] i by simp
      also have "\<dots> = f ((f ^^ (m - 1 - i)) x)" by (simp only: mi funpow.simps(2) comp_apply)
      finally have "((inv f) ^^ i) x = f ((f ^^ (m - 1 - i)) x)" .
      then show ?thesis using nfit_mirror[of "(f ^^ (m - 1 - i)) x" "nhat (l ! ((m - i) mod m))" "l ! (m - 1 - i)"]
        node[OF i] fy[OF i] by simp
    qed
    then show ?thesis by auto
  qed
  also have "\<dots> \<longleftrightarrow> (\<forall>k < m. sfit G ((f ^^ k) x) (l ! k)) \<and>
        (\<forall>k < m. mem_range (nhat (l ! k)) (ar_at Phat G ((f ^^ k) x)))"
    using reidx1[of m "\<lambda>k. sfit G ((f ^^ k) x) (l ! k)"]
      reidx2[OF m0, of "\<lambda>k. mem_range (nhat (l ! k)) (ar_at Phat G ((f ^^ k) x))"] by blast
  also have "\<dots> \<longleftrightarrow> fitp G x p"
    using fitp_plist[of G x p] by (auto simp: nfit_def l_def m_def)
  finally show ?thesis .
qed

theorem exact_fitp_mirror:
  assumes xD: "x \<in> D"
  shows "exact_fitp (mirror G) x (mirror_part p) \<longleftrightarrow> exact_fitp G x p"
  using fitp_mirror[OF xD] by (auto simp: exact_fitp_def psize_mirror F.order_inv)

end

end
