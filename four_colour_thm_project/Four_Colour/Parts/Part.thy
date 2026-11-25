(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Part.thy
    Parts: arity ranges for the faces around a hub, used to describe sets of neighbourhoods
    in the unavoidability proof (part.v).
    Ported from G. Gonthier's Coq development (part.v).

    Design: the range comparison and intersection tables of part.v are replaced by their
    semantic definitions via interval bounds (every prange is an interval [lo, hi], hi possibly
    infinite); they are at least as precise as Gonthier's tables.
*)
theory Part
  imports Four_Colour_Maps.Quiztree
begin

section \<open>Ranges\<close>

datatype prange = Pr55 | Pr66 | Pr77 | Pr88 | Pr99 | Pr56 | Pr67 | Pr78 | Pr89
  | Pr57 | Pr68 | Pr79 | Pr58 | Pr69 | Pr59

fun plo :: "prange \<Rightarrow> nat" where
  "plo Pr55 = 5" | "plo Pr66 = 6" | "plo Pr77 = 7" | "plo Pr88 = 8" | "plo Pr99 = 9"
| "plo Pr56 = 5" | "plo Pr67 = 6" | "plo Pr78 = 7" | "plo Pr89 = 8"
| "plo Pr57 = 5" | "plo Pr68 = 6" | "plo Pr79 = 7" | "plo Pr58 = 5" | "plo Pr69 = 6"
| "plo Pr59 = 5"

fun phi :: "prange \<Rightarrow> nat option" where
  "phi Pr55 = Some 5" | "phi Pr66 = Some 6" | "phi Pr77 = Some 7" | "phi Pr88 = Some 8"
| "phi Pr99 = None" | "phi Pr56 = Some 6" | "phi Pr67 = Some 7" | "phi Pr78 = Some 8"
| "phi Pr89 = None" | "phi Pr57 = Some 7" | "phi Pr68 = Some 8" | "phi Pr79 = None"
| "phi Pr58 = Some 8" | "phi Pr69 = None" | "phi Pr59 = None"

definition mem_range :: "prange \<Rightarrow> nat \<Rightarrow> bool" where
  "mem_range r n \<longleftrightarrow> plo r \<le> n \<and> (case phi r of None \<Rightarrow> True | Some b \<Rightarrow> n \<le> b)"

definition prange_of :: "nat \<Rightarrow> nat option \<Rightarrow> prange" where
  "prange_of lo hi = (case hi of
      None \<Rightarrow> (if lo \<le> 5 then Pr59 else if lo = 6 then Pr69 else if lo = 7 then Pr79
               else if lo = 8 then Pr89 else Pr99)
    | Some b \<Rightarrow> (if lo \<le> 5 then (if b \<le> 5 then Pr55 else if b = 6 then Pr56 else if b = 7 then Pr57 else Pr58)
               else if lo = 6 then (if b \<le> 6 then Pr66 else if b = 7 then Pr67 else Pr68)
               else if lo = 7 then (if b \<le> 7 then Pr77 else Pr78)
               else Pr88))"

definition hi_le :: "nat option \<Rightarrow> nat option \<Rightarrow> bool" where
  "hi_le a b = (case b of None \<Rightarrow> True | Some y \<Rightarrow> (case a of None \<Rightarrow> False | Some x \<Rightarrow> x \<le> y))"

definition hi_min :: "nat option \<Rightarrow> nat option \<Rightarrow> nat option" where
  "hi_min a b = (case a of None \<Rightarrow> b | Some x \<Rightarrow> (case b of None \<Rightarrow> Some x | Some y \<Rightarrow> Some (min x y)))"

definition lo_le_hi :: "nat \<Rightarrow> nat option \<Rightarrow> bool" where
  "lo_le_hi l h = (case h of None \<Rightarrow> True | Some y \<Rightarrow> l \<le> y)"

datatype part_rel = Pdisjoint | Pstraddle | Psubset

fun apply_part_rel :: "part_rel \<Rightarrow> bool \<Rightarrow> bool" where
  "apply_part_rel Pdisjoint b = False" | "apply_part_rel Psubset b = True"
| "apply_part_rel Pstraddle b = b"

fun notPsubset :: "part_rel \<Rightarrow> part_rel" where
  "notPsubset Psubset = Pstraddle" | "notPsubset c = c"

fun meet_prel :: "part_rel \<Rightarrow> part_rel \<Rightarrow> part_rel" where
  "meet_prel Pdisjoint c' = Pdisjoint" | "meet_prel Psubset c' = c'"
| "meet_prel Pstraddle c' = notPsubset c'"

definition cmp_range :: "prange \<Rightarrow> prange \<Rightarrow> part_rel" where
  "cmp_range r r' =
    (if plo r' \<le> plo r \<and> hi_le (phi r) (phi r') then Psubset
     else if lo_le_hi (max (plo r) (plo r')) (hi_min (phi r) (phi r')) then Pstraddle
     else Pdisjoint)"

definition meet_range :: "prange \<Rightarrow> prange \<Rightarrow> prange" where
  "meet_range r r' =
    (let lo = max (plo r) (plo r'); hi = hi_min (phi r) (phi r') in
     if lo_le_hi lo hi then prange_of lo hi else r')"

lemma mem_range_simps [simp]:
  "mem_range Pr55 n \<longleftrightarrow> n = 5" "mem_range Pr66 n \<longleftrightarrow> n = 6" "mem_range Pr77 n \<longleftrightarrow> n = 7"
  "mem_range Pr88 n \<longleftrightarrow> n = 8" "mem_range Pr59 n \<longleftrightarrow> 5 \<le> n"
  by (auto simp: mem_range_def)

text \<open>Every range has its lower bound at least 5 and its finite upper bound at most 8.\<close>

lemma plo_ge5: "5 \<le> plo r" by (cases r) simp_all
lemma phi_le8: "phi r = Some b \<Longrightarrow> b \<le> 8" by (cases r) auto
lemma phi_ge: "phi r = Some b \<Longrightarrow> plo r \<le> b" by (cases r) auto

lemma mem_cmp_range:
  assumes r1: "mem_range r1 n"
  shows "mem_range r2 n = apply_part_rel (cmp_range r1 r2) (mem_range r2 n)"
  using r1
  by (cases r1; cases r2) (auto simp: cmp_range_def mem_range_def hi_le_def hi_min_def lo_le_hi_def)

lemma mem_meet_range: "mem_range r1 n \<Longrightarrow> mem_range r2 n \<Longrightarrow> mem_range (meet_range r1 r2) n"
  by (cases r1; cases r2) (auto simp: meet_range_def mem_range_def hi_min_def lo_le_hi_def prange_of_def)

section \<open>Parts\<close>

datatype part =
    Pnil
  | Pcons prange prange part
  | Pcons6 prange prange part
  | Pcons7 prange prange prange part
  | Pcons8 prange prange prange prange part

datatype subpart_loc = Pspoke | Phat | Pfan1 | Pfan2 | Pfan3

definition pcons_s :: "prange \<Rightarrow> part \<Rightarrow> part" where "pcons_s s = Pcons s Pr59"

definition pcons_any :: "nat \<Rightarrow> part" where "pcons_any n = (Pcons Pr59 Pr59 ^^ n) Pnil"

fun psize :: "part \<Rightarrow> nat" where
  "psize Pnil = 0"
| "psize (Pcons _ _ p) = Suc (psize p)"
| "psize (Pcons6 _ _ p) = Suc (psize p)"
| "psize (Pcons7 _ _ _ p) = Suc (psize p)"
| "psize (Pcons8 _ _ _ _ p) = Suc (psize p)"

fun drop_part :: "nat \<Rightarrow> part \<Rightarrow> part" where
  "drop_part (Suc n) (Pcons _ _ p) = drop_part n p"
| "drop_part (Suc n) (Pcons6 _ _ p) = drop_part n p"
| "drop_part (Suc n) (Pcons7 _ _ _ p) = drop_part n p"
| "drop_part (Suc n) (Pcons8 _ _ _ _ p) = drop_part n p"
| "drop_part _ p = p"

fun take_part :: "nat \<Rightarrow> part \<Rightarrow> part" where
  "take_part (Suc n) (Pcons s h p) = Pcons s h (take_part n p)"
| "take_part (Suc n) (Pcons6 h f1 p) = Pcons6 h f1 (take_part n p)"
| "take_part (Suc n) (Pcons7 h f1 f2 p) = Pcons7 h f1 f2 (take_part n p)"
| "take_part (Suc n) (Pcons8 h f1 f2 f3 p) = Pcons8 h f1 f2 f3 (take_part n p)"
| "take_part _ _ = Pnil"

fun cat_part :: "part \<Rightarrow> part \<Rightarrow> part" where
  "cat_part (Pcons s h p) q = Pcons s h (cat_part p q)"
| "cat_part (Pcons6 h f1 p) q = Pcons6 h f1 (cat_part p q)"
| "cat_part (Pcons7 h f1 f2 p) q = Pcons7 h f1 f2 (cat_part p q)"
| "cat_part (Pcons8 h f1 f2 f3 p) q = Pcons8 h f1 f2 f3 (cat_part p q)"
| "cat_part Pnil q = q"

definition rot_part :: "nat \<Rightarrow> part \<Rightarrow> part" where
  "rot_part n p = cat_part (drop_part n p) (take_part n p)"

lemma psize_cat: "psize (cat_part p1 p2) = psize p1 + psize p2"
  by (induction p1) simp_all

lemma psize_drop: "psize (drop_part n p) = psize p - n"
  by (induction n p rule: drop_part.induct) simp_all

lemma cat_take_drop_part: "cat_part (take_part n p) (drop_part n p) = p"
  by (induction n p rule: take_part.induct) simp_all

lemma psize_take: "n \<le> psize p \<Longrightarrow> psize (take_part n p) = n"
  by (induction n p rule: take_part.induct) simp_all

lemma psize_rot: "psize (rot_part n p) = psize p"
  using psize_cat[of "take_part n p" "drop_part n p"]
  by (simp add: rot_part_def psize_cat cat_take_drop_part)

fun catrev_part :: "part \<Rightarrow> part \<Rightarrow> part" where
  "catrev_part Pnil p2 = p2"
| "catrev_part (Pcons s h p1) p2 = catrev_part p1 (Pcons s h p2)"
| "catrev_part (Pcons6 h f1 p1) p2 = catrev_part p1 (Pcons6 h f1 p2)"
| "catrev_part (Pcons7 h f1 f2 p1) p2 = catrev_part p1 (Pcons7 h f1 f2 p2)"
| "catrev_part (Pcons8 h f1 f2 f3 p1) p2 = catrev_part p1 (Pcons8 h f1 f2 f3 p2)"

definition rev_part :: "part \<Rightarrow> part" where "rev_part p = catrev_part p Pnil"

lemma catrev_part_cat: "catrev_part p1 (cat_part p2 p3) = cat_part (catrev_part p1 p2) p3"
  by (induction p1 arbitrary: p2) (simp_all flip: cat_part.simps)

lemma catrev_part_eq: "catrev_part p1 p2 = cat_part (catrev_part p1 Pnil) p2"
  using catrev_part_cat[of p1 Pnil p2] by simp

lemma psize_catrev: "psize (catrev_part p1 p2) = psize p1 + psize p2"
  by (induction p1 arbitrary: p2) simp_all

lemma psize_rev: "psize (rev_part p) = psize p"
  by (simp add: rev_part_def psize_catrev)

section \<open>Accessors and mirror images\<close>

fun get_spoke :: "part \<Rightarrow> prange" where
  "get_spoke (Pcons s _ _) = s" | "get_spoke (Pcons6 _ _ _) = Pr66"
| "get_spoke (Pcons7 _ _ _ _) = Pr77" | "get_spoke (Pcons8 _ _ _ _ _) = Pr88"
| "get_spoke Pnil = Pr59"

fun next_hat :: "prange \<Rightarrow> part \<Rightarrow> prange" where
  "next_hat h0 Pnil = h0" | "next_hat h0 (Pcons _ h _) = h" | "next_hat h0 (Pcons6 h _ _) = h"
| "next_hat h0 (Pcons7 h _ _ _) = h" | "next_hat h0 (Pcons8 h _ _ _ _) = h"

definition get_hat :: "part \<Rightarrow> prange" where "get_hat = next_hat Pr59"

fun get_fan1r :: "part \<Rightarrow> prange" where
  "get_fan1r (Pcons6 _ f1 _) = f1" | "get_fan1r (Pcons7 _ f1 _ _) = f1"
| "get_fan1r (Pcons8 _ f1 _ _ _) = f1" | "get_fan1r _ = Pr59"

fun get_fan2r :: "part \<Rightarrow> prange" where
  "get_fan2r (Pcons7 _ _ f2 _) = f2" | "get_fan2r (Pcons8 _ _ f2 _ _) = f2" | "get_fan2r _ = Pr59"

fun get_fan3r :: "part \<Rightarrow> prange" where
  "get_fan3r (Pcons8 _ _ _ f3 _) = f3" | "get_fan3r _ = Pr59"

fun get_fan1l :: "part \<Rightarrow> prange" where
  "get_fan1l (Pcons6 _ f1 _) = f1" | "get_fan1l (Pcons7 _ _ f2 _) = f2"
| "get_fan1l (Pcons8 _ _ _ f3 _) = f3" | "get_fan1l _ = Pr59"

fun get_fan2l :: "part \<Rightarrow> prange" where
  "get_fan2l (Pcons7 _ f1 _ _) = f1" | "get_fan2l (Pcons8 _ _ f2 _ _) = f2" | "get_fan2l _ = Pr59"

fun get_fan3l :: "part \<Rightarrow> prange" where
  "get_fan3l (Pcons8 _ f1 _ _ _) = f1" | "get_fan3l _ = Pr59"

fun mirror_part_rec :: "prange \<Rightarrow> part \<Rightarrow> part \<Rightarrow> part" where
  "mirror_part_rec h0 rp Pnil = rp"
| "mirror_part_rec h0 rp (Pcons s _ p') = mirror_part_rec h0 (Pcons s (next_hat h0 p') rp) p'"
| "mirror_part_rec h0 rp (Pcons6 _ f1 p') = mirror_part_rec h0 (Pcons6 (next_hat h0 p') f1 rp) p'"
| "mirror_part_rec h0 rp (Pcons7 _ f1 f2 p') = mirror_part_rec h0 (Pcons7 (next_hat h0 p') f2 f1 rp) p'"
| "mirror_part_rec h0 rp (Pcons8 _ f1 f2 f3 p') =
     mirror_part_rec h0 (Pcons8 (next_hat h0 p') f3 f2 f1 rp) p'"

definition mirror_part :: "part \<Rightarrow> part" where
  "mirror_part p = mirror_part_rec (get_hat p) Pnil p"

lemma psize_mirror_rec: "psize (mirror_part_rec h0 q p) = psize p + psize q"
  by (induction h0 q p rule: mirror_part_rec.induct) simp_all

lemma psize_mirror: "psize (mirror_part p) = psize p"
  by (simp add: mirror_part_def psize_mirror_rec)

section \<open>Converse parts\<close>

fun conv_part12 :: "part \<Rightarrow> prange \<times> (part \<Rightarrow> part)" where
  "conv_part12 (Pcons s2 s1 (Pcons h23 f2 _)) =
     (if f2 = Pr59 then (h23, \<lambda>q. pcons_s s1 (pcons_s s2 q))
      else if s2 = Pr55 then (h23, \<lambda>q. pcons_s s1 (Pcons Pr55 f2 q))
      else if s2 = Pr66 then (h23, \<lambda>q. pcons_s s1 (Pcons6 Pr59 f2 q))
      else if s2 = Pr77 then (h23, \<lambda>q. pcons_s s1 (Pcons7 Pr59 Pr59 f2 q))
      else (Pr59, \<lambda>_. Pnil))"
| "conv_part12 (Pcons6 s1 h12 (Pcons h23 f21 _)) = (h23, \<lambda>q. pcons_s s1 (Pcons6 h12 f21 q))"
| "conv_part12 (Pcons7 s1 h12 f21 (Pcons h23 f22 _)) = (h23, \<lambda>q. pcons_s s1 (Pcons7 h12 f21 f22 q))"
| "conv_part12 _ = (Pr59, \<lambda>_. Pnil)"

fun conv_part3 :: "prange \<Rightarrow> part \<Rightarrow> part \<Rightarrow> part" where
  "conv_part3 h23 Pnil = Pcons Pr55 h23"
| "conv_part3 h23 (Pcons _ _ Pnil) = Pcons Pr66 h23"
| "conv_part3 h23 (Pcons f31 _ (Pcons f32 _ Pnil)) =
     (if f31 = Pr59 \<and> f32 = Pr59 then Pcons Pr77 h23 else Pcons7 h23 f31 f32)"
| "conv_part3 h23 (Pcons f31 _ (Pcons f32 _ (Pcons f33 _ Pnil))) = Pcons8 h23 f31 f32 f33"
| "conv_part3 h23 _ = (\<lambda>_. Pnil)"

fun conv_part4 :: "part \<Rightarrow> prange \<times> (part \<Rightarrow> part)" where
  "conv_part4 (Pcons h34 _ (Pcons s4 f41 _)) =
     (if f41 = Pr59 then (Pr59, Pcons s4 h34)
      else if s4 = Pr55 then (f41, Pcons Pr55 h34)
      else if s4 = Pr66 then (Pr59, Pcons6 h34 f41)
      else if s4 = Pr77 then (Pr59, Pcons7 h34 f41 Pr59)
      else (Pr59, \<lambda>_. Pnil))"
| "conv_part4 (Pcons h34 _ (Pcons6 f41 h45 _)) = (h45, Pcons6 h34 f41)"
| "conv_part4 (Pcons h34 _ (Pcons7 f41 f42 h45 _)) = (h45, Pcons7 h34 f41 f42)"
| "conv_part4 _ = (Pr59, \<lambda>_. Pnil)"

fun conv_part5 :: "prange \<Rightarrow> part \<Rightarrow> prange \<times> part" where
  "conv_part5 h45 (Pcons u s5 _) = (u, Pcons s5 h45 Pnil)"
| "conv_part5 h45 (Pcons7 s5 s6 s7 _) = (Pr77, Pcons s5 h45 (pcons_s s6 (pcons_s s7 Pnil)))"
| "conv_part5 h45 _ = (Pr59, Pnil)"

definition converse_part :: "part \<Rightarrow> prange \<times> part" where
  "converse_part p1 =
    (case conv_part4 p1 of (h45, q4) \<Rightarrow>
     case conv_part5 h45 (drop_part 2 p1) of (u, q5) \<Rightarrow>
     case conv_part12 (drop_part 3 p1) of (h23, q12) \<Rightarrow>
     (u, q12 (conv_part3 h23 (drop_part 5 p1) (q4 q5))))"

section \<open>Splitting parts\<close>

definition prange_lo :: "nat \<Rightarrow> prange" where
  "prange_lo k = (if k = 5 then Pr55 else if k = 6 then Pr56 else if k = 7 then Pr57
                  else if k = 8 then Pr58 else Pr59)"

definition prange_hi :: "nat \<Rightarrow> prange" where
  "prange_hi k = (if k = 5 then Pr69 else if k = 6 then Pr79 else if k = 7 then Pr89
                  else if k = 8 then Pr99 else Pr59)"

definition good_rsplit :: "nat \<Rightarrow> prange \<Rightarrow> bool" where
  "good_rsplit k r \<longleftrightarrow> cmp_range r (prange_lo k) = Pstraddle"

definition split_range :: "nat \<Rightarrow> bool \<Rightarrow> prange \<Rightarrow> prange" where
  "split_range k lo r = meet_range (if lo then prange_lo k else prange_hi k) r"

lemma fit_split_range:
  assumes "good_rsplit k r"
  shows "mem_range (split_range k lo r) a \<longleftrightarrow> (lo \<noteq> (k < a)) \<and> mem_range r a"
  using assms
  by (cases r; cases lo) (auto simp: good_rsplit_def split_range_def cmp_range_def meet_range_def
      prange_lo_def prange_hi_def mem_range_def hi_le_def hi_min_def lo_le_hi_def prange_of_def
      split: if_splits)

fun good_head :: "subpart_loc \<Rightarrow> nat \<Rightarrow> part \<Rightarrow> bool" where
  "good_head Pspoke k (Pcons s _ _) = good_rsplit k s"
| "good_head Phat k (Pcons s h _) = good_rsplit k h"
| "good_head Phat k (Pcons6 h _ _) = good_rsplit k h"
| "good_head Phat k (Pcons7 h _ _ _) = good_rsplit k h"
| "good_head Phat k (Pcons8 h _ _ _ _) = good_rsplit k h"
| "good_head Pfan1 k (Pcons6 _ f1 _) = good_rsplit k f1"
| "good_head Pfan1 k (Pcons s _ _) = ((s = Pr66 \<or> s = Pr77 \<or> s = Pr88) \<and> good_rsplit k Pr59)"
| "good_head Pfan1 k (Pcons7 _ f1 _ _) = good_rsplit k f1"
| "good_head Pfan1 k (Pcons8 _ f1 _ _ _) = good_rsplit k f1"
| "good_head Pfan2 k (Pcons7 _ _ f2 _) = good_rsplit k f2"
| "good_head Pfan2 k (Pcons s _ _) = ((s = Pr77 \<or> s = Pr88) \<and> good_rsplit k Pr59)"
| "good_head Pfan2 k (Pcons8 _ _ f2 _ _) = good_rsplit k f2"
| "good_head Pfan3 k (Pcons8 _ _ _ f3 _) = good_rsplit k f3"
| "good_head Pfan3 k (Pcons s _ _) = (s = Pr88 \<and> good_rsplit k Pr59)"
| "good_head _ _ _ = False"

definition good_split :: "subpart_loc \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> part \<Rightarrow> bool" where
  "good_split i j k p = good_head i k (drop_part j p)"

fun split_head :: "subpart_loc \<Rightarrow> (prange \<Rightarrow> prange) \<Rightarrow> part \<Rightarrow> part" where
  "split_head Pspoke sr (Pcons s h p') = Pcons (sr s) h p'"
| "split_head Phat sr (Pcons s h p') = Pcons s (sr h) p'"
| "split_head Phat sr (Pcons6 h f1 p') = Pcons6 (sr h) f1 p'"
| "split_head Phat sr (Pcons7 h f1 f2 p') = Pcons7 (sr h) f1 f2 p'"
| "split_head Phat sr (Pcons8 h f1 f2 f3 p') = Pcons8 (sr h) f1 f2 f3 p'"
| "split_head Pfan1 sr (Pcons6 h f1 p') = Pcons6 h (sr f1) p'"
| "split_head Pfan1 sr (Pcons s h p') =
     (if s = Pr66 then Pcons6 h (sr Pr59) p' else if s = Pr77 then Pcons7 h (sr Pr59) Pr59 p'
      else if s = Pr88 then Pcons8 h (sr Pr59) Pr59 Pr59 p' else Pcons s h p')"
| "split_head Pfan1 sr (Pcons7 h f1 f2 p') = Pcons7 h (sr f1) f2 p'"
| "split_head Pfan1 sr (Pcons8 h f1 f2 f3 p') = Pcons8 h (sr f1) f2 f3 p'"
| "split_head Pfan2 sr (Pcons7 h f1 f2 p') = Pcons7 h f1 (sr f2) p'"
| "split_head Pfan2 sr (Pcons s h p') =
     (if s = Pr77 then Pcons7 h Pr59 (sr Pr59) p' else if s = Pr88 then Pcons8 h Pr59 (sr Pr59) Pr59 p'
      else Pcons s h p')"
| "split_head Pfan2 sr (Pcons8 h f1 f2 f3 p') = Pcons8 h f1 (sr f2) f3 p'"
| "split_head Pfan3 sr (Pcons8 h f1 f2 f3 p') = Pcons8 h f1 f2 (sr f3) p'"
| "split_head Pfan3 sr (Pcons s h p') = (if s = Pr88 then Pcons8 h Pr59 Pr59 (sr Pr59) p' else Pcons s h p')"
| "split_head _ _ q = q"

definition split_part :: "subpart_loc \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> part \<Rightarrow> part" where
  "split_part i j k lo p =
     (if good_split i j k p then cat_part (take_part j p) (split_head i (split_range k lo) (drop_part j p))
      else p)"

section \<open>Comparing and intersecting parts\<close>

fun cmp_part :: "part \<Rightarrow> part \<Rightarrow> part_rel" where
  "cmp_part p Pnil = Psubset"
| "cmp_part (Pcons sp hp p') (Pcons sq hq q') =
     meet_prel (cmp_range sp sq) (meet_prel (cmp_range hp hq) (cmp_part p' q'))"
| "cmp_part (Pcons6 hp _ p') (Pcons sq hq q') =
     meet_prel (cmp_range Pr66 sq) (meet_prel (cmp_range hp hq) (cmp_part p' q'))"
| "cmp_part (Pcons7 hp _ _ p') (Pcons sq hq q') =
     meet_prel (cmp_range Pr77 sq) (meet_prel (cmp_range hp hq) (cmp_part p' q'))"
| "cmp_part (Pcons8 hp _ _ _ p') (Pcons sq hq q') =
     meet_prel (cmp_range Pr88 sq) (meet_prel (cmp_range hp hq) (cmp_part p' q'))"
| "cmp_part (Pcons sp hp p') (Pcons6 hq _ q') =
     meet_prel (notPsubset (cmp_range sp Pr66)) (meet_prel (cmp_range hp hq) (cmp_part p' q'))"
| "cmp_part (Pcons sp hp p') (Pcons7 hq _ _ q') =
     meet_prel (notPsubset (cmp_range sp Pr77)) (meet_prel (cmp_range hp hq) (cmp_part p' q'))"
| "cmp_part (Pcons sp hp p') (Pcons8 hq _ _ _ q') =
     meet_prel (notPsubset (cmp_range sp Pr88)) (meet_prel (cmp_range hp hq) (cmp_part p' q'))"
| "cmp_part (Pcons6 hp f1p p') (Pcons6 hq f1q q') =
     meet_prel (cmp_range hp hq) (meet_prel (cmp_range f1p f1q) (cmp_part p' q'))"
| "cmp_part (Pcons7 hp f1p f2p p') (Pcons7 hq f1q f2q q') =
     meet_prel (cmp_range hp hq) (meet_prel (cmp_range f1p f1q)
       (meet_prel (cmp_range f2p f2q) (cmp_part p' q')))"
| "cmp_part (Pcons8 hp f1p f2p f3p p') (Pcons8 hq f1q f2q f3q q') =
     meet_prel (cmp_range hp hq) (meet_prel (cmp_range f1p f1q)
       (meet_prel (cmp_range f2p f2q) (meet_prel (cmp_range f3p f3q) (cmp_part p' q'))))"
| "cmp_part Pnil _ = Pstraddle"
| "cmp_part _ _ = Pdisjoint"

fun meet_part :: "part \<Rightarrow> part \<Rightarrow> part" where
  "meet_part (Pcons sp hp p') (Pcons sq hq q') =
     Pcons (meet_range sp sq) (meet_range hp hq) (meet_part p' q')"
| "meet_part (Pcons6 hp f1 p') (Pcons sq hq q') = Pcons6 (meet_range hp hq) f1 (meet_part p' q')"
| "meet_part (Pcons7 hp f1 f2 p') (Pcons sq hq q') = Pcons7 (meet_range hp hq) f1 f2 (meet_part p' q')"
| "meet_part (Pcons8 hp f1 f2 f3 p') (Pcons sq hq q') =
     Pcons8 (meet_range hp hq) f1 f2 f3 (meet_part p' q')"
| "meet_part (Pcons sp hp p') (Pcons6 hq f1 q') = Pcons6 (meet_range hp hq) f1 (meet_part p' q')"
| "meet_part (Pcons sp hp p') (Pcons7 hq f1 f2 q') = Pcons7 (meet_range hp hq) f1 f2 (meet_part p' q')"
| "meet_part (Pcons sp hp p') (Pcons8 hq f1 f2 f3 q') =
     Pcons8 (meet_range hp hq) f1 f2 f3 (meet_part p' q')"
| "meet_part (Pcons6 hp f1p p') (Pcons6 hq f1q q') =
     Pcons6 (meet_range hp hq) (meet_range f1p f1q) (meet_part p' q')"
| "meet_part (Pcons7 hp f1p f2p p') (Pcons7 hq f1q f2q q') =
     Pcons7 (meet_range hp hq) (meet_range f1p f1q) (meet_range f2p f2q) (meet_part p' q')"
| "meet_part (Pcons8 hp f1p f2p f3p p') (Pcons8 hq f1q f2q f3q q') =
     Pcons8 (meet_range hp hq) (meet_range f1p f1q) (meet_range f2p f2q) (meet_range f3p f3q)
       (meet_part p' q')"
| "meet_part p _ = p"

section \<open>Fitting parts\<close>

fun subpart_loc_move :: "subpart_loc \<Rightarrow> 'a hypermap \<Rightarrow> 'a \<Rightarrow> 'a" where
  "subpart_loc_move Pspoke G x = edge G x"
| "subpart_loc_move Phat G x = edge G ((face G ^^ 2) (edge G x))"
| "subpart_loc_move Pfan1 G x = edge G ((face G ^^ 3) (edge G x))"
| "subpart_loc_move Pfan2 G x = edge G ((face G ^^ 4) (edge G x))"
| "subpart_loc_move Pfan3 G x = edge G ((face G ^^ 5) (edge G x))"

abbreviation ar_at :: "subpart_loc \<Rightarrow> 'a hypermap \<Rightarrow> 'a \<Rightarrow> nat" where
  "ar_at i G x \<equiv> arity G (subpart_loc_move i G x)"

fun fitp :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> part \<Rightarrow> bool" where
  "fitp G x Pnil = True"
| "fitp G x (Pcons s h p') \<longleftrightarrow>
     mem_range s (ar_at Pspoke G x) \<and> mem_range h (ar_at Phat G x) \<and> fitp G (face G x) p'"
| "fitp G x (Pcons6 h f1 p') \<longleftrightarrow>
     ar_at Pspoke G x = 6 \<and> mem_range h (ar_at Phat G x) \<and> mem_range f1 (ar_at Pfan1 G x) \<and>
     fitp G (face G x) p'"
| "fitp G x (Pcons7 h f1 f2 p') \<longleftrightarrow>
     ar_at Pspoke G x = 7 \<and> mem_range h (ar_at Phat G x) \<and> mem_range f1 (ar_at Pfan1 G x) \<and>
     mem_range f2 (ar_at Pfan2 G x) \<and> fitp G (face G x) p'"
| "fitp G x (Pcons8 h f1 f2 f3 p') \<longleftrightarrow>
     ar_at Pspoke G x = 8 \<and> mem_range h (ar_at Phat G x) \<and> mem_range f1 (ar_at Pfan1 G x) \<and>
     mem_range f2 (ar_at Pfan2 G x) \<and> mem_range f3 (ar_at Pfan3 G x) \<and> fitp G (face G x) p'"

declare subpart_loc_move.simps [simp del]

definition exact_fitp :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> part \<Rightarrow> bool" where
  "exact_fitp G x p \<longleftrightarrow> arity G x = psize p \<and> fitp G x p"

definition tight_fitp :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> prange \<times> part \<Rightarrow> bool" where
  "tight_fitp G x up = (case up of (u, p) \<Rightarrow> mem_range u (arity G x) \<and> fitp G x p)"

lemma fitp_drop: "fitp G x p \<Longrightarrow> fitp G ((face G ^^ n) x) (drop_part n p)"
proof (induction n p arbitrary: x rule: drop_part.induct)
  case (1 n s h p)
  then show ?case by (simp add: funpow_Suc_right del: funpow.simps)
next
  case (2 n s h p)
  then show ?case by (simp add: funpow_Suc_right del: funpow.simps)
next
  case (3 n a b c p)
  then show ?case by (simp add: funpow_Suc_right del: funpow.simps)
next
  case (4 n a b c d p)
  then show ?case by (simp add: funpow_Suc_right del: funpow.simps)
qed simp_all

lemma fitp_cat:
  "fitp G x (cat_part p1 p2) \<longleftrightarrow> fitp G x p1 \<and> fitp G ((face G ^^ psize p1) x) p2"
  by (induction p1 arbitrary: x) (simp_all add: funpow_Suc_right del: funpow.simps; blast)+

section \<open>Comparison soundness\<close>

definition rel_ok :: "part_rel \<Rightarrow> bool \<Rightarrow> bool" where
  "rel_ok c b \<longleftrightarrow> b = apply_part_rel c b"

lemma rel_ok_meet: "rel_ok c1 b1 \<Longrightarrow> rel_ok c2 b2 \<Longrightarrow> rel_ok (meet_prel c1 c2) (b1 \<and> b2)"
  by (cases c1; cases c2) (auto simp: rel_ok_def)

lemma rel_ok_notP: "rel_ok c b \<Longrightarrow> rel_ok (notPsubset c) b"
  by (cases c) (auto simp: rel_ok_def)

lemma rel_ok_range: "mem_range r1 n \<Longrightarrow> rel_ok (cmp_range r1 r2) (mem_range r2 n)"
  unfolding rel_ok_def by (rule mem_cmp_range)

lemma rel_ok_eq_range: "mem_range r n \<Longrightarrow> rel_ok (cmp_range r Pr66) (n = 6)"
  "mem_range r n \<Longrightarrow> rel_ok (cmp_range r Pr77) (n = 7)"
  "mem_range r n \<Longrightarrow> rel_ok (cmp_range r Pr88) (n = 8)"
  using rel_ok_range[of r n Pr66] rel_ok_range[of r n Pr77] rel_ok_range[of r n Pr88] by simp_all

lemma rel_ok_weaken: "rel_ok c X \<Longrightarrow> c \<noteq> Psubset \<Longrightarrow> (Y \<Longrightarrow> X) \<Longrightarrow> rel_ok c Y"
  by (cases c) (auto simp: rel_ok_def)

lemma meet_notP_ne: "meet_prel (notPsubset c) d \<noteq> Psubset"
  by (cases c; cases d) simp_all

lemma rel_ok_conj_true: "rel_ok c b \<Longrightarrow> rel_ok c (True \<and> b)" by simp

lemma fitp_cmp: "fitp G x p \<Longrightarrow> rel_ok (cmp_part p q) (fitp G x q)"
proof (induction p q arbitrary: x rule: cmp_part.induct)
  case (1 p)
  then show ?case by (simp add: rel_ok_def)
next
  case (2 sp hp p' sq hq q')
  then show ?case by (auto intro!: rel_ok_meet rel_ok_range)
next
  case (3 hp f p' sq hq q')
  then show ?case using rel_ok_range[of Pr66 "ar_at Pspoke G x" sq]
    by (auto intro!: rel_ok_meet rel_ok_range)
next
  case (4 hp f1 f2 p' sq hq q')
  then show ?case using rel_ok_range[of Pr77 "ar_at Pspoke G x" sq]
    by (auto intro!: rel_ok_meet rel_ok_range)
next
  case (5 hp f1 f2 f3 p' sq hq q')
  then show ?case using rel_ok_range[of Pr88 "ar_at Pspoke G x" sq]
    by (auto intro!: rel_ok_meet rel_ok_range)
next
  case (6 sp hp p' hq f q')
  have "rel_ok (meet_prel (notPsubset (cmp_range sp Pr66)) (meet_prel (cmp_range hp hq) (cmp_part p' q')))
      (ar_at Pspoke G x = 6 \<and> mem_range hq (ar_at Phat G x) \<and> fitp G (face G x) q')"
    using "6.prems" "6.IH" rel_ok_eq_range(1)[of sp "ar_at Pspoke G x"]
    by (auto intro!: rel_ok_meet rel_ok_range rel_ok_notP)
  then show ?case unfolding cmp_part.simps fitp.simps by (rule rel_ok_weaken[OF _ meet_notP_ne]) auto
next
  case (7 sp hp p' hq f1 f2 q')
  have "rel_ok (meet_prel (notPsubset (cmp_range sp Pr77)) (meet_prel (cmp_range hp hq) (cmp_part p' q')))
      (ar_at Pspoke G x = 7 \<and> mem_range hq (ar_at Phat G x) \<and> fitp G (face G x) q')"
    using "7.prems" "7.IH" rel_ok_eq_range(2)[of sp "ar_at Pspoke G x"]
    by (auto intro!: rel_ok_meet rel_ok_range rel_ok_notP)
  then show ?case unfolding cmp_part.simps fitp.simps by (rule rel_ok_weaken[OF _ meet_notP_ne]) auto
next
  case (8 sp hp p' hq f1 f2 f3 q')
  have "rel_ok (meet_prel (notPsubset (cmp_range sp Pr88)) (meet_prel (cmp_range hp hq) (cmp_part p' q')))
      (ar_at Pspoke G x = 8 \<and> mem_range hq (ar_at Phat G x) \<and> fitp G (face G x) q')"
    using "8.prems" "8.IH" rel_ok_eq_range(3)[of sp "ar_at Pspoke G x"]
    by (auto intro!: rel_ok_meet rel_ok_range rel_ok_notP)
  then show ?case unfolding cmp_part.simps fitp.simps by (rule rel_ok_weaken[OF _ meet_notP_ne]) auto
next
  case (9 hp f1p p' hq f1q q')
  then show ?case by (auto intro!: rel_ok_meet rel_ok_range)
next
  case (10 hp f1p f2p p' hq f1q f2q q')
  then show ?case by (auto intro!: rel_ok_meet rel_ok_range)
next
  case (11 hp f1p f2p f3p p' hq f1q f2q f3q q')
  then show ?case by (auto intro!: rel_ok_meet rel_ok_range)
qed (auto simp: rel_ok_def)

lemma fitp_meet: "fitp G x p \<Longrightarrow> fitp G x q \<Longrightarrow> fitp G x (meet_part p q)"
  by (induction p q arbitrary: x rule: meet_part.induct) (auto intro: mem_meet_range)

lemma psize_meet: "psize (meet_part p q) = psize p"
  by (induction p q rule: meet_part.induct) simp_all

lemma exact_fitp_meet: "exact_fitp G x p \<Longrightarrow> fitp G x q \<Longrightarrow> exact_fitp G x (meet_part p q)"
  by (simp add: exact_fitp_def psize_meet fitp_meet)

section \<open>Rotations and splits\<close>

lemma psize_pos: "p \<noteq> Pnil \<Longrightarrow> 0 < psize p"
  by (cases p) simp_all

lemma drop_part_nonnil: "drop_part j p \<noteq> Pnil \<Longrightarrow> j < psize p"
  by (induction j p rule: drop_part.induct) (auto simp: psize_pos)

lemma good_head_nonnil: "good_head i k q \<Longrightarrow> q \<noteq> Pnil"
  by (cases q) auto

context hypermap
begin

lemma arity_funpow: "arity G ((f ^^ m) x) = arity G x"
  by (induction m) simp_all

lemma fitp_rot:
  assumes mle: "m \<le> psize p"
  shows "exact_fitp G x p \<longleftrightarrow> exact_fitp G ((f ^^ m) x) (rot_part m p)"
proof (cases "arity G x = psize p")
  case False
  then show ?thesis by (simp add: exact_fitp_def psize_rot arity_funpow)
next
  case True
  have tk: "psize (take_part m p) = m" by (rule psize_take[OF mle])
  have dr: "psize (drop_part m p) = psize p - m" by (rule psize_drop)
  have bk: "(f ^^ psize (drop_part m p)) ((f ^^ m) x) = x"
  proof -
    have "(f ^^ psize (drop_part m p)) ((f ^^ m) x) = (f ^^ (psize p - m + m)) x"
      by (simp add: dr funpow_add)
    also have "psize p - m + m = arity G x" using True mle by simp
    finally show ?thesis by simp
  qed
  have "fitp G x p \<longleftrightarrow> fitp G x (take_part m p) \<and> fitp G ((f ^^ m) x) (drop_part m p)"
    using fitp_cat[of G x "take_part m p" "drop_part m p"] tk by (simp add: cat_take_drop_part)
  moreover have "fitp G ((f ^^ m) x) (rot_part m p) \<longleftrightarrow>
      fitp G ((f ^^ m) x) (drop_part m p) \<and> fitp G x (take_part m p)"
    unfolding rot_part_def fitp_cat bk ..
  ultimately show ?thesis using True by (auto simp: exact_fitp_def psize_rot arity_funpow)
qed

end

lemma psize_split_head: "psize (split_head i sr q) = psize q"
  by (induction i sr q rule: split_head.induct) simp_all

definition fitc :: "subpart_loc \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a hypermap \<Rightarrow> 'a \<Rightarrow> bool" where
  "fitc i j k G x \<longleftrightarrow> k < ar_at i G ((face G ^^ j) x)"

lemma psize_pcons_any: "psize (pcons_any m) = m"
  by (induction m) (simp_all add: pcons_any_def)

context hypermap
begin

lemma move_D: "subpart_loc_move i G y \<in> D \<longleftrightarrow> y \<in> D"
  by (cases i) (simp_all add: subpart_loc_move.simps)

context
  assumes penta: "\<And>y. y \<in> D \<Longrightarrow> 5 \<le> arity G y"
begin

lemma penta_at: "y \<in> D \<Longrightarrow> 5 \<le> ar_at i G y"
  using penta move_D by blast

lemma fitp_pcons_any: "x \<in> D \<Longrightarrow> fitp G x (pcons_any m)"
  by (induction m arbitrary: x) (simp_all add: pcons_any_def penta_at)

lemma exact_fitp_pcons_any: "x \<in> D \<Longrightarrow> exact_fitp G x (pcons_any (arity G x))"
  using fitp_pcons_any by (simp add: exact_fitp_def psize_pcons_any)

lemma fitp_split_head:
  assumes yD: "y \<in> D" and g: "good_head i k q"
  shows "fitp G y (split_head i (split_range k lo) q) \<longleftrightarrow> (lo \<noteq> (k < ar_at i G y)) \<and> fitp G y q"
  using g
proof (induction i "split_range k lo" q rule: split_head.induct)
qed (auto simp: fit_split_range penta_at[OF yD])

lemma fitp_split:
  assumes xD: "x \<in> D" and g: "good_split i j k p"
  shows "exact_fitp G x (split_part i j k lo p) \<longleftrightarrow> (lo \<noteq> fitc i j k G x) \<and> exact_fitp G x p"
proof -
  have gh: "good_head i k (drop_part j p)" using g by (simp add: good_split_def)
  have jl: "j < psize p" using drop_part_nonnil good_head_nonnil[OF gh] by blast
  have tk: "psize (take_part j p) = j" using psize_take jl by simp
  have yD: "(f ^^ j) x \<in> D" using xD by simp
  let ?sh = "split_head i (split_range k lo) (drop_part j p)"
  have sp: "split_part i j k lo p = cat_part (take_part j p) ?sh" using g by (simp add: split_part_def)
  have sz: "psize (split_part i j k lo p) = psize p"
    using psize_cat[of "take_part j p" "drop_part j p"]
    by (simp add: sp psize_cat psize_split_head cat_take_drop_part)
  have "fitp G x (split_part i j k lo p) \<longleftrightarrow>
      fitp G x (take_part j p) \<and> fitp G ((f ^^ j) x) ?sh"
    by (simp add: sp fitp_cat tk)
  also have "\<dots> \<longleftrightarrow> fitp G x (take_part j p) \<and> (lo \<noteq> fitc i j k G x) \<and>
      fitp G ((f ^^ j) x) (drop_part j p)"
    by (simp add: fitp_split_head[OF yD gh] fitc_def)
  also have "\<dots> \<longleftrightarrow> (lo \<noteq> fitc i j k G x) \<and> fitp G x p"
    using fitp_cat[of G x "take_part j p" "drop_part j p"] tk by (auto simp: cat_take_drop_part)
  finally show ?thesis using sz by (auto simp: exact_fitp_def)
qed

end

end

end
