(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Redpart2.thy
    Correctness of the part reducibility check (redpart.v, proofs).
    Ported from G. Gonthier's Coq development (redpart.v).
*)
theory Redpart2
  imports Redpart
begin

lemma catrev_fitp_eq:
  "fitp G x (catrev_part p1 p2) \<longleftrightarrow> fitp G x (rev_part p1) \<and> fitp G ((face G ^^ psize p1) x) p2"
  using fitp_cat[of G x "rev_part p1" p2] catrev_part_eq[of p1 p2]
  by (simp add: rev_part_def psize_catrev)

lemma rev_part_cons:
  "rev_part (Pcons s h p) = cat_part (rev_part p) (Pcons s h Pnil)"
  "rev_part (Pcons6 h f1 p) = cat_part (rev_part p) (Pcons6 h f1 Pnil)"
  "rev_part (Pcons7 h f1 f2 p) = cat_part (rev_part p) (Pcons7 h f1 f2 Pnil)"
  "rev_part (Pcons8 h f1 f2 f3 p) = cat_part (rev_part p) (Pcons8 h f1 f2 f3 Pnil)"
  unfolding rev_part_def catrev_part.simps by (rule catrev_part_eq)+

locale rp_ctx = rp qt ahub red_rec p0l p0r + hypermap G
  for qt ahub red_rec p0l p0r and G :: "'a hypermap" +
  fixes x0 :: 'a
  assumes plainG: "plain G" and cubicG: "cubic G"
    and pentaG: "\<And>y. y \<in> darts G \<Longrightarrow> 5 \<le> arity G y"
    and nofit: "\<And>y. \<not> qzt_ctx.qzt_fit G y qt"
    and not_red_rec: "\<And>x p. x \<in> darts G \<Longrightarrow> arity G x = nat_of_qarity ahub \<Longrightarrow>
                         exact_fitp G x p \<Longrightarrow> \<not> red_rec p"
    and Dp0l: "p0l = rev_part p0r"
    and fit_p0r: "exact_fitp G x0 p0r" and nFx0: "arity G x0 = nat_of_qarity ahub"
    and x0D: "x0 \<in> darts G"
begin

sublocale Q: qzt_ctx G x for x using plainG cubicG by unfold_locales

lemma ee [simp]: "e (e x) = x" by (rule Q.ee)
lemma nnn [simp]: "n (n (n x)) = x" by (rule Q.nnn)
lemma f_ne: "f x = n (n (e x))" by (rule Q.f_ne)
lemma ar_nne [simp]: "arity G (n (n (e x))) = arity G x" by (rule Q.ar_nne)
lemma ar_en [simp]: "arity G (e (n x)) = arity G x" by (rule Q.ar_en)

lemma Ep0r: "psize p0r = nhub" using fit_p0r nFx0 by (simp add: exact_fitp_def)

lemma fit0: "fitp G x0 p0r" using fit_p0r by (simp add: exact_fitp_def)

lemma iter_arity: "(f ^^ arity G x) x = x" by (rule F.funpow_order)

definition zvalid :: "part \<Rightarrow> part \<Rightarrow> bool" where
  "zvalid pl pr \<longleftrightarrow> catrev_part pl pr = cat_part p0r p0r"

definition zorg :: "part \<Rightarrow> 'a" where "zorg pl = (f ^^ psize pl) x0"

fun zmove :: "zpart_loc \<Rightarrow> 'a \<Rightarrow> 'a" where
  "zmove Znil x = x"
| "zmove Zhub x = x"
| "zmove Zhubl x = n x"
| "zmove Zhubr x = n (n x)"
| "zmove Zhat x = n (e (n (n x)))"
| "zmove Zhatl x = e (n (n x))"
| "zmove Zhatr x = f (n (n x))"
| "zmove Zfan0l x = f (e (((e \<circ> n) ^^ 2) (n x)))"
| "zmove Zfan1l x = f (e (((e \<circ> n) ^^ 3) (n x)))"
| "zmove Zfan2l x = f (e (((e \<circ> n) ^^ 4) (n x)))"
| "zmove Zfan3l x = f (e (((e \<circ> n) ^^ 5) (n x)))"
| "zmove Zfan0r x = e ((f ^^ 2) (n x))"
| "zmove Zfan1r x = e ((f ^^ 3) (n x))"
| "zmove Zfan2r x = e ((f ^^ 4) (n x))"
| "zmove Zfan3r x = e ((f ^^ 5) (n x))"

fun zdart :: "zpart \<Rightarrow> 'a" where "zdart (Zpart zi pl _) = zmove zi (zorg pl)"
fun zporg :: "zpart \<Rightarrow> 'a" where "zporg (Zpart _ pl _) = zorg pl"
fun zpvalid :: "zpart \<Rightarrow> bool" where "zpvalid (Zpart _ pl pr) = zvalid pl pr"

definition zpfit :: "'a \<Rightarrow> zpart \<Rightarrow> bool" where "zpfit x zp \<longleftrightarrow> (zproper zp \<longrightarrow> zdart zp = x)"

lemma zorg_D: "zorg pl \<in> D" using x0D by (simp add: zorg_def)

lemma zvalid_fit: "zvalid pl pr \<Longrightarrow> fitp G x0 (catrev_part pl pr)"
  unfolding zvalid_def using fit0 Ep0r nFx0 iter_arity[of x0] by (simp add: fitp_cat)

lemma zvalid_fit_r: "zvalid pl pr \<Longrightarrow> fitp G (zorg pl) pr"
  using zvalid_fit[of pl pr] by (simp add: catrev_fitp_eq zorg_def)

lemma zvalid_fit_l: "zvalid pl pr \<Longrightarrow> fitp G x0 (rev_part pl)"
  using zvalid_fit[of pl pr] by (simp add: catrev_fitp_eq)

text \<open>The head of the left part describes the dart just before the origin.\<close>

lemma zorg_cons: "zorg (Pcons s h pl) = f (zorg pl)" "zorg (Pcons6 h f1 pl) = f (zorg pl)"
  "zorg (Pcons7 h f1 f2 pl) = f (zorg pl)" "zorg (Pcons8 h f1 f2 f3 pl) = f (zorg pl)"
  by (simp_all add: zorg_def)

lemma zvalid_head:
  assumes v: "zvalid pl pr" and pl: "pl = pc pl'" and pcs: "\<And>q. rev_part (pc q) = cat_part (rev_part q) (pc Pnil)"
    and sz: "psize (pc Pnil) = 1"
  shows "fitp G (zorg pl') (pc Pnil)"
proof -
  have "fitp G x0 (rev_part pl)" by (rule zvalid_fit_l[OF v])
  then have "fitp G x0 (cat_part (rev_part pl') (pc Pnil))" using pl pcs by simp
  then show ?thesis by (simp add: fitp_cat psize_rev zorg_def)
qed

lemma e_zorg_prev: "e (n (f y)) = y" by (rule faceK)

lemma head_fit:
  "zvalid (Pcons s h pl') pr \<Longrightarrow> fitp G (zorg pl') (Pcons s h Pnil)"
  "zvalid (Pcons6 h f1 pl') pr \<Longrightarrow> fitp G (zorg pl') (Pcons6 h f1 Pnil)"
  "zvalid (Pcons7 h f1 f2 pl') pr \<Longrightarrow> fitp G (zorg pl') (Pcons7 h f1 f2 Pnil)"
  "zvalid (Pcons8 h f1 f2 f3 pl') pr \<Longrightarrow> fitp G (zorg pl') (Pcons8 h f1 f2 f3 Pnil)"
  by (rule zvalid_head; simp add: rev_part_cons)+

lemma pentaD: "y \<in> D \<Longrightarrow> mem_range Pr59 (arity G y)" using pentaG by simp

lemma nf_simp [simp]: "n (f x) = e x" using f_ne[of x] by simp

lemma fe_nn: "f (e y) = n (n y)" using f_ne[of "e y"] by simp

lemma ar_nn [simp]: "arity G (n (n y)) = arity G (e y)"
  using fe_nn[of y] by (metis F.order_f)

lemma ar_ef: "arity G (e (f w)) = arity G (n (e w))"
  using ar_en[of "n (e w)"] f_ne[of w] by simp

lemma en_f [simp]: "e (n (f w)) = w" by (rule faceK)

lemma enk_step: "(e \<circ> n) ((f ^^ Suc d) u) = (f ^^ d) u" by simp

lemma enk: "arity G u = m \<Longrightarrow> k \<le> m \<Longrightarrow> ((e \<circ> n) ^^ k) u = (f ^^ (m - k)) u"
proof (induction k)
  case 0
  then show ?case using iter_arity[of u] by simp
next
  case (Suc k)
  have km: "k \<le> m" using Suc.prems(2) by simp
  have IH: "((e \<circ> n) ^^ k) u = (f ^^ (m - k)) u" by (rule Suc.IH[OF Suc.prems(1) km])
  have mk: "m - k = Suc (m - Suc k)" using Suc.prems(2) by simp
  have "((e \<circ> n) ^^ Suc k) u = (e \<circ> n) (((e \<circ> n) ^^ k) u)" by (simp only: funpow.simps comp_apply)
  also have "\<dots> = (e \<circ> n) ((f ^^ Suc (m - Suc k)) u)" by (simp only: IH mk)
  also have "\<dots> = (f ^^ (m - Suc k)) u" by (rule enk_step)
  finally show ?case .
qed

lemma hub_range_mem: "mem_range hub_range nhub"
  by (cases ahub) (simp_all add: rp.hub_range_def mem_range_def)

lemma get_nil: "get_spoke Pnil = Pr59" "get_hat Pnil = Pr59" "get_fan1l Pnil = Pr59"
  "get_fan2l Pnil = Pr59" "get_fan3l Pnil = Pr59" "get_fan1r Pnil = Pr59" "get_fan2r Pnil = Pr59"
  "get_fan3r Pnil = Pr59"
  by (simp_all add: get_hat_def)

lemma inD: "zorg pl \<in> D" "n (zorg pl) \<in> D" "e (zorg pl) \<in> D" by (simp_all add: zorg_D)

lemmas mv = subpart_loc_move.simps eval_nat_numeral funpow.simps comp_def

lemma zr_hub: "zvalid pl pr \<Longrightarrow> mem_range (zrange (Zpart Zhub pl pr)) (arity G (zdart (Zpart Zhub pl pr)))"
  using hub_range_mem nFx0 by (simp add: zorg_def arity_funpow)

lemma zr_hubl:
  assumes v: "zvalid pl pr"
  shows "mem_range (zrange (Zpart Zhubl pl pr)) (arity G (zdart (Zpart Zhubl pl pr)))"
  using v head_fit zorg_D pentaD[of "n (zorg pl)"]
  by (cases pl) (auto simp: zorg_cons mv get_hat_def)

lemma zr_hatl:
  assumes v: "zvalid pl pr"
  shows "mem_range (zrange (Zpart Zhatl pl pr)) (arity G (zdart (Zpart Zhatl pl pr)))"
  using v head_fit zorg_D pentaD[of "n (zorg pl)"]
  by (cases pl) (auto simp: zorg_cons mv get_hat_def)

lemma zr_hubr:
  assumes v: "zvalid pl pr"
  shows "mem_range (zrange (Zpart Zhubr pl pr)) (arity G (zdart (Zpart Zhubr pl pr)))"
  using zvalid_fit_r[OF v] zorg_D pentaD[of "e (zorg pl)"]
  by (cases pr) (auto simp: mv)

lemma zr_hatr:
  assumes v: "zvalid pl pr"
  shows "mem_range (zrange (Zpart Zhatr pl pr)) (arity G (zdart (Zpart Zhatr pl pr)))"
  using zvalid_fit_r[OF v] zorg_D pentaD[of "e (zorg pl)"]
  by (cases pr) (auto simp: mv)

lemma zr_hat:
  assumes v: "zvalid pl pr"
  shows "mem_range (zrange (Zpart Zhat pl pr)) (arity G (zdart (Zpart Zhat pl pr)))"
proof -
  have eq: "arity G (n (e (n (n z)))) = arity G (e (f (f (e z))))" for z
    by (simp add: ar_ef fe_nn)
  have zD: "n (e (n (n (zorg pl)))) \<in> D" using zorg_D by simp
  show ?thesis using zvalid_fit_r[OF v] pentaD[OF zD] eq[of "zorg pl"]
    by (cases pr) (auto simp: mv get_hat_def)
qed

lemma zr_fan0l:
  assumes v: "zvalid pl pr"
  shows "mem_range (zrange (Zpart Zfan0l pl pr)) (arity G (zdart (Zpart Zfan0l pl pr)))"
proof -
  have eq: "arity G (f (e (((e \<circ> n) ^^ 2) (n z)))) = arity G (e (f (f (e z))))" for z
    by (simp add: eval_nat_numeral ar_ef fe_nn)
  have zD: "f (e (((e \<circ> n) ^^ 2) (n (zorg pl)))) \<in> D" using zorg_D by (simp add: eval_nat_numeral)
  show ?thesis using zvalid_fit_r[OF v] pentaD[OF zD] eq[of "zorg pl"]
    by (cases pr) (auto simp: mv get_hat_def)
qed

lemma zr_fanr:
  assumes v: "zvalid pl pr"
  shows "mem_range (zrange (Zpart Zfan0r pl pr)) (arity G (zdart (Zpart Zfan0r pl pr)))"
    and "mem_range (zrange (Zpart Zfan1r pl pr)) (arity G (zdart (Zpart Zfan1r pl pr)))"
    and "mem_range (zrange (Zpart Zfan2r pl pr)) (arity G (zdart (Zpart Zfan2r pl pr)))"
    and "mem_range (zrange (Zpart Zfan3r pl pr)) (arity G (zdart (Zpart Zfan3r pl pr)))"
proof -
  have pent: "mem_range Pr59 (arity G (e ((f ^^ k) (n (zorg pl)))))" for k
    by (rule pentaD) (simp add: zorg_D)
  show "mem_range (zrange (Zpart Zfan0r pl pr)) (arity G (zdart (Zpart Zfan0r pl pr)))"
    using v head_fit zorg_D pent[of 2]
    by (cases pl) (auto simp: zorg_cons mv get_hat_def)
  show "mem_range (zrange (Zpart Zfan1r pl pr)) (arity G (zdart (Zpart Zfan1r pl pr)))"
    using v head_fit zorg_D pent[of 3]
    by (cases pl) (auto simp: zorg_cons mv get_hat_def)
  show "mem_range (zrange (Zpart Zfan2r pl pr)) (arity G (zdart (Zpart Zfan2r pl pr)))"
    using v head_fit zorg_D pent[of 4]
    by (cases pl) (auto simp: zorg_cons mv get_hat_def)
  show "mem_range (zrange (Zpart Zfan3r pl pr)) (arity G (zdart (Zpart Zfan3r pl pr)))"
    using v head_fit zorg_D pent[of 5]
    by (cases pl) (auto simp: zorg_cons mv get_hat_def)
qed

lemma zr_fanl:
  assumes v: "zvalid pl pr"
  shows "mem_range (zrange (Zpart Zfan1l pl pr)) (arity G (zdart (Zpart Zfan1l pl pr)))"
    and "mem_range (zrange (Zpart Zfan2l pl pr)) (arity G (zdart (Zpart Zfan2l pl pr)))"
    and "mem_range (zrange (Zpart Zfan3l pl pr)) (arity G (zdart (Zpart Zfan3l pl pr)))"
proof -
  have D3: "f (e (((e \<circ> n) ^^ k) (n (zorg pl)))) \<in> D" for k
  proof -
    have "((e \<circ> n) ^^ k) w \<in> D \<longleftrightarrow> w \<in> D" for w by (induction k) simp_all
    then show ?thesis using zorg_D by simp
  qed
  have key: "arity G (f (e (((e \<circ> n) ^^ k) (e y)))) = arity G (e ((f ^^ (m - k)) (e y)))"
    if "arity G (e y) = m" "k \<le> m" for y m k
    using enk[OF that] by simp
  show "mem_range (zrange (Zpart Zfan1l pl pr)) (arity G (zdart (Zpart Zfan1l pl pr)))"
  proof (cases pl)
    case (Pcons6 h f1 pl')
    have hf: "fitp G (zorg pl') (Pcons6 h f1 Pnil)" using head_fit(2) v Pcons6 by simp
    then show ?thesis using key[of "zorg pl'" 6 3] Pcons6 by (simp add: zorg_cons mv)
  next
    case (Pcons7 h f1 f2 pl')
    have hf: "fitp G (zorg pl') (Pcons7 h f1 f2 Pnil)" using head_fit(3) v Pcons7 by simp
    then show ?thesis using key[of "zorg pl'" 7 3] Pcons7 by (simp add: zorg_cons mv)
  next
    case (Pcons8 h f1 f2 f3 pl')
    have hf: "fitp G (zorg pl') (Pcons8 h f1 f2 f3 Pnil)" using head_fit(4) v Pcons8 by simp
    then show ?thesis using key[of "zorg pl'" 8 3] Pcons8 by (simp add: zorg_cons mv)
  qed (use D3[of 3] pentaD in simp_all)
  show "mem_range (zrange (Zpart Zfan2l pl pr)) (arity G (zdart (Zpart Zfan2l pl pr)))"
  proof (cases pl)
    case (Pcons7 h f1 f2 pl')
    have hf: "fitp G (zorg pl') (Pcons7 h f1 f2 Pnil)" using head_fit(3) v Pcons7 by simp
    then show ?thesis using key[of "zorg pl'" 7 4] Pcons7 by (simp add: zorg_cons mv)
  next
    case (Pcons8 h f1 f2 f3 pl')
    have hf: "fitp G (zorg pl') (Pcons8 h f1 f2 f3 Pnil)" using head_fit(4) v Pcons8 by simp
    then show ?thesis using key[of "zorg pl'" 8 4] Pcons8 by (simp add: zorg_cons mv)
  qed (use D3[of 4] pentaD in simp_all)
  show "mem_range (zrange (Zpart Zfan3l pl pr)) (arity G (zdart (Zpart Zfan3l pl pr)))"
  proof (cases pl)
    case (Pcons8 h f1 f2 f3 pl')
    have hf: "fitp G (zorg pl') (Pcons8 h f1 f2 f3 Pnil)" using head_fit(4) v Pcons8 by simp
    then show ?thesis using key[of "zorg pl'" 8 5] Pcons8 by (simp add: zorg_cons mv)
  qed (use D3[of 5] pentaD in simp_all)
qed

lemma zrange_dart:
  assumes v: "zpvalid zp"
  shows "mem_range (zrange zp) (arity G (zdart zp))"
proof (cases zp)
  case (Zpart zi pl pr)
  then have vv: "zvalid pl pr" using v by simp
  show ?thesis
  proof (cases zi)
    case Znil
    then show ?thesis using pentaD zorg_D Zpart by simp
  qed (use Zpart vv zr_hub zr_hubl zr_hubr zr_hat zr_hatl zr_hatr zr_fan0l zr_fanl zr_fanr in simp_all)
qed

section \<open>Shifting the zipper\<close>

lemma catrev_cat: "catrev_part (cat_part a b) c = catrev_part b (catrev_part a c)"
  by (induction a arbitrary: c) simp_all

lemma rev_rev_part: "rev_part (rev_part p) = p"
proof -
  have "catrev_part (catrev_part p q) Pnil = catrev_part q p" for q
    by (induction p arbitrary: q) simp_all
  then show ?thesis by (simp add: rev_part_def)
qed

lemma p0l_size: "psize p0l = nhub" using Ep0r Dp0l by (simp add: psize_rev)

lemma nhub_pos: "0 < nhub" by (cases ahub) simp_all

lemma zvalid_init: "zvalid p0l p0r"
proof -
  have "catrev_part (rev_part p0r) p0r = cat_part (rev_part (rev_part p0r)) p0r"
    using catrev_part_eq[of "rev_part p0r" p0r] by (simp only: rev_part_def)
  then show ?thesis unfolding zvalid_def Dp0l by (simp only: rev_rev_part)
qed

lemma take1_drop1: "p \<noteq> Pnil \<Longrightarrow> catrev_part (drop_part 1 p) (cat_part (take_part 1 p) q) = catrev_part p q"
  by (cases p) (simp_all add: numeral_One[symmetric] One_nat_def)

lemma p0_ne: "p0l \<noteq> Pnil" "p0r \<noteq> Pnil"
  using p0l_size Ep0r nhub_pos by auto

lemma zvalid_initl: "zvalid p0ll p0lr"
  using zvalid_init take1_drop1[OF p0_ne(1)] by (simp add: zvalid_def shift_part_def)

lemma zvalid_initr: "zvalid p0rl p0rr"
proof -
  have "catrev_part (cat_part (take_part 1 p0r) p0l) (drop_part 1 p0r) =
        catrev_part p0l (catrev_part (take_part 1 p0r) (drop_part 1 p0r))" by (rule catrev_cat)
  also have "catrev_part (take_part 1 p0r) (drop_part 1 p0r) = cat_part (take_part 1 p0r) (drop_part 1 p0r)"
    using p0_ne(2) by (cases p0r) simp_all
  also have "\<dots> = p0r" by (rule cat_take_drop_part)
  finally show ?thesis using zvalid_init by (simp add: zvalid_def shift_part_def)
qed

lemma zvalid_size: "zvalid pl pr \<Longrightarrow> psize pl + psize pr = 2 * nhub"
  unfolding zvalid_def by (metis psize_catrev psize_cat Ep0r mult_2)

lemma zorg_mod: "zorg pl = (f ^^ (psize pl mod nhub)) x0"
  unfolding zorg_def using F.funpow_mod_order[of "psize pl" x0] nFx0 by simp

lemma zpvalid_shiftl: "zpvalid zp \<Longrightarrow> zpvalid (zshiftl zi zp)"
proof (cases zp)
  case (Zpart zi' pl pr)
  assume v: "zpvalid zp"
  show ?thesis
  proof (cases pl)
    case Pnil then show ?thesis using Zpart zvalid_initl by simp
  next
    case (Pcons s h pl') then show ?thesis using Zpart v zvalid_init by (cases "pl' = Pnil") (auto simp: zvalid_def)
  next
    case (Pcons6 h f1 pl') then show ?thesis using Zpart v zvalid_init by (cases "pl' = Pnil") (auto simp: zvalid_def)
  next
    case (Pcons7 h f1 f2 pl') then show ?thesis using Zpart v zvalid_init by (cases "pl' = Pnil") (auto simp: zvalid_def)
  next
    case (Pcons8 h f1 f2 f3 pl') then show ?thesis using Zpart v zvalid_init by (cases "pl' = Pnil") (auto simp: zvalid_def)
  qed
qed

lemma zpvalid_shiftr: "zpvalid zp \<Longrightarrow> zpvalid (zshiftr zi zp)"
proof (cases zp)
  case (Zpart zi' pl pr)
  assume v: "zpvalid zp"
  show ?thesis
  proof (cases pr)
    case Pnil then show ?thesis using Zpart zvalid_initr by simp
  next
    case (Pcons s h pr') then show ?thesis using Zpart v zvalid_init by (cases "pr' = Pnil") (auto simp: zvalid_def)
  next
    case (Pcons6 h f1 pr') then show ?thesis using Zpart v zvalid_init by (cases "pr' = Pnil") (auto simp: zvalid_def)
  next
    case (Pcons7 h f1 f2 pr') then show ?thesis using Zpart v zvalid_init by (cases "pr' = Pnil") (auto simp: zvalid_def)
  next
    case (Pcons8 h f1 f2 f3 pr') then show ?thesis using Zpart v zvalid_init by (cases "pr' = Pnil") (auto simp: zvalid_def)
  qed
qed

lemma zproper_shiftl: "zproper (zshiftl zi zp) \<longleftrightarrow> zi \<noteq> Znil"
  by (cases "(zi, zp)" rule: zshiftl.cases) (cases zi; simp)+

lemma zproper_shiftr: "zproper (zshiftr zi zp) \<longleftrightarrow> zi \<noteq> Znil"
  by (cases "(zi, zp)" rule: zshiftr.cases) (cases zi; simp)+

lemma zorg_p0l: "zorg p0l = x0" using p0l_size iter_arity[of x0] nFx0 by (simp add: zorg_def)

lemma f_pred_iter: assumes "0 < m" shows "f ((f ^^ (m - 1)) x) = (f ^^ m) x"
proof -
  have "m = Suc (m - 1)" using assms by simp
  then have "(f ^^ m) x = (f ^^ Suc (m - 1)) x" by (rule arg_cong)
  then show ?thesis by simp
qed

lemma zorg_p0ll: "zorg p0ll = e (n x0)"
proof -
  have "psize p0ll = nhub - 1" using p0l_size by (simp add: psize_drop)
  moreover have "f ((f ^^ (nhub - 1)) x0) = (f ^^ nhub) x0"
    by (rule f_pred_iter[OF nhub_pos])
  ultimately have "f (zorg p0ll) = x0" using iter_arity[of x0] nFx0 by (simp add: zorg_def)
  then show ?thesis using en_f[of "zorg p0ll"] by simp
qed

lemma zdart_shiftl: "zdart (zshiftl zi zp) = zmove zi (e (n (zporg zp)))"
proof (cases zp)
  case (Zpart zi' pl pr)
  show ?thesis
  proof (cases pl)
    case Pnil
    have "zorg Pnil = x0" by (simp add: zorg_def)
    then show ?thesis using Zpart Pnil zorg_p0ll by simp
  qed (use Zpart zorg_p0l in \<open>auto simp: zorg_cons zorg_def\<close>)
qed

lemma zdart_shiftr: "zpvalid zp \<Longrightarrow> zdart (zshiftr zi zp) = zmove zi (f (zporg zp))"
proof (cases zp)
  case (Zpart zi' pl pr)
  assume v: "zpvalid zp"
  have vv: "zvalid pl pr" using v Zpart by simp
  have sz: "psize pl + psize pr = 2 * nhub" by (rule zvalid_size[OF vv])
  have f2: "(f ^^ (2 * nhub)) x0 = x0" using iter_arity[of x0] nFx0 by (simp add: mult_2 funpow_add)
  show ?thesis
  proof (cases pr)
    case Pnil
    have "psize p0rl = Suc nhub" using p0_ne(2) p0l_size by (cases p0r) (simp_all add: shift_part_def psize_cat)
    then have "zorg p0rl = f x0" using iter_arity[of x0] nFx0 by (simp add: zorg_def)
    moreover have "zorg pl = x0" using sz Pnil f2 by (simp add: zorg_def)
    ultimately show ?thesis using Zpart Pnil by simp
  next
    case (Pcons s h pr')
    show ?thesis
    proof (cases "pr' = Pnil")
      case True
      have "psize pl = 2 * nhub - 1" using sz Pcons True by simp
      then have "f (zorg pl) = x0" using f2 nhub_pos f_pred_iter[of "2 * nhub" x0] by (simp add: zorg_def)
      then show ?thesis using Zpart Pcons True zorg_p0l by simp
    qed (use Zpart Pcons in \<open>simp add: zorg_cons\<close>)
  next
    case (Pcons6 h f1 pr')
    show ?thesis
    proof (cases "pr' = Pnil")
      case True
      have "psize pl = 2 * nhub - 1" using sz Pcons6 True by simp
      then have "f (zorg pl) = x0" using f2 nhub_pos f_pred_iter[of "2 * nhub" x0] by (simp add: zorg_def)
      then show ?thesis using Zpart Pcons6 True zorg_p0l by simp
    qed (use Zpart Pcons6 in \<open>simp add: zorg_cons\<close>)
  next
    case (Pcons7 h f1 f2 pr')
    show ?thesis
    proof (cases "pr' = Pnil")
      case True
      have "psize pl = 2 * nhub - 1" using sz Pcons7 True by simp
      then have "f (zorg pl) = x0" using f2 nhub_pos f_pred_iter[of "2 * nhub" x0] by (simp add: zorg_def)
      then show ?thesis using Zpart Pcons7 True zorg_p0l by simp
    qed (use Zpart Pcons7 in \<open>simp add: zorg_cons\<close>)
  next
    case (Pcons8 h f1 f2 f3 pr')
    show ?thesis
    proof (cases "pr' = Pnil")
      case True
      have "psize pl = 2 * nhub - 1" using sz Pcons8 True by simp
      then have "f (zorg pl) = x0" using f2 nhub_pos f_pred_iter[of "2 * nhub" x0] by (simp add: zorg_def)
      then show ?thesis using Zpart Pcons8 True zorg_p0l by simp
    qed (use Zpart Pcons8 in \<open>simp add: zorg_cons\<close>)
  qed
qed

section \<open>Stepping the zipper\<close>

lemmas wn = f_ne eval_nat_numeral funpow.simps comp_def qstepL_def qstepR_def

lemma idL_hat: "qstepL G (n (e (n (n z)))) = f (e ((f ^^ 3) (e z)))" by (simp add: wn)
lemma idR_hatr: "qstepR G (f (n (n z))) = f (e ((f ^^ 3) (e z)))" by (simp add: wn)
lemma idL_hatl: "qstepL G (e (n (n z))) = e (((e \<circ> n) ^^ 3) (n z))" by (simp add: wn)
lemma idR_hat: "qstepR G (n (e (n (n z)))) = e (((e \<circ> n) ^^ 3) (n z))" by (simp add: wn)
lemma idL_fan: "qstepL G (f (e ((e \<circ> n) t))) = f (e t)" by (simp add: wn)
lemma idR_fan: "qstepR G (e (f t)) = e t" by (simp add: wn)

lemma fanL_dart:
  assumes v: "zvalid pl pr" and ne: "zfanL pr \<noteq> Znil"
  shows "zmove (zfanL pr) (f (zorg pl)) = f (e ((f ^^ 3) (e (zorg pl))))"
proof -
  have fr: "fitp G (zorg pl) pr" by (rule zvalid_fit_r[OF v])
  let ?w = "e (zorg pl)"
  have key: "f (e (((e \<circ> n) ^^ k) ?w)) = f (e ((f ^^ 3) ?w))" if "arity G ?w = k + 3" for k
    using enk[OF that, of k] by simp
  show ?thesis
  proof (cases pr)
    case (Pcons s h pr')
    then have "s = Pr55" using ne by (auto split: if_splits)
    then show ?thesis using fr Pcons key[of 2] by (simp add: mv)
  next
    case (Pcons6 h f1 pr') then show ?thesis using fr key[of 3] by (simp add: mv)
  next
    case (Pcons7 h f1 f2 pr') then show ?thesis using fr key[of 4] by (simp add: mv)
  next
    case (Pcons8 h f1 f2 f3 pr') then show ?thesis using fr key[of 5] by (simp add: mv)
  qed (use ne in simp)
qed

lemma fanR_dart:
  assumes v: "zvalid pl pr" and ne: "zfanR pl \<noteq> Znil"
  shows "zmove (zfanR pl) (zorg pl) = e (((e \<circ> n) ^^ 3) (n (zorg pl)))"
proof -
  have key: "e ((f ^^ k) (e y)) = e (((e \<circ> n) ^^ 3) (e y))" if "arity G (e y) = k + 3" for k y
    using enk[OF that, of 3] by simp
  show ?thesis
  proof (cases pl)
    case (Pcons s h pl')
    then have "s = Pr55" using ne by (auto split: if_splits)
    then show ?thesis using head_fit(1)[OF v[unfolded Pcons]] Pcons key[of _ 2] by (simp add: mv zorg_cons)
  next
    case (Pcons6 h f1 pl')
    then show ?thesis using head_fit(2)[OF v[unfolded Pcons6]] key[of _ 3] by (simp add: mv zorg_cons)
  next
    case (Pcons7 h f1 f2 pl')
    then show ?thesis using head_fit(3)[OF v[unfolded Pcons7]] key[of _ 4] by (simp add: mv zorg_cons)
  next
    case (Pcons8 h f1 f2 f3 pl')
    then show ?thesis using head_fit(4)[OF v[unfolded Pcons8]] key[of _ 5] by (simp add: mv zorg_cons)
  qed (use ne in simp)
qed

lemma zdart_stepL:
  assumes v: "zpvalid zp"
  shows "zpfit (qstepL G (zdart zp)) (zstepL zp)"
proof (cases zp)
  case (Zpart zi pl pr)
  have vv: "zvalid pl pr" using v Zpart by simp
  let ?z = "zorg pl"
  show ?thesis
  proof (cases zi)
    case Zhub
    then show ?thesis using Zpart by (simp add: zpfit_def zdart_shiftl qstepL_def)
  next
    case Zhubl
    then show ?thesis using Zpart by (simp add: zpfit_def qstepL_def)
  next
    case Zhubr
    then show ?thesis using Zpart v by (simp add: zpfit_def zdart_shiftr qstepL_def)
  next
    case Zhat
    show ?thesis unfolding zpfit_def
    proof
      assume pp: "zproper (zstepL zp)"
      then have ne: "zfanL pr \<noteq> Znil" using Zpart Zhat zproper_shiftr by simp
      have "zdart (zstepL zp) = zmove (zfanL pr) (f ?z)" using Zpart Zhat v by (simp add: zdart_shiftr)
      also have "\<dots> = qstepL G (zdart zp)" using fanL_dart[OF vv ne] Zpart Zhat idL_hat by simp
      finally show "zdart (zstepL zp) = qstepL G (zdart zp)" .
    qed
  next
    case Zhatl
    show ?thesis unfolding zpfit_def
    proof
      assume pp: "zproper (zstepL zp)"
      then have ne: "zfanR pl \<noteq> Znil" using Zpart Zhatl by auto
      show "zdart (zstepL zp) = qstepL G (zdart zp)"
        using fanR_dart[OF vv ne] Zpart Zhatl idL_hatl by simp
    qed
  next
    case Zhatr
    then show ?thesis using Zpart by (simp add: zpfit_def wn)
  next
    case Zfan0l
    then show ?thesis using Zpart by (simp add: zpfit_def wn)
  next
    case Zfan1l
    then show ?thesis using Zpart idL_fan[of "((e \<circ> n) ^^ 2) (n ?z)"]
      by (simp add: zpfit_def eval_nat_numeral del: funpow.simps) (simp add: funpow_Suc_right del: funpow.simps)
  next
    case Zfan2l
    then show ?thesis using Zpart idL_fan[of "((e \<circ> n) ^^ 3) (n ?z)"]
      by (simp add: zpfit_def eval_nat_numeral del: funpow.simps) (simp add: funpow_Suc_right del: funpow.simps)
  next
    case Zfan3l
    then show ?thesis using Zpart idL_fan[of "((e \<circ> n) ^^ 4) (n ?z)"]
      by (simp add: zpfit_def eval_nat_numeral del: funpow.simps) (simp add: funpow_Suc_right del: funpow.simps)
  qed (use Zpart in \<open>simp_all add: zpfit_def\<close>)
qed

lemma zdart_stepR:
  assumes v: "zpvalid zp"
  shows "zpfit (qstepR G (zdart zp)) (zstepR zp)"
proof (cases zp)
  case (Zpart zi pl pr)
  have vv: "zvalid pl pr" using v Zpart by simp
  let ?z = "zorg pl"
  show ?thesis
  proof (cases zi)
    case Zhub
    then show ?thesis using Zpart v by (simp add: zpfit_def zdart_shiftr qstepR_def)
  next
    case Zhubl
    then show ?thesis using Zpart by (simp add: zpfit_def zdart_shiftl qstepR_def)
  next
    case Zhubr
    then show ?thesis using Zpart by (simp add: zpfit_def qstepR_def)
  next
    case Zhat
    show ?thesis unfolding zpfit_def
    proof
      assume pp: "zproper (zstepR zp)"
      then have ne: "zfanR pl \<noteq> Znil" using Zpart Zhat by auto
      show "zdart (zstepR zp) = qstepR G (zdart zp)"
        using fanR_dart[OF vv ne] Zpart Zhat idR_hat by simp
    qed
  next
    case Zhatl
    then show ?thesis using Zpart by (simp add: zpfit_def qstepR_def)
  next
    case Zhatr
    show ?thesis unfolding zpfit_def
    proof
      assume pp: "zproper (zstepR zp)"
      then have ne: "zfanL pr \<noteq> Znil" using Zpart Zhatr zproper_shiftr by simp
      have "zdart (zstepR zp) = zmove (zfanL pr) (f ?z)" using Zpart Zhatr v by (simp add: zdart_shiftr)
      also have "\<dots> = qstepR G (zdart zp)" using fanL_dart[OF vv ne] Zpart Zhatr idR_hatr by simp
      finally show "zdart (zstepR zp) = qstepR G (zdart zp)" .
    qed
  next
    case Zfan0r
    then show ?thesis using Zpart by (simp add: zpfit_def zdart_shiftl wn)
  next
    case Zfan1r
    then show ?thesis using Zpart idR_fan[of "(f ^^ 2) (n ?z)"]
      by (simp add: zpfit_def eval_nat_numeral)
  next
    case Zfan2r
    then show ?thesis using Zpart idR_fan[of "(f ^^ 3) (n ?z)"]
      by (simp add: zpfit_def eval_nat_numeral)
  next
    case Zfan3r
    then show ?thesis using Zpart idR_fan[of "(f ^^ 4) (n ?z)"]
      by (simp add: zpfit_def eval_nat_numeral)
  qed (use Zpart in \<open>simp_all add: zpfit_def\<close>)
qed

end

end
