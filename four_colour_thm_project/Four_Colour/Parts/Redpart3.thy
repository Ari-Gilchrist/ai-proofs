(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Redpart3.thy
    Correctness of the part reducibility check, continued (redpart.v).
    Ported from G. Gonthier's Coq development (redpart.v).
*)
theory Redpart3
  imports Four_Colour_Parts.Redpart2
begin

lemma fitqa_topqa: "fitqa r qa \<longleftrightarrow> nat_of_qarity qa \<le> 8 \<and> qa = topqa r"
  by (simp add: fitqa_def)

lemma fitq_simps:
  "fitq G x Qask0"
  "fitq G x (Qask1 qa) \<longleftrightarrow> nat_of_qarity qa = arity G x"
  "fitq G x (QaskL qa ql) \<longleftrightarrow> nat_of_qarity qa = arity G x \<and> fitq G (qstepL G x) ql"
  "fitq G x (QaskR qa qr) \<longleftrightarrow> nat_of_qarity qa = arity G x \<and> fitq G (qstepR G x) qr"
  "fitq G x (QaskLR qa ql qr) \<longleftrightarrow> nat_of_qarity qa = arity G x \<and> fitq G (qstepL G x) ql \<and>
     fitq G (qstepR G x) qr"
  "fitq G x (QaskLL qa ql) \<longleftrightarrow> nat_of_qarity qa = arity G (edge G (node G (qstepL G x))) \<and>
     fitq G (qstepL G (qstepL G x)) ql"
  "fitq G x (QaskRR qa qr) \<longleftrightarrow> nat_of_qarity qa = arity G (qstepR G x) \<and>
     fitq G (qstepR G (qstepR G x)) qr"
  by (auto simp: fitq_def append_eq_append_conv length_walkq)

context rp_ctx
begin

lemma fitqa_proper: "fitqa (zrange zp) qa \<Longrightarrow> zproper zp"
  by (cases zp rule: zproper.cases) (auto simp: fitqa_def)

definition zpfit_top :: "zpart \<Rightarrow> bool" where
  "zpfit_top zp \<longleftrightarrow> arity G (zdart zp) = nat_of_qarity (topqa (zrange zp))"

lemma zdart_stepLt:
  assumes top: "zpfit_top zp" and v: "zpvalid zp"
  shows "zpfit (qstepL G (zdart zp)) (zstepLt zp)"
proof (cases zp)
  case (Zpart zi pl pr)
  have vv: "zvalid pl pr" using v Zpart by simp
  show ?thesis
  proof (cases "zi = Zhatl")
    case False
    then have "zstepLt zp = zstepL zp" using Zpart by (cases zi) simp_all
    then show ?thesis using zdart_stepL[OF v] by simp
  next
    case True
    show ?thesis unfolding zpfit_def
    proof
      assume pp: "zproper (zstepLt zp)"
      then have ne: "zfanRt pl \<noteq> Znil" using Zpart True by auto
      show "zdart (zstepLt zp) = qstepL G (zdart zp)"
      proof (cases "zfanR pl = zfanRt pl")
        case eq: True
        then have "zfanR pl \<noteq> Znil" using ne by simp
        then show ?thesis using fanR_dart[OF vv] Zpart True eq idL_hatl by simp
      next
        case False
        then obtain s h pl' where pl: "pl = Pcons s h pl'" and s: "s = Pr56 \<or> s = Pr66"
          by (cases pl) (auto split: if_splits)
        have hf: "fitp G (zorg pl') (Pcons s h Pnil)" using head_fit(1) vv pl by simp
        have a6: "arity G (e (zorg pl')) = 6"
          using top Zpart True pl s by (auto simp: zpfit_top_def zorg_cons)
        have "e ((f ^^ 3) (e (zorg pl'))) = e (((e \<circ> n) ^^ 3) (e (zorg pl')))"
          using enk[OF a6, of 3] by simp
        then show ?thesis using Zpart True pl s idL_hatl[of "zorg pl"] by (auto simp: zorg_cons)
      qed
    qed
  qed
qed

lemma zdart_stepRt:
  assumes top: "zpfit_top zp" and v: "zpvalid zp"
  shows "zpfit (qstepR G (zdart zp)) (zstepRt zp)"
proof (cases zp)
  case (Zpart zi pl pr)
  have vv: "zvalid pl pr" using v Zpart by simp
  show ?thesis
  proof (cases "zi = Zhatr")
    case False
    then have "zstepRt zp = zstepR zp" using Zpart by (cases zi) simp_all
    then show ?thesis using zdart_stepR[OF v] by simp
  next
    case True
    show ?thesis unfolding zpfit_def
    proof
      assume pp: "zproper (zstepRt zp)"
      then have ne: "zfanLt pr \<noteq> Znil" using Zpart True zproper_shiftr by simp
      have d: "zdart (zstepRt zp) = zmove (zfanLt pr) (f (zorg pl))"
        using Zpart True v by (simp add: zdart_shiftr)
      show "zdart (zstepRt zp) = qstepR G (zdart zp)"
      proof (cases "zfanL pr = zfanLt pr")
        case eq: True
        then have "zfanL pr \<noteq> Znil" using ne by simp
        then show ?thesis using fanL_dart[OF vv] d eq Zpart True idR_hatr by simp
      next
        case False
        then obtain s h pr' where pr: "pr = Pcons s h pr'" and s: "s = Pr56 \<or> s = Pr66"
          by (cases pr) (auto split: if_splits)
        have a6: "arity G (e (zorg pl)) = 6"
          using top Zpart True pr s by (auto simp: zpfit_top_def)
        have "f (e (((e \<circ> n) ^^ 3) (e (zorg pl)))) = f (e ((f ^^ 3) (e (zorg pl))))"
          using enk[OF a6, of 3] by simp
        then show ?thesis using d Zpart True pr s idR_hatr by auto
      qed
    qed
  qed
qed

section \<open>Popping reducible ranges\<close>

definition pupd :: "(prange \<Rightarrow> part \<Rightarrow> part) \<Rightarrow> subpart_loc \<Rightarrow> bool" where
  "pupd pc j \<longleftrightarrow> (\<forall>r p. psize (pc r p) = Suc (psize p) \<and>
     (\<forall>x. fitp G x (pc r p) \<longrightarrow> mem_range r (ar_at j G x) \<and>
        (\<forall>r'. mem_range r' (ar_at j G x) \<longrightarrow> fitp G x (pc r' p))))"

lemma pupd_simps:
  "pupd (\<lambda>r. Pcons r h) Pspoke" "pupd (Pcons s) Phat"
  "pupd (\<lambda>r. Pcons6 r f1) Phat" "pupd (Pcons6 h) Pfan1"
  "pupd (\<lambda>r. Pcons7 r f1 f2) Phat" "pupd (\<lambda>r. Pcons7 h r f2) Pfan1" "pupd (Pcons7 h f1) Pfan2"
  "pupd (\<lambda>r. Pcons8 r f1 f2 f3) Phat" "pupd (\<lambda>r. Pcons8 h r f2 f3) Pfan1"
  "pupd (\<lambda>r. Pcons8 h f1 r f3) Pfan2" "pupd (Pcons8 h f1 f2) Pfan3"
  by (simp_all add: pupd_def)

lemma red_pcons_fit:
  assumes pu: "pupd pc j" and v: "zvalid pl (pc r pr)" and qa: "fitqa r qa"
    and red: "red_pcons pc r pr"
  shows "ar_at j G (zorg pl) = nat_of_qarity qa"
proof -
  have pS: "\<And>r' p. psize (pc r' p) = Suc (psize p)" using pu unfolding pupd_def by blast
  have pM: "\<And>r' p x. fitp G x (pc r' p) \<Longrightarrow> mem_range r' (ar_at j G x)"
    using pu unfolding pupd_def by blast
  have pU: "\<And>r' p x r''. fitp G x (pc r' p) \<Longrightarrow> mem_range r'' (ar_at j G x) \<Longrightarrow> fitp G x (pc r'' p)"
    using pu unfolding pupd_def by blast
  let ?y = "zorg pl"
  have yD: "?y \<in> D" by (rule zorg_D)
  have fy: "fitp G ?y (pc r pr)" by (rule zvalid_fit_r[OF v])
  have mr: "mem_range r (ar_at j G ?y)" by (rule pM[OF fy])
  have upd: "\<And>r'. mem_range r' (ar_at j G ?y) \<Longrightarrow> fitp G ?y (pc r' pr)" by (rule pU[OF fy])
  have ay: "arity G ?y = nhub" using nFx0 by (simp add: zorg_def arity_funpow)
  show ?thesis
  proof (rule fitqa_popqa[OF qa mr])
    show "mem_range (popqa r) 9 \<or> \<not> mem_range (popqa r) (ar_at j G ?y)"
    proof (cases "r \<in> {Pr56, Pr57, Pr58, Pr67, Pr68, Pr78}")
      case False
      then show ?thesis by (cases r) (simp_all add: mem_range_def)
    next
      case True
      have rr: "red_rec (take_part nhub (cat_part (pc (popqa r) pr) p0r))"
        using red True by (simp add: red_pcons_def)
      show ?thesis
      proof (rule disjI2, rule notI)
        assume mp: "mem_range (popqa r) (ar_at j G ?y)"
        let ?q = "cat_part (pc (popqa r) pr) p0r"
        have f1: "fitp G ?y (pc (popqa r) pr)" by (rule upd[OF mp])
        have szv: "psize pl + Suc (psize pr) = 2 * nhub"
          using zvalid_size[OF v] pS[of r pr] by simp
        have bk: "(f ^^ psize (pc (popqa r) pr)) ?y = x0"
        proof -
          have "(f ^^ psize (pc (popqa r) pr)) ?y = (f ^^ (Suc (psize pr) + psize pl)) x0"
            using pS[of "popqa r" pr] by (simp add: zorg_def funpow_add)
          also have "Suc (psize pr) + psize pl = 2 * nhub" using szv by simp
          finally show ?thesis using iter_arity[of x0] nFx0 by (simp add: mult_2 funpow_add)
        qed
        have fq: "fitp G ?y ?q" using f1 fit0 bk by (simp add: fitp_cat)
        have szq: "nhub \<le> psize ?q" by (simp add: psize_cat Ep0r)
        have tk: "psize (take_part nhub ?q) = nhub" by (rule psize_take[OF szq])
        have "fitp G ?y (take_part nhub ?q)"
          using fq fitp_cat[of G ?y "take_part nhub ?q" "drop_part nhub ?q"] by (simp add: cat_take_drop_part)
        then have "exact_fitp G ?y (take_part nhub ?q)" using tk ay by (simp add: exact_fitp_def)
        then show False using not_red_rec[OF yD ay] rr by blast
      qed
    qed
  qed
qed

lemma zvalid_pop:
  "zvalid (Pcons s h pl') pr \<Longrightarrow> zvalid pl' (Pcons s h pr)"
  "zvalid (Pcons6 h f1 pl') pr \<Longrightarrow> zvalid pl' (Pcons6 h f1 pr)"
  "zvalid (Pcons7 h f1 f2 pl') pr \<Longrightarrow> zvalid pl' (Pcons7 h f1 f2 pr)"
  "zvalid (Pcons8 h f1 f2 f3 pl') pr \<Longrightarrow> zvalid pl' (Pcons8 h f1 f2 f3 pr)"
  by (simp_all add: zvalid_def)

lemma fitqa_eq: "fitqa Pr66 qa \<Longrightarrow> nat_of_qarity qa = 6" "fitqa Pr77 qa \<Longrightarrow> nat_of_qarity qa = 7"
  "fitqa Pr88 qa \<Longrightarrow> nat_of_qarity qa = 8" "\<not> fitqa Pr59 qa"
  by (auto simp: fitqa_def)

lemma red_popr_spoke_fit:
  assumes v: "zvalid pl pr" and qa: "fitqa (get_spoke pr) qa" and red: "red_popr_spoke pr"
  shows "arity G (e (zorg pl)) = nat_of_qarity qa"
proof -
  have fr: "fitp G (zorg pl) pr" by (rule zvalid_fit_r[OF v])
  show ?thesis
  proof (cases pr)
    case (Pcons s h p)
    show ?thesis using red_pcons_fit[where pc="\<lambda>r. Pcons r h" and j=Pspoke and pl=pl and r=s and pr=p and qa=qa, OF pupd_simps(1)] v qa red Pcons by (simp add: mv)
  qed (use fr qa fitqa_eq in \<open>auto simp: mv\<close>)
qed

lemma red_popr_hat_fit:
  assumes v: "zvalid pl pr" and qa: "fitqa (get_hat pr) qa" and red: "red_popr_hat pr"
  shows "ar_at Phat G (zorg pl) = nat_of_qarity qa"
proof (cases pr)
  case Pnil then show ?thesis using qa by (auto simp: get_hat_def fitqa_def)
next
  case (Pcons s h p)
  show ?thesis using red_pcons_fit[where pc="Pcons s" and j=Phat and pl=pl and r=h and pr=p and qa=qa, OF pupd_simps(2)] v qa red Pcons by (simp add: get_hat_def)
next
  case (Pcons6 h f1 p)
  show ?thesis using red_pcons_fit[where pc="\<lambda>r. Pcons6 r f1" and j=Phat and pl=pl and r=h and pr=p and qa=qa, OF pupd_simps(3)] v qa red Pcons6 by (simp add: get_hat_def)
next
  case (Pcons7 h f1 f2 p)
  show ?thesis using red_pcons_fit[where pc="\<lambda>r. Pcons7 r f1 f2" and j=Phat and pl=pl and r=h and pr=p and qa=qa, OF pupd_simps(5)] v qa red Pcons7 by (simp add: get_hat_def)
next
  case (Pcons8 h f1 f2 f3 p)
  show ?thesis using red_pcons_fit[where pc="\<lambda>r. Pcons8 r f1 f2 f3" and j=Phat and pl=pl and r=h and pr=p and qa=qa, OF pupd_simps(8)] v qa red Pcons8 by (simp add: get_hat_def)
qed

lemma red_popl_spoke_fit:
  assumes v: "zvalid pl pr" and qa: "fitqa (get_spoke pl) qa" and red: "red_popl_spoke pl pr"
  shows "arity G (n (zorg pl)) = nat_of_qarity qa"
proof (cases pl)
  case Pnil then show ?thesis using qa fitqa_eq by simp
next
  case (Pcons s h pl')
  show ?thesis using red_pcons_fit[where pc="\<lambda>r. Pcons r h" and j=Pspoke and pl="pl'" and r=s and pr=pr and qa=qa, OF pupd_simps(1) zvalid_pop(1)] v qa red Pcons
    by (simp add: mv zorg_cons)
next
  case (Pcons6 h f1 pl')
  show ?thesis using head_fit(2)[of h f1 pl' pr] v qa Pcons6 fitqa_eq by (simp add: mv zorg_cons)
next
  case (Pcons7 h f1 f2 pl')
  show ?thesis using head_fit(3)[of h f1 f2 pl' pr] v qa Pcons7 fitqa_eq by (simp add: mv zorg_cons)
next
  case (Pcons8 h f1 f2 f3 pl')
  show ?thesis using head_fit(4)[of h f1 f2 f3 pl' pr] v qa Pcons8 fitqa_eq by (simp add: mv zorg_cons)
qed

lemma red_popl_hat_fit:
  assumes v: "zvalid pl pr" and qa: "fitqa (get_hat pl) qa" and red: "red_popl_hat pl pr"
  shows "arity G (e ((f ^^ 2) (n (zorg pl)))) = nat_of_qarity qa"
proof (cases pl)
  case Pnil then show ?thesis using qa by (auto simp: get_hat_def fitqa_def)
next
  case (Pcons s h pl')
  show ?thesis using red_pcons_fit[where pc="Pcons s" and j=Phat and pl="pl'" and r=h and pr=pr and qa=qa, OF pupd_simps(2) zvalid_pop(1)] v qa red Pcons
    by (simp add: get_hat_def zorg_cons subpart_loc_move.simps)
next
  case (Pcons6 h f1 pl')
  show ?thesis using red_pcons_fit[where pc="\<lambda>r. Pcons6 r f1" and j=Phat and pl="pl'" and r=h and pr=pr and qa=qa, OF pupd_simps(3) zvalid_pop(2)] v qa red Pcons6
    by (simp add: get_hat_def zorg_cons subpart_loc_move.simps)
next
  case (Pcons7 h f1 f2 pl')
  show ?thesis using red_pcons_fit[where pc="\<lambda>r. Pcons7 r f1 f2" and j=Phat and pl="pl'" and r=h and pr=pr and qa=qa, OF pupd_simps(5) zvalid_pop(3)] v qa red Pcons7
    by (simp add: get_hat_def zorg_cons subpart_loc_move.simps)
next
  case (Pcons8 h f1 f2 f3 pl')
  show ?thesis using red_pcons_fit[where pc="\<lambda>r. Pcons8 r f1 f2 f3" and j=Phat and pl="pl'" and r=h and pr=pr and qa=qa, OF pupd_simps(8) zvalid_pop(4)] v qa red Pcons8
    by (simp add: get_hat_def zorg_cons subpart_loc_move.simps)
qed

lemma lfan: "arity G (e y) = m \<Longrightarrow> k \<le> m \<Longrightarrow>
    arity G (f (e (((e \<circ> n) ^^ k) (e y)))) = arity G (e ((f ^^ (m - k)) (e y)))"
  using enk[of "e y" m k] by simp

lemma red_popl_fanr_fit:
  assumes v: "zvalid pl pr"
  shows "fitqa (get_fan1r pl) qa \<Longrightarrow> red_popl_fan1r pl pr \<Longrightarrow> arity G (zdart (Zpart Zfan1r pl pr)) = nat_of_qarity qa"
    and "fitqa (get_fan2r pl) qa \<Longrightarrow> red_popl_fan2r pl pr \<Longrightarrow> arity G (zdart (Zpart Zfan2r pl pr)) = nat_of_qarity qa"
    and "fitqa (get_fan3r pl) qa \<Longrightarrow> red_popl_fan3r pl pr \<Longrightarrow> arity G (zdart (Zpart Zfan3r pl pr)) = nat_of_qarity qa"
proof -
  assume qa: "fitqa (get_fan1r pl) qa" and red: "red_popl_fan1r pl pr"
  show "arity G (zdart (Zpart Zfan1r pl pr)) = nat_of_qarity qa"
  proof (cases pl)
    case (Pcons6 h f1 pl')
    show ?thesis using red_pcons_fit[where pc="Pcons6 h" and j=Pfan1 and pl="pl'" and r=f1 and pr=pr and qa=qa, OF pupd_simps(4) zvalid_pop(2)] v qa red Pcons6
      by (simp add: zorg_cons subpart_loc_move.simps)
  next
    case (Pcons7 h f1 f2 pl')
    show ?thesis using red_pcons_fit[where pc="\<lambda>r. Pcons7 h r f2" and j=Pfan1 and pl="pl'" and r=f1 and pr=pr and qa=qa, OF pupd_simps(6) zvalid_pop(3)] v qa red Pcons7
      by (simp add: zorg_cons subpart_loc_move.simps)
  next
    case (Pcons8 h f1 f2 f3 pl')
    show ?thesis using red_pcons_fit[where pc="\<lambda>r. Pcons8 h r f2 f3" and j=Pfan1 and pl="pl'" and r=f1 and pr=pr and qa=qa, OF pupd_simps(9) zvalid_pop(4)] v qa red Pcons8
      by (simp add: zorg_cons subpart_loc_move.simps)
  qed (use qa in \<open>auto simp: fitqa_def\<close>)
next
  assume qa: "fitqa (get_fan2r pl) qa" and red: "red_popl_fan2r pl pr"
  show "arity G (zdart (Zpart Zfan2r pl pr)) = nat_of_qarity qa"
  proof (cases pl)
    case (Pcons7 h f1 f2 pl')
    show ?thesis using red_pcons_fit[where pc="Pcons7 h f1" and j=Pfan2 and pl="pl'" and r=f2 and pr=pr and qa=qa, OF pupd_simps(7) zvalid_pop(3)] v qa red Pcons7
      by (simp add: zorg_cons subpart_loc_move.simps)
  next
    case (Pcons8 h f1 f2 f3 pl')
    show ?thesis using red_pcons_fit[where pc="\<lambda>r. Pcons8 h f1 r f3" and j=Pfan2 and pl="pl'" and r=f2 and pr=pr and qa=qa, OF pupd_simps(10) zvalid_pop(4)] v qa red Pcons8
      by (simp add: zorg_cons subpart_loc_move.simps)
  qed (use qa in \<open>auto simp: fitqa_def\<close>)
next
  assume qa: "fitqa (get_fan3r pl) qa" and red: "red_popl_fan3r pl pr"
  show "arity G (zdart (Zpart Zfan3r pl pr)) = nat_of_qarity qa"
  proof (cases pl)
    case (Pcons8 h f1 f2 f3 pl')
    show ?thesis using red_pcons_fit[where pc="Pcons8 h f1 f2" and j=Pfan3 and pl="pl'" and r=f3 and pr=pr and qa=qa, OF pupd_simps(11) zvalid_pop(4)] v qa red Pcons8
      by (simp add: zorg_cons subpart_loc_move.simps)
  qed (use qa in \<open>auto simp: fitqa_def\<close>)
qed

lemma red_popl_fanl_fit:
  assumes v: "zvalid pl pr"
  shows "fitqa (get_fan1l pl) qa \<Longrightarrow> red_popl_fan1l pl pr \<Longrightarrow> arity G (zdart (Zpart Zfan1l pl pr)) = nat_of_qarity qa"
    and "fitqa (get_fan2l pl) qa \<Longrightarrow> red_popl_fan2l pl pr \<Longrightarrow> arity G (zdart (Zpart Zfan2l pl pr)) = nat_of_qarity qa"
    and "fitqa (get_fan3l pl) qa \<Longrightarrow> red_popl_fan3l pl pr \<Longrightarrow> arity G (zdart (Zpart Zfan3l pl pr)) = nat_of_qarity qa"
proof -
  assume qa: "fitqa (get_fan1l pl) qa" and red: "red_popl_fan1l pl pr"
  show "arity G (zdart (Zpart Zfan1l pl pr)) = nat_of_qarity qa"
  proof (cases pl)
    case (Pcons6 h f1 pl')
    have a: "arity G (e (zorg pl')) = 6" using head_fit(2)[of h f1 pl' pr] v Pcons6 by (simp add: mv)
    show ?thesis using red_pcons_fit[where pc="Pcons6 h" and j=Pfan1 and pl="pl'" and r=f1 and pr=pr and qa=qa, OF pupd_simps(4) zvalid_pop(2)] v qa red Pcons6 lfan[OF a, of 3]
      by (simp add: zorg_cons subpart_loc_move.simps)
  next
    case (Pcons7 h f1 f2 pl')
    have a: "arity G (e (zorg pl')) = 7" using head_fit(3)[of h f1 f2 pl' pr] v Pcons7 by (simp add: mv)
    show ?thesis using red_pcons_fit[where pc="Pcons7 h f1" and j=Pfan2 and pl="pl'" and r=f2 and pr=pr and qa=qa, OF pupd_simps(7) zvalid_pop(3)] v qa red Pcons7 lfan[OF a, of 3]
      by (simp add: zorg_cons subpart_loc_move.simps)
  next
    case (Pcons8 h f1 f2 f3 pl')
    have a: "arity G (e (zorg pl')) = 8" using head_fit(4)[of h f1 f2 f3 pl' pr] v Pcons8 by (simp add: mv)
    show ?thesis using red_pcons_fit[where pc="Pcons8 h f1 f2" and j=Pfan3 and pl="pl'" and r=f3 and pr=pr and qa=qa, OF pupd_simps(11) zvalid_pop(4)] v qa red Pcons8 lfan[OF a, of 3]
      by (simp add: zorg_cons subpart_loc_move.simps)
  qed (use qa in \<open>auto simp: fitqa_def\<close>)
next
  assume qa: "fitqa (get_fan2l pl) qa" and red: "red_popl_fan2l pl pr"
  show "arity G (zdart (Zpart Zfan2l pl pr)) = nat_of_qarity qa"
  proof (cases pl)
    case (Pcons7 h f1 f2 pl')
    have a: "arity G (e (zorg pl')) = 7" using head_fit(3)[of h f1 f2 pl' pr] v Pcons7 by (simp add: mv)
    show ?thesis using red_pcons_fit[where pc="\<lambda>r. Pcons7 h r f2" and j=Pfan1 and pl="pl'" and r=f1 and pr=pr and qa=qa, OF pupd_simps(6) zvalid_pop(3)] v qa red Pcons7 lfan[OF a, of 4]
      by (simp add: zorg_cons subpart_loc_move.simps)
  next
    case (Pcons8 h f1 f2 f3 pl')
    have a: "arity G (e (zorg pl')) = 8" using head_fit(4)[of h f1 f2 f3 pl' pr] v Pcons8 by (simp add: mv)
    show ?thesis using red_pcons_fit[where pc="\<lambda>r. Pcons8 h f1 r f3" and j=Pfan2 and pl="pl'" and r=f2 and pr=pr and qa=qa, OF pupd_simps(10) zvalid_pop(4)] v qa red Pcons8 lfan[OF a, of 4]
      by (simp add: zorg_cons subpart_loc_move.simps)
  qed (use qa in \<open>auto simp: fitqa_def\<close>)
next
  assume qa: "fitqa (get_fan3l pl) qa" and red: "red_popl_fan3l pl pr"
  show "arity G (zdart (Zpart Zfan3l pl pr)) = nat_of_qarity qa"
  proof (cases pl)
    case (Pcons8 h f1 f2 f3 pl')
    have a: "arity G (e (zorg pl')) = 8" using head_fit(4)[of h f1 f2 f3 pl' pr] v Pcons8 by (simp add: mv)
    show ?thesis using red_pcons_fit[where pc="\<lambda>r. Pcons8 h r f2 f3" and j=Pfan1 and pl="pl'" and r=f1 and pr=pr and qa=qa, OF pupd_simps(9) zvalid_pop(4)] v qa red Pcons8 lfan[OF a, of 5]
      by (simp add: zorg_cons subpart_loc_move.simps)
  qed (use qa in \<open>auto simp: fitqa_def\<close>)
qed

lemma red_pop_fit:
  assumes v: "zpvalid zp" and qa: "fitqa (zrange zp) qa" and red: "red_pop zp"
  shows "arity G (zdart zp) = nat_of_qarity qa"
proof (cases zp)
  case (Zpart zi pl pr)
  have vv: "zvalid pl pr" using v Zpart by simp
  have qa': "fitqa (zrange (Zpart zi pl pr)) qa" using qa Zpart by simp
  have red': "red_pop (Zpart zi pl pr)" using red Zpart by simp
  have hat: "arity G (n (e (n (n z)))) = ar_at Phat G z" for z
    by (simp add: subpart_loc_move.simps eval_nat_numeral ar_ef fe_nn)
  have fan0: "arity G (f (e (((e \<circ> n) ^^ 2) (n z)))) = ar_at Phat G z" for z
    by (simp add: subpart_loc_move.simps eval_nat_numeral ar_ef fe_nn)
  show ?thesis
  proof (cases zi)
    case Znil then show ?thesis using qa' by (auto simp: fitqa_def)
  next
    case Zhub
    have "arity G (zorg pl) = nhub" using nFx0 by (simp add: zorg_def arity_funpow)
    then show ?thesis using qa' Zhub Zpart by (cases ahub) (auto simp: fitqa_def rp.hub_range_def rp.zrange.simps)
  next
    case Zhubl then show ?thesis using red_popl_spoke_fit[OF vv] qa' red' Zpart by simp
  next
    case Zhubr then show ?thesis using red_popr_spoke_fit[OF vv] qa' red' Zpart by simp
  next
    case Zhatl then show ?thesis using red_popl_spoke_fit[OF vv] qa' red' Zpart by simp
  next
    case Zhat then show ?thesis using red_popr_hat_fit[OF vv] qa' red' Zpart hat by simp
  next
    case Zhatr then show ?thesis using red_popr_spoke_fit[OF vv] qa' red' Zpart by simp
  next
    case Zfan0l then show ?thesis using red_popr_hat_fit[OF vv] qa' red' Zpart fan0 by simp
  next
    case Zfan0r then show ?thesis using red_popl_hat_fit[OF vv] qa' red' Zpart by simp
  qed (use red_popl_fanl_fit[OF vv] red_popl_fanr_fit[OF vv] qa' red' Zpart in simp_all)
qed

lemma zpvalid_steps:
  "zpvalid zp \<Longrightarrow> zpvalid (zstepL zp)" "zpvalid zp \<Longrightarrow> zpvalid (zstepR zp)"
  "zpvalid zp \<Longrightarrow> zpvalid (zstepLt zp)" "zpvalid zp \<Longrightarrow> zpvalid (zstepRt zp)"
  by (cases zp rule: zpvalid.cases, rename_tac zi pl pr, case_tac zi;
      simp add: zpvalid_shiftl zpvalid_shiftr del: zpvalid.simps; simp)+

lemma zproper_stepLR: "zproper (zstepL zp) \<Longrightarrow> zproper zp" "zproper (zstepR zp) \<Longrightarrow> zproper zp"
  by (cases zp rule: zproper.cases; simp)+

lemma fitqzp_proper: "fitqzp zp q \<Longrightarrow> q = Qask0 \<or> zproper zp"
  by (cases q) (auto dest: fitqa_proper zproper_stepLR)

lemma fitqzp_fit: "fitqzp zp q \<Longrightarrow> red_popqzp zp q \<Longrightarrow> zpvalid zp \<Longrightarrow> fitq G (zdart zp) q"
proof (induction q arbitrary: zp)
  case Qask0 then show ?case by (simp add: fitq_simps)
next
  case (Qask1 qa) then show ?case using red_pop_fit by (simp add: fitq_simps)
next
  case (QaskL qa ql)
  have qa: "fitqa (zrange zp) qa" and fl: "fitqzp (zstepLt zp) ql" and rp: "red_pop zp"
    and rl: "red_popqzp (zstepLt zp) ql" using QaskL.prems by simp_all
  have D: "arity G (zdart zp) = nat_of_qarity qa" by (rule red_pop_fit[OF QaskL.prems(3) qa rp])
  have top: "zpfit_top zp" using D qa by (simp add: zpfit_top_def fitqa_def)
  have v': "zpvalid (zstepLt zp)" by (rule zpvalid_steps(3)[OF QaskL.prems(3)])
  have "fitq G (qstepL G (zdart zp)) ql"
  proof (cases "ql = Qask0")
    case True then show ?thesis by (simp add: fitq_simps)
  next
    case False
    then have "zproper (zstepLt zp)" using fitqzp_proper[OF fl] by simp
    then have "zdart (zstepLt zp) = qstepL G (zdart zp)"
      using zdart_stepLt[OF top QaskL.prems(3)] by (simp add: zpfit_def)
    then show ?thesis using QaskL.IH[OF fl rl v'] by simp
  qed
  then show ?case using D by (simp add: fitq_simps)
next
  case (QaskR qa qr)
  have qa: "fitqa (zrange zp) qa" and fl: "fitqzp (zstepRt zp) qr" and rp: "red_pop zp"
    and rl: "red_popqzp (zstepRt zp) qr" using QaskR.prems by simp_all
  have D: "arity G (zdart zp) = nat_of_qarity qa" by (rule red_pop_fit[OF QaskR.prems(3) qa rp])
  have top: "zpfit_top zp" using D qa by (simp add: zpfit_top_def fitqa_def)
  have v': "zpvalid (zstepRt zp)" by (rule zpvalid_steps(4)[OF QaskR.prems(3)])
  have "fitq G (qstepR G (zdart zp)) qr"
  proof (cases "qr = Qask0")
    case True then show ?thesis by (simp add: fitq_simps)
  next
    case False
    then have "zproper (zstepRt zp)" using fitqzp_proper[OF fl] by simp
    then have "zdart (zstepRt zp) = qstepR G (zdart zp)"
      using zdart_stepRt[OF top QaskR.prems(3)] by (simp add: zpfit_def)
    then show ?thesis using QaskR.IH[OF fl rl v'] by simp
  qed
  then show ?case using D by (simp add: fitq_simps)
next
  case (QaskLR qa ql qr)
  have qa: "fitqa (zrange zp) qa" and fl: "fitqzp (zstepL zp) ql" and fr: "fitqzp (zstepR zp) qr"
    and rp: "red_pop zp" and rl: "red_popqzp (zstepL zp) ql" and rr: "red_popqzp (zstepR zp) qr"
    using QaskLR.prems by simp_all
  have D: "arity G (zdart zp) = nat_of_qarity qa" by (rule red_pop_fit[OF QaskLR.prems(3) qa rp])
  have L: "fitq G (qstepL G (zdart zp)) ql"
  proof (cases "ql = Qask0")
    case True then show ?thesis by (simp add: fitq_simps)
  next
    case False
    then have "zproper (zstepL zp)" using fitqzp_proper[OF fl] by simp
    then have "zdart (zstepL zp) = qstepL G (zdart zp)"
      using zdart_stepL[OF QaskLR.prems(3)] by (simp add: zpfit_def)
    then show ?thesis using QaskLR.IH(1)[OF fl rl zpvalid_steps(1)[OF QaskLR.prems(3)]] by simp
  qed
  have R: "fitq G (qstepR G (zdart zp)) qr"
  proof (cases "qr = Qask0")
    case True then show ?thesis by (simp add: fitq_simps)
  next
    case False
    then have "zproper (zstepR zp)" using fitqzp_proper[OF fr] by simp
    then have "zdart (zstepR zp) = qstepR G (zdart zp)"
      using zdart_stepR[OF QaskLR.prems(3)] by (simp add: zpfit_def)
    then show ?thesis using QaskLR.IH(2)[OF fr rr zpvalid_steps(2)[OF QaskLR.prems(3)]] by simp
  qed
  show ?case using D L R by (simp add: fitq_simps)
next
  case (QaskLL qa ql)
  let ?z1 = "zstepL zp"
  have qa: "fitqa (zrange ?z1) qa" and fl: "fitqzp (zstepL ?z1) ql" and rp: "red_pop ?z1"
    and rl: "red_popqzp (zstepL ?z1) ql" using QaskLL.prems by simp_all
  have v1: "zpvalid ?z1" by (rule zpvalid_steps(1)[OF QaskLL.prems(3)])
  have D: "arity G (zdart ?z1) = nat_of_qarity qa" by (rule red_pop_fit[OF v1 qa rp])
  have z1: "zdart ?z1 = qstepL G (zdart zp)"
    using zdart_stepL[OF QaskLL.prems(3)] fitqa_proper[OF qa] by (simp add: zpfit_def)
  have "fitq G (qstepL G (zdart ?z1)) ql"
  proof (cases "ql = Qask0")
    case True then show ?thesis by (simp add: fitq_simps)
  next
    case False
    then have "zproper (zstepL ?z1)" using fitqzp_proper[OF fl] by simp
    then have "zdart (zstepL ?z1) = qstepL G (zdart ?z1)" using zdart_stepL[OF v1] by (simp add: zpfit_def)
    then show ?thesis using QaskLL.IH[OF fl rl zpvalid_steps(1)[OF v1]] by simp
  qed
  then show ?case using D z1 by (simp add: fitq_simps)
next
  case (QaskRR qa qr)
  let ?z1 = "zstepR zp"
  have qa: "fitqa (zrange ?z1) qa" and fl: "fitqzp (zstepR ?z1) qr" and rp: "red_pop ?z1"
    and rl: "red_popqzp (zstepR ?z1) qr" using QaskRR.prems by simp_all
  have v1: "zpvalid ?z1" by (rule zpvalid_steps(2)[OF QaskRR.prems(3)])
  have D: "arity G (zdart ?z1) = nat_of_qarity qa" by (rule red_pop_fit[OF v1 qa rp])
  have z1: "zdart ?z1 = qstepR G (zdart zp)"
    using zdart_stepR[OF QaskRR.prems(3)] fitqa_proper[OF qa] by (simp add: zpfit_def)
  have "fitq G (qstepR G (zdart ?z1)) qr"
  proof (cases "qr = Qask0")
    case True then show ?thesis by (simp add: fitq_simps)
  next
    case False
    then have "zproper (zstepR ?z1)" using fitqzp_proper[OF fl] by simp
    then have "zdart (zstepR ?z1) = qstepR G (zdart ?z1)" using zdart_stepR[OF v1] by (simp add: zpfit_def)
    then show ?thesis using QaskRR.IH[OF fl rl zpvalid_steps(2)[OF v1]] by simp
  qed
  then show ?case using D z1 by (simp add: fitq_simps)
qed

lemma fitq_zp:
  assumes "zpfit y zp" "zpvalid zp" "fitqzp zp q" "red_popqzp zp q"
  shows "fitq G y q"
proof (cases "q = Qask0")
  case True then show ?thesis by (simp add: fitq_simps)
next
  case False
  then have "zproper zp" using fitqzp_proper[OF assms(3)] by simp
  then show ?thesis using fitqzp_fit[OF assms(3,4,2)] assms(1) by (simp add: zpfit_def)
qed

lemma red_qzt_leaf_fit:
  assumes "red_qzt_leaf zp1 zp2 zp3 qtl"
  shows "qzt_proper qtl \<and>
    (\<forall>x. zpfit (qstepR G x) zp1 \<longrightarrow> zpvalid zp1 \<longrightarrow> zpfit (qstepR G (n x)) zp2 \<longrightarrow> zpvalid zp2 \<longrightarrow>
         zpfit (qstepR G (n (n x))) zp3 \<longrightarrow> zpvalid zp3 \<longrightarrow> Q.qzt_fitl x qtl)"
  using assms
proof (induction qtl)
  case (QztLeaf q1 q2 q3 qtl)
  show ?case
  proof (cases "fitqzp zp3 q3 \<and> fitqzp zp2 q2 \<and> fitqzp zp1 q1")
    case True
    then have r: "red_popqzp zp1 q1 \<and> red_popqzp zp2 q2 \<and> red_popqzp zp3 q3" using QztLeaf.prems by simp
    show ?thesis using True r fitq_zp by (auto simp: Q.qzt_fitl.simps)
  next
    case False
    then have "red_qzt_leaf zp1 zp2 zp3 qtl" using QztLeaf.prems by simp
    then show ?thesis using QztLeaf.IH by simp
  qed
qed simp_all

section \<open>The main search invariant\<close>

lemma shiftr_reg:
  assumes "1 < psize pr"
  shows "zshiftr zi1 (Zpart zi pl pr) = Zpart zi1 (shift_part pr pl) (drop_part 1 pr)"
  using assms by (cases pr; simp add: shift_part_def; auto)

lemma no_qzt_fitl:
  assumes "arity G y = nat_of_qarity qa1" "arity G (n y) = nat_of_qarity qa2"
    "arity G (n (n y)) = nat_of_qarity qa3"
  shows "\<not> Q.qzt_fitl y (qzt_get3 qa1 qa2 qa3 qt)"
  using nofit[of y] assms by (simp add: Q.qzt_fit_def Q.qzt_fita_def Q.ax1_def Q.ax2_def Q.ax3_def qarity_of_qarity)

lemma getr2:
  assumes "qzt_proper (qzt_getr r2 (qzt_getr r1 T))"
  shows "qzt_getr r2 (qzt_getr r1 T) = qzt_get1 (topqa r2) (qzt_get1 (topqa r1) T) \<and>
         fitqa r1 (topqa r1) \<and> fitqa r2 (topqa r2)"
proof -
  have a: "fitqa r2 (topqa r2)" "qzt_get1 (topqa r2) (qzt_getr r1 T) = qzt_getr r2 (qzt_getr r1 T)"
    "qzt_proper (qzt_getr r1 T)" using qzt_getr_fit[OF assms] by simp_all
  have b: "fitqa r1 (topqa r1)" "qzt_get1 (topqa r1) T = qzt_getr r1 T" using qzt_getr_fit[OF a(3)] by simp_all
  show ?thesis using a b by simp
qed

lemma sqt_get:
  assumes "qzt_proper (qzt_getr s (qzt_truncate qt))"
  shows "qzt_getr s (qzt_truncate qt) = qzt_get1 (topqa s) qt \<and> fitqa s (topqa s)"
proof -
  have a: "fitqa s (topqa s)" "qzt_get1 (topqa s) (qzt_truncate qt) = qzt_getr s (qzt_truncate qt)"
    "qzt_proper (qzt_truncate qt)" using qzt_getr_fit[OF assms] by simp_all
  have "qzt_proper (qzt_get1 (topqa s) (qzt_truncate qt))" using a(2) assms by simp
  then have "qzt_get1 (topqa s) (qzt_truncate qt) = qzt_get1 (topqa s) qt" by (rule qzt_get1_truncate)
  then show ?thesis using a by simp
qed

lemma leaf_contra:
  assumes leaf: "red_qzt_leaf zp1 zp2 zp3 (qzt_getr a (qzt_getr b C))"
    and C: "qzt_proper (qzt_getr a (qzt_getr b C)) \<Longrightarrow> qzt_get1 (topqa a) (qzt_get1 (topqa b) C) = qzt_get3 qh (topqa b) (topqa a) qt"
    and f1: "zpfit (qstepR G y) zp1" "zpvalid zp1" and f2: "zpfit (qstepR G (n y)) zp2" "zpvalid zp2"
    and f3: "zpfit (qstepR G (n (n y))) zp3" "zpvalid zp3"
    and a1: "arity G y = nat_of_qarity qh"
    and a2: "fitqa b (topqa b) \<Longrightarrow> arity G (n y) = nat_of_qarity (topqa b)"
    and a3: "fitqa a (topqa a) \<Longrightarrow> arity G (n (n y)) = nat_of_qarity (topqa a)"
  shows False
proof -
  have pr: "qzt_proper (qzt_getr a (qzt_getr b C))"
    and fl: "Q.qzt_fitl y (qzt_getr a (qzt_getr b C))"
    using red_qzt_leaf_fit[OF leaf] f1 f2 f3 by blast+
  have g: "qzt_getr a (qzt_getr b C) = qzt_get1 (topqa a) (qzt_get1 (topqa b) C)"
    "fitqa b (topqa b)" "fitqa a (topqa a)" using getr2[OF pr] by simp_all
  have "Q.qzt_fitl y (qzt_get3 qh (topqa b) (topqa a) qt)" using fl g(1) C[OF pr] by simp
  then show False using no_qzt_fitl[OF a1 a2[OF g(2)] a3[OF g(3)]] by blast
qed

lemma G1:
  assumes "arity G w = m" "j < m"
  shows "f (e (((e \<circ> n) ^^ j) w)) = qstepR G ((f ^^ (m - j - 1)) w)"
proof -
  have "((e \<circ> n) ^^ j) w = (f ^^ (m - j)) w" using enk[OF assms(1)] assms(2) by simp
  moreover have "m - j = Suc (m - j - 1)" using assms(2) by simp
  ultimately have "((e \<circ> n) ^^ j) w = f ((f ^^ (m - j - 1)) w)" by (metis comp_apply funpow.simps(2))
  then show ?thesis by (simp add: qstepR_def fe_nn)
qed

lemma G1h: "zmove Zhatr (f x) = f (e ((e \<circ> n) (e x)))"
proof -
  have "n (e x) = e (e (n (e x)))" by simp
  then show ?thesis by simp
qed

lemma G2: "qstepR G (n ((f ^^ Suc (Suc j)) w)) = e ((f ^^ j) w)"
  by (simp add: qstepR_def)

lemma G3: "n ((f ^^ Suc j) w) = e ((f ^^ j) w)" by simp

lemma G4: "arity G (e ((f ^^ 2) (e (f x)))) = arity G (e (((e \<circ> n) ^^ 2) (e x)))"
  by (simp add: eval_nat_numeral f_ne ar_en)

lemma no_red_step:
  assumes v: "zvalid pl pr" and npr: "1 < psize pr"
  shows "\<not> red_step (Zpart Zhub pl pr)"
proof
  assume red: "red_step (Zpart Zhub pl pr)"
  define x where "x = zorg pl"
  define pl1 where "pl1 = shift_part pr pl"
  define pr1 where "pr1 = drop_part 1 pr"
  have sh: "\<And>zi zi1. zshiftr zi1 (Zpart zi pl pr) = Zpart zi1 pl1 pr1"
    using shiftr_reg[OF npr] by (simp add: pl1_def pr1_def)
  have vp: "\<And>zi. zpvalid (Zpart zi pl pr)" using v by simp
  have vp1: "\<And>zi. zpvalid (Zpart zi pl1 pr1)" using zpvalid_shiftr[OF vp, of _ Zhub] sh by metis
  have v1: "zvalid pl1 pr1" using vp1[of Zhub] by simp
  have d1: "\<And>zi. zdart (Zpart zi pl1 pr1) = zmove zi (f x)"
    using zdart_shiftr[OF vp] sh by (metis x_def zporg.simps)
  have xa: "arity G x = nhub" using nFx0 by (simp add: x_def zorg_def arity_funpow)
  let ?s = "get_spoke pr" and ?sl = "get_spoke pl"
  let ?sqt = "qzt_getr ?s (qzt_truncate qt)"
  have sqtp: "qzt_proper ?sqt" using red by (simp add: rp.red_step_def sh Let_def)
  have sq: "?sqt = qzt_get1 (topqa ?s) qt" and fs: "fitqa ?s (topqa ?s)" using sqt_get[OF sqtp] by simp_all
  have aex: "arity G (e x) = nat_of_qarity (topqa ?s) \<or> \<not> red_popr_spoke pr"
    using red_popr_spoke_fit[OF v fs] by (auto simp: x_def)
  let ?L1 = "red_qzt_leaf (Zpart Zhubr pl1 pr1) (zshiftl Zhubl (Zpart Zhub pl pr)) (Zpart Zhat pl pr)
           (qzt_getr ?s (qzt_getr ?sl (qzt_get1 ahub qt)))"
  let ?L2 = "red_qzt_leaf (Zpart (zfanLt pr) pl1 pr1) (Zpart Zhub pl pr) (Zpart (zfanRt pl) pl pr)
           (qzt_getr (get_hat pr) (qzt_getr ?sl ?sqt))"
  have body: "if ?L1 then red_popr_spoke pr \<and> red_popl_spoke pl pr
    else if ?L2 then red_popr_hat pr \<and> red_popl_spoke pl pr \<and> red_popr_spoke pr
    else (case pr of
        Pcons s0 h _ \<Rightarrow>
          s0 = Pr55 \<and> red_qzt_leaf (Zpart Zhatr pl1 pr1) (Zpart Zhatl pl pr) (Zpart Znil pl1 pr1)
                        (qzt_getr (get_hat pr1) (qzt_getr h ?sqt)) \<and>
          red_popr_hat pr1 \<and> red_popr_hat pr
      | Pcons6 h f1 _ \<Rightarrow>
          (if red_qzt_leaf (Zpart Zfan0l pl1 pr1) (Zpart Zhatl pl pr) (Zpart Znil pl1 pr1) (qzt_getr f1 (qzt_getr h ?sqt))
           then red_popl_fan1r pl1 pr1 \<and> red_popr_hat pr
           else red_qzt_leaf (Zpart Zhatr pl1 pr1) (Zpart Zfan0r pl1 pr1) (Zpart Znil pl1 pr1)
                  (qzt_getr (get_hat pr1) (qzt_getr f1 ?sqt)) \<and>
                red_popr_hat pr1 \<and> red_popl_fan1r pl1 pr1)
      | Pcons7 h f1 f2 _ \<Rightarrow>
          (if red_qzt_leaf (Zpart Zfan1l pl1 pr1) (Zpart Zhatl pl pr) (Zpart Znil pl1 pr1) (qzt_getr f1 (qzt_getr h ?sqt))
           then red_popl_fan1r pl1 pr1 \<and> red_popr_hat pr
           else if red_qzt_leaf (Zpart Zfan0l pl1 pr1) (Zpart Zfan0r pl1 pr1) (Zpart Znil pl1 pr1)
                  (qzt_getr f2 (qzt_getr f1 ?sqt))
           then red_popl_fan2r pl1 pr1 \<and> red_popl_fan1r pl1 pr1
           else red_qzt_leaf (Zpart Zhatr pl1 pr1) (Zpart Zfan1r pl1 pr1) (Zpart Znil pl1 pr1)
                  (qzt_getr (get_hat pr1) (qzt_getr f2 ?sqt)) \<and>
                red_popr_hat pr1 \<and> red_popl_fan2r pl1 pr1)
      | Pcons8 h f1 f2 f3 _ \<Rightarrow>
          (if red_qzt_leaf (Zpart Zfan2l pl1 pr1) (Zpart Zhatl pl pr) (Zpart Znil pl1 pr1) (qzt_getr f1 (qzt_getr h ?sqt))
           then red_popl_fan1r pl1 pr1 \<and> red_popr_hat pr
           else if red_qzt_leaf (Zpart Zfan1l pl1 pr1) (Zpart Zfan0r pl1 pr1) (Zpart Znil pl1 pr1)
                  (qzt_getr f2 (qzt_getr f1 ?sqt))
           then red_popl_fan2r pl1 pr1 \<and> red_popl_fan1r pl1 pr1
           else if red_qzt_leaf (Zpart Zfan0l pl1 pr1) (Zpart Zfan1r pl1 pr1) (Zpart Znil pl1 pr1)
                  (qzt_getr f3 (qzt_getr f2 ?sqt))
           then red_popl_fan3r pl1 pr1 \<and> red_popl_fan2r pl1 pr1
           else red_qzt_leaf (Zpart Zhatr pl1 pr1) (Zpart Zfan2r pl1 pr1) (Zpart Znil pl1 pr1)
                  (qzt_getr (get_hat pr1) (qzt_getr f3 ?sqt)) \<and>
                red_popr_hat pr1 \<and> red_popl_fan3r pl1 pr1)
      | Pnil \<Rightarrow> False)"
    using red sh by (simp add: rp.red_step_def Let_def)
  have np: "\<not> zproper (Zpart Znil pl1 pr1)" by simp
  have zpnil: "zpfit y (Zpart Znil pl1 pr1)" for y by (simp add: zpfit_def)
  define w where "w = e x"
  have pl1x: "zorg pl1 = f x"
  proof -
    have "psize pl1 = Suc (psize pl)" using npr by (cases pr) (simp_all add: pl1_def shift_part_def)
    then show ?thesis by (simp add: zorg_def x_def)
  qed
  note [simp] = pl1x
  have zx: "zorg pl = x" by (simp add: x_def)
  note [simp] = zx
  show False
  proof (cases ?L1)
    case L1: True
    then have rp: "red_popr_spoke pr" "red_popl_spoke pl pr" using body by simp_all
    show False
    proof (rule leaf_contra[OF L1, where y = x and qh = ahub])
      show "qzt_get1 (topqa ?s) (qzt_get1 (topqa ?sl) (qzt_get1 ahub qt)) = qzt_get3 ahub (topqa ?sl) (topqa ?s) qt"
        by (simp add: qzt_get3_def qzt_get2_def)
      show "zpfit (qstepR G x) (Zpart Zhubr pl1 pr1)" by (simp add: zpfit_def d1 qstepR_def)
      show "zpfit (qstepR G (n x)) (zshiftl Zhubl (Zpart Zhub pl pr))"
        by (simp add: zpfit_def zdart_shiftl qstepR_def)
      show "zpfit (qstepR G (n (n x))) (Zpart Zhat pl pr)" by (simp add: zpfit_def qstepR_def)
      show "arity G x = nat_of_qarity ahub" by (rule xa)
      show "arity G (n x) = nat_of_qarity (topqa ?sl)" if "fitqa ?sl (topqa ?sl)"
        using red_popl_spoke_fit[OF v that rp(2)] by simp
      show "arity G (n (n x)) = nat_of_qarity (topqa ?s)" if "fitqa ?s (topqa ?s)"
        using red_popr_spoke_fit[OF v that rp(1)] by simp
    qed (use vp1 vp zpvalid_shiftl[OF vp] in simp_all)
  next
    case nL1: False
    show False
    proof (cases ?L2)
      case L2: True
      then have rp: "red_popr_hat pr" "red_popl_spoke pl pr" "red_popr_spoke pr" using body nL1 by simp_all
      have fsl: "fitqa ?sl (topqa ?sl)"
        using getr2[of "get_hat pr" ?sl ?sqt] red_qzt_leaf_fit[OF L2] by blast
      have as: "arity G (e x) = nat_of_qarity (topqa ?s)"
        using red_popr_spoke_fit[OF v fs rp(3)] by simp
      define y2 where "y2 = f (n (n x))"
      have topr: "zpfit_top (Zpart Zhatr pl pr)" using as by (simp add: zpfit_top_def)
      have asl: "arity G (n x) = nat_of_qarity (topqa ?sl)" if "fitqa ?sl (topqa ?sl)"
        using red_popl_spoke_fit[OF v that rp(2)] by simp
      show False
      proof (rule leaf_contra[OF L2, where y = y2 and qh = "topqa ?s"])
        show "qzt_proper (qzt_getr (get_hat pr) (qzt_getr ?sl ?sqt)) \<Longrightarrow>
          qzt_get1 (topqa (get_hat pr)) (qzt_get1 (topqa ?sl) ?sqt) = qzt_get3 (topqa ?s) (topqa ?sl) (topqa (get_hat pr)) qt"
          using sq by (simp add: qzt_get3_def qzt_get2_def)
        have "zpfit (qstepR G (zdart (Zpart Zhatr pl pr))) (zstepRt (Zpart Zhatr pl pr))"
          by (rule zdart_stepRt[OF topr vp])
        then show "zpfit (qstepR G y2) (Zpart (zfanLt pr) pl1 pr1)" using sh by (simp add: y2_def)
        show "zpfit (qstepR G (n y2)) (Zpart Zhub pl pr)" by (simp add: zpfit_def y2_def wn)
        have topl: "zpfit_top (Zpart Zhatl pl pr)"
          using asl[OF fsl] by (simp add: zpfit_top_def)
        have "zpfit (qstepL G (zdart (Zpart Zhatl pl pr))) (zstepLt (Zpart Zhatl pl pr))"
          by (rule zdart_stepLt[OF topl vp])
        then show "zpfit (qstepR G (n (n y2))) (Zpart (zfanRt pl) pl pr)"
          by (simp add: y2_def wn)
        show "arity G y2 = nat_of_qarity (topqa ?s)" using as by (simp add: y2_def)
        show "arity G (n y2) = nat_of_qarity (topqa ?sl)" if "fitqa ?sl (topqa ?sl)"
          using asl[OF that] by (simp add: y2_def fe_nn ar_ef)
        show "arity G (n (n y2)) = nat_of_qarity (topqa (get_hat pr))" if "fitqa (get_hat pr) (topqa (get_hat pr))"
          using red_popr_hat_fit[OF v that rp(1)]
          by (simp add: y2_def subpart_loc_move.simps eval_nat_numeral fe_nn ar_ef)
      qed (use vp1 vp in simp_all)
    next
      case nL2: False
      have body3: "case pr of
        Pcons s0 h _ \<Rightarrow>
          s0 = Pr55 \<and> red_qzt_leaf (Zpart Zhatr pl1 pr1) (Zpart Zhatl pl pr) (Zpart Znil pl1 pr1)
                        (qzt_getr (get_hat pr1) (qzt_getr h ?sqt)) \<and>
          red_popr_hat pr1 \<and> red_popr_hat pr
      | Pcons6 h f1 _ \<Rightarrow>
          (if red_qzt_leaf (Zpart Zfan0l pl1 pr1) (Zpart Zhatl pl pr) (Zpart Znil pl1 pr1) (qzt_getr f1 (qzt_getr h ?sqt))
           then red_popl_fan1r pl1 pr1 \<and> red_popr_hat pr
           else red_qzt_leaf (Zpart Zhatr pl1 pr1) (Zpart Zfan0r pl1 pr1) (Zpart Znil pl1 pr1)
                  (qzt_getr (get_hat pr1) (qzt_getr f1 ?sqt)) \<and>
                red_popr_hat pr1 \<and> red_popl_fan1r pl1 pr1)
      | Pcons7 h f1 f2 _ \<Rightarrow>
          (if red_qzt_leaf (Zpart Zfan1l pl1 pr1) (Zpart Zhatl pl pr) (Zpart Znil pl1 pr1) (qzt_getr f1 (qzt_getr h ?sqt))
           then red_popl_fan1r pl1 pr1 \<and> red_popr_hat pr
           else if red_qzt_leaf (Zpart Zfan0l pl1 pr1) (Zpart Zfan0r pl1 pr1) (Zpart Znil pl1 pr1)
                  (qzt_getr f2 (qzt_getr f1 ?sqt))
           then red_popl_fan2r pl1 pr1 \<and> red_popl_fan1r pl1 pr1
           else red_qzt_leaf (Zpart Zhatr pl1 pr1) (Zpart Zfan1r pl1 pr1) (Zpart Znil pl1 pr1)
                  (qzt_getr (get_hat pr1) (qzt_getr f2 ?sqt)) \<and>
                red_popr_hat pr1 \<and> red_popl_fan2r pl1 pr1)
      | Pcons8 h f1 f2 f3 _ \<Rightarrow>
          (if red_qzt_leaf (Zpart Zfan2l pl1 pr1) (Zpart Zhatl pl pr) (Zpart Znil pl1 pr1) (qzt_getr f1 (qzt_getr h ?sqt))
           then red_popl_fan1r pl1 pr1 \<and> red_popr_hat pr
           else if red_qzt_leaf (Zpart Zfan1l pl1 pr1) (Zpart Zfan0r pl1 pr1) (Zpart Znil pl1 pr1)
                  (qzt_getr f2 (qzt_getr f1 ?sqt))
           then red_popl_fan2r pl1 pr1 \<and> red_popl_fan1r pl1 pr1
           else if red_qzt_leaf (Zpart Zfan0l pl1 pr1) (Zpart Zfan1r pl1 pr1) (Zpart Znil pl1 pr1)
                  (qzt_getr f3 (qzt_getr f2 ?sqt))
           then red_popl_fan3r pl1 pr1 \<and> red_popl_fan2r pl1 pr1
           else red_qzt_leaf (Zpart Zhatr pl1 pr1) (Zpart Zfan2r pl1 pr1) (Zpart Znil pl1 pr1)
                  (qzt_getr (get_hat pr1) (qzt_getr f3 ?sqt)) \<and>
                red_popr_hat pr1 \<and> red_popl_fan3r pl1 pr1)
      | Pnil \<Rightarrow> False" using body nL1 nL2 by simp
      have br: False
        if leaf: "red_qzt_leaf zp1 zp2 (Zpart Znil pl1 pr1) (qzt_getr a (qzt_getr b ?sqt))"
          and d1': "zdart zp1 = qstepR G y" and v1': "zpvalid zp1"
          and d2': "zdart zp2 = qstepR G (n y)" and v2': "zpvalid zp2"
          and a1: "arity G y = nat_of_qarity (topqa ?s)"
          and a2: "fitqa b (topqa b) \<Longrightarrow> arity G (n y) = nat_of_qarity (topqa b)"
          and a3: "fitqa a (topqa a) \<Longrightarrow> arity G (e y) = nat_of_qarity (topqa a)"
        for zp1 zp2 a b y
      proof (rule leaf_contra[OF leaf, where y = y and qh = "topqa ?s"])
        show "qzt_proper (qzt_getr a (qzt_getr b ?sqt)) \<Longrightarrow>
          qzt_get1 (topqa a) (qzt_get1 (topqa b) ?sqt) = qzt_get3 (topqa ?s) (topqa b) (topqa a) qt"
          using sq by (simp add: qzt_get3_def qzt_get2_def)
        show "arity G (n (n y)) = nat_of_qarity (topqa a)" if "fitqa a (topqa a)" using a3[OF that] by simp
      qed (use d1' d2' v1' v2' a1 a2 zpnil vp1 in \<open>simp_all add: zpfit_def\<close>)
      have fx: "fitp G x pr" using zvalid_fit_r[OF v] by simp
      have dhatl: "zdart (Zpart Zhatl pl pr) = qstepR G (n ((f ^^ 3) w))"
        using G2[of 1 w] by (simp add: w_def fe_nn eval_nat_numeral)
      have hat0: "fitqa h (topqa h) \<Longrightarrow> red_popr_hat pr \<Longrightarrow> get_hat pr = h \<Longrightarrow>
          arity G (n ((f ^^ 3) w)) = nat_of_qarity (topqa h)" for h
        using red_popr_hat_fit[OF v, of "topqa h"] G3[of 2 w]
        by (simp add: w_def subpart_loc_move.simps eval_nat_numeral)
      have hat1: "fitqa (get_hat pr1) (topqa (get_hat pr1)) \<Longrightarrow> red_popr_hat pr1 \<Longrightarrow>
          arity G (e (((e \<circ> n) ^^ 2) w)) = nat_of_qarity (topqa (get_hat pr1))"
        using red_popr_hat_fit[OF v1, of "topqa (get_hat pr1)"] G4[of x]
        by (simp add: w_def subpart_loc_move.simps)
      have zfr: "zdart (Zpart Zfan1r pl1 pr1) = e ((f ^^ 3) w)" "zdart (Zpart Zfan2r pl1 pr1) = e ((f ^^ 4) w)"
        "zdart (Zpart Zfan3r pl1 pr1) = e ((f ^^ 5) w)" "zdart (Zpart Zfan0r pl1 pr1) = e ((f ^^ 2) w)"
        by (simp_all add: w_def)
      have dfl: "zdart (Zpart Zfan0l pl1 pr1) = f (e (((e \<circ> n) ^^ 2) w))"
        "zdart (Zpart Zfan1l pl1 pr1) = f (e (((e \<circ> n) ^^ 3) w))"
        "zdart (Zpart Zfan2l pl1 pr1) = f (e (((e \<circ> n) ^^ 4) w))"
        "zdart (Zpart Zhatr pl1 pr1) = f (e (((e \<circ> n) ^^ 1) w))"
        using G1h[of x] by (simp_all add: w_def d1 del: funpow.simps zmove.simps) (simp_all add: d1)
      have dfr: "zdart (Zpart Zfan0r pl1 pr1) = qstepR G (n ((f ^^ 4) w))"
        "zdart (Zpart Zfan1r pl1 pr1) = qstepR G (n ((f ^^ 5) w))"
        "zdart (Zpart Zfan2r pl1 pr1) = qstepR G (n ((f ^^ 6) w))"
        using zfr G2[of 2 w] G2[of 3 w] G2[of 4 w] by (simp_all add: eval_nat_numeral)
      have hatm: "arity G (e (((e \<circ> n) ^^ 2) w)) = arity G (e ((f ^^ (m - 2)) w))"
        if "arity G w = m" "2 \<le> m" for m using enk[OF that] by simp
      have nf: "n ((f ^^ Suc k) w) = e ((f ^^ k) w)" for k by (rule G3)
      have ar_ey: "arity G (e ((f ^^ k) w)) = arity G (e ((f ^^ k) w))" for k ..
      show False
      proof (cases pr)
        case Pnil then show False using body3 by simp
      next
        case (Pcons s0 h p)
        have s0: "s0 = Pr55" using body3 Pcons by simp
        have lf: "red_qzt_leaf (Zpart Zhatr pl1 pr1) (Zpart Zhatl pl pr) (Zpart Znil pl1 pr1)
                        (qzt_getr (get_hat pr1) (qzt_getr h ?sqt))" and r1: "red_popr_hat pr1" and r0: "red_popr_hat pr"
          using body3 Pcons s0 by simp_all
        have m: "arity G w = 5" using fx Pcons s0 by (simp add: w_def subpart_loc_move.simps)
        show False
        proof (rule br[OF lf, where y = "(f ^^ 3) w"])
          show "zdart (Zpart Zhatr pl1 pr1) = qstepR G ((f ^^ 3) w)" using dfl(4) G1[OF m, of 1] by simp
          show "zdart (Zpart Zhatl pl pr) = qstepR G (n ((f ^^ 3) w))" by (rule dhatl)
          show "arity G ((f ^^ 3) w) = nat_of_qarity (topqa ?s)" using m Pcons s0 by (simp add: arity_funpow)
          show "arity G (n ((f ^^ 3) w)) = nat_of_qarity (topqa h)" if "fitqa h (topqa h)"
            using hat0[OF that r0] Pcons by (simp add: get_hat_def)
          show "arity G (e ((f ^^ 3) w)) = nat_of_qarity (topqa (get_hat pr1))"
            if "fitqa (get_hat pr1) (topqa (get_hat pr1))" using hat1[OF that r1] hatm[OF m] by simp
        qed (use vp vp1 in simp_all)
      next
        case (Pcons6 h f1 p)
        have m: "arity G w = 6" using fx Pcons6 by (simp add: w_def subpart_loc_move.simps)
        have pl1s: "pl1 = Pcons6 h f1 pl" using Pcons6 by (simp add: pl1_def shift_part_def)
        have fan1: "fitqa f1 (topqa f1) \<Longrightarrow> red_popl_fan1r pl1 pr1 \<Longrightarrow> arity G (e ((f ^^ 3) w)) = nat_of_qarity (topqa f1)"
          using red_popl_fanr_fit(1)[OF v1, of "topqa f1"] zfr(1) pl1s by simp
        show False
        proof (cases "red_qzt_leaf (Zpart Zfan0l pl1 pr1) (Zpart Zhatl pl pr) (Zpart Znil pl1 pr1) (qzt_getr f1 (qzt_getr h ?sqt))")
          case lf: True
          then have r: "red_popl_fan1r pl1 pr1" "red_popr_hat pr" using body3 Pcons6 by simp_all
          show False
          proof (rule br[OF lf, where y = "(f ^^ 3) w"])
            show "zdart (Zpart Zfan0l pl1 pr1) = qstepR G ((f ^^ 3) w)" using dfl(1) G1[OF m, of 2] by simp
            show "zdart (Zpart Zhatl pl pr) = qstepR G (n ((f ^^ 3) w))" by (rule dhatl)
            show "arity G ((f ^^ 3) w) = nat_of_qarity (topqa ?s)" using m Pcons6 by (simp add: arity_funpow)
            show "arity G (n ((f ^^ 3) w)) = nat_of_qarity (topqa h)" if "fitqa h (topqa h)"
              using hat0[OF that r(2)] Pcons6 by (simp add: get_hat_def)
            show "arity G (e ((f ^^ 3) w)) = nat_of_qarity (topqa f1)" if "fitqa f1 (topqa f1)"
              using fan1[OF that r(1)] .
          qed (use vp vp1 in simp_all)
        next
          case nlf: False
          then have lf: "red_qzt_leaf (Zpart Zhatr pl1 pr1) (Zpart Zfan0r pl1 pr1) (Zpart Znil pl1 pr1)
                  (qzt_getr (get_hat pr1) (qzt_getr f1 ?sqt))" and r: "red_popr_hat pr1" "red_popl_fan1r pl1 pr1"
            using body3 Pcons6 by simp_all
          show False
          proof (rule br[OF lf, where y = "(f ^^ 4) w"])
            show "zdart (Zpart Zhatr pl1 pr1) = qstepR G ((f ^^ 4) w)" using dfl(4) G1[OF m, of 1] by simp
            show "zdart (Zpart Zfan0r pl1 pr1) = qstepR G (n ((f ^^ 4) w))" by (rule dfr(1))
            show "arity G ((f ^^ 4) w) = nat_of_qarity (topqa ?s)" using m Pcons6 by (simp add: arity_funpow)
            show "arity G (n ((f ^^ 4) w)) = nat_of_qarity (topqa f1)" if "fitqa f1 (topqa f1)"
              using fan1[OF that r(2)] nf[of 3] by simp
            show "arity G (e ((f ^^ 4) w)) = nat_of_qarity (topqa (get_hat pr1))"
              if "fitqa (get_hat pr1) (topqa (get_hat pr1))" using hat1[OF that r(1)] hatm[OF m] by simp
          qed (use vp vp1 in simp_all)
        qed
      next
        case (Pcons7 h f1 f2 p)
        have m: "arity G w = 7" using fx Pcons7 by (simp add: w_def subpart_loc_move.simps)
        have pl1s: "pl1 = Pcons7 h f1 f2 pl" using Pcons7 by (simp add: pl1_def shift_part_def)
        have fan1: "fitqa f1 (topqa f1) \<Longrightarrow> red_popl_fan1r pl1 pr1 \<Longrightarrow> arity G (e ((f ^^ 3) w)) = nat_of_qarity (topqa f1)"
          using red_popl_fanr_fit(1)[OF v1, of "topqa f1"] zfr(1) pl1s by simp
        have fan2: "fitqa f2 (topqa f2) \<Longrightarrow> red_popl_fan2r pl1 pr1 \<Longrightarrow> arity G (e ((f ^^ 4) w)) = nat_of_qarity (topqa f2)"
          using red_popl_fanr_fit(2)[OF v1, of "topqa f2"] zfr(2) pl1s by simp
        show False
        proof (cases "red_qzt_leaf (Zpart Zfan1l pl1 pr1) (Zpart Zhatl pl pr) (Zpart Znil pl1 pr1) (qzt_getr f1 (qzt_getr h ?sqt))")
          case lf: True
          then have r: "red_popl_fan1r pl1 pr1" "red_popr_hat pr" using body3 Pcons7 by simp_all
          show False
          proof (rule br[OF lf, where y = "(f ^^ 3) w"])
            show "zdart (Zpart Zfan1l pl1 pr1) = qstepR G ((f ^^ 3) w)" using dfl(2) G1[OF m, of 3] by simp
            show "zdart (Zpart Zhatl pl pr) = qstepR G (n ((f ^^ 3) w))" by (rule dhatl)
            show "arity G ((f ^^ 3) w) = nat_of_qarity (topqa ?s)" using m Pcons7 by (simp add: arity_funpow)
            show "arity G (n ((f ^^ 3) w)) = nat_of_qarity (topqa h)" if "fitqa h (topqa h)"
              using hat0[OF that r(2)] Pcons7 by (simp add: get_hat_def)
            show "arity G (e ((f ^^ 3) w)) = nat_of_qarity (topqa f1)" if "fitqa f1 (topqa f1)"
              using fan1[OF that r(1)] .
          qed (use vp vp1 in simp_all)
        next
          case nlf1: False
          show False
          proof (cases "red_qzt_leaf (Zpart Zfan0l pl1 pr1) (Zpart Zfan0r pl1 pr1) (Zpart Znil pl1 pr1) (qzt_getr f2 (qzt_getr f1 ?sqt))")
            case lf: True
            then have r: "red_popl_fan2r pl1 pr1" "red_popl_fan1r pl1 pr1" using body3 Pcons7 nlf1 by simp_all
            show False
            proof (rule br[OF lf, where y = "(f ^^ 4) w"])
              show "zdart (Zpart Zfan0l pl1 pr1) = qstepR G ((f ^^ 4) w)" using dfl(1) G1[OF m, of 2] by simp
              show "zdart (Zpart Zfan0r pl1 pr1) = qstepR G (n ((f ^^ 4) w))" by (rule dfr(1))
              show "arity G ((f ^^ 4) w) = nat_of_qarity (topqa ?s)" using m Pcons7 by (simp add: arity_funpow)
              show "arity G (n ((f ^^ 4) w)) = nat_of_qarity (topqa f1)" if "fitqa f1 (topqa f1)"
                using fan1[OF that r(2)] nf[of 3] by simp
              show "arity G (e ((f ^^ 4) w)) = nat_of_qarity (topqa f2)" if "fitqa f2 (topqa f2)"
                using fan2[OF that r(1)] .
            qed (use vp vp1 in simp_all)
          next
            case nlf2: False
            then have lf: "red_qzt_leaf (Zpart Zhatr pl1 pr1) (Zpart Zfan1r pl1 pr1) (Zpart Znil pl1 pr1)
                  (qzt_getr (get_hat pr1) (qzt_getr f2 ?sqt))" and r: "red_popr_hat pr1" "red_popl_fan2r pl1 pr1"
              using body3 Pcons7 nlf1 by simp_all
            show False
            proof (rule br[OF lf, where y = "(f ^^ 5) w"])
              show "zdart (Zpart Zhatr pl1 pr1) = qstepR G ((f ^^ 5) w)" using dfl(4) G1[OF m, of 1] by simp
              show "zdart (Zpart Zfan1r pl1 pr1) = qstepR G (n ((f ^^ 5) w))" by (rule dfr(2))
              show "arity G ((f ^^ 5) w) = nat_of_qarity (topqa ?s)" using m Pcons7 by (simp add: arity_funpow)
              show "arity G (n ((f ^^ 5) w)) = nat_of_qarity (topqa f2)" if "fitqa f2 (topqa f2)"
                using fan2[OF that r(2)] nf[of 4] by simp
              show "arity G (e ((f ^^ 5) w)) = nat_of_qarity (topqa (get_hat pr1))"
                if "fitqa (get_hat pr1) (topqa (get_hat pr1))" using hat1[OF that r(1)] hatm[OF m] by simp
            qed (use vp vp1 in simp_all)
          qed
        qed
      next
        case (Pcons8 h f1 f2 f3 p)
        have m: "arity G w = 8" using fx Pcons8 by (simp add: w_def subpart_loc_move.simps)
        have pl1s: "pl1 = Pcons8 h f1 f2 f3 pl" using Pcons8 by (simp add: pl1_def shift_part_def)
        have fan1: "fitqa f1 (topqa f1) \<Longrightarrow> red_popl_fan1r pl1 pr1 \<Longrightarrow> arity G (e ((f ^^ 3) w)) = nat_of_qarity (topqa f1)"
          using red_popl_fanr_fit(1)[OF v1, of "topqa f1"] zfr(1) pl1s by simp
        have fan2: "fitqa f2 (topqa f2) \<Longrightarrow> red_popl_fan2r pl1 pr1 \<Longrightarrow> arity G (e ((f ^^ 4) w)) = nat_of_qarity (topqa f2)"
          using red_popl_fanr_fit(2)[OF v1, of "topqa f2"] zfr(2) pl1s by simp
        have fan3: "fitqa f3 (topqa f3) \<Longrightarrow> red_popl_fan3r pl1 pr1 \<Longrightarrow> arity G (e ((f ^^ 5) w)) = nat_of_qarity (topqa f3)"
          using red_popl_fanr_fit(3)[OF v1, of "topqa f3"] zfr(3) pl1s by simp
        show False
        proof (cases "red_qzt_leaf (Zpart Zfan2l pl1 pr1) (Zpart Zhatl pl pr) (Zpart Znil pl1 pr1) (qzt_getr f1 (qzt_getr h ?sqt))")
          case lf: True
          then have r: "red_popl_fan1r pl1 pr1" "red_popr_hat pr" using body3 Pcons8 by simp_all
          show False
          proof (rule br[OF lf, where y = "(f ^^ 3) w"])
            show "zdart (Zpart Zfan2l pl1 pr1) = qstepR G ((f ^^ 3) w)" using dfl(3) G1[OF m, of 4] by simp
            show "zdart (Zpart Zhatl pl pr) = qstepR G (n ((f ^^ 3) w))" by (rule dhatl)
            show "arity G ((f ^^ 3) w) = nat_of_qarity (topqa ?s)" using m Pcons8 by (simp add: arity_funpow)
            show "arity G (n ((f ^^ 3) w)) = nat_of_qarity (topqa h)" if "fitqa h (topqa h)"
              using hat0[OF that r(2)] Pcons8 by (simp add: get_hat_def)
            show "arity G (e ((f ^^ 3) w)) = nat_of_qarity (topqa f1)" if "fitqa f1 (topqa f1)"
              using fan1[OF that r(1)] .
          qed (use vp vp1 in simp_all)
        next
          case nlf1: False
          show False
          proof (cases "red_qzt_leaf (Zpart Zfan1l pl1 pr1) (Zpart Zfan0r pl1 pr1) (Zpart Znil pl1 pr1) (qzt_getr f2 (qzt_getr f1 ?sqt))")
            case lf: True
            then have r: "red_popl_fan2r pl1 pr1" "red_popl_fan1r pl1 pr1" using body3 Pcons8 nlf1 by simp_all
            show False
            proof (rule br[OF lf, where y = "(f ^^ 4) w"])
              show "zdart (Zpart Zfan1l pl1 pr1) = qstepR G ((f ^^ 4) w)" using dfl(2) G1[OF m, of 3] by simp
              show "zdart (Zpart Zfan0r pl1 pr1) = qstepR G (n ((f ^^ 4) w))" by (rule dfr(1))
              show "arity G ((f ^^ 4) w) = nat_of_qarity (topqa ?s)" using m Pcons8 by (simp add: arity_funpow)
              show "arity G (n ((f ^^ 4) w)) = nat_of_qarity (topqa f1)" if "fitqa f1 (topqa f1)"
                using fan1[OF that r(2)] nf[of 3] by simp
              show "arity G (e ((f ^^ 4) w)) = nat_of_qarity (topqa f2)" if "fitqa f2 (topqa f2)"
                using fan2[OF that r(1)] .
            qed (use vp vp1 in simp_all)
          next
            case nlf2: False
            show False
            proof (cases "red_qzt_leaf (Zpart Zfan0l pl1 pr1) (Zpart Zfan1r pl1 pr1) (Zpart Znil pl1 pr1) (qzt_getr f3 (qzt_getr f2 ?sqt))")
              case lf: True
              then have r: "red_popl_fan3r pl1 pr1" "red_popl_fan2r pl1 pr1" using body3 Pcons8 nlf1 nlf2 by simp_all
              show False
              proof (rule br[OF lf, where y = "(f ^^ 5) w"])
                show "zdart (Zpart Zfan0l pl1 pr1) = qstepR G ((f ^^ 5) w)" using dfl(1) G1[OF m, of 2] by simp
                show "zdart (Zpart Zfan1r pl1 pr1) = qstepR G (n ((f ^^ 5) w))" by (rule dfr(2))
                show "arity G ((f ^^ 5) w) = nat_of_qarity (topqa ?s)" using m Pcons8 by (simp add: arity_funpow)
                show "arity G (n ((f ^^ 5) w)) = nat_of_qarity (topqa f2)" if "fitqa f2 (topqa f2)"
                  using fan2[OF that r(2)] nf[of 4] by simp
                show "arity G (e ((f ^^ 5) w)) = nat_of_qarity (topqa f3)" if "fitqa f3 (topqa f3)"
                  using fan3[OF that r(1)] .
              qed (use vp vp1 in simp_all)
            next
              case nlf3: False
              then have lf: "red_qzt_leaf (Zpart Zhatr pl1 pr1) (Zpart Zfan2r pl1 pr1) (Zpart Znil pl1 pr1)
                    (qzt_getr (get_hat pr1) (qzt_getr f3 ?sqt))" and r: "red_popr_hat pr1" "red_popl_fan3r pl1 pr1"
                using body3 Pcons8 nlf1 nlf2 by simp_all
              show False
              proof (rule br[OF lf, where y = "(f ^^ 6) w"])
                show "zdart (Zpart Zhatr pl1 pr1) = qstepR G ((f ^^ 6) w)" using dfl(4) G1[OF m, of 1] by simp
                show "zdart (Zpart Zfan2r pl1 pr1) = qstepR G (n ((f ^^ 6) w))" by (rule dfr(3))
                show "arity G ((f ^^ 6) w) = nat_of_qarity (topqa ?s)" using m Pcons8 by (simp add: arity_funpow)
                show "arity G (n ((f ^^ 6) w)) = nat_of_qarity (topqa f3)" if "fitqa f3 (topqa f3)"
                  using fan3[OF that r(2)] nf[of 5] by simp
                show "arity G (e ((f ^^ 6) w)) = nat_of_qarity (topqa (get_hat pr1))"
                  if "fitqa (get_hat pr1) (topqa (get_hat pr1))" using hat1[OF that r(1)] hatm[OF m] by simp
              qed (use vp vp1 in simp_all)
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma red_zpart_rec_false:
  "zvalid pl pr \<Longrightarrow> 0 < psize pl \<Longrightarrow> d < psize pr \<Longrightarrow> \<not> red_zpart_rec (Zpart Zhub pl pr) d"
proof (induction d arbitrary: pl pr)
  case 0 then show ?case by simp
next
  case (Suc d)
  have npr: "1 < psize pr" using Suc.prems(3) by simp
  have ns: "\<not> red_step (Zpart Zhub pl pr)" by (rule no_red_step[OF Suc.prems(1) npr])
  have sh: "zshiftr Zhub (Zpart Zhub pl pr) = Zpart Zhub (shift_part pr pl) (drop_part 1 pr)"
    by (rule shiftr_reg[OF npr])
  have v': "zvalid (shift_part pr pl) (drop_part 1 pr)"
    using zpvalid_shiftr[of "Zpart Zhub pl pr" Zhub] Suc.prems(1) sh by simp
  have "0 < psize (shift_part pr pl)" using npr by (cases pr) (simp_all add: shift_part_def)
  moreover have "d < psize (drop_part 1 pr)" using Suc.prems(3) by (simp add: psize_drop)
  ultimately have "\<not> red_zpart_rec (Zpart Zhub (shift_part pr pl) (drop_part 1 pr)) d"
    using Suc.IH[OF v'] by blast
  then show ?case using ns sh by simp
qed

lemma nhub_ge5: "5 \<le> nhub" by (cases ahub) simp_all

theorem not_red_zpart: "\<not> red_zpart"
proof -
  have "0 < psize p0ll" using p0l_size nhub_ge5 by (simp add: psize_drop)
  moreover have "nhub < psize p0lr"
    using p0_ne(1) Ep0r by (cases p0l) (simp_all add: shift_part_def psize_cat)
  ultimately show ?thesis unfolding red_zpart_def using red_zpart_rec_false[OF zvalid_initl] by blast
qed

end

theorem no_fit_redpart:
  assumes hyp: "hypermap G" and plainG: "plain G" and cubicG: "cubic G"
    and pentaG: "\<And>y. y \<in> darts G \<Longrightarrow> 5 \<le> arity G y"
    and nofit: "\<And>y. \<not> qzt_ctx.qzt_fit G y qt"
    and red: "redpart qt p" and xD: "x \<in> darts G"
  shows "\<not> exact_fitp G x p"
proof -
  define ahub where "ahub = qarity_of_nat (psize p)"
  have Ep: "psize p = nat_of_qarity ahub" and loop: "redpart_loop qt ahub (psize p * 12) p"
    using red by (simp_all add: redpart_def ahub_def Let_def)
  have main: "\<And>p x. x \<in> darts G \<Longrightarrow> psize p = nat_of_qarity ahub \<Longrightarrow> exact_fitp G x p \<Longrightarrow>
      \<not> redpart_loop qt ahub d p" for d
  proof (induction d)
    case 0 then show ?case by simp
  next
    case (Suc d)
    fix p x assume xD: "x \<in> darts G" and Ep: "psize p = nat_of_qarity ahub" and fx: "exact_fitp G x p"
    interpret R: rp_ctx qt ahub "redpart_loop qt ahub d" "rev_part p" p G x
    proof (unfold_locales)
      show "finite (darts G)" "edge G permutes darts G" "node G permutes darts G" "face G permutes darts G"
        "\<And>x. node G (face G (edge G x)) = x" using hyp by (simp_all add: hypermap_def)
    qed (use plainG cubicG pentaG nofit fx Ep xD Suc.IH in \<open>auto simp: exact_fitp_def\<close>)
    show "\<not> redpart_loop qt ahub (Suc d) p" using R.not_red_zpart by (simp add: rp.red_zpart_def)
  qed
  show ?thesis using main[OF xD Ep] loop by blast
qed

end
