(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Redpart.thy
    Reducibility of parts: a computational check that every neighbourhood fitting a part
    contains a reducible configuration (redpart.v).
    Ported from G. Gonthier's Coq development (redpart.v).
*)
theory Redpart
  imports Part
begin

section \<open>Zipper parts\<close>

datatype zpart_loc = Znil | Zhub | Zhubl | Zhubr | Zhat | Zhatl | Zhatr
  | Zfan0l | Zfan1l | Zfan2l | Zfan3l | Zfan0r | Zfan1r | Zfan2r | Zfan3r

datatype zpart = Zpart zpart_loc part part

fun zproper :: "zpart \<Rightarrow> bool" where
  "zproper (Zpart Znil _ _) = False" | "zproper _ = True"

definition shift_part :: "part \<Rightarrow> part \<Rightarrow> part" where
  "shift_part p1 p2 = cat_part (take_part 1 p1) p2"

fun zfanL :: "part \<Rightarrow> zpart_loc" where
  "zfanL (Pcons s _ _) = (if s = Pr55 then Zfan0l else Znil)"
| "zfanL (Pcons6 _ _ _) = Zfan1l" | "zfanL (Pcons7 _ _ _ _) = Zfan2l"
| "zfanL (Pcons8 _ _ _ _ _) = Zfan3l" | "zfanL Pnil = Znil"

fun zfanR :: "part \<Rightarrow> zpart_loc" where
  "zfanR (Pcons s _ _) = (if s = Pr55 then Zfan0r else Znil)"
| "zfanR (Pcons6 _ _ _) = Zfan1r" | "zfanR (Pcons7 _ _ _ _) = Zfan2r"
| "zfanR (Pcons8 _ _ _ _ _) = Zfan3r" | "zfanR Pnil = Znil"

fun zfanLt :: "part \<Rightarrow> zpart_loc" where
  "zfanLt (Pcons s _ _) = (if s = Pr55 then Zfan0l else if s = Pr56 \<or> s = Pr66 then Zfan1l else Znil)"
| "zfanLt (Pcons6 _ _ _) = Zfan1l" | "zfanLt (Pcons7 _ _ _ _) = Zfan2l"
| "zfanLt (Pcons8 _ _ _ _ _) = Zfan3l" | "zfanLt Pnil = Znil"

fun zfanRt :: "part \<Rightarrow> zpart_loc" where
  "zfanRt (Pcons s _ _) = (if s = Pr55 then Zfan0r else if s = Pr56 \<or> s = Pr66 then Zfan1r else Znil)"
| "zfanRt (Pcons6 _ _ _) = Zfan1r" | "zfanRt (Pcons7 _ _ _ _) = Zfan2r"
| "zfanRt (Pcons8 _ _ _ _ _) = Zfan3r" | "zfanRt Pnil = Znil"

fun topqa :: "prange \<Rightarrow> qarity" where
  "topqa Pr55 = Qa5" | "topqa Pr56 = Qa6" | "topqa Pr66 = Qa6"
| "topqa Pr57 = Qa7" | "topqa Pr67 = Qa7" | "topqa Pr77 = Qa7"
| "topqa Pr58 = Qa8" | "topqa Pr68 = Qa8" | "topqa Pr78 = Qa8" | "topqa Pr88 = Qa8"
| "topqa _ = Qa9"

definition fitqa :: "prange \<Rightarrow> qarity \<Rightarrow> bool" where
  "fitqa r qa \<longleftrightarrow> nat_of_qarity qa \<le> 8 \<and> qa = topqa r"

fun popqa :: "prange \<Rightarrow> prange" where
  "popqa Pr56 = Pr55" | "popqa Pr57 = Pr56" | "popqa Pr58 = Pr57" | "popqa Pr67 = Pr66"
| "popqa Pr68 = Pr67" | "popqa Pr78 = Pr77" | "popqa _ = Pr99"

lemma fitqa_popqa:
  "fitqa r qa \<Longrightarrow> mem_range r n \<Longrightarrow> (mem_range (popqa r) 9 \<or> \<not> mem_range (popqa r) n) \<Longrightarrow>
   n = nat_of_qarity qa"
  by (cases r) (auto simp: fitqa_def mem_range_def)

fun qzt_getr :: "prange \<Rightarrow> quiz_tree \<Rightarrow> quiz_tree" where
  "qzt_getr r (QztNode qt5 qt6 qt7 qt8) =
     (if r = Pr55 then qt5 else if r = Pr56 \<or> r = Pr66 then qt6
      else if r = Pr57 \<or> r = Pr67 \<or> r = Pr77 then qt7
      else if r = Pr58 \<or> r = Pr68 \<or> r = Pr78 \<or> r = Pr88 then qt8 else QztNil)"
| "qzt_getr r _ = QztNil"

lemma qzt_getr_fit:
  "qzt_proper (qzt_getr r qt1) \<Longrightarrow>
   fitqa r (topqa r) \<and> qzt_get1 (topqa r) qt1 = qzt_getr r qt1 \<and> qzt_proper qt1"
  by (cases qt1) (cases r; auto simp: fitqa_def)+

section \<open>The search, parametrised by its environment\<close>

locale rp =
  fixes qt :: quiz_tree and ahub :: qarity and red_rec :: "part \<Rightarrow> bool"
    and p0l p0r :: part
begin

abbreviation "nhub \<equiv> nat_of_qarity ahub"
abbreviation "p0ll \<equiv> drop_part 1 p0l"
abbreviation "p0lr \<equiv> shift_part p0l p0r"
abbreviation "p0rr \<equiv> drop_part 1 p0r"
abbreviation "p0rl \<equiv> shift_part p0r p0l"

fun zshiftl :: "zpart_loc \<Rightarrow> zpart \<Rightarrow> zpart" where
  "zshiftl zi (Zpart _ (Pcons s h pl) pr) =
     (if pl = Pnil then Zpart zi p0l p0r else Zpart zi pl (Pcons s h pr))"
| "zshiftl zi (Zpart _ (Pcons6 h f1 pl) pr) =
     (if pl = Pnil then Zpart zi p0l p0r else Zpart zi pl (Pcons6 h f1 pr))"
| "zshiftl zi (Zpart _ (Pcons7 h f1 f2 pl) pr) =
     (if pl = Pnil then Zpart zi p0l p0r else Zpart zi pl (Pcons7 h f1 f2 pr))"
| "zshiftl zi (Zpart _ (Pcons8 h f1 f2 f3 pl) pr) =
     (if pl = Pnil then Zpart zi p0l p0r else Zpart zi pl (Pcons8 h f1 f2 f3 pr))"
| "zshiftl zi (Zpart _ Pnil _) = Zpart zi p0ll p0lr"

fun zshiftr :: "zpart_loc \<Rightarrow> zpart \<Rightarrow> zpart" where
  "zshiftr zi (Zpart _ pl (Pcons s h pr)) =
     (if pr = Pnil then Zpart zi p0l p0r else Zpart zi (Pcons s h pl) pr)"
| "zshiftr zi (Zpart _ pl (Pcons6 h f1 pr)) =
     (if pr = Pnil then Zpart zi p0l p0r else Zpart zi (Pcons6 h f1 pl) pr)"
| "zshiftr zi (Zpart _ pl (Pcons7 h f1 f2 pr)) =
     (if pr = Pnil then Zpart zi p0l p0r else Zpart zi (Pcons7 h f1 f2 pl) pr)"
| "zshiftr zi (Zpart _ pl (Pcons8 h f1 f2 f3 pr)) =
     (if pr = Pnil then Zpart zi p0l p0r else Zpart zi (Pcons8 h f1 f2 f3 pl) pr)"
| "zshiftr zi (Zpart _ _ Pnil) = Zpart zi p0rl p0rr"

fun zstepL :: "zpart \<Rightarrow> zpart" where
  "zstepL (Zpart Zhub pl pr) = zshiftl Zhubl (Zpart Zhub pl pr)"
| "zstepL (Zpart Zhubl pl pr) = Zpart Zhat pl pr"
| "zstepL (Zpart Zhubr pl pr) = zshiftr Zhubr (Zpart Zhubr pl pr)"
| "zstepL (Zpart Zhat pl pr) = zshiftr (zfanL pr) (Zpart Zhat pl pr)"
| "zstepL (Zpart Zhatl pl pr) = Zpart (zfanR pl) pl pr"
| "zstepL (Zpart Zhatr pl pr) = Zpart Zhub pl pr"
| "zstepL (Zpart Zfan0l pl pr) = Zpart Zhatr pl pr"
| "zstepL (Zpart Zfan1l pl pr) = Zpart Zfan0l pl pr"
| "zstepL (Zpart Zfan2l pl pr) = Zpart Zfan1l pl pr"
| "zstepL (Zpart Zfan3l pl pr) = Zpart Zfan2l pl pr"
| "zstepL (Zpart _ pl pr) = Zpart Znil pl pr"

fun zstepR :: "zpart \<Rightarrow> zpart" where
  "zstepR (Zpart Zhub pl pr) = zshiftr Zhubr (Zpart Zhub pl pr)"
| "zstepR (Zpart Zhubl pl pr) = zshiftl Zhubl (Zpart Zhubl pl pr)"
| "zstepR (Zpart Zhubr pl pr) = Zpart Zhat pl pr"
| "zstepR (Zpart Zhat pl pr) = Zpart (zfanR pl) pl pr"
| "zstepR (Zpart Zhatl pl pr) = Zpart Zhub pl pr"
| "zstepR (Zpart Zhatr pl pr) = zshiftr (zfanL pr) (Zpart Zhatr pl pr)"
| "zstepR (Zpart Zfan0r pl pr) = zshiftl Zhatl (Zpart Zfan0r pl pr)"
| "zstepR (Zpart Zfan1r pl pr) = Zpart Zfan0r pl pr"
| "zstepR (Zpart Zfan2r pl pr) = Zpart Zfan1r pl pr"
| "zstepR (Zpart Zfan3r pl pr) = Zpart Zfan2r pl pr"
| "zstepR (Zpart _ pl pr) = Zpart Znil pl pr"

fun zstepLt :: "zpart \<Rightarrow> zpart" where
  "zstepLt (Zpart Zhatl pl pr) = Zpart (zfanRt pl) pl pr"
| "zstepLt zp = zstepL zp"

fun zstepRt :: "zpart \<Rightarrow> zpart" where
  "zstepRt (Zpart Zhatr pl pr) = zshiftr (zfanLt pr) (Zpart Zhatr pl pr)"
| "zstepRt zp = zstepR zp"

definition hub_range :: prange where
  "hub_range = (case ahub of Qa5 \<Rightarrow> Pr55 | Qa6 \<Rightarrow> Pr66 | Qa7 \<Rightarrow> Pr77 | Qa8 \<Rightarrow> Pr88 | _ \<Rightarrow> Pr99)"

fun zrange :: "zpart \<Rightarrow> prange" where
  "zrange (Zpart Znil _ _) = Pr59"
| "zrange (Zpart Zhub _ _) = hub_range"
| "zrange (Zpart Zhubl pl _) = get_spoke pl"
| "zrange (Zpart Zhubr _ pr) = get_spoke pr"
| "zrange (Zpart Zhatl pl _) = get_spoke pl"
| "zrange (Zpart Zhat _ pr) = get_hat pr"
| "zrange (Zpart Zhatr _ pr) = get_spoke pr"
| "zrange (Zpart Zfan0l _ pr) = get_hat pr"
| "zrange (Zpart Zfan1l pl _) = get_fan1l pl"
| "zrange (Zpart Zfan2l pl _) = get_fan2l pl"
| "zrange (Zpart Zfan3l pl _) = get_fan3l pl"
| "zrange (Zpart Zfan0r pl _) = get_hat pl"
| "zrange (Zpart Zfan1r pl _) = get_fan1r pl"
| "zrange (Zpart Zfan2r pl _) = get_fan2r pl"
| "zrange (Zpart Zfan3r pl _) = get_fan3r pl"

definition red_pcons :: "(prange \<Rightarrow> part \<Rightarrow> part) \<Rightarrow> prange \<Rightarrow> part \<Rightarrow> bool" where
  "red_pcons pc r pr =
    (if r \<in> {Pr56, Pr57, Pr58, Pr67, Pr68, Pr78}
     then red_rec (take_part nhub (cat_part (pc (popqa r) pr) p0r)) else True)"

fun red_popr_spoke :: "part \<Rightarrow> bool" where
  "red_popr_spoke (Pcons s h p) = red_pcons (\<lambda>r. Pcons r h) s p"
| "red_popr_spoke _ = True"

fun red_popr_hat :: "part \<Rightarrow> bool" where
  "red_popr_hat (Pcons s h p) = red_pcons (Pcons s) h p"
| "red_popr_hat (Pcons6 h f1 p) = red_pcons (\<lambda>r. Pcons6 r f1) h p"
| "red_popr_hat (Pcons7 h f1 f2 p) = red_pcons (\<lambda>r. Pcons7 r f1 f2) h p"
| "red_popr_hat (Pcons8 h f1 f2 f3 p) = red_pcons (\<lambda>r. Pcons8 r f1 f2 f3) h p"
| "red_popr_hat Pnil = True"

fun red_popl_spoke :: "part \<Rightarrow> part \<Rightarrow> bool" where
  "red_popl_spoke (Pcons s h _) pr = red_pcons (\<lambda>r. Pcons r h) s pr"
| "red_popl_spoke _ _ = True"

fun red_popl_hat :: "part \<Rightarrow> part \<Rightarrow> bool" where
  "red_popl_hat (Pcons s h _) pr = red_pcons (Pcons s) h pr"
| "red_popl_hat (Pcons6 h f1 _) pr = red_pcons (\<lambda>r. Pcons6 r f1) h pr"
| "red_popl_hat (Pcons7 h f1 f2 _) pr = red_pcons (\<lambda>r. Pcons7 r f1 f2) h pr"
| "red_popl_hat (Pcons8 h f1 f2 f3 _) pr = red_pcons (\<lambda>r. Pcons8 r f1 f2 f3) h pr"
| "red_popl_hat Pnil _ = True"

fun red_popl_fan1l :: "part \<Rightarrow> part \<Rightarrow> bool" where
  "red_popl_fan1l (Pcons6 h f1 _) pr = red_pcons (\<lambda>r. Pcons6 h r) f1 pr"
| "red_popl_fan1l (Pcons7 h f1 f2 _) pr = red_pcons (\<lambda>r. Pcons7 h f1 r) f2 pr"
| "red_popl_fan1l (Pcons8 h f1 f2 f3 _) pr = red_pcons (\<lambda>r. Pcons8 h f1 f2 r) f3 pr"
| "red_popl_fan1l _ _ = True"

fun red_popl_fan2l :: "part \<Rightarrow> part \<Rightarrow> bool" where
  "red_popl_fan2l (Pcons7 h f1 f2 _) pr = red_pcons (\<lambda>r. Pcons7 h r f2) f1 pr"
| "red_popl_fan2l (Pcons8 h f1 f2 f3 _) pr = red_pcons (\<lambda>r. Pcons8 h f1 r f3) f2 pr"
| "red_popl_fan2l _ _ = True"

fun red_popl_fan3l :: "part \<Rightarrow> part \<Rightarrow> bool" where
  "red_popl_fan3l (Pcons8 h f1 f2 f3 _) pr = red_pcons (\<lambda>r. Pcons8 h r f2 f3) f1 pr"
| "red_popl_fan3l _ _ = True"

fun red_popl_fan1r :: "part \<Rightarrow> part \<Rightarrow> bool" where
  "red_popl_fan1r (Pcons6 h f1 _) pr = red_pcons (\<lambda>r. Pcons6 h r) f1 pr"
| "red_popl_fan1r (Pcons7 h f1 f2 _) pr = red_pcons (\<lambda>r. Pcons7 h r f2) f1 pr"
| "red_popl_fan1r (Pcons8 h f1 f2 f3 _) pr = red_pcons (\<lambda>r. Pcons8 h r f2 f3) f1 pr"
| "red_popl_fan1r _ _ = True"

fun red_popl_fan2r :: "part \<Rightarrow> part \<Rightarrow> bool" where
  "red_popl_fan2r (Pcons7 h f1 f2 _) pr = red_pcons (\<lambda>r. Pcons7 h f1 r) f2 pr"
| "red_popl_fan2r (Pcons8 h f1 f2 f3 _) pr = red_pcons (\<lambda>r. Pcons8 h f1 r f3) f2 pr"
| "red_popl_fan2r _ _ = True"

fun red_popl_fan3r :: "part \<Rightarrow> part \<Rightarrow> bool" where
  "red_popl_fan3r (Pcons8 h f1 f2 f3 _) pr = red_pcons (\<lambda>r. Pcons8 h f1 f2 r) f3 pr"
| "red_popl_fan3r _ _ = True"

fun red_pop :: "zpart \<Rightarrow> bool" where
  "red_pop (Zpart Zhubl pl pr) = red_popl_spoke pl pr"
| "red_pop (Zpart Zhubr pl pr) = red_popr_spoke pr"
| "red_pop (Zpart Zhatl pl pr) = red_popl_spoke pl pr"
| "red_pop (Zpart Zhat pl pr) = red_popr_hat pr"
| "red_pop (Zpart Zhatr pl pr) = red_popr_spoke pr"
| "red_pop (Zpart Zfan0l pl pr) = red_popr_hat pr"
| "red_pop (Zpart Zfan1l pl pr) = red_popl_fan1l pl pr"
| "red_pop (Zpart Zfan2l pl pr) = red_popl_fan2l pl pr"
| "red_pop (Zpart Zfan3l pl pr) = red_popl_fan3l pl pr"
| "red_pop (Zpart Zfan0r pl pr) = red_popl_hat pl pr"
| "red_pop (Zpart Zfan1r pl pr) = red_popl_fan1r pl pr"
| "red_pop (Zpart Zfan2r pl pr) = red_popl_fan2r pl pr"
| "red_pop (Zpart Zfan3r pl pr) = red_popl_fan3r pl pr"
| "red_pop _ = True"

fun fitqzp :: "zpart \<Rightarrow> question \<Rightarrow> bool" where
  "fitqzp zp Qask0 = True"
| "fitqzp zp (Qask1 qa) = fitqa (zrange zp) qa"
| "fitqzp zp (QaskL qa ql) = (fitqa (zrange zp) qa \<and> fitqzp (zstepLt zp) ql)"
| "fitqzp zp (QaskR qa qr) = (fitqa (zrange zp) qa \<and> fitqzp (zstepRt zp) qr)"
| "fitqzp zp (QaskLR qa ql qr) =
     (fitqa (zrange zp) qa \<and> fitqzp (zstepL zp) ql \<and> fitqzp (zstepR zp) qr)"
| "fitqzp zp (QaskLL qa ql) = (fitqa (zrange (zstepL zp)) qa \<and> fitqzp (zstepL (zstepL zp)) ql)"
| "fitqzp zp (QaskRR qa qr) = (fitqa (zrange (zstepR zp)) qa \<and> fitqzp (zstepR (zstepR zp)) qr)"

fun red_popqzp :: "zpart \<Rightarrow> question \<Rightarrow> bool" where
  "red_popqzp zp Qask0 = True"
| "red_popqzp zp (Qask1 _) = red_pop zp"
| "red_popqzp zp (QaskL qa ql) = (red_pop zp \<and> red_popqzp (zstepLt zp) ql)"
| "red_popqzp zp (QaskR qa qr) = (red_pop zp \<and> red_popqzp (zstepRt zp) qr)"
| "red_popqzp zp (QaskLR qa ql qr) =
     (red_pop zp \<and> red_popqzp (zstepL zp) ql \<and> red_popqzp (zstepR zp) qr)"
| "red_popqzp zp (QaskLL qa ql) = (red_pop (zstepL zp) \<and> red_popqzp (zstepL (zstepL zp)) ql)"
| "red_popqzp zp (QaskRR qa qr) = (red_pop (zstepR zp) \<and> red_popqzp (zstepR (zstepR zp)) qr)"

fun red_qzt_leaf :: "zpart \<Rightarrow> zpart \<Rightarrow> zpart \<Rightarrow> quiz_tree \<Rightarrow> bool" where
  "red_qzt_leaf zp1 zp2 zp3 (QztLeaf q1 q2 q3 qtl') =
     (if fitqzp zp3 q3 \<and> fitqzp zp2 q2 \<and> fitqzp zp1 q1
      then red_popqzp zp1 q1 \<and> red_popqzp zp2 q2 \<and> red_popqzp zp3 q3
      else red_qzt_leaf zp1 zp2 zp3 qtl')"
| "red_qzt_leaf zp1 zp2 zp3 _ = False"

definition red_step :: "zpart \<Rightarrow> bool" where
  "red_step zp = (case zp of Zpart _ pl pr \<Rightarrow>
    (case zshiftr Zhub zp of Zpart _ pl' pr' \<Rightarrow>
     let s = get_spoke pr; sqt = qzt_getr s (qzt_truncate qt); sl = get_spoke pl;
         zpnil = Zpart Znil pl' pr' in
     qzt_proper sqt \<and>
     (if red_qzt_leaf (Zpart Zhubr pl' pr') (zshiftl Zhubl zp) (Zpart Zhat pl pr)
           (qzt_getr s (qzt_getr sl (qzt_get1 ahub qt)))
      then red_popr_spoke pr \<and> red_popl_spoke pl pr
      else if red_qzt_leaf (Zpart (zfanLt pr) pl' pr') zp (Zpart (zfanRt pl) pl pr)
           (qzt_getr (get_hat pr) (qzt_getr sl sqt))
      then red_popr_hat pr \<and> red_popl_spoke pl pr \<and> red_popr_spoke pr
      else (case pr of
        Pcons s0 h _ \<Rightarrow>
          s0 = Pr55 \<and> red_qzt_leaf (Zpart Zhatr pl' pr') (Zpart Zhatl pl pr) zpnil
                        (qzt_getr (get_hat pr') (qzt_getr h sqt)) \<and>
          red_popr_hat pr' \<and> red_popr_hat pr
      | Pcons6 h f1 _ \<Rightarrow>
          (if red_qzt_leaf (Zpart Zfan0l pl' pr') (Zpart Zhatl pl pr) zpnil (qzt_getr f1 (qzt_getr h sqt))
           then red_popl_fan1r pl' pr' \<and> red_popr_hat pr
           else red_qzt_leaf (Zpart Zhatr pl' pr') (Zpart Zfan0r pl' pr') zpnil
                  (qzt_getr (get_hat pr') (qzt_getr f1 sqt)) \<and>
                red_popr_hat pr' \<and> red_popl_fan1r pl' pr')
      | Pcons7 h f1 f2 _ \<Rightarrow>
          (if red_qzt_leaf (Zpart Zfan1l pl' pr') (Zpart Zhatl pl pr) zpnil (qzt_getr f1 (qzt_getr h sqt))
           then red_popl_fan1r pl' pr' \<and> red_popr_hat pr
           else if red_qzt_leaf (Zpart Zfan0l pl' pr') (Zpart Zfan0r pl' pr') zpnil
                  (qzt_getr f2 (qzt_getr f1 sqt))
           then red_popl_fan2r pl' pr' \<and> red_popl_fan1r pl' pr'
           else red_qzt_leaf (Zpart Zhatr pl' pr') (Zpart Zfan1r pl' pr') zpnil
                  (qzt_getr (get_hat pr') (qzt_getr f2 sqt)) \<and>
                red_popr_hat pr' \<and> red_popl_fan2r pl' pr')
      | Pcons8 h f1 f2 f3 _ \<Rightarrow>
          (if red_qzt_leaf (Zpart Zfan2l pl' pr') (Zpart Zhatl pl pr) zpnil (qzt_getr f1 (qzt_getr h sqt))
           then red_popl_fan1r pl' pr' \<and> red_popr_hat pr
           else if red_qzt_leaf (Zpart Zfan1l pl' pr') (Zpart Zfan0r pl' pr') zpnil
                  (qzt_getr f2 (qzt_getr f1 sqt))
           then red_popl_fan2r pl' pr' \<and> red_popl_fan1r pl' pr'
           else if red_qzt_leaf (Zpart Zfan0l pl' pr') (Zpart Zfan1r pl' pr') zpnil
                  (qzt_getr f3 (qzt_getr f2 sqt))
           then red_popl_fan3r pl' pr' \<and> red_popl_fan2r pl' pr'
           else red_qzt_leaf (Zpart Zhatr pl' pr') (Zpart Zfan2r pl' pr') zpnil
                  (qzt_getr (get_hat pr') (qzt_getr f3 sqt)) \<and>
                red_popr_hat pr' \<and> red_popl_fan3r pl' pr')
      | Pnil \<Rightarrow> False))))"

fun red_zpart_rec :: "zpart \<Rightarrow> nat \<Rightarrow> bool" where
  "red_zpart_rec zp 0 = False"
| "red_zpart_rec zp (Suc d) = (red_step zp \<or> red_zpart_rec (zshiftr Zhub zp) d)"

definition red_zpart :: bool where
  "red_zpart = red_zpart_rec (Zpart Zhub p0ll p0lr) nhub"

end

fun redpart_loop :: "quiz_tree \<Rightarrow> qarity \<Rightarrow> nat \<Rightarrow> part \<Rightarrow> bool" where
  "redpart_loop qt ahub 0 p = False"
| "redpart_loop qt ahub (Suc d) p = rp.red_zpart qt ahub (redpart_loop qt ahub d) (rev_part p) p"

definition redpart :: "quiz_tree \<Rightarrow> part \<Rightarrow> bool" where
  "redpart qt p = (let ahub = qarity_of_nat (psize p) in
     psize p = nat_of_qarity ahub \<and> redpart_loop qt ahub (psize p * 12) p)"

end
