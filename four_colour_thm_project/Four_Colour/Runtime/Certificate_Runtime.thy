(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
theory Certificate_Runtime
  imports Four_Colour_Checkers.Check_Map "HOL-Library.Code_Target_Numeral"
begin

text \<open>Reuse Isabelle-generated checker code between certificate proofs.
  The equations and eval soundness boundary are unchanged.\<close>

lemma gtree_merge_line_code [code]:
  "gtree_merge_line p0 p1 p2 ls d =
    (if d = 0 then [gtree_merge_pairs p0 p1 p2]
     else case ls of
       [] \<Rightarrow> [gtree_merge_pairs p0 p1 p2,
          gtree_merge_pairs empty_gtree_pair p0 p1,
          gtree_merge_pairs empty_gtree_pair empty_gtree_pair p0]
     | p # ps \<Rightarrow> gtree_merge_pairs p0 p1 p2 # gtree_merge_line p p0 p1 ps (d - 1))"
  by (cases d; cases ls) simp_all

lemma gen_dyck_code [code]:
  "gen_dyck m n = (if n = 0 then (if m = 1 then 1 else 0)
     else if m = 0 then 0 else gen_dyck (m + 1) (n - 1) + gen_dyck (m - 1) (n - 1))"
  by (cases m; cases n) simp_all

lemma ctree_decr_code [code]:
  "ctree_decr t n = (if n = 0 then t else
    case t of CtreeLeaf u \<Rightarrow> ctree_decr u (n - 1) | _ \<Rightarrow> t)"
  by (cases n; cases t) simp_all

lemma check_dbound1_rec_code [code]:
  "check_dbound1_rec redp p rs ns m = (if m = 0 then False else
    case rs of [] \<Rightarrow> True | r # rs' \<Rightarrow>
      if length rs' < ns then True else
      (let p' = meet_part p r in
       (case sort_drules p' rs' of (dns, rs'') \<Rightarrow>
         if ns - dns = 0 then redp p'
         else check_dbound1_rec redp p' rs'' (ns - dns - 1) (m - 1)) \<and>
       check_dbound1_rec redp p rs' ns (m - 1)))"
  by (cases m; cases rs) (simp_all add: Let_def)

lemma check_dbound2_rec_code [code]:
  "check_dbound2_rec redp p rt rs ru nt m = (if m = 0 then False else
    case rt of [] \<Rightarrow> True | r # rt' \<Rightarrow>
      if length rt' < nt then True else
      (let p' = meet_part p r in
       (check_unfit p' ru \<or>
         (case sort_drules p' rt' of (dnt, rt'') \<Rightarrow>
          case sort_drules p' rs of (dns, rs') \<Rightarrow>
          if dns + nt - dnt = 0 then redp p'
          else check_dbound2_rec redp p' rt'' rs' ru (dns + nt - dnt - 1) (m - 1))) \<and>
       check_dbound2_rec redp p rt' rs (r # ru) nt (m - 1)))"
  by (cases m; cases rt) (simp_all add: Let_def)

lemma check_2dbound2_rec_code [code]:
  "check_2dbound2_rec nhub redp p1 p2 rt1 rs1 ru1 rt2 rs2 ru2 i nt m =
    (if m = 0 then False else case rt1 of
       [] \<Rightarrow> (rt2 = [] \<or> check_2dbound2_rec nhub redp p2 p1 rt2 rs2 ru2 [] rs1 ru1 (nhub - i) nt (m - 1))
     | r # rt1' \<Rightarrow> if length rt1' + length rt2 < nt then True else
       (let p1' = meet_part p1 r; p2' = rot_part i p1' in
        (check_unfit p1' ru1 \<or> check_unfit p2' ru2 \<or>
          (case sort_drules p1' rt1' of (dnt1, rt1'') \<Rightarrow>
           case sort_drules p1' rs1 of (dns1, rs1') \<Rightarrow>
           case sort_drules p2' rt2 of (dnt2, rt2') \<Rightarrow>
           case sort_drules p2' rs2 of (dns2, rs2') \<Rightarrow>
           if dns1 + (dns2 + nt) - (dnt1 + dnt2) = 0 then redp p1'
           else check_2dbound2_rec nhub redp p1' p2' rt1'' rs1' ru1 rt2' rs2' ru2 i
             (dns1 + (dns2 + nt) - (dnt1 + dnt2) - 1) (m - 1))) \<and>
        check_2dbound2_rec nhub redp p1 p2 rt1' rs1 (r # ru1) rt2 rs2 ru2 i nt (m - 1)))"
  by (cases m; cases rt1) (simp_all add: Let_def)

lemma ctree_restrict_code [code]:
  "ctree_restrict h t r =
    (case r of CtrNil \<Rightarrow> CtreePair t CtreeEmpty
     | CtrCons bs g rr \<Rightarrow>
       (case t of CtreeNode t1 t2 t3 \<Rightarrow>
         (if h = 0 then
            (case ctr_decr t1 t2 t3 r of (a,b,c) \<Rightarrow> ctree_leaf_pair t1 t2 t3 a b c)
          else (case ctr_split CtrNil CtrNil CtrNil r of (r1,r2,r3) \<Rightarrow>
            ctree_cons_pairs (ctree_restrict (h - 1) t1 r1)
              (ctree_restrict (h - 1) t2 r2) (ctree_restrict (h - 1) t3 r3)))
        | _ \<Rightarrow> ctree_empty_pair))"
  by (cases r; cases t; cases h) simp_all

lemma drop_part_code [code]:
  "drop_part m p = (if m = 0 then p else case p of
      Pnil \<Rightarrow> Pnil
    | Pcons s h q \<Rightarrow> drop_part (m - 1) q
    | Pcons6 h a q \<Rightarrow> drop_part (m - 1) q
    | Pcons7 h a b q \<Rightarrow> drop_part (m - 1) q
    | Pcons8 h a b c q \<Rightarrow> drop_part (m - 1) q)"
  by (cases m; cases p) simp_all

lemma take_part_code [code]:
  "take_part m p = (if m = 0 then Pnil else case p of
      Pnil \<Rightarrow> Pnil
    | Pcons s h q \<Rightarrow> Pcons s h (take_part (m - 1) q)
    | Pcons6 h a q \<Rightarrow> Pcons6 h a (take_part (m - 1) q)
    | Pcons7 h a b q \<Rightarrow> Pcons7 h a b (take_part (m - 1) q)
    | Pcons8 h a b c q \<Rightarrow> Pcons8 h a b c (take_part (m - 1) q))"
  by (cases m; cases p) simp_all

code_reflect Four_Colour_Certificate_Runtime
  datatypes config = _ and cpstep = _ and nat and int = _ and num = _
    and quiz_tree = _ and question = _ and qarity = _
    and pscript = _ and subpart_loc = _ and hubcap = _
    and part = _ and prange = _
  functions check_cfquiz check_reducible check_ps check_dbound1
    nat_of_integer nat_of_num integer_of_nat Suc
    Nat.zero_nat_inst.zero_nat Nat.one_nat_inst.one_nat
    "(+) :: nat \<Rightarrow> nat \<Rightarrow> nat"
    "(-) :: nat \<Rightarrow> nat \<Rightarrow> nat"
    "(*) :: nat \<Rightarrow> nat \<Rightarrow> nat"
    "(div) :: nat \<Rightarrow> nat \<Rightarrow> nat"
    "(mod) :: nat \<Rightarrow> nat \<Rightarrow> nat"

end
