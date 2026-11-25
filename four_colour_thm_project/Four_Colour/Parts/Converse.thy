(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Converse.thy
    Soundness of the converse of a part (fitp_converse of part.v).
    Ported from G. Gonthier's Coq development (part.v, section FitConversePart).
*)
theory Converse
  imports Four_Colour_Parts.Redpart3
begin

definition inv_face2 :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> 'a" where
  "inv_face2 G x = edge G (node G (edge G (node G x)))"

locale pcp = hypermap +
  assumes plainG: "plain G" and cubicG: "cubic G"
    and pentaG: "\<And>y. y \<in> D \<Longrightarrow> 5 \<le> arity G y"
begin

sublocale Q: qzt_ctx G x for x using plainG cubicG by unfold_locales

lemma ee [simp]: "e (e x) = x" by (rule Q.ee)
lemma nnn [simp]: "n (n (n x)) = x" by (rule Q.nnn)
lemma f_ne: "f x = n (n (e x))" by (rule Q.f_ne)
lemma nf [simp]: "n (f x) = e x" using f_ne[of x] by simp
lemma en_f [simp]: "e (n (f w)) = w" by (rule faceK)
lemma fe_nn: "f (e y) = n (n y)" using f_ne[of "e y"] by simp
lemma ar_en [simp]: "arity G (e (n x)) = arity G x" by (rule Q.ar_en)
lemma ar_nn [simp]: "arity G (n (n y)) = arity G (e y)" using fe_nn[of y] by (metis F.order_f)
lemma ar_ef: "arity G (e (f w)) = arity G (n (e w))"
  using ar_en[of "n (e w)"] f_ne[of w] by simp

lemma iter_arity: "(f ^^ arity G x) x = x" by (rule F.funpow_order)
lemma arity_funpow [simp]: "arity G ((f ^^ k) x) = arity G x" by (induction k) simp_all

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
  also have "\<dots> = (f ^^ (m - Suc k)) u" by simp
  finally show ?case .
qed

lemma penta_mem: "y \<in> D \<Longrightarrow> mem_range Pr59 (arity G y)" using pentaG by simp

lemmas mv = subpart_loc_move.simps eval_nat_numeral funpow.simps comp_def

text \<open>Claim B (conv_part5): the sector at the third spoke.\<close>

lemma conv5:
  assumes xD: "x \<in> D" and fit3: "fitp G ((f ^^ 2) x) p3"
    and h45: "mem_range h45 (arity G (e ((f ^^ 2) (e ((f ^^ 2) (e ((f ^^ 2) x)))))))"
  shows "mem_range (fst (conv_part5 h45 p3)) (arity G (e ((f ^^ 2) x))) \<and>
         fitp G ((f ^^ 2) (e ((f ^^ 2) x))) (snd (conv_part5 h45 p3))"
proof (cases p3)
  case (Pcons u s5 p)
  then show ?thesis using fit3 h45 by (simp add: mv)
next
  case (Pcons7 s5 s6 s7 p)
  then show ?thesis using fit3 h45 xD penta_mem by (simp add: mv pcons_s_def)
qed (use xD penta_mem in \<open>simp_all add: mv\<close>)

text \<open>Claim D (conv_part3): the converse hub sits on the second spoke.\<close>

lemma conv3:
  assumes xD: "x \<in> D" and a: "arity G x = 5 + psize p6" and fit6: "fitp G ((f ^^ 5) x) p6"
    and h23: "mem_range h23 (arity G (e ((f ^^ 4) x)))" and fq: "fitp G (f (e ((f ^^ 2) x))) q"
  shows "fitp G (e ((f ^^ 2) x)) (conv_part3 h23 p6 q)"
proof -
  have hat: "ar_at Phat G (e ((f ^^ 2) x)) = arity G (e ((f ^^ 4) x))"
    by (simp add: subpart_loc_move.simps funpow_add[symmetric, unfolded comp_def] eval_nat_numeral)
  have fan: "ar_at Pfan1 G (e ((f ^^ 2) x)) = arity G (e ((f ^^ 5) x))"
    "ar_at Pfan2 G (e ((f ^^ 2) x)) = arity G (e ((f ^^ 6) x))"
    "ar_at Pfan3 G (e ((f ^^ 2) x)) = arity G (e ((f ^^ 7) x))"
    by (simp_all add: subpart_loc_move.simps eval_nat_numeral)
  have sp: "ar_at Pspoke G (e ((f ^^ 2) x)) = arity G x" by (simp add: subpart_loc_move.simps)
  have f5: "fitp G ((f ^^ 5) x) p6" by (rule fit6)
  show ?thesis
  proof (cases "(h23, p6)" rule: conv_part3.cases)
    case (1 h) then show ?thesis using a sp hat h23 fq by simp
  next
    case (2 h a1 b1) then show ?thesis using a sp hat h23 fq by simp
  next
    case (3 h f31 b1 f32 b2)
    then show ?thesis using a sp hat h23 fq fit6 fan xD penta_mem
      by (auto simp: subpart_loc_move.simps eval_nat_numeral)
  next
    case (4 h f31 b1 f32 b2 f33 b3)
    then show ?thesis using a sp hat h23 fq fit6 fan
      by (auto simp: subpart_loc_move.simps eval_nat_numeral)
  qed simp_all
qed

section \<open>Local identities around the hub\<close>

abbreviation (input) g where "g \<equiv> e \<circ> n"

lemma nS: "n (e z) = f (e (f z))"
  using fe_nn[of "f z"] by simp

lemma ge [simp]: "f (e (n z)) = z" by (rule nodeK)

lemma eg: "e (g z) = n z" by simp

lemma g_f: "g (f z) = z" by simp

lemma ng: "n z = e (g z)" by simp

lemma ar_g [simp]: "arity G (g z) = arity G z" by simp

text \<open>Claim A darts: around the dart @{term "f S2"} of the second spoke face.\<close>

lemma A_spoke: "arity G (e (f (e ((f ^^ 2) x)))) = arity G (e (f x))"
  by (simp add: eval_nat_numeral fe_nn)

lemma A_hat: "ar_at Phat G (f (e ((f ^^ 2) x))) = arity G (e x)"
  by (simp add: subpart_loc_move.simps eval_nat_numeral fe_nn)

lemma A_fan1: "ar_at Pfan1 G (f (e ((f ^^ 2) x))) = ar_at Phat G (f x)"
  by (simp add: subpart_loc_move.simps eval_nat_numeral fe_nn)

lemma A_fan2: "ar_at Pfan2 G (f (e ((f ^^ 2) x))) = ar_at Pfan1 G (f x)"
  by (simp add: subpart_loc_move.simps eval_nat_numeral fe_nn)

lemma A_h45: "arity G (e ((f ^^ 2) (e (f (f (e ((f ^^ 2) x))))))) = arity G (e ((g ^^ 3) (e (f x))))"
  by (simp add: eval_nat_numeral fe_nn ar_ef)

lemma g3_rot: "arity G w = m \<Longrightarrow> 3 \<le> m \<Longrightarrow> arity G (e ((g ^^ 3) w)) = arity G (e ((f ^^ (m - 3)) w))"
  using enk[of w m 3] by simp

lemma conv4:
  assumes xD: "x \<in> D" and fit: "fitp G x p1"
  shows "mem_range (fst (conv_part4 p1)) (arity G (e ((f ^^ 2) (e (f (f (e ((f ^^ 2) x)))))))) \<and>
    (\<forall>q5. fitp G (f (f (e ((f ^^ 2) x)))) q5 \<longrightarrow> fitp G (f (e ((f ^^ 2) x))) (snd (conv_part4 p1) q5))"
proof -
  let ?S1 = "e (f x)"
  have dD: "e ((f ^^ 2) (e (f (f (e ((f ^^ 2) x)))))) \<in> D" using xD by simp
  have f2: "True" ..
  have gD: "((e \<circ> n) ^^ k) w \<in> D \<longleftrightarrow> w \<in> D" for k w by (induction k) simp_all
  have dD2: "5 \<le> arity G (e ((g ^^ 3) (e (f x))))"
    by (rule pentaG) (use xD gD in simp)
  have hspk: "ar_at Pspoke G (f (e ((f ^^ 2) x))) = arity G ?S1"
    using A_spoke by (simp add: subpart_loc_move.simps)
  note A = A_hat A_fan1 A_fan2 A_h45
  have hatf: "ar_at Phat G (f x) = arity G (e ((f ^^ 2) ?S1))" by (simp add: subpart_loc_move.simps)
  have fan1f: "ar_at Pfan1 G (f x) = arity G (e ((f ^^ 3) ?S1))" by (simp add: subpart_loc_move.simps)
  have fan2f: "ar_at Pfan2 G (f x) = arity G (e ((f ^^ 4) ?S1))" by (simp add: subpart_loc_move.simps)
  show ?thesis
  proof (cases p1 rule: conv_part4.cases)
    case (1 h34 hh s4 f41 r)
    have fs: "mem_range h34 (arity G (e x))" "mem_range s4 (arity G ?S1)" "mem_range f41 (ar_at Phat G (f x))"
      using fit 1 by (simp_all add: subpart_loc_move.simps)
    show ?thesis
    proof (cases "f41 = Pr59")
      case True then show ?thesis using 1 fs dD dD2 penta_mem hspk A f2 by auto
    next
      case n59: False
      show ?thesis
      proof (cases "s4 = Pr55")
        case True
        then have m: "arity G ?S1 = 5" using fs by simp
        show ?thesis using 1 n59 True fs hspk A f2 g3_rot[OF m] hatf by auto
      next
        case n5: False
        show ?thesis
        proof (cases "s4 = Pr66")
          case True
          then have m: "arity G ?S1 = 6" using fs by simp
          show ?thesis using 1 n59 n5 True fs hspk A f2 dD dD2 penta_mem by auto
        next
          case n6: False
          show ?thesis
          proof (cases "s4 = Pr77")
            case True
            then have m: "arity G ?S1 = 7" using fs by simp
            have "f (e ((f ^^ 2) x)) \<in> D" using xD by simp
            then have "mem_range Pr59 (ar_at Pfan2 G (f (e ((f ^^ 2) x))))" using penta_mem move_D by blast
            then show ?thesis using 1 n59 n5 n6 True fs hspk A f2 dD dD2 penta_mem by auto
          next
            case False
            then show ?thesis using 1 n59 n5 n6 dD dD2 penta_mem A by auto
          qed
        qed
      qed
    qed
  next
    case (2 h34 hh f41 h45 r)
    have fs: "mem_range h34 (arity G (e x))" "arity G ?S1 = 6" "mem_range f41 (ar_at Phat G (f x))"
      "mem_range h45 (ar_at Pfan1 G (f x))" using fit 2 by (simp_all add: subpart_loc_move.simps)
    show ?thesis using 2 fs hspk A f2 g3_rot[OF fs(2)] fan1f by auto
  next
    case (3 h34 hh f41 f42 h45 r)
    have fs: "mem_range h34 (arity G (e x))" "arity G ?S1 = 7" "mem_range f41 (ar_at Phat G (f x))"
      "mem_range f42 (ar_at Pfan1 G (f x))" "mem_range h45 (ar_at Pfan2 G (f x))"
      using fit 3 by (simp_all add: subpart_loc_move.simps)
    show ?thesis using 3 fs hspk A f2 g3_rot[OF fs(2)] fan2f by auto
  qed (use dD dD2 penta_mem A in simp_all)
qed

text \<open>Claim C darts: the two sectors before the second spoke dart, seen from the new hub.\<close>

lemma C_y1: "arity G (e (g (g (e ((f ^^ 2) x))))) = ar_at Phat G ((f ^^ 3) x)"
  by (simp add: subpart_loc_move.simps eval_nat_numeral fe_nn ar_ef)

lemma C_y2: "arity G (e (g (e ((f ^^ 2) x)))) = arity G (e ((f ^^ 3) x))"
  by (simp add: eval_nat_numeral fe_nn ar_ef)

lemma C_hat2: "ar_at Phat G (g (e ((f ^^ 2) x))) = ar_at Pfan1 G ((f ^^ 3) x)"
  by (simp add: subpart_loc_move.simps eval_nat_numeral fe_nn ar_ef)

lemma C_fan1: "ar_at Pfan1 G (g (e ((f ^^ 2) x))) = ar_at Pfan2 G ((f ^^ 3) x)"
  by (simp add: subpart_loc_move.simps eval_nat_numeral fe_nn ar_ef)

lemma C_fan2: "ar_at Pfan2 G (g (e ((f ^^ 2) x))) = arity G (e ((f ^^ 5) (e ((f ^^ 3) x))))"
  by (simp add: subpart_loc_move.simps eval_nat_numeral fe_nn ar_ef)

lemma C_H4: "arity G (e ((g ^^ 2) (e ((f ^^ 3) x)))) = ar_at Phat G ((f ^^ 4) x)"
  by (simp add: subpart_loc_move.simps eval_nat_numeral fe_nn ar_ef)

lemma H4_rot: "arity G (e ((f ^^ 3) x)) = m \<Longrightarrow> 2 \<le> m \<Longrightarrow>
    arity G (e ((f ^^ (m - 2)) (e ((f ^^ 3) x)))) = ar_at Phat G ((f ^^ 4) x)"
  using enk[of "e ((f ^^ 3) x)" m 2] C_H4[of x] by simp

lemma conv12:
  assumes xD: "x \<in> D" and fit4: "fitp G ((f ^^ 3) x) p4"
  shows "mem_range (fst (conv_part12 p4)) (arity G (e ((f ^^ 4) x))) \<and>
    (\<forall>q3. fitp G (e ((f ^^ 2) x)) q3 \<longrightarrow> fitp G (inv_face2 G (e ((f ^^ 2) x))) (snd (conv_part12 p4) q3))"
proof -
  let ?S2 = "e ((f ^^ 2) x)"
  have iv: "inv_face2 G ?S2 = g (g ?S2)" by (simp add: inv_face2_def)
  have fy1: "f (g (g ?S2)) = g ?S2" by simp
  have fy2: "f (g ?S2) = ?S2" by simp
  have sp1: "ar_at Pspoke G (g (g ?S2)) = ar_at Phat G ((f ^^ 3) x)"
    using C_y1[of x] by (simp add: subpart_loc_move.simps)
  have sp2: "ar_at Pspoke G (g ?S2) = arity G (e ((f ^^ 3) x))"
    using C_y2[of x] by (simp add: subpart_loc_move.simps)
  have D1: "g (g ?S2) \<in> D" "g ?S2 \<in> D" using xD by simp_all
  have pm: "\<And>i y. y \<in> D \<Longrightarrow> mem_range Pr59 (ar_at i G y)" using penta_mem move_D by blast
  have s3: "ar_at Pspoke G ((f ^^ 3) x) = arity G (e ((f ^^ 3) x))" by (simp add: subpart_loc_move.simps)
  have s4: "ar_at Pspoke G (f ((f ^^ 3) x)) = arity G (e ((f ^^ 4) x))"
    by (simp add: subpart_loc_move.simps eval_nat_numeral)
  have H4: "ar_at Phat G (f ((f ^^ 3) x)) = ar_at Phat G ((f ^^ 4) x)"
  proof -
    have "f ((f ^^ 3) x) = (f ^^ 4) x" by (simp add: eval_nat_numeral)
    then show ?thesis by (simp only:)
  qed
  note C = C_hat2[of x] C_fan1[of x] C_fan2[of x]
  have fan2m: "ar_at Pfan2 G (g ?S2) = ar_at Phat G ((f ^^ 4) x)" if m: "arity G (e ((f ^^ 3) x)) = 7"
    using C_fan2[of x] H4_rot[OF m] by simp
  have fan1m: "ar_at Pfan1 G (g ?S2) = ar_at Phat G ((f ^^ 4) x)" if m: "arity G (e ((f ^^ 3) x)) = 6"
  proof -
    have "ar_at Pfan1 G (g ?S2) = arity G (e ((f ^^ 4) (e ((f ^^ 3) x))))"
      using C_fan1[of x] by (simp add: subpart_loc_move.simps)
    then show ?thesis using H4_rot[OF m] by simp
  qed
  have hatm: "ar_at Phat G (g ?S2) = ar_at Phat G ((f ^^ 4) x)" if m: "arity G (e ((f ^^ 3) x)) = 5"
  proof -
    have "ar_at Phat G (g ?S2) = arity G (e ((f ^^ 3) (e ((f ^^ 3) x))))"
      using C_hat2[of x] by (simp add: subpart_loc_move.simps)
    then show ?thesis using H4_rot[OF m] by simp
  qed
  show ?thesis
  proof (cases p4 rule: conv_part12.cases)
    case (1 s2 s1 h23 f2 r)
    have fs: "mem_range s2 (arity G (e ((f ^^ 3) x)))" "mem_range s1 (ar_at Phat G ((f ^^ 3) x))"
      "mem_range h23 (arity G (e ((f ^^ 4) x)))" "mem_range f2 (ar_at Phat G ((f ^^ 4) x))"
      using fit4 1 s3 s4 H4 by simp_all
    show ?thesis
      using 1 fs iv fy1 fy2 sp1 sp2 D1 pm hatm fan1m fan2m xD pentaG[of "e ((f ^^ 4) x)"]
      by (auto simp: pcons_s_def)
  next
    case (2 s1 h12 h23 f21 r)
    have fs: "arity G (e ((f ^^ 3) x)) = 6" "mem_range s1 (ar_at Phat G ((f ^^ 3) x))"
      "mem_range h12 (ar_at Pfan1 G ((f ^^ 3) x))"
      "mem_range h23 (arity G (e ((f ^^ 4) x)))" "mem_range f21 (ar_at Phat G ((f ^^ 4) x))"
      using fit4 2 s3 s4 H4 by simp_all
    show ?thesis using 2 fs iv fy1 fy2 sp1 sp2 D1 pm C fan1m[OF fs(1)] by (auto simp: pcons_s_def)
  next
    case (3 s1 h12 f21 h23 f22 r)
    have fs: "arity G (e ((f ^^ 3) x)) = 7" "mem_range s1 (ar_at Phat G ((f ^^ 3) x))"
      "mem_range h12 (ar_at Pfan1 G ((f ^^ 3) x))" "mem_range f21 (ar_at Pfan2 G ((f ^^ 3) x))"
      "mem_range h23 (arity G (e ((f ^^ 4) x)))" "mem_range f22 (ar_at Phat G ((f ^^ 4) x))"
      using fit4 3 s3 s4 H4 by simp_all
    show ?thesis using 3 fs iv fy1 fy2 sp1 sp2 D1 pm C fan2m[OF fs(1)] by (auto simp: pcons_s_def)
  qed (use xD pm pentaG[of "e ((f ^^ 4) x)"] in \<open>auto intro: penta_mem\<close>)
qed

theorem fitp_converse:
  assumes xD: "x \<in> D" and fx: "exact_fitp G x p"
  shows "tight_fitp G (inv_face2 G (e (f (f x)))) (converse_part p)"
proof -
  let ?S2 = "e ((f ^^ 2) x)"
  have s2: "e (f (f x)) = ?S2" by (simp add: eval_nat_numeral)
  have fit: "fitp G x p" and ap: "arity G x = psize p" using fx by (simp_all add: exact_fitp_def)
  obtain h45 q4 where c4: "conv_part4 p = (h45, q4)" by fastforce
  obtain u q5 where c5: "conv_part5 h45 (drop_part 2 p) = (u, q5)" by fastforce
  obtain h23 q12 where c12: "conv_part12 (drop_part 3 p) = (h23, q12)" by fastforce
  have A: "mem_range h45 (arity G (e ((f ^^ 2) (e (f (f ?S2))))))"
    "\<And>q. fitp G (f (f ?S2)) q \<Longrightarrow> fitp G (f ?S2) (q4 q)" using conv4[OF xD fit] c4 by auto
  have h45': "mem_range h45 (arity G (e ((f ^^ 2) (e ((f ^^ 2) (e ((f ^^ 2) x)))))))"
    using A(1) by (simp add: eval_nat_numeral)
  note B0 = conv5[OF xD fitp_drop[OF fit, of 2] h45']
  have B: "mem_range u (arity G ?S2)" "fitp G ((f ^^ 2) ?S2) q5"
    using B0 unfolding c5 by simp_all
  have fq: "fitp G (f ?S2) (q4 q5)" using A(2) B(2) by (simp add: eval_nat_numeral)
  have C: "mem_range h23 (arity G (e ((f ^^ 4) x)))"
    "\<And>q. fitp G ?S2 q \<Longrightarrow> fitp G (inv_face2 G ?S2) (q12 q)"
    using conv12[OF xD fitp_drop[OF fit, of 3]] c12 by auto
  have a5: "arity G x = 5 + psize (drop_part 5 p)" using ap pentaG[OF xD] by (simp add: psize_drop)
  have D': "fitp G ?S2 (conv_part3 h23 (drop_part 5 p) (q4 q5))"
    by (rule conv3[OF xD a5 fitp_drop[OF fit, of 5] C(1) fq])
  have "arity G (inv_face2 G ?S2) = arity G ?S2" by (simp add: inv_face2_def)
  then show ?thesis using B(1) C(2)[OF D'] c4 c5 c12 s2
    by (simp add: tight_fitp_def converse_part_def)
qed

end

end
