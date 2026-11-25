(* Dyadic approximation from approx.v. G. Gonthier et al., CeCILL-B.
   Isabelle/HOL port: Codex. HOL floor replaces the reference range search. *)
theory Approx
  imports Four_Colour_Plane_Maps.Grid_Rectangles
begin

definition exp2R :: "nat \<Rightarrow> real" where "exp2R s = 2^s"

lemma exp2RS [simp]: "exp2R (Suc s) = 2 * exp2R s"
  by (simp add: exp2R_def)
lemma ltR0exp2 [simp]: "0 < exp2R s" by (simp add: exp2R_def)
lemma exp2R_nonzero [simp]: "exp2R s \<noteq> 0" using ltR0exp2[of s] by linarith
lemma leR1exp2: "1 \<le> exp2R s" by (simp add: exp2R_def one_le_power)
lemma exp2R_add: "exp2R (s+t) = exp2R s * exp2R t"
  by (simp add: exp2R_def power_add)
lemma leRexp2: "s \<le> t \<Longrightarrow> exp2R s \<le> exp2R t"
  by (simp add: exp2R_def power_increasing)
lemma ltR1exp2S: "1 < exp2R (Suc s)" using leR1exp2[of s] by simp

definition dyadic_approx :: "nat \<Rightarrow> real \<Rightarrow> int \<Rightarrow> bool" where
  "dyadic_approx s x m \<longleftrightarrow> of_int m \<le> exp2R s * x \<and> exp2R s * x < of_int m + 1"
definition grid_scale :: "nat \<Rightarrow> int \<Rightarrow> real" where
  "grid_scale s m = of_int m / exp2R s"

lemma approx_floor: "dyadic_approx s x m \<longleftrightarrow> \<lfloor>exp2R s * x\<rfloor> = m"
  unfolding dyadic_approx_def by (metis floor_unique floor_correct of_int_add of_int_1)
lemma approx_inj: "dyadic_approx s x m \<Longrightarrow> dyadic_approx s x n \<Longrightarrow> m = n"
  by (simp add: approx_floor)
lemma approx_exists: "\<exists>m. dyadic_approx s x m" by (simp add: approx_floor)
lemma approx_scale: "dyadic_approx s (grid_scale s m) m"
  by (simp add: dyadic_approx_def grid_scale_def)

lemma approx_halfz:
  assumes a: "dyadic_approx (Suc s) x m"
  shows "dyadic_approx s x (m div 2)"
proof -
  have l: "2 * (m div 2) \<le> m" and u: "m + 1 \<le> 2 * (m div 2 + 1)" by presburger+
  have l0: "(of_int (2 * (m div 2)) :: real) \<le> of_int m" using l by (simp only: of_int_le_iff)
  have l': "2 * (of_int (m div 2) :: real) \<le> of_int m" using l0 by simp
  have u0: "(of_int (m+1) :: real) \<le> of_int (2 * (m div 2+1))" using u by (simp only: of_int_le_iff)
  have u': "of_int m + 1 \<le> 2 * (of_int (m div 2) + 1 :: real)" using u0 by simp
  show ?thesis using a l' u' by (auto simp: dyadic_approx_def; linarith)
qed

lemma nat_le_exp2R: "real n \<le> exp2R n"
proof (induction n)
  case 0 then show ?case by (simp add: exp2R_def)
next
  case (Suc n)
  then show ?case using leR1exp2[of n] by simp
qed

lemma scale_exists:
  assumes x: "0 < x"
  shows "\<exists>s. 1 < exp2R s * x"
proof -
  obtain n :: nat where "1/x < real n" using reals_Archimedean2 by blast
  then have "1/x < exp2R n" using nat_le_exp2R[of n] by linarith
  then have "1 < exp2R n * x" using x by (simp add: pos_divide_less_eq)
  then show ?thesis by blast
qed

lemma approx_between:
  assumes a: "dyadic_approx (Suc s) x m1" and b: "dyadic_approx (Suc s) y m2"
    and gap: "1 < exp2R s * (y-x)"
  shows "\<exists>m. m1+1 \<le> m \<and> m+1 \<le> m2"
proof -
  obtain m where m: "dyadic_approx s (x+y) m" using approx_exists by blast
  have l: "(of_int m1 :: real) < of_int m" using a m gap
    by (auto simp: dyadic_approx_def algebra_simps; linarith)
  have u: "(of_int m :: real) < of_int m2" using b m gap
    by (auto simp: dyadic_approx_def algebra_simps; linarith)
  have "m1 < m" "m < m2" using l u by simp_all
  then show ?thesis by (intro exI[of _ m]) linarith
qed

definition approx_point :: "nat \<Rightarrow> rp_point \<Rightarrow> gpoint \<Rightarrow> bool" where
  "approx_point s z p \<longleftrightarrow> dyadic_approx s (fst z) (fst p) \<and> dyadic_approx s (snd z) (snd p)"
definition scale_point :: "nat \<Rightarrow> gpoint \<Rightarrow> rp_point" where
  "scale_point s p = (grid_scale s (fst p), grid_scale s (snd p))"
definition point_approx :: "nat \<Rightarrow> rp_point \<Rightarrow> gpoint" where
  "point_approx s z = (\<lfloor>exp2R s * fst z\<rfloor>, \<lfloor>exp2R s * snd z\<rfloor>)"

lemma approx_point_iff: "approx_point s z p \<longleftrightarrow> p = point_approx s z"
  by (cases p) (auto simp: approx_point_def point_approx_def approx_floor)
lemma approx_point_inj: "approx_point s z p \<Longrightarrow> approx_point s z q \<Longrightarrow> p=q"
  by (simp add: approx_point_iff)
lemma approx_point_exists: "\<exists>p. approx_point s z p" by (simp add: approx_point_iff)
lemma approx_scale_point: "approx_point s (scale_point s p) p"
  by (simp add: approx_point_def scale_point_def approx_scale)
lemma approx_halfg: "approx_point (Suc s) z p \<Longrightarrow> approx_point s z (halfg p)"
  by (auto simp: approx_point_def halfg_def intro: approx_halfz)
lemma point_approx_halfg: "halfg (point_approx (Suc s) z) = point_approx s z"
  using approx_halfg[of s z "point_approx (Suc s) z"] by (simp add: approx_point_iff)

definition mem_approx :: "nat \<Rightarrow> gpoint set \<Rightarrow> rp_point set" where
  "mem_approx s A = {z. \<exists>p\<in>A. approx_point s z p}"

lemma mem_approx_iff: "z \<in> mem_approx s A \<longleftrightarrow> point_approx s z \<in> A"
  by (auto simp: mem_approx_def approx_point_iff)
lemma sub_mem_approx: "A \<subseteq> B \<Longrightarrow> mem_approx s A \<subseteq> mem_approx s B"
  by (auto simp: mem_approx_iff)
lemma mem_approx_scale: "scale_point s p \<in> mem_approx s A \<longleftrightarrow> p \<in> A"
  using approx_scale_point[of s p] by (simp add: approx_point_iff mem_approx_iff)
lemma mem_approx_refine:
  "mem_approx (Suc s) (halfg -` A) = mem_approx s A"
  by (auto simp: mem_approx_iff point_approx_halfg)
lemma mem_approx_refine_inset:
  "mem_approx s (grect_set (inset_grect r)) \<subseteq>
    mem_approx (Suc s) (grect_set (inset_grect (refine_rect r)))"
proof -
  have e: "grect_set (refine_rect (inset_grect r)) = halfg -` grect_set (inset_grect r)"
    by (auto simp: in_refine_rect)
  have "mem_approx s (grect_set (inset_grect r)) =
    mem_approx (Suc s) (grect_set (inset_grect (inset_grect (refine_rect r))))"
    by (simp only: refine_inset[symmetric] e mem_approx_refine)
  also have "\<dots> \<subseteq> mem_approx (Suc s) (grect_set (inset_grect (refine_rect r)))"
    by (rule sub_mem_approx[OF insetW])
  finally show ?thesis .
qed

type_synonym scaled_rect = "nat \<times> grect"
definition srect_set :: "scaled_rect \<Rightarrow> rp_point set" where
  "srect_set b = mem_approx (fst b) (grect_set (snd b))"
definition refine_srect :: "nat \<Rightarrow> scaled_rect \<Rightarrow> scaled_rect" where
  "refine_srect n b = (n + fst b, (refine_rect ^^ n) (snd b))"
definition inset_srect :: "scaled_rect \<Rightarrow> scaled_rect" where
  "inset_srect b = (fst b, inset_grect (snd b))"

lemma mem_approx_refine_rect:
  "mem_approx (Suc s) (grect_set (refine_rect r)) = mem_approx s (grect_set r)"
  by (auto simp: mem_approx_iff in_refine_rect point_approx_halfg)
lemma in_refine_srect: "srect_set (refine_srect n b) = srect_set b"
  unfolding refine_srect_def srect_set_def
  by (induction n) (simp_all add: mem_approx_refine_rect)
lemma in_refine_inset:
  "srect_set (inset_srect b) \<subseteq> srect_set (inset_srect (refine_srect n b))"
  unfolding refine_srect_def srect_set_def inset_srect_def
proof (induction n)
  case 0 then show ?case by simp
next
  case (Suc n)
  then show ?case using mem_approx_refine_inset[of "n+fst b" "(refine_rect ^^ n) (snd b)"] by auto
qed

lemma approx_interval:
  "\<lfloor>exp2R s * x\<rfloor> \<in> {a..<b} \<longleftrightarrow>
    of_int a \<le> exp2R s*x \<and> exp2R s*x < of_int b"
  by (simp add: le_floor_iff floor_less_iff)

lemma srect_set_bounds:
  "srect_set (s,Grect a b c d) =
    {z. of_int a \<le> exp2R s * fst z \<and> exp2R s * fst z < of_int b \<and>
        of_int c \<le> exp2R s * snd z \<and> exp2R s * snd z < of_int d}"
  by (auto simp: srect_set_def mem_approx_iff point_approx_def le_floor_iff floor_less_iff)

lemma inset_gtouch [simp]: "grect_set (inset_grect (gtouch p)) = {p}"
  by (cases p) (auto; presburger)

lemma approx_rect_scalar:
  assumes x: "dyadic_approx s x m" and y: "dyadic_approx s y n"
    and n: "m-1 \<le> n" "n < m+2"
    and gap: "2 < exp2R s * (x-a)" "2 < exp2R s * (b-x)"
  shows "a < y \<and> y < b"
proof -
  have nl0: "(of_int (m-1) :: real) \<le> of_int n" using n(1) by (simp only: of_int_le_iff)
  have nl: "(of_int m :: real) - 1 \<le> of_int n" using nl0 by simp
  have ni: "n \<le> m+1" using n(2) by linarith
  have nu0: "(of_int n :: real) \<le> of_int (m+1)" using ni by (simp only: of_int_le_iff)
  have nu: "(of_int n :: real) \<le> of_int m + 1" using nu0 by simp
  have lo: "exp2R s * a < exp2R s * y" using x y gap nl nu
    unfolding dyadic_approx_def right_diff_distrib left_diff_distrib by linarith
  have hi: "exp2R s * y < exp2R s * b" using x y gap nl nu
    unfolding dyadic_approx_def right_diff_distrib left_diff_distrib by linarith
  show ?thesis using lo hi by simp
qed

text \<open>Every open rectangle around a point contains a dyadic rectangle
  whose one-pixel inset still contains the point (approx_rect in the reference).\<close>
lemma approx_rect:
  assumes z: "z \<in> rp_rectangle a b c d"
  shows "\<exists>q :: scaled_rect. z \<in> srect_set (inset_srect q) \<and>
    srect_set q \<subseteq> rp_rectangle a b c d"
proof -
  obtain x y where zz: "z=(x,y)" by (cases z) auto
  have gaps: "0 < x-a" "0 < b-x" "0 < y-c" "0 < d-y"
    using z by (auto simp: zz rp_rectangle_def)
  let ?e = "min (x-a) (min (b-x) (min (y-c) (d-y)))"
  have "0 < ?e/2" using gaps by simp
  then obtain s where ss: "1 < exp2R s * (?e/2)" using scale_exists by blast
  have eps: "2 < exp2R s * ?e" using ss unfolding times_divide_eq_right by linarith
  have bound: "2 < exp2R s * t" if "?e\<le>t" for t
  proof -
    have "exp2R s * ?e \<le> exp2R s * t" by (rule mult_left_mono[OF that]) (use ltR0exp2[of s] in linarith)
    then show ?thesis using eps by linarith
  qed
  have small: "2 < exp2R s * (x-a)" "2 < exp2R s * (b-x)"
    "2 < exp2R s * (y-c)" "2 < exp2R s * (d-y)"
    by (rule bound; simp add: min_le_iff_disj)+
  let ?p = "point_approx s z"
  let ?q = "(s,gtouch ?p)"
  have at: "z \<in> srect_set (inset_srect ?q)"
    by (simp add: srect_set_def inset_srect_def mem_approx_iff)
  have sub: "srect_set ?q \<subseteq> rp_rectangle a b c d"
  proof
    fix w assume w: "w \<in> srect_set ?q"
    let ?r = "point_approx s w"
    have wr: "?r \<in> grect_set (gtouch ?p)" using w by (simp add: srect_set_def mem_approx_iff)
    have ap: "approx_point s z ?p" "approx_point s w ?r" by (simp_all add: approx_point_iff)
    have wr': "fst ?p-1 \<le> fst ?r \<and> fst ?r < fst ?p+2 \<and>
      snd ?p-1 \<le> snd ?r \<and> snd ?r < snd ?p+2"
      using wr by (cases ?p; cases ?r) auto
    have n: "fst ?p-1 \<le> fst ?r" "fst ?r < fst ?p+2"
      "snd ?p-1 \<le> snd ?r" "snd ?r < snd ?p+2" using wr' by auto
    have "a < fst w \<and> fst w < b"
      by (rule approx_rect_scalar[OF _ _ n(1,2) small(1,2)])
        (use ap in \<open>auto simp: approx_point_def zz\<close>)
    moreover have "c < snd w \<and> snd w < d"
      by (rule approx_rect_scalar[OF _ _ n(3,4) small(3,4)])
        (use ap in \<open>auto simp: approx_point_def zz\<close>)
    ultimately show "w \<in> rp_rectangle a b c d" by (cases w) (auto simp: rp_rectangle_def)
  qed
  show ?thesis by (rule exI[of _ ?q]) (use at sub in blast)
qed

lemma approx_open:
  assumes op: "open U" and z: "z\<in>U"
  shows "\<exists>q :: scaled_rect. z\<in>srect_set (inset_srect q) \<and> srect_set q\<subseteq>U"
proof -
  have "rp_open U" using op by (simp add: rp_open_eq)
  then obtain a b c d where rect: "z\<in>rp_rectangle a b c d" "rp_rectangle a b c d\<subseteq>U"
    using z unfolding rp_open_def by blast
  obtain q where q: "z\<in>srect_set (inset_srect q)" "srect_set q\<subseteq>rp_rectangle a b c d"
    using approx_rect[OF rect(1)] by blast
  have "srect_set q\<subseteq>U" using q(2) rect(2) by blast
  then show ?thesis using q(1) by blast
qed

lemma inset_srect_sub: "srect_set (inset_srect q) \<subseteq> srect_set q"
  unfolding srect_set_def inset_srect_def by (simp add: sub_mem_approx[OF insetW])
lemma srect_nonempty_proper:
  "srect_set q \<noteq> {} \<Longrightarrow> gr_proper (snd q)"
  by (auto simp: srect_set_def mem_approx_def gr_proper_iff)

lemma rect_approx:
  assumes ap: "approx_point s z p"
  shows "\<exists>a b c d. z \<in> rp_rectangle a b c d \<and>
    rp_rectangle a b c d \<subseteq> srect_set (s,ltouch p)"
proof -
  obtain m n where pp: "p=(m,n)" by (cases p) auto
  let ?a = "grid_scale s (m-1)"
  let ?b = "grid_scale s (m+1)"
  let ?c = "grid_scale s (n-1)"
  let ?d = "grid_scale s (n+1)"
  have z: "z \<in> rp_rectangle ?a ?b ?c ?d" using ap ltR0exp2[of s]
    by (auto simp: rp_rectangle_def mem_Times_iff approx_point_def dyadic_approx_def pp
      grid_scale_def pos_divide_less_eq pos_less_divide_eq mult.commute; linarith)
  have sub: "rp_rectangle ?a ?b ?c ?d \<subseteq> srect_set (s,ltouch p)"
    using ltR0exp2[of s]
    by (auto simp: rp_rectangle_def mem_Times_iff pp srect_set_bounds grid_scale_def
      pos_divide_less_eq pos_less_divide_eq mult.commute; linarith)
  show ?thesis
    apply (rule exI[of _ ?a])
    apply (rule exI[of _ ?b])
    apply (rule exI[of _ ?c])
    apply (rule exI[of _ ?d])
    using z sub by blast
qed

lemma srect_inset_interior:
  assumes z: "z\<in>srect_set (inset_srect b)"
  shows "z\<in>interior (srect_set b)"
proof -
  obtain s r where b: "b=(s,r)" by (cases b) auto
  let ?p = "point_approx s z"
  have p: "?p\<in>grect_set (inset_grect r)" using z by (simp add: b srect_set_def inset_srect_def mem_approx_iff)
  have lr: "grect_set (ltouch ?p)\<subseteq>grect_set r"
    by (rule subset_trans[OF gtouch_l]) (rule iffD1[OF insetP p])
  have ap: "approx_point s z ?p" by (simp add: approx_point_iff)
  obtain a c d e where O: "z\<in>rp_rectangle a c d e"
    "rp_rectangle a c d e\<subseteq>srect_set (s,ltouch ?p)" using rect_approx[OF ap] by blast
  have sub: "rp_rectangle a c d e\<subseteq>srect_set b"
    using O(2) sub_mem_approx[OF lr, of s] by (auto simp: srect_set_def b)
  show ?thesis by (rule interiorI[OF _ O(1) sub]) (simp add: rp_rectangle_def open_Times)
qed

lemma double_inset_refine:
  "srect_set (inset_srect (inset_srect (refine_srect 1 b))) = srect_set (inset_srect b)"
  by (cases b) (simp add: refine_srect_def inset_srect_def srect_set_def
      refine_inset[symmetric] mem_approx_refine_rect)

lemma approx_open_interior:
  assumes "open U" "z\<in>U"
  shows "\<exists>q. z\<in>interior (srect_set (inset_srect q)) \<and> srect_set q\<subseteq>U"
proof -
  obtain b where b: "z\<in>srect_set (inset_srect b)" "srect_set b\<subseteq>U"
    using approx_open[OF assms] by blast
  have z: "z\<in>srect_set (inset_srect (inset_srect (refine_srect 1 b)))"
    using b(1) by (simp only: double_inset_refine)
  have at: "z\<in>interior (srect_set (inset_srect (refine_srect 1 b)))"
    by (rule srect_inset_interior[OF z])
  show ?thesis by (rule exI[of _ "refine_srect 1 b"]) (use at b(2) in \<open>simp add: in_refine_srect\<close>)
qed

lemma cap_rectangle:
  "rp_rectangle a b c d \<inter> rp_rectangle e f g h =
    rp_rectangle (max a e) (min b f) (max c g) (min d h)"
  by (auto simp: rp_rectangle_def)

definition sep_interval :: "real \<Rightarrow> real \<Rightarrow> real set" where
  "sep_interval x y = {(if y\<le>(x+y)/2 then y-1 else (x+y)/2)<..<
      (if (x+y)/2\<le>y then y+1 else (x+y)/2)}"
lemma mem_sep_interval: "y\<in>sep_interval x y"
  by (auto simp: sep_interval_def split: if_splits; linarith)
lemma meet_sep_interval: "sep_interval x y \<inter> sep_interval y x \<noteq> {} \<Longrightarrow> x=y"
  by (auto simp: sep_interval_def split: if_splits; linarith)

definition sep_rect :: "rp_point \<Rightarrow> rp_point \<Rightarrow> rp_point set" where
  "sep_rect z w = sep_interval (fst z) (fst w) \<times> sep_interval (snd z) (snd w)"
lemma mem_sep_rect: "w\<in>sep_rect z w"
  by (simp add: sep_rect_def mem_sep_interval mem_Times_iff)
lemma open_sep_rect: "open (sep_rect z w)"
  by (simp add: sep_rect_def sep_interval_def open_Times)
lemma meet_sep_rect: "sep_rect z w \<inter> sep_rect w z \<noteq> {} \<Longrightarrow> z=w"
  using meet_sep_interval by (auto simp: sep_rect_def prod_eq_iff mem_Times_iff)

end
