(* Title: Pascal_Affine.thy *)

section \<open>Pascal's Hexagon Theorem in the Real Plane\<close>

theory Pascal_Affine
  imports
    "HOL-Analysis.Analysis"
    Pascal_Projective
begin

text \<open>
  In this section, we prove Pascal's hexagon theorem in the real plane \<open>\<real>\<^sup>2\<close>.

  Points of the plane have the HOL-Analysis type \<^typ>\<open>real^2\<close>, with coordinates
  \<open>p$1\<close> and \<open>p$2\<close>. Collinearity is defined by the standard notion @{const collinear} from
  HOL-Analysis, and a circle is given by the standard distance @{const dist}.

  The definition \<open>homog\<close> maps points in \<open>\<real>\<^sup>2\<close> into the projective plane.
\<close>

definition homog :: "real^2 \<Rightarrow> real vec3" where
  "homog x = (x$1, x$2, 1)"

subsection \<open>Collinearity in coordinates\<close>

lemma collinear_3_real2:
  fixes a b c :: "real^2"
  shows "collinear {a, b, c} \<longleftrightarrow> (b$1 - a$1) * (c$2 - a$2) = (c$1 - a$1) * (b$2 - a$2)"
proof -
  have "collinear {a, b, c} \<longleftrightarrow> a - b = 0 \<or> c - b = 0 \<or> (\<exists>k. c - b = k *\<^sub>R (a - b))"
    by (simp add: collinear_3[of a b c] collinear_lemma)
  also have "\<dots> \<longleftrightarrow> (b$1 - a$1) * (c$2 - a$2) = (c$1 - a$1) * (b$2 - a$2)"
    (is "?L \<longleftrightarrow> ?R")
  proof
    assume ?L
    then consider "a - b = 0" | "c - b = 0" | k where "c - b = k *\<^sub>R (a - b)"
      by blast
    then show ?R
    proof cases
      case 1
      then have "a$1 = b$1" "a$2 = b$2" by (metis eq_iff_diff_eq_0)+
      then show ?thesis by simp
    next
      case 2
      then have "c$1 = b$1" "c$2 = b$2" by (metis eq_iff_diff_eq_0)+
      then show ?thesis by (simp add: algebra_simps)
    next
      case (3 k)
      then have "(c - b)$1 = (k *\<^sub>R (a - b))$1" "(c - b)$2 = (k *\<^sub>R (a - b))$2"
        by simp_all
      then have c1: "c$1 = b$1 + k * (a$1 - b$1)" and c2: "c$2 = b$2 + k * (a$2 - b$2)"
        by (simp_all add: algebra_simps)
      show ?thesis unfolding c1 c2 by (simp add: algebra_simps)
    qed
  next
    assume R: ?R
    show ?L
    proof (cases "a = b")
      case True
      then show ?thesis by simp
    next
      case False
      then have "a$1 \<noteq> b$1 \<or> a$2 \<noteq> b$2"
        by (metis (mono_tags, lifting) exhaust_2 vec_eq_iff)
      have "(c$2 - b$2) * (a$1 - b$1) - (c$1 - b$1) * (a$2 - b$2) =
          (c$1 - a$1) * (b$2 - a$2) - (b$1 - a$1) * (c$2 - a$2)"
        by (simp add: algebra_simps)
      with R have R': "(c$2 - b$2) * (a$1 - b$1) = (c$1 - b$1) * (a$2 - b$2)"
        by simp
      show ?thesis
        using \<open>a$1 \<noteq> b$1 \<or> a$2 \<noteq> b$2\<close>
      proof
        assume ne: "a$1 \<noteq> b$1"
        then have ne': "a$1 - b$1 \<noteq> 0" by simp
        define k where "k = (c$1 - b$1) / (a$1 - b$1)"
        have "(c - b)$1 = (k *\<^sub>R (a - b))$1"
          using ne' by (simp add: k_def)
        moreover have "(c - b)$2 = (k *\<^sub>R (a - b))$2"
        proof -
          have "c$2 - b$2 = (c$2 - b$2) * (a$1 - b$1) / (a$1 - b$1)"
            using ne' by simp
          also have "\<dots> = (c$1 - b$1) * (a$2 - b$2) / (a$1 - b$1)"
            by (simp only: R')
          also have "\<dots> = k * (a$2 - b$2)"
            by (simp add: k_def)
          finally show ?thesis by simp
        qed
        ultimately have "c - b = k *\<^sub>R (a - b)"
          by (simp add: vec_eq_iff forall_2
            del: vector_minus_component vector_scaleR_component)
        then show ?thesis by blast
      next
        assume ne: "a$2 \<noteq> b$2"
        then have ne': "a$2 - b$2 \<noteq> 0" by simp
        define k where "k = (c$2 - b$2) / (a$2 - b$2)"
        have "(c - b)$2 = (k *\<^sub>R (a - b))$2"
          using ne' by (simp add: k_def)
        moreover have "(c - b)$1 = (k *\<^sub>R (a - b))$1"
        proof -
          have "c$1 - b$1 = (c$1 - b$1) * (a$2 - b$2) / (a$2 - b$2)"
            using ne' by simp
          also have "\<dots> = (c$2 - b$2) * (a$1 - b$1) / (a$2 - b$2)"
            by (simp only: R')
          also have "\<dots> = k * (a$1 - b$1)"
            by (simp add: k_def)
          finally show ?thesis by simp
        qed
        ultimately have "c - b = k *\<^sub>R (a - b)"
          by (simp add: vec_eq_iff forall_2
            del: vector_minus_component vector_scaleR_component)
        then show ?thesis by blast
      qed
    qed
  qed
  finally show ?thesis .
qed

lemma collinear_iff_det3:
  fixes a b c :: "real^2"
  shows "collinear {a, b, c} \<longleftrightarrow> det3 (homog a) (homog b) (homog c) = 0"
  by (simp add: collinear_3_real2 homog_def algebra_simps)

lemma homog_cross_eq_0:
  assumes "cross (homog a) (homog b) = (0, 0, 0)"
  shows "a = b"
proof -
  have "a$1 = b$1" "a$2 = b$2"
    using assms by (simp_all add: homog_def)
  then show ?thesis
    by (simp add: vec_eq_iff forall_2)
qed

subsection \<open>Conics in the real plane\<close>

text \<open>
  \<^term>\<open>conic_eq a b c d e f p\<close> is the value of the polynomial
  \<open>a x\<^sup>2 + b x y + c y\<^sup>2 + d x + e y + f\<close> at the point \<open>p = (x, y)\<close>.
\<close>

definition conic_eq :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^2 \<Rightarrow> real" where
  "conic_eq a b c d e f p = a * (p$1)\<^sup>2 + b * p$1 * p$2 + c * (p$2)\<^sup>2 + d * p$1 + e * p$2 + f"

text \<open>
  An \<open>affine_conic\<close> is the zero set of such a polynomial
  whose six coefficients are not all zero. The definition therefore includes both degenerate
  and non-degenerate cases.
\<close>

definition affine_conic :: "(real^2) set \<Rightarrow> bool" where
  "affine_conic S \<longleftrightarrow>
     (\<exists>a b c d e f. \<not> (a = 0 \<and> b = 0 \<and> c = 0 \<and> d = 0 \<and> e = 0 \<and> f = 0) \<and>
        S = {p. conic_eq a b c d e f p = 0})"

text \<open>
  A conic is \<^emph>\<open>non-degenerate\<close> if, in addition, the homogenised polynomial
  \<open>a x\<^sup>2 + b x y + c y\<^sup>2 + d x z + e y z + f z\<^sup>2\<close> is a non-degenerate quadratic form,
  i.e.\ the symmetric matrix with rows \<open>(2a, b, d)\<close>, \<open>(b, 2c, e)\<close>, \<open>(d, e, 2f)\<close> is
  invertible.
\<close>

definition nondegenerate_conic :: "(real^2) set \<Rightarrow> bool" where
  "nondegenerate_conic S \<longleftrightarrow>
     (\<exists>a b c d e f. det3 (2 * a, b, d) (b, 2 * c, e) (d, e, 2 * f) \<noteq> 0 \<and>
        S = {p. conic_eq a b c d e f p = 0})"

lemma qf_homog: "qf (a, c, f, b, e, d) (homog p) = conic_eq a b c d e f p"
  by (simp add: homog_def conic_eq_def power2_eq_square algebra_simps)

lemma nondegenerate_conic_imp_affine_conic:
  assumes "nondegenerate_conic S"
  shows "affine_conic S"
proof -
  obtain a b c d e f where nd: "det3 (2 * a, b, d) (b, 2 * c, e) (d, e, 2 * f) \<noteq> 0"
    and S: "S = {p. conic_eq a b c d e f p = 0}"
    using assms unfolding nondegenerate_conic_def by blast
  have "\<not> (a = 0 \<and> b = 0 \<and> c = 0 \<and> d = 0 \<and> e = 0 \<and> f = 0)"
    using nd by auto
  then show ?thesis
    unfolding affine_conic_def using S by blast
qed

lemma nondegenerate_conic_no_three_collinear:
  fixes X Y Z :: "real^2"
  assumes "nondegenerate_conic S" "X \<in> S" "Y \<in> S" "Z \<in> S" "distinct [X, Y, Z]"
  shows "\<not> collinear {X, Y, Z}"
proof -
  obtain a b c d e f where nd: "det3 (2 * a, b, d) (b, 2 * c, e) (d, e, 2 * f) \<noteq> 0"
    and S: "S = {p. conic_eq a b c d e f p = 0}"
    using assms(1) unfolding nondegenerate_conic_def by blast
  define q where "q = (a, c, f, b, e, d)"
  have "nondegenerate q"
    using nd by (simp add: q_def nondegenerate_def)
  moreover have "qf q (homog X) = 0" "qf q (homog Y) = 0" "qf q (homog Z) = 0"
    using assms(2-4) by (simp_all add: q_def qf_homog S)
  moreover have "cross (homog X) (homog Y) \<noteq> (0, 0, 0)" "cross (homog X) (homog Z) \<noteq> (0, 0, 0)"
    "cross (homog Y) (homog Z) \<noteq> (0, 0, 0)"
    using assms(5) homog_cross_eq_0 by auto
  ultimately have "det3 (homog X) (homog Y) (homog Z) \<noteq> 0"
    by (rule nondegenerate_no_three_collinear)
  then show ?thesis
    by (simp add: collinear_iff_det3)
qed

subsection \<open>Hexagons on arbitrary conics\<close>

text \<open>
  \<^bold>\<open>Pascal's theorem for arbitrary conics\<close>. Let \<open>A\<close>, \<open>B\<close>, \<open>C\<close>, \<open>D\<close>, \<open>E\<close>, \<open>F\<close> be six
  points on a conic \<open>S\<close>, possibly degenerate, forming the hexagon \<open>ABCDEF\<close>, whose pairs of opposite
  sides are \<open>AB, DE\<close>; \<open>BC, EF\<close> and \<open>CD, FA\<close>.  Assume that no three of the points are collinear,
  except possibly the two triples of alternate vertices \<open>A, C, E\<close> and \<open>B, D, F\<close>.  If
  \<open>P\<close> lies on \<open>AB\<close> and \<open>DE\<close>, \<open>Q\<close> lies on \<open>BC\<close> and \<open>EF\<close>, and \<open>R\<close> lies on \<open>CD\<close> and
  \<open>FA\<close>, then \<open>P\<close>, \<open>Q\<close> and \<open>R\<close> are collinear.
\<close>

theorem pascal_hexagon_any_conic:
  fixes A B C D E F P Q R :: "real^2"
  assumes conic: "affine_conic S"
    and on_conic: "{A, B, C, D, E, F} \<subseteq> S"
    and nc: "\<not> collinear {A, B, C}" "\<not> collinear {A, B, D}" "\<not> collinear {A, B, E}"
            "\<not> collinear {A, B, F}" "\<not> collinear {A, C, D}" "\<not> collinear {A, C, F}"
            "\<not> collinear {A, D, E}" "\<not> collinear {A, D, F}" "\<not> collinear {A, E, F}"
            "\<not> collinear {B, C, D}" "\<not> collinear {B, C, E}" "\<not> collinear {B, C, F}"
            "\<not> collinear {B, D, E}" "\<not> collinear {B, E, F}" "\<not> collinear {C, D, E}"
            "\<not> collinear {C, D, F}" "\<not> collinear {C, E, F}" "\<not> collinear {D, E, F}"
    and P: "collinear {A, B, P}" "collinear {D, E, P}"
    and Q: "collinear {B, C, Q}" "collinear {E, F, Q}"
    and R: "collinear {C, D, R}" "collinear {F, A, R}"
  shows "collinear {P, Q, R}"
proof -
  obtain a b c d e f where nz: "\<not> (a = 0 \<and> b = 0 \<and> c = 0 \<and> d = 0 \<and> e = 0 \<and> f = 0)"
    and S: "S = {p. conic_eq a b c d e f p = 0}"
    using conic unfolding affine_conic_def by blast
  define q where "q = (a, c, f, b, e, d)"
  have q0: "q \<noteq> (0, 0, 0, 0, 0, 0)"
    using nz by (auto simp: q_def)
  have on: "qf q (homog A) = 0" "qf q (homog B) = 0" "qf q (homog C) = 0"
           "qf q (homog D) = 0" "qf q (homog E) = 0" "qf q (homog F) = 0"
    using on_conic by (simp_all add: q_def qf_homog S)
  have "\<not> collinear {B, F, A}"
    using nc(4) by (simp add: insert_commute)
  then have dets: "det3 (homog A) (homog B) (homog C) \<noteq> 0"
    "det3 (homog A) (homog B) (homog D) \<noteq> 0" "det3 (homog A) (homog D) (homog E) \<noteq> 0"
    "det3 (homog B) (homog C) (homog E) \<noteq> 0" "det3 (homog A) (homog E) (homog F) \<noteq> 0"
    "det3 (homog C) (homog D) (homog F) \<noteq> 0" "det3 (homog B) (homog F) (homog A) \<noteq> 0"
    using nc(1,2,7,11,9,16) by (simp_all add: collinear_iff_det3)
  have "det3 (homog P) (homog Q) (homog R) = 0"
    by (rule projective_hexagon[OF q0 on dets])
      (use P Q R in \<open>simp_all add: collinear_iff_det3\<close>)
  then show ?thesis
    by (simp add: collinear_iff_det3)
qed

subsection \<open>Pascal's hexagon theorem\<close>

text \<open>
  \<^bold>\<open>Pascal's hexagon theorem.\<close>  Let \<open>A\<close>, \<open>B\<close>, \<open>C\<close>, \<open>D\<close>, \<open>E\<close>, \<open>F\<close> be six distinct
  points on a non-degenerate conic \<open>S\<close> (an ellipse, parabola or hyperbola), forming the
  hexagon \<open>ABCDEF\<close>.  If \<open>P\<close> lies on \<open>AB\<close> and \<open>DE\<close>, \<open>Q\<close> lies on \<open>BC\<close> and \<open>EF\<close>, and
  \<open>R\<close> lies on \<open>CD\<close> and \<open>FA\<close>, then \<open>P\<close>, \<open>Q\<close> and \<open>R\<close> are collinear. The vertices may lie on the
  conic in any order.
\<close>

theorem pascal_hexagon:
  fixes A B C D E F P Q R :: "real^2"
  assumes conic: "nondegenerate_conic S"
    and on_conic: "{A, B, C, D, E, F} \<subseteq> S"
    and distinct: "distinct [A, B, C, D, E, F]"
    and P: "collinear {A, B, P}" "collinear {D, E, P}"
    and Q: "collinear {B, C, Q}" "collinear {E, F, Q}"
    and R: "collinear {C, D, R}" "collinear {F, A, R}"
  shows "collinear {P, Q, R}"
proof -
  have nc: "collinear {X, Y, Z} \<longleftrightarrow> False"
    if "X \<in> {A, B, C, D, E, F}" "Y \<in> {A, B, C, D, E, F}" "Z \<in> {A, B, C, D, E, F}"
       "X \<noteq> Y" "X \<noteq> Z" "Y \<noteq> Z" for X Y Z
    using nondegenerate_conic_no_three_collinear[OF conic, of X Y Z] that on_conic by auto
  show ?thesis
  proof (rule pascal_hexagon_any_conic[where S = S and A = A and B = B and C = C and D = D
        and E = E and F = F])
    show "affine_conic S"
      by (rule nondegenerate_conic_imp_affine_conic[OF conic])
  qed (use on_conic P Q R distinct in \<open>simp_all add: nc\<close>)
qed

subsection \<open>The circle version\<close>

lemma dist_power2_real2:
  fixes c p :: "real^2"
  shows "(dist c p)\<^sup>2 = (p$1 - c$1)\<^sup>2 + (p$2 - c$2)\<^sup>2"
proof -
  have "(dist c p)\<^sup>2 = inner (c - p) (c - p)"
    by (simp only: dist_norm power2_norm_eq_inner)
  also have "\<dots> = (p$1 - c$1)\<^sup>2 + (p$2 - c$2)\<^sup>2"
    by (simp add: inner_vec_def sum_2 power2_eq_square algebra_simps)
  finally show ?thesis .
qed

text \<open>
  A circle \<open>{p. dist c p = r}\<close> with \<open>r > 0\<close> is a non-degenerate conic: its equation is
  \<open>x\<^sup>2 + y\<^sup>2 - 2 c\<^sub>1 x - 2 c\<^sub>2 y + (c\<^sub>1\<^sup>2 + c\<^sub>2\<^sup>2 - r\<^sup>2) = 0\<close>, and the determinant of its matrix
  is \<open>-8 r\<^sup>2 \<noteq> 0\<close>.
\<close>

lemma circle_nondegenerate_conic:
  fixes c :: "real^2"
  assumes r: "r > 0"
  shows "nondegenerate_conic {p. dist c p = r}"
proof -
  define f where "f = (c$1)\<^sup>2 + (c$2)\<^sup>2 - r\<^sup>2"
  have "{p. dist c p = r} = {p. conic_eq 1 0 1 (-2 * c$1) (-2 * c$2) f p = 0}"
  proof (rule Collect_cong)
    fix p
    have "dist c p = r \<longleftrightarrow> (dist c p)\<^sup>2 = r\<^sup>2"
      using r by simp
    also have "\<dots> \<longleftrightarrow> (dist c p)\<^sup>2 - r\<^sup>2 = 0"
      by simp
    also have "(dist c p)\<^sup>2 - r\<^sup>2 = conic_eq 1 0 1 (-2 * c$1) (-2 * c$2) f p"
      by (simp only: dist_power2_real2) (simp add: conic_eq_def f_def power2_eq_square algebra_simps)
    finally show "dist c p = r \<longleftrightarrow> conic_eq 1 0 1 (-2 * c$1) (-2 * c$2) f p = 0" .
  qed
  moreover have "det3 (2 * 1, 0, -2 * c$1) (0, 2 * 1, -2 * c$2) (-2 * c$1, -2 * c$2, 2 * f) = - 8 * r\<^sup>2"
    by (simp add: f_def power2_eq_square algebra_simps)
  then have "det3 (2 * 1, 0, -2 * c$1) (0, 2 * 1, -2 * c$2) (-2 * c$1, -2 * c$2, 2 * f) \<noteq> 0"
    using r by simp
  ultimately show ?thesis
    unfolding nondegenerate_conic_def by blast
qed

text \<open>
  \<^bold>\<open>Pascal's theorem for a circle.\<close> If \<open>A\<close>, \<open>\<dots>\<close>, \<open>F\<close> are six distinct points on the circle
  with centre \<open>c\<close> and radius \<open>r\<close>, and \<open>P\<close>, \<open>Q\<close>, \<open>R\<close> lie on the pairs of opposite sides as before,
  then \<open>P\<close>, \<open>Q\<close>, \<open>R\<close> are collinear.
\<close>

corollary pascal_hexagon_circle:
  fixes c A B C D E F P Q R :: "real^2" and r :: real
  assumes distinct: "distinct [A, B, C, D, E, F]"
    and on_circle: "dist c A = r" "dist c B = r" "dist c C = r"
                   "dist c D = r" "dist c E = r" "dist c F = r"
    and P: "collinear {A, B, P}" "collinear {D, E, P}"
    and Q: "collinear {B, C, Q}" "collinear {E, F, Q}"
    and R: "collinear {C, D, R}" "collinear {F, A, R}"
  shows "collinear {P, Q, R}"
proof -
  have "r \<noteq> 0"
  proof
    assume "r = 0"
    then have "A = c" "B = c"
      using on_circle(1,2) by auto
    then show False
      using distinct by simp
  qed
  then have r: "r > 0"
    using on_circle(1) zero_le_dist[of c A] by linarith
  have on_conic: "{A, B, C, D, E, F} \<subseteq> {p. dist c p = r}"
    using on_circle by simp
  show ?thesis
    by (rule pascal_hexagon[OF circle_nondegenerate_conic[OF r] on_conic distinct P Q R])
qed

subsection \<open>Pappus's hexagon theorem\<close>

lemma not_collinear_same_line:
  fixes A C E X :: "real^2"
  assumes ACE: "collinear {A, C, E}" and d: "distinct [A, C, E]"
    and X: "\<not> collinear {A, C, X}"
  shows "\<not> collinear {A, E, X}" and "\<not> collinear {C, E, X}"
proof -
  show "\<not> collinear {A, E, X}"
  proof
    assume "collinear {A, E, X}"
    moreover have "collinear {C, A, E}"
      using ACE by (simp add: insert_commute)
    ultimately have "collinear {C, A, X}"
      using collinear_3_trans[of C A E X] d by simp
    then show False
      using X by (simp add: insert_commute)
  qed
  show "\<not> collinear {C, E, X}"
  proof
    assume "collinear {C, E, X}"
    then have "collinear {A, C, X}"
      using collinear_3_trans[of A C E X] ACE d by simp
    then show False
      using X by simp
  qed
qed

lemma line_coeffs:
  fixes A C :: "real^2"
  assumes "A \<noteq> C"
  shows "\<not> (A$2 - C$2 = 0 \<and> C$1 - A$1 = 0)"
  using assms by (auto simp: vec_eq_iff forall_2)

lemma product_coeffs_nonzero:
  fixes \<alpha>1 \<beta>1 \<alpha>2 \<beta>2 :: real
  assumes "\<not> (\<alpha>1 = 0 \<and> \<beta>1 = 0)" "\<not> (\<alpha>2 = 0 \<and> \<beta>2 = 0)"
  shows "\<not> (\<alpha>1 * \<alpha>2 = 0 \<and> \<alpha>1 * \<beta>2 + \<beta>1 * \<alpha>2 = 0 \<and> \<beta>1 * \<beta>2 = 0)"
proof
  assume h: "\<alpha>1 * \<alpha>2 = 0 \<and> \<alpha>1 * \<beta>2 + \<beta>1 * \<alpha>2 = 0 \<and> \<beta>1 * \<beta>2 = 0"
  show False
  proof (cases "\<alpha>1 = 0")
    case True
    then have "\<beta>1 \<noteq> 0" using assms(1) by simp
    then show False using h True assms(2) by simp
  next
    case False
    then have "\<alpha>2 = 0" using h by simp
    then show False using h False assms(2) by simp
  qed
qed

text \<open>
  \<^bold>\<open>Pappus's hexagon theorem.\<close>  Let \<open>A\<close>, \<open>C\<close>, \<open>E\<close> be distinct points on one line and
  \<open>B\<close>, \<open>D\<close>, \<open>F\<close> distinct points on another, with none of the six points lying on both
  lines: none of \<open>B\<close>, \<open>D\<close>, \<open>F\<close> is on the line \<open>AC\<close>, and none of \<open>A\<close>, \<open>C\<close>, \<open>E\<close> is on
  the line \<open>BD\<close>. If \<open>P\<close> lies on \<open>AB\<close> and \<open>DE\<close>, \<open>Q\<close> lies on \<open>BC\<close> and \<open>EF\<close>, and \<open>R\<close>
  lies on \<open>CD\<close> and \<open>FA\<close>, then \<open>P\<close>, \<open>Q\<close> and \<open>R\<close> are collinear.

  This is the special case of Pascal's theorem for the degenerate conic formed by the two lines.
\<close>

corollary pappus_hexagon:
  fixes A B C D E F P Q R :: "real^2"
  assumes ACE: "collinear {A, C, E}" and BDF: "collinear {B, D, F}"
    and d1: "distinct [A, C, E]" and d2: "distinct [B, D, F]"
    and off1: "\<not> collinear {A, C, B}" "\<not> collinear {A, C, D}" "\<not> collinear {A, C, F}"
    and off2: "\<not> collinear {B, D, A}" "\<not> collinear {B, D, C}" "\<not> collinear {B, D, E}"
    and P: "collinear {A, B, P}" "collinear {D, E, P}"
    and Q: "collinear {B, C, Q}" "collinear {E, F, Q}"
    and R: "collinear {C, D, R}" "collinear {F, A, R}"
  shows "collinear {P, Q, R}"
proof -
  define l1 where "l1 p = (C$1 - A$1) * (p$2 - A$2) - (p$1 - A$1) * (C$2 - A$2)" for p :: "real^2"
  define l2 where "l2 p = (D$1 - B$1) * (p$2 - B$2) - (p$1 - B$1) * (D$2 - B$2)" for p :: "real^2"
  define \<alpha>1 \<beta>1 \<gamma>1 where "\<alpha>1 = A$2 - C$2" and "\<beta>1 = C$1 - A$1"
    and "\<gamma>1 = A$1 * (C$2 - A$2) - A$2 * (C$1 - A$1)"
  define \<alpha>2 \<beta>2 \<gamma>2 where "\<alpha>2 = B$2 - D$2" and "\<beta>2 = D$1 - B$1"
    and "\<gamma>2 = B$1 * (D$2 - B$2) - B$2 * (D$1 - B$1)"
  define S where "S = {p. conic_eq (\<alpha>1 * \<alpha>2) (\<alpha>1 * \<beta>2 + \<beta>1 * \<alpha>2) (\<beta>1 * \<beta>2)
                       (\<alpha>1 * \<gamma>2 + \<gamma>1 * \<alpha>2) (\<beta>1 * \<gamma>2 + \<gamma>1 * \<beta>2) (\<gamma>1 * \<gamma>2) p = 0}"
  have S_prod: "p \<in> S \<longleftrightarrow> l1 p * l2 p = 0" for p
  proof -
    have "conic_eq (\<alpha>1 * \<alpha>2) (\<alpha>1 * \<beta>2 + \<beta>1 * \<alpha>2) (\<beta>1 * \<beta>2)
            (\<alpha>1 * \<gamma>2 + \<gamma>1 * \<alpha>2) (\<beta>1 * \<gamma>2 + \<gamma>1 * \<beta>2) (\<gamma>1 * \<gamma>2) p = l1 p * l2 p"
      by (simp add: conic_eq_def l1_def l2_def \<alpha>1_def \<beta>1_def \<gamma>1_def \<alpha>2_def \<beta>2_def \<gamma>2_def
          power2_eq_square algebra_simps)
    then show ?thesis
      by (simp add: S_def)
  qed
  have conic: "affine_conic S"
  proof -
    have "\<not> (\<alpha>1 = 0 \<and> \<beta>1 = 0)"
      using line_coeffs[of A C] d1 by (simp add: \<alpha>1_def \<beta>1_def)
    moreover have "\<not> (\<alpha>2 = 0 \<and> \<beta>2 = 0)"
      using line_coeffs[of B D] d2 by (simp add: \<alpha>2_def \<beta>2_def)
    ultimately have "\<not> (\<alpha>1 * \<alpha>2 = 0 \<and> \<alpha>1 * \<beta>2 + \<beta>1 * \<alpha>2 = 0 \<and> \<beta>1 * \<beta>2 = 0)"
      by (rule product_coeffs_nonzero)
    then show ?thesis
      unfolding affine_conic_def S_def by blast
  qed
  have l1_0: "l1 A = 0" "l1 C = 0" "l1 E = 0"
    using ACE by (simp_all add: l1_def collinear_3_real2)
  have l2_0: "l2 B = 0" "l2 D = 0" "l2 F = 0"
    using BDF by (simp_all add: l2_def collinear_3_real2)
  have on_conic: "{A, B, C, D, E, F} \<subseteq> S"
    using l1_0 l2_0 by (simp add: S_prod)
  note nA = not_collinear_same_line[OF ACE d1 off1(1)]
            not_collinear_same_line[OF ACE d1 off1(2)]
            not_collinear_same_line[OF ACE d1 off1(3)]
  note nB = not_collinear_same_line[OF BDF d2 off2(1)]
            not_collinear_same_line[OF BDF d2 off2(2)]
            not_collinear_same_line[OF BDF d2 off2(3)]
  show ?thesis
  proof (rule pascal_hexagon_any_conic[where S = S and A = A and B = B and C = C and D = D
        and E = E and F = F])
    show "affine_conic S"
      by (rule conic)
  qed (use on_conic off1 off2 nA nB P Q R in \<open>simp_all add: insert_commute\<close>)
qed

end
