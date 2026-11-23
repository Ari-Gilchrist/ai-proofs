(* Title: Pascal_Projective.thy *)

section \<open>Hexagons on Conics in the Projective Plane over a Field\<close>

theory Pascal_Projective
  imports Main
begin

text \<open>
  In this section, we use homogeneous coordinates: a point of the projective plane is represented by a
  non-zero vector \<open>(x, y, z)\<close> in \<open>'a\<^sup>3\<close>, and two vectors represent the same point if one
  is a non-zero multiple of the other.  An ordinary point \<open>(x, y)\<close> of the plane
  corresponds to \<open>(x, y, 1)\<close>.  The vectors with \<open>z = 0\<close> are the \<^emph>\<open>points at infinity\<close>,
  where parallel lines meet.  A line \<open>l x + m y + n z = 0\<close> is represented by its
  coefficient vector \<open>(l, m, n)\<close>, again up to a non-zero multiple. Doing so simplifies the proof,
  since the relevant geometry can be expressed with linear algebra.

  Formally, the projective plane is the set of non-zero
  vectors after accounting for scaling. In our formulation, the statements quantify over all
  vectors including \<open>(0, 0, 0)\<close>, which represents no point.
  In the main results, the zero vector is either excluded by the hypotheses or makes the conclusion
  trivially true.
\<close>

subsection \<open>Vectors in \<open>'a\<^sup>3\<close>\<close>

text \<open>
  No division is needed, so the following vector-based notions are defined over
  commutative rings.
\<close>

type_synonym 'a vec3 = "'a \<times> 'a \<times> 'a"

fun cross :: "'a::comm_ring vec3 \<Rightarrow> 'a vec3 \<Rightarrow> 'a vec3" where
  "cross (a1, a2, a3) (b1, b2, b3) =
     (a2 * b3 - a3 * b2, a3 * b1 - a1 * b3, a1 * b2 - a2 * b1)"

fun dot :: "'a::comm_ring vec3 \<Rightarrow> 'a vec3 \<Rightarrow> 'a" where
  "dot (a1, a2, a3) (b1, b2, b3) = a1 * b1 + a2 * b2 + a3 * b3"

text \<open>Determinant of the matrix with rows \<open>A\<close>, \<open>B\<close>, \<open>C\<close>; zero iff the three points are collinear.\<close>

fun det3 :: "'a::comm_ring vec3 \<Rightarrow> 'a vec3 \<Rightarrow> 'a vec3 \<Rightarrow> 'a" where
  "det3 (a1, a2, a3) (b1, b2, b3) (c1, c2, c3) =
     a1 * (b2 * c3 - b3 * c2) - a2 * (b1 * c3 - b3 * c1) + a3 * (b1 * c2 - b2 * c1)"

fun scale3 :: "'a::comm_ring \<Rightarrow> 'a vec3 \<Rightarrow> 'a vec3" where
  "scale3 k (a1, a2, a3) = (k * a1, k * a2, k * a3)"

text \<open>The linear combination \<open>u\<^sub>1 A + u\<^sub>2 B + u\<^sub>3 C\<close>, i.e.\ \<open>M u\<close> for the matrix \<open>M\<close> with columns \<open>A\<close>, \<open>B\<close>, \<open>C\<close>.\<close>

fun lincomb :: "'a::comm_ring vec3 \<Rightarrow> 'a vec3 \<Rightarrow> 'a vec3 \<Rightarrow> 'a vec3 \<Rightarrow> 'a vec3" where
  "lincomb (a1, a2, a3) (b1, b2, b3) (c1, c2, c3) (x, y, z) =
     (x * a1 + y * b1 + z * c1, x * a2 + y * b2 + z * c2, x * a3 + y * b3 + z * c3)"

text \<open>
  Basic results and identities.
\<close>

lemma det3_eq_dot_cross: "det3 A B C = dot A (cross B C)"
  by (cases A; cases B; cases C) (simp add: algebra_simps)

lemma det3_same1 [simp]: "det3 A A C = 0"
  by (cases A; cases C) (simp add: algebra_simps)

lemma det3_same2 [simp]: "det3 A B A = 0"
  by (cases A; cases B) (simp add: algebra_simps)

lemma det3_same3 [simp]: "det3 A B B = 0"
  by (cases A; cases B) (simp add: algebra_simps)

lemma dot_cross_left [simp]: "dot A (cross A B) = 0"
  by (cases A; cases B) (simp add: algebra_simps)

lemma dot_cross_right [simp]: "dot B (cross A B) = 0"
  by (cases A; cases B) (simp add: algebra_simps)

lemma cross_same [simp]: "cross A A = (0, 0, 0)"
  by (cases A) (simp add: algebra_simps)

lemma det3_scale: "det3 (scale3 k A) (scale3 k B) (scale3 k C) = k * k * k * det3 A B C"
  by (cases A; cases B; cases C) (simp add: algebra_simps)

lemma lincomb_scale: "lincomb A B C (scale3 k u) = scale3 k (lincomb A B C u)"
  by (cases A; cases B; cases C; cases u) (simp add: algebra_simps)

lemma lincomb_scale_columns:
  "lincomb (scale3 k A) (scale3 k B) (scale3 k C) u = scale3 k (lincomb A B C u)"
  by (cases A; cases B; cases C; cases u) (simp add: algebra_simps)

lemma scale_one [simp]: "scale3 1 A = (A :: 'a::comm_ring_1 vec3)"
  by (cases A) simp

lemma scale_scale: "scale3 k (scale3 l A) = scale3 (k * l) A"
  by (cases A) (simp add: algebra_simps)

lemma lincomb_basis1 [simp]:
  fixes A B C :: "'a::comm_ring_1 vec3"
  shows "lincomb A B C (1, 0, 0) = A"
  by (cases A; cases B; cases C) simp

lemma lincomb_basis2 [simp]:
  fixes A B C :: "'a::comm_ring_1 vec3"
  shows "lincomb A B C (0, 1, 0) = B"
  by (cases A; cases B; cases C) simp

lemma lincomb_basis3 [simp]:
  fixes A B C :: "'a::comm_ring_1 vec3"
  shows "lincomb A B C (0, 0, 1) = C"
  by (cases A; cases B; cases C) simp

subsection \<open>The behaviour of cross products and determinants under linear maps\<close>

lemma cross_lincomb:
  "cross (lincomb A B C u) (lincomb A B C v) =
     lincomb (cross B C) (cross C A) (cross A B) (cross u v)"
  by (cases A; cases B; cases C) (cases u; cases v; simp add: algebra_simps)

lemma det3_lincomb:
  "det3 (lincomb A B C u) (lincomb A B C v) (lincomb A B C w) = det3 A B C * det3 u v w"
  by (cases A; cases B; cases C) (cases u; cases v; cases w; simp add: algebra_simps)

lemma cross_cross_cofactor1:
  fixes A B C :: "'a::comm_ring vec3"
  shows "cross (cross C A) (cross A B) = scale3 (det3 A B C) A"
  by (cases A; cases B; cases C) (simp add: algebra_simps)

lemma cross_cross_cofactor2:
  fixes A B C :: "'a::comm_ring vec3"
  shows "cross (cross A B) (cross B C) = scale3 (det3 A B C) B"
  by (cases A; cases B; cases C) (simp add: algebra_simps)

lemma cross_cross_cofactor3:
  fixes A B C :: "'a::comm_ring vec3"
  shows "cross (cross B C) (cross C A) = scale3 (det3 A B C) C"
  by (cases A; cases B; cases C) (simp add: algebra_simps)

lemma cross_lincomb_cofactor:
  "cross (lincomb (cross B C) (cross C A) (cross A B) u)
         (lincomb (cross B C) (cross C A) (cross A B) v) =
     scale3 (det3 A B C) (lincomb A B C (cross u v))"
proof -
  have "cross (lincomb (cross B C) (cross C A) (cross A B) u)
              (lincomb (cross B C) (cross C A) (cross A B) v) =
        lincomb (cross (cross C A) (cross A B)) (cross (cross A B) (cross B C))
                (cross (cross B C) (cross C A)) (cross u v)"
    by (rule cross_lincomb)
  also have "\<dots> = lincomb (scale3 (det3 A B C) A) (scale3 (det3 A B C) B) (scale3 (det3 A B C) C)
                    (cross u v)"
    by (simp only: cross_cross_cofactor1[where A=A and B=B and C=C]
        cross_cross_cofactor2[where A=A and B=B and C=C]
        cross_cross_cofactor3[where A=A and B=B and C=C])
  also have "\<dots> = scale3 (det3 A B C) (lincomb A B C (cross u v))"
    by (rule lincomb_scale_columns)
  finally show ?thesis .
qed

lemma cramer:
  "lincomb A B C (det3 X B C, det3 A X C, det3 A B X) = scale3 (det3 A B C) X"
  by (cases A; cases B; cases C; cases X) (simp add: algebra_simps)

lemma lincomb_surj:
  fixes A B C X :: "'a::field vec3"
  assumes "det3 A B C \<noteq> 0"
  shows "\<exists>u. X = lincomb A B C u"
proof
  let ?k = "det3 A B C"
  show "X = lincomb A B C (scale3 (inverse ?k) (det3 X B C, det3 A X C, det3 A B X))"
    using assms by (simp only: lincomb_scale cramer scale_scale) simp
qed

subsection \<open>Conics\<close>

text \<open>
  A conic in the projective plane is the set of points \<open>(x, y, z)\<close> with
  \<open>q (x, y, z) = 0\<close>, where \<open>q\<close> is a non-zero \<^emph>\<open>ternary quadratic form\<close>
  \<open>q (x, y, z) = a x\<^sup>2 + b y\<^sup>2 + c z\<^sup>2 + d x y + e y z + f z x\<close>.
  We represent \<open>q\<close> by its coefficient vector \<open>(a, b, c, d, e, f)\<close>, and write
  \<^term>\<open>qf q X\<close> for the value of \<open>q\<close> at \<open>X\<close>.  Since \<open>q\<close> is homogeneous of degree 2, we
  have \<open>q (k X) = k\<^sup>2 q (X)\<close>, so whether a point lies on the conic does not depend on the
  vector chosen to represent it.  For example, the unit circle \<open>x\<^sup>2 + y\<^sup>2 = 1\<close> becomes
  \<open>x\<^sup>2 + y\<^sup>2 - z\<^sup>2 = 0\<close>, with coefficient vector \<open>(1, 1, -1, 0, 0, 0)\<close>.
\<close>

type_synonym 'a quadform = "'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a"

fun qf :: "'a::comm_ring quadform \<Rightarrow> 'a vec3 \<Rightarrow> 'a" where
  "qf (a, b, c, d, e, f) (x, y, z) = a * x * x + b * y * y + c * z * z + d * x * y + e * y * z + f * z * x"

text \<open>
  The \<^emph>\<open>polar form\<close> of \<open>q\<close> is the symmetric bilinear form
  \<open>polar q u v = q (u + v) - q (u) - q (v)\<close>, written out explicitly below.
\<close>

fun polar :: "'a::comm_ring_1 quadform \<Rightarrow> 'a vec3 \<Rightarrow> 'a vec3 \<Rightarrow> 'a" where
  "polar (a, b, c, d, e, f) (u1, u2, u3) (v1, v2, v3) =
     2 * a * u1 * v1 + 2 * b * u2 * v2 + 2 * c * u3 * v3 + d * (u1 * v2 + u2 * v1) +
     e * (u2 * v3 + u3 * v2) + f * (u3 * v1 + u1 * v3)"

lemma qf_lincomb:
  "qf q (lincomb A B C (x, y, z)) =
     qf q A * x * x + qf q B * y * y + qf q C * z * z +
     polar q A B * x * y + polar q B C * y * z + polar q C A * z * x"
  by (cases q; cases A; cases B; cases C) (simp add: algebra_simps)

lemma qf_eq_zero_imp:
  fixes q :: "'a::comm_ring_1 quadform"
  assumes "\<And>X. qf q X = 0"
  shows "q = (0, 0, 0, 0, 0, 0)"
proof -
  obtain a b c d e f where q: "q = (a, b, c, d, e, f)"
    by (cases q) auto
  have a: "a = 0" using assms[of "(1, 0, 0)"] by (simp add: q)
  have b: "b = 0" using assms[of "(0, 1, 0)"] by (simp add: q)
  have c: "c = 0" using assms[of "(0, 0, 1)"] by (simp add: q)
  have "d = 0" using assms[of "(1, 1, 0)"] by (simp add: q a b)
  moreover have "e = 0" using assms[of "(0, 1, 1)"] by (simp add: q b c)
  moreover have "f = 0" using assms[of "(1, 0, 1)"] by (simp add: q a c)
  ultimately show ?thesis by (simp add: q a b c)
qed

subsection \<open>The Pascal determinant\<close>

text \<open>
  Consider six points \<open>A\<close>, \<open>B\<close>, \<open>C\<close>, \<open>D\<close>, \<open>E\<close>, \<open>F\<close>, the vertices of the hexagon
  \<open>ABCDEF\<close>.  Its sides are \<open>AB\<close>, \<open>BC\<close>, \<open>CD\<close>, \<open>DE\<close>, \<open>EF\<close>, \<open>FA\<close>, and two sides are
  \<^emph>\<open>opposite\<close> if they are three steps apart in this cyclic order, giving the pairs
  \<open>AB, DE\<close>; \<open>BC, EF\<close> and \<open>CD, FA\<close>.  In homogeneous coordinates:
  \<^item> the line \<open>AB\<close> is \<open>A \<times> B\<close> and the line \<open>DE\<close> is \<open>D \<times> E\<close>;
  \<^item> their intersection point is \<open>(A \<times> B) \<times> (D \<times> E)\<close>, and similarly for the other two
    pairs;
  \<^item> three points are collinear iff the determinant of the matrix where each point
    is a column is 0.

  The \<^emph>\<open>Pascal determinant\<close> is this determinant applied to the intersection points,
  thus, it is 0 iff the intersection points are collinear (when these points are well defined).
\<close>

definition pascal_det :: "'a::comm_ring vec3 \<Rightarrow> 'a vec3 \<Rightarrow> 'a vec3 \<Rightarrow> 'a vec3 \<Rightarrow> 'a vec3 \<Rightarrow> 'a vec3 \<Rightarrow> 'a" where
  "pascal_det A B C D E F =
     det3 (cross (cross A B) (cross D E)) (cross (cross B C) (cross E F)) (cross (cross C D) (cross F A))"

lemma pascal_det_lincomb:
  fixes A B C :: "'a::comm_ring_1 vec3"
  shows "pascal_det (lincomb A B C a) (lincomb A B C b) (lincomb A B C c)
              (lincomb A B C d) (lincomb A B C e) (lincomb A B C f) =
         det3 A B C ^ 4 * pascal_det a b c d e f"
proof -
  have *: "cross (cross (lincomb A B C u) (lincomb A B C v))
                 (cross (lincomb A B C w) (lincomb A B C x)) =
           scale3 (det3 A B C) (lincomb A B C (cross (cross u v) (cross w x)))" for u v w x
    by (simp only: cross_lincomb[of A B C] cross_lincomb_cofactor)
  show ?thesis
    by (simp only: pascal_det_def * det3_scale det3_lincomb)
      (simp add: power4_eq_xxxx mult_ac)
qed

lemma pascal_det_basis:
  fixes d1 :: "'a::idom"
  shows "pascal_det (1, 0, 0) (0, 1, 0) (0, 0, 1) (d1, d2, d3) (e1, e2, e3) (f1, f2, f3) =
     - det3 (d1 * d2, d2 * d3, d3 * d1) (e1 * e2, e2 * e3, e3 * e1) (f1 * f2, f2 * f3, f3 * f1)"
  by (simp add: pascal_det_def algebra_simps)

lemma det3_kernel:
  fixes X Y Z w :: "'a::idom vec3"
  assumes "dot X w = 0" "dot Y w = 0" "dot Z w = 0" "w \<noteq> (0, 0, 0)"
  shows "det3 X Y Z = 0"
proof -
  obtain w1 w2 w3 where w: "w = (w1, w2, w3)" by (cases w) auto
  have "scale3 (det3 X Y Z) w =
          lincomb (cross Y Z) (cross Z X) (cross X Y) (dot X w, dot Y w, dot Z w)"
    by (cases X; cases Y; cases Z) (simp add: w algebra_simps)
  also have "\<dots> = (0, 0, 0)"
    using assms by (cases X; cases Y; cases Z) simp
  finally show ?thesis
    using assms(4) by (auto simp: w)
qed

subsection \<open>Vanishing of the Pascal determinant\<close>

text \<open>
  \<^bold>\<open>The core lemma.\<close>  Let \<open>q\<close> be a non-zero quadratic form vanishing at
  \<open>A\<close>, \<open>B\<close>, \<open>C\<close>, \<open>D\<close>, \<open>E\<close>, \<open>F\<close>, and suppose \<open>A\<close>, \<open>B\<close>, \<open>C\<close> are not collinear,
  i.e.\ \<open>det (A, B, C) \<noteq> 0\<close>.  Then the Pascal determinant of the six points is \<open>0\<close>.
\<close>

lemma pascal_det_eq_0:
  fixes A B C D E F :: "'a::field vec3"
  assumes q: "q \<noteq> (0, 0, 0, 0, 0, 0)"
    and on: "qf q A = 0" "qf q B = 0" "qf q C = 0" "qf q D = 0" "qf q E = 0" "qf q F = 0"
    and ABC: "det3 A B C \<noteq> 0"
  shows "pascal_det A B C D E F = 0"
proof -
  obtain d where d: "D = lincomb A B C d" using lincomb_surj[OF ABC] by blast
  obtain e where e: "E = lincomb A B C e" using lincomb_surj[OF ABC] by blast
  obtain f where f: "F = lincomb A B C f" using lincomb_surj[OF ABC] by blast
  obtain d1 d2 d3 where d': "d = (d1, d2, d3)" by (cases d) auto
  obtain e1 e2 e3 where e': "e = (e1, e2, e3)" by (cases e) auto
  obtain f1 f2 f3 where f': "f = (f1, f2, f3)" by (cases f) auto
  define w where "w = (polar q A B, polar q B C, polar q C A)"
  have qf_simp: "qf q (lincomb A B C (x, y, z)) = dot (x * y, y * z, z * x) w" for x y z
    by (simp add: qf_lincomb on w_def algebra_simps)
  have "w \<noteq> (0, 0, 0)"
  proof
    assume w0: "w = (0, 0, 0)"
    have "qf q X = 0" for X
    proof -
      obtain u where u: "X = lincomb A B C u" using lincomb_surj[OF ABC] by blast
      show ?thesis by (cases u) (simp add: u qf_simp w0)
    qed
    then show False using q qf_eq_zero_imp by blast
  qed
  moreover have "dot (d1 * d2, d2 * d3, d3 * d1) w = 0"
    using on(4) by (simp add: d d' qf_simp)
  moreover have "dot (e1 * e2, e2 * e3, e3 * e1) w = 0"
    using on(5) by (simp add: e e' qf_simp)
  moreover have "dot (f1 * f2, f2 * f3, f3 * f1) w = 0"
    using on(6) by (simp add: f f' qf_simp)
  ultimately have "det3 (d1 * d2, d2 * d3, d3 * d1) (e1 * e2, e2 * e3, e3 * e1)
                        (f1 * f2, f2 * f3, f3 * f1) = 0"
    by (intro det3_kernel[of _ w]) auto
  then have "pascal_det (1, 0, 0) (0, 1, 0) (0, 0, 1) d e f = 0"
    by (simp only: d' e' f' pascal_det_basis) simp
  then have "pascal_det (lincomb A B C (1, 0, 0)) (lincomb A B C (0, 1, 0)) (lincomb A B C (0, 0, 1))
               (lincomb A B C d) (lincomb A B C e) (lincomb A B C f) = 0"
    by (simp only: pascal_det_lincomb) simp
  then show ?thesis by (simp add: d e f)
qed

subsection \<open>Lines and their intersections\<close>

text \<open>
  To turn the core lemma into a statement about points \<open>P\<close>, \<open>Q\<close>, \<open>R\<close>, we require
  the below properties.
\<close>

lemma dot_scale: "dot X (scale3 k Y) = k * dot X Y"
  by (cases X; cases Y) (simp add: algebra_simps)

lemma dot_zero [simp]: "dot X (0, 0, 0) = 0"
  by (cases X) simp

lemma det3_eq_dot_cross': "det3 A B C = dot C (cross A B)"
  by (cases A; cases B; cases C) (simp add: algebra_simps)

lemma det3_scale3: "det3 (scale3 a X) (scale3 b Y) (scale3 c Z) = a * b * c * det3 X Y Z"
  by (cases X; cases Y; cases Z) (simp add: algebra_simps)

lemma cross_cross_eq_0:
  assumes "dot X l = 0" "dot X m = 0"
  shows "cross (cross l m) X = (0, 0, 0)"
proof -
  obtain l1 l2 l3 where l: "l = (l1, l2, l3)" by (cases l) auto
  obtain m1 m2 m3 where m: "m = (m1, m2, m3)" by (cases m) auto
  have "cross (cross l m) X = (m1 * dot X l - l1 * dot X m, m2 * dot X l - l2 * dot X m,
                               m3 * dot X l - l3 * dot X m)"
    by (cases X) (simp add: l m algebra_simps)
  then show ?thesis using assms by simp
qed

lemma cross_eq_0_imp_scale:
  fixes u v :: "'a::field vec3"
  assumes "cross u v = (0, 0, 0)" "u \<noteq> (0, 0, 0)"
  shows "\<exists>k. v = scale3 k u"
proof -
  obtain u1 u2 u3 where u: "u = (u1, u2, u3)" by (cases u) auto
  obtain v1 v2 v3 where v: "v = (v1, v2, v3)" by (cases v) auto
  have h: "u2 * v3 = u3 * v2" "u3 * v1 = u1 * v3" "u1 * v2 = u2 * v1"
    using assms(1) by (simp_all add: u v)
  consider "u1 \<noteq> 0" | "u2 \<noteq> 0" | "u3 \<noteq> 0" using assms(2) u by auto
  then show ?thesis
  proof cases
    case 1
    have "v = scale3 (v1 / u1) u"
      using 1 h by (simp add: u v field_simps)
    then show ?thesis ..
  next
    case 2
    have "v = scale3 (v2 / u2) u"
      using 2 h by (simp add: u v field_simps)
    then show ?thesis ..
  next
    case 3
    have "v = scale3 (v3 / u3) u"
      using 3 h by (simp add: u v field_simps)
    then show ?thesis ..
  qed
qed

lemma intersection_scale:
  fixes P l m :: "'a::field vec3"
  assumes "dot P l = 0" "dot P m = 0" "cross l m \<noteq> (0, 0, 0)"
  shows "\<exists>k. P = scale3 k (cross l m)"
  using cross_eq_0_imp_scale[OF cross_cross_eq_0[OF assms(1,2)] assms(3)] .

lemma det3_ne_0_cross:
  assumes "det3 X D E \<noteq> 0"
  shows "cross D E \<noteq> (0, 0, 0)"
  using assms by (auto simp: det3_eq_dot_cross)

lemma lines_distinct:
  fixes A B D E :: "'a::field vec3"
  assumes "det3 A B D \<noteq> 0" "cross D E \<noteq> (0, 0, 0)"
  shows "cross (cross A B) (cross D E) \<noteq> (0, 0, 0)"
proof
  assume h: "cross (cross A B) (cross D E) = (0, 0, 0)"
  have dAB: "det3 A B D = dot D (cross A B)"
    by (rule det3_eq_dot_cross')
  then have "cross A B \<noteq> (0, 0, 0)"
    using assms(1) by auto
  then obtain k where k: "cross D E = scale3 k (cross A B)"
    using cross_eq_0_imp_scale[OF h] by blast
  have "0 = dot D (cross D E)"
    by simp
  also have "\<dots> = k * dot D (cross A B)"
    by (simp add: k dot_scale)
  finally have "k = 0"
    using assms(1) dAB by simp
  then show False
    using assms(2) k by (cases "cross A B") simp
qed

subsection \<open>Hexagons inscribed in a conic\<close>

lemma hexagon_opposite_sides_distinct:
  fixes A B C D E F :: "'a::field vec3"
  assumes ABD: "det3 A B D \<noteq> 0" and ADE: "det3 A D E \<noteq> 0"
    and BCE: "det3 B C E \<noteq> 0" and AEF: "det3 A E F \<noteq> 0"
    and CDF: "det3 C D F \<noteq> 0" and BFA: "det3 B F A \<noteq> 0"
  shows "cross (cross A B) (cross D E) \<noteq> (0, 0, 0)"
    and "cross (cross B C) (cross E F) \<noteq> (0, 0, 0)"
    and "cross (cross C D) (cross F A) \<noteq> (0, 0, 0)"
  using lines_distinct[OF ABD det3_ne_0_cross[OF ADE]]
    lines_distinct[OF BCE det3_ne_0_cross[OF AEF]]
    lines_distinct[OF CDF det3_ne_0_cross[OF BFA]]
  by simp_all

text \<open>
  \<^bold>\<open>Pascal's theorem in the projective plane.\<close>  Let \<open>A\<close>, \<open>\<dots>\<close>, \<open>F\<close> be six points on
  the conic \<open>q = 0\<close>, where \<open>q\<close> is a non-zero quadratic form, such that \<open>A\<close>, \<open>B\<close>, \<open>C\<close>
  are not collinear (needed by the core lemma) and the six non-collinearity conditions of
  \<open>hexagon_opposite_sides_distinct\<close> hold. Suppose \<open>P\<close> lies on the lines \<open>AB\<close> and \<open>DE\<close>,
  \<open>Q\<close> lies on \<open>BC\<close> and \<open>EF\<close>, and \<open>R\<close> lies on \<open>CD\<close> and \<open>FA\<close>.  Then \<open>P\<close>, \<open>Q\<close> and
  \<open>R\<close> are collinear.

  We encode "\<open>P\<close> lies on the line \<open>AB\<close>" as \<^term>\<open>det3 A B P = 0\<close>,
  i.e.\ \<open>A\<close>, \<open>B\<close>, \<open>P\<close> are collinear, and the conclusion "\<open>P\<close>, \<open>Q\<close>, \<open>R\<close> are collinear"
  as \<^term>\<open>det3 P Q R = 0\<close>.
\<close>

lemma projective_hexagon:
  fixes A B C D E F P Q R :: "'a::field vec3"
  assumes q: "q \<noteq> (0, 0, 0, 0, 0, 0)"
    and on: "qf q A = 0" "qf q B = 0" "qf q C = 0" "qf q D = 0" "qf q E = 0" "qf q F = 0"
    and ABC: "det3 A B C \<noteq> 0"
    and nc: "det3 A B D \<noteq> 0" "det3 A D E \<noteq> 0" "det3 B C E \<noteq> 0"
            "det3 A E F \<noteq> 0" "det3 C D F \<noteq> 0" "det3 B F A \<noteq> 0"
    and P: "det3 A B P = 0" "det3 D E P = 0"
    and Q: "det3 B C Q = 0" "det3 E F Q = 0"
    and R: "det3 C D R = 0" "det3 F A R = 0"
  shows "det3 P Q R = 0"
proof -
  note l1 = hexagon_opposite_sides_distinct(1)[OF nc]
  note l2 = hexagon_opposite_sides_distinct(2)[OF nc]
  note l3 = hexagon_opposite_sides_distinct(3)[OF nc]
  obtain kP where kP: "P = scale3 kP (cross (cross A B) (cross D E))"
    using intersection_scale[OF _ _ l1] P by (metis det3_eq_dot_cross')
  obtain kQ where kQ: "Q = scale3 kQ (cross (cross B C) (cross E F))"
    using intersection_scale[OF _ _ l2] Q by (metis det3_eq_dot_cross')
  obtain kR where kR: "R = scale3 kR (cross (cross C D) (cross F A))"
    using intersection_scale[OF _ _ l3] R by (metis det3_eq_dot_cross')
  have "det3 P Q R = kP * kQ * kR * pascal_det A B C D E F"
    by (simp only: kP kQ kR det3_scale3 pascal_det_def)
  also have "\<dots> = 0"
    using pascal_det_eq_0[OF q on ABC] by simp
  finally show ?thesis .
qed

subsection \<open>Non-degenerate conics\<close>

text \<open>
  Some conics are \<^emph>\<open>degenerate\<close>: for example \<open>x y = 0\<close> is a pair of lines and
  \<open>x\<^sup>2 = 0\<close> is a double line.  Algebraically, write the polar form as a matrix product:
  \<open>polar q u v = u\<^sup>T M v\<close>, where \<open>M\<close> is the symmetric matrix with columns
  \<open>(2a, d, f)\<close>, \<open>(d, 2b, e)\<close>, \<open>(f, e, 2c)\<close>, computed by \<open>qmatrix\<close>. The form \<open>q\<close> is
  \<^emph>\<open>non-degenerate\<close> if \<open>det M \<noteq> 0\<close>.  In characteristic 2 the diagonal entries of \<open>M\<close>
  vanish and \<open>det M = 2 d e f = 0\<close>, so no form is non-degenerate in this sense and the theorem
  below is vacuous there; we only apply it over \<open>\<real>\<close>.
\<close>

fun qmatrix :: "'a::comm_ring_1 quadform \<Rightarrow> 'a vec3 \<times> 'a vec3 \<times> 'a vec3" where
  "qmatrix (a, b, c, d, e, f) = ((2 * a, d, f), (d, 2 * b, e), (f, e, 2 * c))"

definition nondegenerate :: "'a::comm_ring_1 quadform \<Rightarrow> bool" where
  "nondegenerate q \<longleftrightarrow> (case qmatrix q of (M1, M2, M3) \<Rightarrow> det3 M1 M2 M3 \<noteq> 0)"

lemma polar_eq_dot:
  "polar q u v = (case qmatrix q of (M1, M2, M3) \<Rightarrow> dot u (lincomb M1 M2 M3 v))"
  by (cases q; cases u; cases v) (simp add: algebra_simps)

lemma polar_comm: "polar q u v = polar q v u"
  by (cases q; cases u; cases v) (simp add: algebra_simps)

lemma polar_self: "polar q u u = 2 * qf q u"
  by (cases q; cases u) (simp add: algebra_simps)

lemma det3_dot_rows:
  "det3 (dot X U, dot X V, dot X W) (dot Y U, dot Y V, dot Y W) (dot Z U, dot Z V, dot Z W) =
     det3 X Y Z * det3 U V W"
  by (cases X; cases Y; cases Z) (cases U; cases V; cases W; simp add: algebra_simps)

lemma det3_gram:
  "det3 (polar q X X, polar q X Y, polar q X W) (polar q Y X, polar q Y Y, polar q Y W)
        (polar q W X, polar q W Y, polar q W W) =
   det3 X Y W * det3 X Y W * (case qmatrix q of (M1, M2, M3) \<Rightarrow> det3 M1 M2 M3)"
proof -
  obtain M1 M2 M3 where M: "qmatrix q = (M1, M2, M3)" by (cases "qmatrix q") auto
  show ?thesis
    by (simp only: polar_eq_dot M prod.case det3_dot_rows det3_lincomb) (simp add: algebra_simps)
qed

lemma det3_basis_vector:
  fixes X Y :: "'a::field vec3"
  assumes "cross X Y \<noteq> (0, 0, 0)"
  shows "\<exists>W. det3 X Y W \<noteq> 0"
proof -
  obtain c1 c2 c3 where c: "cross X Y = (c1, c2, c3)" by (cases "cross X Y") auto
  have "det3 X Y W = dot W (cross X Y)" for W by (rule det3_eq_dot_cross')
  then have "det3 X Y (1, 0, 0) = c1" "det3 X Y (0, 1, 0) = c2" "det3 X Y (0, 0, 1) = c3"
    by (simp_all add: c)
  then show ?thesis using assms c by (metis)
qed

text \<open>
  A line meets a non-degenerate conic in at most two points. Equivalently: three
  pairwise distinct points \<open>X\<close>, \<open>Y\<close>, \<open>Z\<close> on a non-degenerate conic are not collinear.
  Distinctness of the points is expressed by non-vanishing cross products.
\<close>

theorem nondegenerate_no_three_collinear:
  fixes X Y Z :: "'a::field vec3"
  assumes nd: "nondegenerate q"
    and on: "qf q X = 0" "qf q Y = 0" "qf q Z = 0"
    and distinct: "cross X Y \<noteq> (0, 0, 0)" "cross X Z \<noteq> (0, 0, 0)" "cross Y Z \<noteq> (0, 0, 0)"
  shows "det3 X Y Z \<noteq> 0"
proof
  assume col: "det3 X Y Z = 0"
  obtain W where W: "det3 X Y W \<noteq> 0" using det3_basis_vector[OF distinct(1)] by blast
  obtain z where z: "Z = lincomb X Y W z" using lincomb_surj[OF W] by blast
  obtain z1 z2 z3 where z': "z = (z1, z2, z3)" by (cases z) auto
  have "det3 X Y Z = det3 X Y W * z3"
    by (cases X; cases Y; cases W) (simp add: z z' algebra_simps)
  then have z3: "z3 = 0" using col W by simp
  have "cross X Z = scale3 z2 (cross X Y)"
    by (cases X; cases Y; cases W) (simp add: z z' z3 algebra_simps)
  then have "z2 \<noteq> 0" using distinct(2) by (cases "cross X Y") auto
  have "cross Y Z = scale3 z1 (cross Y X)"
    by (cases X; cases Y; cases W) (simp add: z z' z3 algebra_simps)
  then have "z1 \<noteq> 0" using distinct(3) by (cases "cross Y X") auto
  have "qf q Z = polar q X Y * z1 * z2"
    by (simp add: z z' z3 qf_lincomb on)
  then have XY: "polar q X Y = 0"
    using on(3) \<open>z1 \<noteq> 0\<close> \<open>z2 \<noteq> 0\<close> by simp
  have "det3 (polar q X X, polar q X Y, polar q X W) (polar q Y X, polar q Y Y, polar q Y W)
             (polar q W X, polar q W Y, polar q W W) = 0"
    by (simp add: polar_self on XY polar_comm[of q Y X])
  then have "det3 X Y W * det3 X Y W * (case qmatrix q of (M1, M2, M3) \<Rightarrow> det3 M1 M2 M3) = 0"
    by (simp only: det3_gram)
  then show False
    using W nd by (auto simp: nondegenerate_def split: prod.splits)
qed

end
