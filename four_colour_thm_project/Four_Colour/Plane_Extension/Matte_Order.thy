(* Corner order from matte.v. Original G. Gonthier et al., CeCILL-B.
   Isabelle/HOL port: Codex. *)
theory Matte_Order
  imports Four_Colour_Plane_Geometry.Matte
begin

definition mcorner :: "matte \<Rightarrow> gpoint \<Rightarrow> nat" where
  "mcorner m q = (if q-(1,1)\<in>set (mdisk m) then 0 else 1) +
    2 * ((if q-(0,1)\<in>set (mdisk m) then 0 else 1) +
         (if q-(1,0)\<in>set (mdisk m) then 0 else 1))"

lemma ltouch_enumeration:
  "grect_set (ltouch q) = {q-(1,1),q-(0,1),q-(1,0),q}"
proof -
  have interval: "{x-1..<x+1} = {x-1,x}" for x :: int
    by (auto; presburger)
  show ?thesis by (cases q) (simp add: interval insert_commute)
qed

lemma mcorner0:
  assumes "q\<in>set (mdisk m)" "mcorner m q=0"
  shows "grect_set (ltouch q) \<subseteq> set (mdisk m)"
  using assms by (auto simp: mcorner_def ltouch_enumeration split: if_splits)

lemma mcorner_bound: "mcorner m q \<le> 5"
  by (auto simp: mcorner_def split: if_splits)

lemma mcorner_mono:
  assumes "set (mdisk m) \<subseteq> set (mdisk n)"
  shows "mcorner n q \<le> mcorner m q"
  using assms by (auto simp: mcorner_def split: if_splits)

lemma halfg_sub_corner:
  "halfg (q-c) = halfg q + halfg (oddg q-c)"
proof -
  have "halfg (q-c) = halfg (q + (-c))" by simp
  also have "\<dots> = halfg q + halfg ((-c) + oddg q)" by (rule halfg_add)
  also have "\<dots> = halfg q + halfg (oddg q-c)" by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma mcorner_refine_nonzero:
  assumes parity: "oddg q\<noteq>0" and at: "halfg q\<in>set (mdisk m)"
    and pos: "0 < mcorner m (halfg q)"
    and sub: "{p. halfg p\<in>set (mdisk m)} \<subseteq> set (mdisk n)"
    and gain: "q-ccw (ccw (oddg q))\<in>set (mdisk n)"
  shows "mcorner n q < mcorner m (halfg q)"
proof -
  have transfer: "halfg (q-c)\<in>set (mdisk m) \<Longrightarrow> q-c\<in>set (mdisk n)" for c
    using sub by auto
  have cases: "oddg q=(0,1) \<or> oddg q=(1,1) \<or> oddg q=(1,0)"
    using parity oddg_corners[of q] by (auto simp: gcorners_def)
  show ?thesis using cases
  proof (elim disjE)
    assume parity: "oddg q=(0,1)"
    have hdiag: "halfg (q-(1,1))=halfg q-(1,0)"
      by (simp only: halfg_sub_corner[of q "(1,1)"])
        (simp add: parity halfg_def)
    have hside: "halfg (q-(0,1))=halfg q"
      by (simp only: halfg_sub_corner[of q "(0,1)"])
        (simp add: parity halfg_def)
    have side1: "q-(0,1)\<in>set (mdisk n)" by (rule transfer) (simp only: hside at)
    have side2: "q-(1,0)\<in>set (mdisk n)" using gain by (simp add: parity ccw_def)
    have diag: "halfg q-(1,0)\<in>set (mdisk m) \<Longrightarrow> q-(1,1)\<in>set (mdisk n)"
      by (rule transfer) (simp only: hdiag)
    show ?thesis using pos side1 side2 diag
      by (auto simp: mcorner_def split: if_splits)
  next
    assume parity: "oddg q=(1,1)"
    have h: "halfg (q-(1,1))=halfg q" "halfg (q-(0,1))=halfg q" "halfg (q-(1,0))=halfg q"
      by (simp only: halfg_sub_corner[of q "(1,1)"] halfg_sub_corner[of q "(0,1)"]
          halfg_sub_corner[of q "(1,0)"]; simp add: parity halfg_def)+
    have sides: "q-(1,1)\<in>set (mdisk n)" "q-(0,1)\<in>set (mdisk n)" "q-(1,0)\<in>set (mdisk n)"
      by (rule transfer; simp only: h at)+
    show ?thesis using pos sides by (simp add: mcorner_def)
  next
    assume parity: "oddg q=(1,0)"
    have hdiag: "halfg (q-(1,1))=halfg q-(0,1)"
      by (simp only: halfg_sub_corner[of q "(1,1)"])
        (simp add: parity halfg_def)
    have hside: "halfg (q-(1,0))=halfg q"
      by (simp only: halfg_sub_corner[of q "(1,0)"])
        (simp add: parity halfg_def)
    have side1: "q-(1,0)\<in>set (mdisk n)" by (rule transfer) (simp only: hside at)
    have side2: "q-(0,1)\<in>set (mdisk n)" using gain by (simp add: parity ccw_def)
    have diag: "halfg q-(0,1)\<in>set (mdisk m) \<Longrightarrow> q-(1,1)\<in>set (mdisk n)"
      by (rule transfer) (simp only: hdiag)
    show ?thesis using pos side1 side2 diag
      by (auto simp: mcorner_def split: if_splits)
  qed
qed

lemma mcorner_refine_zero:
  assumes parity: "oddg q=0" and corner: "c\<in>gcorners" "c\<noteq>0"
    and missing: "halfg q-c\<notin>set (mdisk m)"
    and sub: "{p. halfg p\<in>set (mdisk m)} \<subseteq> set (mdisk n)"
    and gain: "q-c\<in>set (mdisk n)"
  shows "mcorner n q < mcorner m (halfg q)"
proof -
  have transfer: "halfg (q-d)\<in>set (mdisk m) \<Longrightarrow> q-d\<in>set (mdisk n)" for d
    using sub by auto
  have cases: "c=(0,1) \<or> c=(1,1) \<or> c=(1,0)"
    using corner by (auto simp: gcorners_def)
  have h: "halfg (q-(1,1))=halfg q-(1,1)"
    "halfg (q-(0,1))=halfg q-(0,1)" "halfg (q-(1,0))=halfg q-(1,0)"
    by (simp only: halfg_sub_corner[of q "(1,1)"] halfg_sub_corner[of q "(0,1)"]
        halfg_sub_corner[of q "(1,0)"]; simp add: parity halfg_def)+
  show ?thesis
    using cases missing gain transfer[of "(1,1)"] transfer[of "(0,1)"] transfer[of "(1,0)"]
    by (simp only: h; elim disjE; auto simp: mcorner_def split: if_splits)
qed

end
