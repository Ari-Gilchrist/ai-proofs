(* Grid mattes from matte.v. Original G. Gonthier et al., CeCILL-B.
   Isabelle port: Codex. Record invariants are explicit in valid_matte. *)
theory Matte
  imports Four_Colour_Plane_Maps.Grid_Rectangles
begin

definition mrlink :: "gpoint \<Rightarrow> gpoint \<Rightarrow> bool" where
  "mrlink d e \<longleftrightarrow> end1g d = end0g e"
definition gborder :: "gpoint set \<Rightarrow> gpoint set" where
  "gborder A = {d. halfg d \<in> A \<and> halfg (gedge d) \<notin> A}"

fun grid_path :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "grid_path r x [] = True"
| "grid_path r x (y#ys) = (r x y \<and> grid_path r y ys)"
definition grid_cycle :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "grid_cycle r xs \<longleftrightarrow> (case xs of [] \<Rightarrow> True | x#ys \<Rightarrow> grid_path r x (ys@[x]))"

record matte =
  mdisk :: "gpoint list"
  mring :: "gpoint list"

definition valid_matte :: "matte \<Rightarrow> bool" where
  "valid_matte m \<longleftrightarrow> mdisk m \<noteq> [] \<and> grid_cycle mrlink (mring m) \<and>
     distinct (map end0g (mring m)) \<and> set (mring m) = gborder (set (mdisk m))"

lemma mring_cycle: "valid_matte m \<Longrightarrow> grid_cycle mrlink (mring m)"
  by (simp add: valid_matte_def)
lemma mring_simple: "valid_matte m \<Longrightarrow> distinct (map end0g (mring m))"
  by (simp add: valid_matte_def)
lemma in_mring: "valid_matte m \<Longrightarrow> set (mring m) = gborder (set (mdisk m))"
  by (simp add: valid_matte_def)
lemma matte_ne: "valid_matte m \<Longrightarrow> mdisk m \<noteq> []"
  by (simp add: valid_matte_def)
lemma mring_edge:
  "valid_matte m \<Longrightarrow> d \<in> set (mring m) \<Longrightarrow> gedge d \<notin> set (mring m)"
  by (auto simp: in_mring gborder_def)
lemma mring_uniq: "valid_matte m \<Longrightarrow> distinct (mring m)"
  by (meson mring_simple distinct_map)

definition madj :: "matte \<Rightarrow> matte \<Rightarrow> bool" where
  "madj m n \<longleftrightarrow> (\<exists>d\<in>set (mring n). gedge d \<in> set (mring m))"
lemma madj_sym: "madj m n \<longleftrightarrow> madj n m"
  unfolding madj_def by (metis gedge2)
lemma madj_irrefl: "valid_matte m \<Longrightarrow> \<not>madj m m"
  by (auto simp: madj_def dest: mring_edge)

definition pmring :: "gpoint \<Rightarrow> gpoint list" where
  "pmring p = [doubleg p, gface (doubleg p), gface (gface (doubleg p)),
      gface (gface (gface (doubleg p)))]"
definition point_matte :: "gpoint \<Rightarrow> matte" where
  "point_matte p = \<lparr>mdisk=[p], mring=pmring p\<rparr>"

lemma in_pmring: "d \<in> set (pmring p) \<longleftrightarrow> halfg d=p"
proof
  assume "d \<in> set (pmring p)"
  then show "halfg d=p" by (auto simp: pmring_def)
next
  assume h: "halfg d=p"
  have "d\<in>set [doubleg p, gface (doubleg p), gface (gface (doubleg p)),
      gface (gface (gface (doubleg p))) ]" by (rule same_halfg) (simp add: h)
  then show "d\<in>set (pmring p)" by (simp add: pmring_def)
qed

lemma pmring_cycle: "grid_cycle mrlink (pmring p)"
  by (simp add: grid_cycle_def pmring_def mrlink_def end0g_face[symmetric] gface4)
lemma pmring_simple: "distinct (map end0g (pmring p))"
  by (simp only: pmring_def list.map end0g_def halfg_face oddg_face halfg_double oddg_double;
      cases p; simp add: ccw_def)
lemma pmring_border: "set (pmring p) = gborder {p}"
  using neq_halfg_edge by (auto simp: in_pmring gborder_def)
lemma point_matte_valid: "valid_matte (point_matte p)"
  by (simp add: valid_matte_def point_matte_def pmring_cycle pmring_simple pmring_border)

definition coarse_in :: "gpoint set \<Rightarrow> matte \<Rightarrow> bool" where
  "coarse_in A m \<longleftrightarrow> (\<forall>p\<in>A. \<forall>q. halfg q=halfg p \<longrightarrow>
       (q\<in>set (mdisk m) \<longleftrightarrow> p\<in>set (mdisk m)))"
definition refine_mdisk :: "gpoint list \<Rightarrow> gpoint list" where
  "refine_mdisk ps = concat (map pmring ps)"
definition refine_mring :: "gpoint list \<Rightarrow> gpoint list" where
  "refine_mring ds = concat (map (\<lambda>d. [doubleg d + oddg d, doubleg (gface d) + oddg d]) ds)"

lemma in_refine_mdisk: "p\<in>set (refine_mdisk ps) \<longleftrightarrow> halfg p\<in>set ps"
  by (auto simp: refine_mdisk_def in_pmring)
lemma refine_mdisk_ne: "ps\<noteq>[] \<Longrightarrow> refine_mdisk ps\<noteq>[]"
  by (cases ps) (auto simp: refine_mdisk_def pmring_def)
lemma in_refine_mring:
  "d\<in>set (refine_mring ds) \<longleftrightarrow>
    (\<exists>e\<in>set ds. oddg d= oddg e \<and> (halfg d=e \<or> halfg d=gface e))"
proof -
  have recon: "d=doubleg (halfg d) + oddg d" using halfgK[of d] by simp
  show ?thesis using oddg_corners[of d] recon
    by (auto simp: refine_mring_def oddg_corners)
qed

definition refine_dart0 :: "gpoint \<Rightarrow> gpoint" where
  "refine_dart0 d = doubleg d + oddg d"
definition refine_dart1 :: "gpoint \<Rightarrow> gpoint" where
  "refine_dart1 d = doubleg (gface d) + oddg d"

lemma refine_mring_Cons [simp]:
  "refine_mring (d#ds) = refine_dart0 d # refine_dart1 d # refine_mring ds"
  by (simp add: refine_mring_def refine_dart0_def refine_dart1_def)
lemma refine_mring_Nil [simp]: "refine_mring [] = []"
  by (simp add: refine_mring_def)

lemma end0g_refine0: "end0g (refine_dart0 d) = doubleg (end0g d)"
  by (cases d) (auto simp: refine_dart0_def end0g_def halfg_def oddg_def doubleg_def; presburger)
lemma end0g_refine1: "end0g (refine_dart1 d) = end1g (refine_dart0 d)"
  by (cases d) (auto simp: refine_dart0_def refine_dart1_def end0g_def end1g_def
    gface_unlocked halfg_def oddg_def doubleg_def arcg_def ccw_def; presburger)
lemma end1g_refine1: "end1g (refine_dart1 d) = doubleg (end1g d)"
  by (simp only: refine_dart1_def end1g_def halfg_add2 oddg_add2
      halfg_odd[OF oddg_corners] oddg_id[OF oddg_corners] add_0_right;
      simp add: gface_def doubleg_def algebra_simps)
lemma doubleg_inj: "doubleg p = doubleg q \<longleftrightarrow> p=q"
  by (cases p; cases q) (auto simp: doubleg_def)
lemma mrlink_refine01 [simp]: "mrlink (refine_dart0 d) (refine_dart1 d)"
  by (simp add: mrlink_def end0g_refine1)
lemma mrlink_refine10 [simp]:
  "mrlink (refine_dart1 d) (refine_dart0 e) \<longleftrightarrow> mrlink d e"
  by (simp add: mrlink_def end1g_refine1 end0g_refine0 doubleg_inj)
lemma refine_mring_path:
  "grid_path mrlink (refine_dart1 d) (refine_mring ds @ [refine_dart0 e]) =
    grid_path mrlink d (ds@[e])"
  by (induction ds arbitrary: d) simp_all
lemma refine_mring_cycle:
  "grid_cycle mrlink (refine_mring ds) \<longleftrightarrow> grid_cycle mrlink ds"
  by (cases ds) (simp_all add: grid_cycle_def refine_mring_path)

lemma end0g_refine1_midpoint: "end0g (refine_dart1 d) = d + ccw (oddg d)"
  by (simp only: refine_dart1_def end0g_def halfg_add2 oddg_add2
      halfg_odd[OF oddg_corners] oddg_id[OF oddg_corners] add_0_right;
      simp add: gface_unlocked arcg_def algebra_simps)
lemma refine_vertex_midpoint:
  "end0g (refine_dart0 d) \<noteq> end0g (refine_dart1 e)"
proof -
  have odd: "oddg (e + ccw (oddg e)) \<noteq> 0"
    using oddg_corners[of e]
    by (auto simp: oddg_add gcorners_def ccw_def oddg_def prod_eq_iff)
  show ?thesis using odd
    by (metis end0g_refine0 end0g_refine1_midpoint oddg_double)
qed

lemma oddg_midpoint:
  "oddg (d + ccw (oddg d)) = oddg (ccw (oddg d) + oddg d)"
  by (rule oddg_add)

lemma midpoint_corner_parity:
  "c\<in>gcorners \<Longrightarrow> b\<in>gcorners \<Longrightarrow> oddg (ccw c+c)= oddg (ccw b+b) \<Longrightarrow>
    c=b \<or> c=ccw (ccw b)"
  by (auto simp: gcorners_def ccw_def oddg_def)

lemma refine_midpoint_eq:
  "end0g (refine_dart1 d) = end0g (refine_dart1 e) \<longleftrightarrow> d=e \<or> d=gedge e"
proof
  assume h: "end0g (refine_dart1 d) = end0g (refine_dart1 e)"
  have eq: "d + ccw (oddg d) = e + ccw (oddg e)" using h by (simp only: end0g_refine1_midpoint)
  have par: "oddg (ccw (oddg d) + oddg d) = oddg (ccw (oddg e) + oddg e)"
    using arg_cong[OF eq, of oddg] by (simp only: oddg_midpoint)
  have c: "oddg d= oddg e \<or> oddg d=ccw (ccw (oddg e))"
    by (rule midpoint_corner_parity[OF oddg_corners oddg_corners par])
  show "d=e \<or> d=gedge e"
  proof (cases "oddg d= oddg e")
    case True then have "d=e" using eq by simp
    then show ?thesis by simp
  next
    case False
    have c': "oddg d=ccw (ccw (oddg e))" using c False by blast
    have eq': "d + ccw (ccw (ccw (oddg e))) = e + ccw (oddg e)"
      using eq by (simp only: c')
    have "d=gedge e" using eq'
      by (auto simp: gedge_unlocked arcg_def ccw_def prod_eq_iff; linarith)
    then show ?thesis by simp
  qed
next
  assume h: "d=e \<or> d=gedge e"
  show "end0g (refine_dart1 d) = end0g (refine_dart1 e)"
  proof (cases "d=e")
    case True then show ?thesis by simp
  next
    case False
    have de: "d=gedge e" using h False by blast
    show ?thesis
      by (simp only: de end0g_refine1_midpoint oddg_edge;
        simp add: gedge_unlocked arcg_def ccw_def algebra_simps prod_eq_iff)
  qed
qed

lemma grid_path_append [simp]:
  "grid_path r x (xs@ys) \<longleftrightarrow> grid_path r x xs \<and> grid_path r (last (x#xs)) ys"
  by (induction xs arbitrary: x) auto

lemma refine_mring_simple_aux:
  assumes simple: "distinct (map end0g ds)"
    and converse: "\<And>d. d\<in>set ds \<Longrightarrow> gedge d\<notin>set ds"
  shows "distinct (map end0g (refine_mring ds))"
  using simple converse
proof (induction ds)
  case Nil then show ?case by simp
next
  case (Cons d ds)
  have tail: "distinct (map end0g (refine_mring ds))"
    by (rule Cons.IH) (use Cons.prems in auto)
  have fresh: "end0g d\<notin>end0g ` set ds" using Cons.prems by auto
  have noedge: "gedge d\<notin>set ds" using Cons.prems(2) by simp
  have not0: "end0g (refine_dart0 d)\<notin>end0g ` set (refine_mring ds)"
  proof
    assume "end0g (refine_dart0 d)\<in>end0g ` set (refine_mring ds)"
    then obtain e where e: "e\<in>set ds" and eq:
      "end0g (refine_dart0 d)=end0g (refine_dart0 e) \<or>
       end0g (refine_dart0 d)=end0g (refine_dart1 e)"
      by (auto simp: refine_mring_def refine_dart0_def[symmetric] refine_dart1_def[symmetric])
    have "end0g (refine_dart0 d)\<noteq>end0g (refine_dart1 e)" by (rule refine_vertex_midpoint)
    then have "end0g d=end0g e" using eq by (simp add: end0g_refine0 doubleg_inj)
    then show False using fresh e by blast
  qed
  have not1: "end0g (refine_dart1 d)\<notin>end0g ` set (refine_mring ds)"
  proof
    assume "end0g (refine_dart1 d)\<in>end0g ` set (refine_mring ds)"
    then obtain e where e: "e\<in>set ds" and eq:
      "end0g (refine_dart1 d)=end0g (refine_dart0 e) \<or>
       end0g (refine_dart1 d)=end0g (refine_dart1 e)"
      by (auto simp: refine_mring_def refine_dart0_def[symmetric] refine_dart1_def[symmetric])
    have "end0g (refine_dart0 e)\<noteq>end0g (refine_dart1 d)" by (rule refine_vertex_midpoint)
    then have "d=e \<or> d=gedge e" using eq refine_midpoint_eq[of d e] by metis
    then show False using fresh e noedge by (metis gedge2 imageI)
  qed
  show ?case using tail not0 not1 refine_vertex_midpoint[of d d] by simp
qed

lemma refine_mring_simple:
  "valid_matte m \<Longrightarrow> distinct (map end0g (refine_mring (mring m)))"
  by (rule refine_mring_simple_aux) (auto intro: mring_simple dest: mring_edge)

lemma halfg_refine0 [simp]: "halfg (refine_dart0 d) = d"
  by (simp add: refine_dart0_def halfg_add2 halfg_odd[OF oddg_corners])
lemma halfg_refine1 [simp]: "halfg (refine_dart1 d) = gface d"
  by (simp add: refine_dart1_def halfg_add2 halfg_odd[OF oddg_corners])
lemma oddg_refine0 [simp]: "oddg (refine_dart0 d) = oddg d"
  by (simp add: refine_dart0_def oddg_add2 oddg_id[OF oddg_corners])
lemma oddg_refine1 [simp]: "oddg (refine_dart1 d) = oddg d"
  by (simp add: refine_dart1_def oddg_add2 oddg_id[OF oddg_corners])
lemma halfg_sub_corner:
  "halfg (d-v) = halfg d + halfg (-v + oddg d)"
  using halfg_add[of d "-v"] by (simp only: diff_conv_add_uminus)
lemma halfg_edge_refine0:
  "halfg (halfg (gedge (refine_dart0 d))) = halfg (gedge d)"
  using oddg_corners[of d]
  by (simp only: halfg_edge oddg_refine0 halfg_refine0 halfg_sub_corner;
      cases "halfg d"; auto simp: gcorners_def arcg_def ccw_def halfg_def)
lemma halfg_edge_refine1:
  "halfg (halfg (gedge (refine_dart1 d))) = halfg (gedge d)"
  using oddg_corners[of d]
  by (simp only: halfg_edge oddg_refine1 halfg_refine1 halfg_sub_corner halfg_face oddg_face;
      cases "halfg d"; auto simp: gcorners_def arcg_def ccw_def halfg_def)
lemma refine_dart0_border [simp]:
  "refine_dart0 d\<in>gborder (halfg -` A) \<longleftrightarrow> d\<in>gborder A"
  by (simp only: gborder_def mem_Collect_eq vimage_eq halfg_refine0 halfg_edge_refine0)
lemma refine_dart1_border [simp]:
  "refine_dart1 d\<in>gborder (halfg -` A) \<longleftrightarrow> d\<in>gborder A"
  by (simp only: gborder_def mem_Collect_eq vimage_eq halfg_refine1 halfg_face halfg_edge_refine1)

lemma boundary_corner:
  "b\<in>gcorners \<Longrightarrow> c\<in>gcorners \<Longrightarrow> halfg (b - arcg (ccw c)) \<noteq> 0 \<Longrightarrow>
    b=c \<or> b=ccw c"
  by (auto simp: gcorners_def arcg_def ccw_def halfg_def)

lemma refine_boundary_decompose:
  assumes neq: "halfg (halfg d) \<noteq> halfg (halfg (gedge d))"
  shows "\<exists>e. d=refine_dart0 e \<or> d=refine_dart1 e"
proof -
  let ?p = "halfg d"
  let ?c = "oddg d"
  let ?b = "oddg ?p"
  let ?v = "arcg (ccw ?c)"
  let ?e = "doubleg (halfg ?p) + ?c"
  have ec: "oddg ?e = ?c"
    by (simp only: oddg_add2 oddg_id[OF oddg_corners])
  have edge: "halfg (halfg (gedge d)) = halfg ?p + halfg (-?v + ?b)"
    by (simp only: halfg_edge halfg_sub_corner)
  have ne: "halfg (-?v + ?b) \<noteq> 0"
  proof
    assume "halfg (-?v + ?b)=0"
    then have "halfg (halfg (gedge d))=halfg ?p" using edge by simp
    then show False using neq by simp
  qed
  (* Explicit substitution avoids cycling between subtraction and addition. *)
  have ne': "halfg (?b - ?v) \<noteq> 0"
    by (subst diff_conv_add_uminus, subst add.commute, rule ne)
  have bc: "?b=?c \<or> ?b=ccw ?c"
    by (rule boundary_corner[OF oddg_corners oddg_corners ne'])
  have "d=refine_dart0 ?e \<or> d=refine_dart1 ?e"
  proof (cases "?b=?c")
    case True
    have p: "?p=?e" using halfgK[of ?p]
      by (simp only: True)
    have "refine_dart0 ?e = doubleg ?e + ?c"
      by (simp only: refine_dart0_def ec)
    also have "\<dots> = doubleg ?p + ?c" by (rule arg_cong[OF p[symmetric]])
    also have "\<dots> = d" by (rule halfgK)
    finally have "d=refine_dart0 ?e" by (rule sym)
    then show ?thesis by simp
  next
    case False
    have b: "?b=ccw ?c" using bc False by blast
    have face: "gface ?e = doubleg (halfg ?p) + ?b"
      by (simp only: gface_def halfg_add2 halfg_odd[OF oddg_corners]
        gpoint_zero add_0_right ec b)
    have p: "?p=gface ?e" using halfgK[of ?p]
      by (simp only: face)
    have "refine_dart1 ?e = doubleg (gface ?e) + ?c"
      by (simp only: refine_dart1_def ec)
    also have "\<dots> = doubleg ?p + ?c" by (rule arg_cong[OF p[symmetric]])
    also have "\<dots> = d" by (rule halfgK)
    finally have "d=refine_dart1 ?e" by (rule sym)
    then show ?thesis by simp
  qed
  then show ?thesis by blast
qed

lemma refine_mring_border:
  assumes "set ds = gborder A"
  shows "set (refine_mring ds) = gborder (halfg -` A)"
proof
  show "set (refine_mring ds) \<subseteq> gborder (halfg -` A)"
    using assms by (auto simp: refine_mring_def refine_dart0_def[symmetric] refine_dart1_def[symmetric])
  show "gborder (halfg -` A) \<subseteq> set (refine_mring ds)"
  proof
    fix d assume d: "d\<in>gborder (halfg -` A)"
    then have neq: "halfg (halfg d) \<noteq> halfg (halfg (gedge d))"
      by (auto simp: gborder_def)
    obtain e where "d=refine_dart0 e \<or> d=refine_dart1 e"
      using refine_boundary_decompose[OF neq] by blast
    then show "d\<in>set (refine_mring ds)" using d assms
      by (auto simp: refine_mring_def refine_dart0_def[symmetric] refine_dart1_def[symmetric])
  qed
qed

definition refine_matte :: "matte \<Rightarrow> matte" where
  "refine_matte m = \<lparr>mdisk=refine_mdisk (mdisk m), mring=refine_mring (mring m)\<rparr>"
lemma refine_matte_valid:
  assumes v: "valid_matte m"
  shows "valid_matte (refine_matte m)"
proof -
  have disk: "set (refine_mdisk (mdisk m)) = halfg -` set (mdisk m)"
    by (auto simp: in_refine_mdisk)
  have border: "set (refine_mring (mring m)) = gborder (set (refine_mdisk (mdisk m)))"
    using refine_mring_border[OF in_mring[OF v]] disk by simp
  show ?thesis using refine_mdisk_ne[OF matte_ne[OF v]]
    refine_mring_cycle[of "mring m"] mring_cycle[OF v] refine_mring_simple[OF v] border
    by (simp add: valid_matte_def refine_matte_def)
qed

lemma in_refine_matte: "p\<in>set (mdisk (refine_matte m)) \<longleftrightarrow> halfg p\<in>set (mdisk m)"
  by (simp add: refine_matte_def in_refine_mdisk)
lemma refine_matte_coarse: "coarse_in A (refine_matte m)"
  by (simp add: coarse_in_def in_refine_matte)

end
