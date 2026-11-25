(* Port of grid.v: finite pixel rectangles, neighbourhoods and refinement.
   Original G. Gonthier et al., CeCILL-B. Isabelle port: Codex. *)
theory Grid_Rectangles
  imports Grid_Geometry
begin

datatype grect = Grect int int int int

fun grect_set :: "grect \<Rightarrow> gpoint set" where
  "grect_set (Grect a b c d) = {a..<b} \<times> {c..<d}"

fun extend_grect :: "gpoint \<Rightarrow> grect \<Rightarrow> grect" where
  "extend_grect (x,y) (Grect a b c d) = Grect (min a x) (max b (x+1)) (min c y) (max d (y+1))"

definition zwidth :: "int \<Rightarrow> int \<Rightarrow> nat" where "zwidth a b = nat (b-a)"
fun gwidth where "gwidth (Grect a b c d) = zwidth a b"
fun gheight where "gheight (Grect a b c d) = zwidth c d"
definition garea :: "grect \<Rightarrow> nat" where "garea r = gwidth r * gheight r"
definition gr_proper :: "grect \<Rightarrow> bool" where "gr_proper r \<longleftrightarrow> 0 < garea r"
definition zspan :: "int \<Rightarrow> int \<Rightarrow> int list" where "zspan a b = [a..b-1]"
fun enum_grect :: "grect \<Rightarrow> gpoint list" where
  "enum_grect (Grect a b c d) = List.product (zspan a b) (zspan c d)"

lemma finite_grect [simp]: "finite (grect_set r)" by (cases r) simp
lemma in_extend_grect: "insert p (grect_set r) \<subseteq> grect_set (extend_grect p r)"
  by (cases p; cases r) auto

lemma size_zspan [simp]: "length (zspan a b) = zwidth a b"
  by (simp add: zspan_def zwidth_def)

lemma set_zspan [simp]: "set (zspan a b) = {a..<b}"
  by (auto simp: zspan_def; presburger)

lemma size_enum_grect [simp]: "length (enum_grect r) = garea r"
  by (cases r) (simp add: garea_def)

lemma set_enum_grect [simp]: "set (enum_grect r) = grect_set r"
  by (cases r) simp

lemma zspan_uniq [simp]: "distinct (zspan a b)"
  by (simp add: zspan_def)

lemma enum_grect_uniq: "distinct (enum_grect r)"
  by (cases r) (auto intro: distinct_product)

lemma garea_card: "garea r = card (grect_set r)"
  using distinct_card[OF enum_grect_uniq[of r]] by simp

lemma gr_proper_iff: "gr_proper r \<longleftrightarrow> grect_set r \<noteq> {}"
  by (simp add: gr_proper_def garea_card card_gt_0_iff)

lemma garea_subrect: "grect_set r \<subseteq> grect_set s \<Longrightarrow> garea r \<le> garea s"
  unfolding garea_card by (rule card_mono) simp_all

lemma ltn_garea_subrect:
  "grect_set r \<subseteq> grect_set s \<Longrightarrow> p \<in> grect_set s - grect_set r \<Longrightarrow> garea r < garea s"
  unfolding garea_card by (rule psubset_card_mono) auto

fun gtouch :: "gpoint \<Rightarrow> grect" where
  "gtouch (x,y) = Grect (x-1) (x+2) (y-1) (y+2)"
fun ltouch :: "gpoint \<Rightarrow> grect" where
  "ltouch (x,y) = Grect (x-1) (x+1) (y-1) (y+1)"
fun inset_grect :: "grect \<Rightarrow> grect" where
  "inset_grect (Grect a b c d) = Grect (a+1) (b-1) (c+1) (d-1)"

lemma gtouch_l: "grect_set (ltouch p) \<subseteq> grect_set (gtouch p)"
  by (cases p) auto
lemma ltouch_refl: "p \<in> grect_set (ltouch p)" by (cases p) auto
lemma gtouch_refl: "p \<in> grect_set (gtouch p)" by (cases p) auto

lemma gtouch_edge: "halfg (gedge d) \<in> grect_set (gtouch (halfg d))"
  using oddg_corners[of d]
  by (cases "halfg d") (auto simp: gcorners_def ccw_def arcg_def; presburger)

lemma insetP:
  "p \<in> grect_set (inset_grect r) \<longleftrightarrow> grect_set (gtouch p) \<subseteq> grect_set r"
proof -
  obtain a b c d where r: "r = Grect a b c d" by (cases r) auto
  obtain x y where p: "p = (x,y)" by (cases p) auto
  show ?thesis unfolding r p
  proof
    assume "(x,y) \<in> grect_set (inset_grect (Grect a b c d))"
    then show "grect_set (gtouch (x,y)) \<subseteq> grect_set (Grect a b c d)" by auto
  next
    assume sub: "grect_set (gtouch (x,y)) \<subseteq> grect_set (Grect a b c d)"
    have lo: "(x-1,y-1) \<in> grect_set (Grect a b c d)"
      by (rule subsetD[OF sub]) auto
    have hi: "(x+1,y+1) \<in> grect_set (Grect a b c d)"
      by (rule subsetD[OF sub]) auto
    show "(x,y) \<in> grect_set (inset_grect (Grect a b c d))"
      using lo hi by (auto; presburger)
  qed
qed

lemma insetW: "grect_set (inset_grect r) \<subseteq> grect_set r"
  using insetP gtouch_refl by blast

fun refine_rect :: "grect \<Rightarrow> grect" where
  "refine_rect (Grect a b c d) = Grect (2*a) (2*b) (2*c) (2*d)"

lemma in_refine_rect: "p \<in> grect_set (refine_rect r) \<longleftrightarrow> halfg p \<in> grect_set r"
  by (cases r; cases p) (auto simp: halfg_def; presburger)

lemma refine_inset:
  "refine_rect (inset_grect r) = inset_grect (inset_grect (refine_rect r))"
  by (cases r) (simp add: algebra_simps)

text \<open>Half-plane cuts follow the orientation of the four pixel darts,
  as in grid.v. Their intersection with a rectangle remains a rectangle.\<close>

definition gchop :: "gpoint \<Rightarrow> gpoint set" where
  "gchop d = {p. if fst (oddg d) = 0 then
       (if snd (oddg d) = 0 then snd (halfg d) \<le> snd p else fst (halfg d) \<le> fst p)
     else (if snd (oddg d) = 0 then fst p \<le> fst (halfg d) else snd p \<le> snd (halfg d))}"

lemma gchop_halfg [simp]: "halfg d \<in> gchop d"
  by (simp add: gchop_def)

lemma gchop_edge: "gchop (gedge d) = - gchop d"
  using oddg_corners[of d]
  by (cases "halfg d"; simp only: gcorners_def insert_iff empty_iff; elim disjE;
      auto simp: gchop_def ccw_def arcg_def; presburger)

lemma gchop_face_node: "gchop (gface (gnode d)) = gchop (gface (gface d))"
  using oddg_corners[of d]
  by (cases "halfg d"; simp only: gcorners_def insert_iff empty_iff; elim disjE;
      auto simp: gchop_def ccw_def arcg_def)

lemma gchop_shift: "gchop (gface (gedge (gface d))) = gchop d"
  unfolding gedge_def by (simp only: gchop_face_node gface4)

definition gchop1 :: "gpoint \<Rightarrow> gpoint set" where
  "gchop1 d = gchop (gface (gface (gedge d)))"

lemma gchop_chop1: "gchop d \<subseteq> gchop1 d"
  using oddg_corners[of d]
  by (cases "halfg d"; simp only: gcorners_def insert_iff empty_iff; elim disjE;
      auto simp: gchop1_def gchop_def ccw_def arcg_def)

lemma gtouch_chop1:
  "grect_set (gtouch (halfg d)) =
    gchop1 d \<inter> gchop1 (gface d) \<inter> gchop1 (gface (gface d)) \<inter>
      gchop1 (gface (gface (gface d)))"
  using oddg_corners[of d]
  by (cases "halfg d"; simp only: gcorners_def insert_iff empty_iff; elim disjE;
      auto simp: gchop1_def gchop_def ccw_def arcg_def; presburger)

lemma gchop1_shift: "gchop1 (gface (gedge (gface d))) = gchop1 d"
  using oddg_corners[of d]
  by (cases "halfg d"; simp only: gcorners_def insert_iff empty_iff; elim disjE;
      auto simp: gchop1_def gchop_def ccw_def arcg_def)

fun gchop_rect :: "grect \<Rightarrow> gpoint \<Rightarrow> grect" where
  "gchop_rect (Grect a b c e) d =
    (if fst (oddg d) = 0 then
       (if snd (oddg d) = 0 then Grect a b (max c (snd (halfg d))) e
        else Grect (max a (fst (halfg d))) b c e)
     else (if snd (oddg d) = 0 then Grect a (min b (fst (halfg d)+1)) c e
           else Grect a b c (min e (snd (halfg d)+1))))"

lemma in_gchop_rect: "grect_set (gchop_rect r d) = grect_set r \<inter> gchop d"
  by (cases r) (auto simp: gchop_def; presburger)

lemma gchop_rect_sub: "grect_set (gchop_rect r d) \<subseteq> grect_set r"
  by (simp add: in_gchop_rect)

lemma gchop_rect_edge:
  assumes "halfg (gedge d) \<in> grect_set r" "p \<in> grect_set (gchop_rect r d)"
  shows "halfg d \<in> grect_set (gchop_rect r d)"
  using assms oddg_corners[of d]
  by (cases r; cases "halfg d"; cases p)
    (auto simp: in_gchop_rect gchop_def gcorners_def ccw_def arcg_def; presburger)

definition gchop1_rect :: "grect \<Rightarrow> gpoint \<Rightarrow> grect" where
  "gchop1_rect r d = gchop_rect r (gface (gface (gedge d)))"

lemma in_gchop1_rect: "grect_set (gchop1_rect r d) = grect_set r \<inter> gchop1 d"
  by (simp add: gchop1_rect_def gchop1_def in_gchop_rect)

lemma zwidth_double: "zwidth (2*a) (2*b) = 2 * zwidth a b"
  unfolding zwidth_def by (simp add: algebra_simps nat_mult_distrib)

lemma garea_refine_rect: "garea (refine_rect r) = 4 * garea r"
  by (cases r)
    (simp only: refine_rect.simps garea_def gwidth.simps gheight.simps zwidth_double; simp add: algebra_simps)

lemma gr_proper_refine: "gr_proper ((refine_rect ^^ s) r) \<longleftrightarrow> gr_proper r"
  by (induction s) (simp_all add: gr_proper_def garea_refine_rect)

end
