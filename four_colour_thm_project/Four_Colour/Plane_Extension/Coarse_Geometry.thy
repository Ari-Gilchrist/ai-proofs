(* Local geometry used by coarse_extends_in in matte.v.
   Original G. Gonthier et al., CeCILL-B. Isabelle/HOL port: Codex. *)
theory Coarse_Geometry
  imports Four_Colour_Plane_Geometry.Matte_Extension
begin

definition neighbour_dart :: "gpoint \<Rightarrow> gpoint" where
  "neighbour_dart p = doubleg p + ccw (ccw (ccw (oddg p)))"

lemma halfg_neighbour_dart [simp]: "halfg (neighbour_dart p) = p"
  unfolding neighbour_dart_def
  by (rule halfg_eq) (intro ccw_corners oddg_corners)

lemma oddg_neighbour_dart [simp]:
  "oddg (neighbour_dart p) = ccw (ccw (ccw (oddg p)))"
  unfolding neighbour_dart_def
  by (rule oddg_eq) (intro ccw_corners oddg_corners)

lemma halfg_edge_neighbour_dart [simp]:
  "halfg (gedge (neighbour_dart p)) = gnode p"
  by (simp add: gnode_unlocked)

lemma neighbour_dart_node:
  "neighbour_dart (gnode p) = gedge (gnode (gedge (neighbour_dart p)))"
proof (rule halfg_oddg_inj)
  show "halfg (neighbour_dart (gnode p)) =
      halfg (gedge (gnode (gedge (neighbour_dart p))))"
    using oddg_corners[of p]
    by (simp only: halfg_neighbour_dart halfg_edge halfg_node
        oddg_edge oddg_node oddg_neighbour_dart ccw4;
      auto simp: gcorners_def gnode_unlocked arcg_def ccw_def algebra_simps)
  show "oddg (neighbour_dart (gnode p)) =
      oddg (gedge (gnode (gedge (neighbour_dart p))))" by simp
qed

lemma neighbour_dart_face_edge:
  "neighbour_dart (gface (gedge p)) = gedge (gface (neighbour_dart p))"
proof -
  have "gnode (gface (gedge p)) = p" by (rule gedgeK)
  then have "neighbour_dart p =
      gedge (gnode (gedge (neighbour_dart (gface (gedge p)))))"
    using neighbour_dart_node[of "gface (gedge p)"] by simp
  then show ?thesis
    by (metis gedge2 gnodeK)
qed

lemma equad_neighbour_block:
  "grect_set (equad (neighbour_dart p)) = {q. halfg q = halfg p}"
proof -
  have eq: "equad (neighbour_dart p) =
      ltouch (p + ccw (ccw (oddg p)))"
    using equad_vertex[of "gface (gface (gface (neighbour_dart p)))"]
    by (simp add: gface4 end0g_def)
  have block: "ltouch (doubleg a + c + ccw (ccw c)) =
      refine_rect (Grect (fst a) (fst a+1) (snd a) (snd a+1))"
    if "c\<in>gcorners" for a c
    using that by (cases a) (auto simp: gcorners_def ccw_def doubleg_def)
  have rect: "equad (neighbour_dart p) =
      refine_rect (Grect (fst (halfg p)) (fst (halfg p)+1)
        (snd (halfg p)) (snd (halfg p)+1))"
    using block[OF oddg_corners[of p], of "halfg p"]
    by (simp only: halfgK eq)
  have unit: "grect_set (Grect x (x+1) y (y+1)) = {(x,y)}" for x y
    by (auto; presburger)
  show ?thesis by (rule set_eqI)
    (simp only: rect in_refine_rect unit singleton_iff mem_Collect_eq prod.collapse)
qed

lemma coarse_equad_occupied:
  assumes coarse: "coarse_in A m" and p: "p\<in>A"
    and occupied: "grect_set (equad (neighbour_dart p)) \<inter> set (mdisk m) \<noteq> {}"
  shows "p\<in>set (mdisk m)"
  using assms by (auto simp: coarse_in_def equad_neighbour_block)

lemma ehex_shift_quad:
  "grect_set (ehex d) \<union> grect_set (ehex (gface (gedge (gface d))))
    \<subseteq> grect_set (equad d) \<union> grect_set (equad (gedge (gface d)))"
  using oddg_corners[of d]
  by (cases "halfg d"; auto simp: gcorners_def equad_def ehex_def
      in_gchop_rect gchop_def ccw_def arcg_def; presburger)

lemma inset_edge_away:
  assumes inset: "halfg d\<in>grect_set (inset_grect r)"
    and far: "q\<in>grect_set r - gchop1 d"
  shows "halfg (gedge d)\<in>grect_set (inset_grect r)"
  using inset far oddg_corners[of d]
  by (cases r; cases "halfg d"; cases q;
      auto simp: gcorners_def gchop1_def gchop_def ccw_def arcg_def; presburger)

lemma node_touch: "gnode p\<in>grect_set (gtouch p)"
  using gtouch_edge[of "neighbour_dart p"]
  by (simp only: halfg_edge_neighbour_dart halfg_neighbour_dart)

lemma gnode_twice_unlocked:
  "gnode (gnode p) = p - arcg (oddg p) - arcg (ccw (oddg p))"
proof -
  have "gnode (gnode p) = gnode p - arcg (oddg (gnode p))" by (rule gnode_unlocked)
  also have "\<dots> = gnode p - arcg (ccw (oddg p))" by (simp only: oddg_node)
  also have "\<dots> = p - arcg (oddg p) - arcg (ccw (oddg p))"
    by (simp only: gnode_unlocked)
  finally show ?thesis .
qed

lemma node2_touch: "gnode (gnode p)\<in>grect_set (gtouch p)"
  using oddg_corners[of p]
  by (simp only: gnode_twice_unlocked;
      cases p; auto simp: gcorners_def arcg_def ccw_def; presburger)

lemma node_between:
  assumes p: "p\<in>grect_set r" and p2: "gnode (gnode p)\<in>grect_set r"
  shows "gnode p\<in>grect_set r"
  using p p2 oddg_corners[of p]
  by (simp only: gnode_twice_unlocked;
      cases r; cases p;
      auto simp: gcorners_def gnode_unlocked arcg_def ccw_def; presburger)

lemma gtouch_enumeration:
  "grect_set (gtouch p) =
    {p+(-1,-1), p+(-1,0), p+(-1,1),
     p+(0,-1), p, p+(0,1), p+(1,-1), p+(1,0), p+(1,1)}"
proof -
  have interval: "{x-1..<x+2} = {x-1,x,x+1}" for x :: int
    by (auto; presburger)
  show ?thesis by (cases p) (simp add: interval)
qed

lemma touch_behind_neighbour:
  "grect_set (gtouch p) \<inter> gchop (gedge (neighbour_dart p)) \<subseteq>
    grect_set (equad (neighbour_dart (gnode p))) \<union>
    grect_set (equad (neighbour_dart (gnode (gnode p))))"
  using oddg_corners[of p]
  by (simp only: equad_neighbour_block gchop_edge;
      simp only: gchop_def halfg_neighbour_dart oddg_neighbour_dart halfg_node oddg_node;
      simp only: gcorners_def insert_iff empty_iff; elim disjE;
      auto simp: gtouch_enumeration
        halfg_add[of p "(-1,-1)"] halfg_add[of p "(-1,0)"] halfg_add[of p "(-1,1)"]
        halfg_add[of p "(0,-1)"] halfg_add[of p "(0,1)"]
        halfg_add[of p "(1,-1)"] halfg_add[of p "(1,0)"] halfg_add[of p "(1,1)"]
        arcg_def ccw_def halfg_def oddg_def
        prod_eq_iff; presburger)

end
