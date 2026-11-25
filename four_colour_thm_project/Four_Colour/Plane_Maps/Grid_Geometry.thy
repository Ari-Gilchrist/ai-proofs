(* Port of the integer-grid geometry in grid.v, through the infinite grid
   permutations. Original G. Gonthier et al., CeCILL-B. Port: Codex. *)
theory Grid_Geometry
  imports Four_Colour_Plane.Realplane
begin

type_synonym gpoint = "int \<times> int"

lemma gpoint_zero [simp]: "(0,0) = (0 :: gpoint)"
  by (simp add: zero_prod_def)

definition doubleg :: "gpoint \<Rightarrow> gpoint" where "doubleg p = p + p"
definition halfg :: "gpoint \<Rightarrow> gpoint" where "halfg p = (fst p div 2, snd p div 2)"
definition oddg :: "gpoint \<Rightarrow> gpoint" where "oddg p = (fst p mod 2, snd p mod 2)"
definition gcorners :: "gpoint set" where "gcorners = {(0,0),(0,1),(1,1),(1,0)}"
definition ccw :: "gpoint \<Rightarrow> gpoint" where "ccw p = (1 - snd p, fst p)"
definition arcg :: "gpoint \<Rightarrow> gpoint" where "arcg p = ccw p - p"

lemma halfg_add2: "halfg (doubleg p + d) = p + halfg d"
  by (cases p; cases d) (auto simp: halfg_def doubleg_def; presburger)

lemma oddg_add2: "oddg (doubleg p + d) = oddg d"
  by (cases p; cases d) (auto simp: oddg_def doubleg_def)

lemma halfgK: "doubleg (halfg d) + oddg d = d"
  by (cases d) (auto simp: halfg_def oddg_def doubleg_def; presburger)

lemma oddg_corners: "oddg d \<in> gcorners"
proof -
  have a: "fst d mod 2 = 0 \<or> fst d mod 2 = 1" by presburger
  have b: "snd d mod 2 = 0 \<or> snd d mod 2 = 1" by presburger
  show ?thesis using a b by (auto simp: oddg_def gcorners_def)
qed

lemma oddg_id: "c \<in> gcorners \<Longrightarrow> oddg c = c"
  by (auto simp: gcorners_def oddg_def)

lemma halfg_odd: "c \<in> gcorners \<Longrightarrow> halfg c = (0,0)"
  by (auto simp: gcorners_def halfg_def)

lemma ccw_corners: "c \<in> gcorners \<Longrightarrow> ccw c \<in> gcorners"
  by (auto simp: gcorners_def ccw_def)

lemma ccw_odd: "ccw (oddg d) = oddg (ccw d)"
  by (cases d) (auto simp: ccw_def oddg_def; presburger)

lemma ccw4 [simp]: "ccw (ccw (ccw (ccw p))) = p"
  by (cases p) (simp add: ccw_def)

lemma ccw2: "ccw (ccw p) = (1,1) - p"
  by (cases p) (simp add: ccw_def)

lemma arcg_ccw2: "arcg (ccw (ccw c)) = - arcg c"
  by (cases c) (simp add: arcg_def ccw_def)

definition end0g :: "gpoint \<Rightarrow> gpoint" where "end0g d = halfg d + oddg d"
definition end1g :: "gpoint \<Rightarrow> gpoint" where "end1g d = halfg d + ccw (oddg d)"

definition gface :: "gpoint \<Rightarrow> gpoint" where
  "gface d = doubleg (halfg d) + ccw (oddg d)"

definition gnode :: "gpoint \<Rightarrow> gpoint" where
  "gnode d = doubleg (halfg d - arcg (oddg d)) + ccw (oddg d)"

definition gedge :: "gpoint \<Rightarrow> gpoint" where "gedge d = gnode (gface d)"

text \<open>The following equalities identify the structured definitions above with
  the arithmetic definitions of gface, gnode and gedge in the reference.\<close>

lemma gface_unlocked: "gface d = d + arcg (oddg d)"
  using halfgK[of d]
  by (cases d) (auto simp: gface_def doubleg_def halfg_def oddg_def arcg_def ccw_def; presburger)

lemma gnode_unlocked: "gnode d = d - arcg (oddg d)"
  using halfgK[of d]
  by (cases d) (auto simp: gnode_def doubleg_def halfg_def oddg_def arcg_def ccw_def; presburger)

lemma halfg_face [simp]: "halfg (gface d) = halfg d"
  unfolding gface_def halfg_add2
  using halfg_odd[OF ccw_corners[OF oddg_corners[of d]]] by simp

lemma oddg_face [simp]: "oddg (gface d) = ccw (oddg d)"
  unfolding gface_def oddg_add2 by (rule oddg_id[OF ccw_corners[OF oddg_corners]])

lemma halfg_node [simp]: "halfg (gnode d) = halfg d - arcg (oddg d)"
  unfolding gnode_def halfg_add2
  using halfg_odd[OF ccw_corners[OF oddg_corners[of d]]] by simp

lemma oddg_node [simp]: "oddg (gnode d) = ccw (oddg d)"
  unfolding gnode_def oddg_add2 by (rule oddg_id[OF ccw_corners[OF oddg_corners]])

lemma halfg_edge [simp]: "halfg (gedge d) = halfg d - arcg (ccw (oddg d))"
  by (simp add: gedge_def)

lemma oddg_edge [simp]: "oddg (gedge d) = ccw (ccw (oddg d))"
  by (simp add: gedge_def)

lemma gedge_eq: "gedge d = doubleg (halfg d - arcg (ccw (oddg d))) + ccw (ccw (oddg d))"
  using halfgK[of "gedge d"] by simp

lemma gedge_unlocked: "gedge d = d + (arcg (oddg d) - arcg (ccw (oddg d)))"
proof -
  have "gedge d = gface d - arcg (ccw (oddg d))"
    by (simp only: gedge_def gnode_unlocked oddg_face)
  then show ?thesis by (simp add: gface_unlocked algebra_simps)
qed

lemma gface4: "gface (gface (gface (gface d))) = d"
  by (subst gface_def) (simp only: halfg_face oddg_face ccw4 halfgK)

lemma gnode4: "gnode (gnode (gnode (gnode d))) = d"
proof -
  have "gnode (gnode (gnode (gnode d))) = doubleg (halfg d) + oddg d"
    by (subst gnode_def) (simp add: arcg_def doubleg_def algebra_simps)
  then show ?thesis by (simp only: halfgK)
qed

lemma gedge2 [simp]: "gedge (gedge d) = d"
proof -
  have "gedge (gedge d) = doubleg (halfg d) + oddg d"
    by (subst gedge_eq) (simp add: arcg_ccw2)
  then show ?thesis by (simp only: halfgK)
qed

lemma end0g_face: "end0g (gface d) = end1g d"
  by (simp add: end0g_def end1g_def)

lemma end0g_node: "end0g (gnode d) = end0g d"
  by (simp add: end0g_def arcg_def algebra_simps)

lemma end0g_edge: "end0g (gedge d) = end1g d"
  by (simp add: gedge_def end0g_node end0g_face)

lemma end1g_edge: "end1g (gedge d) = end0g d"
  using end0g_edge[of "gedge d"] by simp

lemma gedgeK: "gnode (gface (gedge d)) = d"
  by (simp only: gedge_def[symmetric] gedge2)


lemma halfg_oddg_inj:
  "halfg p = halfg q \<Longrightarrow> oddg p = oddg q \<Longrightarrow> p = q"
  using halfgK[of p] halfgK[of q] by metis

lemma end0g_eq: "doubleg (end0g d) - oddg d = d"
  using halfgK[of d]
  by (cases d) (auto simp: doubleg_def end0g_def halfg_def oddg_def; presburger)

lemma end0g_oddg_inj:
  "end0g p = end0g q \<Longrightarrow> oddg p = oddg q \<Longrightarrow> p = q"
  using end0g_eq[of p] end0g_eq[of q] by metis

lemma same_halfg:
  assumes h: "halfg p = halfg q"
  shows "q \<in> set [p, gface p, gface (gface p), gface (gface (gface p))]"
proof -
  have c: "oddg q = oddg p \<or> oddg q = ccw (oddg p) \<or>
      oddg q = ccw (ccw (oddg p)) \<or> oddg q = ccw (ccw (ccw (oddg p)))"
    using oddg_corners[of p] oddg_corners[of q] by (auto simp: gcorners_def ccw_def)
  have "q = p \<or> q = gface p \<or> q = gface (gface p) \<or> q = gface (gface (gface p))"
    using c h by (elim disjE) (metis halfg_oddg_inj halfg_face oddg_face)+
  then show ?thesis by simp
qed

lemma same_end0g:
  assumes h: "end0g p = end0g q"
  shows "q \<in> set [p, gnode p, gnode (gnode p), gnode (gnode (gnode p))]"
proof -
  have c: "oddg q = oddg p \<or> oddg q = ccw (oddg p) \<or>
      oddg q = ccw (ccw (oddg p)) \<or> oddg q = ccw (ccw (ccw (oddg p)))"
    using oddg_corners[of p] oddg_corners[of q] by (auto simp: gcorners_def ccw_def)
  have "q = p \<or> q = gnode p \<or> q = gnode (gnode p) \<or> q = gnode (gnode (gnode p))"
    using c h by (elim disjE) (metis end0g_oddg_inj end0g_node oddg_node)+
  then show ?thesis by simp
qed

lemma bij_period4:
  assumes per: "\<And>x. f (f (f (f x))) = x"
  shows "bij f"
proof (rule bijI)
  show "inj f" unfolding inj_def using per by metis
  show "surj f" unfolding surj_def using per by metis
qed

lemma bij_gface: "bij gface" by (rule bij_period4[OF gface4])
lemma bij_gnode: "bij gnode" by (rule bij_period4[OF gnode4])
lemma bij_gedge: "bij gedge" by (rule bij_period4) simp

lemma gfaceK: "gedge (gnode (gface d)) = d"
  by (simp only: gedge_def[symmetric] gedge2)

lemma gnodeK: "gface (gedge (gnode d)) = d"
  by (rule injD[OF bij_is_inj[OF bij_gnode]]) (rule gedgeK)


lemma neq_ccw: "ccw p \<noteq> p"
  by (cases p) (auto simp: ccw_def; presburger)

lemma neq_halfg_node: "halfg d \<noteq> halfg (gnode d)"
  using oddg_corners[of d] by (auto simp: gcorners_def arcg_def ccw_def prod_eq_iff)

lemma neq_halfg_edge: "halfg d \<noteq> halfg (gedge d)"
  using oddg_corners[of d] by (auto simp: gcorners_def arcg_def ccw_def prod_eq_iff)

lemma halfg_iter_face [simp]: "halfg ((gface ^^ k) d) = halfg d"
  by (induction k) simp_all

lemma oddg_iter_face: "oddg ((gface ^^ k) d) = (ccw ^^ k) (oddg d)"
  by (induction k) simp_all

lemma end0g_iter_node [simp]: "end0g ((gnode ^^ k) d) = end0g d"
  by (induction k) (simp_all add: end0g_node)

lemma oddg_iter_node: "oddg ((gnode ^^ k) d) = (ccw ^^ k) (oddg d)"
  by (induction k) simp_all

lemma halfg_double [simp]: "halfg (doubleg p) = p"
  by (cases p) (simp add: halfg_def doubleg_def)
lemma oddg_double [simp]: "oddg (doubleg p) = 0"
  by (cases p) (simp add: oddg_def doubleg_def)
lemma oddg_eq [simp]: "c \<in> gcorners \<Longrightarrow> oddg (doubleg p + c) = c"
  by (simp add: oddg_add2 oddg_id)
lemma halfg_eq [simp]: "c \<in> gcorners \<Longrightarrow> halfg (doubleg p + c) = p"
  by (simp add: halfg_add2 halfg_odd)
lemma oddg_add: "oddg (p+q) = oddg (q + oddg p)"
  by (cases p; cases q) (auto simp: oddg_def; presburger)
lemma halfg_add: "halfg (p+q) = halfg p + halfg (q + oddg p)"
  by (cases p; cases q) (auto simp: halfg_def oddg_def; presburger)
lemma halfg_add_odd: "halfg (d + oddg d) = end0g d"
  by (simp add: halfg_add end0g_def doubleg_def[symmetric])
lemma end0g_sub1: "end0g d - (1,1) = halfg (d - (1,1))"
  by (cases d) (auto simp: end0g_def halfg_def oddg_def; presburger)
lemma gnode_sub1: "gnode d - (1,1) = gface (d - (1,1))"
  by (cases d) (auto simp: gnode_unlocked gface_unlocked oddg_def arcg_def ccw_def; presburger)

end
