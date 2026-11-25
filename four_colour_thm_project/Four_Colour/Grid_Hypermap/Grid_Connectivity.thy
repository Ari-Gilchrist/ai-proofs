(* Pixel cycles and connectedness of the framed grid, from gridmap.v.
   Original G. Gonthier et al., CeCILL-B. Isabelle/HOL port: Codex. *)
theory Grid_Connectivity
  imports Grid_Darts
begin

lemma gedge_gnode_face3:
  "gedge (gnode d)=gface (gface (gface d))"
  by (rule injD[OF bij_is_inj[OF bij_gface]]) (simp only: gnodeK gface4)

lemma gmnode_inner_rotation:
  "halfg d\<in>grect_set r \<Longrightarrow> gmnode r d=gface (gface (gface d))"
  by (simp only: gmnode_inner gedge_gnode_face3)

lemma gmnode_fconnect_halfg:
  assumes inner: "halfg x\<in>grect_set r"
  shows "fconnect (gmnode r) x y \<longleftrightarrow> halfg x=halfg y"
proof
  assume con: "fconnect (gmnode r) x y"
  have "halfg y=halfg x" using con
  proof (induction rule: fconnect_induct)
    case refl then show ?case by simp
  next
    case (step z)
    have zin: "halfg z\<in>grect_set r" using step.IH inner by simp
    show ?case using gmnode_inner_halfg[OF zin] step.IH by simp
  qed
  then show "halfg x=halfg y" by simp
next
  assume eq: "halfg x=halfg y"
  have cases: "y\<in>set [x,gface x,gface (gface x),gface (gface (gface x))]"
    by (rule same_halfg[OF eq])
  have n1: "gmnode r x=gface (gface (gface x))"
    using inner by (simp add: gmnode_inner_rotation)
  have n2: "gmnode r (gmnode r x)=gface (gface x)"
    using inner by (simp add: gmnode_inner_rotation gface4)
  have n3: "gmnode r (gmnode r (gmnode r x))=gface x"
    using inner by (simp add: gmnode_inner_rotation gface4)
  have c0: "fconnect (gmnode r) x x" by (rule fconnect_refl)
  have c1: "fconnect (gmnode r) x (gmnode r x)" by (rule fconnect_step)
  have c2: "fconnect (gmnode r) x (gmnode r (gmnode r x))" by (rule fconnect_stepI_r[OF c1])
  have c3: "fconnect (gmnode r) x (gmnode r (gmnode r (gmnode r x)))" by (rule fconnect_stepI_r[OF c2])
  have r1: "fconnect (gmnode r) x (gface (gface (gface x)))" using c1 by (simp only: n1)
  have r2: "fconnect (gmnode r) x (gface (gface x))" using c2 by (simp only: n2)
  have r3: "fconnect (gmnode r) x (gface x)" using c3 by (simp only: n3)
  show "fconnect (gmnode r) x y" using cases c0 r1 r2 r3 by auto
qed

definition gm_inner :: "grect \<Rightarrow> gpoint set" where
  "gm_inner r = grect_set (refine_rect r)"

lemma gm_inner_iff [simp]: "d\<in>gm_inner r \<longleftrightarrow> halfg d\<in>grect_set r"
  by (simp add: gm_inner_def in_refine_rect)

lemma finite_gm_inner [simp]: "finite (gm_inner r)" by (simp add: gm_inner_def)

lemma gm_inner_subset: "gm_inner r\<subseteq>gmgrid r"
  by (auto simp only: gm_inner_iff gmgrid_iff)

lemma gm_inner_node_closed:
  "d\<in>gm_inner r \<Longrightarrow> gmnode r d\<in>gm_inner r"
  using gmnode_inner_halfg by (simp only: gm_inner_iff; blast)

lemma gm_inner_halfg_image: "halfg ` gm_inner r = grect_set r"
proof (rule equalityI)
  show "halfg ` gm_inner r \<subseteq> grect_set r" by (auto simp only: gm_inner_iff)
  show "grect_set r \<subseteq> halfg ` gm_inner r"
  proof (rule subsetI)
    fix p assume "p\<in>grect_set r"
    then have member: "doubleg p\<in>gm_inner r" by simp
    have "halfg (doubleg p)\<in>halfg ` gm_inner r" by (rule imageI[OF member])
    then show "p\<in>halfg ` gm_inner r" by simp
  qed
qed

lemma fcard_gmnode_inner:
  "fcard (gmnode r) (gm_inner r) = garea r"
proof -
  interpret G: hypermap "gmdart_map r" by (rule hypermap_gmdart_map)
  have kernel: "cyc (gmnode r) x=cyc (gmnode r) y \<longleftrightarrow> halfg x=halfg y"
    if "x\<in>gm_inner r" "y\<in>gm_inner r" for x y
    using G.N.cyc_eq_iff[of x y] gmnode_fconnect_halfg[of x r y] that by simp
  have "card (cyc (gmnode r) ` gm_inner r) = card (halfg ` gm_inner r)"
    by (rule card_images_same_kernel[OF finite_gm_inner]) (use kernel in blast)
  then show ?thesis by (simp only: fcard_def gm_inner_halfg_image garea_card)
qed

lemma gmdart_same_pixel:
  assumes "halfg x\<in>grect_set r" "halfg x=halfg y"
  shows "gcomp (gmdart_map r) x y"
proof -
  interpret G: hypermap "gmdart_map r" by (rule hypermap_gmdart_map)
  have con: "fconnect (node (gmdart_map r)) x y"
    using gmnode_fconnect_halfg[OF assms(1), of y] assms(2) by simp
  show ?thesis by (rule G.cnode_gcomp[OF con])
qed

lemma gmdart_edge_connected:
  "gcomp (gmdart_map r) d (gmedge r d)"
proof -
  interpret G: hypermap "gmdart_map r" by (rule hypermap_gmdart_map)
  have "gcomp (gmdart_map r) d (edge (gmdart_map r) d)"
    by (rule G.cedge_gcomp, rule fconnect_step)
  then show ?thesis by simp
qed

lemma gmdart_pixel_neighbour:
  assumes corner: "c\<in>gcorners" and p: "p\<in>grect_set r"
    and q: "p-arcg (ccw c)\<in>grect_set r"
  shows "gcomp (gmdart_map r) (doubleg p) (doubleg (p-arcg (ccw c)))"
proof -
  let ?d = "doubleg p+c"
  let ?q = "p-arcg (ccw c)"
  have half: "halfg ?d=p" by (rule halfg_eq[OF corner])
  have odd: "oddg ?d=c" by (rule oddg_eq[OF corner])
  have opposite: "halfg (gedge ?d)=?q" by (simp only: halfg_edge half odd)
  have dD: "?d\<in>gmgrid r" using half p by (simp only: gmgrid_iff; blast)
  have left: "gcomp (gmdart_map r) (doubleg p) ?d"
    by (rule gmdart_same_pixel) (use p half in simp_all)
  have middle: "gcomp (gmdart_map r) ?d (gedge ?d)"
    using gmdart_edge_connected[of r ?d] dD by (simp add: gmedge_def)
  have right: "gcomp (gmdart_map r) (gedge ?d) (doubleg ?q)"
    by (rule gmdart_same_pixel) (use q opposite in simp_all)
  show ?thesis by (rule rtranclp_trans[OF left rtranclp_trans[OF middle right]])
qed

lemma gmdart_pixel_horizontal:
  assumes "p\<in>grect_set r" "p+(1,0)\<in>grect_set r"
  shows "gcomp (gmdart_map r) (doubleg p) (doubleg (p+(1,0)))"
proof -
  have corner: "(1,0)\<in>gcorners" by (simp add: gcorners_def)
  have eq: "p-arcg (ccw (1,0))=p+(1,0)" by (cases p) (simp add: arcg_def ccw_def)
  show ?thesis using gmdart_pixel_neighbour[OF corner assms(1)] assms(2) by (simp only: eq)
qed

lemma gmdart_pixel_vertical:
  assumes "p\<in>grect_set r" "p+(0,1)\<in>grect_set r"
  shows "gcomp (gmdart_map r) (doubleg p) (doubleg (p+(0,1)))"
proof -
  have corner: "(1,1)\<in>gcorners" by (simp add: gcorners_def)
  have eq: "p-arcg (ccw (1,1))=p+(0,1)" by (cases p) (simp add: arcg_def ccw_def)
  show ?thesis using gmdart_pixel_neighbour[OF corner assms(1)] assms(2) by (simp only: eq)
qed

lemma gmdart_pixel_walk:
  assumes bounds: "a<b" "c<d" and pixel: "p\<in>grect_set (Grect a b c d)"
  shows "gcomp (gmdart_map (Grect a b c d)) (doubleg (a,c)) (doubleg p)"
proof -
  let ?r = "Grect a b c d"
  let ?G = "gmdart_map ?r"
  have row: "gcomp ?G (doubleg (a,c)) (doubleg (a+int n,c))"
    if "a+int n<b" for n :: nat
    using that
  proof (induction n)
    case 0 then show ?case by simp
  next
    case (Suc n)
    have prefix: "a+int n<b" using Suc.prems by (simp only: of_nat_Suc; linarith)
    have prior: "gcomp ?G (doubleg (a,c)) (doubleg (a+int n,c))" by (rule Suc.IH[OF prefix])
    have move: "(a+int n,c)+(1,0)=(a+int (Suc n),c)"
      by (simp add: algebra_simps prod_eq_iff)
    have start: "(a+int n,c)\<in>grect_set ?r" using prefix bounds by auto
    have finish: "(a+int n,c)+(1,0)\<in>grect_set ?r" using Suc.prems bounds by (auto simp: move)
    have step: "gcomp ?G (doubleg (a+int n,c)) (doubleg (a+int (Suc n),c))"
      using gmdart_pixel_horizontal[OF start finish] by (simp only: move)
    show ?case by (rule rtranclp_trans[OF prior step])
  qed
  have column: "gcomp ?G (doubleg (x,c)) (doubleg (x,c+int n))"
    if "a\<le>x" "x<b" "c+int n<d" for x :: int and n :: nat
    using that
  proof (induction n)
    case 0 then show ?case by simp
  next
    case (Suc n)
    have prefix: "c+int n<d" using Suc.prems(3) by (simp only: of_nat_Suc; linarith)
    have prior: "gcomp ?G (doubleg (x,c)) (doubleg (x,c+int n))"
      by (rule Suc.IH[OF Suc.prems(1,2) prefix])
    have move: "(x,c+int n)+(0,1)=(x,c+int (Suc n))"
      by (simp add: algebra_simps prod_eq_iff)
    have start: "(x,c+int n)\<in>grect_set ?r" using prefix Suc.prems(1,2) bounds by auto
    have finish: "(x,c+int n)+(0,1)\<in>grect_set ?r"
      using Suc.prems bounds by (auto simp: move)
    have step: "gcomp ?G (doubleg (x,c+int n)) (doubleg (x,c+int (Suc n)))"
      using gmdart_pixel_vertical[OF start finish] by (simp only: move)
    show ?case by (rule rtranclp_trans[OF prior step])
  qed
  obtain x y where point: "p=(x,y)" by (cases p) auto
  have xy: "a\<le>x" "x<b" "c\<le>y" "y<d" using pixel by (auto simp: point)
  have xn: "0\<le>x-a" and yn: "0\<le>y-c" using xy by linarith+
  have xeq: "a+int (nat (x-a))=x" using xn by simp
  have yeq: "c+int (nat (y-c))=y" using yn by simp
  have rowbound: "a+int (nat (x-a))<b" using xeq xy(2) by simp
  have colbound: "c+int (nat (y-c))<d" using yeq xy(4) by simp
  have first: "gcomp ?G (doubleg (a,c)) (doubleg (x,c))"
    using row[OF rowbound] by (simp only: xeq)
  have second: "gcomp ?G (doubleg (x,c)) (doubleg p)"
    using column[OF xy(1,2) colbound] by (simp only: yeq point)
  show ?thesis by (rule rtranclp_trans[OF first second])
qed

fun gm_origin :: "grect \<Rightarrow> gpoint" where
  "gm_origin (Grect a b c d)=(a,c)"

lemma gm_origin_inner:
  "gr_proper r \<Longrightarrow> gm_origin r\<in>grect_set r"
  by (cases r) (simp add: gr_proper_Grect)

lemma gmdart_reachable_from_origin:
  assumes proper: "gr_proper r" and dart: "x\<in>gmgrid r"
  shows "gcomp (gmdart_map r) (doubleg (gm_origin r)) x"
proof -
  obtain a b c d where rect: "r=Grect a b c d" by (cases r) auto
  have bounds: "a<b" "c<d" using proper by (simp_all add: rect gr_proper_Grect)
  have inner_reach: "gcomp (gmdart_map r) (doubleg (gm_origin r)) y"
    if inner: "halfg y\<in>grect_set r" for y
  proof -
    have first: "gcomp (gmdart_map r) (doubleg (gm_origin r)) (doubleg (halfg y))"
      using gmdart_pixel_walk[OF bounds, of "halfg y"] inner by (simp add: rect)
    have second: "gcomp (gmdart_map r) (doubleg (halfg y)) y"
      by (rule gmdart_same_pixel) (use inner in simp_all)
    show ?thesis by (rule rtranclp_trans[OF first second])
  qed
  show ?thesis
  proof (cases "halfg x\<in>grect_set r")
    case True
    then show ?thesis by (rule inner_reach)
  next
    case False
    have inner: "halfg (gedge x)\<in>grect_set r" using dart False by (simp only: gmgrid_iff; blast)
    have first: "gcomp (gmdart_map r) (doubleg (gm_origin r)) (gedge x)" by (rule inner_reach[OF inner])
    have opposite: "gedge x\<in>gmgrid r" using dart by simp
    have second: "gcomp (gmdart_map r) (gedge x) x"
      using gmdart_edge_connected[of r "gedge x"] opposite by (simp add: gmedge_def)
    show ?thesis by (rule rtranclp_trans[OF first second])
  qed
qed

theorem connected_gmdart_map:
  assumes proper: "gr_proper r"
  shows "connected (gmdart_map r)"
proof -
  interpret G: hypermap "gmdart_map r" by (rule hypermap_gmdart_map)
  let ?b = "doubleg (gm_origin r)"
  have base: "?b\<in>gmgrid r" using gm_origin_inner[OF proper] by (simp add: gmgrid_iff)
  have classes: "comp_of (glink (gmdart_map r)) x=comp_of (glink (gmdart_map r)) ?b"
    if x: "x\<in>gmgrid r" for x
  proof -
    have forward: "gcomp (gmdart_map r) ?b x" by (rule gmdart_reachable_from_origin[OF proper x])
    have backward: "gcomp (gmdart_map r) x ?b" by (rule G.gcomp_sym[OF forward])
    show ?thesis unfolding comp_of_def using forward backward by (blast intro: rtranclp_trans)
  qed
  have sub: "comp_of (glink (gmdart_map r)) ` gmgrid r \<subseteq> {comp_of (glink (gmdart_map r)) ?b}"
    by (rule image_subsetI) (use classes in auto)
  have member: "comp_of (glink (gmdart_map r)) ?b\<in>comp_of (glink (gmdart_map r)) ` gmgrid r"
    by (rule imageI[OF base])
  have image: "comp_of (glink (gmdart_map r)) ` gmgrid r = {comp_of (glink (gmdart_map r)) ?b}"
    using sub member by auto
  show ?thesis by (simp add: connected_def n_comp_def image)
qed

end
