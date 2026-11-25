(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Embed2.thy
    The disk and remainder maps of an embedding, the patch they form, and the final
    contradiction not_embed_reducible (embed.v, lines 1082--1467).
    Ported from G. Gonthier's Coq development (embed.v).
*)
theory Embed2
  imports Embed1
begin

lemma rev_rot1: "rev (rot 1 l) = rotr 1 (rev l)"
proof (cases l)
  case Nil
  then show ?thesis by (simp add: rotr_def rot_def)
next
  case (Cons x t)
  then show ?thesis by (simp add: rotr_def rot_def)
qed

lemma rev_rotS: "rev (rot (Suc 0) l) = rotr (Suc 0) (rev l)"
  using rev_rot1[of l] by simp

lemma rot_rotrS: "rot (Suc 0) (rotr (Suc 0) s) = s"
  using rot_rotr[of 1 s] by simp

lemma (in hypermap) face_inv_fconnect:
  assumes k: "\<And>x. x \<in> D \<Longrightarrow> k (f x) = k x" and c: "cface x y"
  shows "k y = k x"
  using c
proof (induction rule: fconnect_induct)
  case refl
  then show ?case by simp
next
  case (step z)
  then show ?case using k[of z] F.out[of z] by (cases "z \<in> D") auto
qed

lemma length_filter_mono_on:
  "(\<And>y. y \<in> set l \<Longrightarrow> P y \<Longrightarrow> Q y) \<Longrightarrow> length (filter P l) \<le> length (filter Q l)"
  by (induction l) auto

lemma cycle_mono_on:
  assumes c: "cycle r p" and m: "\<And>a b. a \<in> set p \<Longrightarrow> r a b \<Longrightarrow> s a b"
  shows "cycle s p"
  using c m by (auto simp: cycle_nth)

context embed_ctx
begin

section \<open>Basic facts about the perimeter\<close>

lemma eeC [simp]: "C.e (C.e w) = w" using C.plain_eq[OF geoGc(4)] .
lemma eeM [simp]: "M.e (M.e w) = w" using M.plain_eq[OF M.plainG] .

lemma bc_D: "x \<in> bc \<Longrightarrow> x \<in> C.D" by (simp add: bc_def)

lemma rc_D: "x \<in> set rc \<Longrightarrow> x \<in> C.D" using geoGc(8) by blast

lemma not_bc: "x \<in> C.D \<Longrightarrow> x \<notin> bc \<longleftrightarrow> x \<in> set rc" by (auto simp: bc_def)

lemma bcN: "C.n x \<in> bc \<longleftrightarrow> x \<in> bc"
proof (cases "x \<in> C.D")
  case True
  then show ?thesis by (rule bc_rcN)
next
  case False
  then show ?thesis by (simp add: bc_def C.N.out)
qed

lemma rc_face: assumes zr: "z \<in> set rc" shows "C.f z \<notin> set rc"
proof
  assume fzr: "C.f z \<in> set rc"
  have "C.f z = z"
    by (rule C.simple_cface[OF geoGc(9) fzr zr C.F.fconnect_sym[OF fconnect_step[of "C.f" z]]])
  then have "arity Gc z = 1" using C.F.order_1_iff by simp
  moreover have "good_ring_arity Gc z" using embedGc zr by (simp add: embeddable_def)
  ultimately show False by (simp add: good_ring_arity_def)
qed

lemma bc_face2: assumes xbc: "x \<in> bc" and fx: "C.f x \<notin> bc" shows "C.f (C.f x) \<in> bc"
proof -
  have fxD: "C.f x \<in> C.D" using bc_D[OF xbc] by simp
  have fxr: "C.f x \<in> set rc" using fx fxD by (simp add: bc_def)
  have "C.f x \<in> bc \<or> C.e (C.f x) \<in> bc" by (rule edge_perimeter[OF fxD])
  then have efx: "C.e (C.f x) \<in> bc" using fx by simp
  have "C.n (C.f (C.e (C.e (C.f x)))) = C.e (C.f x)" by (rule C.edgeK)
  then have "C.n (C.f (C.f x)) = C.e (C.f x)" by simp
  then show ?thesis using efx bcN by metis
qed

lemma bc_edge2: assumes xbc: "x \<in> bc" and ex: "C.e x \<notin> bc" shows "C.e (C.n (C.e x)) \<in> bc"
proof -
  have exD: "C.e x \<in> C.D" using bc_D[OF xbc] by simp
  then have "C.e x \<in> set rc" using ex by (simp add: bc_def)
  then have r: "C.n (C.e x) \<in> set rc" using rcN by simp
  have "C.n (C.e x) \<in> bc \<or> C.e (C.n (C.e x)) \<in> bc" by (rule edge_perimeter) (use exD in simp)
  then show ?thesis using r by (auto simp: bc_def)
qed

lemma erc_bc: "set erc \<subseteq> bc"
proof
  fix y assume "y \<in> set erc"
  then obtain x where xr: "x \<in> set rc" and y: "y = C.e x" by (auto simp: erc_def)
  have "x \<in> bc \<or> C.e x \<in> bc" by (rule edge_perimeter[OF rc_D[OF xr]])
  then show "y \<in> bc" using xr y by (auto simp: bc_def)
qed

lemma erc_iff: "y \<in> set erc \<longleftrightarrow> C.e y \<in> set rc"
proof
  assume "y \<in> set erc"
  then show "C.e y \<in> set rc" by (auto simp: erc_def)
next
  assume "C.e y \<in> set rc"
  then show "y \<in> set erc" using eeC[of y] unfolding erc_def by (metis image_eqI set_map)
qed

lemma bc_not_erc: "x \<in> bc \<Longrightarrow> x \<notin> set erc \<longleftrightarrow> C.e x \<in> bc"
  using erc_iff[of x] bc_D[of x] by (auto simp: bc_def)

section \<open>The disk map\<close>

definition embd_edge :: "'a \<Rightarrow> 'a" where
  "embd_edge x = (if x \<in> bc then (if C.e x \<in> bc then C.e x else C.e (C.n (C.e x))) else x)"

definition embd_node :: "'a \<Rightarrow> 'a" where
  "embd_node x = (if x \<in> bc then C.n x else x)"

definition embd_face :: "'a \<Rightarrow> 'a" where
  "embd_face x = (if x \<in> bc then (if C.f x \<in> bc then C.f x else C.f (C.f x)) else x)"

definition Gd :: "'a hypermap" where
  "Gd = \<lparr>darts = bc, edge = embd_edge, node = embd_node, face = embd_face\<rparr>"

lemma Gd_simps [simp]:
  "darts Gd = bc" "edge Gd = embd_edge" "node Gd = embd_node" "face Gd = embd_face"
  by (simp_all add: Gd_def)

lemma embd_edge_cl: "x \<in> bc \<Longrightarrow> embd_edge x \<in> bc"
  using bc_edge2 by (auto simp: embd_edge_def)

lemma embd_node_cl: "x \<in> bc \<Longrightarrow> embd_node x \<in> bc"
  using bcN by (simp add: embd_node_def)

lemma embd_face_cl: "x \<in> bc \<Longrightarrow> embd_face x \<in> bc"
  using bc_face2 by (auto simp: embd_face_def)

lemma embd_cancel3: "embd_node (embd_face (embd_edge x)) = x"
proof (cases "x \<in> bc")
  case False
  then show ?thesis by (simp add: embd_edge_def embd_face_def embd_node_def)
next
  case xbc: True
  have nfe: "C.n (C.f (C.e x)) = x" by (rule C.edgeK)
  have fe_bc: "C.f (C.e x) \<in> bc" using xbc nfe bcN by metis
  show ?thesis
  proof (cases "C.e x \<in> bc")
    case True
    then show ?thesis using xbc fe_bc nfe by (simp add: embd_edge_def embd_face_def embd_node_def)
  next
    case exb: False
    define y where "y = C.e (C.n (C.e x))"
    have ybc: "y \<in> bc" unfolding y_def by (rule bc_edge2[OF xbc exb])
    have fy: "C.f y = C.e x" by (simp add: y_def C.nodeK)
    have "embd_edge x = y" using xbc exb by (simp add: embd_edge_def y_def)
    moreover have "embd_face y = C.f (C.e x)" using ybc fy exb by (simp add: embd_face_def)
    ultimately show ?thesis using fe_bc nfe by (simp add: embd_node_def)
  qed
qed

lemma hypermap_Gd: "hypermap Gd"
proof -
  have "hypermap \<lparr>darts = bc, edge = embd_edge, node = embd_node, face = embd_face\<rparr>"
  proof (rule hypermap_cancel3)
    show "finite bc" using C.finite_darts by (simp add: bc_def)
    fix x
    show "embd_edge x \<in> bc \<and> embd_node x \<in> bc \<and> embd_face x \<in> bc" if "x \<in> bc"
      using embd_edge_cl[OF that] embd_node_cl[OF that] embd_face_cl[OF that] by blast
    show "embd_edge x = x \<and> embd_node x = x \<and> embd_face x = x" if "x \<notin> bc"
      using that by (simp add: embd_edge_def embd_node_def embd_face_def)
    show "embd_node (embd_face (embd_edge x)) = x" by (rule embd_cancel3)
  qed
  then show ?thesis by (simp add: Gd_def)
qed

sublocale Dk: hypermap Gd by (rule hypermap_Gd)

lemma embd_face_cface: "x \<in> bc \<Longrightarrow> C.cface x (embd_face x)"
proof -
  assume "x \<in> bc"
  have "C.cface x (C.f (C.f x))" by (rule fconnect_stepI_r[OF fconnect_step])
  then show ?thesis by (auto simp: embd_face_def)
qed

lemma cface_embd_fwd:
  assumes c: "fconnect embd_face x y" and xbc: "x \<in> bc"
  shows "C.cface x y"
  using c
proof (induction rule: fconnect_induct)
  case refl
  then show ?case by simp
next
  case (step z)
  have "z \<in> bc" using step(1) xbc Dk.F.fconnect_in_D[of x z] by simp
  then show ?case using fconnect_trans[OF step(2) embd_face_cface] by blast
qed

lemma cface_embd_bwd_pow:
  assumes xbc: "x \<in> bc" and k: "(C.f ^^ k) x \<in> bc"
  shows "fconnect embd_face x ((C.f ^^ k) x)"
  using k
proof (induction k rule: less_induct)
  case (less k)
  show ?case
  proof (cases k)
    case 0
    then show ?thesis by (simp add: fconnect_def exI[of _ 0])
  next
    case (Suc j)
    show ?thesis
    proof (cases "(C.f ^^ j) x \<in> bc")
      case True
      have "fconnect embd_face x ((C.f ^^ j) x)" using less.IH[of j] Suc True by simp
      moreover have "embd_face ((C.f ^^ j) x) = (C.f ^^ k) x"
        using True less.prems Suc by (simp add: embd_face_def)
      ultimately show ?thesis using fconnect_stepI_r by metis
    next
      case jb: False
      obtain i where j: "j = Suc i" using jb xbc by (cases j) auto
      have jD: "(C.f ^^ j) x \<in> C.D" using bc_D[OF xbc] by simp
      have jr: "(C.f ^^ j) x \<in> set rc" using jb jD by (simp add: bc_def)
      have iD: "(C.f ^^ i) x \<in> C.D" using bc_D[OF xbc] by simp
      have ib: "(C.f ^^ i) x \<in> bc"
      proof (rule ccontr)
        assume "(C.f ^^ i) x \<notin> bc"
        then have "(C.f ^^ i) x \<in> set rc" using iD by (simp add: bc_def)
        then have "C.f ((C.f ^^ i) x) \<notin> set rc" by (rule rc_face)
        then show False using jr j by simp
      qed
      have "fconnect embd_face x ((C.f ^^ i) x)" using less.IH[of i] Suc j ib by simp
      moreover have "embd_face ((C.f ^^ i) x) = (C.f ^^ k) x"
        using ib jb Suc j by (simp add: embd_face_def)
      ultimately show ?thesis using fconnect_stepI_r by metis
    qed
  qed
qed

lemma cface_embd:
  assumes xbc: "x \<in> bc" and ybc: "y \<in> bc"
  shows "Dk.cface x y \<longleftrightarrow> C.cface x y"
proof
  assume "Dk.cface x y"
  then show "C.cface x y" using cface_embd_fwd xbc by simp
next
  assume "C.cface x y"
  then obtain k where "(C.f ^^ k) x = y" by (auto simp: fconnect_def)
  then show "Dk.cface x y" using cface_embd_bwd_pow[OF xbc] ybc by auto
qed

section \<open>The perimeter ring of the disk map\<close>

lemma simple_C_erc: "simple Gc erc"
proof (cases "rc = []")
  case True
  have "erc = []" unfolding erc_def using True by simp
  then show ?thesis by (simp add: simple_def)
next
  case False
  interpret E: revsnip_proper Gc erc by (rule erc_props(1)[OF False])
  show ?thesis by (rule E.simple_r)
qed

lemma simple_Gd_iff:
  assumes "set p \<subseteq> bc"
  shows "simple Gd p \<longleftrightarrow> simple Gc p"
proof -
  have "inj_on (cyc embd_face) (set p) \<longleftrightarrow> inj_on (cyc C.f) (set p)"
    using assms by (auto simp: inj_on_def Dk.F.cyc_eq_iff[simplified] C.F.cyc_eq_iff
        cface_embd[symmetric] subset_iff)
  then show ?thesis by (simp add: simple_def distinct_map)
qed

lemma simple_Gd_erc: "simple Gd erc"
  using simple_Gd_iff[OF erc_bc] simple_C_erc by simp

lemma embd_edge_erc: "y \<in> set erc \<Longrightarrow> embd_edge y = C.e (C.n (C.e y))"
proof -
  assume y: "y \<in> set erc"
  have "y \<in> bc" using y erc_bc by blast
  moreover have "C.e y \<notin> bc" using y erc_iff by (simp add: bc_def)
  ultimately show ?thesis by (simp add: embd_edge_def)
qed

lemma cycle_Gd_erc: "cycle (frel embd_edge) erc"
  unfolding cycle_nth
proof (intro allI impI)
  fix i assume i: "i < length erc"
  have cyc: "\<forall>i < length rc. C.n (rc ! i) = rc ! (Suc i mod length rc)"
    using geoGc(7) by (simp add: ucycle_def cycle_nth)
  have il: "i < length rc" using i by (simp add: erc_def)
  have mem: "erc ! i \<in> set erc" using i by simp
  have "embd_edge (erc ! i) = C.e (C.n (rc ! i))"
    using embd_edge_erc[OF mem] il by (simp add: erc_def)
  also have "\<dots> = erc ! (Suc i mod length erc)"
  proof -
    have m: "Suc i mod length rc < length rc" by (rule mod_less_divisor) (use il in \<open>cases rc; simp\<close>)
    show ?thesis using cyc il m unfolding erc_def by simp
  qed
  finally show "embd_edge (erc ! i) = erc ! (Suc i mod length erc)" .
qed

lemma erc_dE_iff: assumes zbc: "z \<in> bc" shows "embd_edge z \<in> set erc \<longleftrightarrow> z \<in> set erc"
proof
  have nxt: "embd_edge y \<in> set erc" if ye: "y \<in> set erc" for y
  proof -
    obtain i where i: "i < length erc" "erc ! i = y" using ye by (auto simp: in_set_conv_nth)
    have "embd_edge (erc ! i) = erc ! (Suc i mod length erc)"
      using cycle_Gd_erc i(1) by (simp add: cycle_nth)
    moreover have m: "Suc i mod length erc < length erc" by (rule mod_less_divisor) (use i(1) in linarith)
    moreover have "erc ! (Suc i mod length erc) \<in> set erc" by (rule nth_mem[OF m])
    ultimately show ?thesis using i(2) by simp
  qed
  show "z \<in> set erc \<Longrightarrow> embd_edge z \<in> set erc" by (rule nxt)
  assume ez: "embd_edge z \<in> set erc"
  have sub: "embd_edge ` set erc \<subseteq> set erc" using nxt by blast
  have inj: "inj_on embd_edge (set erc)"
    using inj_on_subset[OF Dk.E.inj subset_UNIV] by simp
  have "embd_edge ` set erc = set erc"
    using endo_inj_surj[OF finite_set sub inj] .
  then have "embd_edge z \<in> embd_edge ` set erc" using ez by simp
  then obtain z' where z': "z' \<in> set erc" "embd_edge z = embd_edge z'" by (rule imageE)
  have "inj embd_edge" using Dk.E.inj by simp
  then have "z' = z" using z'(2) by (simp add: inj_eq)
  then show "z \<in> set erc" using z' by simp
qed

section \<open>The remainder map\<close>

lemma h1_D: assumes xbc: "x \<in> bc" shows "h1 x \<in> M.D"
proof -
  have hd: "y \<in> C.D \<Longrightarrow> h y \<in> M.D" for y using hD by blast
  have xD: "x \<in> C.D" using bc_D[OF xbc] .
  show ?thesis using hd[of x] hd[of "C.e x"] hd[of "C.n x"] hd[of "C.n (C.e x)"] xD
    by (simp add: h1_def)
qed

lemma h1_inj: "inj_on h1 bc" using embed_inj by (auto simp: inj_on_def)

lemma h1_eq: "x \<in> bc \<Longrightarrow> y \<in> bc \<Longrightarrow> h1 x = h1 y \<longleftrightarrow> x = y"
  using embed_inj by blast

definition rd :: "'b set" where "rd = h1 ` (bc - set erc)"

definition Rd :: "'b set" where "Rd = M.D - rd"

definition pr :: "'b \<Rightarrow> 'a" where "pr x = inv_into (set erc) h1 x"

definition embr_edge :: "'b \<Rightarrow> 'b" where
  "embr_edge x = (if x \<in> Rd then M.e x else x)"

definition embr_node :: "'b \<Rightarrow> 'b" where
  "embr_node x = (if x \<in> Rd then (if x \<in> h1 ` set erc then h1 (C.n (embd_face (pr x))) else M.n x)
                 else x)"

definition embr_face :: "'b \<Rightarrow> 'b" where
  "embr_face x = (if x \<in> Rd then (if M.e x \<in> h1 ` set erc then h1 (embd_edge (pr (M.e x))) else M.f x)
                 else x)"

definition Gr :: "'b hypermap" where
  "Gr = \<lparr>darts = Rd, edge = embr_edge, node = embr_node, face = embr_face\<rparr>"

lemma Gr_simps [simp]:
  "darts Gr = Rd" "edge Gr = embr_edge" "node Gr = embr_node" "face Gr = embr_face"
  by (simp_all add: Gr_def)

lemma pr_mem: "x \<in> h1 ` set erc \<Longrightarrow> pr x \<in> set erc"
  by (simp add: pr_def inv_into_into)

lemma h1_pr: "x \<in> h1 ` set erc \<Longrightarrow> h1 (pr x) = x"
  by (simp add: pr_def f_inv_into_f)

lemma pr_h1: "u \<in> set erc \<Longrightarrow> pr (h1 u) = u"
  using inv_into_f_f[OF inj_on_subset[OF h1_inj erc_bc]] by (simp add: pr_def)

lemma h1_erc_Rd: "u \<in> set erc \<Longrightarrow> h1 u \<in> Rd"
proof -
  assume u: "u \<in> set erc"
  have ubc: "u \<in> bc" using u erc_bc by blast
  have "h1 u \<notin> rd"
  proof
    assume "h1 u \<in> rd"
    then obtain v where v: "v \<in> bc" "v \<notin> set erc" "h1 u = h1 v" by (auto simp: rd_def)
    then have "u = v" using h1_eq[OF ubc v(1)] by simp
    then show False using u v by simp
  qed
  then show ?thesis using h1_D[OF ubc] by (simp add: Rd_def)
qed

lemma in_rd_iff: "x \<in> bc \<Longrightarrow> h1 x \<in> rd \<longleftrightarrow> x \<notin> set erc"
proof -
  assume xbc: "x \<in> bc"
  show ?thesis
  proof
    assume "h1 x \<in> rd"
    then obtain v where v: "v \<in> bc" "v \<notin> set erc" "h1 x = h1 v" by (auto simp: rd_def)
    have "x = v" using h1_eq[OF xbc v(1)] v(3) by simp
    then show "x \<notin> set erc" using v(2) by simp
  next
    assume "x \<notin> set erc"
    then have "x \<in> bc - set erc" using xbc by simp
    then show "h1 x \<in> rd" unfolding rd_def by (rule imageI)
  qed
qed

lemma Rd_edge: assumes w: "w \<in> Rd" shows "M.e w \<in> Rd"
proof -
  have wD: "w \<in> M.D" and wr: "w \<notin> rd" using w by (auto simp: Rd_def)
  have "M.e w \<notin> rd"
  proof
    assume "M.e w \<in> rd"
    then obtain u where u: "u \<in> bc" "u \<notin> set erc" "M.e w = h1 u" by (auto simp: rd_def)
    have eu: "C.e u \<in> bc" using u bc_not_erc by blast
    have "C.e u \<notin> set erc" using u(1) erc_iff by (simp add: bc_def)
    moreover have "h1 (C.e u) = w" using embedE[OF bc_D[OF u(1)]] u(3) by (metis eeM)
    ultimately have "w \<in> rd" using eu by (auto simp: rd_def)
    then show False using wr by simp
  qed
  then show ?thesis using wD by (simp add: Rd_def)
qed

lemma Rd_node: assumes w: "w \<in> Rd" shows "embr_node w \<in> Rd"
proof (cases "w \<in> h1 ` set erc")
  case True
  define u where "u = pr w"
  have u: "u \<in> set erc" using pr_mem[OF True] by (simp add: u_def)
  have ubc: "u \<in> bc" using u erc_bc by blast
  define z where "z = C.n (embd_face u)"
  have zbc: "z \<in> bc" using embd_face_cl[OF ubc] bcN by (simp add: z_def)
  have "embd_edge z = u" using Dk.faceK[of u] ubc embd_face_cl[OF ubc]
    by (simp add: z_def embd_node_def)
  then have "z \<in> set erc" using erc_dE_iff[OF zbc] u by simp
  then have "h1 z \<in> Rd" by (rule h1_erc_Rd)
  then show ?thesis using w True by (simp add: embr_node_def u_def z_def)
next
  case nw: False
  have wD: "w \<in> M.D" and wr: "w \<notin> rd" using w by (auto simp: Rd_def)
  have "M.n w \<notin> rd"
  proof
    assume "M.n w \<in> rd"
    then obtain u where u: "u \<in> bc" "u \<notin> set erc" "M.n w = h1 u" by (auto simp: rd_def)
    have nnu: "C.n (C.n u) \<in> bc" using u(1) bcN by simp
    have "h1 (C.n (C.n u)) = M.n (M.n (h1 u))" using embedN u(1) bcN by simp
    also have "\<dots> = w" using u(3) M.nnn[OF wD] by metis
    finally have w': "h1 (C.n (C.n u)) = w" .
    show False
    proof (cases "C.n (C.n u) \<in> set erc")
      case True
      then show False using nw w' by blast
    next
      case False
      then have "w \<in> rd" using nnu w' by (auto simp: rd_def)
      then show False using wr by simp
    qed
  qed
  then show ?thesis using w nw wD by (simp add: embr_node_def Rd_def)
qed

lemma Rd_face: assumes w: "w \<in> Rd" shows "embr_face w \<in> Rd"
proof (cases "M.e w \<in> h1 ` set erc")
  case True
  define u where "u = pr (M.e w)"
  have u: "u \<in> set erc" using pr_mem[OF True] by (simp add: u_def)
  have ubc: "u \<in> bc" using u erc_bc by blast
  have "embd_edge u \<in> set erc" using erc_dE_iff[OF ubc] u by simp
  then have "h1 (embd_edge u) \<in> Rd" by (rule h1_erc_Rd)
  then show ?thesis using w True by (simp add: embr_face_def u_def)
next
  case nw: False
  have wD: "w \<in> M.D" using w by (auto simp: Rd_def)
  have ew: "M.e w \<in> Rd" by (rule Rd_edge[OF w])
  have "M.f w \<notin> rd"
  proof
    assume "M.f w \<in> rd"
    then obtain u where u: "u \<in> bc" "u \<notin> set erc" "M.f w = h1 u" by (auto simp: rd_def)
    have "M.n (M.f (M.e (M.e w))) = M.e w" by (rule M.edgeK)
    then have "M.e w = M.n (h1 u)" using u(3) by simp
    also have "\<dots> = h1 (C.n u)" using embedN u(1) by simp
    finally have enu: "M.e w = h1 (C.n u)" .
    have nubc: "C.n u \<in> bc" using u(1) bcN by simp
    have "C.n u \<notin> set erc" using nw enu by blast
    then have "M.e w \<in> rd" using enu nubc by (auto simp: rd_def)
    then show False using ew by (simp add: Rd_def)
  qed
  then show ?thesis using w nw wD by (simp add: embr_face_def Rd_def)
qed

lemma embr_cancel3: "embr_node (embr_face (embr_edge w)) = w"
proof (cases "w \<in> Rd")
  case False
  then show ?thesis by (simp add: embr_edge_def embr_face_def embr_node_def)
next
  case w: True
  have ew: "M.e w \<in> Rd" by (rule Rd_edge[OF w])
  have eE: "embr_edge w = M.e w" using w by (simp add: embr_edge_def)
  show ?thesis
  proof (cases "w \<in> h1 ` set erc")
    case True
    define u where "u = pr w"
    have u: "u \<in> set erc" using pr_mem[OF True] by (simp add: u_def)
    have ubc: "u \<in> bc" using u erc_bc by blast
    have hu: "h1 u = w" using h1_pr[OF True] by (simp add: u_def)
    have du: "embd_edge u \<in> set erc" using erc_dE_iff[OF ubc] u by simp
    have F: "embr_face (M.e w) = h1 (embd_edge u)"
      using ew True by (simp add: embr_face_def u_def)
    have "embr_node (h1 (embd_edge u)) = h1 (C.n (embd_face (embd_edge u)))"
      using h1_erc_Rd[OF du] du pr_h1[OF du] by (simp add: embr_node_def)
    also have "C.n (embd_face (embd_edge u)) = u"
      using Dk.edgeK[of u] embd_face_cl[OF embd_edge_cl[OF ubc]] by (simp add: embd_node_def)
    finally show ?thesis using eE F hu by simp
  next
    case nw: False
    have F: "embr_face (M.e w) = M.f (M.e w)" using ew nw by (simp add: embr_face_def)
    have fe: "M.f (M.e w) \<in> Rd" using Rd_face[OF ew] F by simp
    have "M.f (M.e w) \<notin> h1 ` set erc"
    proof
      assume "M.f (M.e w) \<in> h1 ` set erc"
      then obtain u where u: "u \<in> set erc" "M.f (M.e w) = h1 u" by blast
      have ubc: "u \<in> bc" using u erc_bc by blast
      have "w = M.n (h1 u)" using M.edgeK[of w] u(2) by simp
      also have "\<dots> = h1 (C.n u)" using embedN ubc by simp
      finally have wn: "w = h1 (C.n u)" .
      have nubc: "C.n u \<in> bc" using ubc bcN by simp
      show False
      proof (cases "C.n u \<in> set erc")
        case True
        then show False using nw wn by blast
      next
        case False
        then have "w \<in> rd" using wn nubc by (auto simp: rd_def)
        then show False using w by (simp add: Rd_def)
      qed
    qed
    then show ?thesis using eE F fe M.edgeK[of w] by (simp add: embr_node_def)
  qed
qed

lemma hypermap_Gr: "hypermap Gr"
proof -
  have "hypermap \<lparr>darts = Rd, edge = embr_edge, node = embr_node, face = embr_face\<rparr>"
  proof (rule hypermap_cancel3)
    show "finite Rd" using M.finite_darts by (simp add: Rd_def)
    fix x
    show "embr_edge x \<in> Rd \<and> embr_node x \<in> Rd \<and> embr_face x \<in> Rd" if "x \<in> Rd"
      using Rd_edge[OF that] Rd_node[OF that] Rd_face[OF that] that by (simp add: embr_edge_def)
    show "embr_edge x = x \<and> embr_node x = x \<and> embr_face x = x" if "x \<notin> Rd"
      using that by (simp add: embr_edge_def embr_node_def embr_face_def)
    show "embr_node (embr_face (embr_edge x)) = x" by (rule embr_cancel3)
  qed
  then show ?thesis by (simp add: Gr_def)
qed

sublocale Rm: hypermap Gr by (rule hypermap_Gr)

section \<open>The embedding patch\<close>

definition bGr :: "'b list" where "bGr = rev (map h1 erc)"

lemma distinct_erc: "distinct erc" using simple_Gd_erc Dk.simple_distinct by simp

lemma cycle_bGr: "cycle (frel embr_node) bGr"
proof -
  have "cycle (\<lambda>a b. embr_node (h1 b) = h1 a) erc"
  proof (rule cycle_mono_on[OF cycle_Gd_erc])
    fix a b assume a: "a \<in> set erc" and ab: "embd_edge a = b"
    have abc: "a \<in> bc" using a erc_bc by blast
    have b: "b \<in> set erc" using ab erc_dE_iff[OF abc] a by simp
    have "embr_node (h1 b) = h1 (C.n (embd_face b))"
      using h1_erc_Rd[OF b] b pr_h1[OF b] by (simp add: embr_node_def)
    also have "C.n (embd_face b) = a"
      using Dk.edgeK[of a] ab embd_face_cl[OF embd_edge_cl[OF abc]] by (simp add: embd_node_def)
    finally show "embr_node (h1 b) = h1 a" .
  qed
  then show ?thesis by (simp add: bGr_def cycle_rev cycle_map)
qed

lemma distinct_bGr: "distinct bGr"
  using distinct_erc inj_on_subset[OF h1_inj erc_bc] by (simp add: bGr_def distinct_map)

lemma set_bGr: "set bGr = h1 ` set erc" by (simp add: bGr_def)

lemma embed_patch: "patch Gm Gd Gr h1 id erc bGr"
proof (intro patch.intro patch_axioms.intro)
  show "hypermap Gm" by (rule M.hypermap_axioms)
  show "hypermap Gd" by (rule hypermap_Gd)
  show "hypermap Gr" by (rule hypermap_Gr)
  show "inj_on h1 (darts Gd)" using h1_inj by simp
  show "inj_on id (darts Gr)" by simp
  show "cycle (frel (edge Gd)) erc" using cycle_Gd_erc by simp
  show "simple Gd erc" by (rule simple_Gd_erc)
  show "set erc \<subseteq> darts Gd" using erc_bc by simp
  show "cycle (frel (node Gr)) bGr" using cycle_bGr by simp
  show "distinct bGr" by (rule distinct_bGr)
  show "set bGr \<subseteq> darts Gr" using h1_erc_Rd by (auto simp: set_bGr)
  show "map id bGr = rev (map h1 erc)" by (simp add: bGr_def)
  show "h1 ` darts Gd \<subseteq> darts Gm" using h1_D by auto
  show "id ` darts Gr = (darts Gm - h1 ` darts Gd) \<union> set (map h1 erc)"
  proof -
    have "h1 ` bc = rd \<union> h1 ` set erc" using erc_bc by (auto simp: rd_def)
    moreover have "rd \<inter> h1 ` set erc = {}" using h1_erc_Rd by (auto simp: Rd_def)
    moreover have "h1 ` set erc \<subseteq> M.D" using h1_D erc_bc by auto
    ultimately show ?thesis by (auto simp: Rd_def)
  qed
  fix x
  show "x \<in> darts Gd \<Longrightarrow> x \<notin> set erc \<Longrightarrow> h1 (edge Gd x) = edge Gm (h1 x)"
  proof -
    assume xbc: "x \<in> darts Gd" and xe: "x \<notin> set erc"
    have "C.e x \<in> bc" using xbc xe bc_not_erc by simp
    then show ?thesis using xbc embedE[OF bc_D] by (simp add: embd_edge_def)
  qed
  show "x \<in> darts Gd \<Longrightarrow> h1 (node Gd x) = node Gm (h1 x)"
    using embedN by (simp add: embd_node_def)
  show "\<And>z. z \<in> darts Gr \<Longrightarrow> id (edge Gr z) = edge Gm (id z)" by (simp add: embr_edge_def)
  show "\<And>z. z \<in> darts Gr \<Longrightarrow> z \<notin> set bGr \<Longrightarrow> id (node Gr z) = node Gm (id z)"
    by (simp add: embr_node_def set_bGr)
qed

sublocale P: patch Gm Gd Gr h1 id erc bGr by (rule embed_patch)

lemma planar_Gr: "planar Gr" using P.planar_patch M.planarG by simp

lemma plain_Gr: "plain Gr" using P.plain_patch M.plainG by simp

lemma quasicubic_Gr: "quasicubic Gr bGr"
  using P.cubic_patch M.cubicG by (simp add: quasicubic_def)

section \<open>Faces under h1\<close>

lemma h1F: assumes fx: "C.f x \<in> bc" shows "h1 (C.f x) = M.f (h1 x)"
proof -
  have fxD: "C.f x \<in> C.D" using bc_D[OF fx] .
  have nD: "C.n (C.f x) \<in> C.D" using fxD by simp
  have x: "C.e (C.n (C.f x)) = x" by (rule C.faceK)
  have "h1 x = M.e (h1 (C.n (C.f x)))" using embedE[OF nD] x by simp
  also have "\<dots> = M.e (M.n (h1 (C.f x)))" using embedN[OF fx] by simp
  finally have "h1 x = M.e (M.n (h1 (C.f x)))" .
  then show ?thesis using M.nodeK[of "h1 (C.f x)"] by simp
qed

lemma cface_h1_step: "M.cface (h1 x) (h1 (C.f x))"
proof (cases "x \<in> C.D")
  case False
  then show ?thesis by (simp add: C.F.out)
next
  case xD: True
  show ?thesis
  proof (cases "C.f x \<in> bc")
    case True
    then show ?thesis using h1F by simp
  next
    case fx: False
    have fxr: "C.f x \<in> set rc" using fx xD by (simp add: bc_def)
    have ffx: "C.f (C.f x) \<in> bc"
      using rc_face[OF fxr] xD by (simp add: bc_def)
    have "M.cface (h1 x) (h1 (C.f (C.f x)))"
    proof (cases "x \<in> bc")
      case True
      have "embd_face x = C.f (C.f x)" using True fx by (simp add: embd_face_def)
      then have "Dk.cface x (C.f (C.f x))" using fconnect_step[of embd_face x] by simp
      then show ?thesis using P.patch_face_d'[of x] True by simp
    next
      case False
      then have "x \<in> set rc" using xD by (simp add: bc_def)
      then show ?thesis using rc_face fxr by blast
    qed
    then show ?thesis using h1F[OF ffx] by simp
  qed
qed

lemma cface_h1: "C.cface x y \<Longrightarrow> M.cface (h1 x) (h1 y)"
proof (induction rule: fconnect_induct)
  case refl
  then show ?case by simp
next
  case (step z)
  then show ?case using fconnect_trans[OF step(2) cface_h1_step] by blast
qed

lemma cface_ac_h1:
  assumes xac: "x \<in> ac" and ybc: "y \<in> bc" and c: "M.cface (h1 x) (h1 y)"
  shows "C.cface x y"
proof -
  have "h1 x = h x" using xac by (simp add: h1_def)
  then obtain x1 where xx1: "C.cface x x1" and hx1: "h x1 = h1 y" using cface_h_ac[OF xac] c by auto
  have x1ac: "x1 \<in> ac" by (rule ac_cface[OF xac xx1])
  then have "h1 x1 = h1 y" using hx1 by (simp add: h1_def)
  then have "x1 = y" using h1_eq ac_bc x1ac ybc by blast
  then show ?thesis using xx1 by simp
qed

lemma h1_funpowN: "x \<in> bc \<Longrightarrow> h1 ((C.n ^^ k) x) = (M.n ^^ k) (h1 x) \<and> (C.n ^^ k) x \<in> bc"
  by (induction k) (auto simp: embedN bcN)

lemma cnode_h1: assumes xbc: "x \<in> bc" and ybc: "y \<in> bc" and c: "M.cnode (h1 x) (h1 y)"
  shows "C.cnode x y"
proof -
  obtain k where k: "(M.n ^^ k) (h1 x) = h1 y" using c by (auto simp: fconnect_def)
  then have "h1 ((C.n ^^ k) x) = h1 y" using h1_funpowN[OF xbc] by simp
  then have "(C.n ^^ k) x = y" using h1_eq h1_funpowN[OF xbc] ybc by blast
  then show ?thesis by (auto simp: fconnect_def)
qed

lemma h1_funpowF: "x \<in> ac \<Longrightarrow> h1 ((C.f ^^ k) x) = (M.f ^^ k) (h1 x) \<and> (C.f ^^ k) x \<in> ac"
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  then have a: "(C.f ^^ k) x \<in> ac" and b: "h1 ((C.f ^^ k) x) = (M.f ^^ k) (h1 x)" by simp_all
  have fa: "C.f ((C.f ^^ k) x) \<in> ac" using a acF by simp
  have "h1 (C.f ((C.f ^^ k) x)) = M.f (h1 ((C.f ^^ k) x))"
    using fa a hF by (simp add: h1_def)
  then show ?case using b fa by simp
qed

lemma orbF_h1: assumes xac: "x \<in> ac" shows "orb M.f (h1 x) = map h1 (orb C.f x)"
proof -
  have "order M.f (h1 x) = order C.f x" using hFn[OF xac] xac by (simp add: h1_def)
  then show ?thesis using h1_funpowF[OF xac] by (simp add: orb_def traject_def)
qed

section \<open>The contract colouring and the final contradiction\<close>

lemma rc_face_erc: "map g rc = rot 1 (map g erc)" if g: "\<And>z. z \<in> C.D \<Longrightarrow> g (C.f z) = g z"
proof -
  have cyc: "\<forall>i < length rc. C.n (rc ! i) = rc ! (Suc i mod length rc)"
    using geoGc(7) by (simp add: ucycle_def cycle_nth)
  have "map g rc = map g (rot 1 erc)"
  proof (rule nth_equalityI)
    show "length (map g rc) = length (map g (rot 1 erc))" by (simp add: erc_def)
    fix i assume i: "i < length (map g rc)"
    then have il: "i < length rc" by simp
    have r1: "rot 1 erc ! i = erc ! (Suc i mod length erc)"
      by (rule rot1_nth) (use il in \<open>simp add: erc_def\<close>)
    have m: "Suc i mod length rc < length rc" by (rule mod_less_divisor) (use il in \<open>cases rc; simp\<close>)
    have "rot 1 erc ! i = C.e (C.n (rc ! i))" using r1 cyc il m by (simp add: erc_def)
    then have f: "C.f (rot 1 erc ! i) = rc ! i" by (simp add: C.nodeK)
    have "rot 1 erc ! i \<in> set (rot 1 erc)" by (rule nth_mem) (use il in \<open>simp add: erc_def\<close>)
    then have mem: "rot 1 erc ! i \<in> set erc" by simp
    have zD: "rot 1 erc ! i \<in> C.D" using mem erc_bc bc_D by blast
    have "g (rc ! i) = g (rot 1 erc ! i)" using g[OF zD] unfolding f .
    then show "map g rc ! i = map g (rot 1 erc) ! i"
      using il by (simp add: erc_def)
  qed
  then show ?thesis by (simp add: map_rot)
qed

lemma ucycle_planar_Gr: "ucycle_planar_plain_quasicubic Gr (rotr 1 bGr)"
proof -
  have sr: "set (rotr 1 bGr) = set bGr" by (simp add: rotr_def)
  have "cycle (frel embr_node) (rotr 1 bGr)" using cycle_bGr by (simp add: rotr_def cycle_rot)
  moreover have "distinct (rotr 1 bGr)" using distinct_bGr by (simp add: rotr_def)
  moreover have "set (rotr 1 bGr) \<subseteq> Rd" using sr h1_erc_Rd by (auto simp: set_bGr)
  ultimately show ?thesis
    using hypermap_Gr plain_Gr quasicubic_Gr planar_Gr sr
    by (simp add: ucycle_planar_plain_quasicubic_def ucycle_plain_quasicubic_def
        plain_quasicubic_def ucycle_def quasicubic_def)
qed

lemma embed_closure: "Kempe_closed (ring_trace Gr (rotr 1 bGr))"
  by (rule Kempe_map[OF ucycle_planar_Gr])

end

locale embed_ctx2 = embed_ctx +
  assumes ccD: "set cc \<subseteq> darts Gc"
begin

abbreviation icc where "icc \<equiv> insertE Gc cc"

lemma vcC: "valid_contract Gc rc cc" using Cred by (simp add: C_reducible_def)

lemma icc_D: "set (insertE Gc p) \<subseteq> C.D" if "set p \<subseteq> C.D" for p
  using that by (induction p) auto

lemma icc_rc: "set rc \<inter> set icc = {}"
  by (rule conjunct1[OF vcC[unfolded valid_contract_def]])

lemma icc_bc: "set icc \<subseteq> bc"
proof
  fix y assume y: "y \<in> set icc"
  have "y \<in> C.D" using y icc_D[OF ccD] by blast
  moreover have "y \<notin> set rc" using y icc_rc by blast
  ultimately show "y \<in> bc" by (simp add: bc_def)
qed

lemma mapEh1: "set p \<subseteq> C.D \<Longrightarrow> insertE Gm (map h1 p) = map h1 (insertE Gc p)"
proof (induction p)
  case Nil
  then show ?case by simp
next
  case (Cons a p)
  then have aD: "a \<in> C.D" and pD: "set p \<subseteq> C.D" by simp_all
  show ?case using Cons.IH[OF pD] embedE[OF aD] by simp
qed

lemma iccE: "y \<in> set icc \<Longrightarrow> C.e y \<in> set icc"
proof (induction cc)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then show ?case by auto
qed

lemma embed_sparse: "sparse Gm (insertE Gm (map h1 cc))"
proof -
  have spC: "sparse Gc icc" using vcC by (simp add: valid_contract_def)
  have dC: "distinct icc" and nC: "\<forall>a \<in> set icc. \<forall>b \<in> set icc. C.cnode a b \<longrightarrow> a = b"
    using spC sparse_iff[OF C.hypermap_axioms] by auto
  have inj: "inj_on h1 (set icc)" by (rule inj_on_subset[OF h1_inj icc_bc])
  have "distinct (map h1 icc)" using dC inj by (simp add: distinct_map)
  moreover have "a' = b'" if a': "a' \<in> set (map h1 icc)" and b': "b' \<in> set (map h1 icc)"
    and c: "M.cnode a' b'" for a' b'
  proof -
    obtain a b where a: "a \<in> set icc" "a' = h1 a" and b: "b \<in> set icc" "b' = h1 b" using a' b' by auto
    have "C.cnode a b" using cnode_h1[of a b] a b c icc_bc by blast
    then show ?thesis using nC a b by blast
  qed
  ultimately show ?thesis
    using sparse_iff[OF M.hypermap_axioms] mapEh1[OF ccD] by auto
qed

lemma embed_valid_contract: "valid_contract Gm [] (map h1 cc)"
  unfolding valid_contract_def
proof (intro conjI impI)
  show "set [] \<inter> set (insertE Gm (map h1 cc)) = {}" by simp
  show "sparse Gm (insertE Gm (map h1 cc))" by (rule embed_sparse)
  show "length (map h1 cc) \<in> {1, 2, 3, 4}" using vcC by (simp add: valid_contract_def)
  assume l4: "length (map h1 cc) = 4"
  obtain x where xD: "x \<in> C.D" and kx: "kernel Gc rc x" and tri: "triad Gc icc x"
    using vcC l4 by (auto simp: valid_contract_def)
  have xac: "x \<in> ac" using xD kx by (simp add: ac_def)
  have h1x: "h1 x = h x" using xac by (simp add: h1_def)
  have hxD: "h1 x \<in> M.D" using h1_D ac_bc xac by blast
  have icc_m: "insertE Gm (map h1 cc) = map h1 icc" by (rule mapEh1[OF ccD])
  have "triad Gm (map h1 icc) (h1 x)"
    unfolding triad_def
  proof
    let ?P = "\<lambda>y. fband Gc icc (C.e y)"
    let ?Q = "\<lambda>y. fband Gm (map h1 icc) (M.e y)"
    have imp: "?Q (h1 y)" if y: "y \<in> set (orb C.f x)" and py: "?P y" for y
    proof -
      have "C.cface x y" using y by (auto simp: orb_def traject_def fconnect_def)
      then have yac: "y \<in> ac" by (rule ac_cface[OF xac])
      have yD: "y \<in> C.D" using yac by (simp add: ac_def)
      obtain z where z: "z \<in> set icc" and ez: "C.cface (C.e y) z" using py by (auto simp: fband_def)
      have "M.cface (h1 (C.e y)) (h1 z)" by (rule cface_h1[OF ez])
      then show ?thesis using z embedE[OF yD] by (auto simp: fband_def)
    qed
    have "length (filter ?P (orb C.f x)) \<le> length (filter (?Q \<circ> h1) (orb C.f x))"
      by (rule length_filter_mono_on) (use imp in auto)
    also have "\<dots> = length (filter ?Q (orb M.f (h1 x)))"
      by (simp add: orbF_h1[OF xac] filter_map)
    finally show "2 < length (filter ?Q (orb M.f (h1 x)))" using tri by (simp add: triad_def)
    show "\<not> (\<forall>y \<in> set (map h1 icc). adj Gm (h1 x) y)"
    proof
      assume all: "\<forall>y \<in> set (map h1 icc). adj Gm (h1 x) y"
      interpret S: spoke_ctx Gm "h1 x" by (rule M.spoke_ctxI[OF hxD])
      have "adj Gc x y" if yc: "y \<in> set icc" for y
      proof -
        have ybc: "y \<in> bc" using yc icc_bc by blast
        have eyc: "C.e y \<in> set icc" by (rule iccE[OF yc])
        have eybc: "C.e y \<in> bc" using eyc icc_bc by blast
        have yD: "y \<in> C.D" using bc_D[OF ybc] .
        have a1: "adj Gm (h1 x) (h1 y)" using all yc by simp
        have a2: "adj Gm (h1 x) (M.e (h1 y))" using all eyc embedE[OF yD] by force
        have "h1 y \<in> set S.sr \<or> M.e (h1 y) \<in> set S.sr" by (rule S.adj11_edge[OF a1 a2])
        then have "M.cface (h1 x) (M.n (h1 y)) \<or> M.cface (h1 x) (M.n (M.e (h1 y)))"
          by (simp add: S.mem_sr)
        then have "M.cface (h1 x) (h1 (C.n y)) \<or> M.cface (h1 x) (h1 (C.n (C.e y)))"
          using embedN[OF ybc] embedN[OF eybc] embedE[OF yD] by simp
        then have "C.cface x (C.n y) \<or> C.cface x (C.n (C.e y))"
          using cface_ac_h1[OF xac] bcN ybc eybc by blast
        then show ?thesis
        proof
          assume c: "C.cface x (C.n y)"
          have "C.cface (C.e (C.n y)) y" using fconnect_step[of C.f "C.e (C.n y)"] by (simp add: C.nodeK)
          then show ?thesis using c by (auto simp: C.adj_iff)
        next
          assume c: "C.cface x (C.n (C.e y))"
          have n3: "C.n (C.n (C.n (C.e y))) = C.e y" using bc_cubic(1)[OF eybc] .
          have fy: "C.f y = C.n (C.n (C.e y))"
          proof -
            have "C.f y = C.f (C.e (C.n (C.n (C.n (C.e y)))))" using n3 by simp
            then show ?thesis by (simp add: C.nodeK)
          qed
          have "C.f (C.e (C.f y)) = C.n (C.e y)" using fy C.nodeK[of "C.n (C.e y)"] by simp
          then have "C.cface (C.e (C.f y)) (C.n (C.e y))" using fconnect_step[of C.f "C.e (C.f y)"] by simp
          then have xz: "C.cface x (C.e (C.f y))" by (rule fconnect_trans[OF c C.F.fconnect_sym])
          have "C.cface (C.e (C.e (C.f y))) y"
            using C.F.fconnect_sym[OF fconnect_step[of C.f y]] by simp
          then show ?thesis using xz by (auto simp: C.adj_iff)
        qed
      qed
      then show False using tri by (simp add: triad_def)
    qed
  qed
  then show "\<exists>x \<in> darts Gm. kernel Gm [] x \<and> triad Gm (insertE Gm (map h1 cc)) x"
    using hxD icc_m by (auto simp: kernel_def fband_def)
qed

lemma embed_contract: "\<exists>et. cc_ring_trace Gc cc (rev rc) et \<and> ring_trace Gr (rotr 1 bGr) et"
proof -
  obtain k where kc: "cc_coloring Gm (map h1 cc) k"
    using M.contract_coloring[OF embed_valid_contract] by (auto simp: cc_colorable_def)
  have kE: "x \<in> M.D \<Longrightarrow> k (M.e x) = k x \<longleftrightarrow> x \<in> set (map h1 icc)" for x
    using kc mapEh1[OF ccD] by (simp add: cc_coloring_def)
  have kF: "x \<in> M.D \<Longrightarrow> k (M.f x) = k x" for x using kc by (simp add: cc_coloring_def)
  have kk: "\<And>a b. M.cface a b \<Longrightarrow> k b = k a"
    using M.face_inv_fconnect[where k=k, OF kF] by blast
  define k1 where "k1 = k \<circ> h1"
  have k1F: "k1 (C.f x) = k1 x" for x
    using M.face_inv_fconnect[where k=k, OF kF cface_h1_step[of x]] by (simp add: k1_def)
  have k1Ebc: "k1 (C.e x) = k1 x \<longleftrightarrow> x \<in> set icc" if xbc: "x \<in> bc" for x
  proof -
    have "k1 (C.e x) = k (M.e (h1 x))" using embedE[OF bc_D[OF xbc]] by (simp add: k1_def)
    then have "k1 (C.e x) = k1 x \<longleftrightarrow> h1 x \<in> set (map h1 icc)"
      using kE[OF h1_D[OF xbc]] by (simp add: k1_def)
    also have "\<dots> \<longleftrightarrow> x \<in> set icc" using h1_eq xbc icc_bc by auto
    finally show ?thesis .
  qed
  have k1cc: "cc_coloring Gc cc k1"
    unfolding cc_coloring_def
  proof (intro conjI ballI)
    fix x assume xD: "x \<in> C.D"
    show "k1 (C.e x) = k1 x \<longleftrightarrow> x \<in> set icc"
    proof (cases "x \<in> bc")
      case True
      then show ?thesis by (rule k1Ebc)
    next
      case False
      then have exbc: "C.e x \<in> bc" using edge_perimeter[OF xD] by blast
      have "k1 x = k1 (C.e x) \<longleftrightarrow> C.e x \<in> set icc" using k1Ebc[OF exbc] by simp
      moreover have "C.e x \<in> set icc \<longleftrightarrow> x \<in> set icc" using iccE[of x] iccE[of "C.e x"] by auto
      ultimately show ?thesis by auto
    qed
    show "k1 (C.f x) = k1 x" by (rule k1F)
  qed
  have kr: "coloring Gr k"
    unfolding coloring_def
  proof (intro conjI ballI)
    fix x assume xR: "x \<in> darts Gr"
    then have xD: "x \<in> M.D" and xr: "x \<notin> rd" by (auto simp: Rd_def)
    show "k (edge Gr x) \<noteq> k x"
    proof
      assume "k (edge Gr x) = k x"
      then have "x \<in> set (map h1 icc)" using kE[OF xD] xR by (simp add: embr_edge_def)
      then obtain y where y: "y \<in> set icc" and xy: "x = h1 y" by auto
      have ybc: "y \<in> bc" using y icc_bc by blast
      have "C.e y \<in> bc" using iccE[OF y] icc_bc by blast
      then have "y \<notin> set erc" using bc_not_erc[OF ybc] by simp
      then have "x \<in> rd" using ybc xy by (auto simp: rd_def)
      then show False using xr by simp
    qed
    have "Rm.cface x (face Gr x)" by (rule fconnect_step)
    then have "M.cface x (face Gr x)" using P.patch_face_r[of x "face Gr x"] xR Rd_face by simp
    then show "k (face Gr x) = k x" using kk by blast
  qed
  have tr: "map k1 (rev rc) = map k (rotr 1 bGr)"
  proof -
    have "map k1 rc = rot 1 (map k1 erc)" by (rule rc_face_erc) (rule k1F)
    then have "map k1 (rev rc) = rotr 1 (rev (map k1 erc))" by (simp add: rev_map[symmetric] rev_rot1 rev_rotS)
    also have "rev (map k1 erc) = map k bGr" by (simp add: bGr_def k1_def rev_map)
    also have "rotr 1 (map k bGr) = map k (rotr 1 bGr)" by (simp add: rotr_def map_rot)
    finally show ?thesis .
  qed
  have "cc_ring_trace Gc cc (rev rc) (trace (map k1 (rev rc)))"
    using k1cc by (auto simp: cc_ring_trace_def)
  moreover have "ring_trace Gr (rotr 1 bGr) (trace (map k1 (rev rc)))"
    unfolding ring_trace_def tr using kr by blast
  ultimately show ?thesis by blast
qed

theorem not_embed_reducible: False
proof -
  obtain et where etC: "cc_ring_trace Gc cc (rev rc) et" and etR: "ring_trace Gr (rotr 1 bGr) et"
    using embed_contract by blast
  have "Kempe_coclosure (ring_trace Gc (rev rc)) et" using Cred etC by (simp add: C_reducible_def)
  then obtain et' where etC': "ring_trace Gc (rev rc) et'" and etR': "ring_trace Gr (rotr 1 bGr) et'"
    using embed_closure etR unfolding Kempe_coclosure_def by blast
  obtain kc where kc: "coloring Gc kc" and det: "et' = trace (map kc (rev rc))"
    using etC' by (auto simp: ring_trace_def)
  obtain kr where kr: "coloring Gr kr" and detr: "et' = trace (map kr (rotr 1 bGr))"
    using etR' by (auto simp: ring_trace_def)
  have kcF: "kc (C.f z) = kc z" if "z \<in> C.D" for z using kc that by (simp add: coloring_def)
  have kd: "coloring Gd kc"
    unfolding coloring_def
  proof (intro conjI ballI)
    fix x assume x: "x \<in> darts Gd"
    then have xbc: "x \<in> bc" by simp
    have xD: "x \<in> C.D" using bc_D[OF xbc] .
    have kcE: "kc (C.e z) \<noteq> kc z" if "z \<in> C.D" for z using kc that by (simp add: coloring_def)
    show "kc (edge Gd x) \<noteq> kc x"
    proof (cases "C.e x \<in> bc")
      case True
      then show ?thesis using xbc kcE[OF xD] by (simp add: embd_edge_def)
    next
      case False
      have "kc (C.e (C.n (C.e x))) = kc (C.f (C.e (C.n (C.e x))))"
        using kcF[of "C.e (C.n (C.e x))"] xD by simp
      also have "\<dots> = kc (C.e x)" by (simp add: C.nodeK)
      finally show ?thesis using xbc False kcE[OF xD] by (simp add: embd_edge_def)
    qed
    have "C.cface x (embd_face x)" by (rule embd_face_cface[OF xbc])
    then show "kc (face Gd x) = kc x" using C.face_inv_fconnect[where k=kc, OF kcF] by simp
  qed
  have "map kc rc = rot 1 (map kc erc)" by (rule rc_face_erc) (rule kcF)
  have "rot 1 (map kr (rotr 1 bGr)) = map kr bGr"
    unfolding map_rot[symmetric] rot_rotr ..
  then have "trace (map kr bGr) = trace (rot 1 (map kr (rotr 1 bGr)))" by simp
  also have "\<dots> = rot 1 et'" unfolding detr by (rule trace_rot1)
  also have "\<dots> = rot 1 (rev (trace (map kc erc)))"
  proof -
    have "et' = trace (rev (rot 1 (map kc erc)))"
      using det \<open>map kc rc = rot 1 (map kc erc)\<close> by (simp add: rev_map[symmetric])
    also have "\<dots> = rot 1 (rev (trace (rot 1 (map kc erc))))" by (rule trace_rev)
    also have "\<dots> = rot 1 (rev (rot 1 (trace (map kc erc))))" unfolding trace_rot1 ..
    also have "\<dots> = rot 1 (rotr 1 (rev (trace (map kc erc))))" unfolding rev_rot1 ..
    also have "\<dots> = rev (trace (map kc erc))" by (rule rot_rotr)
    finally show ?thesis by simp
  qed
  finally have "trace (map kr bGr) = rot 1 (rev (trace (map kc erc)))" .
  then have "four_colorable Gm" using P.colorable_patch_bwd[OF kd kr] by simp
  then show False using M.noncolG by simp
qed

end

end
