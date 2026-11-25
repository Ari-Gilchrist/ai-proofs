(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
theory Quiz_Embed
  imports Four_Colour_Presentations.PresentBase
begin

lemma (in hypermap) fitqz_darts:
  assumes qr: "isQuizR qz" and fit: "fitqz G x qz"
  shows "x \<in> D"
proof -
  obtain q0 q1 where qz: "qz = Quiz q0 q1" by (cases qz)
  obtain qa q where q0: "q0 = QaskR qa q" using qr qz by (cases q0) auto
  have a: "nat_of_qarity qa = arity G x" using fit by (simp add: fitqz_def qz q0)
  have "5 \<le> nat_of_qarity qa" by (cases qa) simp_all
  then show ?thesis using a F.order_out[of x] by auto
qed

lemma cfcontract_darts:
  assumes cp: "config_prog (cfprog cf)"
  shows "set (cfcontract cf) \<subseteq> darts (cpG (cfprog cf))"
  using set_mask_subset[of "cfcontract_mask cf" "ctrenum (cfprog cf)"]
    ctrenum_darts[of "cfprog cf"] cp
  by (auto simp: cfcontract_def)

lemma no_fit_reducible_quiz:
  assumes m: "minimal_counter_example (G :: 'a hypermap)"
    and red: "cfreducible cf" and cor: "cfquiz_correct cf"
    and cp: "config_prog (cfprog cf)" and qr: "isQuizR (cfquiz cf)"
  shows "\<not> fitqz G x (cfquiz cf)"
proof
  assume fit: "fitqz G x (cfquiz cf)"
  interpret P: pcp G by (rule mce_pcp[OF m])
  have emb: "embeddable (cpG (cfprog cf)) (cfring cf)"
    and vq: "\<exists>u. valid_quiz (cpG (cfprog cf)) (cfring cf) u (cfquiz cf) \<and>
      u \<in> darts (cpG (cfprog cf))"
    using cor qr by (simp_all add: cfquiz_correct_def)
  obtain u where u: "u \<in> darts (cpG (cfprog cf))"
    and v: "valid_quiz (cpG (cfprog cf)) (cfring cf) u (cfquiz cf)" using vq by blast
  have plain: "plain (cpG (cfprog cf))" by (rule cpmap_plain[OF config_prog_cubic[OF cp]])
  have qc: "quasicubic (cpG (cfprog cf)) (cfring cf)"
    using cpmap_cubic[OF config_prog_cubic[OF cp]] by (simp add: cfring_def)
  interpret Q: quiz_ctx G "cpG (cfprog cf)" "cfring cf" x u "cfquiz cf"
    by (simp add: quiz_ctx_def P.hypermap_axioms P.plainG P.cubicG
        hypermap_cpmap plain qc P.fitqz_darts[OF qr fit] u v fit)
  interpret E: embed_ctx2 G "cpG (cfprog cf)" "cfring cf" "cfcontract cf" Q.h
    by (simp add: embed_ctx2_def embed_ctx_def embed_ctx2_axioms_def
        m emb Q.quiz_preembedding[unfolded Q.ac_def]
        red[unfolded cfreducible_def] Q.h_darts cfcontract_darts[OF cp])
  show False by (rule E.not_embed_reducible)
qed

lemma no_fit_config_tree:
  assumes red: "\<And>cf. cf \<in> set cfs \<Longrightarrow> cfreducible cf"
    and cor: "\<And>cf. cf \<in> set cfs \<Longrightarrow> cfquiz_correct cf"
    and cp: "\<And>cf. cf \<in> set cfs \<Longrightarrow> config_prog (cfprog cf)"
    and m: "minimal_counter_example (G :: 'a hypermap)"
  shows "\<not> qzt_ctx.qzt_fit G x (cfquiz_tree cfs)"
proof
  assume fit: "qzt_ctx.qzt_fit G x (cfquiz_tree cfs)"
  interpret P: pcp G by (rule mce_pcp[OF m])
  obtain i where i: "i < length cfs" and f: "qzt_ctx.cf_fits G (cfs ! i)"
    using P.Q.qzt_fit_cfquiz[OF fit] by blast
  have mem: "cfs ! i \<in> set cfs" by (rule nth_mem[OF i])
  have qr: "isQuizR (cfquiz (cfs ! i))" and fits:
    "(\<exists>y. fitqz G y (cfquiz (cfs ! i))) \<or> (\<exists>y. fitqz (mirror G) y (cfquiz (cfs ! i)))"
    using f by (simp_all add: P.Q.cf_fits_def)
  have nf: "\<not> fitqz G y (cfquiz (cfs ! i))" for y
    by (rule no_fit_reducible_quiz[OF m red[OF mem] cor[OF mem] cp[OF mem] qr])
  have nm: "\<not> fitqz (mirror G) y (cfquiz (cfs ! i))" for y
    by (rule no_fit_reducible_quiz[OF P.minimal_counter_example_mirror[OF m]
          red[OF mem] cor[OF mem] cp[OF mem] qr])
  show False using fits nf nm by blast
qed

end
