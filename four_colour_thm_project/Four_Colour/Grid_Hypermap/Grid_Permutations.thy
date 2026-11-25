(* Permutation restriction used for the framed grid hypermap in gridmap.v.
   Original G. Gonthier et al., CeCILL-B. Isabelle/HOL port: Codex. *)
theory Grid_Permutations
  imports Four_Colour_Grid_Map.Grid_Bounds Four_Colour_Base.Walkup
begin

lemma skip_list_permutes:
  assumes finite: "finite S" and perm: "f permutes S"
  shows "foldl (\<lambda>g z. skip z g) f xs permutes (S - set xs)"
  using finite perm
proof (induction xs arbitrary: f S)
  case Nil then show ?case by simp
next
  case (Cons z xs)
  interpret P: fperm f S by unfold_locales (rule Cons.prems)+
  have finite: "finite (S-{z})" using Cons.prems(1) by simp
  have perm: "skip z f permutes (S-{z})" by (rule P.skip_perm)
  have rest: "foldl (\<lambda>g z. skip z g) (skip z f) xs permutes ((S-{z}) - set xs)"
    by (rule Cons.IH[OF finite perm])
  have eq: "(S-{z}) - set xs = S - set (z#xs)" by auto
  show ?case using rest by (simp only: foldl.simps eq)
qed

lemma skip_list_fconnect:
  assumes finite: "finite S" and perm: "f permutes S" and outside: "x\<notin>set xs"
  shows "fconnect (foldl (\<lambda>g z. skip z g) f xs) x y \<longleftrightarrow>
    fconnect f x y \<and> y\<notin>set xs"
  using finite perm outside
proof (induction xs arbitrary: f S)
  case Nil then show ?case by simp
next
  case (Cons z xs)
  interpret P: fperm f S by unfold_locales (rule Cons.prems)+
  have finite: "finite (S-{z})" using Cons.prems(1) by simp
  have perm: "skip z f permutes (S-{z})" by (rule P.skip_perm)
  have xz: "x\<noteq>z" and rest: "x\<notin>set xs" using Cons.prems(3) by auto
  have ih: "fconnect (foldl (\<lambda>g z. skip z g) (skip z f) xs) x y \<longleftrightarrow>
      fconnect (skip z f) x y \<and> y\<notin>set xs"
    by (rule Cons.IH[OF finite perm rest])
  show ?case using ih P.fconnect_skip[OF xz, of y] by auto
qed

definition gmedge :: "grect \<Rightarrow> gpoint \<Rightarrow> gpoint" where
  "gmedge r d = (if d\<in>gmgrid r then gedge d else d)"

lemma gmedge2 [simp]: "gmedge r (gmedge r d)=d"
  by (cases "d\<in>gmgrid r") (auto simp: gmedge_def)

lemma gmedge_permutes: "gmedge r permutes gmgrid r"
proof -
  have inj: "inj_on (gmedge r) (gmgrid r)" by (rule inj_onI) (metis gmedge2)
  have sub: "gmedge r ` gmgrid r \<subseteq> gmgrid r"
    by (rule image_subsetI) (simp add: gmedge_def)
  have image: "gmedge r ` gmgrid r = gmgrid r"
    by (rule endo_inj_surj[OF finite_gmgrid sub inj])
  have bij: "bij_betw (gmedge r) (gmgrid r) (gmgrid r)" using inj image by (simp only: bij_betw_def)
  show ?thesis by (rule bij_imp_permutes[OF bij]) (simp add: gmedge_def)
qed

lemma gmedge_no_fixed:
  assumes "d\<in>gmgrid r"
  shows "gmedge r d\<noteq>d"
proof -
  have "gedge d\<noteq>d" using neq_halfg_edge[of d] by metis
  then show ?thesis using assms by (simp add: gmedge_def)
qed

end
