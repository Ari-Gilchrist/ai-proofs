(* First-contact argument from extend_madj in matte.v.
   Original G. Gonthier et al., CeCILL-B. Isabelle/HOL port: Codex. *)
theory Matte_Contact
  imports Four_Colour_Plane_Geometry.Matte_Extension
begin

lemma matte_extension_first_contact:
  assumes ext: "matte_extension m xm"
    and valid: "valid_matte m1"
    and disjoint: "set (mdisk m) \<inter> set (mdisk m1) = {}"
    and bound: "set (mdisk xm) \<subseteq> B"
    and meet: "set (mdisk xm) \<inter> set (mdisk m1) \<noteq> {}"
  shows "\<exists>ym. matte_extension m ym \<and>
    set (mdisk ym) \<subseteq> B - set (mdisk m1) \<and> madj m1 ym"
  using ext disjoint bound meet
proof (induction rule: matte_extension.induct)
  case (refl m)
  have False by (rule notE[OF refl.prems(3) refl.prems(1)])
  then show ?case by (rule FalseE)
next
  case (add m xm ym d)
  have sub: "set (mdisk xm) \<subseteq> set (mdisk ym)"
    using add.hyps(4) by (auto simp: ext_mdisk_def)
  have bound0: "set (mdisk xm) \<subseteq> B" using sub add.prems(2) by blast
  show ?case
  proof (cases "set (mdisk xm) \<inter> set (mdisk m1) = {}")
    case False
    then show ?thesis by (rule add.IH[OF add.prems(1) bound0])
  next
    case True
    have at: "halfg d\<in>set (mdisk m1)"
      using add.prems(3) add.hyps(4) True by (auto simp: ext_mdisk_def)
    have vx: "valid_matte xm" using matte_extension_valid[OF add.hyps(1)] by simp
    have old: "halfg (gedge d)\<in>set (mdisk xm)"
      using add.hyps(3) by (simp only: mring_gedge_iff[OF vx]; blast)
    have notin: "halfg (gedge d)\<notin>set (mdisk m1)" using old True by blast
    have boundary: "d\<in>set (mring m1)"
      using at notin by (simp only: in_mring[OF valid] gborder_def mem_Collect_eq; blast)
    have adj: "madj m1 xm"
      unfolding madj_def by (rule bexI[OF _ add.hyps(3)]) (simp only: gedge2 boundary)
    show ?thesis by (rule exI[of _ xm]) (use add.hyps(1) bound0 True adj in blast)
  qed
qed

end
