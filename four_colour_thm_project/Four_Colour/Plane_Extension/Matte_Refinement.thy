(* Refinement and corner reduction from matte.v.
   Original G. Gonthier et al., CeCILL-B. Isabelle/HOL port: Codex. *)
theory Matte_Refinement
  imports Coarse_Extension Matte_Order
begin

lemma inset_refine_corner:
  assumes inset: "halfg q\<in>grect_set (inset_grect r)" and corner: "c\<in>gcorners"
  shows "q-c\<in>grect_set (inset_grect (refine_rect r))"
proof -
  have "q\<in>grect_set (inset_grect (inset_grect (refine_rect r)))"
    using inset by (simp only: refine_inset[symmetric] in_refine_rect)
  then show ?thesis using corner
    by (cases r; cases q; auto simp: gcorners_def; presburger)
qed

lemma refine_extends_corner:
  assumes v: "valid_matte m" and at: "halfg q\<in>set (mdisk m)"
    and inset: "halfg q\<in>grect_set (inset_grect r)" and corner: "c\<in>gcorners"
  shows "\<exists>n. valid_matte n \<and>
    {p. halfg p\<in>set (mdisk m)} \<subseteq> set (mdisk n) \<and>
    set (mdisk n) \<subseteq> {p. halfg p\<in>grect_set r \<union> set (mdisk m)} \<and>
    q-c\<in>set (mdisk n)"
proof -
  let ?ref = "refine_matte m"
  let ?rect = "refine_rect r"
  have vr: "valid_matte ?ref" by (rule refine_matte_valid[OF v])
  have coarse: "coarse_in (grect_set ?rect) ?ref" by (rule refine_matte_coarse)
  have meet: "set (mdisk ?ref) \<inter> grect_set ?rect \<noteq> {}"
  proof -
    have "q\<in>set (mdisk ?ref)" using at by (simp only: in_refine_matte)
    moreover have "q\<in>grect_set ?rect"
      using inset insetW[of r] by (auto simp only: in_refine_rect)
    ultimately show ?thesis by blast
  qed
  obtain n where ext: "matte_extension ?ref n"
    and bound: "set (mdisk n) \<subseteq> grect_set ?rect \<union> set (mdisk ?ref)"
    and atn: "q-c\<in>set (mdisk n)"
    using coarse_extends_in[OF vr coarse meet inset_refine_corner[OF inset corner]]
    unfolding extends_in_def by blast
  have valid: "valid_matte n" using matte_extension_valid[OF ext] by simp
  have old: "{p. halfg p\<in>set (mdisk m)} \<subseteq> set (mdisk n)"
    using in_extension[OF ext] by (auto simp only: in_refine_matte mem_Collect_eq)
  have new: "set (mdisk n) \<subseteq> {p. halfg p\<in>grect_set r \<union> set (mdisk m)}"
    using bound by (auto simp only: in_refine_rect in_refine_matte mem_Collect_eq Un_iff)
  show ?thesis by (rule exI[of _ n]) (use valid old new atn in blast)
qed

lemma refine_mcorner:
  assumes v: "valid_matte m" and at: "halfg q\<in>set (mdisk m)"
    and inset: "halfg q\<in>grect_set (inset_grect r)"
    and pos: "0 < mcorner m (halfg q)"
  shows "\<exists>n. valid_matte n \<and>
    {p. halfg p\<in>set (mdisk m)} \<subseteq> set (mdisk n) \<and>
    set (mdisk n) \<subseteq> {p. halfg p\<in>grect_set r \<union> set (mdisk m)} \<and>
    mcorner n q < mcorner m (halfg q)"
proof (cases "oddg q=0")
  case False
  have corner: "ccw (ccw (oddg q))\<in>gcorners" by (intro ccw_corners oddg_corners)
  obtain n where n: "valid_matte n"
    "{p. halfg p\<in>set (mdisk m)} \<subseteq> set (mdisk n)"
    "set (mdisk n) \<subseteq> {p. halfg p\<in>grect_set r \<union> set (mdisk m)}"
    "q-ccw (ccw (oddg q))\<in>set (mdisk n)"
    using refine_extends_corner[OF v at inset corner] by blast
  have "mcorner n q < mcorner m (halfg q)"
    by (rule mcorner_refine_nonzero[OF False at pos n(2,4)])
  then show ?thesis by (rule_tac x=n in exI) (use n in blast)
next
  case True
  let ?c = "if halfg q-(1,1)\<notin>set (mdisk m) then ((1,1)::gpoint)
    else if halfg q-(0,1)\<notin>set (mdisk m) then (0,1) else (1,0)"
  have c: "?c\<in>gcorners" "?c\<noteq>0" "halfg q-?c\<notin>set (mdisk m)"
    using pos by (auto simp: mcorner_def gcorners_def prod_eq_iff split: if_splits)
  obtain n where n: "valid_matte n"
    "{p. halfg p\<in>set (mdisk m)} \<subseteq> set (mdisk n)"
    "set (mdisk n) \<subseteq> {p. halfg p\<in>grect_set r \<union> set (mdisk m)}"
    "q-?c\<in>set (mdisk n)"
    using refine_extends_corner[OF v at inset c(1)] by blast
  have "mcorner n q < mcorner m (halfg q)"
    by (rule mcorner_refine_zero[OF True c n(2,4)])
  then show ?thesis by (rule_tac x=n in exI) (use n in blast)
qed

end
