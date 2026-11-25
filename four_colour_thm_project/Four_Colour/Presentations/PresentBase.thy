(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
theory PresentBase
  imports Present Configurations
begin

declare rp.red_zpart_def[code] rp.red_pcons_def[code] rp.hub_range_def[code] rp.red_step_def[code]
declare rp.zshiftl.simps[code] rp.zshiftr.simps[code] rp.zstepL.simps[code] rp.zstepR.simps[code]
  rp.zstepLt.simps[code] rp.zstepRt.simps[code] rp.zrange.simps[code]
  rp.red_popr_spoke.simps[code] rp.red_popr_hat.simps[code] rp.red_popl_spoke.simps[code]
  rp.red_popl_hat.simps[code] rp.red_popl_fan1l.simps[code] rp.red_popl_fan2l.simps[code]
  rp.red_popl_fan3l.simps[code] rp.red_popl_fan1r.simps[code] rp.red_popl_fan2r.simps[code]
  rp.red_popl_fan3r.simps[code] rp.red_pop.simps[code] rp.fitqzp.simps[code] rp.red_popqzp.simps[code]
  rp.red_qzt_leaf.simps[code] rp.red_zpart_rec.simps[code]

definition the_quiz_tree :: quiz_tree where "the_quiz_tree = cfquiz_tree the_configs"

end
