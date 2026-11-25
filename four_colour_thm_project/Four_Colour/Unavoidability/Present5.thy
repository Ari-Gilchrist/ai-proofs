(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
theory Present5
  imports Four_Colour_Runtime.Certificate_Runtime
begin

text \<open>The generated configuration or presentation data is retained in the
  theory source. Its long literal terms are omitted from the PDF.\<close>

(*<*)

definition "script5 = (PSplit Pspoke 0 5 True 1 (PSplit Pspoke 1 5 True 2 (PSplit Pspoke 2 6 True 3 (PSplit Pspoke 2 5 True 0 PRed (PSplit Pspoke 3 5 True 0 PRed (PSplit Pspoke 4 6 False 0 (PHub (Hubcap2 0 1 0 (Hubcap2 2 3 (-6) (Hubcap1 4 (-4) Hubcap0)))) (PSplit Pspoke 4 5 False 0 (PHub (Hubcap2 0 1 0 (Hubcap2 2 3 (-7) (Hubcap1 4 (-3) Hubcap0)))) PRed)))) (PSplit Pspoke 4 6 True 0 (PSim 3 True 3) (PSplit Pspoke 3 5 False 0 (PHub (Hubcap2 0 1 0 (Hubcap2 2 3 (-6) (Hubcap1 4 (-4) Hubcap0)))) (PHub (Hubcap2 0 1 0 (Hubcap2 2 3 (-5) (Hubcap1 4 (-5) Hubcap0))))))) (PSplit Pspoke 4 5 True 0 (PSim 4 False 2) (PSplit Pspoke 2 5 True 4 (PSplit Pspoke 1 6 True 0 PRed (PSplit Pspoke 3 5 True 0 (PSim 2 False 2) (PSplit Pspoke 3 6 True 3 (PSplit Pspoke 4 6 True 0 PRed (PHub (Hubcap2 0 1 (-4) (Hubcap2 2 3 (-2) (Hubcap1 4 (-4) Hubcap0))))) (PSplit Pspoke 4 6 True 0 (PSim 2 True 3) (PHub (Hubcap2 0 1 (-4) (Hubcap2 2 3 (-3) (Hubcap1 4 (-3) Hubcap0)))))))) (PSplit Pspoke 3 5 True 0 (PSim 4 True 4) (PSplit Pspoke 1 6 False 5 (PSplit Pspoke 4 6 False 0 (PHub (Hubcap2 0 1 (-3) (Hubcap2 2 3 (-4) (Hubcap1 4 (-3) Hubcap0)))) (PHub (Hubcap2 0 1 (-3) (Hubcap2 2 3 (-5) (Hubcap1 4 (-2) Hubcap0))))) (PSplit Pspoke 4 6 False 0 (PSim 4 True 5) (PHub (Hubcap2 0 1 (-2) (Hubcap2 2 3 (-6) (Hubcap1 4 (-2) Hubcap0)))))))))) (PSplit Pspoke 1 5 True 0 (PSim 1 False 1) (PSplit Pspoke 2 5 True 0 (PSim 2 False 1) (PSplit Pspoke 3 5 True 0 (PSim 3 False 1) (PSplit Pspoke 4 5 True 0 (PSim 4 False 1) (PHub (Hubcap2 0 1 (-4) (Hubcap2 2 3 (-4) (Hubcap1 4 (-2) Hubcap0)))))))))"

lemma check5: "check_ps the_quiz_tree [] (pcons_any 5) (pcons_any 5) script5" by eval

(*>*)

end
