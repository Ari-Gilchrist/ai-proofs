(* Proof-integrity checkpoint for the framed grid hypermap. *)
theory Grid_Hypermap_Audit
  imports Grid_Colouring
begin

ML \<open>
val grid_hypermap_theorems =
  [@{thm skip_list_permutes}, @{thm skip_list_fconnect},
   @{thm gmface_permutes}, @{thm gmface_fconnect_end0},
   @{thm hypermap_gmdart_map}, @{thm gmdart_plain}, @{thm gmnode_inner},
   @{thm gmface_fcard}, @{thm gmedge_fcard},
   @{thm card_gmgrid}, @{thm fcard_gmface}, @{thm fcard_gmedge},
   @{thm fcard_gmnode_lower}, @{thm connected_gmdart_map},
   @{thm planar_gmdart_map}, @{thm snip_ring.snip_patch},
   @{thm snip_ring.planar_snipr}, @{thm gmring_scycle},
   @{thm snip_ring.diskN_subset_invariant}, @{thm gm_disk_def},
   @{thm disjoint_gmdisk}, @{thm grid_mattes.cutout_insert},
   @{thm grid_mattes.has_cutout}, @{thm grid_mattes.cutout_loopless},
   @{thm grid_mattes.planar_loopless_cutout},
   @{thm grid_mattes.cutout_colour_transfer}];
val _ = if Thm_Deps.has_skip_proof grid_hypermap_theorems
  then error "The grid hypermap depends on a skipped proof" else ();
val _ = if null (Thm_Deps.all_oracles grid_hypermap_theorems)
  then writeln "Grid hypermap audit: no skipped proof and no oracle dependencies"
  else error "Unexpected oracle dependency in the grid hypermap";
\<close>

end
