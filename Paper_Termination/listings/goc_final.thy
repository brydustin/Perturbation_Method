theorem goctagon_stops_no_band:
  "tie_rule tm ts \<Longrightarrow> gstops_within ocp 9 (real_of_float oc_dlf) None tm ts t 14"
  by (rule goc_pieces_terminates [OF band_none gall_nc])
