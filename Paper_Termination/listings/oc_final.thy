theorem octagon_stops_band30:
  "tie_rule tm ts \<Longrightarrow> stops_within ocp 9 (Some (pi / 6)) tm ts t 10"
  by (rule oc_pieces_terminates [OF band30_in [where p = 53, folded oc_b30_def] all_c30])

theorem octagon_stops_no_band:
  "tie_rule tm ts \<Longrightarrow> stops_within ocp 9 None tm ts t 10"
  by (rule oc_pieces_terminates [OF band_none all_nc])
