theorem double_cross_stops_band30:
  "tie_rule tm ts \<Longrightarrow> stops_within dcp 9 (Some (pi / 6)) tm ts t 20"
  by (rule dc_pieces_terminates [OF band30_in [where p = 53, folded dc_b30_def] all_c30])

theorem double_cross_stops_no_band:
  "tie_rule tm ts \<Longrightarrow> stops_within dcp 9 None tm ts t 20"
  by (rule dc_pieces_terminates [OF band_none all_nc])
