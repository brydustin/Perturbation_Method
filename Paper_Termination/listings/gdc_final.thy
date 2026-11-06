theorem gdouble_cross_stops_no_band:
  "tie_rule tm ts \<Longrightarrow> gstops_within dcp 9 (real_of_float dc_dlf) None tm ts t 26"
  by (rule gdc_pieces_terminates [OF band_none gall_nc])

theorem gdouble_cross_sidelobes_no_band:
  "tie_rule tm ts \<Longrightarrow> \<exists>n \<le> 26. gelig dcp 9 (real_of_float dc_dlf) None tm (grun dcp 9 (real_of_float dc_dlf) None tm ts t n) t = {} \<and>
     (\<forall>\<phi>. pw dcp 9 (grun dcp 9 (real_of_float dc_dlf) None tm ts t n) \<phi> > sqmax dcp 9 (grun dcp 9 (real_of_float dc_dlf) None tm ts t n) / 100 \<longrightarrow>
        (\<exists>q y. lift q y \<and> (q = tm (fmains dcp 9 (grun dcp 9 (real_of_float dc_dlf) None tm ts t n) t) mod M \<or> (q < M \<and> \<not> in_band None t q))
           \<and> (\<forall>\<theta>. min \<phi> y \<le> \<theta> \<and> \<theta> \<le> max \<phi> y \<longrightarrow>
                pw dcp 9 (grun dcp 9 (real_of_float dc_dlf) None tm ts t n) \<theta>
                  > sqmax dcp 9 (grun dcp 9 (real_of_float dc_dlf) None tm ts t n) / 100 - 2 * real_of_float dc_dlf)))"
  by (rule gdc_guarantee [OF gdouble_cross_stops_no_band])
