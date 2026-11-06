theorem double_cross_band30:
  assumes "tie_rule tm ts"
  shows "H[True] perturb (dcp, 9, Some (pi / 6), tm, ts, t)
    [w = Algorithm.run dcp 9 (Some (pi / 6)) tm ts t n \<and> n \<le> 20 \<and> m0 = tm (mains dcp 9 w t) \<and>
     (\<forall>m<M. is_peak dcp 9 w m \<and> m \<noteq> m0 \<and> in_band (Some (pi / 6)) t m \<longrightarrow>
        10 * log 10 (sq dcp 9 w m / sqmax dcp 9 w) \<le> -20)]"
  by (rule perturb_correct [OF double_cross_stops_band30 [OF assms]])
