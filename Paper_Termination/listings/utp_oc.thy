theorem octagon_band30:
  assumes "tie_rule tm ts"
  shows "H[True] perturb (ocp, 9, Some (pi / 6), tm, ts, t)
    [w = Algorithm.run ocp 9 (Some (pi / 6)) tm ts t n \<and> n \<le> 10 \<and> m0 = tm (mains ocp 9 w t) \<and>
     (\<forall>m<M. is_peak ocp 9 w m \<and> m \<noteq> m0 \<and> in_band (Some (pi / 6)) t m \<longrightarrow>
        10 * log 10 (sq ocp 9 w m / sqmax ocp 9 w) \<le> -20)]"
  by (rule perturb_correct [OF octagon_stops_band30 [OF assms]])
