theory Octagon_UTP
  imports "Perturbative_UTP.Perturbative_UTP" "OCX_Final.Octagon_Final"
begin

text \<open>The octagon with the 30-degree band and with no band: for every focus angle and every tie
  rule the program stops after at most 10 corrections, and then every sidelobe outside the band is
  at or below -20 dB.\<close>

theorem octagon_band30:
  assumes "tie_rule tm ts"
  shows "H[True] perturb (ocp, 9, Some (pi / 6), tm, ts, t)
    [w = Algorithm.run ocp 9 (Some (pi / 6)) tm ts t n \<and> n \<le> 10 \<and> m0 = tm (mains ocp 9 w t) \<and>
     (\<forall>m<M. is_peak ocp 9 w m \<and> m \<noteq> m0 \<and> in_band (Some (pi / 6)) t m \<longrightarrow>
        10 * log 10 (sq ocp 9 w m / sqmax ocp 9 w) \<le> -20)]"
  by (rule perturb_correct [OF octagon_stops_band30 [OF assms]])

theorem octagon_no_band:
  assumes "tie_rule tm ts"
  shows "H[True] perturb (ocp, 9, None, tm, ts, t)
    [w = Algorithm.run ocp 9 None tm ts t n \<and> n \<le> 10 \<and> m0 = tm (mains ocp 9 w t) \<and>
     (\<forall>m<M. is_peak ocp 9 w m \<and> m \<noteq> m0 \<and> in_band None t m \<longrightarrow>
        10 * log 10 (sq ocp 9 w m / sqmax ocp 9 w) \<le> -20)]"
  by (rule perturb_correct [OF octagon_stops_no_band [OF assms]])

ML \<open>writeln ("oracles: " ^ commas (map (#1 o #1) (Thm_Deps.all_oracles
  [@{thm octagon_band30}, @{thm octagon_no_band}])))\<close>

end
