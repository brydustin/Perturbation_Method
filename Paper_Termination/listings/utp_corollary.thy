corollary perturb_correct:
  assumes "stops_within p N band tm ts t D"
  shows "H[True] perturb (p, N, band, tm, ts, t)
    [w = Algorithm.run p N band tm ts t n \<and> n \<le> D \<and> m0 = tm (mains p N w t) \<and>
     (\<forall>m<M. is_peak p N w m \<and> m \<noteq> m0 \<and> in_band band t m \<longrightarrow>
        10 * log 10 (sq p N w m / sqmax p N w) \<le> -20)]"
  using perturb_ann_correct [OF assms] by (simp only: perturb_ann_is_perturb)
