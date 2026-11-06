theorem perturb_ann_correct:
  assumes stop: "stops_within p N band tm ts t D"
  shows "H[True] perturb_ann (p, N, band, tm, ts, t, D)
    [w = Algorithm.run p N band tm ts t n \<and> n \<le> D \<and> m0 = tm (mains p N w t) \<and>
     (\<forall>m<M. is_peak p N w m \<and> m \<noteq> m0 \<and> in_band band t m \<longrightarrow>
        10 * log 10 (sq p N w m / sqmax p N w) \<le> -20)]"
  unfolding perturb_ann_def scan_def
  apply (simp only: prod.case kcomp_assoc)
  apply vcg
  apply (simp_all only: fun_eq_iff [symmetric] c0_lam corr_lam sq_patt)
  apply (simp_all add: scan_simps agrees_fupd fupd_at busy_less [OF stop])
  apply (auto simp: c0_def corr_def dest: busy_mem [OF stop] intro: stopped_log)
  apply (auto simp: below_def is_peak_def elig_mem less_Suc_eq)
  done
