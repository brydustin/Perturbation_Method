theorem gcheck_sector_sound:
  assumes IN: "1 / real N \<in>\<^sub>r IN" and bd: "band_in bd band" and tr: "tie_rule tm ts"
    and chk: "gcheck_sector p dlf q N IN band Dmax wmin f lo hi"
    and t: "real_of_float lo \<le> t" "t \<le> real_of_float hi"
  shows "gstops_within (fpos q) N (real_of_float dlf) bd tm ts t Dmax"
