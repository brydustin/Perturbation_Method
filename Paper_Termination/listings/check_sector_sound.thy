theorem check_sector_sound:
  assumes IN: "1 / real N \<in>\<^sub>r IN" and bd: "band_in bd band" and tr: "tie_rule tm ts"
    and chk: "check_sector p q N IN band Dmax wmin f lo hi"
    and t: "real_of_float lo \<le> t" "t \<le> real_of_float hi"
  shows "stops_within (fpos q) N bd tm ts t Dmax"
