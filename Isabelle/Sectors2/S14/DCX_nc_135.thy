theory DCX_nc_135
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2160: "dc_sub None 2160"
  by (dc_eval dc_nc_2160)

lemma dc_nc_2161: "dc_sub None 2161"
  by (dc_eval dc_nc_2161)

lemma dc_nc_2162: "dc_sub None 2162"
  by (dc_eval dc_nc_2162)

lemma dc_nc_2163: "dc_sub None 2163"
  by (dc_eval dc_nc_2163)

lemma dc_nc_2164: "dc_sub None 2164"
  by (dc_eval dc_nc_2164)

lemma dc_nc_2165: "dc_sub None 2165"
  by (dc_eval dc_nc_2165)

lemma dc_nc_2166: "dc_sub None 2166"
  by (dc_eval dc_nc_2166)

lemma dc_nc_2167: "dc_sub None 2167"
  by (dc_eval dc_nc_2167)

lemma dc_nc_2168: "dc_sub None 2168"
  by (dc_eval dc_nc_2168)

lemma dc_nc_2169: "dc_sub None 2169"
  by (dc_eval dc_nc_2169)

lemma dc_nc_2170: "dc_sub None 2170"
  by (dc_eval dc_nc_2170)

lemma dc_nc_2171: "dc_sub None 2171"
  by (dc_eval dc_nc_2171)

lemma dc_nc_2172: "dc_sub None 2172"
  by (dc_eval dc_nc_2172)

lemma dc_nc_2173: "dc_sub None 2173"
  by (dc_eval dc_nc_2173)

lemma dc_nc_2174: "dc_sub None 2174"
  by (dc_eval dc_nc_2174)

lemma dc_nc_2175: "dc_sub None 2175"
  by (dc_eval dc_nc_2175)

lemma upt_nc_135: "[2160..<2176] = [2160, 2161, 2162, 2163, 2164, 2165, 2166, 2167, 2168, 2169, 2170, 2171, 2172, 2173, 2174, 2175]"
  by (simp add: upt_rec)

lemma sec_nc_135: "\<forall>j\<in>{16 * 135..<16 * 135 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 135..<16 * 135 + 16}"
  then have "j \<in> set [2160..<2176]" unfolding set_upt by simp
  then have "j \<in> set [2160, 2161, 2162, 2163, 2164, 2165, 2166, 2167, 2168, 2169, 2170, 2171, 2172, 2173, 2174, 2175]" unfolding upt_nc_135 .
  then show "dc_sub None j" using dc_nc_2160 dc_nc_2161 dc_nc_2162 dc_nc_2163 dc_nc_2164 dc_nc_2165 dc_nc_2166 dc_nc_2167 dc_nc_2168 dc_nc_2169 dc_nc_2170 dc_nc_2171 dc_nc_2172 dc_nc_2173 dc_nc_2174 dc_nc_2175
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
