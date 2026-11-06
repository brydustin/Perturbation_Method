theory GDCX_nc_135
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2160: "gdc_sub None 2160"
  by (gdc_eval gdc_nc_2160)

lemma gdc_nc_2161: "gdc_sub None 2161"
  by (gdc_eval gdc_nc_2161)

lemma gdc_nc_2162: "gdc_sub None 2162"
  by (gdc_eval gdc_nc_2162)

lemma gdc_nc_2163: "gdc_sub None 2163"
  by (gdc_eval gdc_nc_2163)

lemma gdc_nc_2164: "gdc_sub None 2164"
  by (gdc_eval gdc_nc_2164)

lemma gdc_nc_2165: "gdc_sub None 2165"
  by (gdc_eval gdc_nc_2165)

lemma gdc_nc_2166: "gdc_sub None 2166"
  by (gdc_eval gdc_nc_2166)

lemma gdc_nc_2167: "gdc_sub None 2167"
  by (gdc_eval gdc_nc_2167)

lemma gdc_nc_2168: "gdc_sub None 2168"
  by (gdc_eval gdc_nc_2168)

lemma gdc_nc_2169: "gdc_sub None 2169"
  by (gdc_eval gdc_nc_2169)

lemma gdc_nc_2170: "gdc_sub None 2170"
  by (gdc_eval gdc_nc_2170)

lemma gdc_nc_2171: "gdc_sub None 2171"
  by (gdc_eval gdc_nc_2171)

lemma gdc_nc_2172: "gdc_sub None 2172"
  by (gdc_eval gdc_nc_2172)

lemma gdc_nc_2173: "gdc_sub None 2173"
  by (gdc_eval gdc_nc_2173)

lemma gdc_nc_2174: "gdc_sub None 2174"
  by (gdc_eval gdc_nc_2174)

lemma gdc_nc_2175: "gdc_sub None 2175"
  by (gdc_eval gdc_nc_2175)

lemma gupt_nc_135: "[2160..<2176] = [2160, 2161, 2162, 2163, 2164, 2165, 2166, 2167, 2168, 2169, 2170, 2171, 2172, 2173, 2174, 2175]"
  by (simp add: upt_rec)

lemma gsec_nc_135: "\<forall>j\<in>{16 * 135..<16 * 135 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 135..<16 * 135 + 16}"
  then have "j \<in> set [2160..<2176]" unfolding set_upt by simp
  then have "j \<in> set [2160, 2161, 2162, 2163, 2164, 2165, 2166, 2167, 2168, 2169, 2170, 2171, 2172, 2173, 2174, 2175]" unfolding gupt_nc_135 .
  then show "gdc_sub None j" using gdc_nc_2160 gdc_nc_2161 gdc_nc_2162 gdc_nc_2163 gdc_nc_2164 gdc_nc_2165 gdc_nc_2166 gdc_nc_2167 gdc_nc_2168 gdc_nc_2169 gdc_nc_2170 gdc_nc_2171 gdc_nc_2172 gdc_nc_2173 gdc_nc_2174 gdc_nc_2175
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
