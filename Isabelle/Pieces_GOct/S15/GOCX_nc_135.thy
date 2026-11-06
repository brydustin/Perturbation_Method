theory GOCX_nc_135
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2160: "goc_sub None 2160"
  by (goc_eval goc_nc_2160)

lemma goc_nc_2161: "goc_sub None 2161"
  by (goc_eval goc_nc_2161)

lemma goc_nc_2162: "goc_sub None 2162"
  by (goc_eval goc_nc_2162)

lemma goc_nc_2163: "goc_sub None 2163"
  by (goc_eval goc_nc_2163)

lemma goc_nc_2164: "goc_sub None 2164"
  by (goc_eval goc_nc_2164)

lemma goc_nc_2165: "goc_sub None 2165"
  by (goc_eval goc_nc_2165)

lemma goc_nc_2166: "goc_sub None 2166"
  by (goc_eval goc_nc_2166)

lemma goc_nc_2167: "goc_sub None 2167"
  by (goc_eval goc_nc_2167)

lemma goc_nc_2168: "goc_sub None 2168"
  by (goc_eval goc_nc_2168)

lemma goc_nc_2169: "goc_sub None 2169"
  by (goc_eval goc_nc_2169)

lemma goc_nc_2170: "goc_sub None 2170"
  by (goc_eval goc_nc_2170)

lemma goc_nc_2171: "goc_sub None 2171"
  by (goc_eval goc_nc_2171)

lemma goc_nc_2172: "goc_sub None 2172"
  by (goc_eval goc_nc_2172)

lemma goc_nc_2173: "goc_sub None 2173"
  by (goc_eval goc_nc_2173)

lemma goc_nc_2174: "goc_sub None 2174"
  by (goc_eval goc_nc_2174)

lemma goc_nc_2175: "goc_sub None 2175"
  by (goc_eval goc_nc_2175)

lemma gupt_nc_135: "[2160..<2176] = [2160, 2161, 2162, 2163, 2164, 2165, 2166, 2167, 2168, 2169, 2170, 2171, 2172, 2173, 2174, 2175]"
  by (simp add: upt_rec)

lemma gsec_nc_135: "\<forall>j\<in>{16 * 135..<16 * 135 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 135..<16 * 135 + 16}"
  then have "j \<in> set [2160..<2176]" unfolding set_upt by simp
  then have "j \<in> set [2160, 2161, 2162, 2163, 2164, 2165, 2166, 2167, 2168, 2169, 2170, 2171, 2172, 2173, 2174, 2175]" unfolding gupt_nc_135 .
  then show "goc_sub None j" using goc_nc_2160 goc_nc_2161 goc_nc_2162 goc_nc_2163 goc_nc_2164 goc_nc_2165 goc_nc_2166 goc_nc_2167 goc_nc_2168 goc_nc_2169 goc_nc_2170 goc_nc_2171 goc_nc_2172 goc_nc_2173 goc_nc_2174 goc_nc_2175
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
