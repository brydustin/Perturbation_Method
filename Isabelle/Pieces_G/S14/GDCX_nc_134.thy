theory GDCX_nc_134
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2144: "gdc_sub None 2144"
  by (gdc_eval gdc_nc_2144)

lemma gdc_nc_2145: "gdc_sub None 2145"
  by (gdc_eval gdc_nc_2145)

lemma gdc_nc_2146: "gdc_sub None 2146"
  by (gdc_eval gdc_nc_2146)

lemma gdc_nc_2147: "gdc_sub None 2147"
  by (gdc_eval gdc_nc_2147)

lemma gdc_nc_2148: "gdc_sub None 2148"
  by (gdc_eval gdc_nc_2148)

lemma gdc_nc_2149: "gdc_sub None 2149"
  by (gdc_eval gdc_nc_2149)

lemma gdc_nc_2150: "gdc_sub None 2150"
  by (gdc_eval gdc_nc_2150)

lemma gdc_nc_2151: "gdc_sub None 2151"
  by (gdc_eval gdc_nc_2151)

lemma gdc_nc_2152: "gdc_sub None 2152"
  by (gdc_eval gdc_nc_2152)

lemma gdc_nc_2153: "gdc_sub None 2153"
  by (gdc_eval gdc_nc_2153)

lemma gdc_nc_2154: "gdc_sub None 2154"
  by (gdc_eval gdc_nc_2154)

lemma gdc_nc_2155: "gdc_sub None 2155"
  by (gdc_eval gdc_nc_2155)

lemma gdc_nc_2156: "gdc_sub None 2156"
  by (gdc_eval gdc_nc_2156)

lemma gdc_nc_2157: "gdc_sub None 2157"
  by (gdc_eval gdc_nc_2157)

lemma gdc_nc_2158: "gdc_sub None 2158"
  by (gdc_eval gdc_nc_2158)

lemma gdc_nc_2159: "gdc_sub None 2159"
  by (gdc_eval gdc_nc_2159)

lemma gupt_nc_134: "[2144..<2160] = [2144, 2145, 2146, 2147, 2148, 2149, 2150, 2151, 2152, 2153, 2154, 2155, 2156, 2157, 2158, 2159]"
  by (simp add: upt_rec)

lemma gsec_nc_134: "\<forall>j\<in>{16 * 134..<16 * 134 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 134..<16 * 134 + 16}"
  then have "j \<in> set [2144..<2160]" unfolding set_upt by simp
  then have "j \<in> set [2144, 2145, 2146, 2147, 2148, 2149, 2150, 2151, 2152, 2153, 2154, 2155, 2156, 2157, 2158, 2159]" unfolding gupt_nc_134 .
  then show "gdc_sub None j" using gdc_nc_2144 gdc_nc_2145 gdc_nc_2146 gdc_nc_2147 gdc_nc_2148 gdc_nc_2149 gdc_nc_2150 gdc_nc_2151 gdc_nc_2152 gdc_nc_2153 gdc_nc_2154 gdc_nc_2155 gdc_nc_2156 gdc_nc_2157 gdc_nc_2158 gdc_nc_2159
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
