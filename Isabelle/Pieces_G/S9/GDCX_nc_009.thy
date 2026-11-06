theory GDCX_nc_009
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0144: "gdc_sub None 144"
  by (gdc_eval gdc_nc_0144)

lemma gdc_nc_0145: "gdc_sub None 145"
  by (gdc_eval gdc_nc_0145)

lemma gdc_nc_0146: "gdc_sub None 146"
  by (gdc_eval gdc_nc_0146)

lemma gdc_nc_0147: "gdc_sub None 147"
  by (gdc_eval gdc_nc_0147)

lemma gdc_nc_0148: "gdc_sub None 148"
  by (gdc_eval gdc_nc_0148)

lemma gdc_nc_0149: "gdc_sub None 149"
  by (gdc_eval gdc_nc_0149)

lemma gdc_nc_0150: "gdc_sub None 150"
  by (gdc_eval gdc_nc_0150)

lemma gdc_nc_0151: "gdc_sub None 151"
  by (gdc_eval gdc_nc_0151)

lemma gdc_nc_0152: "gdc_sub None 152"
  by (gdc_eval gdc_nc_0152)

lemma gdc_nc_0153: "gdc_sub None 153"
  by (gdc_eval gdc_nc_0153)

lemma gdc_nc_0154: "gdc_sub None 154"
  by (gdc_eval gdc_nc_0154)

lemma gdc_nc_0155: "gdc_sub None 155"
  by (gdc_eval gdc_nc_0155)

lemma gdc_nc_0156: "gdc_sub None 156"
  by (gdc_eval gdc_nc_0156)

lemma gdc_nc_0157: "gdc_sub None 157"
  by (gdc_eval gdc_nc_0157)

lemma gdc_nc_0158: "gdc_sub None 158"
  by (gdc_eval gdc_nc_0158)

lemma gdc_nc_0159: "gdc_sub None 159"
  by (gdc_eval gdc_nc_0159)

lemma gupt_nc_009: "[144..<160] = [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]"
  by (simp add: upt_rec)

lemma gsec_nc_009: "\<forall>j\<in>{16 * 9..<16 * 9 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 9..<16 * 9 + 16}"
  then have "j \<in> set [144..<160]" unfolding set_upt by simp
  then have "j \<in> set [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]" unfolding gupt_nc_009 .
  then show "gdc_sub None j" using gdc_nc_0144 gdc_nc_0145 gdc_nc_0146 gdc_nc_0147 gdc_nc_0148 gdc_nc_0149 gdc_nc_0150 gdc_nc_0151 gdc_nc_0152 gdc_nc_0153 gdc_nc_0154 gdc_nc_0155 gdc_nc_0156 gdc_nc_0157 gdc_nc_0158 gdc_nc_0159
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
