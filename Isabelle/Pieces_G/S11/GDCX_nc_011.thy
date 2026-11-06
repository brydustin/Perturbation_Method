theory GDCX_nc_011
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0176: "gdc_sub None 176"
  by (gdc_eval gdc_nc_0176)

lemma gdc_nc_0177: "gdc_sub None 177"
  by (gdc_eval gdc_nc_0177)

lemma gdc_nc_0178: "gdc_sub None 178"
  by (gdc_eval gdc_nc_0178)

lemma gdc_nc_0179: "gdc_sub None 179"
  by (gdc_eval gdc_nc_0179)

lemma gdc_nc_0180: "gdc_sub None 180"
  by (gdc_eval gdc_nc_0180)

lemma gdc_nc_0181: "gdc_sub None 181"
  by (gdc_eval gdc_nc_0181)

lemma gdc_nc_0182: "gdc_sub None 182"
  by (gdc_eval gdc_nc_0182)

lemma gdc_nc_0183: "gdc_sub None 183"
  by (gdc_eval gdc_nc_0183)

lemma gdc_nc_0184: "gdc_sub None 184"
  by (gdc_eval gdc_nc_0184)

lemma gdc_nc_0185: "gdc_sub None 185"
  by (gdc_eval gdc_nc_0185)

lemma gdc_nc_0186: "gdc_sub None 186"
  by (gdc_eval gdc_nc_0186)

lemma gdc_nc_0187: "gdc_sub None 187"
  by (gdc_eval gdc_nc_0187)

lemma gdc_nc_0188: "gdc_sub None 188"
  by (gdc_eval gdc_nc_0188)

lemma gdc_nc_0189: "gdc_sub None 189"
  by (gdc_eval gdc_nc_0189)

lemma gdc_nc_0190: "gdc_sub None 190"
  by (gdc_eval gdc_nc_0190)

lemma gdc_nc_0191: "gdc_sub None 191"
  by (gdc_eval gdc_nc_0191)

lemma gupt_nc_011: "[176..<192] = [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]"
  by (simp add: upt_rec)

lemma gsec_nc_011: "\<forall>j\<in>{16 * 11..<16 * 11 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 11..<16 * 11 + 16}"
  then have "j \<in> set [176..<192]" unfolding set_upt by simp
  then have "j \<in> set [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]" unfolding gupt_nc_011 .
  then show "gdc_sub None j" using gdc_nc_0176 gdc_nc_0177 gdc_nc_0178 gdc_nc_0179 gdc_nc_0180 gdc_nc_0181 gdc_nc_0182 gdc_nc_0183 gdc_nc_0184 gdc_nc_0185 gdc_nc_0186 gdc_nc_0187 gdc_nc_0188 gdc_nc_0189 gdc_nc_0190 gdc_nc_0191
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
