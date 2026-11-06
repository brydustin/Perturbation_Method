theory GOCX_nc_011
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0176: "goc_sub None 176"
  by (goc_eval goc_nc_0176)

lemma goc_nc_0177: "goc_sub None 177"
  by (goc_eval goc_nc_0177)

lemma goc_nc_0178: "goc_sub None 178"
  by (goc_eval goc_nc_0178)

lemma goc_nc_0179: "goc_sub None 179"
  by (goc_eval goc_nc_0179)

lemma goc_nc_0180: "goc_sub None 180"
  by (goc_eval goc_nc_0180)

lemma goc_nc_0181: "goc_sub None 181"
  by (goc_eval goc_nc_0181)

lemma goc_nc_0182: "goc_sub None 182"
  by (goc_eval goc_nc_0182)

lemma goc_nc_0183: "goc_sub None 183"
  by (goc_eval goc_nc_0183)

lemma goc_nc_0184: "goc_sub None 184"
  by (goc_eval goc_nc_0184)

lemma goc_nc_0185: "goc_sub None 185"
  by (goc_eval goc_nc_0185)

lemma goc_nc_0186: "goc_sub None 186"
  by (goc_eval goc_nc_0186)

lemma goc_nc_0187: "goc_sub None 187"
  by (goc_eval goc_nc_0187)

lemma goc_nc_0188: "goc_sub None 188"
  by (goc_eval goc_nc_0188)

lemma goc_nc_0189: "goc_sub None 189"
  by (goc_eval goc_nc_0189)

lemma goc_nc_0190: "goc_sub None 190"
  by (goc_eval goc_nc_0190)

lemma goc_nc_0191: "goc_sub None 191"
  by (goc_eval goc_nc_0191)

lemma gupt_nc_011: "[176..<192] = [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]"
  by (simp add: upt_rec)

lemma gsec_nc_011: "\<forall>j\<in>{16 * 11..<16 * 11 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 11..<16 * 11 + 16}"
  then have "j \<in> set [176..<192]" unfolding set_upt by simp
  then have "j \<in> set [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]" unfolding gupt_nc_011 .
  then show "goc_sub None j" using goc_nc_0176 goc_nc_0177 goc_nc_0178 goc_nc_0179 goc_nc_0180 goc_nc_0181 goc_nc_0182 goc_nc_0183 goc_nc_0184 goc_nc_0185 goc_nc_0186 goc_nc_0187 goc_nc_0188 goc_nc_0189 goc_nc_0190 goc_nc_0191
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
