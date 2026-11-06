theory DCX_nc_011
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0176: "dc_sub None 176"
  by (dc_eval dc_nc_0176)

lemma dc_nc_0177: "dc_sub None 177"
  by (dc_eval dc_nc_0177)

lemma dc_nc_0178: "dc_sub None 178"
  by (dc_eval dc_nc_0178)

lemma dc_nc_0179: "dc_sub None 179"
  by (dc_eval dc_nc_0179)

lemma dc_nc_0180: "dc_sub None 180"
  by (dc_eval dc_nc_0180)

lemma dc_nc_0181: "dc_sub None 181"
  by (dc_eval dc_nc_0181)

lemma dc_nc_0182: "dc_sub None 182"
  by (dc_eval dc_nc_0182)

lemma dc_nc_0183: "dc_sub None 183"
  by (dc_eval dc_nc_0183)

lemma dc_nc_0184: "dc_sub None 184"
  by (dc_eval dc_nc_0184)

lemma dc_nc_0185: "dc_sub None 185"
  by (dc_eval dc_nc_0185)

lemma dc_nc_0186: "dc_sub None 186"
  by (dc_eval dc_nc_0186)

lemma dc_nc_0187: "dc_sub None 187"
  by (dc_eval dc_nc_0187)

lemma dc_nc_0188: "dc_sub None 188"
  by (dc_eval dc_nc_0188)

lemma dc_nc_0189: "dc_sub None 189"
  by (dc_eval dc_nc_0189)

lemma dc_nc_0190: "dc_sub None 190"
  by (dc_eval dc_nc_0190)

lemma dc_nc_0191: "dc_sub None 191"
  by (dc_eval dc_nc_0191)

lemma upt_nc_011: "[176..<192] = [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]"
  by (simp add: upt_rec)

lemma sec_nc_011: "\<forall>j\<in>{16 * 11..<16 * 11 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 11..<16 * 11 + 16}"
  then have "j \<in> set [176..<192]" unfolding set_upt by simp
  then have "j \<in> set [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]" unfolding upt_nc_011 .
  then show "dc_sub None j" using dc_nc_0176 dc_nc_0177 dc_nc_0178 dc_nc_0179 dc_nc_0180 dc_nc_0181 dc_nc_0182 dc_nc_0183 dc_nc_0184 dc_nc_0185 dc_nc_0186 dc_nc_0187 dc_nc_0188 dc_nc_0189 dc_nc_0190 dc_nc_0191
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
