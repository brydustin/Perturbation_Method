theory OCX_nc_011
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0176: "oc_sub None 176"
  by (oc_eval oc_nc_0176)

lemma oc_nc_0177: "oc_sub None 177"
  by (oc_eval oc_nc_0177)

lemma oc_nc_0178: "oc_sub None 178"
  by (oc_eval oc_nc_0178)

lemma oc_nc_0179: "oc_sub None 179"
  by (oc_eval oc_nc_0179)

lemma oc_nc_0180: "oc_sub None 180"
  by (oc_eval oc_nc_0180)

lemma oc_nc_0181: "oc_sub None 181"
  by (oc_eval oc_nc_0181)

lemma oc_nc_0182: "oc_sub None 182"
  by (oc_eval oc_nc_0182)

lemma oc_nc_0183: "oc_sub None 183"
  by (oc_eval oc_nc_0183)

lemma oc_nc_0184: "oc_sub None 184"
  by (oc_eval oc_nc_0184)

lemma oc_nc_0185: "oc_sub None 185"
  by (oc_eval oc_nc_0185)

lemma oc_nc_0186: "oc_sub None 186"
  by (oc_eval oc_nc_0186)

lemma oc_nc_0187: "oc_sub None 187"
  by (oc_eval oc_nc_0187)

lemma oc_nc_0188: "oc_sub None 188"
  by (oc_eval oc_nc_0188)

lemma oc_nc_0189: "oc_sub None 189"
  by (oc_eval oc_nc_0189)

lemma oc_nc_0190: "oc_sub None 190"
  by (oc_eval oc_nc_0190)

lemma oc_nc_0191: "oc_sub None 191"
  by (oc_eval oc_nc_0191)

lemma upt_nc_011: "[176..<192] = [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]"
  by (simp add: upt_rec)

lemma sec_nc_011: "\<forall>j\<in>{16 * 11..<16 * 11 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 11..<16 * 11 + 16}"
  then have "j \<in> set [176..<192]" unfolding set_upt by simp
  then have "j \<in> set [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]" unfolding upt_nc_011 .
  then show "oc_sub None j" using oc_nc_0176 oc_nc_0177 oc_nc_0178 oc_nc_0179 oc_nc_0180 oc_nc_0181 oc_nc_0182 oc_nc_0183 oc_nc_0184 oc_nc_0185 oc_nc_0186 oc_nc_0187 oc_nc_0188 oc_nc_0189 oc_nc_0190 oc_nc_0191
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
