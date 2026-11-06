theory DCX_nc_008
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0128: "dc_sub None 128"
  by (dc_eval dc_nc_0128)

lemma dc_nc_0129: "dc_sub None 129"
  by (dc_eval dc_nc_0129)

lemma dc_nc_0130: "dc_sub None 130"
  by (dc_eval dc_nc_0130)

lemma dc_nc_0131: "dc_sub None 131"
  by (dc_eval dc_nc_0131)

lemma dc_nc_0132: "dc_sub None 132"
  by (dc_eval dc_nc_0132)

lemma dc_nc_0133: "dc_sub None 133"
  by (dc_eval dc_nc_0133)

lemma dc_nc_0134: "dc_sub None 134"
  by (dc_eval dc_nc_0134)

lemma dc_nc_0135: "dc_sub None 135"
  by (dc_eval dc_nc_0135)

lemma dc_nc_0136: "dc_sub None 136"
  by (dc_eval dc_nc_0136)

lemma dc_nc_0137: "dc_sub None 137"
  by (dc_eval dc_nc_0137)

lemma dc_nc_0138: "dc_sub None 138"
  by (dc_eval dc_nc_0138)

lemma dc_nc_0139: "dc_sub None 139"
  by (dc_eval dc_nc_0139)

lemma dc_nc_0140: "dc_sub None 140"
  by (dc_eval dc_nc_0140)

lemma dc_nc_0141: "dc_sub None 141"
  by (dc_eval dc_nc_0141)

lemma dc_nc_0142: "dc_sub None 142"
  by (dc_eval dc_nc_0142)

lemma dc_nc_0143: "dc_sub None 143"
  by (dc_eval dc_nc_0143)

lemma upt_nc_008: "[128..<144] = [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]"
  by (simp add: upt_rec)

lemma sec_nc_008: "\<forall>j\<in>{16 * 8..<16 * 8 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 8..<16 * 8 + 16}"
  then have "j \<in> set [128..<144]" unfolding set_upt by simp
  then have "j \<in> set [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]" unfolding upt_nc_008 .
  then show "dc_sub None j" using dc_nc_0128 dc_nc_0129 dc_nc_0130 dc_nc_0131 dc_nc_0132 dc_nc_0133 dc_nc_0134 dc_nc_0135 dc_nc_0136 dc_nc_0137 dc_nc_0138 dc_nc_0139 dc_nc_0140 dc_nc_0141 dc_nc_0142 dc_nc_0143
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
