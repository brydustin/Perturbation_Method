theory DCX_c30_009
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0144: "dc_sub dc_b30 144"
  by (dc_eval dc_c30_0144)

lemma dc_c30_0145: "dc_sub dc_b30 145"
  by (dc_eval dc_c30_0145)

lemma dc_c30_0146: "dc_sub dc_b30 146"
  by (dc_eval dc_c30_0146)

lemma dc_c30_0147: "dc_sub dc_b30 147"
  by (dc_eval dc_c30_0147)

lemma dc_c30_0148: "dc_sub dc_b30 148"
  by (dc_eval dc_c30_0148)

lemma dc_c30_0149: "dc_sub dc_b30 149"
  by (dc_eval dc_c30_0149)

lemma dc_c30_0150: "dc_sub dc_b30 150"
  by (dc_eval dc_c30_0150)

lemma dc_c30_0151: "dc_sub dc_b30 151"
  by (dc_eval dc_c30_0151)

lemma dc_c30_0152: "dc_sub dc_b30 152"
  by (dc_eval dc_c30_0152)

lemma dc_c30_0153: "dc_sub dc_b30 153"
  by (dc_eval dc_c30_0153)

lemma dc_c30_0154: "dc_sub dc_b30 154"
  by (dc_eval dc_c30_0154)

lemma dc_c30_0155: "dc_sub dc_b30 155"
  by (dc_eval dc_c30_0155)

lemma dc_c30_0156: "dc_sub dc_b30 156"
  by (dc_eval dc_c30_0156)

lemma dc_c30_0157: "dc_sub dc_b30 157"
  by (dc_eval dc_c30_0157)

lemma dc_c30_0158: "dc_sub dc_b30 158"
  by (dc_eval dc_c30_0158)

lemma dc_c30_0159: "dc_sub dc_b30 159"
  by (dc_eval dc_c30_0159)

lemma upt_c30_009: "[144..<160] = [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]"
  by (simp add: upt_rec)

lemma sec_c30_009: "\<forall>j\<in>{16 * 9..<16 * 9 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 9..<16 * 9 + 16}"
  then have "j \<in> set [144..<160]" unfolding set_upt by simp
  then have "j \<in> set [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]" unfolding upt_c30_009 .
  then show "dc_sub dc_b30 j" using dc_c30_0144 dc_c30_0145 dc_c30_0146 dc_c30_0147 dc_c30_0148 dc_c30_0149 dc_c30_0150 dc_c30_0151 dc_c30_0152 dc_c30_0153 dc_c30_0154 dc_c30_0155 dc_c30_0156 dc_c30_0157 dc_c30_0158 dc_c30_0159
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
