theory DCX_nc_009
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0144: "dc_sub None 144"
  by (dc_eval dc_nc_0144)

lemma dc_nc_0145: "dc_sub None 145"
  by (dc_eval dc_nc_0145)

lemma dc_nc_0146: "dc_sub None 146"
  by (dc_eval dc_nc_0146)

lemma dc_nc_0147: "dc_sub None 147"
  by (dc_eval dc_nc_0147)

lemma dc_nc_0148: "dc_sub None 148"
  by (dc_eval dc_nc_0148)

lemma dc_nc_0149: "dc_sub None 149"
  by (dc_eval dc_nc_0149)

lemma dc_nc_0150: "dc_sub None 150"
  by (dc_eval dc_nc_0150)

lemma dc_nc_0151: "dc_sub None 151"
  by (dc_eval dc_nc_0151)

lemma dc_nc_0152: "dc_sub None 152"
  by (dc_eval dc_nc_0152)

lemma dc_nc_0153: "dc_sub None 153"
  by (dc_eval dc_nc_0153)

lemma dc_nc_0154: "dc_sub None 154"
  by (dc_eval dc_nc_0154)

lemma dc_nc_0155: "dc_sub None 155"
  by (dc_eval dc_nc_0155)

lemma dc_nc_0156: "dc_sub None 156"
  by (dc_eval dc_nc_0156)

lemma dc_nc_0157: "dc_sub None 157"
  by (dc_eval dc_nc_0157)

lemma dc_nc_0158: "dc_sub None 158"
  by (dc_eval dc_nc_0158)

lemma dc_nc_0159: "dc_sub None 159"
  by (dc_eval dc_nc_0159)

lemma upt_nc_009: "[144..<160] = [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]"
  by (simp add: upt_rec)

lemma sec_nc_009: "\<forall>j\<in>{16 * 9..<16 * 9 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 9..<16 * 9 + 16}"
  then have "j \<in> set [144..<160]" unfolding set_upt by simp
  then have "j \<in> set [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]" unfolding upt_nc_009 .
  then show "dc_sub None j" using dc_nc_0144 dc_nc_0145 dc_nc_0146 dc_nc_0147 dc_nc_0148 dc_nc_0149 dc_nc_0150 dc_nc_0151 dc_nc_0152 dc_nc_0153 dc_nc_0154 dc_nc_0155 dc_nc_0156 dc_nc_0157 dc_nc_0158 dc_nc_0159
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
