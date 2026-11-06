theory OCX_nc_009
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0144: "oc_sub None 144"
  by (oc_eval oc_nc_0144)

lemma oc_nc_0145: "oc_sub None 145"
  by (oc_eval oc_nc_0145)

lemma oc_nc_0146: "oc_sub None 146"
  by (oc_eval oc_nc_0146)

lemma oc_nc_0147: "oc_sub None 147"
  by (oc_eval oc_nc_0147)

lemma oc_nc_0148: "oc_sub None 148"
  by (oc_eval oc_nc_0148)

lemma oc_nc_0149: "oc_sub None 149"
  by (oc_eval oc_nc_0149)

lemma oc_nc_0150: "oc_sub None 150"
  by (oc_eval oc_nc_0150)

lemma oc_nc_0151: "oc_sub None 151"
  by (oc_eval oc_nc_0151)

lemma oc_nc_0152: "oc_sub None 152"
  by (oc_eval oc_nc_0152)

lemma oc_nc_0153: "oc_sub None 153"
  by (oc_eval oc_nc_0153)

lemma oc_nc_0154: "oc_sub None 154"
  by (oc_eval oc_nc_0154)

lemma oc_nc_0155: "oc_sub None 155"
  by (oc_eval oc_nc_0155)

lemma oc_nc_0156: "oc_sub None 156"
  by (oc_eval oc_nc_0156)

lemma oc_nc_0157: "oc_sub None 157"
  by (oc_eval oc_nc_0157)

lemma oc_nc_0158: "oc_sub None 158"
  by (oc_eval oc_nc_0158)

lemma oc_nc_0159: "oc_sub None 159"
  by (oc_eval oc_nc_0159)

lemma upt_nc_009: "[144..<160] = [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]"
  by (simp add: upt_rec)

lemma sec_nc_009: "\<forall>j\<in>{16 * 9..<16 * 9 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 9..<16 * 9 + 16}"
  then have "j \<in> set [144..<160]" unfolding set_upt by simp
  then have "j \<in> set [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]" unfolding upt_nc_009 .
  then show "oc_sub None j" using oc_nc_0144 oc_nc_0145 oc_nc_0146 oc_nc_0147 oc_nc_0148 oc_nc_0149 oc_nc_0150 oc_nc_0151 oc_nc_0152 oc_nc_0153 oc_nc_0154 oc_nc_0155 oc_nc_0156 oc_nc_0157 oc_nc_0158 oc_nc_0159
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
