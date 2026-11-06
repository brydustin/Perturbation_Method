theory OCX_c30_009
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0144: "oc_sub oc_b30 144"
  by (oc_eval oc_c30_0144)

lemma oc_c30_0145: "oc_sub oc_b30 145"
  by (oc_eval oc_c30_0145)

lemma oc_c30_0146: "oc_sub oc_b30 146"
  by (oc_eval oc_c30_0146)

lemma oc_c30_0147: "oc_sub oc_b30 147"
  by (oc_eval oc_c30_0147)

lemma oc_c30_0148: "oc_sub oc_b30 148"
  by (oc_eval oc_c30_0148)

lemma oc_c30_0149: "oc_sub oc_b30 149"
  by (oc_eval oc_c30_0149)

lemma oc_c30_0150: "oc_sub oc_b30 150"
  by (oc_eval oc_c30_0150)

lemma oc_c30_0151: "oc_sub oc_b30 151"
  by (oc_eval oc_c30_0151)

lemma oc_c30_0152: "oc_sub oc_b30 152"
  by (oc_eval oc_c30_0152)

lemma oc_c30_0153: "oc_sub oc_b30 153"
  by (oc_eval oc_c30_0153)

lemma oc_c30_0154: "oc_sub oc_b30 154"
  by (oc_eval oc_c30_0154)

lemma oc_c30_0155: "oc_sub oc_b30 155"
  by (oc_eval oc_c30_0155)

lemma oc_c30_0156: "oc_sub oc_b30 156"
  by (oc_eval oc_c30_0156)

lemma oc_c30_0157: "oc_sub oc_b30 157"
  by (oc_eval oc_c30_0157)

lemma oc_c30_0158: "oc_sub oc_b30 158"
  by (oc_eval oc_c30_0158)

lemma oc_c30_0159: "oc_sub oc_b30 159"
  by (oc_eval oc_c30_0159)

lemma upt_c30_009: "[144..<160] = [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]"
  by (simp add: upt_rec)

lemma sec_c30_009: "\<forall>j\<in>{16 * 9..<16 * 9 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 9..<16 * 9 + 16}"
  then have "j \<in> set [144..<160]" unfolding set_upt by simp
  then have "j \<in> set [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]" unfolding upt_c30_009 .
  then show "oc_sub oc_b30 j" using oc_c30_0144 oc_c30_0145 oc_c30_0146 oc_c30_0147 oc_c30_0148 oc_c30_0149 oc_c30_0150 oc_c30_0151 oc_c30_0152 oc_c30_0153 oc_c30_0154 oc_c30_0155 oc_c30_0156 oc_c30_0157 oc_c30_0158 oc_c30_0159
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
