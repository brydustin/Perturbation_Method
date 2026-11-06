theory DCX_c30_187
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2992: "dc_sub dc_b30 2992"
  by (dc_eval dc_c30_2992)

lemma dc_c30_2993: "dc_sub dc_b30 2993"
  by (dc_eval dc_c30_2993)

lemma dc_c30_2994: "dc_sub dc_b30 2994"
  by (dc_eval dc_c30_2994)

lemma dc_c30_2995: "dc_sub dc_b30 2995"
  by (dc_eval dc_c30_2995)

lemma dc_c30_2996: "dc_sub dc_b30 2996"
  by (dc_eval dc_c30_2996)

lemma dc_c30_2997: "dc_sub dc_b30 2997"
  by (dc_eval dc_c30_2997)

lemma dc_c30_2998: "dc_sub dc_b30 2998"
  by (dc_eval dc_c30_2998)

lemma dc_c30_2999: "dc_sub dc_b30 2999"
  by (dc_eval dc_c30_2999)

lemma dc_c30_3000: "dc_sub dc_b30 3000"
  by (dc_eval dc_c30_3000)

lemma dc_c30_3001: "dc_sub dc_b30 3001"
  by (dc_eval dc_c30_3001)

lemma dc_c30_3002: "dc_sub dc_b30 3002"
  by (dc_eval dc_c30_3002)

lemma dc_c30_3003: "dc_sub dc_b30 3003"
  by (dc_eval dc_c30_3003)

lemma dc_c30_3004: "dc_sub dc_b30 3004"
  by (dc_eval dc_c30_3004)

lemma dc_c30_3005: "dc_sub dc_b30 3005"
  by (dc_eval dc_c30_3005)

lemma dc_c30_3006: "dc_sub dc_b30 3006"
  by (dc_eval dc_c30_3006)

lemma dc_c30_3007: "dc_sub dc_b30 3007"
  by (dc_eval dc_c30_3007)

lemma upt_c30_187: "[2992..<3008] = [2992, 2993, 2994, 2995, 2996, 2997, 2998, 2999, 3000, 3001, 3002, 3003, 3004, 3005, 3006, 3007]"
  by (simp add: upt_rec)

lemma sec_c30_187: "\<forall>j\<in>{16 * 187..<16 * 187 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 187..<16 * 187 + 16}"
  then have "j \<in> set [2992..<3008]" unfolding set_upt by simp
  then have "j \<in> set [2992, 2993, 2994, 2995, 2996, 2997, 2998, 2999, 3000, 3001, 3002, 3003, 3004, 3005, 3006, 3007]" unfolding upt_c30_187 .
  then show "dc_sub dc_b30 j" using dc_c30_2992 dc_c30_2993 dc_c30_2994 dc_c30_2995 dc_c30_2996 dc_c30_2997 dc_c30_2998 dc_c30_2999 dc_c30_3000 dc_c30_3001 dc_c30_3002 dc_c30_3003 dc_c30_3004 dc_c30_3005 dc_c30_3006 dc_c30_3007
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
