theory DCX_nc_187
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2992: "dc_sub None 2992"
  by (dc_eval dc_nc_2992)

lemma dc_nc_2993: "dc_sub None 2993"
  by (dc_eval dc_nc_2993)

lemma dc_nc_2994: "dc_sub None 2994"
  by (dc_eval dc_nc_2994)

lemma dc_nc_2995: "dc_sub None 2995"
  by (dc_eval dc_nc_2995)

lemma dc_nc_2996: "dc_sub None 2996"
  by (dc_eval dc_nc_2996)

lemma dc_nc_2997: "dc_sub None 2997"
  by (dc_eval dc_nc_2997)

lemma dc_nc_2998: "dc_sub None 2998"
  by (dc_eval dc_nc_2998)

lemma dc_nc_2999: "dc_sub None 2999"
  by (dc_eval dc_nc_2999)

lemma dc_nc_3000: "dc_sub None 3000"
  by (dc_eval dc_nc_3000)

lemma dc_nc_3001: "dc_sub None 3001"
  by (dc_eval dc_nc_3001)

lemma dc_nc_3002: "dc_sub None 3002"
  by (dc_eval dc_nc_3002)

lemma dc_nc_3003: "dc_sub None 3003"
  by (dc_eval dc_nc_3003)

lemma dc_nc_3004: "dc_sub None 3004"
  by (dc_eval dc_nc_3004)

lemma dc_nc_3005: "dc_sub None 3005"
  by (dc_eval dc_nc_3005)

lemma dc_nc_3006: "dc_sub None 3006"
  by (dc_eval dc_nc_3006)

lemma dc_nc_3007: "dc_sub None 3007"
  by (dc_eval dc_nc_3007)

lemma upt_nc_187: "[2992..<3008] = [2992, 2993, 2994, 2995, 2996, 2997, 2998, 2999, 3000, 3001, 3002, 3003, 3004, 3005, 3006, 3007]"
  by (simp add: upt_rec)

lemma sec_nc_187: "\<forall>j\<in>{16 * 187..<16 * 187 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 187..<16 * 187 + 16}"
  then have "j \<in> set [2992..<3008]" unfolding set_upt by simp
  then have "j \<in> set [2992, 2993, 2994, 2995, 2996, 2997, 2998, 2999, 3000, 3001, 3002, 3003, 3004, 3005, 3006, 3007]" unfolding upt_nc_187 .
  then show "dc_sub None j" using dc_nc_2992 dc_nc_2993 dc_nc_2994 dc_nc_2995 dc_nc_2996 dc_nc_2997 dc_nc_2998 dc_nc_2999 dc_nc_3000 dc_nc_3001 dc_nc_3002 dc_nc_3003 dc_nc_3004 dc_nc_3005 dc_nc_3006 dc_nc_3007
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
