theory OCX_nc_187
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2992: "oc_sub None 2992"
  by (oc_eval oc_nc_2992)

lemma oc_nc_2993: "oc_sub None 2993"
  by (oc_eval oc_nc_2993)

lemma oc_nc_2994: "oc_sub None 2994"
  by (oc_eval oc_nc_2994)

lemma oc_nc_2995: "oc_sub None 2995"
  by (oc_eval oc_nc_2995)

lemma oc_nc_2996: "oc_sub None 2996"
  by (oc_eval oc_nc_2996)

lemma oc_nc_2997: "oc_sub None 2997"
  by (oc_eval oc_nc_2997)

lemma oc_nc_2998: "oc_sub None 2998"
  by (oc_eval oc_nc_2998)

lemma oc_nc_2999: "oc_sub None 2999"
  by (oc_eval oc_nc_2999)

lemma oc_nc_3000: "oc_sub None 3000"
  by (oc_eval oc_nc_3000)

lemma oc_nc_3001: "oc_sub None 3001"
  by (oc_eval oc_nc_3001)

lemma oc_nc_3002: "oc_sub None 3002"
  by (oc_eval oc_nc_3002)

lemma oc_nc_3003: "oc_sub None 3003"
  by (oc_eval oc_nc_3003)

lemma oc_nc_3004: "oc_sub None 3004"
  by (oc_eval oc_nc_3004)

lemma oc_nc_3005: "oc_sub None 3005"
  by (oc_eval oc_nc_3005)

lemma oc_nc_3006: "oc_sub None 3006"
  by (oc_eval oc_nc_3006)

lemma oc_nc_3007: "oc_sub None 3007"
  by (oc_eval oc_nc_3007)

lemma upt_nc_187: "[2992..<3008] = [2992, 2993, 2994, 2995, 2996, 2997, 2998, 2999, 3000, 3001, 3002, 3003, 3004, 3005, 3006, 3007]"
  by (simp add: upt_rec)

lemma sec_nc_187: "\<forall>j\<in>{16 * 187..<16 * 187 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 187..<16 * 187 + 16}"
  then have "j \<in> set [2992..<3008]" unfolding set_upt by simp
  then have "j \<in> set [2992, 2993, 2994, 2995, 2996, 2997, 2998, 2999, 3000, 3001, 3002, 3003, 3004, 3005, 3006, 3007]" unfolding upt_nc_187 .
  then show "oc_sub None j" using oc_nc_2992 oc_nc_2993 oc_nc_2994 oc_nc_2995 oc_nc_2996 oc_nc_2997 oc_nc_2998 oc_nc_2999 oc_nc_3000 oc_nc_3001 oc_nc_3002 oc_nc_3003 oc_nc_3004 oc_nc_3005 oc_nc_3006 oc_nc_3007
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
