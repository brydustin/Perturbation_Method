theory OCX_c30_187
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2992: "oc_sub oc_b30 2992"
  by (oc_eval oc_c30_2992)

lemma oc_c30_2993: "oc_sub oc_b30 2993"
  by (oc_eval oc_c30_2993)

lemma oc_c30_2994: "oc_sub oc_b30 2994"
  by (oc_eval oc_c30_2994)

lemma oc_c30_2995: "oc_sub oc_b30 2995"
  by (oc_eval oc_c30_2995)

lemma oc_c30_2996: "oc_sub oc_b30 2996"
  by (oc_eval oc_c30_2996)

lemma oc_c30_2997: "oc_sub oc_b30 2997"
  by (oc_eval oc_c30_2997)

lemma oc_c30_2998: "oc_sub oc_b30 2998"
  by (oc_eval oc_c30_2998)

lemma oc_c30_2999: "oc_sub oc_b30 2999"
  by (oc_eval oc_c30_2999)

lemma oc_c30_3000: "oc_sub oc_b30 3000"
  by (oc_eval oc_c30_3000)

lemma oc_c30_3001: "oc_sub oc_b30 3001"
  by (oc_eval oc_c30_3001)

lemma oc_c30_3002: "oc_sub oc_b30 3002"
  by (oc_eval oc_c30_3002)

lemma oc_c30_3003: "oc_sub oc_b30 3003"
  by (oc_eval oc_c30_3003)

lemma oc_c30_3004: "oc_sub oc_b30 3004"
  by (oc_eval oc_c30_3004)

lemma oc_c30_3005: "oc_sub oc_b30 3005"
  by (oc_eval oc_c30_3005)

lemma oc_c30_3006: "oc_sub oc_b30 3006"
  by (oc_eval oc_c30_3006)

lemma oc_c30_3007: "oc_sub oc_b30 3007"
  by (oc_eval oc_c30_3007)

lemma upt_c30_187: "[2992..<3008] = [2992, 2993, 2994, 2995, 2996, 2997, 2998, 2999, 3000, 3001, 3002, 3003, 3004, 3005, 3006, 3007]"
  by (simp add: upt_rec)

lemma sec_c30_187: "\<forall>j\<in>{16 * 187..<16 * 187 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 187..<16 * 187 + 16}"
  then have "j \<in> set [2992..<3008]" unfolding set_upt by simp
  then have "j \<in> set [2992, 2993, 2994, 2995, 2996, 2997, 2998, 2999, 3000, 3001, 3002, 3003, 3004, 3005, 3006, 3007]" unfolding upt_c30_187 .
  then show "oc_sub oc_b30 j" using oc_c30_2992 oc_c30_2993 oc_c30_2994 oc_c30_2995 oc_c30_2996 oc_c30_2997 oc_c30_2998 oc_c30_2999 oc_c30_3000 oc_c30_3001 oc_c30_3002 oc_c30_3003 oc_c30_3004 oc_c30_3005 oc_c30_3006 oc_c30_3007
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
