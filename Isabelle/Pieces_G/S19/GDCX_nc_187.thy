theory GDCX_nc_187
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2992: "gdc_sub None 2992"
  by (gdc_eval gdc_nc_2992)

lemma gdc_nc_2993: "gdc_sub None 2993"
  by (gdc_eval gdc_nc_2993)

lemma gdc_nc_2994: "gdc_sub None 2994"
  by (gdc_eval gdc_nc_2994)

lemma gdc_nc_2995: "gdc_sub None 2995"
  by (gdc_eval gdc_nc_2995)

lemma gdc_nc_2996: "gdc_sub None 2996"
  by (gdc_eval gdc_nc_2996)

lemma gdc_nc_2997: "gdc_sub None 2997"
  by (gdc_eval gdc_nc_2997)

lemma gdc_nc_2998: "gdc_sub None 2998"
  by (gdc_eval gdc_nc_2998)

lemma gdc_nc_2999: "gdc_sub None 2999"
  by (gdc_eval gdc_nc_2999)

lemma gdc_nc_3000: "gdc_sub None 3000"
  by (gdc_eval gdc_nc_3000)

lemma gdc_nc_3001: "gdc_sub None 3001"
  by (gdc_eval gdc_nc_3001)

lemma gdc_nc_3002: "gdc_sub None 3002"
  by (gdc_eval gdc_nc_3002)

lemma gdc_nc_3003: "gdc_sub None 3003"
  by (gdc_eval gdc_nc_3003)

lemma gdc_nc_3004: "gdc_sub None 3004"
  by (gdc_eval gdc_nc_3004)

lemma gdc_nc_3005: "gdc_sub None 3005"
  by (gdc_eval gdc_nc_3005)

lemma gdc_nc_3006: "gdc_sub None 3006"
  by (gdc_eval gdc_nc_3006)

lemma gdc_nc_3007: "gdc_sub None 3007"
  by (gdc_eval gdc_nc_3007)

lemma gupt_nc_187: "[2992..<3008] = [2992, 2993, 2994, 2995, 2996, 2997, 2998, 2999, 3000, 3001, 3002, 3003, 3004, 3005, 3006, 3007]"
  by (simp add: upt_rec)

lemma gsec_nc_187: "\<forall>j\<in>{16 * 187..<16 * 187 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 187..<16 * 187 + 16}"
  then have "j \<in> set [2992..<3008]" unfolding set_upt by simp
  then have "j \<in> set [2992, 2993, 2994, 2995, 2996, 2997, 2998, 2999, 3000, 3001, 3002, 3003, 3004, 3005, 3006, 3007]" unfolding gupt_nc_187 .
  then show "gdc_sub None j" using gdc_nc_2992 gdc_nc_2993 gdc_nc_2994 gdc_nc_2995 gdc_nc_2996 gdc_nc_2997 gdc_nc_2998 gdc_nc_2999 gdc_nc_3000 gdc_nc_3001 gdc_nc_3002 gdc_nc_3003 gdc_nc_3004 gdc_nc_3005 gdc_nc_3006 gdc_nc_3007
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
