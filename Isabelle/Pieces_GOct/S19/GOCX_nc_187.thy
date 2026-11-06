theory GOCX_nc_187
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2992: "goc_sub None 2992"
  by (goc_eval goc_nc_2992)

lemma goc_nc_2993: "goc_sub None 2993"
  by (goc_eval goc_nc_2993)

lemma goc_nc_2994: "goc_sub None 2994"
  by (goc_eval goc_nc_2994)

lemma goc_nc_2995: "goc_sub None 2995"
  by (goc_eval goc_nc_2995)

lemma goc_nc_2996: "goc_sub None 2996"
  by (goc_eval goc_nc_2996)

lemma goc_nc_2997: "goc_sub None 2997"
  by (goc_eval goc_nc_2997)

lemma goc_nc_2998: "goc_sub None 2998"
  by (goc_eval goc_nc_2998)

lemma goc_nc_2999: "goc_sub None 2999"
  by (goc_eval goc_nc_2999)

lemma goc_nc_3000: "goc_sub None 3000"
  by (goc_eval goc_nc_3000)

lemma goc_nc_3001: "goc_sub None 3001"
  by (goc_eval goc_nc_3001)

lemma goc_nc_3002: "goc_sub None 3002"
  by (goc_eval goc_nc_3002)

lemma goc_nc_3003: "goc_sub None 3003"
  by (goc_eval goc_nc_3003)

lemma goc_nc_3004: "goc_sub None 3004"
  by (goc_eval goc_nc_3004)

lemma goc_nc_3005: "goc_sub None 3005"
  by (goc_eval goc_nc_3005)

lemma goc_nc_3006: "goc_sub None 3006"
  by (goc_eval goc_nc_3006)

lemma goc_nc_3007: "goc_sub None 3007"
  by (goc_eval goc_nc_3007)

lemma gupt_nc_187: "[2992..<3008] = [2992, 2993, 2994, 2995, 2996, 2997, 2998, 2999, 3000, 3001, 3002, 3003, 3004, 3005, 3006, 3007]"
  by (simp add: upt_rec)

lemma gsec_nc_187: "\<forall>j\<in>{16 * 187..<16 * 187 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 187..<16 * 187 + 16}"
  then have "j \<in> set [2992..<3008]" unfolding set_upt by simp
  then have "j \<in> set [2992, 2993, 2994, 2995, 2996, 2997, 2998, 2999, 3000, 3001, 3002, 3003, 3004, 3005, 3006, 3007]" unfolding gupt_nc_187 .
  then show "goc_sub None j" using goc_nc_2992 goc_nc_2993 goc_nc_2994 goc_nc_2995 goc_nc_2996 goc_nc_2997 goc_nc_2998 goc_nc_2999 goc_nc_3000 goc_nc_3001 goc_nc_3002 goc_nc_3003 goc_nc_3004 goc_nc_3005 goc_nc_3006 goc_nc_3007
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
