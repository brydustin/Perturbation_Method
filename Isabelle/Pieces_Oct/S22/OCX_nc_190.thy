theory OCX_nc_190
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_3040: "oc_sub None 3040"
  by (oc_eval oc_nc_3040)

lemma oc_nc_3041: "oc_sub None 3041"
  by (oc_eval oc_nc_3041)

lemma oc_nc_3042: "oc_sub None 3042"
  by (oc_eval oc_nc_3042)

lemma oc_nc_3043: "oc_sub None 3043"
  by (oc_eval oc_nc_3043)

lemma oc_nc_3044: "oc_sub None 3044"
  by (oc_eval oc_nc_3044)

lemma oc_nc_3045: "oc_sub None 3045"
  by (oc_eval oc_nc_3045)

lemma oc_nc_3046: "oc_sub None 3046"
  by (oc_eval oc_nc_3046)

lemma oc_nc_3047: "oc_sub None 3047"
  by (oc_eval oc_nc_3047)

lemma oc_nc_3048: "oc_sub None 3048"
  by (oc_eval oc_nc_3048)

lemma oc_nc_3049: "oc_sub None 3049"
  by (oc_eval oc_nc_3049)

lemma oc_nc_3050: "oc_sub None 3050"
  by (oc_eval oc_nc_3050)

lemma oc_nc_3051: "oc_sub None 3051"
  by (oc_eval oc_nc_3051)

lemma oc_nc_3052: "oc_sub None 3052"
  by (oc_eval oc_nc_3052)

lemma oc_nc_3053: "oc_sub None 3053"
  by (oc_eval oc_nc_3053)

lemma oc_nc_3054: "oc_sub None 3054"
  by (oc_eval oc_nc_3054)

lemma oc_nc_3055: "oc_sub None 3055"
  by (oc_eval oc_nc_3055)

lemma upt_nc_190: "[3040..<3056] = [3040, 3041, 3042, 3043, 3044, 3045, 3046, 3047, 3048, 3049, 3050, 3051, 3052, 3053, 3054, 3055]"
  by (simp add: upt_rec)

lemma sec_nc_190: "\<forall>j\<in>{16 * 190..<16 * 190 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 190..<16 * 190 + 16}"
  then have "j \<in> set [3040..<3056]" unfolding set_upt by simp
  then have "j \<in> set [3040, 3041, 3042, 3043, 3044, 3045, 3046, 3047, 3048, 3049, 3050, 3051, 3052, 3053, 3054, 3055]" unfolding upt_nc_190 .
  then show "oc_sub None j" using oc_nc_3040 oc_nc_3041 oc_nc_3042 oc_nc_3043 oc_nc_3044 oc_nc_3045 oc_nc_3046 oc_nc_3047 oc_nc_3048 oc_nc_3049 oc_nc_3050 oc_nc_3051 oc_nc_3052 oc_nc_3053 oc_nc_3054 oc_nc_3055
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
