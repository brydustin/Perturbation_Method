theory GOCX_nc_190
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_3040: "goc_sub None 3040"
  by (goc_eval goc_nc_3040)

lemma goc_nc_3041: "goc_sub None 3041"
  by (goc_eval goc_nc_3041)

lemma goc_nc_3042: "goc_sub None 3042"
  by (goc_eval goc_nc_3042)

lemma goc_nc_3043: "goc_sub None 3043"
  by (goc_eval goc_nc_3043)

lemma goc_nc_3044: "goc_sub None 3044"
  by (goc_eval goc_nc_3044)

lemma goc_nc_3045: "goc_sub None 3045"
  by (goc_eval goc_nc_3045)

lemma goc_nc_3046: "goc_sub None 3046"
  by (goc_eval goc_nc_3046)

lemma goc_nc_3047: "goc_sub None 3047"
  by (goc_eval goc_nc_3047)

lemma goc_nc_3048: "goc_sub None 3048"
  by (goc_eval goc_nc_3048)

lemma goc_nc_3049: "goc_sub None 3049"
  by (goc_eval goc_nc_3049)

lemma goc_nc_3050: "goc_sub None 3050"
  by (goc_eval goc_nc_3050)

lemma goc_nc_3051: "goc_sub None 3051"
  by (goc_eval goc_nc_3051)

lemma goc_nc_3052: "goc_sub None 3052"
  by (goc_eval goc_nc_3052)

lemma goc_nc_3053: "goc_sub None 3053"
  by (goc_eval goc_nc_3053)

lemma goc_nc_3054: "goc_sub None 3054"
  by (goc_eval goc_nc_3054)

lemma goc_nc_3055: "goc_sub None 3055"
  by (goc_eval goc_nc_3055)

lemma gupt_nc_190: "[3040..<3056] = [3040, 3041, 3042, 3043, 3044, 3045, 3046, 3047, 3048, 3049, 3050, 3051, 3052, 3053, 3054, 3055]"
  by (simp add: upt_rec)

lemma gsec_nc_190: "\<forall>j\<in>{16 * 190..<16 * 190 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 190..<16 * 190 + 16}"
  then have "j \<in> set [3040..<3056]" unfolding set_upt by simp
  then have "j \<in> set [3040, 3041, 3042, 3043, 3044, 3045, 3046, 3047, 3048, 3049, 3050, 3051, 3052, 3053, 3054, 3055]" unfolding gupt_nc_190 .
  then show "goc_sub None j" using goc_nc_3040 goc_nc_3041 goc_nc_3042 goc_nc_3043 goc_nc_3044 goc_nc_3045 goc_nc_3046 goc_nc_3047 goc_nc_3048 goc_nc_3049 goc_nc_3050 goc_nc_3051 goc_nc_3052 goc_nc_3053 goc_nc_3054 goc_nc_3055
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
