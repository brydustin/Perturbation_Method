theory GOCX_nc_182
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2912: "goc_sub None 2912"
  by (goc_eval goc_nc_2912)

lemma goc_nc_2913: "goc_sub None 2913"
  by (goc_eval goc_nc_2913)

lemma goc_nc_2914: "goc_sub None 2914"
  by (goc_eval goc_nc_2914)

lemma goc_nc_2915: "goc_sub None 2915"
  by (goc_eval goc_nc_2915)

lemma goc_nc_2916: "goc_sub None 2916"
  by (goc_eval goc_nc_2916)

lemma goc_nc_2917: "goc_sub None 2917"
  by (goc_eval goc_nc_2917)

lemma goc_nc_2918: "goc_sub None 2918"
  by (goc_eval goc_nc_2918)

lemma goc_nc_2919: "goc_sub None 2919"
  by (goc_eval goc_nc_2919)

lemma goc_nc_2920: "goc_sub None 2920"
  by (goc_eval goc_nc_2920)

lemma goc_nc_2921: "goc_sub None 2921"
  by (goc_eval goc_nc_2921)

lemma goc_nc_2922: "goc_sub None 2922"
  by (goc_eval goc_nc_2922)

lemma goc_nc_2923: "goc_sub None 2923"
  by (goc_eval goc_nc_2923)

lemma goc_nc_2924: "goc_sub None 2924"
  by (goc_eval goc_nc_2924)

lemma goc_nc_2925: "goc_sub None 2925"
  by (goc_eval goc_nc_2925)

lemma goc_nc_2926: "goc_sub None 2926"
  by (goc_eval goc_nc_2926)

lemma goc_nc_2927: "goc_sub None 2927"
  by (goc_eval goc_nc_2927)

lemma gupt_nc_182: "[2912..<2928] = [2912, 2913, 2914, 2915, 2916, 2917, 2918, 2919, 2920, 2921, 2922, 2923, 2924, 2925, 2926, 2927]"
  by (simp add: upt_rec)

lemma gsec_nc_182: "\<forall>j\<in>{16 * 182..<16 * 182 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 182..<16 * 182 + 16}"
  then have "j \<in> set [2912..<2928]" unfolding set_upt by simp
  then have "j \<in> set [2912, 2913, 2914, 2915, 2916, 2917, 2918, 2919, 2920, 2921, 2922, 2923, 2924, 2925, 2926, 2927]" unfolding gupt_nc_182 .
  then show "goc_sub None j" using goc_nc_2912 goc_nc_2913 goc_nc_2914 goc_nc_2915 goc_nc_2916 goc_nc_2917 goc_nc_2918 goc_nc_2919 goc_nc_2920 goc_nc_2921 goc_nc_2922 goc_nc_2923 goc_nc_2924 goc_nc_2925 goc_nc_2926 goc_nc_2927
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
