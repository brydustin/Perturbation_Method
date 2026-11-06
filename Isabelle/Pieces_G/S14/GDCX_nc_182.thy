theory GDCX_nc_182
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2912: "gdc_sub None 2912"
  by (gdc_eval gdc_nc_2912)

lemma gdc_nc_2913: "gdc_sub None 2913"
  by (gdc_eval gdc_nc_2913)

lemma gdc_nc_2914: "gdc_sub None 2914"
  by (gdc_eval gdc_nc_2914)

lemma gdc_nc_2915: "gdc_sub None 2915"
  by (gdc_eval gdc_nc_2915)

lemma gdc_nc_2916: "gdc_sub None 2916"
  by (gdc_eval gdc_nc_2916)

lemma gdc_nc_2917: "gdc_sub None 2917"
  by (gdc_eval gdc_nc_2917)

lemma gdc_nc_2918: "gdc_sub None 2918"
  by (gdc_eval gdc_nc_2918)

lemma gdc_nc_2919: "gdc_sub None 2919"
  by (gdc_eval gdc_nc_2919)

lemma gdc_nc_2920: "gdc_sub None 2920"
  by (gdc_eval gdc_nc_2920)

lemma gdc_nc_2921: "gdc_sub None 2921"
  by (gdc_eval gdc_nc_2921)

lemma gdc_nc_2922: "gdc_sub None 2922"
  by (gdc_eval gdc_nc_2922)

lemma gdc_nc_2923: "gdc_sub None 2923"
  by (gdc_eval gdc_nc_2923)

lemma gdc_nc_2924: "gdc_sub None 2924"
  by (gdc_eval gdc_nc_2924)

lemma gdc_nc_2925: "gdc_sub None 2925"
  by (gdc_eval gdc_nc_2925)

lemma gdc_nc_2926: "gdc_sub None 2926"
  by (gdc_eval gdc_nc_2926)

lemma gdc_nc_2927: "gdc_sub None 2927"
  by (gdc_eval gdc_nc_2927)

lemma gupt_nc_182: "[2912..<2928] = [2912, 2913, 2914, 2915, 2916, 2917, 2918, 2919, 2920, 2921, 2922, 2923, 2924, 2925, 2926, 2927]"
  by (simp add: upt_rec)

lemma gsec_nc_182: "\<forall>j\<in>{16 * 182..<16 * 182 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 182..<16 * 182 + 16}"
  then have "j \<in> set [2912..<2928]" unfolding set_upt by simp
  then have "j \<in> set [2912, 2913, 2914, 2915, 2916, 2917, 2918, 2919, 2920, 2921, 2922, 2923, 2924, 2925, 2926, 2927]" unfolding gupt_nc_182 .
  then show "gdc_sub None j" using gdc_nc_2912 gdc_nc_2913 gdc_nc_2914 gdc_nc_2915 gdc_nc_2916 gdc_nc_2917 gdc_nc_2918 gdc_nc_2919 gdc_nc_2920 gdc_nc_2921 gdc_nc_2922 gdc_nc_2923 gdc_nc_2924 gdc_nc_2925 gdc_nc_2926 gdc_nc_2927
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
