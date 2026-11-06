theory DCX_nc_182
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2912: "dc_sub None 2912"
  by (dc_eval dc_nc_2912)

lemma dc_nc_2913: "dc_sub None 2913"
  by (dc_eval dc_nc_2913)

lemma dc_nc_2914: "dc_sub None 2914"
  by (dc_eval dc_nc_2914)

lemma dc_nc_2915: "dc_sub None 2915"
  by (dc_eval dc_nc_2915)

lemma dc_nc_2916: "dc_sub None 2916"
  by (dc_eval dc_nc_2916)

lemma dc_nc_2917: "dc_sub None 2917"
  by (dc_eval dc_nc_2917)

lemma dc_nc_2918: "dc_sub None 2918"
  by (dc_eval dc_nc_2918)

lemma dc_nc_2919: "dc_sub None 2919"
  by (dc_eval dc_nc_2919)

lemma dc_nc_2920: "dc_sub None 2920"
  by (dc_eval dc_nc_2920)

lemma dc_nc_2921: "dc_sub None 2921"
  by (dc_eval dc_nc_2921)

lemma dc_nc_2922: "dc_sub None 2922"
  by (dc_eval dc_nc_2922)

lemma dc_nc_2923: "dc_sub None 2923"
  by (dc_eval dc_nc_2923)

lemma dc_nc_2924: "dc_sub None 2924"
  by (dc_eval dc_nc_2924)

lemma dc_nc_2925: "dc_sub None 2925"
  by (dc_eval dc_nc_2925)

lemma dc_nc_2926: "dc_sub None 2926"
  by (dc_eval dc_nc_2926)

lemma dc_nc_2927: "dc_sub None 2927"
  by (dc_eval dc_nc_2927)

lemma upt_nc_182: "[2912..<2928] = [2912, 2913, 2914, 2915, 2916, 2917, 2918, 2919, 2920, 2921, 2922, 2923, 2924, 2925, 2926, 2927]"
  by (simp add: upt_rec)

lemma sec_nc_182: "\<forall>j\<in>{16 * 182..<16 * 182 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 182..<16 * 182 + 16}"
  then have "j \<in> set [2912..<2928]" unfolding set_upt by simp
  then have "j \<in> set [2912, 2913, 2914, 2915, 2916, 2917, 2918, 2919, 2920, 2921, 2922, 2923, 2924, 2925, 2926, 2927]" unfolding upt_nc_182 .
  then show "dc_sub None j" using dc_nc_2912 dc_nc_2913 dc_nc_2914 dc_nc_2915 dc_nc_2916 dc_nc_2917 dc_nc_2918 dc_nc_2919 dc_nc_2920 dc_nc_2921 dc_nc_2922 dc_nc_2923 dc_nc_2924 dc_nc_2925 dc_nc_2926 dc_nc_2927
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
