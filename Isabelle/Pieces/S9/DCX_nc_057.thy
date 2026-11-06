theory DCX_nc_057
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0912: "dc_sub None 912"
  by (dc_eval dc_nc_0912)

lemma dc_nc_0913: "dc_sub None 913"
  by (dc_eval dc_nc_0913)

lemma dc_nc_0914: "dc_sub None 914"
  by (dc_eval dc_nc_0914)

lemma dc_nc_0915: "dc_sub None 915"
  by (dc_eval dc_nc_0915)

lemma dc_nc_0916: "dc_sub None 916"
  by (dc_eval dc_nc_0916)

lemma dc_nc_0917: "dc_sub None 917"
  by (dc_eval dc_nc_0917)

lemma dc_nc_0918: "dc_sub None 918"
  by (dc_eval dc_nc_0918)

lemma dc_nc_0919: "dc_sub None 919"
  by (dc_eval dc_nc_0919)

lemma dc_nc_0920: "dc_sub None 920"
  by (dc_eval dc_nc_0920)

lemma dc_nc_0921: "dc_sub None 921"
  by (dc_eval dc_nc_0921)

lemma dc_nc_0922: "dc_sub None 922"
  by (dc_eval dc_nc_0922)

lemma dc_nc_0923: "dc_sub None 923"
  by (dc_eval dc_nc_0923)

lemma dc_nc_0924: "dc_sub None 924"
  by (dc_eval dc_nc_0924)

lemma dc_nc_0925: "dc_sub None 925"
  by (dc_eval dc_nc_0925)

lemma dc_nc_0926: "dc_sub None 926"
  by (dc_eval dc_nc_0926)

lemma dc_nc_0927: "dc_sub None 927"
  by (dc_eval dc_nc_0927)

lemma upt_nc_057: "[912..<928] = [912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927]"
  by (simp add: upt_rec)

lemma sec_nc_057: "\<forall>j\<in>{16 * 57..<16 * 57 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 57..<16 * 57 + 16}"
  then have "j \<in> set [912..<928]" unfolding set_upt by simp
  then have "j \<in> set [912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927]" unfolding upt_nc_057 .
  then show "dc_sub None j" using dc_nc_0912 dc_nc_0913 dc_nc_0914 dc_nc_0915 dc_nc_0916 dc_nc_0917 dc_nc_0918 dc_nc_0919 dc_nc_0920 dc_nc_0921 dc_nc_0922 dc_nc_0923 dc_nc_0924 dc_nc_0925 dc_nc_0926 dc_nc_0927
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
