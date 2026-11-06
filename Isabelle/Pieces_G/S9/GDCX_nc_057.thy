theory GDCX_nc_057
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0912: "gdc_sub None 912"
  by (gdc_eval gdc_nc_0912)

lemma gdc_nc_0913: "gdc_sub None 913"
  by (gdc_eval gdc_nc_0913)

lemma gdc_nc_0914: "gdc_sub None 914"
  by (gdc_eval gdc_nc_0914)

lemma gdc_nc_0915: "gdc_sub None 915"
  by (gdc_eval gdc_nc_0915)

lemma gdc_nc_0916: "gdc_sub None 916"
  by (gdc_eval gdc_nc_0916)

lemma gdc_nc_0917: "gdc_sub None 917"
  by (gdc_eval gdc_nc_0917)

lemma gdc_nc_0918: "gdc_sub None 918"
  by (gdc_eval gdc_nc_0918)

lemma gdc_nc_0919: "gdc_sub None 919"
  by (gdc_eval gdc_nc_0919)

lemma gdc_nc_0920: "gdc_sub None 920"
  by (gdc_eval gdc_nc_0920)

lemma gdc_nc_0921: "gdc_sub None 921"
  by (gdc_eval gdc_nc_0921)

lemma gdc_nc_0922: "gdc_sub None 922"
  by (gdc_eval gdc_nc_0922)

lemma gdc_nc_0923: "gdc_sub None 923"
  by (gdc_eval gdc_nc_0923)

lemma gdc_nc_0924: "gdc_sub None 924"
  by (gdc_eval gdc_nc_0924)

lemma gdc_nc_0925: "gdc_sub None 925"
  by (gdc_eval gdc_nc_0925)

lemma gdc_nc_0926: "gdc_sub None 926"
  by (gdc_eval gdc_nc_0926)

lemma gdc_nc_0927: "gdc_sub None 927"
  by (gdc_eval gdc_nc_0927)

lemma gupt_nc_057: "[912..<928] = [912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927]"
  by (simp add: upt_rec)

lemma gsec_nc_057: "\<forall>j\<in>{16 * 57..<16 * 57 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 57..<16 * 57 + 16}"
  then have "j \<in> set [912..<928]" unfolding set_upt by simp
  then have "j \<in> set [912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927]" unfolding gupt_nc_057 .
  then show "gdc_sub None j" using gdc_nc_0912 gdc_nc_0913 gdc_nc_0914 gdc_nc_0915 gdc_nc_0916 gdc_nc_0917 gdc_nc_0918 gdc_nc_0919 gdc_nc_0920 gdc_nc_0921 gdc_nc_0922 gdc_nc_0923 gdc_nc_0924 gdc_nc_0925 gdc_nc_0926 gdc_nc_0927
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
