theory GOCX_nc_057
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0912: "goc_sub None 912"
  by (goc_eval goc_nc_0912)

lemma goc_nc_0913: "goc_sub None 913"
  by (goc_eval goc_nc_0913)

lemma goc_nc_0914: "goc_sub None 914"
  by (goc_eval goc_nc_0914)

lemma goc_nc_0915: "goc_sub None 915"
  by (goc_eval goc_nc_0915)

lemma goc_nc_0916: "goc_sub None 916"
  by (goc_eval goc_nc_0916)

lemma goc_nc_0917: "goc_sub None 917"
  by (goc_eval goc_nc_0917)

lemma goc_nc_0918: "goc_sub None 918"
  by (goc_eval goc_nc_0918)

lemma goc_nc_0919: "goc_sub None 919"
  by (goc_eval goc_nc_0919)

lemma goc_nc_0920: "goc_sub None 920"
  by (goc_eval goc_nc_0920)

lemma goc_nc_0921: "goc_sub None 921"
  by (goc_eval goc_nc_0921)

lemma goc_nc_0922: "goc_sub None 922"
  by (goc_eval goc_nc_0922)

lemma goc_nc_0923: "goc_sub None 923"
  by (goc_eval goc_nc_0923)

lemma goc_nc_0924: "goc_sub None 924"
  by (goc_eval goc_nc_0924)

lemma goc_nc_0925: "goc_sub None 925"
  by (goc_eval goc_nc_0925)

lemma goc_nc_0926: "goc_sub None 926"
  by (goc_eval goc_nc_0926)

lemma goc_nc_0927: "goc_sub None 927"
  by (goc_eval goc_nc_0927)

lemma gupt_nc_057: "[912..<928] = [912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927]"
  by (simp add: upt_rec)

lemma gsec_nc_057: "\<forall>j\<in>{16 * 57..<16 * 57 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 57..<16 * 57 + 16}"
  then have "j \<in> set [912..<928]" unfolding set_upt by simp
  then have "j \<in> set [912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927]" unfolding gupt_nc_057 .
  then show "goc_sub None j" using goc_nc_0912 goc_nc_0913 goc_nc_0914 goc_nc_0915 goc_nc_0916 goc_nc_0917 goc_nc_0918 goc_nc_0919 goc_nc_0920 goc_nc_0921 goc_nc_0922 goc_nc_0923 goc_nc_0924 goc_nc_0925 goc_nc_0926 goc_nc_0927
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
