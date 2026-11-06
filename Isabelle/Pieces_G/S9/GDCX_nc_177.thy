theory GDCX_nc_177
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2832: "gdc_sub None 2832"
  by (gdc_eval gdc_nc_2832)

lemma gdc_nc_2833: "gdc_sub None 2833"
  by (gdc_eval gdc_nc_2833)

lemma gdc_nc_2834: "gdc_sub None 2834"
  by (gdc_eval gdc_nc_2834)

lemma gdc_nc_2835: "gdc_sub None 2835"
  by (gdc_eval gdc_nc_2835)

lemma gdc_nc_2836: "gdc_sub None 2836"
  by (gdc_eval gdc_nc_2836)

lemma gdc_nc_2837: "gdc_sub None 2837"
  by (gdc_eval gdc_nc_2837)

lemma gdc_nc_2838: "gdc_sub None 2838"
  by (gdc_eval gdc_nc_2838)

lemma gdc_nc_2839: "gdc_sub None 2839"
  by (gdc_eval gdc_nc_2839)

lemma gdc_nc_2840: "gdc_sub None 2840"
  by (gdc_eval gdc_nc_2840)

lemma gdc_nc_2841: "gdc_sub None 2841"
  by (gdc_eval gdc_nc_2841)

lemma gdc_nc_2842: "gdc_sub None 2842"
  by (gdc_eval gdc_nc_2842)

lemma gdc_nc_2843: "gdc_sub None 2843"
  by (gdc_eval gdc_nc_2843)

lemma gdc_nc_2844: "gdc_sub None 2844"
  by (gdc_eval gdc_nc_2844)

lemma gdc_nc_2845: "gdc_sub None 2845"
  by (gdc_eval gdc_nc_2845)

lemma gdc_nc_2846: "gdc_sub None 2846"
  by (gdc_eval gdc_nc_2846)

lemma gdc_nc_2847: "gdc_sub None 2847"
  by (gdc_eval gdc_nc_2847)

lemma gupt_nc_177: "[2832..<2848] = [2832, 2833, 2834, 2835, 2836, 2837, 2838, 2839, 2840, 2841, 2842, 2843, 2844, 2845, 2846, 2847]"
  by (simp add: upt_rec)

lemma gsec_nc_177: "\<forall>j\<in>{16 * 177..<16 * 177 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 177..<16 * 177 + 16}"
  then have "j \<in> set [2832..<2848]" unfolding set_upt by simp
  then have "j \<in> set [2832, 2833, 2834, 2835, 2836, 2837, 2838, 2839, 2840, 2841, 2842, 2843, 2844, 2845, 2846, 2847]" unfolding gupt_nc_177 .
  then show "gdc_sub None j" using gdc_nc_2832 gdc_nc_2833 gdc_nc_2834 gdc_nc_2835 gdc_nc_2836 gdc_nc_2837 gdc_nc_2838 gdc_nc_2839 gdc_nc_2840 gdc_nc_2841 gdc_nc_2842 gdc_nc_2843 gdc_nc_2844 gdc_nc_2845 gdc_nc_2846 gdc_nc_2847
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
