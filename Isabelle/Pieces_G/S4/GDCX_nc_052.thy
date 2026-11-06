theory GDCX_nc_052
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0832: "gdc_sub None 832"
  by (gdc_eval gdc_nc_0832)

lemma gdc_nc_0833: "gdc_sub None 833"
  by (gdc_eval gdc_nc_0833)

lemma gdc_nc_0834: "gdc_sub None 834"
  by (gdc_eval gdc_nc_0834)

lemma gdc_nc_0835: "gdc_sub None 835"
  by (gdc_eval gdc_nc_0835)

lemma gdc_nc_0836: "gdc_sub None 836"
  by (gdc_eval gdc_nc_0836)

lemma gdc_nc_0837: "gdc_sub None 837"
  by (gdc_eval gdc_nc_0837)

lemma gdc_nc_0838: "gdc_sub None 838"
  by (gdc_eval gdc_nc_0838)

lemma gdc_nc_0839: "gdc_sub None 839"
  by (gdc_eval gdc_nc_0839)

lemma gdc_nc_0840: "gdc_sub None 840"
  by (gdc_eval gdc_nc_0840)

lemma gdc_nc_0841: "gdc_sub None 841"
  by (gdc_eval gdc_nc_0841)

lemma gdc_nc_0842: "gdc_sub None 842"
  by (gdc_eval gdc_nc_0842)

lemma gdc_nc_0843: "gdc_sub None 843"
  by (gdc_eval gdc_nc_0843)

lemma gdc_nc_0844: "gdc_sub None 844"
  by (gdc_eval gdc_nc_0844)

lemma gdc_nc_0845: "gdc_sub None 845"
  by (gdc_eval gdc_nc_0845)

lemma gdc_nc_0846: "gdc_sub None 846"
  by (gdc_eval gdc_nc_0846)

lemma gdc_nc_0847: "gdc_sub None 847"
  by (gdc_eval gdc_nc_0847)

lemma gupt_nc_052: "[832..<848] = [832, 833, 834, 835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847]"
  by (simp add: upt_rec)

lemma gsec_nc_052: "\<forall>j\<in>{16 * 52..<16 * 52 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 52..<16 * 52 + 16}"
  then have "j \<in> set [832..<848]" unfolding set_upt by simp
  then have "j \<in> set [832, 833, 834, 835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847]" unfolding gupt_nc_052 .
  then show "gdc_sub None j" using gdc_nc_0832 gdc_nc_0833 gdc_nc_0834 gdc_nc_0835 gdc_nc_0836 gdc_nc_0837 gdc_nc_0838 gdc_nc_0839 gdc_nc_0840 gdc_nc_0841 gdc_nc_0842 gdc_nc_0843 gdc_nc_0844 gdc_nc_0845 gdc_nc_0846 gdc_nc_0847
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
