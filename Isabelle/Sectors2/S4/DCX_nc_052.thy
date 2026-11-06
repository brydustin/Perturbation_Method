theory DCX_nc_052
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0832: "dc_sub None 832"
  by (dc_eval dc_nc_0832)

lemma dc_nc_0833: "dc_sub None 833"
  by (dc_eval dc_nc_0833)

lemma dc_nc_0834: "dc_sub None 834"
  by (dc_eval dc_nc_0834)

lemma dc_nc_0835: "dc_sub None 835"
  by (dc_eval dc_nc_0835)

lemma dc_nc_0836: "dc_sub None 836"
  by (dc_eval dc_nc_0836)

lemma dc_nc_0837: "dc_sub None 837"
  by (dc_eval dc_nc_0837)

lemma dc_nc_0838: "dc_sub None 838"
  by (dc_eval dc_nc_0838)

lemma dc_nc_0839: "dc_sub None 839"
  by (dc_eval dc_nc_0839)

lemma dc_nc_0840: "dc_sub None 840"
  by (dc_eval dc_nc_0840)

lemma dc_nc_0841: "dc_sub None 841"
  by (dc_eval dc_nc_0841)

lemma dc_nc_0842: "dc_sub None 842"
  by (dc_eval dc_nc_0842)

lemma dc_nc_0843: "dc_sub None 843"
  by (dc_eval dc_nc_0843)

lemma dc_nc_0844: "dc_sub None 844"
  by (dc_eval dc_nc_0844)

lemma dc_nc_0845: "dc_sub None 845"
  by (dc_eval dc_nc_0845)

lemma dc_nc_0846: "dc_sub None 846"
  by (dc_eval dc_nc_0846)

lemma dc_nc_0847: "dc_sub None 847"
  by (dc_eval dc_nc_0847)

lemma upt_nc_052: "[832..<848] = [832, 833, 834, 835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847]"
  by (simp add: upt_rec)

lemma sec_nc_052: "\<forall>j\<in>{16 * 52..<16 * 52 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 52..<16 * 52 + 16}"
  then have "j \<in> set [832..<848]" unfolding set_upt by simp
  then have "j \<in> set [832, 833, 834, 835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847]" unfolding upt_nc_052 .
  then show "dc_sub None j" using dc_nc_0832 dc_nc_0833 dc_nc_0834 dc_nc_0835 dc_nc_0836 dc_nc_0837 dc_nc_0838 dc_nc_0839 dc_nc_0840 dc_nc_0841 dc_nc_0842 dc_nc_0843 dc_nc_0844 dc_nc_0845 dc_nc_0846 dc_nc_0847
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
