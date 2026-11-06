theory DCX_c30_052
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0832: "dc_sub dc_b30 832"
  by (dc_eval dc_c30_0832)

lemma dc_c30_0833: "dc_sub dc_b30 833"
  by (dc_eval dc_c30_0833)

lemma dc_c30_0834: "dc_sub dc_b30 834"
  by (dc_eval dc_c30_0834)

lemma dc_c30_0835: "dc_sub dc_b30 835"
  by (dc_eval dc_c30_0835)

lemma dc_c30_0836: "dc_sub dc_b30 836"
  by (dc_eval dc_c30_0836)

lemma dc_c30_0837: "dc_sub dc_b30 837"
  by (dc_eval dc_c30_0837)

lemma dc_c30_0838: "dc_sub dc_b30 838"
  by (dc_eval dc_c30_0838)

lemma dc_c30_0839: "dc_sub dc_b30 839"
  by (dc_eval dc_c30_0839)

lemma dc_c30_0840: "dc_sub dc_b30 840"
  by (dc_eval dc_c30_0840)

lemma dc_c30_0841: "dc_sub dc_b30 841"
  by (dc_eval dc_c30_0841)

lemma dc_c30_0842: "dc_sub dc_b30 842"
  by (dc_eval dc_c30_0842)

lemma dc_c30_0843: "dc_sub dc_b30 843"
  by (dc_eval dc_c30_0843)

lemma dc_c30_0844: "dc_sub dc_b30 844"
  by (dc_eval dc_c30_0844)

lemma dc_c30_0845: "dc_sub dc_b30 845"
  by (dc_eval dc_c30_0845)

lemma dc_c30_0846: "dc_sub dc_b30 846"
  by (dc_eval dc_c30_0846)

lemma dc_c30_0847: "dc_sub dc_b30 847"
  by (dc_eval dc_c30_0847)

lemma upt_c30_052: "[832..<848] = [832, 833, 834, 835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847]"
  by (simp add: upt_rec)

lemma sec_c30_052: "\<forall>j\<in>{16 * 52..<16 * 52 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 52..<16 * 52 + 16}"
  then have "j \<in> set [832..<848]" unfolding set_upt by simp
  then have "j \<in> set [832, 833, 834, 835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847]" unfolding upt_c30_052 .
  then show "dc_sub dc_b30 j" using dc_c30_0832 dc_c30_0833 dc_c30_0834 dc_c30_0835 dc_c30_0836 dc_c30_0837 dc_c30_0838 dc_c30_0839 dc_c30_0840 dc_c30_0841 dc_c30_0842 dc_c30_0843 dc_c30_0844 dc_c30_0845 dc_c30_0846 dc_c30_0847
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
