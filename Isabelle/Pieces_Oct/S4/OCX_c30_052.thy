theory OCX_c30_052
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0832: "oc_sub oc_b30 832"
  by (oc_eval oc_c30_0832)

lemma oc_c30_0833: "oc_sub oc_b30 833"
  by (oc_eval oc_c30_0833)

lemma oc_c30_0834: "oc_sub oc_b30 834"
  by (oc_eval oc_c30_0834)

lemma oc_c30_0835: "oc_sub oc_b30 835"
  by (oc_eval oc_c30_0835)

lemma oc_c30_0836: "oc_sub oc_b30 836"
  by (oc_eval oc_c30_0836)

lemma oc_c30_0837: "oc_sub oc_b30 837"
  by (oc_eval oc_c30_0837)

lemma oc_c30_0838: "oc_sub oc_b30 838"
  by (oc_eval oc_c30_0838)

lemma oc_c30_0839: "oc_sub oc_b30 839"
  by (oc_eval oc_c30_0839)

lemma oc_c30_0840: "oc_sub oc_b30 840"
  by (oc_eval oc_c30_0840)

lemma oc_c30_0841: "oc_sub oc_b30 841"
  by (oc_eval oc_c30_0841)

lemma oc_c30_0842: "oc_sub oc_b30 842"
  by (oc_eval oc_c30_0842)

lemma oc_c30_0843: "oc_sub oc_b30 843"
  by (oc_eval oc_c30_0843)

lemma oc_c30_0844: "oc_sub oc_b30 844"
  by (oc_eval oc_c30_0844)

lemma oc_c30_0845: "oc_sub oc_b30 845"
  by (oc_eval oc_c30_0845)

lemma oc_c30_0846: "oc_sub oc_b30 846"
  by (oc_eval oc_c30_0846)

lemma oc_c30_0847: "oc_sub oc_b30 847"
  by (oc_eval oc_c30_0847)

lemma upt_c30_052: "[832..<848] = [832, 833, 834, 835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847]"
  by (simp add: upt_rec)

lemma sec_c30_052: "\<forall>j\<in>{16 * 52..<16 * 52 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 52..<16 * 52 + 16}"
  then have "j \<in> set [832..<848]" unfolding set_upt by simp
  then have "j \<in> set [832, 833, 834, 835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847]" unfolding upt_c30_052 .
  then show "oc_sub oc_b30 j" using oc_c30_0832 oc_c30_0833 oc_c30_0834 oc_c30_0835 oc_c30_0836 oc_c30_0837 oc_c30_0838 oc_c30_0839 oc_c30_0840 oc_c30_0841 oc_c30_0842 oc_c30_0843 oc_c30_0844 oc_c30_0845 oc_c30_0846 oc_c30_0847
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
