theory DCX_c30_058
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0928: "dc_sub dc_b30 928"
  by (dc_eval dc_c30_0928)

lemma dc_c30_0929: "dc_sub dc_b30 929"
  by (dc_eval dc_c30_0929)

lemma dc_c30_0930: "dc_sub dc_b30 930"
  by (dc_eval dc_c30_0930)

lemma dc_c30_0931: "dc_sub dc_b30 931"
  by (dc_eval dc_c30_0931)

lemma dc_c30_0932: "dc_sub dc_b30 932"
  by (dc_eval dc_c30_0932)

lemma dc_c30_0933: "dc_sub dc_b30 933"
  by (dc_eval dc_c30_0933)

lemma dc_c30_0934: "dc_sub dc_b30 934"
  by (dc_eval dc_c30_0934)

lemma dc_c30_0935: "dc_sub dc_b30 935"
  by (dc_eval dc_c30_0935)

lemma dc_c30_0936: "dc_sub dc_b30 936"
  by (dc_eval dc_c30_0936)

lemma dc_c30_0937: "dc_sub dc_b30 937"
  by (dc_eval dc_c30_0937)

lemma dc_c30_0938: "dc_sub dc_b30 938"
  by (dc_eval dc_c30_0938)

lemma dc_c30_0939: "dc_sub dc_b30 939"
  by (dc_eval dc_c30_0939)

lemma dc_c30_0940: "dc_sub dc_b30 940"
  by (dc_eval dc_c30_0940)

lemma dc_c30_0941: "dc_sub dc_b30 941"
  by (dc_eval dc_c30_0941)

lemma dc_c30_0942: "dc_sub dc_b30 942"
  by (dc_eval dc_c30_0942)

lemma dc_c30_0943: "dc_sub dc_b30 943"
  by (dc_eval dc_c30_0943)

lemma upt_c30_058: "[928..<944] = [928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943]"
  by (simp add: upt_rec)

lemma sec_c30_058: "\<forall>j\<in>{16 * 58..<16 * 58 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 58..<16 * 58 + 16}"
  then have "j \<in> set [928..<944]" unfolding set_upt by simp
  then have "j \<in> set [928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943]" unfolding upt_c30_058 .
  then show "dc_sub dc_b30 j" using dc_c30_0928 dc_c30_0929 dc_c30_0930 dc_c30_0931 dc_c30_0932 dc_c30_0933 dc_c30_0934 dc_c30_0935 dc_c30_0936 dc_c30_0937 dc_c30_0938 dc_c30_0939 dc_c30_0940 dc_c30_0941 dc_c30_0942 dc_c30_0943
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
