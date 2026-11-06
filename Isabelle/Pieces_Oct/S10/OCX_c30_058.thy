theory OCX_c30_058
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0928: "oc_sub oc_b30 928"
  by (oc_eval oc_c30_0928)

lemma oc_c30_0929: "oc_sub oc_b30 929"
  by (oc_eval oc_c30_0929)

lemma oc_c30_0930: "oc_sub oc_b30 930"
  by (oc_eval oc_c30_0930)

lemma oc_c30_0931: "oc_sub oc_b30 931"
  by (oc_eval oc_c30_0931)

lemma oc_c30_0932: "oc_sub oc_b30 932"
  by (oc_eval oc_c30_0932)

lemma oc_c30_0933: "oc_sub oc_b30 933"
  by (oc_eval oc_c30_0933)

lemma oc_c30_0934: "oc_sub oc_b30 934"
  by (oc_eval oc_c30_0934)

lemma oc_c30_0935: "oc_sub oc_b30 935"
  by (oc_eval oc_c30_0935)

lemma oc_c30_0936: "oc_sub oc_b30 936"
  by (oc_eval oc_c30_0936)

lemma oc_c30_0937: "oc_sub oc_b30 937"
  by (oc_eval oc_c30_0937)

lemma oc_c30_0938: "oc_sub oc_b30 938"
  by (oc_eval oc_c30_0938)

lemma oc_c30_0939: "oc_sub oc_b30 939"
  by (oc_eval oc_c30_0939)

lemma oc_c30_0940: "oc_sub oc_b30 940"
  by (oc_eval oc_c30_0940)

lemma oc_c30_0941: "oc_sub oc_b30 941"
  by (oc_eval oc_c30_0941)

lemma oc_c30_0942: "oc_sub oc_b30 942"
  by (oc_eval oc_c30_0942)

lemma oc_c30_0943: "oc_sub oc_b30 943"
  by (oc_eval oc_c30_0943)

lemma upt_c30_058: "[928..<944] = [928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943]"
  by (simp add: upt_rec)

lemma sec_c30_058: "\<forall>j\<in>{16 * 58..<16 * 58 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 58..<16 * 58 + 16}"
  then have "j \<in> set [928..<944]" unfolding set_upt by simp
  then have "j \<in> set [928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943]" unfolding upt_c30_058 .
  then show "oc_sub oc_b30 j" using oc_c30_0928 oc_c30_0929 oc_c30_0930 oc_c30_0931 oc_c30_0932 oc_c30_0933 oc_c30_0934 oc_c30_0935 oc_c30_0936 oc_c30_0937 oc_c30_0938 oc_c30_0939 oc_c30_0940 oc_c30_0941 oc_c30_0942 oc_c30_0943
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
