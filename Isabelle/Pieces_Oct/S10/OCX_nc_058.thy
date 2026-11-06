theory OCX_nc_058
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0928: "oc_sub None 928"
  by (oc_eval oc_nc_0928)

lemma oc_nc_0929: "oc_sub None 929"
  by (oc_eval oc_nc_0929)

lemma oc_nc_0930: "oc_sub None 930"
  by (oc_eval oc_nc_0930)

lemma oc_nc_0931: "oc_sub None 931"
  by (oc_eval oc_nc_0931)

lemma oc_nc_0932: "oc_sub None 932"
  by (oc_eval oc_nc_0932)

lemma oc_nc_0933: "oc_sub None 933"
  by (oc_eval oc_nc_0933)

lemma oc_nc_0934: "oc_sub None 934"
  by (oc_eval oc_nc_0934)

lemma oc_nc_0935: "oc_sub None 935"
  by (oc_eval oc_nc_0935)

lemma oc_nc_0936: "oc_sub None 936"
  by (oc_eval oc_nc_0936)

lemma oc_nc_0937: "oc_sub None 937"
  by (oc_eval oc_nc_0937)

lemma oc_nc_0938: "oc_sub None 938"
  by (oc_eval oc_nc_0938)

lemma oc_nc_0939: "oc_sub None 939"
  by (oc_eval oc_nc_0939)

lemma oc_nc_0940: "oc_sub None 940"
  by (oc_eval oc_nc_0940)

lemma oc_nc_0941: "oc_sub None 941"
  by (oc_eval oc_nc_0941)

lemma oc_nc_0942: "oc_sub None 942"
  by (oc_eval oc_nc_0942)

lemma oc_nc_0943: "oc_sub None 943"
  by (oc_eval oc_nc_0943)

lemma upt_nc_058: "[928..<944] = [928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943]"
  by (simp add: upt_rec)

lemma sec_nc_058: "\<forall>j\<in>{16 * 58..<16 * 58 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 58..<16 * 58 + 16}"
  then have "j \<in> set [928..<944]" unfolding set_upt by simp
  then have "j \<in> set [928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943]" unfolding upt_nc_058 .
  then show "oc_sub None j" using oc_nc_0928 oc_nc_0929 oc_nc_0930 oc_nc_0931 oc_nc_0932 oc_nc_0933 oc_nc_0934 oc_nc_0935 oc_nc_0936 oc_nc_0937 oc_nc_0938 oc_nc_0939 oc_nc_0940 oc_nc_0941 oc_nc_0942 oc_nc_0943
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
