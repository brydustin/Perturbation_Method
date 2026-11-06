theory DCX_nc_058
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0928: "dc_sub None 928"
  by (dc_eval dc_nc_0928)

lemma dc_nc_0929: "dc_sub None 929"
  by (dc_eval dc_nc_0929)

lemma dc_nc_0930: "dc_sub None 930"
  by (dc_eval dc_nc_0930)

lemma dc_nc_0931: "dc_sub None 931"
  by (dc_eval dc_nc_0931)

lemma dc_nc_0932: "dc_sub None 932"
  by (dc_eval dc_nc_0932)

lemma dc_nc_0933: "dc_sub None 933"
  by (dc_eval dc_nc_0933)

lemma dc_nc_0934: "dc_sub None 934"
  by (dc_eval dc_nc_0934)

lemma dc_nc_0935: "dc_sub None 935"
  by (dc_eval dc_nc_0935)

lemma dc_nc_0936: "dc_sub None 936"
  by (dc_eval dc_nc_0936)

lemma dc_nc_0937: "dc_sub None 937"
  by (dc_eval dc_nc_0937)

lemma dc_nc_0938: "dc_sub None 938"
  by (dc_eval dc_nc_0938)

lemma dc_nc_0939: "dc_sub None 939"
  by (dc_eval dc_nc_0939)

lemma dc_nc_0940: "dc_sub None 940"
  by (dc_eval dc_nc_0940)

lemma dc_nc_0941: "dc_sub None 941"
  by (dc_eval dc_nc_0941)

lemma dc_nc_0942: "dc_sub None 942"
  by (dc_eval dc_nc_0942)

lemma dc_nc_0943: "dc_sub None 943"
  by (dc_eval dc_nc_0943)

lemma upt_nc_058: "[928..<944] = [928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943]"
  by (simp add: upt_rec)

lemma sec_nc_058: "\<forall>j\<in>{16 * 58..<16 * 58 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 58..<16 * 58 + 16}"
  then have "j \<in> set [928..<944]" unfolding set_upt by simp
  then have "j \<in> set [928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943]" unfolding upt_nc_058 .
  then show "dc_sub None j" using dc_nc_0928 dc_nc_0929 dc_nc_0930 dc_nc_0931 dc_nc_0932 dc_nc_0933 dc_nc_0934 dc_nc_0935 dc_nc_0936 dc_nc_0937 dc_nc_0938 dc_nc_0939 dc_nc_0940 dc_nc_0941 dc_nc_0942 dc_nc_0943
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
