theory GDCX_nc_058
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0928: "gdc_sub None 928"
  by (gdc_eval gdc_nc_0928)

lemma gdc_nc_0929: "gdc_sub None 929"
  by (gdc_eval gdc_nc_0929)

lemma gdc_nc_0930: "gdc_sub None 930"
  by (gdc_eval gdc_nc_0930)

lemma gdc_nc_0931: "gdc_sub None 931"
  by (gdc_eval gdc_nc_0931)

lemma gdc_nc_0932: "gdc_sub None 932"
  by (gdc_eval gdc_nc_0932)

lemma gdc_nc_0933: "gdc_sub None 933"
  by (gdc_eval gdc_nc_0933)

lemma gdc_nc_0934: "gdc_sub None 934"
  by (gdc_eval gdc_nc_0934)

lemma gdc_nc_0935: "gdc_sub None 935"
  by (gdc_eval gdc_nc_0935)

lemma gdc_nc_0936: "gdc_sub None 936"
  by (gdc_eval gdc_nc_0936)

lemma gdc_nc_0937: "gdc_sub None 937"
  by (gdc_eval gdc_nc_0937)

lemma gdc_nc_0938: "gdc_sub None 938"
  by (gdc_eval gdc_nc_0938)

lemma gdc_nc_0939: "gdc_sub None 939"
  by (gdc_eval gdc_nc_0939)

lemma gdc_nc_0940: "gdc_sub None 940"
  by (gdc_eval gdc_nc_0940)

lemma gdc_nc_0941: "gdc_sub None 941"
  by (gdc_eval gdc_nc_0941)

lemma gdc_nc_0942: "gdc_sub None 942"
  by (gdc_eval gdc_nc_0942)

lemma gdc_nc_0943: "gdc_sub None 943"
  by (gdc_eval gdc_nc_0943)

lemma gupt_nc_058: "[928..<944] = [928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943]"
  by (simp add: upt_rec)

lemma gsec_nc_058: "\<forall>j\<in>{16 * 58..<16 * 58 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 58..<16 * 58 + 16}"
  then have "j \<in> set [928..<944]" unfolding set_upt by simp
  then have "j \<in> set [928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943]" unfolding gupt_nc_058 .
  then show "gdc_sub None j" using gdc_nc_0928 gdc_nc_0929 gdc_nc_0930 gdc_nc_0931 gdc_nc_0932 gdc_nc_0933 gdc_nc_0934 gdc_nc_0935 gdc_nc_0936 gdc_nc_0937 gdc_nc_0938 gdc_nc_0939 gdc_nc_0940 gdc_nc_0941 gdc_nc_0942 gdc_nc_0943
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
