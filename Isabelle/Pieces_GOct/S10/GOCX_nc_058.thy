theory GOCX_nc_058
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0928: "goc_sub None 928"
  by (goc_eval goc_nc_0928)

lemma goc_nc_0929: "goc_sub None 929"
  by (goc_eval goc_nc_0929)

lemma goc_nc_0930: "goc_sub None 930"
  by (goc_eval goc_nc_0930)

lemma goc_nc_0931: "goc_sub None 931"
  by (goc_eval goc_nc_0931)

lemma goc_nc_0932: "goc_sub None 932"
  by (goc_eval goc_nc_0932)

lemma goc_nc_0933: "goc_sub None 933"
  by (goc_eval goc_nc_0933)

lemma goc_nc_0934: "goc_sub None 934"
  by (goc_eval goc_nc_0934)

lemma goc_nc_0935: "goc_sub None 935"
  by (goc_eval goc_nc_0935)

lemma goc_nc_0936: "goc_sub None 936"
  by (goc_eval goc_nc_0936)

lemma goc_nc_0937: "goc_sub None 937"
  by (goc_eval goc_nc_0937)

lemma goc_nc_0938: "goc_sub None 938"
  by (goc_eval goc_nc_0938)

lemma goc_nc_0939: "goc_sub None 939"
  by (goc_eval goc_nc_0939)

lemma goc_nc_0940: "goc_sub None 940"
  by (goc_eval goc_nc_0940)

lemma goc_nc_0941: "goc_sub None 941"
  by (goc_eval goc_nc_0941)

lemma goc_nc_0942: "goc_sub None 942"
  by (goc_eval goc_nc_0942)

lemma goc_nc_0943: "goc_sub None 943"
  by (goc_eval goc_nc_0943)

lemma gupt_nc_058: "[928..<944] = [928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943]"
  by (simp add: upt_rec)

lemma gsec_nc_058: "\<forall>j\<in>{16 * 58..<16 * 58 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 58..<16 * 58 + 16}"
  then have "j \<in> set [928..<944]" unfolding set_upt by simp
  then have "j \<in> set [928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943]" unfolding gupt_nc_058 .
  then show "goc_sub None j" using goc_nc_0928 goc_nc_0929 goc_nc_0930 goc_nc_0931 goc_nc_0932 goc_nc_0933 goc_nc_0934 goc_nc_0935 goc_nc_0936 goc_nc_0937 goc_nc_0938 goc_nc_0939 goc_nc_0940 goc_nc_0941 goc_nc_0942 goc_nc_0943
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
