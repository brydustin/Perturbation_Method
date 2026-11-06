theory GOCX_nc_059
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0944: "goc_sub None 944"
  by (goc_eval goc_nc_0944)

lemma goc_nc_0945: "goc_sub None 945"
  by (goc_eval goc_nc_0945)

lemma goc_nc_0946: "goc_sub None 946"
  by (goc_eval goc_nc_0946)

lemma goc_nc_0947: "goc_sub None 947"
  by (goc_eval goc_nc_0947)

lemma goc_nc_0948: "goc_sub None 948"
  by (goc_eval goc_nc_0948)

lemma goc_nc_0949: "goc_sub None 949"
  by (goc_eval goc_nc_0949)

lemma goc_nc_0950: "goc_sub None 950"
  by (goc_eval goc_nc_0950)

lemma goc_nc_0951: "goc_sub None 951"
  by (goc_eval goc_nc_0951)

lemma goc_nc_0952: "goc_sub None 952"
  by (goc_eval goc_nc_0952)

lemma goc_nc_0953: "goc_sub None 953"
  by (goc_eval goc_nc_0953)

lemma goc_nc_0954: "goc_sub None 954"
  by (goc_eval goc_nc_0954)

lemma goc_nc_0955: "goc_sub None 955"
  by (goc_eval goc_nc_0955)

lemma goc_nc_0956: "goc_sub None 956"
  by (goc_eval goc_nc_0956)

lemma goc_nc_0957: "goc_sub None 957"
  by (goc_eval goc_nc_0957)

lemma goc_nc_0958: "goc_sub None 958"
  by (goc_eval goc_nc_0958)

lemma goc_nc_0959: "goc_sub None 959"
  by (goc_eval goc_nc_0959)

lemma gupt_nc_059: "[944..<960] = [944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959]"
  by (simp add: upt_rec)

lemma gsec_nc_059: "\<forall>j\<in>{16 * 59..<16 * 59 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 59..<16 * 59 + 16}"
  then have "j \<in> set [944..<960]" unfolding set_upt by simp
  then have "j \<in> set [944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959]" unfolding gupt_nc_059 .
  then show "goc_sub None j" using goc_nc_0944 goc_nc_0945 goc_nc_0946 goc_nc_0947 goc_nc_0948 goc_nc_0949 goc_nc_0950 goc_nc_0951 goc_nc_0952 goc_nc_0953 goc_nc_0954 goc_nc_0955 goc_nc_0956 goc_nc_0957 goc_nc_0958 goc_nc_0959
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
