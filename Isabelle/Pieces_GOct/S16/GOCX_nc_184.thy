theory GOCX_nc_184
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2944: "goc_sub None 2944"
  by (goc_eval goc_nc_2944)

lemma goc_nc_2945: "goc_sub None 2945"
  by (goc_eval goc_nc_2945)

lemma goc_nc_2946: "goc_sub None 2946"
  by (goc_eval goc_nc_2946)

lemma goc_nc_2947: "goc_sub None 2947"
  by (goc_eval goc_nc_2947)

lemma goc_nc_2948: "goc_sub None 2948"
  by (goc_eval goc_nc_2948)

lemma goc_nc_2949: "goc_sub None 2949"
  by (goc_eval goc_nc_2949)

lemma goc_nc_2950: "goc_sub None 2950"
  by (goc_eval goc_nc_2950)

lemma goc_nc_2951: "goc_sub None 2951"
  by (goc_eval goc_nc_2951)

lemma goc_nc_2952: "goc_sub None 2952"
  by (goc_eval goc_nc_2952)

lemma goc_nc_2953: "goc_sub None 2953"
  by (goc_eval goc_nc_2953)

lemma goc_nc_2954: "goc_sub None 2954"
  by (goc_eval goc_nc_2954)

lemma goc_nc_2955: "goc_sub None 2955"
  by (goc_eval goc_nc_2955)

lemma goc_nc_2956: "goc_sub None 2956"
  by (goc_eval goc_nc_2956)

lemma goc_nc_2957: "goc_sub None 2957"
  by (goc_eval goc_nc_2957)

lemma goc_nc_2958: "goc_sub None 2958"
  by (goc_eval goc_nc_2958)

lemma goc_nc_2959: "goc_sub None 2959"
  by (goc_eval goc_nc_2959)

lemma gupt_nc_184: "[2944..<2960] = [2944, 2945, 2946, 2947, 2948, 2949, 2950, 2951, 2952, 2953, 2954, 2955, 2956, 2957, 2958, 2959]"
  by (simp add: upt_rec)

lemma gsec_nc_184: "\<forall>j\<in>{16 * 184..<16 * 184 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 184..<16 * 184 + 16}"
  then have "j \<in> set [2944..<2960]" unfolding set_upt by simp
  then have "j \<in> set [2944, 2945, 2946, 2947, 2948, 2949, 2950, 2951, 2952, 2953, 2954, 2955, 2956, 2957, 2958, 2959]" unfolding gupt_nc_184 .
  then show "goc_sub None j" using goc_nc_2944 goc_nc_2945 goc_nc_2946 goc_nc_2947 goc_nc_2948 goc_nc_2949 goc_nc_2950 goc_nc_2951 goc_nc_2952 goc_nc_2953 goc_nc_2954 goc_nc_2955 goc_nc_2956 goc_nc_2957 goc_nc_2958 goc_nc_2959
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
