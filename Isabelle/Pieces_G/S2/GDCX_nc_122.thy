theory GDCX_nc_122
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1952: "gdc_sub None 1952"
  by (gdc_eval gdc_nc_1952)

lemma gdc_nc_1953: "gdc_sub None 1953"
  by (gdc_eval gdc_nc_1953)

lemma gdc_nc_1954: "gdc_sub None 1954"
  by (gdc_eval gdc_nc_1954)

lemma gdc_nc_1955: "gdc_sub None 1955"
  by (gdc_eval gdc_nc_1955)

lemma gdc_nc_1956: "gdc_sub None 1956"
  by (gdc_eval gdc_nc_1956)

lemma gdc_nc_1957: "gdc_sub None 1957"
  by (gdc_eval gdc_nc_1957)

lemma gdc_nc_1958: "gdc_sub None 1958"
  by (gdc_eval gdc_nc_1958)

lemma gdc_nc_1959: "gdc_sub None 1959"
  by (gdc_eval gdc_nc_1959)

lemma gdc_nc_1960: "gdc_sub None 1960"
  by (gdc_eval gdc_nc_1960)

lemma gdc_nc_1961: "gdc_sub None 1961"
  by (gdc_eval gdc_nc_1961)

lemma gdc_nc_1962: "gdc_sub None 1962"
  by (gdc_eval gdc_nc_1962)

lemma gdc_nc_1963: "gdc_sub None 1963"
  by (gdc_eval gdc_nc_1963)

lemma gdc_nc_1964: "gdc_sub None 1964"
  by (gdc_eval gdc_nc_1964)

lemma gdc_nc_1965: "gdc_sub None 1965"
  by (gdc_eval gdc_nc_1965)

lemma gdc_nc_1966: "gdc_sub None 1966"
  by (gdc_eval gdc_nc_1966)

lemma gdc_nc_1967: "gdc_sub None 1967"
  by (gdc_eval gdc_nc_1967)

lemma gupt_nc_122: "[1952..<1968] = [1952, 1953, 1954, 1955, 1956, 1957, 1958, 1959, 1960, 1961, 1962, 1963, 1964, 1965, 1966, 1967]"
  by (simp add: upt_rec)

lemma gsec_nc_122: "\<forall>j\<in>{16 * 122..<16 * 122 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 122..<16 * 122 + 16}"
  then have "j \<in> set [1952..<1968]" unfolding set_upt by simp
  then have "j \<in> set [1952, 1953, 1954, 1955, 1956, 1957, 1958, 1959, 1960, 1961, 1962, 1963, 1964, 1965, 1966, 1967]" unfolding gupt_nc_122 .
  then show "gdc_sub None j" using gdc_nc_1952 gdc_nc_1953 gdc_nc_1954 gdc_nc_1955 gdc_nc_1956 gdc_nc_1957 gdc_nc_1958 gdc_nc_1959 gdc_nc_1960 gdc_nc_1961 gdc_nc_1962 gdc_nc_1963 gdc_nc_1964 gdc_nc_1965 gdc_nc_1966 gdc_nc_1967
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
