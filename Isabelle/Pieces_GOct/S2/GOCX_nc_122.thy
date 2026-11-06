theory GOCX_nc_122
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1952: "goc_sub None 1952"
  by (goc_eval goc_nc_1952)

lemma goc_nc_1953: "goc_sub None 1953"
  by (goc_eval goc_nc_1953)

lemma goc_nc_1954: "goc_sub None 1954"
  by (goc_eval goc_nc_1954)

lemma goc_nc_1955: "goc_sub None 1955"
  by (goc_eval goc_nc_1955)

lemma goc_nc_1956: "goc_sub None 1956"
  by (goc_eval goc_nc_1956)

lemma goc_nc_1957: "goc_sub None 1957"
  by (goc_eval goc_nc_1957)

lemma goc_nc_1958: "goc_sub None 1958"
  by (goc_eval goc_nc_1958)

lemma goc_nc_1959: "goc_sub None 1959"
  by (goc_eval goc_nc_1959)

lemma goc_nc_1960: "goc_sub None 1960"
  by (goc_eval goc_nc_1960)

lemma goc_nc_1961: "goc_sub None 1961"
  by (goc_eval goc_nc_1961)

lemma goc_nc_1962: "goc_sub None 1962"
  by (goc_eval goc_nc_1962)

lemma goc_nc_1963: "goc_sub None 1963"
  by (goc_eval goc_nc_1963)

lemma goc_nc_1964: "goc_sub None 1964"
  by (goc_eval goc_nc_1964)

lemma goc_nc_1965: "goc_sub None 1965"
  by (goc_eval goc_nc_1965)

lemma goc_nc_1966: "goc_sub None 1966"
  by (goc_eval goc_nc_1966)

lemma goc_nc_1967: "goc_sub None 1967"
  by (goc_eval goc_nc_1967)

lemma gupt_nc_122: "[1952..<1968] = [1952, 1953, 1954, 1955, 1956, 1957, 1958, 1959, 1960, 1961, 1962, 1963, 1964, 1965, 1966, 1967]"
  by (simp add: upt_rec)

lemma gsec_nc_122: "\<forall>j\<in>{16 * 122..<16 * 122 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 122..<16 * 122 + 16}"
  then have "j \<in> set [1952..<1968]" unfolding set_upt by simp
  then have "j \<in> set [1952, 1953, 1954, 1955, 1956, 1957, 1958, 1959, 1960, 1961, 1962, 1963, 1964, 1965, 1966, 1967]" unfolding gupt_nc_122 .
  then show "goc_sub None j" using goc_nc_1952 goc_nc_1953 goc_nc_1954 goc_nc_1955 goc_nc_1956 goc_nc_1957 goc_nc_1958 goc_nc_1959 goc_nc_1960 goc_nc_1961 goc_nc_1962 goc_nc_1963 goc_nc_1964 goc_nc_1965 goc_nc_1966 goc_nc_1967
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
