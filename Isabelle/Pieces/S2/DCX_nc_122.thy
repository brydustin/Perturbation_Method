theory DCX_nc_122
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1952: "dc_sub None 1952"
  by (dc_eval dc_nc_1952)

lemma dc_nc_1953: "dc_sub None 1953"
  by (dc_eval dc_nc_1953)

lemma dc_nc_1954: "dc_sub None 1954"
  by (dc_eval dc_nc_1954)

lemma dc_nc_1955: "dc_sub None 1955"
  by (dc_eval dc_nc_1955)

lemma dc_nc_1956: "dc_sub None 1956"
  by (dc_eval dc_nc_1956)

lemma dc_nc_1957: "dc_sub None 1957"
  by (dc_eval dc_nc_1957)

lemma dc_nc_1958: "dc_sub None 1958"
  by (dc_eval dc_nc_1958)

lemma dc_nc_1959: "dc_sub None 1959"
  by (dc_eval dc_nc_1959)

lemma dc_nc_1960: "dc_sub None 1960"
  by (dc_eval dc_nc_1960)

lemma dc_nc_1961: "dc_sub None 1961"
  by (dc_eval dc_nc_1961)

lemma dc_nc_1962: "dc_sub None 1962"
  by (dc_eval dc_nc_1962)

lemma dc_nc_1963: "dc_sub None 1963"
  by (dc_eval dc_nc_1963)

lemma dc_nc_1964: "dc_sub None 1964"
  by (dc_eval dc_nc_1964)

lemma dc_nc_1965: "dc_sub None 1965"
  by (dc_eval dc_nc_1965)

lemma dc_nc_1966: "dc_sub None 1966"
  by (dc_eval dc_nc_1966)

lemma dc_nc_1967: "dc_sub None 1967"
  by (dc_eval dc_nc_1967)

lemma upt_nc_122: "[1952..<1968] = [1952, 1953, 1954, 1955, 1956, 1957, 1958, 1959, 1960, 1961, 1962, 1963, 1964, 1965, 1966, 1967]"
  by (simp add: upt_rec)

lemma sec_nc_122: "\<forall>j\<in>{16 * 122..<16 * 122 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 122..<16 * 122 + 16}"
  then have "j \<in> set [1952..<1968]" unfolding set_upt by simp
  then have "j \<in> set [1952, 1953, 1954, 1955, 1956, 1957, 1958, 1959, 1960, 1961, 1962, 1963, 1964, 1965, 1966, 1967]" unfolding upt_nc_122 .
  then show "dc_sub None j" using dc_nc_1952 dc_nc_1953 dc_nc_1954 dc_nc_1955 dc_nc_1956 dc_nc_1957 dc_nc_1958 dc_nc_1959 dc_nc_1960 dc_nc_1961 dc_nc_1962 dc_nc_1963 dc_nc_1964 dc_nc_1965 dc_nc_1966 dc_nc_1967
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
