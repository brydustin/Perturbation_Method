theory DCX_c30_122
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1952: "dc_sub dc_b30 1952"
  by (dc_eval dc_c30_1952)

lemma dc_c30_1953: "dc_sub dc_b30 1953"
  by (dc_eval dc_c30_1953)

lemma dc_c30_1954: "dc_sub dc_b30 1954"
  by (dc_eval dc_c30_1954)

lemma dc_c30_1955: "dc_sub dc_b30 1955"
  by (dc_eval dc_c30_1955)

lemma dc_c30_1956: "dc_sub dc_b30 1956"
  by (dc_eval dc_c30_1956)

lemma dc_c30_1957: "dc_sub dc_b30 1957"
  by (dc_eval dc_c30_1957)

lemma dc_c30_1958: "dc_sub dc_b30 1958"
  by (dc_eval dc_c30_1958)

lemma dc_c30_1959: "dc_sub dc_b30 1959"
  by (dc_eval dc_c30_1959)

lemma dc_c30_1960: "dc_sub dc_b30 1960"
  by (dc_eval dc_c30_1960)

lemma dc_c30_1961: "dc_sub dc_b30 1961"
  by (dc_eval dc_c30_1961)

lemma dc_c30_1962: "dc_sub dc_b30 1962"
  by (dc_eval dc_c30_1962)

lemma dc_c30_1963: "dc_sub dc_b30 1963"
  by (dc_eval dc_c30_1963)

lemma dc_c30_1964: "dc_sub dc_b30 1964"
  by (dc_eval dc_c30_1964)

lemma dc_c30_1965: "dc_sub dc_b30 1965"
  by (dc_eval dc_c30_1965)

lemma dc_c30_1966: "dc_sub dc_b30 1966"
  by (dc_eval dc_c30_1966)

lemma dc_c30_1967: "dc_sub dc_b30 1967"
  by (dc_eval dc_c30_1967)

lemma upt_c30_122: "[1952..<1968] = [1952, 1953, 1954, 1955, 1956, 1957, 1958, 1959, 1960, 1961, 1962, 1963, 1964, 1965, 1966, 1967]"
  by (simp add: upt_rec)

lemma sec_c30_122: "\<forall>j\<in>{16 * 122..<16 * 122 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 122..<16 * 122 + 16}"
  then have "j \<in> set [1952..<1968]" unfolding set_upt by simp
  then have "j \<in> set [1952, 1953, 1954, 1955, 1956, 1957, 1958, 1959, 1960, 1961, 1962, 1963, 1964, 1965, 1966, 1967]" unfolding upt_c30_122 .
  then show "dc_sub dc_b30 j" using dc_c30_1952 dc_c30_1953 dc_c30_1954 dc_c30_1955 dc_c30_1956 dc_c30_1957 dc_c30_1958 dc_c30_1959 dc_c30_1960 dc_c30_1961 dc_c30_1962 dc_c30_1963 dc_c30_1964 dc_c30_1965 dc_c30_1966 dc_c30_1967
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
