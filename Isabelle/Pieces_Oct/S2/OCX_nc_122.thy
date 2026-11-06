theory OCX_nc_122
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1952: "oc_sub None 1952"
  by (oc_eval oc_nc_1952)

lemma oc_nc_1953: "oc_sub None 1953"
  by (oc_eval oc_nc_1953)

lemma oc_nc_1954: "oc_sub None 1954"
  by (oc_eval oc_nc_1954)

lemma oc_nc_1955: "oc_sub None 1955"
  by (oc_eval oc_nc_1955)

lemma oc_nc_1956: "oc_sub None 1956"
  by (oc_eval oc_nc_1956)

lemma oc_nc_1957: "oc_sub None 1957"
  by (oc_eval oc_nc_1957)

lemma oc_nc_1958: "oc_sub None 1958"
  by (oc_eval oc_nc_1958)

lemma oc_nc_1959: "oc_sub None 1959"
  by (oc_eval oc_nc_1959)

lemma oc_nc_1960: "oc_sub None 1960"
  by (oc_eval oc_nc_1960)

lemma oc_nc_1961: "oc_sub None 1961"
  by (oc_eval oc_nc_1961)

lemma oc_nc_1962: "oc_sub None 1962"
  by (oc_eval oc_nc_1962)

lemma oc_nc_1963: "oc_sub None 1963"
  by (oc_eval oc_nc_1963)

lemma oc_nc_1964: "oc_sub None 1964"
  by (oc_eval oc_nc_1964)

lemma oc_nc_1965: "oc_sub None 1965"
  by (oc_eval oc_nc_1965)

lemma oc_nc_1966: "oc_sub None 1966"
  by (oc_eval oc_nc_1966)

lemma oc_nc_1967: "oc_sub None 1967"
  by (oc_eval oc_nc_1967)

lemma upt_nc_122: "[1952..<1968] = [1952, 1953, 1954, 1955, 1956, 1957, 1958, 1959, 1960, 1961, 1962, 1963, 1964, 1965, 1966, 1967]"
  by (simp add: upt_rec)

lemma sec_nc_122: "\<forall>j\<in>{16 * 122..<16 * 122 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 122..<16 * 122 + 16}"
  then have "j \<in> set [1952..<1968]" unfolding set_upt by simp
  then have "j \<in> set [1952, 1953, 1954, 1955, 1956, 1957, 1958, 1959, 1960, 1961, 1962, 1963, 1964, 1965, 1966, 1967]" unfolding upt_nc_122 .
  then show "oc_sub None j" using oc_nc_1952 oc_nc_1953 oc_nc_1954 oc_nc_1955 oc_nc_1956 oc_nc_1957 oc_nc_1958 oc_nc_1959 oc_nc_1960 oc_nc_1961 oc_nc_1962 oc_nc_1963 oc_nc_1964 oc_nc_1965 oc_nc_1966 oc_nc_1967
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
