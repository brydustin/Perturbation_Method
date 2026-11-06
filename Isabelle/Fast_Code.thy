theory Fast_Code
  imports "HOL-Library.Float" "HOL-Library.Code_Target_Numeral"
begin

text \<open>Faster, provably equal code equations for float comparisons.  The library compares floats through a
  rounded addition at precision 0, which normalises the result; a direct comparison of the aligned
  mantissas is much faster.\<close>

lemma float_align:
  assumes "e1 \<le> e2"
  shows "real_of_float (Float m2 e2) = real_of_int (m2 * 2 ^ nat (e2 - e1)) * 2 powr real_of_int e1"
proof -
  have "real_of_int (e2 - e1) = real (nat (e2 - e1))" using assms by simp
  then have 1: "2 powr real_of_int (e2 - e1) = (2::real) ^ nat (e2 - e1)"
    by (simp only: powr_realpow [OF zero_less_numeral])
  have "real_of_int e2 = real_of_int (e2 - e1) + real_of_int e1" by simp
  then have 2: "(2::real) powr real_of_int e2 = 2 powr real_of_int (e2 - e1) * 2 powr real_of_int e1"
    by (subst (1) \<open>real_of_int e2 = real_of_int (e2 - e1) + real_of_int e1\<close>) (rule powr_add)
  show ?thesis
    by (simp only: Float.rep_eq 2 1 of_int_mult of_int_power of_int_numeral mult.assoc)
qed

lemma two_powr_pos: "0 < (2::real) powr x"
  by simp

lemma float_le_fast [code]:
  "Float m1 e1 \<le> Float m2 e2 \<longleftrightarrow> (if e1 \<le> e2 then m1 \<le> m2 * 2 ^ nat (e2 - e1) else m1 * 2 ^ nat (e1 - e2) \<le> m2)"
proof (cases "e1 \<le> e2")
  case True
  have "real_of_float (Float m1 e1) \<le> real_of_float (Float m2 e2) \<longleftrightarrow> m1 \<le> m2 * 2 ^ nat (e2 - e1)"
    unfolding float_align [OF True, of m2] Float.rep_eq [of m1 e1]
    by (simp only: mult_le_cancel_right_pos [OF two_powr_pos] of_int_le_iff)
  then show ?thesis using True unfolding less_eq_float.rep_eq by simp
next
  case False
  then have le: "e2 \<le> e1" by simp
  have "real_of_float (Float m1 e1) \<le> real_of_float (Float m2 e2) \<longleftrightarrow> m1 * 2 ^ nat (e1 - e2) \<le> m2"
    unfolding float_align [OF le, of m1] Float.rep_eq [of m2 e2]
    by (simp only: mult_le_cancel_right_pos [OF two_powr_pos] of_int_le_iff)
  then show ?thesis using False unfolding less_eq_float.rep_eq by simp
qed

lemma float_less_fast [code]:
  "Float m1 e1 < Float m2 e2 \<longleftrightarrow> (if e1 \<le> e2 then m1 < m2 * 2 ^ nat (e2 - e1) else m1 * 2 ^ nat (e1 - e2) < m2)"
proof (cases "e1 \<le> e2")
  case True
  have "real_of_float (Float m1 e1) < real_of_float (Float m2 e2) \<longleftrightarrow> m1 < m2 * 2 ^ nat (e2 - e1)"
    unfolding float_align [OF True, of m2] Float.rep_eq [of m1 e1]
    by (simp only: mult_less_cancel_right_pos [OF two_powr_pos] of_int_less_iff)
  then show ?thesis using True unfolding less_float.rep_eq by simp
next
  case False
  then have le: "e2 \<le> e1" by simp
  have "real_of_float (Float m1 e1) < real_of_float (Float m2 e2) \<longleftrightarrow> m1 * 2 ^ nat (e1 - e2) < m2"
    unfolding float_align [OF le, of m1] Float.rep_eq [of m2 e2]
    by (simp only: mult_less_cancel_right_pos [OF two_powr_pos] of_int_less_iff)
  then show ?thesis using False unfolding less_float.rep_eq by simp
qed

text \<open>A divide-and-conquer code equation for the bit length: the library's recursion halves the number
  once per bit.\<close>

lemma bitlen_div_pow: "2 ^ k \<le> x \<Longrightarrow> bitlen (x div 2 ^ k) + int k = bitlen x"
proof (induction k)
  case 0 then show ?case by simp
next
  case (Suc k)
  have "(2::int) ^ k \<le> 2 ^ Suc k" by simp
  with Suc.prems have le: "2 ^ k \<le> x" by linarith
  have pos: "0 < x div 2 ^ k"
  proof -
    have "2 ^ Suc k div 2 ^ k \<le> x div 2 ^ k" using Suc.prems by (rule zdiv_mono1) simp
    then show ?thesis by (simp add: power_Suc2)
  qed
  have "x div 2 ^ Suc k = (x div 2 ^ k) div 2"
  proof -
    have "x div 2 ^ Suc k = x div (2 ^ k * 2)" by (simp only: power_Suc2)
    also have "\<dots> = x div 2 ^ k div 2" by (rule zdiv_zmult2_eq) simp
    finally show ?thesis .
  qed
  then have "bitlen (x div 2 ^ Suc k) + 1 = bitlen (x div 2 ^ k)"
    using compute_bitlen [of "x div 2 ^ k"] pos by simp
  with Suc.IH [OF le] show ?case by simp
qed

lemma bitlen_fast [code]:
  "bitlen x = (if 18446744073709551616 \<le> x then bitlen (x div 18446744073709551616) + 64
               else if x > 0 then bitlen (x div 2) + 1 else 0)"
proof -
  have "(18446744073709551616::int) = 2 ^ 64" by simp
  then show ?thesis using bitlen_div_pow [of 64 x] compute_bitlen [of x] by simp
qed

text \<open>Square-and-multiply code equation for integer powers (the default recursion is linear in the exponent;
  the rounding functions compute \<open>2 ^ k\<close> for \<open>k\<close> of the order of the mantissa length).\<close>

lemma power_int_fast [code]:
  "(x::int) ^ n = (if n = 0 then 1 else let p = x ^ (n div 2) in if even n then p * p else x * (p * p))"
proof (cases "n = 0")
  case True then show ?thesis by simp
next
  case False
  have "n = n div 2 + n div 2 + n mod 2" by presburger
  then have eq: "x ^ n = x ^ (n div 2) * x ^ (n div 2) * x ^ (n mod 2)" by (metis power_add)
  show ?thesis
  proof (cases "even n")
    case True
    then have m0: "n mod 2 = 0" by (simp add: even_iff_mod_2_eq_zero)
    show ?thesis unfolding Let_def
      by (simp only: eq m0 True if_True power_0 mult_1_right False if_False)
  next
    case False
    then have m1: "n mod 2 = 1" by (simp add: odd_iff_mod_2_eq_one)
    have "x ^ n = x * (x ^ (n div 2) * x ^ (n div 2))"
      unfolding eq m1 power_one_right by (simp only: mult.commute)
    then show ?thesis unfolding Let_def
      by (simp only: False if_False \<open>n \<noteq> 0\<close>)
  qed
qed

end
