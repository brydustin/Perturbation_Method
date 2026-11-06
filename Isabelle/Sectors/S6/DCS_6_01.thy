theory DCS_6_01
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_100: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 100) (-8)) (Float (int 100 + 1) (-8))"
  by eval

lemma dc_nc_100: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 100) (-8)) (Float (int 100 + 1) (-8))"
  by eval

lemma dc_c30_101: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 101) (-8)) (Float (int 101 + 1) (-8))"
  by eval

lemma dc_nc_101: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 101) (-8)) (Float (int 101 + 1) (-8))"
  by eval

lemma dc_c30_102: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 102) (-8)) (Float (int 102 + 1) (-8))"
  by eval

lemma dc_nc_102: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 102) (-8)) (Float (int 102 + 1) (-8))"
  by eval

lemma dc_c30_103: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 103) (-8)) (Float (int 103 + 1) (-8))"
  by eval

lemma dc_nc_103: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 103) (-8)) (Float (int 103 + 1) (-8))"
  by eval

end
