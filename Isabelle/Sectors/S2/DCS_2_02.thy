theory DCS_2_02
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_040: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 40) (-8)) (Float (int 40 + 1) (-8))"
  by eval

lemma dc_nc_040: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 40) (-8)) (Float (int 40 + 1) (-8))"
  by eval

lemma dc_c30_041: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 41) (-8)) (Float (int 41 + 1) (-8))"
  by eval

lemma dc_nc_041: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 41) (-8)) (Float (int 41 + 1) (-8))"
  by eval

lemma dc_c30_042: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 42) (-8)) (Float (int 42 + 1) (-8))"
  by eval

lemma dc_nc_042: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 42) (-8)) (Float (int 42 + 1) (-8))"
  by eval

lemma dc_c30_043: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 43) (-8)) (Float (int 43 + 1) (-8))"
  by eval

lemma dc_nc_043: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 43) (-8)) (Float (int 43 + 1) (-8))"
  by eval

end
