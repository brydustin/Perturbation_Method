theory DCS_1_01
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_020: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 20) (-8)) (Float (int 20 + 1) (-8))"
  by eval

lemma dc_nc_020: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 20) (-8)) (Float (int 20 + 1) (-8))"
  by eval

lemma dc_c30_021: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 21) (-8)) (Float (int 21 + 1) (-8))"
  by eval

lemma dc_nc_021: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 21) (-8)) (Float (int 21 + 1) (-8))"
  by eval

lemma dc_c30_022: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 22) (-8)) (Float (int 22 + 1) (-8))"
  by eval

lemma dc_nc_022: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 22) (-8)) (Float (int 22 + 1) (-8))"
  by eval

lemma dc_c30_023: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 23) (-8)) (Float (int 23 + 1) (-8))"
  by eval

lemma dc_nc_023: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 23) (-8)) (Float (int 23 + 1) (-8))"
  by eval

end
