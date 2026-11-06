theory DCS_2_01
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_036: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 36) (-8)) (Float (int 36 + 1) (-8))"
  by eval

lemma dc_nc_036: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 36) (-8)) (Float (int 36 + 1) (-8))"
  by eval

lemma dc_c30_037: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 37) (-8)) (Float (int 37 + 1) (-8))"
  by eval

lemma dc_nc_037: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 37) (-8)) (Float (int 37 + 1) (-8))"
  by eval

lemma dc_c30_038: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 38) (-8)) (Float (int 38 + 1) (-8))"
  by eval

lemma dc_nc_038: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 38) (-8)) (Float (int 38 + 1) (-8))"
  by eval

lemma dc_c30_039: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 39) (-8)) (Float (int 39 + 1) (-8))"
  by eval

lemma dc_nc_039: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 39) (-8)) (Float (int 39 + 1) (-8))"
  by eval

end
