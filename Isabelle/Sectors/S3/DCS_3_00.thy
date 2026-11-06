theory DCS_3_00
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_048: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 48) (-8)) (Float (int 48 + 1) (-8))"
  by eval

lemma dc_nc_048: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 48) (-8)) (Float (int 48 + 1) (-8))"
  by eval

lemma dc_c30_049: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 49) (-8)) (Float (int 49 + 1) (-8))"
  by eval

lemma dc_nc_049: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 49) (-8)) (Float (int 49 + 1) (-8))"
  by eval

lemma dc_c30_050: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 50) (-8)) (Float (int 50 + 1) (-8))"
  by eval

lemma dc_nc_050: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 50) (-8)) (Float (int 50 + 1) (-8))"
  by eval

lemma dc_c30_051: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 51) (-8)) (Float (int 51 + 1) (-8))"
  by eval

lemma dc_nc_051: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 51) (-8)) (Float (int 51 + 1) (-8))"
  by eval

end
