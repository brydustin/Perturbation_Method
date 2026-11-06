theory DCS_6_00
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_096: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 96) (-8)) (Float (int 96 + 1) (-8))"
  by eval

lemma dc_nc_096: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 96) (-8)) (Float (int 96 + 1) (-8))"
  by eval

lemma dc_c30_097: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 97) (-8)) (Float (int 97 + 1) (-8))"
  by eval

lemma dc_nc_097: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 97) (-8)) (Float (int 97 + 1) (-8))"
  by eval

lemma dc_c30_098: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 98) (-8)) (Float (int 98 + 1) (-8))"
  by eval

lemma dc_nc_098: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 98) (-8)) (Float (int 98 + 1) (-8))"
  by eval

lemma dc_c30_099: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 99) (-8)) (Float (int 99 + 1) (-8))"
  by eval

lemma dc_nc_099: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 99) (-8)) (Float (int 99 + 1) (-8))"
  by eval

end
