
axiom df-dpj
  let vg: setvar g
  let vi: setvar i
  let vs: setvar s
  assert |- dProj = ( g e. Grp , s e. ( dom DProd " { g } ) |-> ( i e. dom s |-> ( ( s ` i ) ( proj1 ` g ) ( g DProd ( s |` ( dom s \ { i } ) ) ) ) ) )
end
