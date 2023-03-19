
axiom df-lcmf
  let vz: setvar z
  let vm: setvar m
  let vn: setvar n
  assert |- _lcm = ( z e. ~P ZZ |-> if ( 0 e. z , 0 , inf ( { n e. NN | A. m e. z m || n } , RR , < ) ) )
end
