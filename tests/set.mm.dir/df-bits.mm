
axiom df-bits
  let vm: setvar m
  let vn: setvar n
  assert |- bits = ( n e. ZZ |-> { m e. NN0 | -. 2 || ( |_ ` ( n / ( 2 ^ m ) ) ) } )
end
