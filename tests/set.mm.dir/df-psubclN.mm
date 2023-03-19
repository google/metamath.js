
axiom df-psubclN
  let vk: setvar k
  let vs: setvar s
  assert |- PSubCl = ( k e. _V |-> { s | ( s C_ ( Atoms ` k ) /\ ( ( _|_P ` k ) ` ( ( _|_P ` k ) ` s ) ) = s ) } )
end
