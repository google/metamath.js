
axiom df-retr
  let vj: setvar j
  let vk: setvar k
  let vs: setvar s
  let vr: setvar r
  assert |- Retr = ( j e. Top , k e. Top |-> { r e. ( j Cn k ) | E. s e. ( k Cn j ) ( ( r o. s ) ( j Htpy j ) ( _I |` U. j ) ) =/= (/) } )
end
