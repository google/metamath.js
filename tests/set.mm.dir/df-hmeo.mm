
axiom df-hmeo
  let vf: setvar f
  let vj: setvar j
  let vk: setvar k
  assert |- Homeo = ( j e. Top , k e. Top |-> { f e. ( j Cn k ) | `' f e. ( k Cn j ) } )
end
