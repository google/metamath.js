
axiom df-cn
  let vy: setvar y
  let vf: setvar f
  let vj: setvar j
  let vk: setvar k
  assert |- Cn = ( j e. Top , k e. Top |-> { f e. ( U. k ^m U. j ) | A. y e. k ( `' f " y ) e. j } )
end
