
axiom df-cld
  let vx: setvar x
  let vj: setvar j
  assert |- Clsd = ( j e. Top |-> { x e. ~P U. j | ( U. j \ x ) e. j } )
end
