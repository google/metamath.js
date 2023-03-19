
axiom df-cnp
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g
  let vj: setvar j
  let vk: setvar k
  assert |- CnP = ( j e. Top , k e. Top |-> ( x e. U. j |-> { f e. ( U. k ^m U. j ) | A. y e. k ( ( f ` x ) e. y -> E. g e. j ( x e. g /\ ( f " g ) C_ y ) ) } ) )
end
