
axiom df-fcls
  let vx: setvar x
  let vf: setvar f
  let vj: setvar j
  assert |- fClus = ( j e. Top , f e. U. ran Fil |-> if ( U. j = U. f , |^|_ x e. f ( ( cls ` j ) ` x ) , (/) ) )
end
