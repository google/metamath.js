
axiom df-mrc
  let vx: setvar x
  let vs: setvar s
  let vc: setvar c
  assert |- mrCls = ( c e. U. ran Moore |-> ( x e. ~P U. c |-> |^| { s e. c | x C_ s } ) )
end
