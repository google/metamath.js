
axiom df-flim
  let vx: setvar x
  let vf: setvar f
  let vj: setvar j
  assert |- fLim = ( j e. Top , f e. U. ran Fil |-> { x e. U. j | ( ( ( nei ` j ) ` { x } ) C_ f /\ f C_ ~P U. j ) } )
end
