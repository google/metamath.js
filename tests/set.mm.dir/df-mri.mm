
axiom df-mri
  let vx: setvar x
  let vs: setvar s
  let vc: setvar c
  assert |- mrInd = ( c e. U. ran Moore |-> { s e. ~P U. c | A. x e. s -. x e. ( ( mrCls ` c ) ` ( s \ { x } ) ) } )
end
