
axiom df-utop
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let va: setvar a
  assert |- unifTop = ( u e. U. ran UnifOn |-> { a e. ~P dom U. u | A. x e. a E. v e. u ( v " { x } ) C_ a } )
end
