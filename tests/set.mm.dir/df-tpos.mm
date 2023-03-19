
axiom df-tpos
  let vx: setvar x
  let cF: class F
  assert |- tpos F = ( F o. ( x e. ( `' dom F u. { (/) } ) |-> U. `' { x } ) )
end
