
axiom df-tail
  let vx: setvar x
  let vr: setvar r
  assert |- tail = ( r e. DirRel |-> ( x e. U. U. r |-> ( r " { x } ) ) )
end
