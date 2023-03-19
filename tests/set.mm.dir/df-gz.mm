
axiom df-gz
  let vx: setvar x
  assert |- Z[i] = { x e. CC | ( ( Re ` x ) e. ZZ /\ ( Im ` x ) e. ZZ ) }
end
