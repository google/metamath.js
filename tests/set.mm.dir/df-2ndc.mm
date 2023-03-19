
axiom df-2ndc
  let vx: setvar x
  let vj: setvar j
  assert |- 2ndc = { j | E. x e. TopBases ( x ~<_ _om /\ ( topGen ` x ) = j ) }
end
