
axiom df-bj-topmgmhom
  let vx: setvar x
  let vy: setvar y
  assert |- -TopMgm-> = ( x e. TopMnd , y e. TopMnd |-> ( ( x -Top-> y ) i^i ( x -Mgm-> y ) ) )
end
