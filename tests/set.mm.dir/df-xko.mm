
axiom df-xko
  let vx: setvar x
  let vv: setvar v
  let vf: setvar f
  let vk: setvar k
  let vs: setvar s
  let vr: setvar r
  assert |- ^ko = ( s e. Top , r e. Top |-> ( topGen ` ( fi ` ran ( k e. { x e. ~P U. r | ( r |`t x ) e. Comp } , v e. s |-> { f e. ( r Cn s ) | ( f " k ) C_ v } ) ) ) )
end
