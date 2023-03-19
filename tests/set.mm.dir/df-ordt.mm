
axiom df-ordt
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r
  assert |- ordTop = ( r e. _V |-> ( topGen ` ( fi ` ( { dom r } u. ran ( ( x e. dom r |-> { y e. dom r | -. y r x } ) u. ( x e. dom r |-> { y e. dom r | -. x r y } ) ) ) ) ) )
end
