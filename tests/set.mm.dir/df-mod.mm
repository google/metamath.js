
axiom df-mod
  let vx: setvar x
  let vy: setvar y
  assert |- mod = ( x e. RR , y e. RR+ |-> ( x - ( y x. ( |_ ` ( x / y ) ) ) ) )
end
