
axiom df-mp
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  assert |- .P. = ( x e. P. , y e. P. |-> { w | E. v e. x E. u e. y w = ( v .Q u ) } )
end
