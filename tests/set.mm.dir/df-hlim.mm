
axiom df-hlim
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vf: setvar f
  assert |- ~~>v = { <. f , w >. | ( ( f : NN --> ~H /\ w e. ~H ) /\ A. x e. RR+ E. y e. NN A. z e. ( ZZ>= ` y ) ( normh ` ( ( f ` z ) -h w ) ) < x ) }
end
