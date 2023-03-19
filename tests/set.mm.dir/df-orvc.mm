
axiom df-orvc
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let va: setvar a
  assert |- oRVC R = ( x e. { x | Fun x } , a e. _V |-> ( `' x " { y | y R a } ) )
end
