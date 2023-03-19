
axiom df-scut
  let vx: setvar x
  let vy: setvar y
  let va: setvar a
  let vb: setvar b
  assert |- |s = ( a e. ~P No , b e. ( <<s " { a } ) |-> ( iota_ x e. { y e. No | ( a <<s { y } /\ { y } <<s b ) } ( bday ` x ) = |^| ( bday " { y e. No | ( a <<s { y } /\ { y } <<s b ) } ) ) )
end
