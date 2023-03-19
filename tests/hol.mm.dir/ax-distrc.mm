
axiom ax-distrc
  let hal: type al
  let hbe: type be
  let hga: type ga
  let vx: var x
  let ta: term A
  let tb: term B
  let tf: term F
  assume ax-beta.1: |- A : be
  assume ax-distrc.2: |- B : al
  assume ax-distrc.3: |- F : ( be -> ga )
  assert |- T. |= ( ( = ( \ x : al . ( F A ) B ) ) ( ( \ x : al . F B ) ( \ x : al . A B ) ) )
end
