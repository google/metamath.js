

axiom ax-distrc
  param hal: type al
  param hbe: type be
  param hga: type ga
  param vx: var x
  param ta: term A
  param tb: term B
  param tf: term F
  assume ax-beta.1: |- A : be
  assume ax-distrc.2: |- B : al
  assume ax-distrc.3: |- F : ( be -> ga )
  assert |- T. |= ( ( = ( \ x : al . ( F A ) B ) ) ( ( \ x : al . F B ) ( \ x : al . A B ) ) )
end
