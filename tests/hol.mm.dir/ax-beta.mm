

axiom ax-beta
  param hal: type al
  param hbe: type be
  param vx: var x
  param ta: term A
  assume ax-beta.1: |- A : be
  assert |- T. |= ( ( = ( \ x : al . A x : al ) ) A )
end
