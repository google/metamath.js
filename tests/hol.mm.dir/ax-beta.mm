

axiom ax-beta
  let hal: type al
  let hbe: type be
  let vx: var x
  let ta: term A
  assume ax-beta.1: |- A : be
  assert |- T. |= ( ( = ( \ x : al . A x : al ) ) A )
end
