

axiom ax-inst
  param hal: type al
  param vx: var x
  param vy: var y
  param ta: term A
  param tb: term B
  param tc: term C
  param tr: term R
  param ts: term S
  assume ax-inst.1: |- R |= A
  assume ax-inst.2: |- T. |= [ ( \ x : al . B y : al ) = B ]
  assume ax-inst.3: |- T. |= [ ( \ x : al . S y : al ) = S ]
  assume ax-inst.4: |- [ x : al = C ] |= [ A = B ]
  assume ax-inst.5: |- [ x : al = C ] |= [ R = S ]
  assert |- S |= B
end
