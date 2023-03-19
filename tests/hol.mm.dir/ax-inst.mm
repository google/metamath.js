
axiom ax-inst
  let hal: type al
  let vx: var x
  let vy: var y
  let ta: term A
  let tb: term B
  let tc: term C
  let tr: term R
  let ts: term S
  assume ax-inst.1: |- R |= A
  assume ax-inst.2: |- T. |= [ ( \ x : al . B y : al ) = B ]
  assume ax-inst.3: |- T. |= [ ( \ x : al . S y : al ) = S ]
  assume ax-inst.4: |- [ x : al = C ] |= [ A = B ]
  assume ax-inst.5: |- [ x : al = C ] |= [ R = S ]
  assert |- S |= B
end
