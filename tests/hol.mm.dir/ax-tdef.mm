
axiom ax-tdef
  let hal: type al
  let hbe: type be
  let vx: var x
  let ta: term A
  let tb: term B
  let tf: term F
  let tr: term R
  assume ax-tdef.1: |- B : al
  assume ax-tdef.2: |- F : ( al -> bool )
  assume ax-tdef.3: |- T. |= ( F B )
  assume ax-tdef.4: |- typedef be ( A , R ) F
  assert |- T. |= ( ( ! \ x : be . [ ( A ( R x : be ) ) = x : be ] ) , ( ! \ x : al . [ ( F x : al ) = [ ( R ( A x : al ) ) = x : al ] ] ) )
end
