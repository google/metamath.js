
axiom df-oposet
  let vo: setvar o
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  assert |- OP = { p e. Poset | ( ( ( Base ` p ) e. dom ( lub ` p ) /\ ( Base ` p ) e. dom ( glb ` p ) ) /\ E. o ( o = ( oc ` p ) /\ A. a e. ( Base ` p ) A. b e. ( Base ` p ) ( ( ( o ` a ) e. ( Base ` p ) /\ ( o ` ( o ` a ) ) = a /\ ( a ( le ` p ) b -> ( o ` b ) ( le ` p ) ( o ` a ) ) ) /\ ( a ( join ` p ) ( o ` a ) ) = ( 1. ` p ) /\ ( a ( meet ` p ) ( o ` a ) ) = ( 0. ` p ) ) ) ) }
end
