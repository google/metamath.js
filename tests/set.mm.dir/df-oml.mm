
axiom df-oml
  let va: setvar a
  let vb: setvar b
  let vl: setvar l
  assert |- OML = { l e. OL | A. a e. ( Base ` l ) A. b e. ( Base ` l ) ( a ( le ` l ) b -> b = ( a ( join ` l ) ( b ( meet ` l ) ( ( oc ` l ) ` a ) ) ) ) }
end
