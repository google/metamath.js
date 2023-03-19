
axiom df-coa
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vc: setvar c
  assert |- compA = ( c e. Cat |-> ( g e. ( Arrow ` c ) , f e. { h e. ( Arrow ` c ) | ( codA ` h ) = ( domA ` g ) } |-> <. ( domA ` f ) , ( codA ` g ) , ( ( 2nd ` g ) ( <. ( domA ` f ) , ( domA ` g ) >. ( comp ` c ) ( codA ` g ) ) ( 2nd ` f ) ) >. ) )
end
