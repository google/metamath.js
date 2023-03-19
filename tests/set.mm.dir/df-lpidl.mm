
axiom df-lpidl
  let vw: setvar w
  let vg: setvar g
  assert |- LPIdeal = ( w e. Ring |-> U_ g e. ( Base ` w ) { ( ( RSpan ` w ) ` { g } ) } )
end
