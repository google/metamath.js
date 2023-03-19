
axiom df-lcdual
  let vw: setvar w
  let vf: setvar f
  let vk: setvar k
  assert |- LCDual = ( k e. _V |-> ( w e. ( LHyp ` k ) |-> ( ( LDual ` ( ( DVecH ` k ) ` w ) ) |`s { f e. ( LFnl ` ( ( DVecH ` k ) ` w ) ) | ( ( ( ocH ` k ) ` w ) ` ( ( ( ocH ` k ) ` w ) ` ( ( LKer ` ( ( DVecH ` k ) ` w ) ) ` f ) ) ) = ( ( LKer ` ( ( DVecH ` k ) ` w ) ) ` f ) } ) ) )
end
