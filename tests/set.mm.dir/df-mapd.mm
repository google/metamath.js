
axiom df-mapd
  let vw: setvar w
  let vf: setvar f
  let vk: setvar k
  let vs: setvar s
  assert |- mapd = ( k e. _V |-> ( w e. ( LHyp ` k ) |-> ( s e. ( LSubSp ` ( ( DVecH ` k ) ` w ) ) |-> { f e. ( LFnl ` ( ( DVecH ` k ) ` w ) ) | ( ( ( ( ocH ` k ) ` w ) ` ( ( ( ocH ` k ) ` w ) ` ( ( LKer ` ( ( DVecH ` k ) ` w ) ) ` f ) ) ) = ( ( LKer ` ( ( DVecH ` k ) ` w ) ) ` f ) /\ ( ( ( ocH ` k ) ` w ) ` ( ( LKer ` ( ( DVecH ` k ) ` w ) ) ` f ) ) C_ s ) } ) ) )
end
