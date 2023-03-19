
axiom df-cms
  let vw: setvar w
  let vb: setvar b
  assert |- CMetSp = { w e. MetSp | [. ( Base ` w ) / b ]. ( ( dist ` w ) |` ( b X. b ) ) e. ( CMet ` b ) }
end
