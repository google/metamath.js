
axiom df-xms
  let vf: setvar f
  assert |- *MetSp = { f e. TopSp | ( TopOpen ` f ) = ( MetOpen ` ( ( dist ` f ) |` ( ( Base ` f ) X. ( Base ` f ) ) ) ) }
end
