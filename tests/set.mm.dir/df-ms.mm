
axiom df-ms
  let vf: setvar f
  assert |- MetSp = { f e. *MetSp | ( ( dist ` f ) |` ( ( Base ` f ) X. ( Base ` f ) ) ) e. ( Met ` ( Base ` f ) ) }
end
