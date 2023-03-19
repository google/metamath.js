
axiom df-cdeq
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assert |- ( CondEq ( x = y -> ph ) <-> ( x = y -> ph ) )
end
