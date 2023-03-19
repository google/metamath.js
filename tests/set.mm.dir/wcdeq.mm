
axiom wcdeq
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assert wff CondEq ( x = y -> ph )
end
