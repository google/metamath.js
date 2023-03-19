
axiom ax-11d
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assert |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) )
end
