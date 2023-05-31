

axiom ax-12
  param wph: wff ph
  param vx: setvar x
  param vy: setvar y
  assert |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) )
end
