

axiom ax-11
  param wph: wff ph
  param vx: setvar x
  param vy: setvar y
  assert |- ( A. x A. y ph -> A. y A. x ph )
end
