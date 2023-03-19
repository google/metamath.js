
axiom ax-c11
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assert |- ( A. x x = y -> ( A. x ph -> A. y ph ) )
end
