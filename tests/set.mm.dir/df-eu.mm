
axiom df-eu
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assert |- ( E! x ph <-> E. y A. x ( ph <-> x = y ) )
end
