
axiom ax-c15
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assert |- ( -. A. x x = y -> ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) )
end
