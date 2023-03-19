
axiom ax-c10
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assert |- ( A. x ( x = y -> A. x ph ) -> ph )
end
