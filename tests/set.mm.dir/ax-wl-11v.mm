
axiom ax-wl-11v
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assert |- ( A. x A. y ph -> A. y A. x ph )
end
