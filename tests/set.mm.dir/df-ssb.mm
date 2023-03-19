
axiom df-ssb
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  assert |- ( [b t /b x ]b ph <-> A. y ( y = t -> A. x ( x = y -> ph ) ) )
end
