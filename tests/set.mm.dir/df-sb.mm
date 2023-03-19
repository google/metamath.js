
axiom df-sb
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assert |- ( [ y / x ] ph <-> ( ( x = y -> ph ) /\ E. x ( x = y /\ ph ) ) )
end
