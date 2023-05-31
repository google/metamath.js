

axiom df-sb
  param wph: wff ph
  param vx: setvar x
  param vy: setvar y
  assert |- ( [ y / x ] ph <-> ( ( x = y -> ph ) /\ E. x ( x = y /\ ph ) ) )
end
