

axiom df-iota
  param wph: wff ph
  param vx: setvar x
  param vy: setvar y
  assert |- ( iota x ph ) = U. { y | { x | ph } = { y } }
end
