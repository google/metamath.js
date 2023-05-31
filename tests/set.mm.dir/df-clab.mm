

axiom df-clab
  param wph: wff ph
  param vx: setvar x
  param vy: setvar y
  assert |- ( x e. { y | ph } <-> [ x / y ] ph )
end
