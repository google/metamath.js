
axiom df-clab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assert |- ( x e. { y | ph } <-> [ x / y ] ph )
end
