

axiom ax-gen
  param wph: wff ph
  param vx: setvar x
  assume ax-gen.1: |- ph
  assert |- A. x ph
end
