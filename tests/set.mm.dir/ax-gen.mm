
axiom ax-gen
  let wph: wff ph
  let vx: setvar x
  assume ax-gen.1: |- ph
  assert |- A. x ph
end
