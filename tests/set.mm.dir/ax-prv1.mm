
axiom ax-prv1
  let wph: wff ph
  assume ax-prv1.1: |- ph
  assert |- Prv ph
end
