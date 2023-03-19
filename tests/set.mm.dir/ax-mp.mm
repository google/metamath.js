
axiom ax-mp
  let wph: wff ph
  let wps: wff ps
  assume min: |- ph
  assume maj: |- ( ph -> ps )
  assert |- ps
end
