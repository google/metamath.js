

axiom ax-mp
  param wph: wff ph
  param wps: wff ps
  assume min: |- ph
  assume maj: |- ( ph -> ps )
  assert |- ps
end
