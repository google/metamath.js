

axiom ax-3
  param wph: wff ph
  param wps: wff ps
  assert |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) )
end
