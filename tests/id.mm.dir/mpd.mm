
axiom mpd
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume mpd.1: |- ( ph -> ps )
  assume mpd.2: |- ( ph -> ( ps -> ch ) )
  assert |- ( ph -> ch )
end
