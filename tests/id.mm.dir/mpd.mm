
axiom mpd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume mpd.1: |- ( ph -> ps )
  assume mpd.2: |- ( ph -> ( ps -> ch ) )
  assert |- ( ph -> ch )
end
