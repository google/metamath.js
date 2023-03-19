include "vd12.mm"
include "e22.mm"

theorem e12
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume e12.1: |- (. ph ->. ps ).
  assume e12.2: |- (. ph ,. ch ->. th ).
  assume e12.3: |- ( ps -> ( th -> ta ) )


  assert |- (. ph ,. ch ->. ta ).

  proof
    wph
    wch
    wps
    wth
    wta
    wph
    wps
    wch
    e12.1
    vd12
    e12.2
    e12.3
    e22
end
