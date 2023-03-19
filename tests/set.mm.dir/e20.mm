include "vd02.mm"
include "e22.mm"

theorem e20
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume e20.1: |- (. ph ,. ps ->. ch ).
  assume e20.2: |- th
  assume e20.3: |- ( ch -> ( th -> ta ) )


  assert |- (. ph ,. ps ->. ta ).

  proof
    wph
    wps
    wch
    wth
    wta
    e20.1
    wth
    wph
    wps
    e20.2
    vd02
    e20.3
    e22
end
