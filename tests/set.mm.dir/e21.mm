include "vd12.mm"
include "e22.mm"

theorem e21
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume e21.1: |- (. ph ,. ps ->. ch ).
  assume e21.2: |- (. ph ->. th ).
  assume e21.3: |- ( ch -> ( th -> ta ) )


  assert |- (. ph ,. ps ->. ta ).

  proof
    wph
    wps
    wch
    wth
    wta
    e21.1
    wph
    wth
    wps
    e21.2
    vd12
    e21.3
    e22
end
