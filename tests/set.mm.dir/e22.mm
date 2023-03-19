include "wi.mm"
include "a1i.mm"
include "e222.mm"

theorem e22
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume e22.1: |- (. ph ,. ps ->. ch ).
  assume e22.2: |- (. ph ,. ps ->. th ).
  assume e22.3: |- ( ch -> ( th -> ta ) )


  assert |- (. ph ,. ps ->. ta ).

  proof
    wph
    wps
    wch
    wch
    wth
    wta
    e22.1
    e22.1
    e22.2
    wch
    wth
    wta
    wi
    wi
    wch
    e22.3
    a1i
    e222
end
