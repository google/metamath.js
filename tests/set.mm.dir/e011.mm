include "vd01.mm"
include "e111.mm"

theorem e011
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume e011.1: |- ph
  assume e011.2: |- (. ps ->. ch ).
  assume e011.3: |- (. ps ->. th ).
  assume e011.4: |- ( ph -> ( ch -> ( th -> ta ) ) )


  assert |- (. ps ->. ta ).

  proof
    wps
    wph
    wch
    wth
    wta
    wph
    wps
    e011.1
    vd01
    e011.2
    e011.3
    e011.4
    e111
end
