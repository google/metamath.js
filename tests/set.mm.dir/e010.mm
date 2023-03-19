include "vd01.mm"
include "e111.mm"

theorem e010
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume e010.1: |- ph
  assume e010.2: |- (. ps ->. ch ).
  assume e010.3: |- th
  assume e010.4: |- ( ph -> ( ch -> ( th -> ta ) ) )


  assert |- (. ps ->. ta ).

  proof
    wps
    wph
    wch
    wth
    wta
    wph
    wps
    e010.1
    vd01
    e010.2
    wth
    wps
    e010.3
    vd01
    e010.4
    e111
end
