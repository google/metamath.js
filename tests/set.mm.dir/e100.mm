include "vd01.mm"
include "e111.mm"

theorem e100
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume e100.1: |- (. ph ->. ps ).
  assume e100.2: |- ch
  assume e100.3: |- th
  assume e100.4: |- ( ps -> ( ch -> ( th -> ta ) ) )


  assert |- (. ph ->. ta ).

  proof
    wph
    wps
    wch
    wth
    wta
    e100.1
    wch
    wph
    e100.2
    vd01
    wth
    wph
    e100.3
    vd01
    e100.4
    e111
end
