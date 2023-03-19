include "vd01.mm"
include "e111.mm"

theorem e110
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume e110.1: |- (. ph ->. ps ).
  assume e110.2: |- (. ph ->. ch ).
  assume e110.3: |- th
  assume e110.4: |- ( ps -> ( ch -> ( th -> ta ) ) )


  assert |- (. ph ->. ta ).

  proof
    wph
    wps
    wch
    wth
    wta
    e110.1
    e110.2
    wth
    wph
    e110.3
    vd01
    e110.4
    e111
end
