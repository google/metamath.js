include "vd01.mm"
include "e111.mm"

theorem e101
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume e101.1: |- (. ph ->. ps ).
  assume e101.2: |- ch
  assume e101.3: |- (. ph ->. th ).
  assume e101.4: |- ( ps -> ( ch -> ( th -> ta ) ) )


  assert |- (. ph ->. ta ).

  proof
    wph
    wps
    wch
    wth
    wta
    e101.1
    wch
    wph
    e101.2
    vd01
    e101.3
    e101.4
    e111
end
