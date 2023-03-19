include "vd13.mm"
include "vd23.mm"
include "e333.mm"

theorem e123
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  assume e123.1: |- (. ph ->. ps ).
  assume e123.2: |- (. ph ,. ch ->. th ).
  assume e123.3: |- (. ph ,. ch ,. ta ->. et ).
  assume e123.4: |- ( ps -> ( th -> ( et -> ze ) ) )


  assert |- (. ph ,. ch ,. ta ->. ze ).

  proof
    wph
    wch
    wta
    wps
    wth
    wet
    wze
    wph
    wps
    wch
    wta
    e123.1
    vd13
    wph
    wch
    wth
    wta
    e123.2
    vd23
    e123.3
    e123.4
    e333
end
