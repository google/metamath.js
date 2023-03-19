include "in1.mm"
include "syl3an.mm"
include "dfvd3anir.mm"

theorem el123
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  assume el123.1: |- (. ph ->. ps ).
  assume el123.2: |- (. ch ->. th ).
  assume el123.3: |- (. ta ->. et ).
  assume el123.4: |- ( ( ps /\ th /\ et ) -> ze )


  assert |- (. (. ph ,. ch ,. ta ). ->. ze ).

  proof
    wph
    wch
    wta
    wze
    wph
    wps
    wch
    wth
    wta
    wet
    wze
    wph
    wps
    el123.1
    in1
    wch
    wth
    el123.2
    in1
    wta
    wet
    el123.3
    in1
    el123.4
    syl3an
    dfvd3anir
end
