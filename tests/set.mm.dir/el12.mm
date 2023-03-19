include "in1.mm"
include "syl2an.mm"
include "dfvd2anir.mm"

theorem el12
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume el12.1: |- (. ph ->. ps ).
  assume el12.2: |- (. ta ->. ch ).
  assume el12.3: |- ( ( ps /\ ch ) -> th )


  assert |- (. (. ph ,. ta ). ->. th ).

  proof
    wph
    wta
    wth
    wph
    wps
    wch
    wth
    wta
    wph
    wps
    el12.1
    in1
    wta
    wch
    el12.2
    in1
    el12.3
    syl2an
    dfvd2anir
end
