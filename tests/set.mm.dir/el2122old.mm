include "dfvd2ani.mm"
include "in1.mm"
include "eel2122old.mm"
include "dfvd2anir.mm"

theorem el2122old
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume el2122old.1: |- (. (. ph ,. ps ). ->. ch ).
  assume el2122old.2: |- (. ps ->. th ).
  assume el2122old.3: |- (. ps ->. ta ).
  assume el2122old.4: |- ( ( ch /\ th /\ ta ) -> et )


  assert |- (. (. ph ,. ps ). ->. et ).

  proof
    wph
    wps
    wet
    wph
    wps
    wch
    wth
    wta
    wet
    wph
    wps
    wch
    el2122old.1
    dfvd2ani
    wps
    wth
    el2122old.2
    in1
    wps
    wta
    el2122old.3
    in1
    el2122old.4
    eel2122old
    dfvd2anir
end
