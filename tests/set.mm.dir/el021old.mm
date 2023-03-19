include "wa.mm"
include "dfvd2ani.mm"
include "sylancr.mm"
include "dfvd2anir.mm"

theorem el021old
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume el021old.1: |- ph
  assume el021old.2: |- (. (. ps ,. ch ). ->. th ).
  assume el021old.3: |- ( ( ph /\ th ) -> ta )


  assert |- (. (. ps ,. ch ). ->. ta ).

  proof
    wps
    wch
    wta
    wps
    wch
    wa
    wph
    wth
    wta
    el021old.1
    wps
    wch
    wth
    el021old.2
    dfvd2ani
    el021old.3
    sylancr
    dfvd2anir
end
