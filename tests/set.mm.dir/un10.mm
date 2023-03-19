include "wtru.mm"
include "wa.mm"
include "tru.mm"
include "jctr.mm"
include "dfvd2ani.mm"
include "syl.mm"
include "dfvd1ir.mm"

theorem un10
  let wph: wff ph
  let wps: wff ps
  assume un10.1: |- (. (. ph ,. T. ). ->. ps ).


  assert |- (. ph ->. ps ).

  proof
    wph
    wps
    wph
    wph
    wtru
    wa
    wps
    wph
    wtru
    tru
    jctr
    wph
    wtru
    wps
    un10.1
    dfvd2ani
    syl
    dfvd1ir
end
