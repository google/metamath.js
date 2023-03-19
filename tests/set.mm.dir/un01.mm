include "wtru.mm"
include "wa.mm"
include "tru.mm"
include "jctl.mm"
include "dfvd2ani.mm"
include "syl.mm"
include "dfvd1ir.mm"

theorem un01
  let wph: wff ph
  let wps: wff ps
  assume un01.1: |- (. (. T. ,. ph ). ->. ps ).


  assert |- (. ph ->. ps ).

  proof
    wph
    wps
    wph
    wtru
    wph
    wa
    wps
    wph
    wtru
    tru
    jctl
    wtru
    wph
    wps
    un01.1
    dfvd2ani
    syl
    dfvd1ir
end
