include "wex.mm"
include "dfvd2i.mm"
include "exlimexi.mm"

theorem exinst
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume exinst.1: |- ( ps -> A. x ps )
  assume exinst.2: |- (. E. x ph ,. ph ->. ps ).


  assert |- ( E. x ph -> ps )

  proof
    wph
    wps
    vx
    exinst.1
    wph
    vx
    wex
    wph
    wps
    exinst.2
    dfvd2i
    exlimexi
end
